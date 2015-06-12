Require Export List.
Require Export Arith.

(*Inductive ty : Type :=
  | ty_cons : nat -> ty.*)

Inductive var : Type :=
  |v_cons : nat -> var.

Inductive label : Type :=
  | l_cons : nat -> label.

(*Inductive meth : Type :=
  | m_cons : nat -> meth.*)

Inductive type : Type :=
  | t_rec   : var -> list type_d -> type
  | t_sel   : exp -> label -> type
(*  | t_union : type -> type -> type*)
  | t_top   : type
  | t_bot   : type

with type_d : Type :=
  | t_var  : label -> type -> type_d
  | t_def  : label -> type -> type -> type_d
  | t_type : label -> type -> type -> type_d

with exp : Type :=
  | e_var    : var -> exp
  | e_new    : var -> list decl -> exp -> exp
  | e_meth   : exp -> label -> exp -> exp
  | e_field  : exp -> label -> exp
  | e_type   : exp -> type -> exp

with decl : Type :=
  | d_var  : label -> type -> exp -> decl
  | d_def  : label -> var -> type -> exp -> type -> decl
  | d_type : label -> type -> type -> decl.

Inductive val : exp -> Prop :=
  | V_Var  : forall x, val (e_var x)
  | V_Path : forall v f, val v ->
             val (e_field v f)
  | V_Type : forall v T, val v ->
             val (e_type v T).

Inductive d_val : decl -> Prop :=
  | DV_Var : forall f T v,
             val v ->
             d_val (d_var f T v)
  | DV_Def : forall m x S e T,
             d_val (d_def m x S e T)
  | DV_Type : forall L S U,
             d_val (d_type L S U).

Fixpoint range {A B : Type} (l: list (A * B)) : list B :=
  match l with
  | nil => nil
  | (_, b)::t => b::(range t)
end.

Fixpoint dom {A B : Type} (l: list (A * B)) : list A :=
  match l with
  | nil => nil
  | (a, _)::t => a::(dom t)
end.

Module Type VarComparator.

  Parameter X: Set.
  Parameter eq_var : X -> X -> Prop.
  Parameter neq_var :  X -> X -> Prop.

  Infix "=" := eq_var (at level 70).
  Infix "<>" := (~ eq_var) (at level 70).

  Parameter eq_dec_var : forall x y : X, { x = y } + { x <> y }.

End VarComparator.

Definition X := var.
Definition eq_var x y := match x with
                         | v_cons n => match y with
                                       | v_cons m => eq_nat n m
                                       end
                         end.
Definition neq_var x y:= ~ eq_var  x y.

Definition eq_dec_var (x y : var) : { x = y } + { x <> y }.
Proof.
  destruct x as [n]; destruct y as [m].
  destruct (eq_nat_dec n m); subst; auto.
  right; intros HContra;
  inversion HContra; subst; auto.
Qed.

(*End VarComparator.*)

Module Type LabelComparator.

  Parameter Y: Set.
  Parameter eq_lab : Y -> Y -> Prop.
  Parameter neq_lab :  Y -> Y -> Prop.

  Infix "=" := eq_lab (at level 70).
  Infix "<>" := (~ eq_lab) (at level 70).

  Parameter eq_dec_lab : forall x y : Y, { x = y } + { x <> y }.

End LabelComparator.

Definition Y := label.
Definition eq_lab x y := match x with
                     | l_cons n => match y with
                                   | l_cons m => eq_nat n m
                                   end
                     end.
Definition neq_lab x y:= ~ eq_lab  x y.

Definition eq_dec_lab (x y : label) : { x = y } + { x <> y }.
Proof.
  destruct x as [n]; destruct y as [m].
  destruct (eq_nat_dec n m); subst; auto.
  right; intros HContra;
  inversion HContra; subst; auto.
Qed.

Fixpoint get {A : Type} (x : var) (l : list (var * A)) : option A :=
  match l with
  | nil => None
  | (y,b)::t => if eq_dec_var x y then Some b else get x t 
end.

Fixpoint subst_t (x : var) (p : exp) (t : type): type :=
  match t with
  | t_rec z D_ => t_rec z (map (subst_D x p) D_)
  | t_sel p' L => t_sel (subst_e x p p') L
  | t_top => t
  | t_bot => t
  end

with subst_D (x : var) (p : exp) (D : type_d): type_d :=
  match D with
  | t_var f T => t_var f (subst_t x p T)
  | t_def m T T' => t_def m (subst_t x p T) (subst_t x p T')
  | t_type L T U => t_type L (subst_t x p T) (subst_t x p U)
end

with subst_e (x : var) (p : exp) (e : exp): exp :=
  match e with
  | e_var z => if eq_dec_var x z then p else e
  | e_new y d_ e' => e_new y (map (subst_d x p) d_) (subst_e x p e')
  | e_meth e0 m e1 => e_meth (subst_e x p e0) m (subst_e x p e1)
  | e_field e0 f => e_field (subst_e x p e0) f
  | e_type e0 T => e_type (subst_e x p e0) T
  end

with subst_d (x : var) (p : exp) (d : decl): decl :=
  match d with
  | d_var f T e => d_var f (subst_t x p T) (subst_e x p e)
  | d_def m x T e U => d_def m x (subst_t x p T) (subst_e x p e) (subst_t x p U)
  | d_type L T U => d_type L (subst_t x p T) (subst_t x p U)
end.

Inductive notin_e : var -> exp -> Prop :=
  | notin_var : forall x y,
                x <> y ->
                notin_e x (e_var y)
  | notin_new : forall x y d_ e,
                (forall d, In d d_ -> notin_d x d) ->
                notin_e x (e_var y) ->
                notin_e x e ->
                notin_e x (e_new y d_ e)
  | notin_meth : forall x e m e0,
                 notin_e x e ->
                 notin_e x e0 ->
                 notin_e x (e_meth e m e0)
  | notin_field : forall x e f,
                 notin_e x e ->
                 notin_e x (e_field e f)
  | notin_type : forall x e T,
                 notin_e x e ->
                 notin_t x T ->
                 notin_e x (e_type e T)

with notin_d : var -> decl -> Prop :=
  | notin_d_var : forall x l T e,
                  notin_t x T ->
                  notin_e x e ->
                  notin_d x (d_var l T e)
  | notin_d_def : forall x m y S e T,
                  notin_t x S ->
                  notin_t x T ->
                  notin_e x e ->
                  notin_d x (d_def m y S e T)
  | notin_d_type : forall x L S U,
                   notin_t x S ->
                   notin_t x U ->
                   notin_d x (d_type L S U)

with notin_t : var -> type -> Prop :=
  | notin_rec : forall x z D_,
                (forall D, In D D_ -> notin_D x D) ->
                notin_t x (t_rec z D_)
  | notin_sel : forall x p L,
                notin_e x p ->
                notin_t x (t_sel p L)

with notin_D : var -> type_d -> Prop :=
  | notin_D_var : forall x f T,
                   notin_t x T ->
                   notin_D x (t_var f T)
  | notin_D_def : forall x m S T,
                   notin_t x S ->
                   notin_t x T ->
                   notin_D x (t_def m S T)
  | notin_D_type : forall x L S U,
                   notin_t x S ->
                   notin_t x U ->
                   notin_D x (t_type L S U).

Inductive typing : list (var * type) -> exp -> type -> Prop :=
  | T_Var : forall G x T,
            In (x,T) G ->
            typing G (e_var x) T

  | T_New : forall G y d_ e T,
            (exists2 D_, typings_d ((y, t_rec y D_)::G) d_ D_ &
                         typing ((y, t_rec y D_)::G) e T) ->
            ~In y (dom G) ->
            typing G (e_new y d_ e) T

  | T_Meth : forall G e0 m e1 T0 S T,
             member G e0 (t_def m S T) ->
             typing G e0 T0 ->
             typing G e1 S ->
             typing G (e_meth e0 m e1) T

  | T_Acc : forall G e0 f T0 T,
            typing G e0 T0 ->
            member G e0 (t_var f T) ->
            typing G (e_field e0 f) T

  | T_Wide : forall G e T,
             subtyping G e T ->
             typing G (e_type e T) T

with subtyping : list (var * type) -> exp -> type -> Prop :=
  | T_Sub : forall G e S T,
            typing G e S ->
            sub G S T ->
            subtyping G e T

with typing_d : list (var * type) -> decl -> type_d -> Prop :=
  | TD_Var : forall G f T v,
             typing G v T ->
             val v ->
             typing_d G (d_var f T v) (t_var f T)

  | TD_Def : forall G m x S e T,
             typing ((x,S)::G) e T ->
             typing_d G (d_def m x S e T) (t_def m S T)

  | TD_Type : forall G L S U,
              sub G S U ->
              typing_d G (d_type L S U) (t_type L S U)
              

with typings_d : list (var * type) -> list decl -> list type_d -> Prop :=
  | TD_Nil : forall G, typings_d G nil nil

  | TD_Head : forall G d D d_ D_,
              typing_d G d D ->
              typings_d G d_ D_ ->
              typings_d G (d::d_) (D::D_)

with sub : list (var * type) -> type -> type -> Prop :=
  | S_Refl      : forall G T, sub G T T

  | S_Rec       : forall G z z' D_ D_',
                  (forall D, In D D_ -> 
                  exists2 D', In D' D_' & sub_d ((z,t_rec z D_)::G) D (subst_D z' (e_var z) D')) ->
                  sub G (t_rec z D_) (t_rec z' D_')

  | S_Sel_Upper : forall G p L S U U',
                  sub G U U' ->
                  member G p (t_type L S U) ->
                  sub G (t_sel p L) U'

  | S_Sel_Lower : forall G p L S U S',
                  sub G S' S ->
                  member G p (t_type L S U) ->
                  sub G S' (t_sel p L)

  | S_Top       : forall G T,
                  sub G T t_top

  | S_Bot       : forall G T,
                  sub G t_bot T

with sub_d : list (var * type) -> type_d -> type_d -> Prop :=
  | SD_Var  : forall G f S T,
              sub G S T ->
              sub_d G (t_var f S) (t_var f T)
  | SD_Def  : forall G m S T S' T',
              sub G S' S ->
              sub G T T' ->
              sub_d G (t_def m S T) (t_def m S' T')
  | SD_Type : forall G L S U S' U',
              sub G S' S ->
              sub G U U' ->
              sub_d G (t_type L S U) (t_type L S' U')

with expansion : list (var * type) -> var -> type -> list type_d -> Prop:=
  | E_Rec : forall G z D_,
            expansion G z (t_rec z D_) D_
  | E_Sel : forall G z p L S U D_,
            val p ->
            member G p (t_type L S U) ->
            expansion G z U D_ ->
            expansion G z (t_sel p L) D_

with member : list (var * type) -> exp -> type_d -> Prop:=
  | M_Path : forall G z p T D_ D,
             typing G p T ->
             expansion G z T D_ ->
             In D D_ ->
             member G p (subst_D z p D)
  | M_Exp : forall G z e T D_ D,
            typing G e T ->
            expansion G z T D_ ->
            In D D_ ->
            notin_D z D ->
            member G e D.

Definition store := list (var * list decl).

Fixpoint lookup {A : Type} (x : var) (u : list (var * A)) : option (var * A) :=
match u with
  | nil => None
  | (y,a)::u' => if (eq_dec_var x y) then Some (y,a) else lookup x u'
end.

Fixpoint lookup_d (l : label) (d_ : list decl) : option decl :=
match d_ with
  | nil => None
  | d::d_' => match d with
                | d_var f T e => if (eq_dec_lab l f) then Some d else lookup_d l d_'
                | d_def m x T e U => if (eq_dec_lab l m) then Some d else lookup_d l d_'
                | d_type L T U => if (eq_dec_lab l L) then Some d else lookup_d l d_'
              end
end.

Inductive path : exp -> store -> var * list decl -> Prop :=
  | p_var : forall x u y d_,
            lookup x u = Some (y,d_) ->
            path (e_var x) u (y,d_)
  | p_field : forall e f u x d_ l T v z d_',
              path (e_field e f) u (x, d_) ->
              lookup_d f d_ = Some (d_var l T v) ->
              path v u (z, d_') ->
              path (e_field e f) u (z, d_')
  | p_type : forall e T u z d_,
             path e u (z, d_) ->
             path (e_type e T) u (z, d_).

(*Fixpoint path (e : exp) (u : store) : option (var * list decl) :=
match e with
  | e_var x => lookup x u
  | e_field e0 f => match path e0 u with
                      | Some (x, d_) => match lookup_d f d_ with
                                          | Some (d_var f' T v) => path v u
                                          | Some (d_def _ _ _ _ _) => None
                                          | Some (d_type _ _ _) => None
                                          | None => None
                                        end
                      | None => None
                    end
  | e_type e0 T => path e0 u
  | _ => None
end.*)

Inductive reduction : store -> exp -> store -> exp -> Prop :=
  | R_New : forall u' u y d_ e,
            (forall d, In d d_ -> d_val d) ->
            u' = (y,d_)::u ->
            reduction u (e_new y d_ e) u' e

  | R_Meth : forall u v1 m v2 u'


(*Inductive typing : list (var * type) -> exp -> type -> Prop :=
  | T_Var : forall G x T,
            In (x,T) G ->
            typing G (e_var x) T

  | T_New : forall G y d_ e T,
            (exists2 D_, typings_d ((y, t_rec y D_)::G) d_ D_ &
                         typing ((y, t_rec y D_)::G) e T) ->
            ~In y (dom G) ->
            typing G (e_new y d_ e) T

  | T_Meth : forall G e0 m e1 T0 S T,
             member G e0 (t_def m S T) ->
             typing G e0 T0 ->
             typing G e1 S ->
             typing G (e_meth e0 m e1) T

  | T_Acc : forall G e0 f T0 T,
            typing G e0 T0 ->
            member G e0 (t_var f T) ->
            typing G (e_field e0 f) T

  | T_Wide : forall G e T,
             subtyping G e T ->
             typing G (e_type e T) T

with subtyping : list (var * type) -> exp -> type -> Prop :=
  | T_Sub : forall G e S T,
            typing G e S ->
            sub G S T ->
            subtyping G e T

with typing_d : list (var * type) -> decl -> type_d -> Prop :=
  | TD_Var : forall G f T v,
             typing G v T ->
             val v ->
             typing_d G (d_var f T v) (t_var f T)

  | TD_Def : forall G m x S e T,
             typing ((x,S)::G) e T ->
             typing_d G (d_def m x S e T) (t_def m S T)

  | TD_Type : forall G L S U,
              sub G S U ->
              typing_d G (d_type L S U) (t_type L S U)
              

with typings_d : list (var * type) -> list decl -> list type_d -> Prop :=
  | TD_Nil : forall G, typings_d G nil nil

  | TD_Head : forall G d D d_ D_,
              typing_d G d D ->
              typings_d G d_ D_ ->
              typings_d G (d::d_) (D::D_).*)


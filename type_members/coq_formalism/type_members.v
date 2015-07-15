Require Export List.
Require Export Arith.

(*Inductive ty : Type :=
  | ty_cons : nat -> ty.*)

Inductive var : Type :=
  |v_cons : nat -> var.

Definition self := v_cons 0.

Inductive label : Type :=
  | l_cons : nat -> label.

(*Inductive meth : Type :=
  | m_cons : nat -> meth.*)

Inductive type : Type :=
  | t_rec   : list type_d -> type
  | t_sel   : exp -> label -> type
(*  | t_union : type -> type -> type*)
  | t_top   : type
  | t_bot   : type

with type_d : Type :=
  | t_val  : label -> type -> type_d
  | t_def  : label -> type -> type -> type_d
  | t_type : label -> type -> type -> type_d

with exp : Type :=
  | e_var    : var -> exp
  | e_loc    : nat -> exp
  | e_new    : list decl -> exp
  | e_meth   : exp -> label -> type -> exp -> exp
  | e_field  : exp -> label -> exp
  | e_type   : exp -> type -> exp

with decl : Type :=
  | d_val  : label -> type -> exp -> decl
  | d_def  : label -> var -> type -> exp -> type -> decl
  | d_type : label -> type -> type -> decl.

Inductive is_path : exp -> Prop :=
  | P_Var   : forall x, is_path (e_var x)
  | P_Loc   : forall l, is_path (e_loc l)
  | P_Field : forall p f, is_path p ->
              is_path (e_field p f)
  | P_Type  : forall p T, is_path p ->
              is_path (e_type p T).

Inductive is_value : exp -> Prop :=
  | V_Loc   : forall l, is_value (e_loc l)
  | V_Field : forall v f, is_value v ->
              is_value (e_field v f)
  | V_Type  : forall v T, is_value v ->
              is_value (e_type v T).

Inductive is_value_d : decl -> Prop :=
  | DV_Val : forall f T l,
             is_value_d (d_val f T (e_loc l))
  | DV_Def : forall m x S e T,
             is_value_d (d_def m x S e T)
  | DV_Type : forall L S U,
             is_value_d (d_type L S U).

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

Fixpoint subst_t (x : var) (v : exp) (t : type): type :=
  match t with
  | t_rec D_ => t_rec (map (subst_D x v) D_)
  | t_sel p' L => t_sel (subst_e x v p') L
  | t_top => t
  | t_bot => t
  end

with subst_D (x : var) (v : exp) (D : type_d): type_d :=
  match D with
  | t_val f T => t_val f (subst_t x v T)
  | t_def m T T' => t_def m (subst_t x v T) (subst_t x v T')
  | t_type L T U => t_type L (subst_t x v T) (subst_t x v U)
end

with subst_e (x : var) (v : exp) (e : exp): exp :=
  match e with
  | e_var y => if eq_dec_var x y then v else e
  | e_loc l => e
  | e_new d_ => e_new (map (subst_d x v) d_)
  | e_meth e0 m T e1 => e_meth (subst_e x v e0) m (subst_t x v T) (subst_e x v e1)
  | e_field e0 f => e_field (subst_e x v e0) f
  | e_type e0 T => e_type (subst_e x v e0) T
  end

with subst_d (x : var) (v : exp) (d : decl): decl :=
  match d with
  | d_val f T e => d_val f (subst_t x v T) (subst_e x v e)
  | d_def m x T e U => d_def m x (subst_t x v T) (subst_e x v e) (subst_t x v U)
  | d_type L T U => d_type L (subst_t x v T) (subst_t x v U)
end.

Inductive notin_e : var -> exp -> Prop :=
  | notin_var : forall x y,
                x <> y ->
                notin_e x (e_var y)
  | notin_new : forall x d_ e,
                (forall d, In d d_ -> notin_d x d) ->
                notin_e x e ->
                notin_e x (e_new d_)
  | notin_meth : forall x e m T e0,
                 notin_e x e ->
                 notin_e x e0 ->
                 notin_e x (e_meth e m T e0)
  | notin_field : forall x e f,
                 notin_e x e ->
                 notin_e x (e_field e f)
  | notin_type : forall x e T,
                 notin_e x e ->
                 notin_t x T ->
                 notin_e x (e_type e T)

with notin_d : var -> decl -> Prop :=
  | notin_d_val : forall x l T e,
                  notin_t x T ->
                  notin_e x e ->
                  notin_d x (d_val l T e)
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
  | notin_rec : forall x D_,
                (forall D, In D D_ -> notin_D x D) ->
                notin_t x (t_rec D_)
  | notin_sel : forall x p L,
                notin_e x p ->
                notin_t x (t_sel p L)

with notin_D : var -> type_d -> Prop :=
  | notin_D_val : forall x f T,
                   notin_t x T ->
                   notin_D x (t_val f T)
  | notin_D_def : forall x m S T,
                   notin_t x S ->
                   notin_t x T ->
                   notin_D x (t_def m S T)
  | notin_D_type : forall x L S U,
                   notin_t x S ->
                   notin_t x U ->
                   notin_D x (t_type L S U).

Fixpoint lookup {A : Type} (n : nat) (l : list A) : option A :=
  match l with
  | nil => None
  | h::t => match n with
            | O => Some h
            | S m => lookup m t
            end
end.

Inductive typing : list (var * type) -> list type -> exp -> type -> Prop :=
  | T_Var : forall G E x T,
            In (x,T) G ->
            typing G E (e_var x) T

  | T_Loc : forall G E l T,
            lookup l E = Some T ->
            typing G E (e_loc l) T

  | T_New : forall G E d_ e T,
            (exists2 D_, typings_d ((self, t_rec D_)::G) E d_ D_ &
                         typing ((self, t_rec D_)::G) E e T) ->
            typing G E (e_new d_) T

  | T_Meth : forall G E e0 m U e1 T0 S T,
             member G E e0 (t_def m S T) ->
             typing G E e0 T0 ->
             typing G E e1 S ->
             sub G E T U ->
             typing G E (e_meth e0 m U e1) U

  | T_Acc : forall G E e0 f T0 T,
            typing G E e0 T0 ->
            member G E e0 (t_val f T) ->
            typing G E (e_field e0 f) T

  | T_Wide : forall G E e T,
             subtyping G E e T ->
             typing G E (e_type e T) T

with subtyping : list (var * type) -> list type -> exp -> type -> Prop :=
  | T_Sub : forall G E e S T,
            typing G E e S ->
            sub G E S T ->
            subtyping G E e T

with typing_d : list (var * type) -> list type -> decl -> type_d -> Prop :=
  | TD_Val_x : forall G E f T e,
             typing G E e T ->
             typing_d G E (d_val f T e) (t_val f T)

  | TD_Def : forall G E m x S e T,
             typing ((x,S)::G) E e T ->
             typing_d G E (d_def m x S e T) (t_def m S T)

  | TD_Type : forall G E L S U,
              sub G E S U ->
              typing_d G E (d_type L S U) (t_type L S U)

with typings_d : list (var * type) -> list type -> list decl -> list type_d -> Prop :=
  | TD_Nil : forall G E, typings_d G E nil nil

  | TD_Head : forall G E d D d_ D_,
              typing_d G E d D ->
              typings_d G E d_ D_ ->
              typings_d G E (d::d_) (D::D_)

with subtyping_d : list (var * type) -> list type -> decl -> type_d -> Prop :=
  | TD_Sub : forall G E d D D',
             typing_d G E d D ->
             sub_d G E D D' ->
             subtyping_d G E d D'

with subtypings_d : list (var * type) -> list type -> list decl -> list type_d -> Prop :=
  | Sub_TD_Nil  : forall G E, subtypings_d G E nil nil

  | Sub_TD_Head : forall G E d D d_ D_,
                  subtyping_d G E d D ->
                  subtypings_d G E d_ D_ ->
                  subtypings_d G E (d::d_) (D::D_)

with sub : list (var * type) -> list type -> type -> type -> Prop :=
  | S_Refl      : forall G E T, sub G E T T

  | S_Rec       : forall G E D_ D_',
                  subs_d G E D_ D_' ->
                  sub G E (t_rec D_) (t_rec D_')

  | S_Sel_Upper : forall G E p L S U U',
                  sub G E U U' ->
                  member G E p (t_type L S U) ->
                  sub G E (t_sel p L) U'

  | S_Sel_Lower : forall G E p L S U S',
                  sub G E S' S ->
                  member G E p (t_type L S U) ->
                  sub G E S' (t_sel p L)

  | S_Top       : forall G E T,
                  sub G E T t_top

  | S_Bot       : forall G E T,
                  sub G E t_bot T

with sub_d : list (var * type) -> list type -> type_d -> type_d -> Prop :=
  | SD_Var  : forall G E f S T,
              sub G E S T ->
              sub_d G E (t_val f S) (t_val f T)
  | SD_Def  : forall G E m S T S' T',
              sub G E S' S ->
              sub G E T T' ->
              sub_d G E (t_def m S T) (t_def m S' T')
  | SD_Type : forall G E L S U S' U',
              sub G E S' S ->
              sub G E U U' ->
              sub_d G E (t_type L S U) (t_type L S' U')

with subs_d : list (var * type) -> list type -> list type_d -> list type_d -> Prop :=
  | SD_Nil  : forall G E D_,
              subs_d G E D_ nil
  | SD_list  : forall G E D_ D_' D D',
              sub_d G E D D' ->
              subs_d G E D_ D_' ->
              subs_d G E (D::D_) (D'::D_')

with expansion : list (var * type) -> list type -> type -> list type_d -> Prop:=
  | E_Rec : forall G E D_,
            expansion G E (t_rec D_) D_
  | E_Sel : forall G E p L S U D_,
            is_path p ->
            member G E p (t_type L S U) ->
            expansion G E U D_ ->
            expansion G E (t_sel p L) D_

with member : list (var * type) -> list type -> exp -> type_d -> Prop:=
  | M_Path : forall G E p T D_ D,
             typing G E p T ->
             expansion G E T D_ ->
             In D D_ ->
             member G E p (subst_D self p D)
  | M_Exp : forall G E e T D_ D,
            typing G E e T ->
            expansion G E T D_ ->
            In D D_ ->
            notin_D self D ->
            member G E e D.

Hint Constructors typing subtyping typing_d typings_d subtyping_d subtypings_d sub sub_d subs_d expansion member.

Inductive sub_t : list (var * type) -> list type -> type -> type -> Prop :=
  | S_t_Refl  : forall G E T, sub_t G E T T
  | S_t_Trans : forall G E S T U, sub_t G E S T ->
                sub G E T U ->
                sub_t G E S U.

Hint Constructors sub_t.

Definition store := list (list decl).

Fixpoint get_d (l : label) (d_ : list decl) : option decl :=
match d_ with
  | nil => None
  | d::d_' => match d with
                | d_val f T e => if (eq_dec_lab l f) then Some d else get_d l d_'
                | d_def m x T e U => if (eq_dec_lab l m) then Some d else get_d l d_'
                | d_type L T U => if (eq_dec_lab l L) then Some d else get_d l d_'
              end
end.

Inductive path : exp -> store -> nat -> Prop :=
  | p_var   : forall l u,
              path (e_loc l) u l
  | p_field : forall e f u l l' d_ f' T v,
              path e u l' ->
              lookup l' u = Some d_->
              get_d f d_ = Some (d_val f' T v) ->
              path v u l ->
              path (e_field e f) u l
  | p_type  : forall e T u l,
              path e u l ->
              path (e_type e T) u l.

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
  | R_New : forall l u d_,
            length u = l ->
            reduction u (e_new d_) (d_::u) (e_loc l).
            

Require Export String.
Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.
Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Scheme typing_typing_ind := Minimality for typing Sort Prop
with typing_subtyping_ind := Minimality for subtyping Sort Prop
with typing_typing_d_ind := Minimality for typing_d Sort Prop
with typing_typings_d_ind := Minimality for typings_d Sort Prop
with typing_subtyping_d_ind := Minimality for subtyping_d Sort Prop
with typing_subtypings_d_ind := Minimality for subtypings_d Sort Prop
with typing_sub_ind := Minimality for sub Sort Prop
with typing_sub_d_ind := Minimality for sub_d Sort Prop
with typing_subs_d_ind := Minimality for subs_d Sort Prop
with typing_expansion_ind := Minimality for expansion Sort Prop
with typing_member_ind := Minimality for member Sort Prop.

Combined Scheme typing_mutind from 
      typing_typing_ind,
      typing_subtyping_ind,
      typing_typing_d_ind,
      typing_typings_d_ind,
      typing_subtyping_d_ind,
      typing_subtypings_d_ind,
      typing_sub_ind,
      typing_sub_d_ind,
      typing_subs_d_ind,
      typing_expansion_ind,
      typing_member_ind.

Scheme subtype_sub_ind := Minimality for sub Sort Prop
with subtype_sub_d_ind := Minimality for sub_d Sort Prop
with subtype_subs_d_ind := Minimality for subs_d Sort Prop.

Combined Scheme sub_mutind from 
      subtype_sub_ind,
      subtype_sub_d_ind,
      subtype_subs_d_ind.

Notation "l1 '++' l2" := (app l1 l2).

(*Theorem preservation : forall G E e T, bleh.*)

Theorem environment_narrowing_mutind : 
  (forall G E e T, typing G E e T -> (forall G_a x S U G_b,
                                      G = (G_a ++ ((x,U)::G_b)) ->
                                      sub G_a E S U ->
                                      subtyping (G_a ++ ((x,S)::G_b)) E e T)) /\

  (forall G E e T, subtyping G E e T -> (forall G_a x S U G_b,
                                         G = (G_a ++ ((x,U)::G_b)) ->
                                         sub G_a E S U ->
                                         subtyping (G_a ++ ((x,S)::G_b)) E e T)) /\

  (forall G E d D, typing_d G E d D -> (forall G_a x S U G_b,
                                         G = (G_a ++ ((x,U)::G_b)) ->
                                         sub G_a E S U ->
                                         typing_d (G_a ++ ((x,S)::G_b)) E d D)) /\

  (forall G E d_ D_, typings_d G E d_ D_ -> (forall G_a x S U G_b,
                                               G = (G_a ++ ((x,U)::G_b)) ->
                                               sub G_a E S U ->
                                               subtypings_d (G_a ++ ((x,S)::G_b)) E d_ D_)) /\

  (forall G E d D, subtyping_d G E d D -> (forall G_a x S U G_b,
                                               G = (G_a ++ ((x,U)::G_b)) ->
                                               sub G_a E S U ->
                                               subtyping_d (G_a ++ ((x,S)::G_b)) E d D)) /\

  (forall G E d_ D_, subtypings_d G E d_ D_ -> (forall G_a x S U G_b,
                                               G = (G_a ++ ((x,U)::G_b)) ->
                                               sub G_a E S U ->
                                               subtypings_d (G_a ++ ((x,S)::G_b)) E d_ D_)) /\

  (forall G E T T', sub G E T T' -> (forall G_a x S U G_b,
                                       G = (app G_a ((x,U)::G_b)) ->
                                       sub G_a E S U ->
                                       sub (G_a ++ ((x,S)::G_b)) E T T')) /\

  (forall G E D D', sub_d G E D D' -> (forall G_a x S U G_b,
                                       G = (G_a ++ ((x,U)::G_b)) ->
                                       sub G_a E S U ->
                                       sub_d (G_a ++ ((x,S)::G_b)) E D D')) /\

  (forall G E D_ D_', subs_d G E D_ D_' -> (forall G_a x S U G_b,
                                       G = (G_a ++ ((x,U)::G_b)) ->
                                       sub G_a E S U ->
                                       subs_d (G_a ++ ((x,S)::G_b)) E D_ D_')) /\

  (forall G E T D_, expansion G E T D_ -> (forall G_a x S U G_b,
                                           G = (G_a ++ ((x,U)::G_b)) ->
                                           sub G_a E S U ->
                                           expansion (G_a ++ ((x,S)::G_b)) E T D_)) /\

  (forall G E e D, member G E e D -> (forall G_a x S U G_b,
                                      G = (G_a ++ ((x,U)::G_b)) ->
                                      sub G_a E S U ->
                                      member (G_a ++ ((x,S)::G_b)) E e D)).
Proof.
  apply typing_mutind; intros; subst; eauto.
  Case "T_Var".
    apply T_Var.
  Case "T_New".
  Case "T_Meth".
  Case "TD_Def".
Qed.  
  
  

Theorem subtype_equality : forall G S T,
  subtype G S T ->
  subtype G T S ->
  

Theorem subtype_transitivity : forall G S T,
  sub G S T ->
  forall U, sub G T U ->
  sub G S U.
Proof.
  intros G S T; revert G S.
  induction T; intros.

Qed.

Theorem subtype_transitivity : forall G S T,
  sub G S T ->
  forall U, sub G T U ->
  sub G S U.
Proof.
  intros G S T Hsub;
  induction Hsub; intros.

  auto.

  induction H0; subst. admit. admit.
    apply S_Rec; auto.

    admit.

    apply S_Rec; intros.
    apply H5 in H1; destruct H1 as [D Ha Hb].
    

    

Qed.
  
  
  
  

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


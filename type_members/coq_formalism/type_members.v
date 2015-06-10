Require Export List.
Require Export Arith.

Inductive ty : Type :=
  | ty_cons : nat -> ty.

Inductive var : Type :=
  |v_cons : nat -> var.

Inductive label : Type :=
  | l_cons : nat -> label.

Inductive meth : Type :=
  | m_cons : nat -> meth.

Inductive path : Type :=
  | p_var : var -> path
  | p_sel : path -> label -> path. 

Inductive type : Type :=
  | t_rec   : var -> list type_d -> type
  | t_sel   : exp -> ty -> type
(*  | t_union : type -> type -> type*)
  | t_top   : type
  | t_bot   : type

with type_d : Type :=
  | t_var  : label -> type -> type_d
  | t_def  : meth -> type -> type -> type_d
  | t_type : ty -> type -> type -> type_d

with exp : Type :=
  | e_var    : var -> exp
  | e_new    : list decl -> exp -> exp
  | e_meth   : exp -> meth -> exp -> exp
  | e_field  : exp -> label -> exp
  | e_type   : exp -> type -> exp

with decl : Type :=
  | d_var  : label -> type -> exp -> decl
  | d_def  : meth -> var -> type -> exp -> type -> decl
  | d_type : ty -> type -> type -> decl.

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

Module Type Comparator.

  Parameter X: Set.
  Parameter eq : X -> X -> Prop.
  Parameter neq :  X -> X -> Prop.

  Infix "=" := eq (at level 70).
  Infix "<>" := (~ eq) (at level 70).

  Parameter eq_dec : forall x y : X, { x = y } + { x <> y }.

End Comparator.

Definition X := var.
Definition eq x y := match x with
                     | v_cons n => match y with
                                   | v_cons m => eq_nat n m
                                   end
                     end.
Definition neq x y:= ~ eq  x y.

Definition eq_dec (x y : var) : { x = y } + { x <> y }.
Proof.
  destruct x as [n]; destruct y as [m].
  destruct (eq_nat_dec n m); subst; auto.
  right; intros HContra;
  inversion HContra; subst; auto.
Qed.

(*End VarComparator.*)

Fixpoint get {A : Type} (x : var) (l : list (var * A)) : option A :=
  match l with
  | nil => None
  | (y,b)::t => if eq_dec x y then Some b else get x t 
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
  | e_var z => if eq_dec x z then p else e
  | e_new d_ e' => e_new (map (subst_d x p) d_) (subst_e x p e')
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
  | notin_new : forall x d_ e,
                (forall d, In d d_ -> notin_d x d) ->
                notin_e x e ->
                notin_e x (e_new d_ e)
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
                (forall D, In D D_ -> notin_td x D) ->
                notin_t x (t_rec z D_)
  | notin_sel : forall x p L,
                notin_e x p ->
                notin_t x (t_sel p L)

with notin_td : var -> type_d -> Prop :=
  | notin_td_var : forall x f T,
                   notin_t x T ->
                   notin_td x (t_var f T)
  | notin_td_def : forall x m S T,
                   notin_t x S ->
                   notin_t x T ->
                   notin_td x (t_def m S T)
  | notin_td_type : forall x L S U,
                   notin_t x S ->
                   notin_t x U ->
                   notin_td x (t_type L S U).

Inductive expansion : list (var * type) -> var -> type -> list type_d -> Prop:=
  | E_Rec : forall G z D_,
            expansion G z (t_rec z D_) D_
  | E_Sel : forall G z p L S U D_,
            val p ->
            member G z p (t_type L S U) ->
            expansion G z U D_ ->
            expansion G z (t_sel p L) D_

with member : list (var * type) -> var -> exp -> type_d -> Prop:=
  | M_Path : forall G z p T D_ D,
(*typing G p T*)
             expansion G z T D_ ->
             In D D_ ->
             member G z p (subst_D z p D)
  | M_Exp : forall G z e T D_ D,
(*typing G e T*)
            expansion G z T D_ ->
            In D D_ ->
            notin_td z D ->
            member G z e D.

Inductive sub : list (var * type) -> type -> type -> Prop :=
  | S_Refl : forall G T, sub G T T
  | S_Rec  : forall G D_ D_',
             (forall D, In D D_ -> exists2 D', In D' D_' & sub_d G. D D') ->
             sub G (t_rec D_) (t_rec D_')
  | S_Sel_Upper : forall G x L S U U',
                  sub G U U' ->
                  member 

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
              sub_d G (t_type L S U) (t_type L S' U').


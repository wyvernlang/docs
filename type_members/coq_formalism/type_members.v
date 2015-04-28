Require Export List.
Require Export Arith.

Inductive ty : Type :=
  | ty_cons : nat -> ty.

Inductive var : Type :=
  |v_cons : nat -> var.

Definition self := v_cons 0.

Inductive field : Type :=
  | f_cons : nat -> field.

Inductive meth : Type :=
  | m_cons : nat -> meth.

Inductive type : Type :=
  | t_rec : list type_d -> type
  | t_sel : var -> ty -> type
  | t_top : type
  | t_bot : type

with type_d : Type :=
  | t_var  : field -> type -> type_d
  | t_def  : meth -> type -> type -> type_d
  | t_type : ty -> type -> type -> type_d.

Inductive exp : Type :=
  | e_var    : var -> exp
  | e_new    : var -> list decl -> exp -> exp
  | e_meth   : exp -> meth -> exp -> exp
  | e_field  : exp -> field -> exp
  | e_assign : exp -> field -> exp -> exp

with decl : Type :=
  | d_var  : field -> type -> exp -> decl
  | d_def  : meth -> var -> type -> exp -> type -> decl
  | d_type : ty -> type -> type -> decl.

Inductive val : exp -> Prop :=
  | V_Var : forall x, val (e_var x).

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

(*Fixpoint eq_var (x y : var) : Prop :=
  match x with
  | v_cons O => match y with
                | v_cons O => True
                | v_cons (S _) => False
                end
  | v_cons (S n) => match y with
                  | v_cons O => False
                  | v_cons (S m) => eq_nat n m
                  end
end.*)

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

Fixpoint subst_t (x y : var) (t : type): type :=
  match t with
  | t_rec D_ => t_rec (map (subst_D x y) D_)
  | t_sel z L => if eq_dec x z then t_sel y L else t
  | t_top => t
  | t_bot => t
  end

with subst_D (x y : var) (D : type_d): type_d :=
  match D with
  | t_var f T => t_var f (subst_t x y T)
  | t_def m T T' => t_def m (subst_t x y T) (subst_t x y T')
  | t_type L T U => t_type L (subst_t x y T) (subst_t x y U)
end.

Fixpoint subst_e (x y : var) (e : exp): exp :=
  match e with
  | e_var z => if eq_dec x z then e_var y else e
  | e_new z d_ e' => e_new z (map (subst_d x y) d_) (subst_e x y e')
  | e_meth e0 m e1 => e_meth (subst_e x y e0) m (subst_e x y e1)
  | e_field e0 f => e_field (subst_e x y e0) f
  | e_assign e0 f e1 => e_assign (subst_e x y e0) f (subst_e x y e1)
  end

with subst_d (x y : var) (d : decl): decl :=
  match d with
  | d_var f T e => d_var f (subst_t x y T) (subst_e x y e)
  | d_def m x T e U => d_def m x (subst_t x y T) (subst_e x y e) (subst_t x y U)
  | d_type L T U => d_type L (subst_t x y T) (subst_t x y U)
end.

Inductive expansion : list (var * type) -> type -> list type_d -> Prop:=
  | E_Rec : forall G D_,
            expansion G (t_rec D_) D_
  | E_Sel : forall G x L S U D_,
            mem G (e_var x) (t_type L S U) ->
            expansion G U D_ ->
            expansion G (t_sel x L) D_

with mem : list (var * type) -> exp -> type_d -> Prop:=
  | M_Path : forall G x T D_ D,
             In (x,T) G ->
             expansion G T D_ ->
             In D D_ ->
             mem G (e_var x) (subst_D self x D)
  | M_Exp : forall G e D_ D,
            .

Inductive sub : list (var * type) -> type -> type -> Prop :=
  | S_Refl : forall G T, sub G T T
  | S_Rec  : forall G D_ D_',
             (forall D, In D D_ -> exists D', In D' D_' /\ sub_d ((self,t_rec D_)::G) D D') ->
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


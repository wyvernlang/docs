Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Set Implicit Arguments.

Scheme type_mutind' := Induction for ty Sort Prop
  with decl_ty_mutind' := Induction for decl_ty Sort Prop
  with decl_tys_mutind' := Induction for decl_tys Sort Prop.

Combined Scheme type_mutind from type_mutind', decl_ty_mutind', decl_tys_mutind'.

Fixpoint raise_list (E : list exp) : list exp :=
  match E with
  | nil => nil
  | e :: E' => (e raise_e 0)::(raise_list E')
  end.

Fixpoint lsubst_t (E : list exp)(n : nat)(t : ty) : ty :=
  match E with
  | nil => t
  | e :: E' => [e /t n](lsubst_t E' (S n) t)
  end.

Fixpoint lsubst_s (E : list exp)(n : nat)(s : decl_ty) : decl_ty :=
  match E with
  | nil => s
  | e :: E' => [e /s n](lsubst_s E' (S n) s)
  end.

Fixpoint lsubst_ss (E : list exp)(n : nat)(ss : decl_tys) : decl_tys :=
  match E with
  | nil => ss
  | e :: E' => [e /ss n](lsubst_ss E' (S n) ss)
  end.

Fixpoint lsubst_e (E : list exp)(n : nat)(e : exp) : exp :=
  match E with
  | nil => e
  | e' :: E' => [e' /e n](lsubst_e E' (S n) e)
  end.

Fixpoint lsubst_d (E : list exp)(n : nat)(d : decl) : decl :=
  match E with
  | nil => d
  | e :: E' => [e /d n](lsubst_d E' (S n) d)
  end.

Fixpoint lsubst_ds (E : list exp)(n : nat)(ds : decls) : decls :=
  match E with
  | nil => ds
  | e :: E' => [e /ds n](lsubst_ds E' (S n) ds)
  end.

Lemma lsubst_ty_sel :
  forall E n p l, (lsubst_t E n (sel p l)) = (sel (lsubst_e E n p) l).
Proof.
  intros E;
    induction E as [|e' E'];
    intros;
    auto.
  
  simpl;
    rewrite IHE';
    auto.
Qed.

Hint Rewrite lsubst_ty_sel.
Hint Resolve lsubst_ty_sel.

Lemma lsubst_ty_top :
  forall E n, (lsubst_t E n top) = top.
Proof.
  intro E;
    induction E;
    auto;
    intros;
    simpl;
    rewrite IHE;
    auto.
Qed.

Hint Rewrite lsubst_ty_top.
Hint Resolve lsubst_ty_top.

Lemma lsubst_ty_bot :
  forall E n, (lsubst_t E n bot) = bot.
Proof.
  intro E;
    induction E;
    auto;
    intros;
    simpl;
    rewrite IHE;
    auto.
Qed.

Hint Rewrite lsubst_ty_bot.
Hint Resolve lsubst_ty_bot.

Lemma lsubst_ty_arr :
  forall E n t1 t2, (lsubst_t E n (t1 arr t2)) = ((lsubst_t E n t1) arr (lsubst_t (raise_list E) (S n) t2)).
Proof.
  intro E;
    induction E as [|e E'];
    intros;
    auto;
    simpl.
  
  rewrite IHE'; 
    auto.
Qed.

Hint Rewrite lsubst_ty_arr.
Hint Resolve lsubst_ty_arr.

Lemma lsubst_ty_str :
  forall E n ss, (lsubst_t E n (str ss rts)) = (str (lsubst_ss (raise_list E) (S n) ss) rts).
Proof.
  intro E;
    induction E as [|e' E'];
    intros;
    simpl;
    auto.

  rewrite IHE';
    auto.
Qed.

Hint Rewrite lsubst_ty_str.
Hint Resolve lsubst_ty_str.

Lemma lsubst_decl_ty_upper :
  forall E n l t, (lsubst_s E n (type l ext t)) = (type l ext (lsubst_t E n t)).
Proof.
  intros E;
    induction E as [|e' E'];
    intros;
    auto.
  
  simpl;
    rewrite IHE';
    auto.
Qed.

Hint Rewrite lsubst_decl_ty_upper.
Hint Resolve lsubst_decl_ty_upper.

Lemma lsubst_decl_ty_lower :
  forall E n l t, (lsubst_s E n (type l sup t)) = (type l sup (lsubst_t E n t)).
Proof.
  intros E;
    induction E as [|e' E'];
    intros;
    auto.
  
  simpl;
    rewrite IHE';
    auto.
Qed.

Hint Rewrite lsubst_decl_ty_lower.
Hint Resolve lsubst_decl_ty_lower.

Lemma lsubst_decl_ty_equal :
  forall E n l t, (lsubst_s E n (type l eqt t)) = (type l eqt (lsubst_t E n t)).
Proof.
  intros E;
    induction E as [|e' E'];
    intros;
    auto.
  
  simpl;
    rewrite IHE';
    auto.
Qed.

Hint Rewrite lsubst_decl_ty_equal.
Hint Resolve lsubst_decl_ty_equal.

Lemma lsubst_decl_ty_value :
  forall E n l t, (lsubst_s E n (val l oft t)) = (val l oft (lsubst_t E n t)).
Proof.
  intros E;
    induction E as [|e' E'];
    intros;
    auto.
  
  simpl;
    rewrite IHE';
    auto.
Qed.

Hint Rewrite lsubst_decl_ty_value.
Hint Resolve lsubst_decl_ty_value.

Lemma lsubst_nil :
  forall E n, (lsubst_ss E n (dt_nil)) = dt_nil.
Proof.
  intro E;
    induction E as [|e E'];
    intros;
    auto;
    simpl.
  
  rewrite IHE'; 
    auto.
Qed.

Hint Rewrite lsubst_nil.
Hint Resolve lsubst_nil.

Lemma lsubst_decl_tys_con :
  forall E n s ss, (lsubst_ss E n (dt_con s ss)) = (dt_con (lsubst_s E n s) (lsubst_ss E n ss)).
Proof.
  intro E;
    induction E as [|e E'];
    intros;
    auto;
    simpl.
  
  rewrite IHE'; 
    auto.
Qed.

Hint Rewrite lsubst_decl_tys_con.
Hint Resolve lsubst_decl_tys_con.


Lemma subtype_reflexivity_mutind :
  (forall t E Sig G1 G2, length G1 = length G2 -> Sig en G1 vdash (lsubst_t E 0 t) <; (lsubst_t E 0 t) dashv G2) /\
  (forall s E Sig G1 G2, length G1 = length G2 -> Sig en G1 vdash (lsubst_s E 0 s) <;; (lsubst_s E 0 s) dashv G2) /\
  (forall ss E Sig G1 G2, length G1 = length G2 -> Sig en G1 vdash (lsubst_ss E 0 ss) <;;; (lsubst_ss E 0 ss) dashv G2).
Proof.
  apply type_mutind;
    intros;
    simpl;
    auto;
    try solve [rewrite lsubst_ty_sel;
               auto];
    try solve [rewrite lsubst_ty_top;
               auto];
    try solve [rewrite lsubst_ty_bot;
               auto];
    try solve [rewrite lsubst_decl_ty_upper;
               auto];
    try solve [rewrite lsubst_decl_ty_lower;
               auto];
    try solve [rewrite lsubst_decl_ty_equal;
               auto];
    try solve [rewrite lsubst_decl_ty_value;
               auto];
    try solve [rewrite lsubst_nil;
               auto];
    try solve [rewrite lsubst_decl_tys_con;
               auto].

  (*str*)
  rewrite lsubst_ty_str.
  apply s_struct with (i:= length G1);
    auto;
    simpl.
  assert (Hsub : (length (str (lsubst_ss (raise_list E) 1 d) rts :: G1)) =
                 (length (str (lsubst_ss (raise_list E) 1 d) rts :: G2)));
    [simpl
    |apply H
       with
         (E:=(c_ (length G1))::(raise_list E))
         (Sig:=Sig)
      in Hsub;
    simpl in Hsub];
    auto.

  (*arr*)
  rewrite lsubst_ty_arr.
  apply s_arr with (i:=length G1);
    auto;
    simpl.
  assert (Hsub : (length ((lsubst_t E 0 t) :: G1)) =
                 (length ((lsubst_t E 0 t) :: G2)));
    [simpl
    |apply H0
       with
         (E:=(c_ (length G1))::(raise_list E))
         (Sig:=Sig)
      in Hsub;
    simpl in Hsub];
    auto.
Qed.

Lemma subtype_reflexivity :
  forall Sig G1 t G2, length G1 = length G2 ->
               Sig en G1 vdash t <; t dashv G2.
Proof.
  intros.
  destruct subtype_reflexivity_mutind as [Ha Hb].
  apply Ha
    with
      (t:=t)
      (E:=nil)
      (Sig:=Sig)
    in H;
    simpl in Ha;
    auto.
Qed.
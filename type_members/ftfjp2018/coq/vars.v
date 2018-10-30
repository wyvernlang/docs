Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Require Import common.
Require Import weakening.
Require Import strengthening.
Require Import subst.
Set Implicit Arguments.


Reserved Notation "Sig 'en' G 'vdash' p 'ni_w' s" (at level 80).
Reserved Notation "s 'cont_w' t" (at level 80).


Inductive struct_contains : ty -> decl_ty -> Prop :=
| cont_wf : forall ss s, in_dty s ss ->
                    s cont_w (str ss)
where "s 'cont_w' t" := (struct_contains t s).


Inductive alt_has : env -> env -> exp -> decl_ty -> Prop :=
| h_struct : forall Sig G p ss s, Sig en G vdash p pathType (str ss) ->
                           s cont_w (str ss) ->
                           Sig en G vdash p ni_w ([p /s 0] s)
| h_upper : forall Sig G p p' l' t s, Sig en G vdash p pathType (sel p' l') ->
                               Sig en G vdash p' ni_w (type l' ext t) ->
                               Sig en G vdash (p cast t) ni_w s ->
                               Sig en G vdash p ni_w s
| h_equal : forall Sig G p p' l' t s, Sig en G vdash p pathType (sel p' l') ->
                               Sig en G vdash p' ni_w (type l' eqt t) ->
                               Sig en G vdash (p cast t) ni_w s ->
                               Sig en G vdash p ni_w s
where "Sig 'en' G 'vdash' p 'ni_w' s" := (alt_has Sig G p s).


Hint Constructors alt_has struct_contains.

Lemma struct_contains_implies_contains :
  (forall Sig G t s, s cont_w t ->
              Sig en G vdash s cont t).
Proof.
  intros;
    inversion H;
    subst;
    auto.
Qed.

Lemma path_typing_is_path :
  forall Sig G p t, Sig en G vdash p pathType t ->
             is_path p.
Proof.
  intros Sig G p t Htyp;
    induction Htyp;
    auto.
Qed.

Hint Resolve path_typing_is_path.

Lemma closed_struct_contains :
  forall s t n, s cont_w t ->
           closed_ty t n ->
           closed_decl_ty s (S n).
Proof.
  intros.
  inversion H; subst.
  apply closed_in_dty with (ss:=ss);
    auto.
  eapply closed_ty_str; eauto.
Qed.

Lemma closed_alt_has :
  forall Sig G p s, Sig en G vdash p ni_w s ->
             closed_exp p 0 ->
             closed_env Sig 0 ->
             closed_env G 0 ->
             closed_decl_ty s 0.
Proof.
  intros Sig G p s Hhas;
    induction Hhas;
    intros.

  (*struct*)
  apply closed_subst_hole_decl_ty;
    auto.
  eapply closed_struct_contains;
    eauto.
  eapply closed_typing_p;
    eauto.

  (*upper*)
  apply IHHhas2;
    auto.
  apply closed_exp_cast;
    split;
    auto.
  apply closed_decl_ty_upper
    with (L:=l').
  apply IHHhas1;
    auto.
  eapply closed_ty_sel with (l:=l'); eauto.
  eapply closed_typing_p; eauto.

  (*equal*)
  apply IHHhas2;
    auto.
  apply closed_exp_cast;
    split;
    auto.
  apply closed_decl_ty_equal
    with (L:=l').
  apply IHHhas1;
    auto.
  eapply closed_ty_sel with (l:=l'); eauto.
  eapply closed_typing_p; eauto.
Qed.

Lemma raise_n_0 :
  forall n, (n raise_n 0) = S n.
Proof.
  intros;
    unfold raise_nat;
    assert (Hnlt : ~ n < 0);
    [crush
    |apply Nat.ltb_nlt in Hnlt;
     rewrite Hnlt;
     rewrite Nat.add_1_r;
     auto].
Qed.

Lemma subst_same_mutind :
  (forall t p1 p2 n, ([p1 /t n]([p2 /t n] t)) = ([[p1 /e n] p2 /t n] t)) /\

  (forall s p1 p2 n, ([p1 /s n]([p2 /s n] s)) = ([[p1 /e n] p2 /s n] s)) /\

  (forall ss p1 p2 n, ([p1 /ss n]([p2 /ss n] ss)) = ([[p1 /e n] p2 /ss n] ss)) /\

  (forall e p1 p2 n, ([p1 /e n]([p2 /e n] e)) = ([[p1 /e n] p2 /e n] e)) /\

  (forall d p1 p2 n, ([p1 /d n]([p2 /d n] d)) = ([[p1 /e n] p2 /d n] d)) /\

  (forall ds p1 p2 n, ([p1 /ds n]([p2 /ds n] ds)) = ([[p1 /e n] p2 /ds n] ds)).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               rewrite H;
               try (rewrite H0);
               try (rewrite H1);
               try (rewrite raise_subst_distr_exp);
               try (rewrite raise_n_0);
               auto].

  destruct v as [x|x];
    simpl; auto.
  destruct (Nat.eq_dec n x) as [Heq|Heq];
    [subst;
     rewrite <- beq_nat_refl;
     auto
    |apply Nat.eqb_neq in Heq;
     rewrite Heq;
     simpl;
     rewrite Heq;
     auto].
Qed.

Lemma subst_same_type :
  (forall t p1 p2 n, ([p1 /t n]([p2 /t n] t)) = ([[p1 /e n] p2 /t n] t)).
Proof.
  destruct subst_same_mutind; crush.
Qed.

Lemma subst_same_decl_ty :
  (forall s p1 p2 n, ([p1 /s n]([p2 /s n] s)) = ([[p1 /e n] p2 /s n] s)).
Proof.
  destruct subst_same_mutind; crush.
Qed.

Lemma subst_same_var_decl_tys :
  (forall ss p1 p2 n, ([p1 /ss n]([p2 /ss n] ss)) = ([[p1 /e n] p2 /ss n] ss)).
Proof.
  destruct subst_same_mutind; crush.
Qed.

Lemma subst_same_exp :
  (forall e p1 p2 n, ([p1 /e n]([p2 /e n] e)) = ([[p1 /e n] p2 /e n] e)).
Proof.
  destruct subst_same_mutind; crush.
Qed.

Lemma subst_same_decl :
  (forall d p1 p2 n, ([p1 /d n]([p2 /d n] d)) = ([[p1 /e n] p2 /d n] d)).
Proof.
  destruct subst_same_mutind; crush.
Qed.

Lemma subst_same_var_decls :
  (forall ds p1 p2 n, ([p1 /ds n]([p2 /ds n] ds)) = ([[p1 /e n] p2 /ds n] ds)).
Proof.
  destruct subst_same_mutind; crush.
Qed.

Lemma has_contains_equivalence_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              closed_exp p 0 ->
              closed_decl_ty s 0 ->
              closed_env G 0 ->
              closed_env Sig 0 ->
              Sig en G vdash p ni_w s) /\
  (forall Sig G t s, Sig en G vdash s cont t ->
              forall p, Sig en G vdash p pathType t ->
                   closed_ty t 0 ->
                   closed_env G 0 ->
                   closed_env Sig 0 ->
                   Sig en G vdash p ni_w ([p /s 0]s)).
Proof.
  apply has_contains_mutind;
    intros.

  (*has path*)
  apply H;
    auto.
  eapply closed_typing_p;
    eauto.
  
  (*cont struct*)
  eapply h_struct;
    eauto.

  (*cont upper*)
  assert (Hclosed_p : closed_exp p 0);
    [eapply closed_ty_sel;
     eauto
    |].
  assert (Hclosed_Lt : closed_decl_ty (type L ext t) 0);
    [eapply closed_has;
     eauto
    |].
  assert (Hclosed_t : closed_ty t 0);
    [eapply closed_decl_ty_upper;
     eauto
    |].
  rewrite subst_same_decl_ty.
  simpl.
  rewrite closed_subst_type;
    auto.
  eapply h_upper;
    eauto.

  (*equal*)
  assert (Hclosed_p : closed_exp p 0);
    [eapply closed_ty_sel;
     eauto
    |].
  assert (Hclosed_Lt : closed_decl_ty (type L eqt t) 0);
    [eapply closed_has;
     eauto
    |].
  assert (Hclosed_t : closed_ty t 0);
    [eapply closed_decl_ty_equal;
     eauto
    |].
  rewrite subst_same_decl_ty.
  simpl.
  rewrite closed_subst_type;
    auto.
  eapply h_equal;
    eauto.
Qed.

Lemma alt_has_implies_has :
  forall Sig G p s, Sig en G vdash p ni_w s ->
             closed_exp p 0 ->
             closed_env Sig 0 ->
             closed_env G 0 ->
             Sig en G vdash p ni s.
Proof.
  intros Sig G p s Hni;
    induction Hni;
    intros;
    auto.

  (*struct*)
  apply has_path with (t:=str ss);
    auto.
  apply struct_contains_implies_contains;
    auto.

  (*upper*)
  assert (Hclosed_p' : closed_exp p' 0);
    [eapply closed_ty_sel;
     eapply closed_typing_p;
     eauto|].
  assert (Hclosed_lt : closed_decl_ty (type l' ext t) 0);
    [eapply closed_alt_has;
     eauto|].
  assert (Hclosed_t : closed_ty t 0);
    [eapply closed_decl_ty_upper;
     eauto|].
  assert (Hhas1 : Sig en G vdash p cast t ni s);
    [apply IHHni2;
     auto;
     eapply closed_exp_cast;
     eauto|].
    inversion Hhas1;
    subst.
  inversion H3;
    subst t0;
    subst.
  assert (Hrewrite1 : (p cast t) = ([p /e 0]((a_ 0) cast t)));
    [simpl;
     rewrite closed_subst_type;
     auto
    |rewrite Hrewrite1;
     rewrite <- subst_same_decl_ty].
  apply has_path with (t:=sel p' l');
  auto.

  (*equal*)
  assert (Hclosed_p' : closed_exp p' 0);
    [eapply closed_ty_sel;
     eapply closed_typing_p;
     eauto|].
  assert (Hclosed_lt : closed_decl_ty (type l' eqt t) 0);
    [eapply closed_alt_has;
     eauto|].
  assert (Hclosed_t : closed_ty t 0);
    [eapply closed_decl_ty_equal;
     eauto|].
  assert (Hhas1 : Sig en G vdash p cast t ni s);
    [apply IHHni2;
     auto;
     eapply closed_exp_cast;
     eauto|].
    inversion Hhas1;
    subst.
  inversion H3;
    subst t0;
    subst.
  assert (Hrewrite1 : (p cast t) = ([p /e 0]((a_ 0) cast t)));
    [simpl;
     rewrite closed_subst_type;
     auto
    |rewrite Hrewrite1;
     rewrite <- subst_same_decl_ty].
  apply has_path with (t:=sel p' l');
  auto.
Qed.

Lemma in_dty_wf :
  forall s ss, in_dty s ss ->
          forall Sig G, Sig en G vdash ss wf_ss ->
                 Sig en G vdash s wf_s.
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    auto;
    inversion H;
    subst;
    auto.
Qed.

Lemma subst_in_dty :
  forall s ss, in_dty s ss ->
          forall p n, in_dty ([p /s n] s) ([p /ss n]ss).
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    auto.

  apply in_head_dty.

  simpl; apply in_tail_dty;
    auto.
Qed.

Lemma struct_contains_wf' :
  forall Sig G t, Sig en G vdash t wf_t ->
           forall s, s cont_w t ->
                Sig en t::G vdash [c_ (length G) /s 0]s wf_s.
Proof.
  intros.
  inversion H0;
    subst.
  inversion H;
    subst.
  eapply in_dty_wf; eauto.
  apply subst_in_dty;
    auto.
Qed.

Definition unbound_in_dty := strengthening_utils.unbound_in_dty.

Lemma struct_contains_wf :
  forall Sig G t, Sig en G vdash t wf_t ->
           Sig wf_st ->
           Sig evdash G wf_env ->
           forall s, s cont_w t ->
                forall p, Sig en G vdash p pathType t ->
                     Sig en G vdash p wf_e ->
                     Sig en G vdash [p /s 0]s wf_s.
Proof.
  intros.
  inversion H2; subst.
  inversion H; subst.
  apply subst_in_dty
    with
      (p:=c_ (length G))(n:=0)
    in H5.
  apply in_dty_wf
    with
      (Sig:=Sig)(G:=str ss::G)
    in H5;
    auto.
  apply wf_subst_decl_ty_actual
    with
      (p:=p)
    in H5;
    auto.

  apply wf_con;
    auto.
  
  apply unbound_in_dty with (ss:=ss);
    inversion H2;
    auto.
Qed.

Lemma path_typing_wf :
  forall Sig G p t, Sig en G vdash p pathType t ->
             Sig wf_st ->
             Sig evdash G wf_env ->
             Sig en G vdash p wf_e ->
             Sig en G vdash t wf_t.
Proof.
  intros Sig G p t Htyp;
    induction Htyp;
    intros;
    auto.

  apply wf_in_env;
    auto.
  eapply in_rev, get_in;
    eauto.

  apply wf_in_store_type;
    auto.
  eapply in_rev, get_in;
    eauto.

  inversion H2;
    eauto.
Qed.

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
  forall E n ss, (lsubst_t E n (str ss)) = (str (lsubst_ss (raise_list E) (S n) ss)).
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
  assert (Hsub : (length (str (lsubst_ss (raise_list E) 1 d) :: G1)) =
                 (length (str (lsubst_ss (raise_list E) 1 d) :: G2)));
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

Lemma alt_has_wf :
  (forall Sig G p s, Sig en G vdash p ni_w s ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash p wf_e ->
              Sig en G vdash s wf_s).
Proof.
  intros Sig G p s Hni;
    induction Hni;
    intros;
    auto.

  (*struct*)
  apply struct_contains_wf with (t:=str ss);
    auto.
  eapply path_typing_wf;
    eauto.

  (*upper*)
  apply IHHni2;
    auto.
  assert (HwfSel : Sig en G vdash sel p' l' wf_t);
    [apply path_typing_wf in H;
     auto|].
  assert (Hwfp' : Sig en G vdash p' wf_e);
    [inversion HwfSel;
     auto
    |].
  assert (HwfUpper : Sig en G vdash type l' ext t wf_s);
    [apply IHHni1;
     auto;
     inversion HwfSel;
     auto
    |].
  apply wf_cast with (t':=sel p' l');
    eauto;
    [inversion HwfUpper;
     auto
    |apply path_typing_implies_typing;
     auto
    |].
  apply s_upper with (t1:=t);
    auto.
  apply alt_has_implies_has;
    auto.
  intros n' Hle;
    eapply wf_closed_exp;
    eauto.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  apply subtype_reflexivity;
    auto.

  (*equal*)
  apply IHHni2;
    auto.
  assert (HwfSel : Sig en G vdash sel p' l' wf_t);
    [apply path_typing_wf in H;
     auto|].
  assert (Hwfp' : Sig en G vdash p' wf_e);
    [inversion HwfSel;
     auto
    |].
  assert (HwfEqual : Sig en G vdash type l' eqt t wf_s);
    [apply IHHni1;
     auto;
     inversion HwfSel;
     auto
    |].
  apply wf_cast with (t':=sel p' l');
    eauto;
    [inversion HwfEqual;
     auto
    |apply path_typing_implies_typing;
     auto
    |].
  apply s_equal1 with (t1:=t);
    auto.
  apply alt_has_implies_has;
    auto.
  intros n' Hle;
    eapply wf_closed_exp;
    eauto.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  apply subtype_reflexivity;
    auto.
Qed.


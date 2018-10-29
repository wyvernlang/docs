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

Lemma struct_contains_wf :
  forall Sig G t, Sig en G vdash t wf_t ->
           forall s, s cont_w t ->
                forall p, Sig en G vdash p pathType t ->
                     Sig en t::G vdash [p /s 0]s wf_s.
Proof.
  intros.
  
  
Qed.
  

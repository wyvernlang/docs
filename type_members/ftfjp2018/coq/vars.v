Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Require Import common.
Require Import weakening.
Require Import subst.
Require Import strengthening.
Set Implicit Arguments.

Lemma wf_contains_implies_contains :
  (forall Sig G t s, Sig en G vdash s cont_w t ->
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

Lemma bleh :
  (forall Sig G p s, Sig en G vdash p ni_w s ->
              forall t, Sig en G vdash p pathType t ->
                   closed_exp p 0 ->
                   closed_ty t 0 ->
                   closed_env G 0 ->
                   closed_env Sig 0 ->
                   exists s', Sig en G vdash s' cont t /\
                         s = ([p /s 0] s')).
Proof.
  intros Sig G p s Hni;
    induction Hni;
    intros.

  (*struct*)
  exists s;
    split; auto.
  apply wf_contains_implies_contains;
    auto.
  apply path_typing_uniqueness with (t:=str ss) in H1;
    auto;
    subst t;
    auto.

  (*upper*)
  destruct IHHni2
    with
      (t0:=t)
    as [s' Ha];
    auto.

  apply pt_cast; eauto.
  apply closed_typing_p with (m:=0) in H;
    auto.
  eapply closed_exp_cast; split; eauto.
  
  
Qed.

  
Lemma wf_has_implies_has :
  (forall Sig G p s, Sig en G vdash p ni_w s ->
              Sig en G vdash p ni s).
Proof.
  intros Sig G p s Hni;
    induction Hni;
    intros;
    auto.

  (*struct*)
  apply has_path with (t:=str ss);
    auto.
  apply wf_contains_implies_contains;
    auto.

  (*upper*)
  
  
Qed.
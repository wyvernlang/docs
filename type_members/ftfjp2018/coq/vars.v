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
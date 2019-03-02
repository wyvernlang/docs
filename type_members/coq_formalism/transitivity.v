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

Inductive monotonic : env -> env -> env -> env -> Prop :=
| mon_nil : forall Sig, monotonic Sig nil nil nil
| mon_cons1 : forall Sig t1 G1 t2 G2 t3 G3, Sig en G1 vdash t1 <; t2 dashv G2 ->
                                     Sig en G2 vdash t2 <; t3 dashv G3 ->
                                     monotonic Sig G1 G2 G3 ->
                                     monotonic Sig (t1::G1) (t2::G2) (t3::G3)
| mon_cons2 : forall Sig t1 G1 t2 G2 t3 G3, Sig en G3 vdash t3 <; t2 dashv G2 ->
                                     Sig en G2 vdash t2 <; t1 dashv G1 ->
                                     monotonic Sig G1 G2 G3 ->
                                     monotonic Sig (t1::G1) (t2::G2) (t3::G3).

Inductive concrete_ub : env -> env -> ty -> ty -> Prop :=
| cub_top : forall Sig G, concrete_ub Sig G top top
| cub_bot : forall Sig G, concrete_ub Sig G bot bot
| cub_upp : forall Sig G p l t t', Sig en G vdash p ni (type l ext t) ->
                           concrete_ub Sig G t t' ->
                           concrete_ub Sig G (sel p l) t'
| cub_equ : forall Sig G p l t t', Sig en G vdash p ni (type l eqt t) ->
                           concrete_ub Sig G t t' ->
                           concrete_ub Sig G (sel p l) t'
| cub_arr : forall Sig G t1 t2, concrete_ub Sig G (t1 arr t2) (t1 arr t2)
| cub_str : forall Sig G ss, concrete_ub Sig G (str ss rts) (str ss rts).

Inductive concrete_env : env -> env -> env -> Prop :=
| cub_nil : forall Sig, concrete_env Sig nil nil
| cub_cons : forall Sig G G' t t', concrete_ub Sig G t t' ->
                            concrete_env Sig G G' ->
                            concrete_env Sig (t::G) (t'::G').

Lemma concrete_env_subtyping :
  (forall Sig G1 t1 t2 G2, ).

Lemma subtype_transitivity :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    forall G3 t3, Sig en G2 vdash t2 <; t3 dashv G3 ->
                             balanced Sig G1 G2 G3 ->
                             Sig en G1 vdash t1 <; t3 dashv G3).
Proof.
  intros Sig G1 t1 t2 G3 Hsub;
    induction Hsub;
    intros;
    auto.

  (*s-top*)
  intros.
  admit.

  (*s-refl*)
  remember (sel p L) as t'.
  induction H;
    auto;
    try solve [inversion Heqt'].
  inversion Heqt';
    subst.
  

  
Qed.
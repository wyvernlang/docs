Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Require Import common.
Require Import refl.
Require Import member_uniqueness.
Require Import weakening.
Set Implicit Arguments.

Inductive upp : env -> env -> ty -> ty -> Prop :=
| up_top : forall Sig G, upp Sig G top top
| up_bot : forall Sig G, upp Sig G bot bot
| up_refl : forall Sig G p l, upp Sig G (sel p l) (sel p l)
| up_upp : forall Sig G p l t t', Sig en G vdash p ni (type l ext t) ->
                           upp Sig G t t' ->
                           upp Sig G (sel p l) t'
| up_equ : forall Sig G p l t t', Sig en G vdash p ni (type l eqt t) ->
                           upp Sig G t t' ->
                           upp Sig G (sel p l) t'
| up_low : forall Sig G p l t, Sig en G vdash p ni (type l sup t) ->
                        upp Sig G (sel p l) top
| up_arr : forall Sig G t1 t2, upp Sig G (t1 arr t2) (t1 arr t2)
| up_str : forall Sig G ss, upp Sig G (str ss rts) (str ss rts).


Inductive low : env -> env -> ty -> ty -> Prop :=
| lo_top : forall Sig G, low Sig G top top
| lo_bot : forall Sig G, low Sig G bot bot
| lo_refl : forall Sig G p l, low Sig G (sel p l) (sel p l)
| lo_low : forall Sig G p l t t', Sig en G vdash p ni (type l sup t) ->
                           low Sig G t t' ->
                           low Sig G (sel p l) t
| lo_equ : forall Sig G p l t t', Sig en G vdash p ni (type l eqt t) ->
                           low Sig G t t' ->
                           low Sig G (sel p l) t'
| lo_upp : forall Sig G p l t, Sig en G vdash p ni (type l ext t) ->
                          low Sig G (sel p l) bot
| lo_arr : forall Sig G t1 t2, low Sig G (t1 arr t2) (t1 arr t2)
| lo_str : forall Sig G ss, low Sig G (str ss rts) (str ss rts).

Hint Constructors upp low.

Lemma upper_bound_super_type :
  forall Sig G t1 t2, upp Sig G t1 t2 ->
               Sig en G vdash t1 <; t2 dashv G.
Proof.
  intros.
  induction H; auto;
    try solve [apply subtype_reflexivity;
               auto].

  apply s_upper1 with (t1:=t);
    auto.

  apply s_equal1 with (t1:=t);
    auto.
Qed.

Lemma upper_bound_refl :
  forall t Sig G, upp Sig G t t.
Proof.
  intros t;
    destruct t;
    intros;
    auto.
Qed.

Lemma super_top :
  forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                   t1 = top ->
                   forall t, Sig en G1 vdash t <; t2 dashv G2.
Proof.
  intros Sig G1 t1 t2 G2 Hsub;
    induction Hsub;
    intros;
    auto;
    try solve [inversion H];
    try solve [inversion H0];
    try solve [inversion H1];
    try solve [inversion H2].

  apply IHHsub
    with
      (t:=t)
    in H0;
    auto.
  apply s_lower1 with (t2:=t2);
    auto.

  apply IHHsub
    with
      (t:=t)
    in H0.
  apply s_lower2 with (t2:=t2);
    auto.

  apply IHHsub
    with
      (t:=t)
    in H0.
  apply s_equal2 with (t2:=t2);
    auto.

  apply IHHsub
    with
      (t:=t)
    in H0.
  apply s_equal4 with (t2:=t2);
    auto.
Qed.

Lemma upp_subtype_mutind :
  (forall Sig G1 t1 t1', upp Sig G1 t1 t1' ->
                  forall G2 t2, Sig en G1 vdash t1' <; t2 dashv G2 ->
                           Sig en G1 vdash t1 <; t2 dashv G2).
Proof.
  intros Sig G1 t1 t1' Hupp;
    induction Hupp;
    intros;
    auto.

  apply s_upper1 with (t1:=t);
    auto.

  apply s_equal1 with (t1:=t);
    auto.

  apply super_top
    with
      (t:=sel p l)
    in H0;
    auto.
Qed.

Lemma sub_bot :
  forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                   t2 = bot ->
                   forall t, Sig en G1 vdash t1 <; t dashv G2.
Proof.
  intros Sig G1 t1 t2 G2 Hsub;
    induction Hsub;
    intros;
    eauto;
    try solve [inversion H];
    try solve [inversion H0];
    try solve [inversion H1];
    try solve [inversion H2].
Qed.

Lemma upper_bound_contains :
  forall Sig G t1 t2, upp Sig G t1 t2 ->
               mem_unique_ctx Sig ->
               mem_unique_ctx G ->
               mem_unique t1 ->
               forall s, Sig en G vdash s cont t1 <->
                    Sig en G vdash s cont t2.
Proof.
  intros Sig G t1 t2 Hupp;
    induction Hupp;
    intros; split;
      intros Hcont;
      auto;
      try solve [inversion Hcont].

  inversion Hcont;
    subst.
  apply unique_has with (s:=type l ext t) in H7;
    auto;
    [|inversion H2; auto].
  inversion H7;
    subst t0.
  apply IHHupp;
    auto.
  apply mem_unique_has in H;
    auto;
    [|inversion H2; auto].
  inversion H;
    auto.
  apply unique_has with (s:=type l ext t) in H7;
    auto.
  inversion H7.
  inversion H2;
    auto.

  eapply cont_upper;
    eauto.
  apply IHHupp;
    auto.
  apply mem_unique_has in H;
    auto;
    [|inversion H2; auto].
  inversion H;
    auto.

  inversion Hcont;
    subst.
  apply unique_has with (s:=type l eqt t) in H7;
    auto;
    [|inversion H2; auto].
  inversion H7;
    subst t0.
  apply unique_has with (s:=type l eqt t) in H7;
    auto;
    [|inversion H2; auto].
  inversion H7;
    subst t0.
  apply IHHupp;
    auto.
  apply mem_unique_has in H;
    auto;
    [|inversion H2; auto].
  inversion H;
    auto.

  eapply cont_equal;
    eauto.
  apply IHHupp;
    auto.
  apply mem_unique_has in H;
    auto;
    [|inversion H2; auto].
  inversion H;
    auto.

  inversion Hcont;
    subst.
  apply unique_has with (s:=type l sup t) in H7;
    auto;
    [inversion H7|inversion H2; auto].
  apply unique_has with (s:=type l sup t) in H7;
    auto;
    [inversion H7|inversion H2; auto].

Qed.

Lemma upper_bound_implies_type_contains :
  forall Sig G t1 t2, upp Sig G t1 t2 ->
               mem_unique_ctx Sig ->
               mem_unique_ctx G ->
               mem_unique t1 ->
               forall s, Sig en G vdash s cont t2 ->
                    Sig en G vdash s cont t1.
Proof.
  intros.
  apply <- upper_bound_contains;
    eauto.
Qed.

Lemma type_implies_upper_bound_contains :
  forall Sig G t1 t2, upp Sig G t1 t2 ->
               mem_unique_ctx Sig ->
               mem_unique_ctx G ->
               mem_unique t1 ->
               forall s, Sig en G vdash s cont t1 ->
                    Sig en G vdash s cont t2.
Proof.
  intros.
  apply -> upper_bound_contains;
    eauto.
Qed.

Lemma upper_bound_weakening :
  (forall Sig G t1 t2, upp Sig G t1 t2 ->
    forall G1 G2, G = G1 ++ G2 ->
             forall i n G', i = length G2 ->
                       n = length G' ->
                       upp (Sig [i] rjump_env n) ((G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n)) (t1 [i] rjump_t n) (t2 [i] rjump_t n)).
Proof.
  intros Sig G t1 t2 Hupp;
    induction Hupp;
    intros;
    auto.

  (*refl*)
  apply up_refl.

  (*upp*)
  simpl; apply up_upp with (t:=t [i] rjump_t n);
    auto.
  apply has_weakening with (G1:=G1)(G2:=G2)
                           (i:=i)(n:=n)
                           (G':=G')in H;
    auto.

  (*equ*)
  simpl; apply up_equ with (t:=t [i] rjump_t n);
    auto.
  apply has_weakening with (G1:=G1)(G2:=G2)
                           (i:=i)(n:=n)
                           (G':=G')in H;
    auto.
  
  (*low*)
  simpl; apply up_low with (t:=t [i] rjump_t n);
    auto.
  apply has_weakening with (G1:=G1)(G2:=G2)
                           (i:=i)(n:=n)
                           (G':=G')in H;
    auto.

  (*arr*)
  apply up_arr.

  (*str*)
  apply up_str.
Qed.

Lemma upper_bound_weakening_actual :
  forall Sig G t1 t2, upp Sig G t1 t2 ->
               lt_ctx Sig (length G) ->
               lt_env G (length G) ->
               lt_t t1 (length G) ->
               lt_t t2 (length G) ->
               forall G', upp Sig (G'++G) t1 t2.
Proof.
  intros.
  (*assert (Hwft1 : Sig en G vdash t1 wf_t); [auto|].
  assert (Hwft2 : Sig en G vdash t2 wf_t); [auto|].*)
  apply upper_bound_weakening with (G1:=nil)(G2:=G)
                           (G':=G')(i:=length G)
                           (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H; auto.
  rewrite lt_rjump_env in H; auto.
  rewrite lt_rjump_type in H; auto.
  rewrite lt_rjump_type in H; auto.
Qed.

Lemma upper_bound_weakening_cons :
  forall Sig G t1 t2, upp Sig G t1 t2 ->
               lt_ctx Sig (length G) ->
               lt_env G (length G) ->
               lt_t t1 (length G) ->
               lt_t t2 (length G) ->
               forall t, upp Sig (t::G) t1 t2.
Proof.
  intros.
  apply upper_bound_weakening_actual with (G':=t :: nil) in H; auto.
Qed.

Lemma wf_sub_environment :
  forall Sig G, Sig evdash G wf_env ->
         Sig wf_st ->
         forall G1 G2, G = G1 ++ G2 ->
                  Sig evdash G2 wf_env.
Proof.
  intros Sig G Hwf;
    induction Hwf;
    intros.

  destruct G1;
    [simpl in H0; subst; apply wf_nil|inversion H0].

  destruct G1;
    [simpl in H1; subst; auto|].
  apply wf_con; auto.
  inversion H1; subst t0.
  apply IHHwf with (G1:=G1); auto.
Qed.

Lemma lt_sub_environment :
  forall G, lt_env G (length G) ->
       forall G1 G2, G = G1 ++ G2 ->
                lt_env G2 (length G2).
Proof.
  intros G; induction G as [|t G']; intros.

  destruct G1; [simpl in H0; subst; auto|inversion H0].

  destruct G1; simpl in H0; subst.

  simpl in *; inversion H; subst.
  apply lt_cons; auto.

  inversion H0; subst.
  apply IHG' with (G3:=G1); simpl in *; inversion H; auto.
Qed.

Lemma app_mid_cons :
  forall {A : Type} (a : A) (l1 l2 : list A), (l1 ++ (a :: l2)) = ((l1 ++ (a::nil)) ++ l2).
Proof.
  intros A a l1;
    induction l1 as [|a' l1'];
    auto;
    intros.

  simpl.
  rewrite IHl1'; auto.
Qed.

Lemma limited_narrowing_path_typing :
  forall Sig G p t, Sig en G vdash p pathType t ->
             lt_ctx Sig 0 ->
             lt_env G (length G) ->
             forall G1 G2 t1,
               G = G1 ++ (t1::G2) ->
               forall t2, upp Sig G2 t2 t1 ->
                     lt_t t2 (length G2) ->
                     exists t', Sig en G1 ++ (t2::G2) vdash p pathType t' /\
                           upp Sig (G1 ++ (t2::G2)) t' t.
Proof.
  intros.
  inversion H;
    subst.

  (*var*)
  unfold mapping in H5.
  rewrite rev_app_distr in H5.
  destruct get_some_app
    with
      (G1:=rev(t1::G2))
      (G2:=rev G1)(n:=n)
    as [Ha|Ha];
    destruct Ha as [Ha Hb].

  simpl in Ha, Hb.
  destruct get_some_app
    with
      (G1:=rev G2)
      (G2:=t1::nil)
      (n:=n)
    as [Hc|Hc];
    destruct Hc as [Hc Hd].
  exists t;
    split;
    [|apply upper_bound_refl].
  apply pt_var.
  unfold mapping.
  rewrite rev_app_distr; simpl.
  repeat rewrite get_app_l;
    auto.
  rewrite Hd in Hb;
    simpl in H5;
    rewrite Hb in H5;
    auto.
  rewrite app_length;
    simpl.
  rewrite app_length in Ha;
    auto.

  assert (Hn : n = length (rev G2));
    [rewrite app_length in Ha;
     simpl in Ha;
     crush|].
  exists t2;
    split.
  apply pt_var.
  unfold mapping.
  rewrite rev_app_distr.
  rewrite get_app_l;
    [
    |simpl;
     simpl in Ha;
     rewrite app_length;
     rewrite app_length in Ha;
     simpl in *;
     auto].
  simpl;
    rewrite get_app_r;
    auto.
  subst n.
  rewrite Nat.sub_diag;
    simpl;
    auto.

  simpl in H5;
    rewrite Hb in H5;
    rewrite Hd in H5.
  subst n;
    rewrite Nat.sub_diag in H5;
    simpl in H5;
    inversion H5;
    subst t.

  apply upper_bound_weakening_actual; auto.
  apply upper_bound_weakening_cons; auto.
  apply lt_n_ge_ctx with (n:=0); crush.
  apply lt_sub_environment with (G1:=G1)(G2:=t1::G2) in H1; auto.
  simpl in H1; inversion H1; subst; auto.
  apply lt_sub_environment with (G1:=G1)(G2:=t1::G2) in H1; auto.
  simpl in H1; inversion H1; subst; auto.
  apply lt_n_ge_ctx with (n:=0); crush.
  apply lt_sub_environment with (G1:=G1)(G2:=t1::G2) in H1; auto.
  simpl in H1; inversion H1; subst.
  simpl; apply lt_cons; auto.
  simpl; apply lt_n_ge_type with (n:=length G2); crush.
  apply lt_sub_environment with (G1:=G1)(G2:=t1::G2) in H1; auto.
  simpl in H1; inversion H1; subst.
  simpl; apply lt_n_ge_type with (n:=length G2); crush.
  
  exists t;
    split;
    [|apply upper_bound_refl].
  apply pt_var.
  unfold mapping.
  rewrite rev_app_distr; simpl.
  rewrite get_app_r;
    [
    |rewrite app_length;
     simpl in *;
     rewrite app_length in Ha;
     simpl in Ha;
     auto].
  rewrite Hb in H5;
    auto.
  simpl in H5;
    rewrite app_length in H5;
    simpl in H5.
  rewrite app_length;
    simpl;
    auto.

  exists t;
    split;
    [auto|apply upper_bound_refl].

  exists t;
    split;
    [auto|apply upper_bound_refl].
  
Qed.

Lemma limited_narrowing_has_contains :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              lt_ctx Sig 0 ->
              lt_env G (length G) ->
              mem_unique_p p ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t2 t1 ->
                      mem_unique t2 ->
                      lt_t t2 (length G2) ->
                      Sig en G1 ++ (t2::G2) vdash p ni s) /\

  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              lt_ctx Sig 0 ->
              lt_env G (length G) ->
              mem_unique t ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t2 t1 ->
                      mem_unique t2 ->
                      lt_t t2 (length G2) ->
                      Sig en G1 ++ (t2::G2) vdash s cont t).
Proof.
  apply has_contains_mutind; intros;
    auto.

  (*has*)
  assert (Huniq : mem_unique_ctx (G1++t2::G2));  
    [intros t'' Hin;
     apply in_app_or in Hin;
     destruct Hin as [Hc|Hc];
     [apply H1;
      subst;
      apply in_or_app;
      left;
      auto
     |inversion Hc;
      subst;
      auto;
      apply H1, in_or_app;
      right;
      apply in_cons;
      auto]|].
  destruct limited_narrowing_path_typing
    with
      (Sig:=Sig)(G:=G)
      (p:=p)(t:=t)
      (G1:=G1)(G2:=G2)
      (t1:=t1)(t2:=t2)
    as [t' Ha];
    auto;
    destruct Ha as [Ha Hb].
  apply has_path with (t:=t');
    auto.
  apply upper_bound_implies_type_contains with (t2:=t); auto.
  eapply mem_unique_path_typing; eauto.
  apply H with (t1:=t1); eauto.
  eapply mem_unique_path_typing; eauto.

  (*upper*)
  apply cont_upper with (t:=t).
  eapply H;
    eauto.
  inversion H5;
    auto.
  eapply H0;
    eauto.
  apply mem_unique_has in h;
    auto.
  inversion h;
    auto.
  inversion H5;
    auto.

  (*equal*)
  apply cont_equal with (t:=t).
  eapply H;
    eauto.
  inversion H5;
    auto.
  eapply H0;
    eauto.
  apply mem_unique_has in h;
    auto.
  inversion h;
    auto.
  inversion H5;
    auto.
Qed.

Lemma limited_narrowing_has :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              lt_ctx Sig 0 ->
              lt_env G (length G) ->
              mem_unique_p p ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t2 t1 ->
                      mem_unique t2 ->
                      lt_t t2 (length G2) ->
                      Sig en G1 ++ (t2::G2) vdash p ni s).
Proof.
  destruct limited_narrowing_has_contains; auto.
Qed.

Lemma limited_narrowing_contains :
  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              lt_ctx Sig 0 ->
              lt_env G (length G) ->
              mem_unique t ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t2 t1 ->
                      mem_unique t2 ->
                      lt_t t2 (length G2) ->
                      Sig en G1 ++ (t2::G2) vdash s cont t).
Proof.
  destruct limited_narrowing_has_contains; auto.
Qed.

Lemma limited_narrowing_subtype_mutind :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    lt_ctx Sig 0 ->
                    lt_env G1 (length G1) ->
                    lt_env G2 (length G2) ->
                    mem_unique t1 ->
                    mem_unique t2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3' t3 ->
                                 upp Sig G6 t4' t4 ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 lt_t t3' (length G4) ->
                                 lt_t t4' (length G6) ->
                                 Sig en G3 ++ (t3'::G4) vdash t1 <; t2 dashv G5 ++ (t4'::G6)) /\

  (forall Sig G1 s1 s2 G2, Sig en G1 vdash s1 <;; s2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    lt_ctx Sig 0 ->
                    lt_env G1 (length G1) ->
                    lt_env G2 (length G2) ->
                    mem_unique_s s1 ->
                    mem_unique_s s2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3' t3 ->
                                 upp Sig G6 t4' t4 ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 lt_t t3' (length G4) ->
                                 lt_t t4' (length G6) ->
                                 Sig en G3 ++ (t3'::G4) vdash s1 <;; s2 dashv G5 ++ (t4'::G6)) /\

  (forall Sig G1 ss1 ss2 G2, Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
                      mem_unique_ctx Sig ->
                      mem_unique_ctx G1 ->
                      mem_unique_ctx G2 ->
                      lt_ctx Sig 0 ->
                      lt_env G1 (length G1) ->
                      lt_env G2 (length G2) ->
                      mem_unique_ss ss1 ->
                      mem_unique_ss ss2 ->
                      forall G3 G4 G5 G6 t3 t4,
                        G1 = G3 ++ (t3::G4) ->
                        G2 = G5 ++ (t4::G6) ->
                        forall t3' t4', upp Sig G4 t3' t3 ->
                                   upp Sig G6 t4' t4 ->
                                   mem_unique t3' ->
                                   mem_unique t4' ->
                                   lt_t t3' (length G4) ->
                                   lt_t t4' (length G6) ->
                                   Sig en G3 ++ (t3'::G4) vdash ss1 <;;; ss2 dashv G5 ++ (t4'::G6)).
Proof.
  apply sub_mutind;
    intros;
    auto;
    try solve [inversion H5;
               inversion H6;
               inversion H7;
               inversion H8;
               eauto].

  (*arr*)
  apply s_arr with (i:=i).
  eapply H;
    eauto;
    [inversion H5; auto
    |inversion H4; auto].

  rewrite app_length; simpl;
    subst G1;
    rewrite app_length in e;
    simpl in e;
    auto.
  rewrite app_length; simpl;
    subst G2;
    rewrite app_length in e0;
    simpl in e0;
    auto.

  assert (Hrewrite1 : t1 :: G3 ++ t3' :: G4 =
                      (t1 :: G3) ++ t3' :: G4);
    [auto|rewrite Hrewrite1];
    assert (Hrewrite2 : t2 :: G5 ++ t4' :: G6 =
                        (t2 :: G5) ++ t4' :: G6);
    [auto|rewrite Hrewrite2].
  eapply H0;
    eauto;
    try solve [apply wf_con;
               inversion H4;
               inversion H5;
               auto];
    try solve [inversion H4;
               inversion H5;
               subst;
               auto];
    try solve [subst; auto].

  inversion H5; subst; rewrite e0; auto.

  (*s_upper1*)
  apply s_upper1 with (t1:=t1).

  apply limited_narrowing_has with (G:=G1)(t1:=t3);
    eauto.
  apply wf_implies_unique_mutind in H3; inversion H3; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_upper2*)
  apply s_upper2 with (t1:=t1).

  apply limited_narrowing_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t4)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_lower1*)
  apply s_lower1 with (t2:=t2).

  apply limited_narrowing_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*s_lower2*)
  apply s_lower2 with (t2:=t2).

  apply limited_narrowing_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t3);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*s_equal1*)
  apply s_equal1 with (t1:=t1).

  apply limited_narrowing_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_equal2*)
  apply s_equal2 with (t2:=t2).

  apply limited_narrowing_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*s_equal3*)
  apply s_equal3 with (t1:=t1).

  apply limited_narrowing_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t4)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_equal4*)
  apply s_equal4 with (t2:=t2).

  apply limited_narrowing_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t3);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*struct*)
  apply s_struct with (i:=i);
    try solve [rewrite app_length; simpl;
               subst G1 G2;
               rewrite app_length in e, e0;
               simpl in e, e0;
               auto].
  assert (Hrewrite1 : str ds1 rts :: G3 ++ t3' :: G4 =
                      (str ds1 rts :: G3) ++ t3' :: G4);
    [auto|rewrite Hrewrite1].
  assert (Hrewrite2 : str ds2 rts :: G5 ++ t4' :: G6 =
                      (str ds2 rts :: G5) ++ t4' :: G6);
    [auto|rewrite Hrewrite2].
  apply H with (t3:=t3)(t4:=t4);
    auto;
    try solve [apply mem_unique_subst_decl_tys;
               inversion H3;
               inversion H4;
               auto];
    try solve [intros t'' Hin;
               inversion Hin;
               subst;
               auto];
    try solve [subst G1 G2; auto].

  (*sd_equal*)
  inversion H4;
    inversion H5;
    eauto.

  (*sd_value*)
  inversion H4;
    inversion H5;
    eauto.

  (*sd_cons*)
  inversion H4;
    inversion H5;
    eauto.
Qed.

Lemma limited_narrowing_subtype_type :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    mem_unique t1 ->
                    mem_unique t2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3' t3 ->
                                 upp Sig G6 t4' t4 ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 Sig en G3 ++ (t3'::G4) vdash t1 <; t2 dashv G5 ++ (t4'::G6)).
Proof.
  destruct limited_narrowing_subtype_mutind; crush.
Qed.

Lemma limited_narrowing_subtype_decl_ty :
  (forall Sig G1 s1 s2 G2, Sig en G1 vdash s1 <;; s2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    mem_unique_s s1 ->
                    mem_unique_s s2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3' t3 ->
                                 upp Sig G6 t4' t4 ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 Sig en G3 ++ (t3'::G4) vdash s1 <;; s2 dashv G5 ++ (t4'::G6)).
Proof.
  destruct limited_narrowing_subtype_mutind; crush.
Qed.

Lemma limited_narrowing_subtype_decl_tys :
  (forall Sig G1 ss1 ss2 G2, Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
                      mem_unique_ctx Sig ->
                      mem_unique_ctx G1 ->
                      mem_unique_ctx G2 ->
                      mem_unique_ss ss1 ->
                      mem_unique_ss ss2 ->
                      forall G3 G4 G5 G6 t3 t4,
                        G1 = G3 ++ (t3::G4) ->
                        G2 = G5 ++ (t4::G6) ->
                        forall t3' t4', upp Sig G4 t3' t3 ->
                                   upp Sig G6 t4' t4 ->
                                   mem_unique t3' ->
                                   mem_unique t4' ->
                                   Sig en G3 ++ (t3'::G4) vdash ss1 <;;; ss2 dashv G5 ++ (t4'::G6)).
Proof.
  destruct limited_narrowing_subtype_mutind; crush.
Qed.

Lemma limited_widening_path_typing :
  forall Sig G p t, Sig en G vdash p pathType t ->
             forall G1 G2 t1,
               G = G1 ++ t1::G2 ->
               forall t2, upp Sig G2 t1 t2 ->
                     exists t', Sig en G1 ++ t2::G2 vdash p pathType t' /\
                           upp Sig (G1 ++ t2::G2) t t'.
Proof.
  intros.

  inversion H;
    subst.
  unfold mapping in H2.
  rewrite rev_app_distr in H2.
  destruct get_some_app
    with
      (G1:=rev(t1::G2))
      (G2:=rev G1)(n:=n)
    as [Ha|Ha];
    destruct Ha as [Ha Hb].

  simpl in Ha, Hb, H2.
  destruct get_some_app
    with
      (G1:=rev G2)
      (G2:=t1::nil)(n:=n)
    as [Hc|Hc];
    destruct Hc as [Hc Hd].
  exists t;
    split;
    [|apply upper_bound_refl].
  apply pt_var;
    unfold mapping;
    rewrite rev_app_distr;
    simpl.
  rewrite get_app_l;
    [rewrite get_app_l, <- Hd, <- Hb; auto|].
  rewrite app_length;
    rewrite app_length in Ha;
    simpl;
    simpl in Ha;
    auto.
  assert (Hn : n = length (rev G2));
    [rewrite app_length in Ha;
     simpl in Ha;
     crush|].
  exists t2;
    split.
  apply pt_var.
  unfold mapping.
  rewrite rev_app_distr.
  rewrite get_app_l;
    [
    |simpl;
     simpl in Ha;
     rewrite app_length;
     rewrite app_length in Ha;
     simpl in *;
     auto].
  simpl;
    rewrite get_app_r;
    auto.
  subst n.
  rewrite Nat.sub_diag;
    simpl;
    auto.
  
  simpl in H2;
    rewrite Hb in H2;
    rewrite Hd in H2.
  subst n;
    rewrite Nat.sub_diag in H2;
    simpl in H2;
    inversion H2;
    subst t.
  apply upper_bound_weakening, upper_bound_weakening_cons;
    auto.

  simpl in Ha, Hb, H2.
  rewrite app_length in Ha, Hb;
    simpl in Ha, Hb.
  exists t;
    split;
    [|apply upper_bound_refl].
  apply pt_var;
    unfold mapping;
    rewrite rev_app_distr;
    simpl.
  rewrite get_app_r;
    rewrite app_length; simpl; [|auto].
  rewrite <- Hb; auto.

  exists t;
    split;
    [auto|apply upper_bound_refl].

  exists t;
    split;
    [auto|apply upper_bound_refl].
Qed.

Lemma limited_widening_has_contains :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique_p p ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t1 t2 ->
                      mem_unique t2 ->
                      Sig en G1 ++ (t2::G2) vdash p ni s) /\

  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique t ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t1 t2 ->
                      mem_unique t2 ->
                      Sig en G1 ++ (t2::G2) vdash s cont t).
Proof.
  apply has_contains_mutind;
    intros;
    auto.

  (*path*)
  assert (Ha:=t0);
    apply limited_widening_path_typing
    with
      (G1:=G1)(G2:=G2)
      (t1:=t1)(t2:=t2)
    in Ha;
    auto;
    destruct Ha as [t' Ha];
    destruct Ha as [Ha Hb].
  apply upper_bound_contains
    with
      (s:=d)
    in Hb;
    auto;
    [| |apply mem_unique_path_typing in t0; auto].
  apply has_path with (t:=t');
    auto.
  apply Hb.
  apply H with (t1:=t1);
    auto.
  apply mem_unique_path_typing in t0;
    auto.
  intros t'' Hin;
    apply in_app_or in Hin;
    destruct Hin as [Hin|Hin];
    [subst G;
     apply H1, in_or_app;
     left;
     auto
    |inversion Hin;
     subst;
     auto;
     apply H1, in_or_app;
     right;
     apply in_cons;
     auto].

  (*cont-upper*)
  apply cont_upper with (t:=t).
  eapply H;
    eauto.
  inversion H3;
    auto.
  eapply H0;
    eauto.
  apply mem_unique_has in h;
    auto;
    inversion h;
    auto.
  inversion H3;
    auto.

  (*cont-equal*)
  apply cont_equal with (t:=t).
  eapply H;
    eauto.
  inversion H3;
    auto.
  eapply H0;
    eauto.
  apply mem_unique_has in h;
    auto;
    inversion h;
    auto.
  inversion H3;
    auto.
Qed.

Lemma limited_widening_has :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique_p p ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t1 t2 ->
                      mem_unique t2 ->
                      Sig en G1 ++ (t2::G2) vdash p ni s).
Proof.
  destruct limited_widening_has_contains; auto.
Qed.

Lemma limited_widening_contains :
  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique t ->
              forall G1 G2 t1,
                G = G1 ++ (t1::G2) ->
                forall t2, upp Sig G2 t1 t2 ->
                      mem_unique t2 ->
                      Sig en G1 ++ (t2::G2) vdash s cont t).
Proof.
  destruct limited_widening_has_contains; auto.
Qed.

Lemma limited_widening_subtype_mutind :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    mem_unique t1 ->
                    mem_unique t2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3 t3' ->
                                 upp Sig G6 t4 t4' ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 Sig en G3 ++ (t3'::G4) vdash t1 <; t2 dashv G5 ++ (t4'::G6)) /\

  (forall Sig G1 s1 s2 G2, Sig en G1 vdash s1 <;; s2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    mem_unique_s s1 ->
                    mem_unique_s s2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3 t3' ->
                                 upp Sig G6 t4 t4' ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 Sig en G3 ++ (t3'::G4) vdash s1 <;; s2 dashv G5 ++ (t4'::G6)) /\

  (forall Sig G1 ss1 ss2 G2, Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
                      mem_unique_ctx Sig ->
                      mem_unique_ctx G1 ->
                      mem_unique_ctx G2 ->
                      mem_unique_ss ss1 ->
                      mem_unique_ss ss2 ->
                      forall G3 G4 G5 G6 t3 t4,
                        G1 = G3 ++ (t3::G4) ->
                        G2 = G5 ++ (t4::G6) ->
                        forall t3' t4', upp Sig G4 t3 t3' ->
                                   upp Sig G6 t4 t4' ->
                                   mem_unique t3' ->
                                   mem_unique t4' ->
                                   Sig en G3 ++ (t3'::G4) vdash ss1 <;;; ss2 dashv G5 ++ (t4'::G6)).
Proof.
  apply sub_mutind;
    intros;
    auto;
    try solve [inversion H3;
               inversion H4;
               eauto].

  (*arr*)
  apply s_arr with (i:=i).
  eapply H;
    eauto;
    [inversion H5; auto
    |inversion H4; auto].

  rewrite app_length; simpl;
    subst G1;
    rewrite app_length in e;
    simpl in e;
    auto.
  rewrite app_length; simpl;
    subst G2;
    rewrite app_length in e0;
    simpl in e0;
    auto.

  assert (Hrewrite1 : t1 :: G3 ++ t3' :: G4 =
                      (t1 :: G3) ++ t3' :: G4);
    [auto|rewrite Hrewrite1];
    assert (Hrewrite2 : t2 :: G5 ++ t4' :: G6 =
                        (t2 :: G5) ++ t4' :: G6);
    [auto|rewrite Hrewrite2].
  eapply H0;
    eauto;
    try solve [intros t'' Hin;
               inversion Hin;
               inversion H4;
               inversion H5;
               subst;
               auto];
    try solve [apply mem_unique_subst_type;
               inversion H4;
               inversion H5;
               auto];
    try solve [subst; auto].

  (*s_upper1*)
  apply s_upper1 with (t1:=t1).

  apply limited_widening_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_upper2*)
  apply s_upper2 with (t1:=t1).

  apply limited_widening_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t4)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_lower1*)
  apply s_lower1 with (t2:=t2).

  apply limited_widening_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*s_lower2*)
  apply s_lower2 with (t2:=t2).

  apply limited_widening_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t3);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*s_equal1*)
  apply s_equal1 with (t1:=t1).

  apply limited_widening_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_equal2*)
  apply s_equal2 with (t2:=t2).

  apply limited_widening_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*s_equal3*)
  apply s_equal3 with (t1:=t1).

  apply limited_widening_has with (G:=G2)(t1:=t4);
    eauto.
  inversion H3; auto.

  apply H with (t3:=t4)(t4:=t4);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H3; auto];
    inversion h;
    auto.

  (*s_equal4*)
  apply s_equal4 with (t2:=t2).

  apply limited_widening_has with (G:=G1)(t1:=t3);
    eauto.
  inversion H4; auto.

  apply H with (t3:=t3)(t4:=t3);
    auto.
  apply mem_unique_has in h;
    auto;
    [|inversion H4; auto];
    inversion h;
    auto.

  (*struct*)
  apply s_struct with (i:=i);
    try solve [rewrite app_length; simpl;
               subst G1 G2;
               rewrite app_length in e, e0;
               simpl in e, e0;
               auto].
  assert (Hrewrite1 : str ds1 rts :: G3 ++ t3' :: G4 =
                      (str ds1 rts :: G3) ++ t3' :: G4);
    [auto|rewrite Hrewrite1].
  assert (Hrewrite2 : str ds2 rts :: G5 ++ t4' :: G6 =
                      (str ds2 rts :: G5) ++ t4' :: G6);
    [auto|rewrite Hrewrite2].
  apply H with (t3:=t3)(t4:=t4);
    auto;
    try solve [apply mem_unique_subst_decl_tys;
               inversion H3;
               inversion H4;
               auto];
    try solve [intros t'' Hin;
               inversion Hin;
               subst;
               auto];
    try solve [subst G1 G2; auto].

  (*sd_equal*)
  inversion H4;
    inversion H5;
    eauto.

  (*sd_value*)
  inversion H4;
    inversion H5;
    eauto.

  (*sd_cons*)
  inversion H4;
    inversion H5;
    eauto.
Qed.

Lemma limited_widening_subtype_type :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    mem_unique t1 ->
                    mem_unique t2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3 t3' ->
                                 upp Sig G6 t4 t4' ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 Sig en G3 ++ (t3'::G4) vdash t1 <; t2 dashv G5 ++ (t4'::G6)).
Proof.
  destruct limited_widening_subtype_mutind; crush.
Qed.

Lemma limited_widening_subtype_decl_ty :
  (forall Sig G1 s1 s2 G2, Sig en G1 vdash s1 <;; s2 dashv G2 ->
                    mem_unique_ctx Sig ->
                    mem_unique_ctx G1 ->
                    mem_unique_ctx G2 ->
                    mem_unique_s s1 ->
                    mem_unique_s s2 ->
                    forall G3 G4 G5 G6 t3 t4,
                      G1 = G3 ++ (t3::G4) ->
                      G2 = G5 ++ (t4::G6) ->
                      forall t3' t4', upp Sig G4 t3 t3' ->
                                 upp Sig G6 t4 t4' ->
                                 mem_unique t3' ->
                                 mem_unique t4' ->
                                 Sig en G3 ++ (t3'::G4) vdash s1 <;; s2 dashv G5 ++ (t4'::G6)).
Proof.
  destruct limited_widening_subtype_mutind; crush.
Qed.

Lemma limited_widening_subtype_decl_tys :
  (forall Sig G1 ss1 ss2 G2, Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
                      mem_unique_ctx Sig ->
                      mem_unique_ctx G1 ->
                      mem_unique_ctx G2 ->
                      mem_unique_ss ss1 ->
                      mem_unique_ss ss2 ->
                      forall G3 G4 G5 G6 t3 t4,
                        G1 = G3 ++ (t3::G4) ->
                        G2 = G5 ++ (t4::G6) ->
                        forall t3' t4', upp Sig G4 t3 t3' ->
                                   upp Sig G6 t4 t4' ->
                                   mem_unique t3' ->
                                   mem_unique t4' ->
                                   Sig en G3 ++ (t3'::G4) vdash ss1 <;;; ss2 dashv G5 ++ (t4'::G6)).
Proof.
  destruct limited_widening_subtype_mutind; crush.
Qed.
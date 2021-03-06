Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Require Import common.
Set Implicit Arguments.


(*Weakening*)

Lemma mapping_weakening :
  forall G r t, r mapsto t elem G ->
           forall G1 G2,
             G = G1 ++ G2 ->
             forall i n G',
               i = length G2 ->
               n = length G' ->
               (r [i] rjump_n n) mapsto (t [i] rjump_t n) elem ((G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n)).
Proof.
  intros; subst.

  unfold mapping.

  rewrite rev_app_distr.
  unfold right_jump_n.
  destruct (le_gt_dec (length G2) r);
    [rewrite leb_correct|
     rewrite leb_correct_conv]; auto.
  rewrite get_app_r; unfold right_jump_env.
  rewrite rev_length, app_length, map_length, Nat.sub_add_distr.

  rewrite <- Nat.add_sub_assoc;
    [rewrite Nat.sub_diag, plus_0_r|auto].
  rewrite <- map_rev.
  unfold mapping in H.
  rewrite rev_app_distr in H.
  rewrite get_app_r, rev_length in H.
  apply get_map with (f:=(fun t0 : ty => t0 [length G2]rjump_t length G')) in H; auto.

  rewrite rev_length; crush.
  rewrite rev_length, app_length, map_length; crush.

  rewrite get_app_l;
    [|unfold right_jump_env;
      rewrite rev_length, app_length, map_length;
      crush].
  unfold right_jump_env.
  rewrite rev_app_distr, get_app_l;
    [|rewrite rev_length, map_length; auto].
  rewrite <- map_rev.
  unfold mapping in H.
  rewrite rev_app_distr in H.
  rewrite get_app_l in H;
    [|rewrite rev_length; auto].
  apply get_map with (f:=(fun t0 : ty => t0 [length G2]rjump_t length G')) in H; auto.
  
Qed.



Lemma typing_p_weakening :
  forall Sig G p t, Sig en G vdash p pathType t ->
             forall G1 G2, G = G1 ++ G2 ->
                      forall i n G', i = length G2 ->
                                n = length G' ->
                                (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (p [i] rjump_e n) pathType (t [i] rjump_t n).
Proof.

  intros; induction H.
  
  simpl.
  apply pt_var.

  apply mapping_weakening with (G:=G); crush.

  simpl.
  apply pt_loc.
  apply get_map with (f:=fun (t : ty) => t [i] rjump_t n) in H.
  rewrite map_rev in H.
  crush.

  apply pt_cast.
  apply rjump_is_path; auto.
Qed.

Lemma typing_p_weakening_actual :
  forall Sig G p t, Sig en G vdash p pathType t ->
             Sig en G vdash p wf_e ->
             Sig en G vdash t wf_t ->
             Sig evdash G wf_env ->
             Sig wf_st ->
             forall G', Sig en G' ++ G vdash p pathType t.
Proof.
  intros.

  apply typing_p_weakening with (G1:=nil)(G2:=G)
                                (i:=length G)
                                (n:=length G')
                                (G':=G')in H;
    auto.
  simpl in H.
  rewrite lt_rjump_ctx, lt_rjump_env,
  lt_rjump_exp, lt_rjump_type in H; auto.
  apply wf_lt_type with (Sig:=Sig); auto.
  apply wf_lt_exp with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type with (Sig:=Sig); auto.
Qed.

Lemma has_contains_weakening_mutind :
  (forall Sig G p d, Sig en G vdash p ni d ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall i n G',
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (p [i] rjump_e n) ni (d [i] rjump_s n)) /\
  (forall Sig G t d, Sig en G vdash d cont t ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall i n G',
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (d [i] rjump_s n) cont (t [i] rjump_t n)).
Proof.
  apply has_contains_mutind; intros.

  simpl.
  rewrite rjump_subst_distr_decl_ty.
  apply has_path with (t:=t [i] rjump_t n); auto.
  apply typing_p_weakening with (G:=G1 ++ G2); subst; auto.

  simpl; apply cont_struct.
  apply in_dty_rjump; auto.

  simpl;
    apply cont_upper with (t:=t [i] rjump_t n);
    auto.
  apply H;
    auto.

  apply cont_equal with (t:=t [i] rjump_t n);
    auto.
  apply H;
    auto.
Qed.

Lemma has_weakening :
  (forall Sig G p d, Sig en G vdash p ni d ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall i n G',
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (p [i] rjump_e n) ni (d [i] rjump_s n)).
Proof.
  destruct has_contains_weakening_mutind; crush.
Qed.

Lemma has_weakening_actual : 
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig en G vdash p wf_e ->
              Sig en G vdash s wf_s ->
              Sig evdash G wf_env ->
              Sig wf_st ->
              forall G', Sig en G' ++ G vdash p ni s).
Proof.
  intros.
  assert (Hwfp : Sig en G vdash p wf_e); [auto|].
  assert (Hwfs : Sig en G vdash s wf_s); [auto|].
  apply has_weakening with (G1:=nil)(G2:=G)
                               (G':=G')(i:=length G)
                               (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_decl_ty in H.
  rewrite lt_rjump_exp in H; auto.
  apply wf_lt_exp with (Sig:=Sig); auto.
  apply wf_lt_decl_ty with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.
Qed.

Lemma contains_weakening :
  (forall Sig G t d, Sig en G vdash d cont t ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall i n G',
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (d [i] rjump_s n) cont (t [i] rjump_t n)).
Proof.
  destruct has_contains_weakening_mutind; crush.
Qed.

Lemma contains_weakening_actual : 
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig en G vdash t wf_t ->
              Sig en G vdash s wf_s ->
              Sig evdash G wf_env ->
              Sig wf_st ->
              forall G', Sig en G' ++ G vdash s cont t).
Proof.
  intros.
  assert (Hwft : Sig en G vdash t wf_t); [auto|].
  assert (Hwfs : Sig en G vdash s wf_s); [auto|].
  apply contains_weakening with (G1:=nil)(G2:=G)
                               (G':=G')(i:=length G)
                               (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_decl_ty in H.
  rewrite lt_rjump_type in H; auto.
  apply wf_lt_type with (Sig:=Sig); auto.
  apply wf_lt_decl_ty with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.
Qed.

Lemma sub_weakening_mutind :
  (forall Sig G1 t1 t2 G2,
      Sig en G1 vdash t1 <; t2 dashv G2 ->
      forall G3 G4 G5 G6 G G',
        G1 = G3 ++ G4 ->
        G2 = G5 ++ G6 ->
        forall i n,
          i = length G4 -> i = length G6 ->
          n = length G -> n = length G' ->
          (Sig [i] rjump_env n) en (G3 [i] rjump_env n) ++ G ++ (G4 [i] rjump_env n) vdash
                                (t1 [i] rjump_t n) <; (t2 [i] rjump_t n)
                                dashv (G5 [i] rjump_env n) ++ G' ++ (G6 [i] rjump_env n)) /\
  
  (forall Sig G1 s1 s2 G2,
      Sig en G1 vdash s1 <;; s2 dashv G2 ->
      forall G3 G4 G5 G6 G G',
        G1 = G3 ++ G4 ->
        G2 = G5 ++ G6 ->
        forall i n,
          i = length G4 -> i = length G6 ->
          n = length G -> n = length G' ->
          (Sig [i] rjump_env n) en (G3 [i] rjump_env n) ++ G ++ (G4 [i] rjump_env n) vdash
                                (s1 [i] rjump_s n) <;; (s2 [i] rjump_s n)
                                dashv (G5 [i] rjump_env n) ++ G' ++ (G6 [i] rjump_env n)) /\
  
  (forall Sig G1 ss1 ss2 G2,
      Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
      forall G3 G4 G5 G6 G G',
        G1 = G3 ++ G4 ->
        G2 = G5 ++ G6 ->
        forall i n,
          i = length G4 -> i = length G6 ->
          n = length G -> n = length G' ->
          (Sig [i] rjump_env n) en (G3 [i] rjump_env n) ++ G ++ (G4 [i] rjump_env n) vdash
                                (ss1 [i] rjump_ss n) <;;; (ss2 [i] rjump_ss n)
                                dashv (G5 [i] rjump_env n) ++ G' ++ (G6 [i] rjump_env n)).
Proof.
  apply sub_mutind; intros;
    try solve [crush].

  (*s-arr*)
  simpl; apply s_arr with (i:=length (G3 ++ G ++ G4)); auto.
  repeat (rewrite app_length);
    unfold right_jump_env;
    repeat (rewrite map_length);
    auto.
  assert (Hleng : length G3 = length G5);
    [subst;
     repeat rewrite app_length in e0;
     rewrite H4 in e0;
     crush|].
  repeat (rewrite app_length);
    unfold right_jump_env;
    repeat (rewrite map_length);
    rewrite Hleng, <- H3, H4, <- H5, H6; auto.
  assert (Hsub : (Sig [i0]rjump_env n) en ((t1::G3) [i0]rjump_env n) ++ G ++ (G4 [i0]rjump_env n)
                                       vdash ([v_ Var i /t 0] t1') [i0]rjump_t n <; ([v_ Var i /t 0] t2') [i0]rjump_t n
                                       dashv ((t2::G5) [i0]rjump_env n) ++ G' ++ (G6 [i0]rjump_env n)).
  apply H0; auto.
  subst; auto.
  subst; auto.
  repeat (rewrite rjump_subst_distr_type in Hsub).
  assert (Hleng : i0 <= i);
    [rewrite e, H3, H1, app_length; crush|].
  apply Nat.leb_le in Hleng.
  simpl in Hsub;
    unfold right_jump_n in Hsub;
    rewrite Hleng in Hsub.
  repeat rewrite app_length.
  assert ((length G3 + (length G + length G4)) = (length G + (length G3 + length G4))); [crush|].
  rewrite H7, <- app_length, <- H1, <- e, <- H5, plus_comm.
  crush.
  
  (*s-upper1*)
  simpl; apply s_upper1 with (t1:=t1 [i] rjump_t n); auto.
  apply has_weakening with (G1:=G3)(G2:=G4)(i:=i)(n:=n)(G':=G) in h; auto.
  
  (*s-upper2*)
  simpl; apply s_upper2 with (t1:=t1 [i] rjump_t n); auto.
  apply has_weakening with (G1:=G5)(G2:=G6)(i:=i)(n:=n)(G':=G') in h; auto.
  
  (*s-lower1*)
  simpl; apply s_lower1 with (t2:=t2 [i] rjump_t n); auto.
  apply has_weakening with (G1:=G5)(G2:=G6)(i:=i)(n:=n)(G':=G') in h; auto.
  
  (*s-lower2*)
  simpl; apply s_lower2 with (t2:=t2 [i] rjump_t n); auto.
  eapply has_weakening in h; eauto.
  
  (*s-equal1*)
  simpl; apply s_equal1 with (t1:=t1 [i] rjump_t n); auto.
  eapply has_weakening in h; eauto.
  
  (*s-equal2*)
  simpl; apply s_equal2 with (t2:=t2 [i] rjump_t n); auto.
  eapply has_weakening in h; eauto.
  
  (*s-equal3*)
  simpl; apply s_equal3 with (t1:=t1 [i] rjump_t n); auto.
  eapply has_weakening in h; eauto.
  
  (*s-equal4*)
  simpl; apply s_equal4 with (t2:=t2 [i] rjump_t n); auto.
  eapply has_weakening in h; eauto.

  (*s-struct*)
  simpl; apply s_struct with (i:=length (G3 ++ G ++ G4)).
  repeat (rewrite app_length);
    unfold right_jump_env;
    repeat (rewrite map_length);
    auto.
  assert (Hleng : length G3 = length G5);
    [subst;
     repeat rewrite app_length in e0;
     rewrite H3 in e0;
     crush|].
  repeat (rewrite app_length);
    unfold right_jump_env;
    repeat (rewrite map_length);
    rewrite Hleng, <- H2, H3, <- H4, H5; auto.
  assert (Hsub : (Sig [i0]rjump_env n) en (((str ds1 rts)::G3) [i0]rjump_env n) ++ G ++ (G4 [i0]rjump_env n) vdash
                                       ([v_ Var i /ss 0] ds1) [i0]rjump_ss n <;;; ([v_ Var i /ss 0] ds2) [i0]rjump_ss n
                                       dashv (((str ds2 rts)::G5) [i0]rjump_env n) ++ G' ++ (G6 [i0]rjump_env n)).
  apply H; auto.
  subst; auto.
  subst; auto.
  repeat (rewrite rjump_subst_distr_decl_tys in Hsub).
  assert (Hleng : i0 <= i);
    [rewrite e, H2, H0, app_length; crush|].
  apply Nat.leb_le in Hleng.
  simpl in Hsub;
    unfold right_jump_n in Hsub;
    rewrite Hleng in Hsub.
  repeat rewrite app_length.
  assert ((length G3 + (length G + length G4)) = (length G + (length G3 + length G4))); [crush|].
  rewrite H6, <- app_length, <- H0, <- e, <- H4, plus_comm.
  crush.
Qed.

Lemma sub_weakening_type :
  (forall Sig G1 t1 t2 G2,
      Sig en G1 vdash t1 <; t2 dashv G2 ->
      forall G3 G4 G5 G6 G G',
        G1 = G3 ++ G4 ->
        G2 = G5 ++ G6 ->
        forall i n,
          i = length G4 -> i = length G6 ->
          n = length G -> n = length G' ->
          (Sig [i] rjump_env n) en (G3 [i] rjump_env n) ++ G ++ (G4 [i] rjump_env n) vdash
                                (t1 [i] rjump_t n) <; (t2 [i] rjump_t n)
                                dashv (G5 [i] rjump_env n) ++ G' ++ (G6 [i] rjump_env n)).
Proof.
  destruct sub_weakening_mutind; crush.
Qed.

Lemma sub_weakening_decl_ty :
  
  (forall Sig G1 s1 s2 G2,
      Sig en G1 vdash s1 <;; s2 dashv G2 ->
      forall G3 G4 G5 G6 G G',
        G1 = G3 ++ G4 ->
        G2 = G5 ++ G6 ->
        forall i n,
          i = length G4 -> i = length G6 ->
          n = length G -> n = length G' ->
          (Sig [i] rjump_env n) en (G3 [i] rjump_env n) ++ G ++ (G4 [i] rjump_env n) vdash
                                (s1 [i] rjump_s n) <;; (s2 [i] rjump_s n)
                                dashv (G5 [i] rjump_env n) ++ G' ++ (G6 [i] rjump_env n)).
Proof.
  destruct sub_weakening_mutind; crush.
Qed.

Lemma sub_weakening_decl_tys :
  
  (forall Sig G1 ss1 ss2 G2,
      Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
      forall G3 G4 G5 G6 G G',
        G1 = G3 ++ G4 ->
        G2 = G5 ++ G6 ->
        forall i n,
          i = length G4 -> i = length G6 ->
          n = length G -> n = length G' ->
          (Sig [i] rjump_env n) en (G3 [i] rjump_env n) ++ G ++ (G4 [i] rjump_env n) vdash
                                (ss1 [i] rjump_ss n) <;;; (ss2 [i] rjump_ss n)
                                dashv (G5 [i] rjump_env n) ++ G' ++ (G6 [i] rjump_env n)).
Proof.
  destruct sub_weakening_mutind; crush.
Qed.

Lemma typing_weakening_mutind :
  (forall Sig G e t, Sig en G vdash e hasType t ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall G' i n,
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (e [i] rjump_e n) hasType (t [i] rjump_t n)) /\
  
  (forall Sig G d s, Sig en G vdash d hasType_d s ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall G' i n,
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (d [i] rjump_d n) hasType_d (s [i] rjump_s n)) /\
  
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                       forall G1 G2,
                         G = G1 ++ G2 ->
                         forall G' i n,
                           i = length G2 ->
                           n = length G' ->
                           (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (ds [i] rjump_ds n) hasType_ds (ss [i] rjump_ss n)).
Proof.
  apply typing_mutind; intros;
    try solve [crush].

  (*t-var*)
  apply t_var, mapping_weakening with (G:=G); auto.

  (*t-loc*)
  apply t_loc.
  apply get_map with (f:=fun (t0 : ty) => t0 [i0] rjump_t n) in e.
  rewrite map_rev in e; auto.

  (*t-cast*)
  simpl; apply t_cast with (t':=t' [i] rjump_t n); auto.
  apply sub_weakening_type with (G1:=G1++G2)(G2:=G1++G2); subst; auto.

  (*t-fn*)
  simpl; apply t_fn.
  assert (Htyp : (Sig [i]rjump_env n) en ((t1::G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n) vdash
                                      ([v_ Var (length G) /e 0] e) [i]rjump_e n hasType (([v_ Var (length G) /t 0] t2) [i]rjump_t n)).
  apply H; subst; auto.
  rewrite rjump_subst_distr_exp, rjump_subst_distr_type in Htyp.
  simpl in Htyp.
  assert (Hleng : i <=? length G = true);
    [apply leb_correct;
     rewrite H1, H0, app_length;
     crush|].
  unfold right_jump_n in Htyp.
  rewrite Hleng, H0, app_length, <- H1 in Htyp.
  repeat rewrite app_length, rjump_length.
  rewrite <- H1, <- H2.
  assert (Hleng2 : (length G1 + (n + i)) =(length G1 + i + n));
    [crush|rewrite Hleng2; auto].

  (*t-app*)
  simpl.
  apply t_app with (t1:=t1 [i] rjump_t n)(t':=t' [i] rjump_t n); auto.
  simpl in H;
    apply H; auto.
  apply sub_weakening_type with (G1:=G)(G2:=G); auto.
  intros.
  eapply closed_rjump_type, c, rjump_closed_type; eauto.

  (*t-app-path*)
  simpl;
    rewrite rjump_subst_distr_type;
    simpl;
    apply t_app_path with (t':=t' [i] rjump_t n);
    [crush| |].
  apply typing_p_weakening with (G:=G); auto.
  apply sub_weakening_type with (G1:=G)(G2:=G); auto.

  (*t-new*)
  simpl; apply t_new.
  repeat rewrite app_length, rjump_length.
  rewrite <- H1.
  assert (Htyp : (Sig [i]rjump_env n) en ((str ss rts :: G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)
                                      vdash ([v_ Var (length G) /ds 0] ds) [i]rjump_ds n
                                      hasType_ds (([v_ Var (length G) /ss 0] ss) [i]rjump_ss n)).
  apply H; auto.
  rewrite H0; crush.
  rewrite <- H2.
  rewrite rjump_subst_distr_decls, rjump_subst_distr_decl_tys in Htyp.
  assert (Hleng : i <=? length G = true);
    [apply leb_correct;
     rewrite H1, H0, app_length;
     crush|].
  simpl in Htyp.
  unfold right_jump_n in Htyp.
  rewrite Hleng in Htyp.
  rewrite H0, app_length, <- H1 in Htyp.
  assert (Hleng2 : (length G1 + (n + i)) = (length G1 + i + n));
    [crush|rewrite Hleng2]; auto.
  assert (Hrewrite : (length ((G1 [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n))) =
                     (length G [i] rjump_n n));
    [
     |rewrite Hrewrite].
  repeat rewrite app_length, rjump_length.
  subst.
  rewrite app_length.
  unfold right_jump_n.
  assert (Hle : length G2 <= length G1 + length G2);
    [crush
    |apply leb_correct in Hle;
     rewrite Hle; crush].
  apply unbound_rjump_decl_tys; auto.

  (*t-acc-path*)
  simpl; apply t_acc_path.
  apply has_weakening with (G1:=G1)(G2:=G2)(i:=i)(n:=n)(G':=G') in h; auto.

  (*t-acc*)
  simpl; apply t_acc_closed with (t':=t' [i] rjump_t n); auto.
  apply contains_weakening with (G1:=G1)(G2:=G2)(i:=i)(n:=n)(G':=G') in c; auto.
  intros.
  eapply closed_rjump_type, c0, rjump_closed_type; eauto.

  (*td-val*)
  simpl; apply td_val with (t':=t' [i] rjump_t n); auto.
  apply sub_weakening_type with (G3:=G1)(G4:=G2)
                                (G5:=G1)(G6:=G2)
                                (G:=G')(G':=G')
                                (i:=i)(n:=n) in s; auto.
Qed.

Lemma typing_weakening_exp :
  (forall Sig G e t, Sig en G vdash e hasType t ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall G' i n,
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (e [i] rjump_e n) hasType (t [i] rjump_t n)).
Proof.
  destruct typing_weakening_mutind; crush.
Qed.

Lemma typing_weakening_decl :
  
  (forall Sig G d s, Sig en G vdash d hasType_d s ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall G' i n,
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (d [i] rjump_d n) hasType_d (s [i] rjump_s n)).
Proof.
  destruct typing_weakening_mutind; crush.
Qed.

Lemma typing_weakening_decls :
  
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                       forall G1 G2,
                         G = G1 ++ G2 ->
                         forall G' i n,
                           i = length G2 ->
                           n = length G' ->
                           (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (ds [i] rjump_ds n) hasType_ds (ss [i] rjump_ss n)).
Proof.
  destruct typing_weakening_mutind; crush.
Qed.

Lemma member_weakening :
  (forall Sig G e d, Sig en G vdash e mem d ->
                     forall G1 G2,
                       G = G1 ++ G2 ->
                       forall i n G',
                         i = length G2 ->
                         n = length G' ->
                         (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (e [i] rjump_e n) mem (d [i] rjump_s n)).
Proof.
  intros Sig G e d H;
    inversion H; subst; intros.
  apply has_weakening with (G1:=G1)(G2:=G2)
                           (i:=i)(n:=n)(G':=G') in H0; auto.
  apply mem_path; auto.

  apply typing_weakening_exp with (G1:=G1)(G2:=G2)
                                  (i:=i)(n:=n)(G':=G') in H0; auto.
  apply contains_weakening with (G1:=G1)(G2:=G2)
                                (i:=i)(n:=n)(G':=G') in H1; auto.
  apply mem_exp with (t:=t [i] rjump_t n); auto.
  apply closed_rjump_decl_ty; auto.
Qed.


Lemma typing_weakening_actual_exp :
  (forall Sig G e t, Sig en G vdash e hasType t ->
              Sig en G vdash e wf_e ->
              Sig en G vdash t wf_t ->
              Sig evdash G wf_env ->
              Sig wf_st ->
              forall G', Sig en G' ++ G vdash e hasType t).
Proof.
  intros.
  assert (Htyp := H).
  apply typing_weakening_exp with (G1:=nil)(G2:=G)
                                  (G':=G')(i:=length G)
                                  (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_type in H; auto.
  rewrite lt_rjump_exp in H; auto.
  apply wf_lt_exp with (Sig:=Sig); auto.
  apply wf_lt_type with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.

Qed.

Lemma typing_weakening_actual_decl :
  (forall Sig G d s, Sig en G vdash d hasType_d s ->
              Sig en G vdash d wf_d ->
              Sig en G vdash s wf_s ->
              Sig evdash G wf_env ->
              Sig wf_st ->
              forall G', Sig en G' ++ G vdash d hasType_d s).
Proof.
  intros.
  assert (Htyp := H).
  apply typing_weakening_decl with (G1:=nil)(G2:=G)
                                   (G':=G')(i:=length G)
                                   (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_decl_ty in H; auto.
  rewrite lt_rjump_decl in H; auto.
  apply wf_lt_decl with (Sig:=Sig); auto.
  apply wf_lt_decl_ty with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.

Qed.

Lemma typing_weakening_actual_decls :
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                Sig en G vdash ds wf_ds ->
                Sig en G vdash ss wf_ss ->
                Sig evdash G wf_env ->
                Sig wf_st ->
                forall G', Sig en G' ++ G vdash ds hasType_ds ss).
Proof.
  intros.
  assert (Htyp := H).
  apply typing_weakening_decls with (G1:=nil)(G2:=G)
                                    (G':=G')(i:=length G)
                                    (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_decl_tys in H; auto.
  rewrite lt_rjump_decls in H; auto.
  apply wf_lt_decls with (Sig:=Sig); auto.
  apply wf_lt_decl_tys with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.
Qed.


Lemma wf_weakening_mutind :
  (forall Sig G t, Sig en G vdash t wf_t ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (t [i] rjump_t n) wf_t) /\
  
  (forall Sig G s, Sig en G vdash s wf_s ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (s [i] rjump_s n) wf_s) /\
  
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
                    forall G1 G2,
                      G = G1 ++ G2 ->
                      forall G' i n,
                        i = length G2 ->
                        n = length G' ->
                        (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (ss [i] rjump_ss n) wf_ss) /\
  
  (forall Sig G e, Sig en G vdash e wf_e ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (e [i] rjump_e n) wf_e) /\
  
  (forall Sig G d, Sig en G vdash d wf_d ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (d [i] rjump_d n) wf_d) /\
  
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
                    forall G1 G2,
                      G = G1 ++ G2 ->
                      forall G' i n,
                        i = length G2 ->
                        n = length G' ->
                        (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (ds [i] rjump_ds n) wf_ds).
Proof.
  apply wf_mutind; intros;
    try solve [crush].

  (*wf-arr*)
  simpl; apply wf_arr; auto.
  assert (Hjump : length ((G1 [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)) =
                  (length G [i] rjump_n n));
    [|rewrite Hjump; apply unbound_rjump_type; auto].
  repeat rewrite app_length, rjump_length; subst.
  unfold right_jump_n;
    rewrite leb_correct;
    rewrite app_length; crush.
  assert (Hwf : (Sig [i]rjump_env n) en ((t1::G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n) vdash
                                     ([v_ Var (length G) /t 0] t2) [i]rjump_t n wf_t);
    [apply H0; subst; auto
    |auto].
  repeat rewrite app_length, rjump_length;
    rewrite <- H2, <- H3.
  rewrite rjump_subst_distr_type in Hwf;
    simpl in Hwf.
  unfold right_jump_n in Hwf;
    rewrite leb_correct in Hwf;
    [|subst; rewrite app_length; crush].
  rewrite H1, app_length, <- H2 in Hwf.
  assert (Hleng : length G1 + (n + i) = (length G1 + i + n));
    [crush|rewrite Hleng; auto].

  (*wf-sel-upper*)
  simpl; apply wf_sel_upper with (t:=t [i0] rjump_t n); auto.
  apply is_path_rjump; auto.
  apply has_weakening with (G1:=G1)(G2:=G2)(i:=i0)(n:=n)(G':=G') in h; simpl in h; auto.

  (*wf-sel-lower*)
  simpl; apply wf_sel_lower with (t:=t [i0] rjump_t n); auto.
  apply is_path_rjump; auto.
  apply has_weakening with (G1:=G1)(G2:=G2)(i:=i0)(n:=n)(G':=G') in h; simpl in h; auto.

  (*wf-sel-equal*)
  simpl; apply wf_sel_equal with (t:=t [i0] rjump_t n); auto.
  apply is_path_rjump; auto.
  apply has_weakening with (G1:=G1)(G2:=G2)(i:=i0)(n:=n)(G':=G') in h; simpl in h; auto.

  (*wf-struct*)
  simpl; apply wf_str; auto.
  assert (Hjump : length ((G1 [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)) =
                  (length G [i] rjump_n n));
    [|rewrite Hjump; apply unbound_rjump_decl_tys; auto].
  repeat rewrite app_length, rjump_length; subst.
  unfold right_jump_n;
    rewrite leb_correct;
    rewrite app_length; crush.
  
  assert (Hwf : (Sig [i]rjump_env n) en ((str ss rts :: G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)
                                     vdash ([v_ Var (length G) /ss 0] ss) [i]rjump_ss n wf_ss);
    [apply H; simpl; crush|].
  rewrite rjump_subst_distr_decl_tys in Hwf.
  simpl in Hwf.
  repeat rewrite app_length, rjump_length.
  rewrite <- H1, <- H2.
  assert (Hleng : i <=? length G = true);
    [apply leb_correct;
     rewrite H0, app_length, H1;
     crush|].
  unfold right_jump_n in Hwf;
    rewrite Hleng in Hwf.
  rewrite H0, app_length, <- H1 in Hwf.
  assert (Hleng' : (length G1 + (n + i)) = (length G1 + i + n));
    [crush|
     rewrite Hleng'; auto].

  (*wf-decl-tys*)
  simpl; apply wft_con; auto.
  apply not_in_decl_tys_rjump; auto.

  (*wf-var*)
  simpl; apply wf_var.
  unfold right_jump_n.
  destruct (le_lt_dec i n) as [Hle | Hlt].
  rewrite leb_correct; auto.
  repeat rewrite app_length, rjump_length.
  rewrite <- H0, <- H1.
  assert (Hleng : length G = length G1 + i);
    [rewrite H, app_length; crush|
     crush].
  rewrite leb_correct_conv; auto.
  repeat rewrite app_length, rjump_length;
    rewrite <- H0; crush.
  
  
  (*wf-loc*)
  simpl; apply wf_loc;
    rewrite rjump_length; auto.

  (*wf-fn*)
  simpl; apply wf_fn; auto.
  assert (Hjump : length ((G1 [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)) =
                  (length G [i] rjump_n n));
    [|rewrite Hjump; apply unbound_rjump_exp; auto].
  repeat rewrite app_length, rjump_length; subst.
  unfold right_jump_n;
    rewrite leb_correct;
    rewrite app_length; crush.
  
  repeat rewrite app_length, rjump_length.
  assert (Hwf : (Sig [i]rjump_env n) en ((t1::G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)
                                     vdash ([v_ Var (length G) /e 0] e) [i]rjump_e n wf_e);
    [apply H0; simpl; subst; auto|].
  rewrite rjump_subst_distr_exp in Hwf; simpl in Hwf;
    assert (Hleng : i <=? length G = true);
    [apply leb_correct;
     rewrite H2, app_length, <- H3;
     crush
    |simpl in Hwf;
     unfold right_jump_n in Hwf;
     rewrite Hleng in Hwf].
  rewrite H2, app_length in Hwf.
  rewrite <- H4.
  assert (Hleng' : (length G1 + (n + length G2)) = (length G1 + length G2 + n));
    [crush
    |rewrite Hleng'; auto].

  assert (Hjump : length ((G1 [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)) =
                  (length G [i] rjump_n n));
    [|rewrite Hjump; apply unbound_rjump_type; auto].
  repeat rewrite app_length, rjump_length; subst.
  unfold right_jump_n;
    rewrite leb_correct;
    rewrite app_length; crush.
  assert (Hwf : (Sig [i]rjump_env n) en ((t1::G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)
                                     vdash ([v_ Var (length G) /t 0] t2) [i]rjump_t n wf_t);
    [apply H1; simpl; subst; auto|].
  rewrite rjump_subst_distr_type in Hwf; simpl in Hwf;
    assert (Hleng : i <=? length G = true);
    [apply leb_correct;
     rewrite H2, app_length, <- H3;
     crush
    |simpl in Hwf;
     unfold right_jump_n in Hwf;
     rewrite Hleng in Hwf].
  rewrite H2, app_length in Hwf.
  repeat rewrite app_length, rjump_length.
  rewrite <- H4.
  assert (Hleng' : (length G1 + (n + length G2)) = (length G1 + length G2 + n));
    [crush
    |rewrite Hleng'; auto].

  apply typing_weakening_exp with (G1:=t1::G1)(G2:=G2)
                                  (G':=G')(i:=i)(n:=n) in t;
    try solve [crush].
  rewrite rjump_subst_distr_type, rjump_subst_distr_exp in t;
    simpl in t;
    unfold right_jump_n in t.
  
  assert (Hleng : i <=? length G = true);
    [apply leb_correct; subst; rewrite app_length; crush
    |rewrite Hleng in t].
  repeat rewrite app_length, rjump_length;
    rewrite <- H3, <- H4.
  rewrite H2, app_length, <- H3 in t.
  assert (Hleng' : (length G1 + (n + i)) = (length G1 + i + n));
    [crush
    |rewrite Hleng'; auto].

  (*wf-app*)
  simpl; apply wf_app with (t1:=t1 [i] rjump_t n)(t2:=t2 [i] rjump_t n); auto.
  apply typing_weakening_exp with (G1:=G1)(G2:=G2)
                                  (G':=G')(i:=i)(n:=n) in t; auto.
  apply typing_weakening_exp with (G1:=G1)(G2:=G2)
                                  (G':=G')(i:=i)(n:=n) in t0; auto.

  (*wf-acc*)
  simpl; apply wf_acc with (t':=t' [i] rjump_t n); auto.
  apply member_weakening with (G1:=G1)(G2:=G2)
                              (i:=i)(n:=n)(G':=G') in m; auto.

  (*wf-cast*)
  simpl; apply wf_cast with (t':=t' [i] rjump_t n); auto.
  apply typing_weakening_exp with (G:=G); auto.
  apply sub_weakening_type with (G1:=G)(G2:=G); auto.

  (*wf-new*)
  simpl; apply wf_new with (ss:=ss [i] rjump_ss n).
  apply typing_weakening_exp with (G1:=G1)(G2:=G2)
                                  (G':=G')(i:=i)(n:=n) in t; auto.
  
  assert (Hjump : length ((G1 [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)) =
                  (length G [i] rjump_n n));
    [|rewrite Hjump; apply unbound_rjump_decls; auto].
  repeat rewrite app_length, rjump_length; subst.
  unfold right_jump_n;
    rewrite leb_correct;
    rewrite app_length; crush.

  
  assert (Hwf : (Sig [i]rjump_env n) en ((str ss rts :: G1) [i]rjump_env n) ++ G' ++ (G2 [i]rjump_env n)
                                     vdash ([v_ Var (length G) /ds 0] ds) [i]rjump_ds n wf_ds);
    [apply H; crush
    |].
  rewrite rjump_subst_distr_decls in Hwf;
    simpl in Hwf;
    unfold right_jump_n in Hwf.
  assert (Hleng : i <=? length G = true);
    [apply leb_correct;
     subst;
     rewrite app_length;
     crush
    |rewrite Hleng in Hwf].
  repeat rewrite app_length, rjump_length.
  assert (Hleng' : length G1 + (length G' + length G2) = length G + n);
    [|rewrite Hleng'; auto].
  rewrite H0, app_length, <- H2; crush.

  simpl; apply wfe_value with (t':=t' [i]rjump_t n); auto.
  apply typing_weakening_exp with (G:=G);
    auto.
  eapply sub_weakening_type;
    eauto.

  (*wf-decls*)
  simpl; apply wfe_con; auto.
  apply not_in_decls_rjump; auto.
Qed.


Lemma wf_weakening_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (t [i] rjump_t n) wf_t).
Proof.
  destruct wf_weakening_mutind; crush.
Qed.

Lemma wf_weakening_decl_ty :
  
  (forall Sig G s, Sig en G vdash s wf_s ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (s [i] rjump_s n) wf_s).
Proof.
  destruct wf_weakening_mutind; crush.
Qed.

Lemma wf_weakening_decl_tys :
  
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
                    forall G1 G2,
                      G = G1 ++ G2 ->
                      forall G' i n,
                        i = length G2 ->
                        n = length G' ->
                        (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (ss [i] rjump_ss n) wf_ss).

Proof.
  destruct wf_weakening_mutind; crush.
Qed.

Lemma wf_weakening_exp :    
  (forall Sig G e, Sig en G vdash e wf_e ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (e [i] rjump_e n) wf_e).
Proof.
  destruct wf_weakening_mutind; crush.
Qed.

Lemma wf_weakening_decl :
  
  (forall Sig G d, Sig en G vdash d wf_d ->
                   forall G1 G2,
                     G = G1 ++ G2 ->
                     forall G' i n,
                       i = length G2 ->
                       n = length G' ->
                       (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (d [i] rjump_d n) wf_d).
Proof.
  destruct wf_weakening_mutind; crush.
Qed.

Lemma wf_weakening_decls :    
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
                    forall G1 G2,
                      G = G1 ++ G2 ->
                      forall G' i n,
                        i = length G2 ->
                        n = length G' ->
                        (Sig [i] rjump_env n) en (G1 [i] rjump_env n) ++ G' ++ (G2 [i] rjump_env n) vdash (ds [i] rjump_ds n) wf_ds).
Proof.
  destruct wf_weakening_mutind; crush.
Qed.

Lemma wf_weakening_actual_type :
  forall Sig G t, Sig en G vdash t wf_t ->
                  Sig evdash G wf_env ->
                  Sig wf_st -> 
                  forall G', Sig en G'++G vdash t wf_t.
Proof.
  intros.
  assert (Hwf : Sig en G vdash t wf_t); [auto|].
  apply wf_weakening_type with (G1:=nil)(G2:=G)
                               (G':=G')(i:=length G)
                               (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_type in H; auto.
  apply wf_lt_type with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.
Qed.

Lemma wf_weakening_actual_exp :
  forall Sig G e, Sig en G vdash e wf_e ->
           Sig evdash G wf_env ->
           Sig wf_st -> 
           forall G', Sig en G'++G vdash e wf_e.
Proof.
  intros.
  assert (Hwf := H).
  apply wf_weakening_exp with (G1:=nil)(G2:=G)
                              (G':=G')(i:=length G)
                              (n:=length G') in H; auto.
  simpl in H.
  rewrite lt_rjump_ctx in H.
  rewrite lt_rjump_env in H.
  rewrite lt_rjump_exp in H; auto.
  apply wf_lt_exp with (Sig:=Sig); auto.
  apply wf_lt_env with (Sig:=Sig); auto.
  apply wf_lt_store_type; auto.
Qed.

Lemma wf_in_env :
  forall Sig G, Sig evdash G wf_env ->
         Sig wf_st ->
         forall t, In t G ->
              Sig en G vdash t wf_t.
Proof.
  intros Sig G Hwf;
    induction Hwf;
    intros.

  inversion H0.

  inversion H1;
    [subst t0|].
  apply wf_weakening_actual_type
    with
      (G':=t::nil)
    in H;
    auto.

  assert (Htmp := H0).
  apply IHHwf
    with
      (t:=t0)
    in Htmp;
    auto.
  apply wf_weakening_actual_type
    with
      (G':=t::nil)
    in Htmp;
    auto.
Qed.

Lemma path_typing_store_type_weakening :
  (forall Sig G p t, Sig en G vdash p pathType t ->
              forall S, (S ++ Sig) en G vdash p pathType t).
Proof.
  intros.

  destruct H;
    auto.

  apply pt_loc.
  unfold mapping in *.
  rewrite rev_app_distr;
    auto.
Qed.

Hint Resolve path_typing_store_type_weakening.
Hint Rewrite path_typing_store_type_weakening.

Lemma has_contains_store_type_weakening_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              forall S, S ++ Sig en G vdash p ni s) /\

  (forall Sig G t s, Sig en G vdash s cont t ->
              forall S, S ++ Sig en G vdash s cont t).
Proof.
  apply has_contains_mutind; intros;
    eauto.
Qed.

Lemma has_store_type_weakening :
  (forall Sig G p s, Sig en G vdash p ni s ->
              forall S, S ++ Sig en G vdash p ni s) /\

  (forall Sig G t s, Sig en G vdash s cont t ->
              forall S, S ++ Sig en G vdash s cont t).
Proof.
  destruct has_contains_store_type_weakening_mutind; crush.
Qed.

Lemma contains_store_type_weakening :
  (forall Sig G p s, Sig en G vdash p ni s ->
              forall S, S ++ Sig en G vdash p ni s) /\

  (forall Sig G t s, Sig en G vdash s cont t ->
              forall S, S ++ Sig en G vdash s cont t).
Proof.
  destruct has_contains_store_type_weakening_mutind; crush.
Qed.

Hint Resolve contains_store_type_weakening.
Hint Rewrite contains_store_type_weakening.
Hint Resolve has_store_type_weakening.
Hint Rewrite has_store_type_weakening.

Lemma subtyping_store_type_weakening_mutind :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    forall S, S ++ Sig en G1 vdash t1 <; t2 dashv G2) /\

  (forall Sig G1 s1 s2 G2, Sig en G1 vdash s1 <;; s2 dashv G2 ->
                    forall S, S ++ Sig en G1 vdash s1 <;; s2 dashv G2) /\
  
  (forall Sig G1 ss1 ss2 G2, Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
                      forall S, S ++ Sig en G1 vdash ss1 <;;; ss2 dashv G2).
Proof.
  apply sub_mutind;
    intros;
    eauto.

  eapply s_upper1;
    eauto.
  apply has_store_type_weakening;
    auto.

  eapply s_upper2;
    eauto.
  apply has_store_type_weakening;
    auto.
  
  eapply s_lower1;
    eauto.
  apply has_store_type_weakening;
    auto.
  
  eapply s_lower2;
    eauto.
  apply has_store_type_weakening;
    auto.
  
  eapply s_equal1;
    eauto.
  apply has_store_type_weakening;
    auto.
  
  eapply s_equal2;
    eauto.
  apply has_store_type_weakening;
    auto.
  
  eapply s_equal3;
    eauto.
  apply has_store_type_weakening;
    auto.
  
  eapply s_equal4;
    eauto.
  apply has_store_type_weakening;
    auto.
  
Qed.

Lemma subtyping_store_type_weakening_type :
  (forall Sig G1 t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                    forall S, S ++ Sig en G1 vdash t1 <; t2 dashv G2).
Proof.
  destruct subtyping_store_type_weakening_mutind; crush.
Qed.

Lemma subtyping_store_type_weakening_decl_ty :
  (forall Sig G1 s1 s2 G2, Sig en G1 vdash s1 <;; s2 dashv G2 ->
                    forall S, S ++ Sig en G1 vdash s1 <;; s2 dashv G2).
Proof.
  destruct subtyping_store_type_weakening_mutind; crush.
Qed.

Lemma subtyping_store_type_weakening_decl_tys :  
  (forall Sig G1 ss1 ss2 G2, Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
                      forall S, S ++ Sig en G1 vdash ss1 <;;; ss2 dashv G2).
Proof.
  destruct subtyping_store_type_weakening_mutind; crush.
Qed.

Hint Rewrite subtyping_store_type_weakening_type.
Hint Resolve subtyping_store_type_weakening_type.
Hint Rewrite subtyping_store_type_weakening_decl_ty.
Hint Resolve subtyping_store_type_weakening_decl_ty.
Hint Rewrite subtyping_store_type_weakening_decl_tys.
Hint Resolve subtyping_store_type_weakening_decl_tys.

Lemma typing_store_type_weakening_mutind :
  (forall Sig G e t, Sig en G vdash e hasType t ->
              forall S, S ++ Sig en G vdash e hasType t) /\

  (forall Sig G d s, Sig en G vdash d hasType_d s ->
              forall S, S ++ Sig en G vdash d hasType_d s) /\
  
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                forall S, S ++ Sig en G vdash ds hasType_ds ss).
Proof.
  apply typing_mutind;
    intros;
    eauto.

  apply t_loc;
    eauto;
    unfold mapping in *.
  rewrite rev_app_distr;
    auto.

  apply t_acc_path;
    eapply has_store_type_weakening;
    eauto.

  eapply t_acc_closed;
    eauto;
    eapply has_store_type_weakening;
    eauto.  
Qed.

Lemma typing_store_type_weakening_exp :
  (forall Sig G e t, Sig en G vdash e hasType t ->
              forall S, S ++ Sig en G vdash e hasType t).
Proof.
  destruct typing_store_type_weakening_mutind; crush.
Qed.

Lemma typing_store_type_weakening_decl :
  (forall Sig G e t, Sig en G vdash e hasType t ->
              forall S, S ++ Sig en G vdash e hasType t).
Proof.
  destruct typing_store_type_weakening_mutind; crush.
Qed.

Lemma typing_store_type_weakening_decls :  
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                forall S, S ++ Sig en G vdash ds hasType_ds ss).
Proof.
  destruct typing_store_type_weakening_mutind; crush.
Qed.

Hint Rewrite typing_store_type_weakening_exp.
Hint Resolve typing_store_type_weakening_exp.
Hint Rewrite typing_store_type_weakening_decl.
Hint Resolve typing_store_type_weakening_decl.
Hint Rewrite typing_store_type_weakening_decls.
Hint Resolve typing_store_type_weakening_decls.

Lemma membership_store_type_weakening :
  forall Sig G e s, Sig en G vdash e mem s ->
             forall S, S ++ Sig en G vdash e mem s.
Proof.
  intros.

  destruct H.

  apply mem_path;
    eapply has_store_type_weakening;
    eauto.

  eapply mem_exp;
    eauto;
    eapply contains_store_type_weakening;
    eauto.
Qed.

Hint Rewrite membership_store_type_weakening.
Hint Resolve membership_store_type_weakening.

Lemma wf_store_type_weakening_mutind :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall S, (S ++ Sig) en G vdash t wf_t) /\

  (forall Sig G s, Sig en G vdash s wf_s ->
            forall S, (S ++ Sig) en G vdash s wf_s) /\

  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall S, (S ++ Sig) en G vdash ss wf_ss) /\

  (forall Sig G e, Sig en G vdash e wf_e ->
            forall S, (S ++ Sig) en G vdash e wf_e) /\

  (forall Sig G d, Sig en G vdash d wf_d ->
            forall S, (S ++ Sig) en G vdash d wf_d) /\

  (forall Sig G ds, Sig en G vdash ds wf_ds ->
             forall S, (S ++ Sig) en G vdash ds wf_ds).
Proof.
  apply wf_mutind;
    intros;
    eauto.

  eapply wf_sel_upper;
    try (eapply has_store_type_weakening);
    eauto.

  eapply wf_sel_lower;
    try (eapply has_store_type_weakening);
    eauto.

  eapply wf_sel_equal;
    try (eapply has_store_type_weakening);
    eauto.

  apply wf_loc;
    auto;
    rewrite app_length;
    crush.
Qed.

Lemma wf_store_type_weakening_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall S, (S ++ Sig) en G vdash t wf_t).
Proof.
  destruct wf_store_type_weakening_mutind; crush.
Qed.

Lemma wf_store_type_weakening_decl_ty :
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall S, (S ++ Sig) en G vdash s wf_s).
Proof.
  destruct wf_store_type_weakening_mutind; crush.
Qed.

Lemma wf_store_type_weakening_decl_tys :
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall S, (S ++ Sig) en G vdash ss wf_ss).
Proof.
  destruct wf_store_type_weakening_mutind; crush.
Qed.

Lemma wf_store_type_weakening_exp :
  (forall Sig G e, Sig en G vdash e wf_e ->
            forall S, (S ++ Sig) en G vdash e wf_e).
Proof.
  destruct wf_store_type_weakening_mutind; crush.
Qed.

Lemma wf_store_type_weakening_decl :
  (forall Sig G d, Sig en G vdash d wf_d ->
            forall S, (S ++ Sig) en G vdash d wf_d).
Proof.
  destruct wf_store_type_weakening_mutind; crush.
Qed.

Lemma wf_store_type_weakening_decls :
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
             forall S, (S ++ Sig) en G vdash ds wf_ds).
Proof.
  destruct wf_store_type_weakening_mutind; crush.
Qed.

Hint Rewrite wf_store_type_weakening_type.
Hint Rewrite wf_store_type_weakening_decl_ty.
Hint Rewrite wf_store_type_weakening_decl_tys.
Hint Rewrite wf_store_type_weakening_exp.
Hint Rewrite wf_store_type_weakening_decl.
Hint Rewrite wf_store_type_weakening_decls.

Hint Resolve wf_store_type_weakening_type.
Hint Resolve wf_store_type_weakening_decl_ty.
Hint Resolve wf_store_type_weakening_decl_tys.
Hint Resolve wf_store_type_weakening_exp.
Hint Resolve wf_store_type_weakening_decl.
Hint Resolve wf_store_type_weakening_decls.

Lemma wf_in_store_type :
  forall Sig, Sig wf_st ->
       forall G t, In t Sig ->
              Sig en G vdash t wf_t.
Proof.
  intros Sig Hwf;
    induction Hwf;
    intros.

  inversion H.

  inversion H0;
    [subst t|].
  apply wf_weakening_actual_type
    with
      (G':=G)
    in H;
    auto;
    [rewrite app_nil_r in H|apply wf_nil].
  apply wf_store_type_weakening_type
    with
      (S:=str ds rts::nil)
    in H;
    simpl in H;
    auto.

  apply IHHwf
    with
      (G:=G)
    in H1.
  apply wf_store_type_weakening_type
    with
      (S:=str ds rts::nil)
    in H1;
    auto.
Qed.
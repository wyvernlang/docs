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
Set Implicit Arguments.


Lemma mapping_subst :
  forall G x t, x mapsto t elem G ->
           forall p n G', G = ([p /env n] G') ->
                     p notin_env G' ->
                     exists t', (t = ([p /t n + x] t')) /\ p notin_t t'.
Proof.
  intro G; induction G as [|t1 G1]; intros.

  destruct G'; simpl in H0; inversion H0.
  unfold mapping in H; simpl in H; rewrite get_empty in H; auto.
  inversion H.

  rewrite subst_cons in H0; inversion H0.

  destruct G'; simpl in H0.
  rewrite subst_nil in H0; inversion H0.
  rewrite subst_cons in H0; inversion H0; subst.
  unfold mapping in H; simpl in H.
  
  apply get_cons_dec in H;
    destruct H as [Ha|Ha];
    destruct Ha as [Ha Hb].
  destruct IHG1 with (x:=x)(t:=t)(p0:=p)(n0:=n)(G'0:=G') as [t' Hc]; auto;
    [intros t' Hin;
     apply H1, in_cons; auto
    |destruct Hc as [Hc Hd]].
  exists t'; auto.
  exists t0; subst.
  rewrite rev_length, subst_length; split; auto.
  apply H1, in_eq.
Qed.


Lemma mapping_subst_switch :
  forall G r t, r mapsto t elem G ->
           forall p1 n G',
             G = ([p1 /env n] G') ->
             p1 notin_env G' ->
             forall t', p1 notin_t t' ->
                   t = ([p1 /t n + r] t') ->
                   forall p2, r mapsto ([p2 /t n + r] t') elem ([p2 /env n] G') .
Proof.
  intro G; induction G as [|t1 G1]; intros;
    destruct G' as [|t2 G2];
    try (rewrite subst_cons in H0; inversion H0);
    try (rewrite subst_nil in H0; inversion H0).

  unfold mapping in H;
    simpl in H;
    rewrite get_empty in H;
    inversion H; auto.
  
  unfold mapping in H; simpl in H.
  apply get_cons_dec in H;
    destruct H as [Ha|Ha];
    destruct Ha as [Ha Hb]. 
  apply IHG1 with (p1:=p1)(n:=n)(G':=G2)(t':=t')(p2:=p2) in Hb; auto.
  destruct Hb.
  unfold mapping.
  rewrite subst_cons.
  assert (Happ : (([p2 /t n + length G2] t2) :: ([p2 /env n] G2)) =
                 (([p2 /t n + length G2] t2) :: nil) ++ ([p2 /env n] G2));
    [auto|].
  rewrite Happ.
  rewrite rev_app_distr.
  rewrite get_app_l;
    [auto
    |subst; rewrite rev_length, subst_length;
     rewrite rev_length, subst_length in Ha; auto].
  intros  t'' Hin;
    apply H1, in_cons; auto.

  unfold mapping.
  rewrite subst_cons; simpl.
  assert (Hleng : r = (length G2));
    [inversion H0; subst; rewrite rev_length, subst_length; auto|].
  rewrite get_app_r; rewrite rev_length, subst_length;
    [rewrite Hleng, Nat.sub_diag; simpl|crush].
  subst.
  inversion H0; subst.
  rewrite rev_length, subst_length in H3.
  apply subst_equality_type in H3; subst; auto.
  apply H1, in_eq.
Qed.


Lemma typing_p_exists_subst :
  (forall Sig G p t, Sig en G vdash p pathType t ->
              forall p1 G1 G2 n p',
                G = ([p1 /env 0] G1) ++ G2 ->
                p = ([p1 /e n] p') ->
                p1 notin_e p' ->
                p1 notin_env (G1 ++ G2) ->
                p1 notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_exp p1 0 ->
                exists t', (t = [p1 /t n] t') /\ p1 notin_t t').
Proof.
  intros Sig G p t Htyp; destruct Htyp; intros.

  assert (Hleng : n < length G);
    [unfold mapping in H;
     apply get_some_index in H;
     rewrite rev_length in H;
     auto|].
  destruct p'; simpl in H1; inversion H1; subst; auto.
  destruct v as [x|x];
    inversion H1; subst.

  unfold mapping in H;
    rewrite rev_app_distr in H.
  destruct get_some_app with (G1:=rev G2)(G2:=rev ([p1 /env 0] G1))(n:=x) as [Ha|Ha];
    destruct Ha as [Ha Hb].

  exists t; rewrite closed_subst_type; [split|]; auto.
  apply H3, in_or_app; right;
    apply in_rev, get_in with (n:=x);
    rewrite Hb in H; auto.
  apply H6;
    [apply in_or_app;
     right;
     apply in_rev;
     apply get_in with (n:=x);
     rewrite <- Hb; auto
    |crush].

  rewrite Hb in H.
  assert (Hget := H).
  apply mapping_subst with (p:=p1)(n:=0)(G':=G1) in H; auto;
    simpl in H.
  destruct H as [t' Heq];
    destruct Heq as [Heq Hni].
  rewrite rename_closed_subst_type with (m:=length G1) in Heq.
  exists (t' [x - length (rev G2) maps_t length G1]); split; auto.
  apply notin_rename_type; auto.
  apply H8; crush.
  apply H6; [|crush].
  apply in_or_app; left.
  apply in_rev, get_in with (n:=x - length(rev G2)); crush.
  intros t' Hin.
  apply H3, in_or_app; auto.

  destruct (Nat.eq_dec (length G1) x) as [Heq|Heq];
    [subst;
     rewrite <- beq_nat_refl in H1;
     subst
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H1;
     inversion H1].
  clear H5 H10.

  
  destruct get_some_app with (G1:=rev G2)(G2:=rev ([c_ n /env 0] G1))(n:=n) as [Ha|Ha];
    destruct Ha as [Ha Hb].
  
  unfold mapping in H;
    rewrite rev_app_distr, get_app_l in H;
    [|auto].
  exists t; split;
    [rewrite closed_subst_type;
     auto;
     apply H6; [|crush]
    |apply H3];
    apply in_or_app;
    right;
    apply in_rev, get_in with (n0:=n); auto.

  unfold mapping in H;
    rewrite rev_app_distr, Hb in H.    
  destruct mapping_subst with (x:=n - length G2)
                              (t:=t)(p:=c_ n)
                              (n:=0)(G':=G1)
                              (G:=([c_ n /env 0] G1)) as [t' Hc]; auto;
    [rewrite <- rev_length
    |intros t' Hin;
     apply H3, in_or_app
    |destruct Hc as [Hc Hd];
     simpl in Hc]; auto.
  exists (t' [n - length G2 maps_t length G1]); split.
  rewrite <- rename_closed_subst_type; auto.
  rewrite <- Hc.
  apply H6; [|crush].
  apply in_or_app; left.
  apply in_rev, get_in with (n0:=n - length (rev G2)); auto.
  apply notin_rename_type; auto.

  exists t; split;
    [rewrite closed_subst_type; auto;
     apply H7;
     [|crush]
    |apply H4];
    apply in_rev, get_in with (n0:=i); unfold mapping in H; auto.

  destruct p'; simpl in H1; inversion H1; subst.
  destruct v as [|x]; [inversion H1|].
  destruct (Nat.eq_dec (length G1) x) as [Heq|Heq];
    [subst; rewrite <- beq_nat_refl in H1; subst
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H1;
     inversion H1].
  exists t; split.
  apply closed_exp_cast in H8;
    rewrite closed_subst_type; crush.
  apply synsize_notin_type; simpl; crush.

  exists t0; split; auto.
  inversion H2; auto.
Qed.



Lemma typing_p_subst:
  (forall Sig G p t, Sig en G vdash p pathType t ->
              Sig wf_st ->
              forall p1 G1 G2 n p' t',
                G = ([p1 /env 0] G1) ++ G2 ->
                p = ([p1 /e n] p') ->
                t = ([p1 /t n] t') ->
                p1 notin_e p' ->
                p1 notin_t t' ->
                p1 notin_env (G1 ++ G2) ->
                p1 notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                Sig evdash G2 wf_env ->
                forall p2 tp,
                  is_path p2 ->
                  closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                  Sig en G2 vdash p1 pathType tp ->
                  Sig en G2 vdash p2 pathType tp ->
                  Sig en G2 vdash p1 wf_e ->
                  Sig en G2 vdash p2 wf_e ->
                  Sig en G2 vdash tp wf_t ->
                  Sig en ([p2 /env 0] G1) ++ G2 vdash ([p2 /e n] p') pathType ([p2 /t n] t')).
Proof.
  intros Sig G p t Htyp;
    destruct Htyp; intros.

  destruct p'; simpl in H2; inversion H2; subst.
  destruct v as [r|r];
    [inversion H2; subst
    |destruct (Nat.eq_dec (length G1) r) as [Heq|Heq];
     subst;
     [rewrite <- beq_nat_refl in H2; subst
     |apply Nat.eqb_neq in Heq; rewrite Heq in H2; inversion H2]];
    clear H20.    

  unfold mapping in H.
  rewrite rev_app_distr in H.
  destruct (get_some_app (rev G2) (rev ([p1 /env 0] G1)) r) as [Ha|Ha];
    destruct Ha as [Ha Hb];
    rewrite Hb in H.
  assert (Hclosed : closed_t (length G1) t');
    [apply notin_subst_closed_type with (e:=p1);
     apply H6;
     apply in_or_app; right;
     apply in_rev;
     apply get_in with (n:=r); auto|].
  rewrite closed_subst_type in H; auto.
  rewrite closed_subst_type; auto.
  simpl.
  apply pt_var.
  unfold mapping;
    rewrite rev_app_distr;
    rewrite get_app_l;
    auto.

  assert (Hget := H); unfold mapping in Hget.
  rewrite rename_closed_subst_type with (m:=r - length (rev G2)) in H;
    [
     |apply H9;
      [|crush];
      apply in_or_app;
      left;
      apply in_rev, get_in with (n:=r - length (rev G2));
      auto].
  apply mapping_subst_switch
    with (G:=[p1 /env 0]G1)(r:=r - length (rev G2))
         (t:=[p1 /t r - length (rev G2)] (t'[length G1 maps_t r - length (rev G2)]))
         (p1:=p1)(G':=G1)(n:=0)
         (t':=(t'[length G1 maps_t r - length (rev G2)]))(p2:=p2)in H;
    auto.
  simpl in *.
  apply pt_var; unfold mapping.
  rewrite rev_app_distr.
  rewrite get_app_r; auto.
  rewrite rename_closed_subst_type with (m:=r - length (rev G2)); auto.
  assert (Hclosed : closed_ty ([p2 /t length G1] t') 0); [|apply Hclosed; crush].
  apply closed_subst_switch_type with (p1:=p1).
  apply H9, in_or_app;
    left;
    apply in_rev, get_in with (n:=r - length (rev G2));
    auto.
  intros n Hin;
    apply wf_closed_exp with (Sig:=Sig)(G:=G2);
    auto.
  intros t Hin;
    apply H6, in_or_app; auto.
  apply notin_rename_type; auto.
  apply wf_closed_exp with (Sig:=Sig)(G:=G2);
    auto.

  simpl; rewrite <- beq_nat_refl.
  inversion H14; subst.
  assert (Hleng : n < length (rev G2));
    [eapply get_some_index; eauto|].
  unfold mapping in H, H8.
  rewrite rev_app_distr, get_app_l in H; auto.
  rewrite H8 in H;
    inversion H;
    subst.
  apply typing_p_weakening_actual with (G':=[p2 /env 0]G1) in H15; auto.
  assert (Hclosed : closed_t (length G1) t');
    [apply notin_subst_closed_type with (e:=c_ n),
                                        H6,
                                        in_or_app;
     right;
     apply in_rev, get_in with (n0:=n);
     auto
    |].
  rewrite closed_subst_type in H15; auto.
  rewrite closed_subst_type; auto.

  destruct p'; simpl in H2; inversion H2; subst.
  
  destruct v as [|r];
    [inversion H2
    |destruct (Nat.eq_dec (length G1) r) as [|Heq];
     [subst; rewrite <- beq_nat_refl in H2; subst;
      simpl; rewrite <- beq_nat_refl
     |apply Nat.eqb_neq in Heq;
      rewrite Heq in H2;
      inversion H2]].
  apply path_typing_uniqueness with (t:=[i_ i /t length G1] t') in H14;
    auto; subst.
  apply typing_p_weakening_actual with (G':=[p2 /env 0]G1) in H15; auto.
  assert (Hclosed : closed_t (length G1) t');
    [apply notin_subst_closed_type
       with (e:=i_ i),
            H7,
            in_rev,
            get_in with (n:=i);
     auto
    |].
  rewrite closed_subst_type in H15; auto.
  rewrite closed_subst_type; auto.
  
  simpl.
  assert (Hclosed : closed_t (length G1) t');
    [apply notin_subst_closed_type
       with (e:=p1),
            H7,
            in_rev,
            get_in with (n:=n0);
     auto
    |].
  rewrite closed_subst_type in H; auto.
  rewrite closed_subst_type; auto.

  destruct p';
    try solve [simpl in H2; inversion H2; subst].
  simpl in H2; inversion H2; subst.
  destruct v as [|r];
    [inversion H2
    |destruct (Nat.eq_dec (length G1) r) as [|Heq];
     [subst; rewrite <- beq_nat_refl in H2; subst;
      simpl; rewrite <- beq_nat_refl
     |apply Nat.eqb_neq in Heq;
      rewrite Heq in H2;
      inversion H2]].
  assert (Hnotin : p1 notin_t([p1 /t length G1] t'));
    [apply synsize_notin_type;
     assert (Hsize : synsize_e p1 = (synsize_e ((p cast ([p1 /t length G1] t')))));
     [rewrite H2; auto|];
     rewrite Hsize;
     simpl;
     crush|].
  apply notin_subst_closed_type in Hnotin;
    rewrite (closed_subst_type Hnotin) in *; auto.
  subst.
  inversion H14; subst.
  apply typing_p_weakening_actual with (G':=[p2 /env 0]G1) in H15; auto.

  subst.
  simpl in *;
    inversion H2; subst.
  apply subst_equality_type in H8; auto;
    [subst; auto|inversion H4; auto].
  apply pt_cast.
  apply is_path_subst; auto.
  eapply subst_is_path; eauto.
Qed.



Lemma has_contains_exists_subst_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig wf_st ->
              forall r n G1 G2 p',
                G = ([c_ r /env 0] G1) ++ G2 ->
                p = ([c_ r /e n] p') ->
                (c_ r) notin_e p' ->
                (c_ r) notin_env (G1 ++ G2) ->
                (c_ r) notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_exp p 0 ->
                exists s', (s = ([c_ r /s n] s')) /\
                      (c_ r) notin_s s') /\
  
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig wf_st ->
              forall r n G1 G2 t',
                G = ([c_ r /env 0] G1) ++ G2 ->
                t = ([c_ r /t n] t') ->
                (c_ r) notin_t t' ->
                (c_ r) notin_env (G1 ++ G2) ->
                (c_ r) notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_ty t 0 ->
                exists s', (s = ([c_ r /s S n] s')) /\
                           (c_ r) notin_s s').
Proof.
  apply has_contains_mutind; intros.

  (*has*)
  assert (Htyp := t0); auto.
  assert (Hclosed_t : closed_ty t 0);
    [apply closed_typing_p with (Sig:=Sig)(G:=G)(p:=p); auto|].
  eapply typing_p_exists_subst with (p1:=c_ r)(n:=n) in t0; eauto;
    try solve [try (eapply root_notin_exp);
               try (eapply root_notin_env);
               eauto];
    destruct t0 as [t' Ha];
    destruct Ha as [Ha Hb].
  edestruct H with (r:=r)(n:=n)(G1:=G1)(G2:=G2) as [s' Hc];
    eauto.
  
  destruct Hc as [Hc Hd].
  assert (Hclosed_s : closed_decl_ty ([p /s 0] d) 0);
    [apply closed_subst_hole_decl_ty; auto;
     apply closed_contains with (Sig:=Sig)(G:=G)(t:=t); auto|].
  exists (([p' [n maps_e S n] /s 0] s') [S n maps_s n]); split.
  (*equality*)
  rewrite Hc, H2;
    rewrite Hc, H2 in Hclosed_s.
  assert (Hrewrite1 : ([c_ r /e n] p') = [c_ r /e S n] (p' [n maps_e S n]));
    [apply rename_closed_subst_exp;
     subst; apply H9; crush
    |rewrite Hrewrite1;
     rewrite Hrewrite1 in Hclosed_s].
  rewrite <- subst_distr_decl_ty; auto;
    rewrite <- subst_distr_decl_ty in Hclosed_s; auto.
  rewrite rename_closed_subst_decl_ty with (n:=S n)(m:=n); [auto|].
  apply Hclosed_s; crush.
  (*notin*)
  apply notin_rename_decl_ty; auto.
  apply unbound_var_notin_decl_ty.
  apply unbound_subst_components_decl_ty.
  apply notin_var_unbound_decl_ty; auto.
  apply notin_var_unbound_exp.
  apply notin_rename_exp; auto.

  (*struct contains*)
  destruct t' as [ss| | | |]; simpl in H1; inversion H1; subst ds.
  destruct (in_dty_subst_notin (c_ r) (S n) i) with (e:=c_ r) as [s' Ha];
    [
     |destruct Ha as [Ha Hb];
      subst d].
  inversion H2; subst;
    simpl in H11; auto.
  exists s'; auto.

  (*upper contains*)
  destruct t' as [|p' l| | |]; simpl in H3; inversion H3; subst p L.
  destruct H with (r0:=r)(n0:=n)(G1:=G1)
                  (G2:=G2)(p'0:=p')as [s' Ha];
    auto;
    [inversion H4; auto
    |apply closed_ty_sel in H10; auto
    |destruct Ha as [Ha Hb];
     destruct s' as [l' t'| | |];
     simpl in Ha;
     inversion Ha;
     subst l t].
  assert (Hclosed : closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h;
     auto;
     [apply closed_decl_ty_upper in h; auto
     |apply closed_ty_sel in H10; auto]
    |].
  destruct H0 with (n0:=n)(r0:=r)
                   (G1:=G1)(G2:=G2)
                   (t'0:=t') as [s'' Hc];
    auto;
    [inversion Hb; auto
    |destruct Hc as [Hc Hd];
     subst d].
  exists (s'');
    split; auto.

  
  (*equal contains*)
  destruct t' as [|p' l| | |]; simpl in H3; inversion H3; subst p L.
  destruct H with (r0:=r)(n0:=n)(G1:=G1)
                  (G2:=G2)(p'0:=p')as [s' Ha];
    auto;
    [inversion H4; auto
    |apply closed_ty_sel in H10; auto
    |destruct Ha as [Ha Hb];
     destruct s' as [| |l' t'|];
     simpl in Ha;
     inversion Ha;
     subst l t].
  assert (Hclosed : closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h;
     auto;
     [apply closed_decl_ty_equal in h; auto
     |apply closed_ty_sel in H10; auto]
    |].
  destruct H0 with (n0:=n)(r0:=r)
                   (G1:=G1)(G2:=G2)
                   (t'0:=t') as [s'' Hc];
    auto;
    [inversion Hb; auto
    |destruct Hc as [Hc Hd];
     subst d].
  exists s'';
    split; auto.
Qed.

Lemma has_exists_subst :
  (forall Sig G p s, Sig en G vdash p ni s ->
                     Sig wf_st ->
                     forall r n G1 G2 p',
                       G = ([c_ r /env 0] G1) ++ G2 ->
                       p = ([c_ r /e n] p') ->
                       (c_ r) notin_e p' ->
                       (c_ r) notin_env (G1 ++ G2) ->
                       (c_ r) notin_env Sig ->
                       n = length G1 ->
                       closed_env G 0 ->
                       closed_env Sig 0 ->
                       closed_exp p 0 ->
                       exists s', (s = ([c_ r /s n] s')) /\
                                  (c_ r) notin_s s').
Proof.
  destruct has_contains_exists_subst_mutind; crush.
Qed.

Lemma contains_exists_subst :
  (forall Sig G t s, Sig en G vdash s cont t ->
                     Sig wf_st ->
                     forall r n G1 G2 t',
                       G = ([c_ r /env 0] G1) ++ G2 ->
                       t = ([c_ r /t n] t') ->
                       (c_ r) notin_t t' ->
                       (c_ r) notin_env (G1 ++ G2) ->
                       (c_ r) notin_env Sig ->
                       n = length G1 ->
                       closed_env G 0 ->
                       closed_env Sig 0 ->
                       closed_ty t 0 ->
                       exists s', (s = ([c_ r /s S n] s')) /\
                                  (c_ r) notin_s s').
Proof.
  destruct has_contains_exists_subst_mutind; crush.
Qed.

Lemma has_contains_subst_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
                     Sig wf_st ->
                     forall r n G1 G2 p' s',
                       G = ([c_ r /env 0] G1) ++ G2 ->
                       p = ([c_ r /e n] p') ->
                       s = ([c_ r /s n] s') ->
                       (c_ r) notin_e p' ->
                       (c_ r) notin_s s' ->
                       (c_ r) notin_env (G1 ++ G2) ->
                       (c_ r) notin_env Sig ->
                       n = length G1 ->
                       closed_env G 0 ->
                       closed_env Sig 0 ->
                       closed_exp p 0 ->
                       Sig evdash G2 wf_env ->
                       forall p2 tp,
                         closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                         Sig en G2 vdash (c_ r) pathType tp ->
                         Sig en G2 vdash p2 pathType tp ->
                         Sig en G2 vdash (c_ r) wf_e ->
                         Sig en G2 vdash p2 wf_e ->
                         Sig en G2 vdash tp wf_t ->
                         is_path p2 ->
                         Sig en ([p2 /env 0] G1) ++ G2 vdash ([p2 /e n] p') ni ([p2 /s n] s')) /\
  
  (forall Sig G t s, Sig en G vdash s cont t ->
                     Sig wf_st ->
                     forall r n G1 G2 t' s',
                       G = ([c_ r /env 0] G1) ++ G2 ->
                       t = ([c_ r /t n] t') ->
                       s = ([c_ r /s S n] s') ->
                       (c_ r) notin_t t' ->
                       (c_ r) notin_s s' ->
                       (c_ r) notin_env (G1 ++ G2) ->
                       (c_ r) notin_env Sig ->
                       n = length G1 ->
                       closed_env G 0 ->
                       closed_env Sig 0 ->
                       closed_ty t 0 ->
                       Sig evdash G2 wf_env ->
                       forall p2 tp,
                         closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                         Sig en G2 vdash (c_ r) pathType tp ->
                         Sig en G2 vdash p2 pathType tp ->
                         Sig en G2 vdash (c_ r) wf_e ->
                         Sig en G2 vdash p2 wf_e ->
                         Sig en G2 vdash tp wf_t ->
                         is_path p2 ->
                         Sig en ([p2 /env 0] G1) ++ G2 vdash ([p2 /s S n] s') cont ([p2 /t n] t')).
Proof.
  apply has_contains_mutind; intros.

  (*has*)
  destruct typing_p_exists_subst with (Sig:=Sig)(G:=G)(p:=p)
                                      (t:=t)(p1:=c_ r)
                                      (G1:=G1)(G2:=G2)
                                      (n:=n)(p':=p') as [t' Ha];
    auto;
    destruct Ha as [Ha Hb].
  destruct contains_exists_subst with (Sig:=Sig)(G:=G)(t:=t)
                                      (s:=d)(r:=r)
                                      (G1:=G1)(G2:=G2)
                                      (n:=n)(t':=t') as [s'' Hc];
    auto;
    [apply closed_typing_p with (Sig:=Sig)(G:=G)(p:=p); auto
    |destruct Hc as [Hc Hd]].

  
  assert (Hclosed : closed_decl_ty ([v_ Var r /s n] s') 0);
    [subst d;
     apply closed_contains in c; auto;
     [apply closed_subst_hole_decl_ty with (e:=p) in c; auto;
      rewrite <- H3; auto
     |apply closed_typing_p with (m:=0) in t0; auto]|].

  (*build the rewrite and establish that it does not have the appropriate variables free in it*)
  assert (Hrewrite : s' = (([p'[n maps_e S n] /s 0] s'')[S n maps_s n]) /\
                     closed_s n ([p'[n maps_e S n] /s 0] s''));
    [|destruct Hrewrite as [Hrewrite Hclosed1]].
  rewrite Hc in H3.
  rewrite rename_closed_subst_exp with (m:=S n) in H2;
    [subst p
    |subst p; auto;
     apply H11; crush].
  rewrite rename_closed_subst_decl_ty with (s:=s')(m:=S n) in H3;
    [|apply Hclosed; crush].
  subst d.
  rewrite <- subst_distr_decl_ty in H3; [|auto|auto].
  apply subst_equality_decl_ty in H3;
    [
     |apply unbound_var_notin_decl_ty;
      apply unbound_subst_components_decl_ty;
      [apply notin_var_unbound_decl_ty; auto
      |apply notin_var_unbound_exp;
       apply notin_rename_exp;
       auto]
     |apply notin_rename_decl_ty; auto].
  assert (Htmp : (([p' [n maps_e S n] /s 0] s'')[S n maps_s n]) = ((s' [n maps_s S n])[S n maps_s n]));
    [rewrite H3; auto|].
  rewrite rename_inverse_decl_ty in Htmp; auto;
    [
     |apply closed_subst_neq_decl_ty with (s:=[c_ r /s n]s')(p:=c_ r)(m:=n); auto;
      apply Hclosed; crush].
  split; auto.
  assert (Htmp' : ([c_ r /s n] s') = ([c_ r /s S n] (s'[n maps_s S n])));
    [apply rename_closed_subst_decl_ty with (m:=S n);
     apply Hclosed; crush|].
  rewrite H3.
  apply closed_subst_neq_decl_ty with (s:=[c_ r /s n]s')(p:=c_ r)(m:=S n); auto;
    apply Hclosed; crush.

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros m Hle; apply wf_closed_exp with (Sig:=Sig)(G:=G2); auto|].
  rewrite Hrewrite.
  rewrite rename_closed_subst_decl_ty with (m:=S n); auto;
    [
     |rewrite <- Hrewrite;
      apply closed_subst_switch_decl_ty with (p2:=p2) in Hclosed;
      [apply Hclosed; crush|];
      auto].
  rewrite rename_inverse_decl_ty; auto.
  rewrite subst_distr_decl_ty; auto.
  rewrite <- rename_closed_subst_exp;
    [
     |subst p;
      apply closed_subst_switch_exp
        with (p2:=p2)(e:=p')(p1:=c_ r)(n:=n) in H11;
      auto;
      apply H11;
      crush].

  (*apply has rule*)
  apply has_path with (t:=[p2 /t n] t').
  apply typing_p_subst with (G:=G)(p:=p)
                            (t:=t)(p1:=c_ r)(tp:=tp);
    auto.
  apply H with (r:=r)(tp:=tp); auto;
    apply closed_typing_p with (Sig:=Sig)(G:=G)(p:=p); auto.

  (*contains struct*)
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros m Hle; apply wf_closed_exp with (Sig:=Sig)(G:=G2); auto|].
  destruct t' as [ss| | | |]; simpl in *;
    try solve [inversion H1].
  rewrite raise_closed_le_exp with (n:=0);
    [|apply Hclosed_p2|crush].
  apply cont_struct.
  destruct (in_dty_subst_notin) with (ss:=ss)(s:=d)
                                     (p:=c_ r)(e:=c_ r)
                                     (n:=S n) as [s'' Ha]; auto;
    [inversion H1; subst; auto
    |inversion H3; subst; simpl in *; auto
    |destruct Ha as [Ha Hb]].
  inversion H1; subst.
  apply in_dty_subst_switch with (p1:=c_ r); auto;
    inversion H3; auto.

  (*contains upper*)
  destruct t' as [|p' l| | |];
    simpl in H3;
    try solve [inversion H3].

  destruct has_exists_subst with (Sig:=Sig)(G:=G)(p:=p)
                                 (s:=type L ext t)(r:=r)
                                 (n:=n)(G1:=G1)(G2:=G2)
                                 (p':=p') as [s Ha];
    inversion H3;
    subst p l;
    auto;
    [inversion H5; auto
    |apply closed_ty_sel with (l:=L); auto
    |destruct Ha as [Ha Hb];
     destruct s as [l' t'| | |];
     inversion Ha; subst L t].
  destruct contains_exists_subst with (Sig:=Sig)(G:=G)(t:=([v_ Var r /t n] t'))
                                      (s:=d)(r:=r)(n:=n)
                                      (G1:=G1)(G2:=G2)
                                      (t':=t') as [s Hc];
    auto;
    [inversion Hb; auto
    |apply closed_has, closed_decl_ty_upper in h; auto;
     apply closed_ty_sel in H12; auto
    |destruct Hc as [Hc Hd]].

  
  simpl; apply cont_upper with (t:=[p2 /t n] t');
    auto.
  assert (Hrewrite1 : (type l' ext ([p2 /t n] t')) =
                      ([p2 /s n] (type l' ext t')));
    [auto|rewrite Hrewrite1].
  apply H with (r0:=r)(tp:=tp); auto.
  inversion H5; auto.
  eapply closed_ty_sel; eauto.
  apply H0 with (r0:=r)(tp:=tp); auto.
  inversion Hb; auto.
  apply closed_has, closed_decl_ty_upper in h;
    auto;
    apply closed_ty_sel in H12; auto.

  (*contains equal*)
  destruct t' as [|p' l| | |];
    simpl in H3;
    try solve [inversion H3].

  destruct has_exists_subst with (Sig:=Sig)(G:=G)(p:=p)
                                 (s:=type L eqt t)(r:=r)
                                 (n:=n)(G1:=G1)(G2:=G2)
                                 (p':=p') as [s Ha];
    inversion H3;
    subst p l;
    auto;
    [inversion H5; auto
    |apply closed_ty_sel with (l:=L); auto
    |destruct Ha as [Ha Hb];
     destruct s as [| |l' t'|];
     inversion Ha; subst L t].
  destruct contains_exists_subst with (Sig:=Sig)(G:=G)(t:=([v_ Var r /t n] t'))
                                      (s:=d)(r:=r)(n:=n)
                                      (G1:=G1)(G2:=G2)
                                      (t':=t') as [s Hc];
    auto;
    [inversion Hb; auto
    |apply closed_has, closed_decl_ty_equal in h; auto;
     apply closed_ty_sel in H12; auto
    |destruct Hc as [Hc Hd]].
  
  simpl; apply cont_equal with (t:=[p2 /t n] t');
    auto.
  assert (Hrewrite1 : (type l' eqt ([p2 /t n] t')) =
                      ([p2 /s n] (type l' eqt t')));
    [auto|rewrite Hrewrite1].
  apply H with (r0:=r)(tp:=tp); auto.
  inversion H5; auto.
  eapply closed_ty_sel; eauto.
  apply H0 with (r0:=r)(tp:=tp); auto.
  inversion Hb; auto.
  apply closed_has, closed_decl_ty_equal in h;
    auto;
    apply closed_ty_sel in H12; auto.

Qed.



Lemma has_subst :
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig wf_st ->
              forall r n G1 G2 p' s',
                G = ([c_ r /env 0] G1) ++ G2 ->
                p = ([c_ r /e n] p') ->
                s = ([c_ r /s n] s') ->
                (c_ r) notin_e p' ->
                (c_ r) notin_s s' ->
                (c_ r) notin_env (G1 ++ G2) ->
                (c_ r) notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_exp p 0 ->
                Sig evdash G2 wf_env ->
                forall p2 tp,
                  closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                  Sig en G2 vdash (c_ r) pathType tp ->
                  Sig en G2 vdash p2 pathType tp ->
                  Sig en G2 vdash (c_ r) wf_e ->
                  Sig en G2 vdash p2 wf_e ->
                  Sig en G2 vdash tp wf_t ->
                  is_path p2 ->
                  Sig en ([p2 /env 0] G1) ++ G2 vdash ([p2 /e n] p') ni ([p2 /s n] s')).
Proof.
  destruct has_contains_subst_mutind; crush.
Qed.

Lemma contains_subst :
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig wf_st ->
              forall r n G1 G2 t' s',
                G = ([c_ r /env 0] G1) ++ G2 ->
                t = ([c_ r /t n] t') ->
                s = ([c_ r /s S n] s') ->
                (c_ r) notin_t t' ->
                (c_ r) notin_s s' ->
                (c_ r) notin_env (G1 ++ G2) ->
                (c_ r) notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_ty t 0 ->
                Sig evdash G2 wf_env ->
                forall p2 tp,
                  closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                  Sig en G2 vdash (c_ r) pathType tp ->
                  Sig en G2 vdash p2 pathType tp ->
                  Sig en G2 vdash (c_ r) wf_e ->
                  Sig en G2 vdash p2 wf_e ->
                  Sig en G2 vdash tp wf_t ->
                  is_path p2 ->
                  Sig en ([p2 /env 0] G1) ++ G2 vdash ([p2 /s S n] s') cont ([p2 /t n] t')).
Proof.
  destruct has_contains_subst_mutind; crush.
Qed.

Lemma subtyping_subst_mutind :
  (forall Sig G1 t1 t2 G2,
      Sig en G1 vdash t1 <; t2 dashv G2 ->
      Sig wf_st ->
      forall r n G3 G4 G t1' t2',
        G1 = ([c_ r /env 0] G3) ++ G ->
        G2 = ([c_ r /env 0] G4) ++ G ->
        t1 = ([c_ r /t n] t1') ->
        t2 = ([c_ r /t n] t2') ->
        (c_ r) notin_t t1' ->
        (c_ r) notin_t t2' ->
        (c_ r) notin_env (G3 ++ G) ->
        (c_ r) notin_env (G4 ++ G) ->
        (c_ r) notin_env Sig ->
        n = length G3 ->
        n = length G4 ->
        closed_env G1 0 ->
        closed_env G2 0 ->
        closed_env Sig 0 ->
        closed_ty t1 0 ->
        closed_ty t2 0 ->
        Sig evdash G wf_env ->
        forall p2 tp1 tp2,
          closed_env (([p2 /env 0] G3) ++ G) 0 ->
          closed_env (([p2 /env 0] G4) ++ G) 0 ->
          Sig en G vdash (c_ r) pathType tp1 ->
          Sig en G vdash p2 pathType tp1 ->
          Sig en G vdash (c_ r) pathType tp2 ->
          Sig en G vdash p2 pathType tp2 ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp1 wf_t ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp2 wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G3) ++ G) vdash ([p2 /t n] t1') <; ([p2 /t n] t2') dashv (([p2 /env 0] G4) ++ G)) /\
  
  (forall Sig G1 s1 s2 G2,
      Sig en G1 vdash s1 <;; s2 dashv G2 ->
      Sig wf_st ->
      forall r n G3 G4 G s1' s2',
        G1 = ([c_ r /env 0] G3) ++ G ->
        G2 = ([c_ r /env 0] G4) ++ G ->
        s1 = ([c_ r /s n] s1') ->
        s2 = ([c_ r /s n] s2') ->
        (c_ r) notin_s s1' ->
        (c_ r) notin_s s2' ->
        (c_ r) notin_env (G3 ++ G) ->
        (c_ r) notin_env (G4 ++ G) ->
        (c_ r) notin_env Sig ->
        n = length G3 ->
        n = length G4 ->
        closed_env G1 0 ->
        closed_env G2 0 ->
        closed_env Sig 0 ->
        closed_decl_ty s1 0 ->
        closed_decl_ty s2 0 ->
        Sig evdash G wf_env ->
        forall p2 tp1 tp2,
          closed_env (([p2 /env 0] G3) ++ G) 0 ->
          closed_env (([p2 /env 0] G4) ++ G) 0 ->
          Sig en G vdash (c_ r) pathType tp1 ->
          Sig en G vdash p2 pathType tp1 ->
          Sig en G vdash (c_ r) pathType tp2 ->
          Sig en G vdash p2 pathType tp2 ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp1 wf_t ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp2 wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G3) ++ G) vdash ([p2 /s n] s1') <;; ([p2 /s n] s2') dashv (([p2 /env 0] G4) ++ G)) /\

  (forall Sig G1 ss1 ss2 G2,
      Sig en G1 vdash ss1 <;;; ss2 dashv G2 ->
      Sig wf_st ->
      forall r n G3 G4 G ss1' ss2',
        G1 = ([c_ r /env 0] G3) ++ G ->
        G2 = ([c_ r /env 0] G4) ++ G ->
        ss1 = ([c_ r /ss n] ss1') ->
        ss2 = ([c_ r /ss n] ss2') ->
        (c_ r) notin_ss ss1' ->
        (c_ r) notin_ss ss2' ->
        (c_ r) notin_env (G3 ++ G) ->
        (c_ r) notin_env (G4 ++ G) ->
        (c_ r) notin_env Sig ->
        n = length G3 ->
        n = length G4 ->
        closed_env G1 0 ->
        closed_env G2 0 ->
        closed_env Sig 0 ->
        closed_decl_tys ss1 0 ->
        closed_decl_tys ss2 0 ->
        Sig evdash G wf_env ->
        forall p2 tp1 tp2,
          closed_env (([p2 /env 0] G3) ++ G) 0 ->
          closed_env (([p2 /env 0] G4) ++ G) 0 ->
          Sig en G vdash (c_ r) pathType tp1 ->
          Sig en G vdash p2 pathType tp1 ->
          Sig en G vdash (c_ r) pathType tp2 ->
          Sig en G vdash p2 pathType tp2 ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp1 wf_t ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp2 wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G3) ++ G) vdash ([p2 /ss n] ss1') <;;; ([p2 /ss n] ss2') dashv (([p2 /env 0] G4) ++ G)).
Proof.
  apply sub_mutind; intros; auto.

  (*s-top*)
  destruct t2'; simpl in H3; inversion H3; subst; auto.

  (*s-bot*)
  destruct t1'; simpl in H2; inversion H2; subst; auto.

  (*s-refl*)
  destruct t1' as [|p1' l1'| | |];
    simpl in H2;
    inversion H2;
    subst p L.
  destruct t2' as [|p' l'| | |];
    simpl in H3;
    inversion H3;
    subst l1'.
  apply subst_equality_exp in H31;
    [subst p1'; simpl; auto
    |inversion H4; auto
    |inversion H5; auto].

  (*s-arr*)
  destruct t1'0 as [| |t3 t3'| |];
    simpl in H4;
    inversion H4;
    subst t1 t1'.
  destruct t2'0 as [| |t4 t4'| |];
    simpl in H5;
    inversion H5;
    subst t2 t2'.
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hin; apply wf_closed_exp with (Sig:=Sig)(G:=G); auto|].
  simpl;
    rewrite raise_closed_le_exp with (n:=0); auto.
  apply s_arr with (i:=length G1).
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_ty_arr; eauto].
  rewrite app_length, subst_length,
  <- subst_length with (G:=G3)(p:=c_ r)(n:=0), <- app_length;
    subst; auto.
  rewrite app_length, subst_length,
  <- subst_length with (G:=G4)(p:=c_ r)(n:=0), <- app_length;
    subst; auto.
  assert (Hleng1 : ([p2 /t n] t3) :: ([p2 /env 0] G3) ++ G = ([p2 /env 0](t3 :: G3)) ++ G);
    [rewrite subst_cons; subst; auto|].
  assert (Hleng2 : ([p2 /t n] t4) :: ([p2 /env 0] G4) ++ G = ([p2 /env 0](t4 :: G4)) ++ G);
    [rewrite subst_cons; subst; rewrite H12; auto|].
  rewrite Hleng1, Hleng2.
  rewrite closed_subst_distr_type with (t:=t3'); auto.
  rewrite closed_subst_distr_type with (t:=t4'); auto.
  apply H0 with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [apply unbound_var_notin_type, unbound_subst_components_type;
               [apply notin_var_unbound_type;
                inversion H6;
                inversion H7;
                auto|];
               inversion H26;
               inversion H28;
               subst;
               apply ub_var, ub_con, Nat.lt_neq;
               rewrite app_length;
               apply Nat.lt_lt_add_l; auto];
    try solve [rewrite subst_cons;
               simpl; apply closed_cons;
               auto;
               apply closed_subst_switch_type with (p1:=c_ r); auto;
               try (rewrite <- H11);
               try (rewrite <- H12);
               try (eapply closed_ty_arr with (t1:=[c_ r /t n] t3); subst; eauto);
               try (eapply closed_ty_arr with (t1:=[c_ r /t n] t4); subst; eauto)];
    try solve [apply closed_cons;
               auto;
               eapply closed_ty_arr;
               eauto];
    try solve [apply closed_subst_hole_type;
               [|auto];
               eapply closed_ty_arr;
               eauto];
    try solve [subst; simpl;
               rewrite subst_cons;
               simpl;
               try (rewrite H12);
               auto];
    try solve [subst;
               simpl;
               rewrite closed_subst_distr_type;
               auto];
    try solve [intros t Hin;
               simpl in Hin;
               destruct Hin; subst; auto;
               inversion H6; inversion H7; subst; auto];
    try solve [simpl in *; auto].

  (*s_upper1*)
  destruct t1' as [|p' l'| | |];
    simpl in H3;
    inversion H3;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G1)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' ext t1)
                                 (r:=r)(n:=n)(G1:=G3)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [l'' t'| | | ];
     inversion Ha;
     subst l'' t1].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_upper; eauto|].
  apply s_upper1 with (t1:=[p2 /t n]t').
  assert (Hrewrite : (type l' ext ([p2 /t n] t')) =
                     ([p2 /s n] (type l' ext t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G1)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' ext t')))(r:=r)(tp:=tp1);
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_upper2*)
  destruct t1' as [|p' l'| | |];
    simpl in H3;
    inversion H3;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G2)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' ext t1)
                                 (r:=r)(n:=n)(G1:=G4)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [l'' t'| | | ];
     inversion Ha;
     subst l'' t1].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_upper; eauto|].
  apply s_upper2 with (t1:=[p2 /t n]t').
  assert (Hrewrite : (type l' ext ([p2 /t n] t')) =
                     ([p2 /s n] (type l' ext t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G2)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' ext t')))(r:=r)(tp:=tp1);
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_lower1*)
  destruct t2' as [|p' l'| | |];
    simpl in H4;
    inversion H4;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G2)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' sup t2)
                                 (r:=r)(n:=n)(G1:=G4)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [|l'' t'| | ];
     inversion Ha;
     subst l'' t2].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_lower; eauto|].
  apply s_lower1 with (t2:=[p2 /t n]t').
  assert (Hrewrite : (type l' sup ([p2 /t n] t')) =
                     ([p2 /s n] (type l' sup t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G2)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' sup t')))(r:=r)(tp:=tp2);
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_lower2*)
  destruct t2' as [|p' l'| | |];
    simpl in H4;
    inversion H4;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G1)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' sup t2)
                                 (r:=r)(n:=n)(G1:=G3)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [|l'' t'| | ];
     inversion Ha;
     subst l'' t2].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_lower; eauto|].
  apply s_lower2 with (t2:=[p2 /t n]t').
  assert (Hrewrite : (type l' sup ([p2 /t n] t')) =
                     ([p2 /s n] (type l' sup t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G1)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' sup t')))(r:=r)(tp:=tp2);
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_equal1*)
  destruct t1' as [|p' l'| | |];
    simpl in H3;
    inversion H3;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G1)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' eqt t1)
                                 (r:=r)(n:=n)(G1:=G3)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| |l'' t'| ];
     inversion Ha;
     subst l'' t1].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_equal; eauto|].
  apply s_equal1 with (t1:=[p2 /t n]t').
  assert (Hrewrite : (type l' eqt ([p2 /t n] t')) =
                     ([p2 /s n] (type l' eqt t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G1)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' eqt t')))(r:=r)(tp:=tp1);
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_equal2*)
  destruct t2' as [|p' l'| | |];
    simpl in H4;
    inversion H4;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G2)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' eqt t2)
                                 (r:=r)(n:=n)(G1:=G4)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| |l'' t'| ];
     inversion Ha;
     subst l'' t2].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_equal; eauto|].
  apply s_equal2 with (t2:=[p2 /t n]t').
  assert (Hrewrite : (type l' eqt ([p2 /t n] t')) =
                     ([p2 /s n] (type l' eqt t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G2)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' eqt t')))(r:=r)(tp:=tp2);
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_equal3*)
  destruct t1' as [|p' l'| | |];
    simpl in H3;
    inversion H3;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G2)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' eqt t1)
                                 (r:=r)(n:=n)(G1:=G4)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| |l'' t'| ];
     inversion Ha;
     subst l'' t1].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_equal; eauto|].
  apply s_equal3 with (t1:=[p2 /t n]t').
  assert (Hrewrite : (type l' eqt ([p2 /t n] t')) =
                     ([p2 /s n] (type l' eqt t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G2)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' eqt t')))(r:=r)(tp:=tp1);
    auto;
    [inversion H5; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_equal2*)
  destruct t2' as [|p' l'| | |];
    simpl in H4;
    inversion H4;
    subst p L;
    simpl.
  destruct has_exists_subst with (Sig:=Sig)(G:=G1)
                                 (p:=[v_ Var r /e n] p')
                                 (s:=type l' eqt t2)
                                 (r:=r)(n:=n)(G1:=G3)
                                 (G2:=G)(p':=p') as [s' Ha];
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| |l'' t'| ];
     inversion Ha;
     subst l'' t2].
  assert (closed_ty ([v_ Var r /t n] t') 0);
    [apply closed_has in h; auto;
     [|eapply closed_ty_sel; eauto];
     eapply closed_decl_ty_equal; eauto|].
  apply s_equal4 with (t2:=[p2 /t n]t').
  assert (Hrewrite : (type l' eqt ([p2 /t n] t')) =
                     ([p2 /s n] (type l' eqt t')));
    [auto|rewrite Hrewrite].
  apply has_subst with (G:=G1)(p:=[c_ r /e n] p')(s:=([v_ Var r /s n] (type l' eqt t')))(r:=r)(tp:=tp2);
    auto;
    [inversion H6; auto
    |eapply closed_ty_sel; eauto].
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    inversion Hb; auto.

  (*s_struct*)
  destruct t1' as [ss1'| | | |];
    inversion H3;
    subst ds1;
    destruct t2' as [ss2'| | | |];
    inversion H4;
    subst ds2.

  rewrite closed_subst_distr_decl_tys with (ss:=ss1') in s; auto;
    rewrite closed_subst_distr_decl_tys with (ss:=ss2') in s; auto.
  simpl; apply s_struct with (i:=i); auto;
    [subst;
     repeat rewrite app_length, subst_length; auto
    |subst;
     rewrite e0;
     repeat rewrite app_length, subst_length; auto
    |].
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hin; apply wf_closed_exp with (Sig:=Sig)(G:=G); auto|].
  rewrite raise_closed_le_exp with (n:=0); auto.
  assert (Hrewrite1 : (str ([p2 /ss S n] ss1') rts :: ([p2 /env 0] G3) ++ G) =
                      (([p2 /env 0](str ss1' rts:: G3)) ++ G));
    [rewrite subst_cons;
     simpl;
     rewrite  raise_closed_le_exp with (n:=0);
     subst; auto|rewrite Hrewrite1];
    assert (Hrewrite2 : (str ([p2 /ss S n] ss2') rts :: ([p2 /env 0] G4) ++ G) =
                        (([p2 /env 0](str ss2' rts:: G4)) ++ G));
    [rewrite subst_cons;
     simpl;
     rewrite  raise_closed_le_exp with (n:=0);
     subst;
     auto;
     rewrite H11;
     auto
    |rewrite Hrewrite2].
  rewrite closed_subst_distr_decl_tys with (ss:=ss1'); auto.
  rewrite closed_subst_distr_decl_tys with (ss:=ss2'); auto.
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [simpl in *; auto];
    try solve [subst; simpl;
               rewrite subst_cons;
               simpl;
               try (rewrite H11);
               auto];
    try solve [rewrite closed_subst_distr_decl_tys;
               auto];
    try solve [apply unbound_var_notin_decl_tys, unbound_subst_components_decl_tys;
               [apply notin_var_unbound_decl_tys;
                inversion H5;
                inversion H6;
                auto|];
               inversion H25;
               inversion H27;
               subst;
               apply ub_var, ub_con, Nat.lt_neq;
               rewrite app_length;
               apply Nat.lt_lt_add_l; auto];
    try solve [intros t Hin;
               simpl in Hin;
               destruct Hin; subst; auto;
               inversion H6; inversion H7; subst; auto];
    try solve [apply closed_subst_hole_decl_tys;
               [|auto];
               eapply closed_ty_str;
               eauto];
    try solve [rewrite subst_cons;
               apply closed_cons;
               auto;
               try (rewrite <- H10);
               try (rewrite <- H11);
               apply closed_subst_switch_type with (p1:= c_ r);
               auto].

  (*sd_upper*)
  destruct s1' as [l t1'| | |];
    inversion H3;
    subst L t1;
    destruct s2' as [l' t2'| | |];
    inversion H4;
    subst l t2.
  simpl; apply sd_upper, H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [inversion H5; auto];
    try solve [inversion H6; auto];
    try solve [eapply closed_decl_ty_upper;
               eauto].

  (*sd_lower*)
  destruct s1' as [|l t1'| |];
    inversion H3;
    subst L t1;
    destruct s2' as [|l' t2'| |];
    inversion H4;
    subst l t2.
  simpl; apply sd_lower, H with (r0:=r)(tp1:=tp2)(tp2:=tp1); auto;
    try solve [inversion H5; auto];
    try solve [inversion H6; auto];
    try solve [eapply closed_decl_ty_lower;
               eauto].

  (*sd_eq_up*)
  destruct s1' as [| |l t1'|];
    inversion H3;
    subst L t1;
    destruct s2' as [l' t2'| | |];
    inversion H4;
    subst l t2.
  simpl; apply sd_eq_up, H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [inversion H5; auto];
    try solve [inversion H6; auto];
    try solve [eapply closed_decl_ty_upper;
               eauto];
    try solve [eapply closed_decl_ty_equal;
               eauto].

  (*sd_eq_lo*)
  destruct s1' as [|l t1'| |];
    inversion H3;
    subst L t1;
    destruct s2' as [| |l' t2'|];
    inversion H4;
    subst l t2.
  simpl; apply sd_eq_lo, H with (r0:=r)(tp1:=tp2)(tp2:=tp1); auto;
    try solve [inversion H5; auto];
    try solve [inversion H6; auto];
    try solve [eapply closed_decl_ty_lower;
               eauto];
    try solve [eapply closed_decl_ty_equal;
               eauto].

  (*sd_equal*)
  destruct s1' as [| |l t1'|];
    inversion H4;
    subst L t1;
    destruct s2' as [| |l' t2'|];
    inversion H5;
    subst l t2.
  simpl; apply sd_equal.
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_decl_ty_equal;
               eauto].
  apply H0 with (r0:=r)(tp1:=tp2)(tp2:=tp1); auto;
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_decl_ty_equal;
               eauto].

  (*sd_value*)
  destruct s1' as [| | |l1' t1'];
    inversion H4;
    subst l t1;
    destruct s2' as [| | |l2' t2'];
    inversion H5;
    subst l1' t2.
  simpl; apply sd_value.
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_decl_ty_value;
               eauto].
  apply H0 with (r0:=r)(tp1:=tp2)(tp2:=tp1); auto;
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_decl_ty_value;
               eauto].

  (*s_nil*)
  destruct ss1';
    inversion H2;
    destruct ss2';
    inversion H3;
    subst;
    auto.

  (*s_cons*)
  destruct ss1' as [|s1 ss1];
    inversion H4;
    subst d1 ds1.
  destruct ss2' as [|s2 ss2];
    inversion H5;
    subst d2 ds2.
  simpl;
    apply sd_cons.
  apply H with (r0:=r)(tp1:=tp1)(tp2:=tp2); auto;
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_decl_tys_con;
               eauto].
  apply H0 with (r0:=r)(tp1:=tp1)(tp2:=tp2);
    try solve [inversion H6; auto];
    try solve [inversion H7; auto];
    try solve [eapply closed_decl_tys_con;
               eauto].
Qed.

Lemma subtyping_subst_type :
  (forall Sig G1 t1 t2 G2,
      Sig en G1 vdash t1 <; t2 dashv G2 ->
      Sig wf_st ->
      forall r n G3 G4 G t1' t2',
        G1 = ([c_ r /env 0] G3) ++ G ->
        G2 = ([c_ r /env 0] G4) ++ G ->
        t1 = ([c_ r /t n] t1') ->
        t2 = ([c_ r /t n] t2') ->
        (c_ r) notin_t t1' ->
        (c_ r) notin_t t2' ->
        (c_ r) notin_env (G3 ++ G) ->
        (c_ r) notin_env (G4 ++ G) ->
        (c_ r) notin_env Sig ->
        n = length G3 ->
        n = length G4 ->
        closed_env G1 0 ->
        closed_env G2 0 ->
        closed_env Sig 0 ->
        closed_ty t1 0 ->
        closed_ty t2 0 ->
        Sig evdash G wf_env ->
        forall p2 tp1 tp2,
          closed_env (([p2 /env 0] G3) ++ G) 0 ->
          closed_env (([p2 /env 0] G4) ++ G) 0 ->
          Sig en G vdash (c_ r) pathType tp1 ->
          Sig en G vdash p2 pathType tp1 ->
          Sig en G vdash (c_ r) pathType tp2 ->
          Sig en G vdash p2 pathType tp2 ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp1 wf_t ->
          Sig en G vdash (c_ r) wf_e ->
          Sig en G vdash p2 wf_e ->
          Sig en G vdash tp2 wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G3) ++ G) vdash ([p2 /t n] t1') <; ([p2 /t n] t2') dashv (([p2 /env 0] G4) ++ G)).
Proof.
  destruct subtyping_subst_mutind; crush. 
Qed.



Lemma typing_exists_subst_decl :
  (forall Sig G d s p n, Sig en G vdash ([p /d n] d) hasType_d s ->
                  p notin_d d ->
                  exists s', (s = [p /s n] s') /\
                        (p notin_s s')).
Proof.
  intros;
    destruct d;
    inversion H;
    subst.

  exists (type l eqt t); split; auto.
  inversion H0; auto.

  exists (val l oft t); split; auto.
  inversion H0; auto.    
Qed.

Lemma typing_exists_subst_decls :
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                forall ds' p n,
                  ds = ([p /ds n] ds') ->
                  p notin_ds ds' ->
                  exists ss', (ss = [p /ss n] ss') /\
                         (p notin_ss ss')).
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp; intros; subst.

  exists dt_nil; auto.

  destruct ds' as [|d' ds'];
    inversion H0;
    subst d ds.
  destruct IHHtyp with (ds'0:=ds')(p0:=p)(n0:=n) as [ss' Ha];
    auto;
    try solve [inversion H1; auto];
    destruct Ha as [Ha Hb];
    subst.
  destruct typing_exists_subst_decl with (Sig:=Sig)(G:=G)(d:=d')
                                         (s:=s)(p:=p)
                                         (n:=n) as [s' Hd]; auto.
  inversion H1; auto.
  destruct Hd; subst.
  exists (dt_con s' ss'); auto.
Qed.


Lemma typing_exists_subst_exp :
  (forall Sig G e t, Sig en G vdash e hasType t ->
              Sig wf_st ->
              forall r G1 G2 n e',
                G =([c_ r /env 0] G1) ++ G2 ->
                e = ([c_ r /e n] e') ->
                (c_ r) notin_e e' ->
                (c_ r) notin_env (G1 ++ G2) ->
                (c_ r) notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_exp e 0 ->
                Sig en G2 vdash (c_ r) wf_e ->
                exists t', (t = [c_ r /t n] t') /\
                           (c_ r) notin_t t').
Proof.
  intros Sig G e t Htyp;
    induction Htyp; intros; auto.
  

  (*var*)
  destruct typing_p_exists_subst
    with (Sig:=Sig)(G:=G)(p1:=c_ r)(p:=[c_ r /e n0] e')(t:=t)
         (G1:=G1)(G2:=G2)(n:=n0)(p':=e') as [t' Ha]; auto;
    try solve [rewrite <- H2;
               auto];
    destruct Ha as [Ha Hb];
    exists t'; auto.

  (*loc*)
  destruct typing_p_exists_subst
    with (Sig:=Sig)(G:=G)(p1:=c_ r)(p:=[c_ r /e n] e')(t:=t)
         (G1:=G1)(G2:=G2)(n:=n)(p':=e') as [t' Ha]; auto;
    try solve [rewrite <- H2;
               auto];
    destruct Ha as [Ha Hb];
    exists t'; auto.

  (*cast*)
  destruct e' as [| | | | | |ec tc];
    try solve [inversion H2];
    try solve [simpl in H2;
               destruct v as [|x]; inversion H2;
               destruct (n =? x); inversion H2];
    inversion H2; subst e t.
  exists tc; split; auto.
  inversion H3; auto.
  
  (*fn*)
  destruct e' as [| |t1' e0 t2'| | | |];
    inversion H1;
    [subst t1 e t2
    |destruct v as [x|x];
     [inversion H11
     |destruct (n =? x);
      inversion H11]].
  exists (t1' arr t2'); split; auto.
  inversion H2; auto.
  
  (*app*)
  destruct e'0 as [|e1' e2'| | | | |];
    inversion H3;
    [subst e e'
    |destruct v as [x|x];
     [inversion H13
     |destruct (n =? x);
      inversion H13]].
  destruct IHHtyp1 with (r0:=r)(G1:=G1)(G2:=G2)(n0:=n)(e':=e1') as [tarr Ha];
    auto;
    try solve [inversion H4; auto];
    try solve [apply closed_exp_app in H10;
               destruct H10;
               auto];
    try solve [inversion H11; auto].
  destruct tarr as [ | |t1' t2'| |];
    destruct Ha as [Ha Hb];
    inversion Ha;
    subst t1 t2.
  exists (t2' [S n maps_t n]); split;
    [
     |inversion Hb; subst;
      apply notin_rename_type; auto].
  apply rename_closed_subst_type.
  apply closed_typing_exp in Htyp1; auto;
    try solve [apply closed_exp_app in H10;
               destruct H10;
               auto].
  destruct n as [|n'];
    [|eapply closed_ty_arr; eauto; crush].
  apply H0.
  apply closed_ty_arr in Htyp1;
    destruct Htyp1; auto.
  
  (*app path*)
  destruct e' as [|e1 e2| | | | |];
    inversion H3;
    try solve [destruct v as [x|x];
               [inversion H13
               |destruct (n =? x);
                inversion H13]];
    subst e p.
  destruct IHHtyp with (r0:=r)(G1:=G1)
                       (G2:=G2)(n0:=n)
                       (e':=e1) as [t'' Ha]; auto;
    try solve [inversion H4; auto];
    try solve [apply closed_exp_app in H10;
               destruct H10;
               auto];
    try solve [inversion H11; auto];
    destruct t'' as [| |t1' t2'| |];
    destruct Ha as [Ha Hb];
    inversion Ha;
    subst t1 t2.
  assert (Hrewrite :(([c_ r /e n] e2) cast ([c_ r /t n] t1')) = ([c_ r /e n](e2 cast t1')));
    [auto|rewrite Hrewrite].
  apply closed_exp_app in H10;
    destruct H10 as [Hc Hd].
  apply closed_typing_exp in Htyp; auto.
  apply closed_ty_arr in Htyp;
    destruct Htyp as [He Hf].
  rewrite rename_closed_subst_exp with (m:=S n).
  rewrite <- subst_distr_type; auto.
  rewrite rename_closed_subst_type with (m:=n).
  exists ((([(e2 cast t1') [n maps_e S n] /t 0] t2') [S n maps_t n])); split; auto;
    apply notin_rename_type; auto;
      apply unbound_var_notin_type;
      apply unbound_subst_components_type;
      [inversion Hb; subst;
       apply notin_var_unbound_type;
       auto
      |];
      apply notin_var_unbound_exp, notin_rename_exp; auto;
        inversion H4;
        inversion Hb;
        subst;
        apply ni_cast;
        auto;
        crush.
  
  rewrite subst_distr_type; simpl; auto.
  assert (Hrewrite1 : ([v_ Var r /e S n] (e2 [n maps_e S n])) =
                      ([v_ Var r /e n] e2));
    [rewrite rename_closed_subst_exp with (e:=e2)(m:=S n);
     auto;
     try solve [apply Hd; crush]
    |rewrite Hrewrite1].
  assert (Hrewrite2 : ([v_ Var r /t S n] (t1' [n maps_t S n])) =
                      ([v_ Var r /t n] (t1')));
    [rewrite rename_closed_subst_type with (t:=t1')(m:=S n);
     auto;
     try solve [apply He; crush]
    |rewrite Hrewrite2].
  destruct n as [|n'].
  apply closed_subst_hole_type; auto.
  apply closed_exp_cast; split; auto.
  apply closed_subst_components_type with
      (p:=([v_ Var r /e S n'] e2) cast ([v_ Var r /t S n'] t1'))(m:=0) in Hf.
  apply Hf; crush.
  apply closed_exp_cast; split;
    [intros m Hle; apply Hd; crush
    |intros m Hle; apply He; crush].
  simpl; apply cl_cast;
    [apply Hd; crush
    |apply He; crush].

  (*new*)
  destruct e' as [ds'| | | | | |];
    inversion H3;
    try solve [destruct v as [x|x];
               [inversion H13
               |destruct (n =? x);
                inversion H13]];
    subst ds.
  rewrite closed_subst_distr_decls in H; auto.
  destruct (typing_exists_subst_decls H)
    with (ds'0:=[c_ (length G) /ds 0] ds')
         (p:=c_ r)(n0:=S n) as [ss' Ha]; auto;
    [apply unbound_var_notin_decls,
     unbound_subst_components_decls;
     [inversion H4; subst;
      apply notin_var_unbound_decls;
      auto
     |inversion H11; subst;
      apply ub_var, ub_con;
      apply Nat.lt_neq;
      rewrite app_length;
      crush]
    |destruct Ha as [Ha Hb]].
  destruct (differing_subst_equality_decl_tys Ha) as [ss'' Hc]; auto;
    try solve [inversion H11; subst;
               apply ni_var;
               intro Hcontra;
               inversion Hcontra; subst;
               rewrite app_length in H7;
               try (rewrite H7 in H15);
               try (rewrite <- H7 in H15); crush];
    destruct Hc as [Hc Hd];
    subst ss.
  exists (str ss'' rts); subst; simpl; split; auto.

  (*acc path*)
  destruct e' as [| | |p' l'| | |];
    inversion H2;
    try solve [destruct v as [x|x];
               [inversion H12
               |destruct (n =? x);
                inversion H12]];
    subst p l.
  destruct (has_exists_subst H)
    with (r0:=r)(n0:=n)
         (G1:=G1)(G2:=G2)
         (p'0:=p')
    as [s' Ha]; auto;
    try solve [inversion H3; auto];
    try solve [eapply closed_exp_acc; eauto];
    destruct Ha as [Ha Hb];
    destruct s';
    inversion Ha;
    subst l' t.
  exists t0; split; auto.
  inversion Hb; auto.

  (*acc*)
  destruct e' as [| | |e0' l'| | |];
    inversion H3;
    try solve [destruct v as [x|x];
               [inversion H13
               |destruct (n =? x);
                inversion H13]].
  destruct IHHtyp with (r:=r)(G1:=G1)(G2:=G2)(n:=n)(e':=e0') as [t'' Ha];
    auto;
    try solve [inversion H4; auto];
    try solve [apply closed_exp_acc in H10; auto];
    destruct Ha as [Ha Hb];
    subst t' l'.
  destruct (contains_exists_subst H)
    with (r0:=r)(n0:=n)
         (G1:=G1)(G2:=G2)
         (t':=t'')
    as [s' Hc];
    auto;
    [apply closed_typing_exp
       with (Sig:=Sig)(G:=G)(e:=e);
     auto;
     eapply closed_exp_acc; eauto
    |destruct Hc as [Hc Hd];
     destruct s';
     inversion Hc;
     subst l t].
  exists (t0[S n maps_t n]); split;
    [|apply notin_rename_type; 
      inversion Hd;
      auto].
  assert (Hclosed : closed_ty ([c_ r /t S n] t0) 0);
    [|].
  intros n' Hin.
  apply H0.
  apply closed_typing_exp in Htyp; auto.
  eapply closed_exp_acc; eauto.
  
  rewrite rename_closed_subst_type
    with (n:=S n)(m:=n); auto.
  apply Hclosed; crush.
Qed.

Lemma typing_subst_mutind :
  (forall Sig G e t,
      Sig en G vdash e hasType t ->
      Sig wf_st ->
      forall r n G1 G2 e' t',
        G = ([c_ r /env 0] G1) ++ G2 ->
        e = ([c_ r /e n] e') ->
        t = ([c_ r /t n] t') ->
        (c_ r) notin_e e' ->
        (c_ r) notin_t t' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_exp e 0 ->
        closed_ty t 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /e n] e') hasType ([p2 /t n] t')) /\
  
  (forall Sig G d s, Sig en G vdash d hasType_d s ->
              Sig wf_st ->
              forall G1 G2 d' s' r n,
                G = (([c_ r /env 0]G1) ++ G2) ->
                d = ([c_ r /d n]d') ->
                s = ([c_ r /s n]s') ->
                c_ r notin_d d' ->
                c_ r notin_s s' ->
                c_ r notin_env (G1 ++ G2) ->
                c_ r notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_decl d 0 ->
                closed_decl_ty s 0 ->
                Sig evdash G2 wf_env ->
                forall p2 tp,
                  closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                  Sig en G2 vdash (c_ r) pathType tp ->
                  Sig en G2 vdash p2 pathType tp ->
                  Sig en G2 vdash (c_ r) wf_e ->
                  Sig en G2 vdash p2 wf_e ->
                  Sig en G2 vdash tp wf_t ->
                  is_path p2 ->
                  Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /d n] d') hasType_d ([p2 /s n] s')) /\
  
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                Sig wf_st ->
                forall G1 G2 ds' ss' r n,
                  G = (([c_ r /env 0]G1) ++ G2) ->
                  ds = ([c_ r /ds n]ds') ->
                  ss = ([c_ r /ss n]ss') ->
                  c_ r notin_ds ds' ->
                  c_ r notin_ss ss' ->
                  c_ r notin_env (G1 ++ G2) ->
                  c_ r notin_env Sig ->
                  n = length G1 ->
                  closed_env G 0 ->
                  closed_env Sig 0 ->
                  closed_decls ds 0 ->
                  closed_decl_tys ss 0 ->
                  Sig evdash G2 wf_env ->
                  forall p2 tp,
                    closed_env (([p2 /env 0] G1) ++ G2) 0 ->
                    Sig en G2 vdash (c_ r) pathType tp ->
                    Sig en G2 vdash p2 pathType tp ->
                    Sig en G2 vdash (c_ r) wf_e ->
                    Sig en G2 vdash p2 wf_e ->
                    Sig en G2 vdash tp wf_t ->
                    is_path p2 ->
                    Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /ds n] ds') hasType_ds ([p2 /ss n] ss')).
Proof.
  apply typing_mutind; intros.

  (*var*)
  destruct e' as [| | | |v|i'|];
    inversion H1.
  assert (Hptyp := H0);
    apply typing_p_subst
      with
        (Sig:=Sig)(G:=G)(p:=[c_ r /e n0](v_ v))
        (t:=t)(p1:=c_ r)(G1:=G1)
        (G2:=G2)(n:=n0)(p':=v_ v)
        (t':=t')(p2:=p2)(tp:=tp)
    in Hptyp;
    auto;
    [|rewrite <- H1; auto].
  destruct v as [x|x];
    simpl in *;
    [inversion Hptyp; auto
    |destruct (n0 =? x);
     [|inversion Hptyp]].
  apply path_typing_implies_typing; auto.
  apply wf_weakening_actual_exp; auto.

  (*loc*)
  destruct e' as [| | | |v| |];
    inversion H1.
  assert (Hptyp := H0);
    apply typing_p_subst
      with
        (Sig:=Sig)(G:=G)(p:=[c_ r /e n](v_ v))
        (t:=t)(p1:=c_ r)(G1:=G1)
        (G2:=G2)(n:=n)(p':=v_ v)
        (t':=t')(p2:=p2)(tp:=tp)
    in Hptyp;
    auto;
    [|rewrite <- H1; auto].
  destruct v as [x|x];
    simpl in *;
    [inversion Hptyp; auto
    |destruct (n =? x);
     [|inversion Hptyp]].
  apply path_typing_implies_typing; auto.
  apply wf_weakening_actual_exp; auto.
  
  assert (Hptyp := H0);
    apply typing_p_subst
      with
        (Sig:=Sig)(G:=G)(p:=i_ i)
        (t:=t)(p1:=c_ r)(G1:=G1)
        (G2:=G2)(n:=n)(p':=i_ i)
        (t':=t')(p2:=p2)(tp:=tp)
    in Hptyp;
    auto.
  simpl in *;
    inversion H1; subst n0.
  apply path_typing_implies_typing; auto.
  apply wf_loc.
  unfold mapping in e;
    apply get_some_index in e.
  rewrite rev_length in e; auto.

  (*cast*)
  destruct e' as [| | | | | |e'' t''];
    inversion H2;
    try solve [destruct v as [n'|n'];
               inversion H22;
               destruct (n =? n');
               inversion H22];
    subst e t.      
  destruct (typing_exists_subst_exp t0)
    with
      (r0:=r)(G1:=G1)
      (G2:=G2)(n0:=n)
      (e':=e'')
    as
      [t Ha];
    auto;
    try solve [inversion H4; auto];
    try solve [eapply closed_exp_cast; eauto];
    destruct Ha as [Ha Hb].
  apply subst_equality_type in H23;
    auto;
    [subst t'0|inversion H4; auto].
  simpl; apply t_cast with (t':=[p2 /t n] t).
  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H4; auto
    |eapply closed_exp_cast; eauto
    |apply closed_typing_exp with (Sig:=Sig)(G:=G)(e:=[c_ r /e n] e''); auto;
     eapply closed_exp_cast; eauto].

  apply subtyping_subst_type
    with (G1:=G)(G2:=G)
         (t1:=t')(t2:=[c_ r /t n]t'')
         (r:=r)(tp1:=tp)(tp2:=tp);
    auto.
  apply closed_typing_exp with (Sig:=Sig)(G:=G)(e:=[c_ r /e n] e''); auto;
    eapply closed_exp_cast; eauto.

  (*fn*)
  destruct e' as [| |t1' e0' t2'| | | |];
    inversion H2;
    [subst t1 e t2
    |destruct v as [|x]; inversion H22;
     destruct (n =? x); inversion H22].
  destruct t' as [| |t1'' t2''| |];
    inversion H3.
  apply subst_equality_type in H22; auto;
    try solve [inversion H4; auto];
    try solve [inversion H5; auto];
    subst t1''.
  apply subst_equality_type in H23; auto;
    try solve [inversion H4; auto];
    try solve [inversion H5; auto];
    subst t2''.
  simpl; apply t_fn.
  
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; apply wf_closed_exp with (Sig:=Sig)(G:=G2); auto|].
  assert (Hneq_r : r < (length G2));
    [inversion H17;
     auto|].
  rewrite raise_closed_le_exp with (n:=0); auto.
  rewrite closed_subst_distr_type; auto.
  rewrite closed_subst_distr_exp; auto.
  assert (Hrewrite : ([p2 /t n] t1') :: ([p2 /env 0] G1) ++ G2 =
                     (([p2 /env 0](t1'::G1)) ++ G2));
    [rewrite subst_cons; subst; auto
    |rewrite Hrewrite].
  apply H with (r0:=r)(tp:=tp); auto;
    try solve [rewrite subst_cons; subst; auto];
    try solve [try (rewrite closed_subst_distr_exp);
               try (rewrite closed_subst_distr_type);
               auto;
               subst;
               repeat rewrite app_length, subst_length;
               auto];
    try solve [try (apply unbound_var_notin_exp, unbound_subst_components_exp;
                    [apply notin_var_unbound_exp; inversion H4; auto
                    |]);
               try (apply unbound_var_notin_type, unbound_subst_components_type;
                    [apply notin_var_unbound_type; inversion H4; auto
                    |]);
               apply ub_var, ub_con, Nat.lt_neq;
               rewrite app_length, subst_length;
               crush];
    try solve [intros t' Hin; inversion Hin;
               [subst t1'; inversion H5; auto
               |apply H6; auto]];
    try solve [intros t' Hin; inversion Hin;
               [subst t';
                eapply closed_ty_arr; eauto
               |apply H9; auto]];
    try solve [try (apply closed_subst_hole_exp);
               try (apply closed_subst_hole_type);
               auto;
               eapply closed_exp_fn; eauto].
  intros t' Hin;
    apply in_app_or in Hin;
    destruct Hin as [Hin|];
    [|apply H14, in_or_app; auto];
    rewrite subst_cons in Hin; inversion Hin;
      [subst t'
      |apply H14, in_or_app; auto].
  simpl.
  apply closed_subst_switch_type with (p1:=c_ r); auto.
  eapply closed_ty_arr; subst n; eauto.

  (*app*)
  destruct e'0 as [|e1' e2'| | | | |];
    inversion H3;
    [subst e e'
    |destruct v as [|x];
     [|destruct (n =? x)];
     inversion H23].
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros t'' Hle; eapply wf_closed_exp; eauto|].
  destruct (typing_exists_subst_exp t)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e':=e1')
    as [tarr Ha];
    auto;
    try solve [inversion H5; auto];
    try solve [eapply closed_exp_app in H12;
               destruct H12; auto];
    destruct Ha as [Ha Hb];
    destruct tarr as [| |t1' t2'| |];
    inversion Ha;
    subst t1 t2.
  rewrite H24 in t.

  assert (Hrewrite1 := H24).
  rewrite rename_closed_subst_type
    with
      (n:=n)
      (m:=S n)
    in H24;
    [|apply H13; crush].
  apply subst_equality_type in H24; auto;
    [|apply notin_rename_type; auto
     |inversion Hb; auto].
  destruct (typing_exists_subst_exp t0)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e':=e2')
    as [t'' Hc];
    auto;
    [inversion H5; auto
    |eapply closed_exp_app; eauto
    |destruct Hc as [Hc Hd];
     subst t'].
  assert (Hclosed_t'' : closed_ty ([v_ Var r /t n] t'') 0);
    [eapply closed_typing_exp; eauto;
     eapply closed_exp_app in H12;
     destruct H12;
     eauto|].
  assert (Hclosed_t1' : closed_ty (([v_ Var r /t n] t1') arr (([v_ Var r /t S n] t2'))) 0);
    [eapply closed_typing_exp; eauto;
     eapply closed_exp_app in H12;
     destruct H12;
     eauto|].

  simpl;
    apply t_app
      with
        (t1:=[p2 /t n]t1')
        (t':=[p2 /t n] t'');
    auto.
  rewrite rename_closed_subst_type
    with
      (t:=t'0)
      (n:=n)
      (m:=S n);
    [rewrite H24
    |apply closed_subst_switch_type
       with
         (p2:=p2)
      in H13;
     [apply H13; crush|auto]].
  assert (Hrewrite2 : (([p2 /t n] t1') arr ([p2 /t S n] t2')) =
                      [p2 /t n](t1' arr t2'));
    [simpl;
     rewrite raise_closed_le_exp
       with
         (n:=0);
     auto
    |rewrite Hrewrite2].
  apply H
    with
      (r0:=r)(tp:=tp);
    auto;
    try solve [inversion H5; auto];
    try solve [eapply closed_exp_app in H12;
               destruct H12;
               eauto];
    apply closed_typing_exp in t;
    auto;
    [rewrite Ha;
     simpl; auto
    |eapply closed_exp_app in H12;
     destruct H12;
     eauto].
  apply H0
    with
      (r0:=r)(tp:=tp);
    auto;
    try solve [inversion H5; auto];
    try solve [eapply closed_exp_app in H12;
               destruct H12;
               eauto];
    eapply closed_typing_exp; eauto;
      eapply closed_exp_app in H12;
      destruct H12;
      eauto.
  eapply subtyping_subst_type; eauto;
    try solve [inversion Hb; auto];
    try solve [eapply closed_ty_arr; eauto].

  assert (Hrewrite2 : t'0 [n maps_t S n][S n maps_t n] =
                      (t2' [S n maps_t n]));
    [rewrite H24; auto
    |rewrite rename_inverse_type in Hrewrite2;
     [|apply closed_subst_neq_type
         with
           (t:=([c_ r /t n] t'0))
           (p:=c_ r)(m:=n);
       auto;
       apply H13; crush]].
  
  apply closed_ty_arr in Hclosed_t1';
    destruct Hclosed_t1' as [He Hf].
  assert (Hg : closed_ty ([c_ r /t S n] t2') 0);
    [intros n' Hle;
     rewrite <- Hrewrite1;
     apply H13; auto
    |rewrite <- Hrewrite1 in Hg].
  apply closed_subst_switch_type
    with (p2:=p2)
    in Hg;
    auto.
  intros;
    apply Hg; crush.

  (*app path*)
  destruct e' as [|e' p'| | | | |];
    inversion H2;
    [subst e p
    |destruct v as [|x];
     [|destruct (n =? x)];
     inversion H22].

  
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros t'' Hle; eapply wf_closed_exp; eauto|].
  assert (Hclosed_arr : closed_ty (t1 arr t2) 0);
    [intros t'' Hle;
     apply closed_typing_exp in t;
     eauto;
     apply closed_exp_app in H11;
     crush|].
  
  destruct (typing_exists_subst_exp t)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e'0:=e')
    as [tarr Ha];
    auto;
    try solve [inversion H4; auto];
    try solve [eapply closed_exp_app in H11;
               destruct H11; auto];
    destruct Ha as [Ha Hb];
    destruct tarr as [| |t1' t2'| |];
    inversion Ha;
    subst t1 t2.
  assert (Hrewrite1 : (([c_ r /e n] p') cast ([c_ r /t n] t1')) =
                      ([c_ r /e n](p' cast t1')));
    [auto
    |rewrite Hrewrite1 in H3].

  rewrite rename_closed_subst_exp
    with
      (m:=S n)
      (e:=p' cast t1')
    in H3;
    auto;
    [
       |simpl;
        apply <- (closed_exp_cast 0);
        [|crush];
        split;
        [apply closed_exp_app in H11; crush
        |apply closed_ty_arr in Hclosed_arr; crush]].
  rewrite <- subst_distr_type in H3;
    [|crush|crush].
  assert (Hclosed_cast : closed_t n ([(p' cast t1') [n maps_e S n] /t 0] t2'));
    [destruct n as [|n'];
     apply closed_ty_arr in Hclosed_arr;
     destruct Hclosed_arr as [Hc Hd];
     [apply closed_remove_subst_hole_type in Hd;
      apply closed_subst_eq_type;
      apply rename_is_closed_exp; auto|]|].
  apply closed_n_subst_components_type;
    [apply closed_subst_neq_type
       with
         (t:=([c_ r /t S (S n')] t2'))
         (p:=c_ r)(m:=S (S n'));
     auto;
     apply Hd;
     crush
    |apply rename_is_closed_exp; auto].
  
  rewrite rename_closed_subst_type
    with
      (n:=S n)(m:=n)
    in H3;
    auto;
    [|apply closed_n_subst_components_type; auto].
  apply subst_equality_type in H3;
    auto;
    [|apply notin_rename_type;
      auto;
      apply unbound_var_notin_type;
      apply unbound_subst_components_type;
      [inversion Hb; subst; simpl in *;
       apply notin_var_unbound_type; auto
      |apply notin_var_unbound_exp;
       apply notin_rename_exp;
       auto];
      apply ni_cast;
      [inversion H4; auto
      |inversion Hb; simpl in *; auto
      |crush]].
  assert (Hrewrite2 : (([(p' cast t1') [n maps_e S n] /t 0] t2') [S n maps_t n])[n maps_t S n] =
                      (t'0[n maps_t S n]));
    [rewrite H3; auto|].
  rewrite rename_inverse_type in Hrewrite2; auto.
  rewrite rename_closed_subst_type
    with
      (m:=S n);
    [|apply closed_n_subst_components_type; auto;
      [rewrite <- H3;
       apply rename_is_closed_type;
       crush
      |apply Hclosed_p2; crush]].
  rewrite <- Hrewrite2.
  rewrite subst_distr_type; auto.
  rewrite <- rename_closed_subst_exp; auto;
    [|simpl; apply cl_cast;
      [apply closed_exp_app in H11;
       destruct H11 as [Hc Hd];
       apply closed_subst_switch_exp
         with
           (p2:=p2)
         in Hd;
       auto;
       apply Hd; crush
      |apply closed_ty_arr in Hclosed_arr;
       destruct Hclosed_arr as [Hc Hd];
       apply closed_subst_switch_type
         with
           (p2:=p2)
         in Hc;
       auto;
       apply Hc; crush]].
  destruct (typing_p_exists_subst t0)
    with
      (G1:=G1)(G2:=G2)
      (n0:=n)(p'0:=p')
      (p1:=c_ r)
    as [t'' Hc];
    auto;
    [inversion H4;
     auto
    |destruct Hc as [Hc Hd];
     subst t'].
  simpl;
    apply t_app_path
      with
        (t':=[p2 /t n] t'');
    auto.
  assert (Hrewrite3 : (([p2 /t n] t1') arr ([p2 /t S n] t2')) =
                      ([p2 /t n] (t1' arr t2')));
    [auto;
     simpl;
     rewrite raise_closed_le_exp with (n:=0); crush
    |rewrite Hrewrite3].
  apply H
    with
      (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |apply closed_exp_app in H11;
     destruct H11; auto].
  apply (typing_p_subst t0)
    with
      (p1:=c_ r)(tp:=tp);
    auto;
    inversion H4; auto.
  apply (subtyping_subst_type s)
    with
      (r0:=r)(tp1:=tp)(tp2:=tp);
    auto;
    [inversion Hb; auto
    |apply closed_typing_p
       with
         (Sig:=Sig)
         (G:=G)
         (p:=[v_ Var r /e n] p');
     auto;
     apply closed_exp_app in H11;
     destruct H11; auto
    |apply closed_ty_arr in Hclosed_arr;
     destruct Hclosed_arr;
     auto].

  (*new*)
  destruct e' as [ds'| | | | | |];
    inversion H2;
    [subst ds
    |destruct v as [|x];
     [|destruct (n =? x)];
     inversion H22].
  destruct t' as [ss'| | | |];
    inversion H3;
    subst ss.

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  assert (Hneqr : r <> length G);
    [apply Nat.lt_neq;
     rewrite H1, app_length;
     apply Nat.lt_lt_add_l;
     inversion H17;
     auto|].
  assert (HeqG : length (([p2 /env 0] G1) ++ G2) =
                 length G);
    [rewrite H1;
     repeat rewrite app_length, subst_length;
     auto
    |].
  simpl; apply t_new.
  assert (Hrewrite1 : (str ([p2 raise_e 0 /ss S n] ss') rts :: ([p2 /env 0] G1) ++ G2) =
                      (([p2 /env 0] (str ss' rts:: G1)) ++ G2));
    [simpl; rewrite subst_cons; subst; simpl; auto
    |rewrite Hrewrite1].
  rewrite raise_closed_le_exp
    with
      (n:=0);
    auto.
  rewrite closed_subst_distr_decls, closed_subst_distr_decl_tys; auto.
  apply H
    with
      (r0:=r)
      (tp:=tp);
    auto;
    try solve [rewrite subst_cons; simpl; subst; auto];
    try solve [rewrite HeqG;
               try (rewrite closed_subst_distr_decls);
               try (rewrite closed_subst_distr_decl_tys);
               auto];
    try solve [rewrite HeqG;
               apply unbound_var_notin_mutind, unbound_subst_components_mutind;
               inversion H4;
               inversion H5;
               simpl in *; auto];
    try solve [intros t' Hin;
               inversion Hin;
               [subst t'; auto
               |try (apply H6);
                try (apply H9);
                auto]];
    try solve [simpl; subst n; auto];
    try solve [eapply closed_subst_hole_mutind; auto;
               try eapply closed_exp_new;
               try eapply closed_ty_str;
               eauto];
    try solve [intros t' Hin;
               rewrite subst_cons in Hin;
               inversion Hin;
               [subst t' n; simpl
               |apply H14; auto];
               rewrite raise_closed_le_exp with (n:=0);
               [|auto|crush];
               apply -> closed_ty_str in H12;
               apply closed_subst_switch_decl_tys
                 with
                   (p2:=p2)
                 in H12;
               [eapply closed_ty_str; eauto
               |intros n'' Hle;
                apply Hclosed_p2;
                crush]].
  rewrite HeqG.
  apply unbound_subst_components_decl_tys;
    [eapply unbound_subst_decl_tys; eauto|].
  rewrite raise_closed_le_exp with (n:=0);
    [|auto|crush].
  eapply wf_unbound_exp; eauto;
    subst G;
    rewrite app_length;
    crush.
  
  (*acc path*)
  destruct e' as [| | |p' l'|v| |];
    inversion H1;
    [subst p l
    |destruct v as [|x];
     [|destruct (n =? x)];
     inversion H21].

  destruct (has_exists_subst h)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (p'0:=p')
    as [s' Ha];
    auto;
    [inversion H3; auto
    |eapply closed_exp_acc; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| | |l'' t''];
     inversion Ha;
     subst l'' t].
  apply subst_equality_type in H22;
    [subst t''
    |auto
    |inversion Hb; auto].
  apply has_subst
    with
      (G1:=G1)(G2:=G2)
      (r:=r)(n:=n)
      (p':=p')(s':=val l' oft t')
      (p2:=p2)(tp:=tp)
    in h;
    auto;
    [
       |inversion H3; auto
       |eapply closed_exp_acc; eauto].
  simpl; apply t_acc_path; auto.

  (*acc closed*)
  destruct e' as [| | |e'' l''| | |];
    inversion H2;
    [subst e l
    |destruct v as [|x];
     [|destruct (n =? x)];
     inversion H22].

  destruct (typing_exists_subst_exp t0)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e':=e'')
    as [t'' Ha];
    auto;
    [inversion H4; auto
    |eapply closed_exp_acc; eauto
    |destruct Ha as [Ha Hb];
     subst t'].

  destruct (contains_exists_subst c)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (t':=t'')
    as [s' Hc];
    auto;
    [eapply closed_typing_exp
       with
         (e:=[v_ Var r /e n] e'');
     eauto;
     eapply closed_exp_acc; eauto
    |destruct Hc as [Hc Hd];
     destruct s' as [| | |l' t'];
     inversion Hc;
     subst l'' t].

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  
  rewrite rename_closed_subst_type
    with
      (n:=n)
      (m:=S n)
      (t:=t'0)
    in H23, c;
    [
       |apply H12; crush
       |apply H12; crush].
  rewrite rename_closed_subst_type
    with
      (n:=n)
      (m:=S n);
    [
       |apply closed_subst_switch_type
          with
            (p2:=p2)
         in H12;
        auto;
        apply H12; crush].
  apply subst_equality_type in H23;
    [
       |apply notin_rename_type; auto
       |inversion Hd; auto].
  rewrite H23.
  rewrite H23 in c.

  simpl;
    apply t_acc_closed
      with
        (t':=[p2 /t n]t'').

  apply H
    with
      (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_exp_acc; eauto
    |eapply closed_typing_exp
       with (e:=[v_ Var r /e n] e'');
     eauto;
     eapply closed_exp_acc; eauto].

  assert (Hrewrite1 : (val l' oft ([p2 /t S n] t')) =
                      ([p2 /s S n](val l' oft t')));
    [auto
    |rewrite Hrewrite1].
  apply (contains_subst c)
    with
      (r0:=r)(tp:=tp);
    auto.
  
  eapply closed_typing_exp
    with (e:=[v_ Var r /e n] e'');
    eauto;
    eapply closed_exp_acc; eauto.

  intros.
  rewrite rename_closed_subst_type
    with
      (n:=n)
      (m:=S n)
      (t:=t'0), H23
    in H12;
    [
       |apply H12; crush].
  apply closed_subst_switch_type
    with
      (p2:=p2)
    in H12;
    auto.
  apply H12;
    crush.

  (*equal*)
  destruct d' as [l' t'|];
    inversion H1;
    subst L t.
  destruct s' as [| |l'' t''|];
    inversion H2;
    subst l''.

  apply subst_equality_type in H22;
    [subst t''; simpl; auto
    |inversion H3; auto
    |inversion H4; auto].

  (*value*)
  destruct d' as [|l1' e' t1'];
    inversion H2;
    subst e t l1'.
  destruct s' as [| | |l2' t2'];
    inversion H3;
    subst l2'.

  apply subst_equality_type in H23;
    auto;
    [subst t2'
    |inversion H4; auto
    |inversion H5; auto].
  
  destruct (typing_exists_subst_exp t0)
    with
      (r0:=r)(G1:=G1)
      (G2:=G2)(n0:=n)
      (e'0:=e')
    as
      [t Ha];
    auto;
    try solve [inversion H4; auto];
    try solve [eapply closed_decl_value; eauto];
    destruct Ha as [Ha Hb];
    subst t'.

  apply subtyping_subst_type
    with
      (G3:=G1)(G4:=G1)
      (G:=G2)
      (r:=r)(n:=n)
      (t1':=t)(t2':=t1')
      (tp1:=tp)(tp2:=tp)
      (p2:=p2)
    in s;
    auto;
    [
       |inversion H4; auto
       |eapply closed_typing_exp; eauto;
        eapply closed_decl_value; eauto
       |eapply closed_decl_ty_value; eauto].

  simpl; apply td_val with (t':=[p2 /t n]t); auto.
  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H4; auto
    |eapply closed_decl_value; eauto
    |eapply closed_typing_exp; eauto;
     eapply closed_decl_value; eauto].

  (*nil*)
  destruct ds';
    inversion H1.
  destruct ss';
    inversion H2.
  simpl; auto.

  (*cons*)
  destruct ds' as [|d' ds'];
    inversion H3;
    subst d ds.
  destruct ss' as [|s' ss'];
    inversion H4;
    subst s ss.

  simpl; apply td_con.

  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H5; auto
    |inversion H6; auto
    |eapply closed_decls_con;
     eauto
    |eapply closed_decl_tys_con;
     eauto].

  apply H0 with (r0:=r)(tp:=tp); auto;
    [inversion H5; auto
    |inversion H6; auto
    |eapply closed_decls_con;
     eauto
    |eapply closed_decl_tys_con;
     eauto].
Qed.

Lemma typing_subst_exp :
  (forall Sig G e t,
      Sig en G vdash e hasType t ->
      Sig wf_st ->
      forall r n G1 G2 e' t',
        G = ([c_ r /env 0] G1) ++ G2 ->
        e = ([c_ r /e n] e') ->
        t = ([c_ r /t n] t') ->
        (c_ r) notin_e e' ->
        (c_ r) notin_t t' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_exp e 0 ->
        closed_ty t 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /e n] e') hasType ([p2 /t n] t')).
Proof.
  destruct typing_subst_mutind; crush.
Qed.

Lemma membership_exists_subst :
  (forall Sig G e s, Sig en G vdash e mem s ->
              Sig wf_st ->
              forall r G1 G2 n e',
                G =([c_ r /env 0] G1) ++ G2 ->
                e = ([c_ r /e n] e') ->
                (c_ r) notin_e e' ->
                (c_ r) notin_env (G1 ++ G2) ->
                (c_ r) notin_env Sig ->
                n = length G1 ->
                closed_env G 0 ->
                closed_env Sig 0 ->
                closed_exp e 0 ->
                Sig en G2 vdash (c_ r) wf_e ->
                exists s', (s = [c_ r /s n] s') /\
                      (c_ r) notin_s s').
Proof.
  intros Sig G e s Hmem;
    induction Hmem;
    intros.

  (*path membership*)
  eapply has_exists_subst; eauto.

  (*non-path membership*)
  edestruct (typing_exists_subst_exp H)
    as [t' Ha];
    eauto;
    destruct Ha as [Ha Hb];
    subst t.
  assert (Hclosed_t' : closed_ty ([c_ r /t n] t') 0);
    [eapply closed_typing_exp; eauto|].
  edestruct (contains_exists_subst H0)
    as [s' Hc];
    eauto;
    destruct Hc as [Hc Hd];
    subst d.
  rewrite rename_closed_subst_decl_ty
    with
      (n:=S n)(m:=n);
    [|].

  exists (s' [S n maps_s n]); split; auto;
    apply notin_rename_decl_ty; auto.

  destruct n as [|n']; auto.
  apply closed_contains in H0;
    auto.
  apply H0;
    crush.
Qed.

Lemma membership_subst :
  (forall Sig G e s,
      Sig en G vdash e mem s ->
      Sig wf_st ->
      forall r n G1 G2 e' s',
        G = ([c_ r /env 0] G1) ++ G2 ->
        e = ([c_ r /e n] e') ->
        s = ([c_ r /s n] s') ->
        (c_ r) notin_e e' ->
        (c_ r) notin_s s' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_exp e 0 ->
        closed_decl_ty s 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /e n] e') mem ([p2 /s n] s')).
Proof.
  intros Sig G e s Hmem;
    induction Hmem;
    intros.

  (*path membership*)
  apply mem_path.
  eapply has_subst; eauto.

  (*closed membership*)
  edestruct (typing_exists_subst_exp H)
    as [t' Ha];
    eauto;
    destruct Ha as [Ha Hb];
    subst t e d.
  assert (Hclosed_t' : closed_ty ([v_ Var r /t n] t') 0);
    [eapply closed_typing_exp; eauto|].
  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  eapply typing_subst_exp
    with
      (p2:=p2)
    in H; eauto.
  edestruct (contains_exists_subst H0)
    as [s'' Hc];
    eauto;
    destruct Hc as [Hc Hd].
  assert (He := Hc);
    rewrite rename_closed_subst_decl_ty
      with
        (n:=n)(m:=S n)
    in He;
    [
       |apply closed_contains in H0;
        auto;
        apply H0;
        crush].
  apply subst_equality_mutind in He;
    [subst s''
    |apply notin_rename_decl_ty;
     auto
    |auto].
  eapply contains_subst
    with
      (s':=(s' [n maps_s S n]))
    in H0; eauto.
  apply mem_exp with (t:=([p2 /t n] t')); auto;
    [
       |apply closed_subst_switch_decl_ty
          with
            (p2:=p2)
         in H14;
        auto].
  rewrite rename_closed_subst_decl_ty
    with
      (m:=S n);
    [auto
    |apply closed_subst_switch_decl_ty
       with
         (p2:=p2)
      in H14;
     auto;
     apply H14;
     crush].
Qed.

Lemma wf_subst_mutind :
  (forall Sig G t,
      Sig en G vdash t wf_t ->
      Sig wf_st ->
      forall r n G1 G2 t',
        G = ([c_ r /env 0] G1) ++ G2 ->
        t = ([c_ r /t n] t') ->
        (c_ r) notin_t t' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_ty t 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /t n] t') wf_t) /\
  
  (forall Sig G s,
      Sig en G vdash s wf_s ->
      Sig wf_st ->
      forall r n G1 G2 s',
        G = ([c_ r /env 0] G1) ++ G2 ->
        s = ([c_ r /s n] s') ->
        (c_ r) notin_s s' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decl_ty s 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /s n] s') wf_s) /\
  
  (forall Sig G ss,
      Sig en G vdash ss wf_ss ->
      Sig wf_st ->
      forall r n G1 G2 ss',
        G = ([c_ r /env 0] G1) ++ G2 ->
        ss = ([c_ r /ss n] ss') ->
        (c_ r) notin_ss ss' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decl_tys ss 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /ss n] ss') wf_ss) /\
  
  (forall Sig G e,
      Sig en G vdash e wf_e ->
      Sig wf_st ->
      forall r n G1 G2 e',
        G = ([c_ r /env 0] G1) ++ G2 ->
        e = ([c_ r /e n] e') ->
        (c_ r) notin_e e' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_exp e 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /e n] e') wf_e) /\
  
  (forall Sig G d,
      Sig en G vdash d wf_d ->
      Sig wf_st ->
      forall r n G1 G2 d',
        G = ([c_ r /env 0] G1) ++ G2 ->
        d = ([c_ r /d n] d') ->
        (c_ r) notin_d d' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decl d 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /d n] d') wf_d) /\
  
  (forall Sig G ds,
      Sig en G vdash ds wf_ds ->
      Sig wf_st ->
      forall r n G1 G2 ds',
        G = ([c_ r /env 0] G1) ++ G2 ->
        ds = ([c_ r /ds n] ds') ->
        (c_ r) notin_ds ds' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decls ds 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /ds n] ds') wf_ds). 
Proof.
  apply wf_mutind; intros.

  (*top*)
  destruct t';
    inversion H1;
    simpl;
    auto.

  (*bot*)
  destruct t';
    inversion H1;
    simpl;
    auto.

  (*arr*)
  destruct t' as [| |t1' t2'| |];
    inversion H3;
    subst t1 t2.

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  assert (Hleng : length (([p2 /env 0] G1) ++ G2) =
                  length G);
    [rewrite app_length,
     subst_length,
     <- subst_length with (p:=c_ r)(n:=0),
                         <- app_length;
     subst G;
     auto
    |].
  
  simpl; apply wf_arr.
  
  eapply H
    with
      (p2:=p2);
    eauto;
    [inversion H4;
     auto
    |eapply closed_ty_arr; eauto].
  rewrite Hleng.
  apply unbound_subst_components_mutind;
    [eapply unbound_subst_type;
     eauto
    |rewrite raise_closed_le_exp with (n:=0);
     [eapply wf_unbound_exp;
      eauto;
      subst G;
      rewrite app_length;
      crush
     |auto
     |auto]].
  rewrite raise_closed_le_exp with (n:=0);
    [|auto|auto].
  rewrite closed_subst_distr_type;
    auto.
  assert (Hrewrite1 : (([p2 /t n] t1') :: ([p2 /env 0] G1) ++ G2) =
                      (([p2 /env 0] (t1'::G1)) ++ G2));
    [rewrite subst_cons; simpl; subst n; auto
    |rewrite Hrewrite1].
  apply H0 with (r0:=r)(tp:=tp);
    auto;
    try solve [try rewrite subst_cons;
               simpl;
               subst n G;
               auto];
    try solve [rewrite closed_subst_distr_type;
               auto;
               subst G;
               repeat rewrite app_length, subst_length;
               auto];
    try solve [apply unbound_var_notin_type, unbound_subst_components_type;
               auto;
               [inversion H4; auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H15; auto]];
    try solve [intros t Hin;
               inversion Hin;
               [subst t;
                inversion H4;
                try (eapply closed_ty_arr);
                eauto
               |try (apply H5);
                try (apply H8);
                auto]];
    try solve [apply closed_subst_hole_type;
               [eapply closed_ty_arr; eauto
               |auto]];
    try solve [rewrite subst_cons; simpl;
               intros t Hin;
               inversion Hin;
               [subst t;
                apply closed_subst_switch_type with (p1:=c_ r);
                auto;
                subst n;
                eapply closed_ty_arr in H10;
                destruct H10;
                eauto
               |apply H12;
                auto]].

  (*sel upper*)
  destruct t' as [|p' l'| | |];
    inversion H2;
    subst p L.
  
  destruct (has_exists_subst h)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (p'0:=p')
    as [s' Ha];
    auto;
    [inversion H3; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [l'' t'| | |];
     inversion Ha;
     subst l'' t].

  simpl;
    apply wf_sel_upper
      with (t:=[p2 /t n]t').

  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H3; auto
    |eapply closed_ty_sel;
     eauto].

  apply is_path_subst; auto.
  apply subst_is_path
    with (p':=c_ r)(n:=n);
    auto.

  assert (Hrewrite : (type l' ext ([p2 /t n] t')) =
                     ([p2 /s n] (type l' ext t')));
    [auto
    |rewrite Hrewrite].
  apply (has_subst h)
    with
      (r0:=r)(tp:=tp);
    auto.
  
  inversion H3; auto.
  eapply closed_ty_sel; eauto.

  (*sel lower*)
  destruct t' as [|p' l'| | |];
    inversion H2;
    subst p L.
  
  destruct (has_exists_subst h)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (p'0:=p')
    as [s' Ha];
    auto;
    [inversion H3; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [|l'' t'| |];
     inversion Ha;
     subst l'' t].

  simpl;
    apply wf_sel_lower
      with (t:=[p2 /t n]t').

  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H3; auto
    |eapply closed_ty_sel;
     eauto].

  apply is_path_subst; auto.
  apply subst_is_path
    with (p':=c_ r)(n:=n);
    auto.

  assert (Hrewrite : (type l' sup ([p2 /t n] t')) =
                     ([p2 /s n] (type l' sup t')));
    [auto
    |rewrite Hrewrite].
  apply (has_subst h)
    with
      (r0:=r)(tp:=tp);
    auto.
  
  inversion H3; auto.
  eapply closed_ty_sel; eauto.

  (*sel equal*)
  destruct t' as [|p' l'| | |];
    inversion H2;
    subst p L.
  
  destruct (has_exists_subst h)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (p'0:=p')
    as [s' Ha];
    auto;
    [inversion H3; auto
    |eapply closed_ty_sel; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| |l'' t'|];
     inversion Ha;
     subst l'' t].

  simpl;
    apply wf_sel_equal
      with (t:=[p2 /t n]t').

  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H3; auto
    |eapply closed_ty_sel;
     eauto].

  apply is_path_subst; auto.
  apply subst_is_path
    with (p':=c_ r)(n:=n);
    auto.

  assert (Hrewrite : (type l' eqt ([p2 /t n] t')) =
                     ([p2 /s n] (type l' eqt t')));
    [auto
    |rewrite Hrewrite].
  apply (has_subst h)
    with
      (r0:=r)(tp:=tp);
    auto.
  
  inversion H3; auto.
  eapply closed_ty_sel; eauto.

  (*str*)
  destruct t' as [ss'| | | |];
    inversion H2;
    subst ss.

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  assert (Hleng : length (([p2 /env 0] G1) ++ G2) =
                  length G);
    [subst G;
     repeat rewrite app_length, subst_length;
     auto|].
  
  simpl;
    apply wf_str.

  apply unbound_subst_components_decl_tys;
    [rewrite Hleng;
     apply unbound_subst_decl_tys with (p:=c_ r)(n:=S n);
     auto                                           
    |rewrite raise_closed_le_exp with (n:=0);
     auto;
     apply wf_unbound_exp with (Sig:=Sig)(G:=G2);
     auto;
     rewrite app_length;
     crush].

  assert (Hrewrite : (str ([p2 raise_e 0 /ss S n] ss') rts:: ([p2 /env 0] G1) ++ G2) =
                     (([p2 /env 0] (str ss' rts::G1)) ++ G2));
    [rewrite subst_cons; subst n; simpl; auto
    |rewrite Hrewrite].
  
  rewrite raise_closed_le_exp with (n:=0);
    auto.
  rewrite closed_subst_distr_decl_tys;
    auto.
  apply H with (r0:=r)(tp:=tp);
    auto;
    try solve [subst n G;
               try rewrite subst_cons;
               simpl; auto];
    try solve [rewrite closed_subst_distr_decl_tys;
               auto;
               rewrite Hleng; auto];
    try solve [apply unbound_var_notin_decl_tys, unbound_subst_components_decl_tys;
               [apply notin_var_unbound_decl_tys;
                inversion H3; auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H14; auto]];
    try solve [intros t Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|Hin];
               [inversion Hin;
                [subst t; auto
                |apply H4; apply in_or_app; auto]
               |apply H4; apply in_or_app; auto]];
    try solve [intros t Hin;
               inversion Hin;
               [subst t; auto
               |apply H7; auto]];
    try solve [apply closed_subst_hole_decl_tys;
               auto;
               eapply closed_ty_str; eauto].
  intros t Hin;
    apply in_app_or in Hin;
    destruct Hin as [Hin|Hin];
    [rewrite subst_cons in Hin;
     inversion Hin;
     [subst t; simpl;
      apply closed_ty_str;
      rewrite raise_closed_le_exp with (n:=0);
      auto;
      apply closed_subst_switch_decl_tys with (p1:=c_ r);
      [eapply closed_ty_str;
       subst n;
       eauto
      |intros n' Hle; apply Hclosed_p2; crush]
        
     |apply H11, in_or_app; auto]
       
    |apply H11, in_or_app; auto].

  (*upper*)
  destruct s' as [l' t'| | |];
    inversion H2;
    subst L t.
  
  simpl; apply wft_upper.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H3;
     auto
    |eapply closed_decl_ty_upper; eauto].

  (*lower*)
  destruct s' as [|l' t'| |];
    inversion H2;
    subst L t.
  
  simpl; apply wft_lower.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H3;
     auto
    |eapply closed_decl_ty_lower; eauto].

  (*equal*)
  destruct s' as [| |l' t'|];
    inversion H2;
    subst L t.
  
  simpl; apply wft_equal.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H3;
     auto
    |eapply closed_decl_ty_equal; eauto].

  (*value*)
  destruct s' as [| | |l' t'];
    inversion H2;
    subst l t.
  
  simpl; apply wft_value.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H3;
     auto
    |eapply closed_decl_ty_value; eauto].

  (*nil type*)
  destruct ss';
    inversion H1;
    auto.

  (*cons type*)
  destruct ss' as [|s' ss'];
    inversion H3;
    subst s ss.

  simpl; apply wft_con.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decl_tys_con; eauto].

  apply H0 with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decl_tys_con; eauto].

  intros.
  destruct in_dty_idt_subst_switch
    with
      (ss:=ss')(s:=s'0)
      (p:=p2)(n:=n0)(p':=c_ r)
    as [s'' Ha];
    auto;
    destruct Ha as [Ha Hb];
    rewrite Ha.
  destruct in_dty_subst
    with
      (ss:=ss')(s:=s'')
      (p:=c_ r)(n:=n0)
    as [s0 Hc];
    auto.
  rewrite idt_subst;
    rewrite idt_subst in n.
  apply n; auto.

  (*var*)
  destruct e' as [| | | |v| |];
    inversion H1.
  destruct v as [x|x];
    [inversion H18;
     subst n;
     simpl;
     apply wf_var;
     rewrite app_length, subst_length;
     subst G;
     rewrite app_length in l;
     rewrite subst_length in l;
     auto
    |simpl;
     destruct (n0 =? x);
     inversion H18;
     subst n].
  apply wf_weakening_actual_exp; auto.

  (*loc*)
  destruct e' as [| | | |v|i'|];
    inversion H1;
    [destruct v as [x|x];
     [inversion H18
     |destruct (n =? x);
      inversion H18]
    |subst i; simpl; auto].

  (*fn*)
  destruct e' as [| |t1' e' t2'| |v| |];
    inversion H4;
    [subst t1 e t2
    |destruct v as [x|x];
     [inversion H21
     |destruct (n =? x);
      inversion H21]].

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  assert (Hleng : length (([p2 /env 0] G1) ++ G2) =
                  length G);
    [subst G;
     repeat rewrite app_length, subst_length;
     auto|].
  assert (HrewriteEnv : (([p2 /t n] t1') :: ([p2 /env 0] G1) ++ G2) =
                        (([p2 /env 0] (t1' :: G1)) ++ G2));
    [rewrite subst_cons;
     simpl;
     subst n;
     auto|].
  
  simpl;
    apply wf_fn.
  
  apply H with (r0:=r)(tp:=tp); auto;
    [inversion H5; auto
    |eapply closed_exp_fn; eauto].

  erewrite raise_closed_le_exp; eauto;
    rewrite Hleng;
    apply unbound_subst_components_exp;
    [eapply unbound_subst_exp; eauto
    |apply wf_unbound_exp with (Sig:=Sig)(G:=G2);
     auto;
     subst G;
     rewrite app_length;
     crush].

  rewrite HrewriteEnv.
  erewrite raise_closed_le_exp; eauto.
  rewrite closed_subst_distr_exp; auto.
  apply H0 with (r0:=r)(tp:=tp);
    auto;
    try solve [try rewrite subst_cons;
               subst n G;
               simpl;
               auto];
    try solve [rewrite closed_subst_distr_exp, Hleng;
               auto];
    try solve [apply unbound_var_notin_exp, unbound_subst_components_exp;
               [apply notin_var_unbound_exp;
                inversion H5; 
                auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H16;
                auto]];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|];
               [inversion Hin;
                [subst t';
                 inversion H5;
                 auto
                |apply H6, in_or_app;
                 auto]
               |apply H6, in_or_app;
                auto]];
    try solve [intros t' Hin;
               inversion Hin;
               [subst t';
                eapply closed_exp_fn; eauto
               |apply H9; auto]];
    try solve [apply closed_subst_hole_exp;
               auto;
               inversion H4;
               eapply closed_exp_fn;
               eauto];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|Hin];
               [rewrite subst_cons in Hin;
                inversion Hin;
                [subst t';
                 simpl;
                 subst n;
                 apply closed_subst_switch_type with (p1:=c_ r);
                 eapply closed_exp_fn in H11;
                 destruct H11;
                 eauto
                |subst G;
                 apply H13, in_or_app;
                 auto]
               |subst G;
                apply H13, in_or_app;
                auto]].
  
  rewrite Hleng, raise_closed_le_exp with (n:=0);
    auto;
    apply unbound_subst_components_type;
    [eapply unbound_subst_type;
     eauto
    |eapply wf_unbound_exp with (G:=G2);
     eauto;
     subst G;
     rewrite app_length;
     crush].

  rewrite Hleng, HrewriteEnv, raise_closed_le_exp with (n:=0);
    auto.
  rewrite closed_subst_distr_type;
    auto.
  apply H1 with (r0:=r)(tp:=tp);
    auto;
    try solve [try rewrite subst_cons;
               subst n G;
               simpl;
               auto];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|];
               [inversion Hin;
                [subst t';
                 inversion H5;
                 auto
                |apply H6, in_or_app;
                 auto]
               |apply H6, in_or_app;
                auto]];
    try solve [intros t' Hin;
               inversion Hin;
               [subst t';
                eapply closed_exp_fn; eauto
               |apply H9; auto]];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|Hin];
               [rewrite subst_cons in Hin;
                inversion Hin;
                [subst t';
                 simpl;
                 subst n;
                 apply closed_subst_switch_type with (p1:=c_ r);
                 eapply closed_exp_fn in H11;
                 destruct H11;
                 eauto
                |subst G;
                 apply H13, in_or_app;
                 auto]
               |subst G;
                apply H13, in_or_app;
                auto]];      
    try solve [rewrite closed_subst_distr_type;
               auto];      
    try solve [apply unbound_var_notin_type, unbound_subst_components_type;
               [apply notin_var_unbound_type;
                inversion H5; 
                auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite <- Hleng;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H16;
                auto]];        
    try solve [apply closed_subst_hole_type;
               auto;
               inversion H4;
               eapply closed_exp_fn;
               eauto].

  rewrite Hleng, HrewriteEnv, raise_closed_le_exp with (n:=0);
    auto.
  rewrite closed_subst_distr_type, closed_subst_distr_exp;
    auto.
  apply typing_subst_exp
    with
      (r:=r)(tp:=tp)
      (G:=([c_ r /t length G1] t1')::G)
      (e:=[c_ (length G) /e 0] ([c_ r /e S n] e'))
      (t:=([c_ (length G) /t 0] ([c_ r /t S n] t2')));
    auto;
    try solve [rewrite closed_subst_distr_exp;
               auto];
    try solve [rewrite closed_subst_distr_type;
               auto];
    try solve [try rewrite subst_cons;
               subst n G;
               simpl;
               auto];      
    try solve [apply unbound_var_notin_type, unbound_subst_components_type;
               [apply notin_var_unbound_type;
                inversion H5; 
                auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite <- Hleng;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H16;
                auto]];      
    try solve [apply unbound_var_notin_exp, unbound_subst_components_exp;
               [apply notin_var_unbound_exp;
                inversion H5; 
                auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite <- Hleng;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H16;
                auto]];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|];
               [inversion Hin;
                [subst t';
                 inversion H5;
                 auto
                |apply H6, in_or_app;
                 auto]
               |apply H6, in_or_app;
                auto]];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|Hin];
               [rewrite subst_cons in Hin;
                inversion Hin;
                [subst t';
                 simpl;
                 subst n;
                 apply closed_subst_switch_type with (p1:=c_ r);
                 eapply closed_exp_fn in H11;
                 destruct H11;
                 eauto
                |subst G;
                 apply H13, in_or_app;
                 auto]
               |subst G;
                apply H13, in_or_app;
                auto]];
    try solve [intros t' Hin;
               inversion Hin;
               [subst t';
                eapply closed_exp_fn;
                subst n;
                eauto
               |apply H9; auto]];        
    try solve [try apply closed_subst_hole_type;
               try apply closed_subst_hole_exp;
               auto;
               inversion H4;
               eapply closed_exp_fn;
               eauto].

  (*app*)
  destruct e'0 as [|e1' e2'| | | | |];
    inversion H3;
    [subst e e'
    |destruct v as [x|x];
     [inversion H20
     |destruct (n =? x);
      inversion H20]].

  destruct (typing_exists_subst_exp t)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e':=e1')
    as [t' Ha];
    auto;
    [inversion H4; auto
    |eapply closed_exp_app in H10;
     destruct H10;
     eauto
    |destruct Ha as [Ha Hb];
     destruct t' as [| |t1' t2'| |];
     inversion Ha;
     subst t1 t2].

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hin; eapply wf_closed_exp;
     eauto
    |].
  
  simpl;
    apply wf_app
      with
        (t1:=[p2 /t n]t1')
        (t2:=[p2 /t S n]t2').

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H4;
     auto
    |apply closed_exp_app in H10;
     destruct H10;
     auto].

  apply H0 with (r0:=r)(tp:=tp);
    auto;
    [inversion H4;
     auto
    |eapply closed_exp_app; eauto].

  assert (Hrewrite1 : (([p2 /t n] t1') arr ([p2 /t S n] t2')) =
                      ([p2 /t n] (t1' arr t2')));
    [simpl;
     rewrite raise_closed_le_exp with (n:=0);
     auto
    |rewrite Hrewrite1].
  
  apply (typing_subst_exp t) with (r0:=r)(tp:=tp);
    auto;
    [inversion H4;
     auto
    |apply closed_exp_app in H10;
     destruct H10;
     auto
    |eapply (closed_typing_exp t);
     eauto;
     apply closed_exp_app in H10;
     destruct H10;
     auto].

  apply (typing_subst_exp t0) with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |inversion Hb; auto
    |eapply closed_exp_app; eauto
    |eapply closed_typing_exp;
     eauto;
     eapply closed_exp_app; eauto].

  (*acc*)
  destruct e' as [| | |e' l'| | |];
    inversion H2;
    [subst e l
    |destruct v as [x|x];
     [inversion H19
     |destruct (n =? x);
      inversion H19]].

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hin; eapply wf_closed_exp;
     eauto
    |].

  destruct (membership_exists_subst m)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e'0:=e')
    as [s' Ha];
    auto;
    [inversion H3;
     auto
    |eapply closed_exp_acc; eauto
    |destruct Ha as [Ha Hb];
     destruct s' as [| | |l t];
     inversion Ha;
     subst l' t'].

  simpl; apply wf_acc with (t':=[p2 /t n]t).

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H3;
     auto
    |eapply closed_exp_acc; eauto].

  assert (Hrewrite : (val l oft [p2 /t n] t) =
                     ([p2 /s n](val l oft t)));
    [auto
    |rewrite Hrewrite].
  eapply (membership_subst m);
    eauto;
    [inversion H3; auto
    |eapply closed_exp_acc; eauto
    |eapply closed_membership;
     eauto;
     eapply closed_exp_acc;
     eauto].

  (*cast*)
  destruct e' as [| | | | | |ec tc];
    inversion H3;
    [destruct v as [x|x];
     [inversion H20
     |destruct (n =? x);
      inversion H20]
    |subst e t].

  destruct (typing_exists_subst_exp t0)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e':=ec)
    as [t Ha];
    auto;
    [inversion H4; auto
    |eapply closed_exp_cast; eauto
    |destruct Ha as [Ha Hb];
     subst t'].

  simpl; apply wf_cast
           with (t':=[p2 /t n]t).

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H4;
     auto
    |eapply closed_exp_cast;
     eauto].

  apply H0 with (r0:=r)(tp:=tp);
    auto;
    [inversion H4;
     auto
    |eapply closed_exp_cast;
     eauto].

  apply (typing_subst_exp t0) with (r0:=r)(tp:=tp);
    auto;
    [inversion H4;
     auto
    |eapply closed_exp_cast;
     eauto
    |eapply closed_typing_exp;
     eauto;
     eapply closed_exp_cast;
     eauto].

  apply (subtyping_subst_type s)
    with
      (r0:=r)(tp1:=tp)(tp2:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_typing_exp;
     eauto;
     eapply closed_exp_cast;
     eauto
    |eapply closed_exp_cast;
     eauto].

  (*new*)
  destruct e' as [ds'| | | | | |];
    inversion H2;
    [subst ds
    |destruct v as [x|x];
     [inversion H19
     |destruct (n =? x);
      inversion H19]].

  destruct (typing_exists_subst_exp t)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e':=new ds')
    as [t' Ha];
    auto;
    destruct Ha as [Ha Hb];
    destruct t' as [ss'| | | |];
    inversion Ha;
    subst ss.

  assert (Hclosed_p2 : closed_exp p2 0);
    [intros n' Hle; eapply wf_closed_exp; eauto|].
  
  assert (Hrewrite1 : (str ([p2 /ss S n] ss') rts) =
                      (([p2 /t n]str ss' rts)));
    [simpl;
     rewrite raise_closed_le_exp with (n:=0);
     auto
    |].
  assert (Hrewrite2 : (new ([p2 raise_e 0 /ds S n] ds')) =
                      (([p2 /e n]new ds')));
    [auto
    |].

  simpl; apply wf_new with (ss:=[p2 /ss S n]ss');
    auto.

  rewrite Hrewrite1, Hrewrite2.
  apply (typing_subst_exp t)
    with
      (r0:=r)(tp:=tp);
    auto;
    eapply closed_typing_exp; eauto.
  
  apply unbound_subst_components_decls;
    [rewrite app_length, subst_length;
     subst G;
     rewrite app_length, subst_length in u;
     eapply unbound_subst_decls; eauto
    |erewrite raise_closed_le_exp; eauto;
     eapply wf_unbound_exp;
     eauto;
     rewrite app_length;
     crush].

  rewrite Hrewrite1.
  assert (Hrewrite3 : (([p2 /t n] str ss' rts) :: ([p2 /env 0] G1) ++ G2) =
                      (([p2 /env 0] (str ss' rts:: G1)) ++ G2));
    [rewrite subst_cons; subst n; simpl; auto
    |rewrite Hrewrite3].
  assert (Hleng : (length (([p2 /env 0] G1) ++ G2)) =
                  (length G));
    [subst G;
     repeat rewrite app_length, subst_length;
     auto
    |].
  erewrite raise_closed_le_exp; eauto.
  rewrite closed_subst_distr_decls; auto.
  rewrite Hleng.
  apply H with (r0:=r)(tp:=tp);
    auto;
    try solve [try rewrite subst_cons;
               subst n G;
               simpl;
               auto];
    try solve [rewrite closed_subst_distr_decls;
               auto];      
    try solve [apply unbound_var_notin_decls, unbound_subst_components_decls;
               [apply notin_var_unbound_decls;
                inversion H3; 
                auto
               |apply ub_var, ub_con, Nat.lt_neq;
                rewrite <- Hleng;
                rewrite app_length;
                apply Nat.lt_lt_add_l;
                inversion H14;
                auto]];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|];
               [inversion Hin;
                [subst t';
                 inversion H3;
                 auto
                |apply H4, in_or_app;
                 auto]
               |apply H4, in_or_app;
                auto]];
    try solve [intros t' Hin;
               inversion Hin;
               [subst t';
                eapply closed_typing_exp; eauto
               |apply H7; auto]];        
    try solve [apply closed_subst_hole_decls;
               auto;
               inversion H2;
               eapply closed_exp_new;
               eauto];
    try solve [intros t' Hin;
               apply in_app_or in Hin;
               destruct Hin as [Hin|Hin];
               [rewrite subst_cons in Hin;
                inversion Hin;
                [subst t';
                 simpl;
                 subst n;
                 assert (Htmp : (str ([p2 raise_e 0 /ss S (length G1)] ss') rts) =
                                ([p2 /t length G1](str ss' rts)));
                 [auto|rewrite Htmp];
                 apply closed_subst_switch_type with (p1:=c_ r); auto;
                 eapply closed_typing_exp; eauto
                |subst G;
                 apply H11, in_or_app;
                 auto]
               |subst G;
                apply H11, in_or_app;
                auto]].

  (*decl equal*)
  destruct d' as [l' t'|];
    inversion H2;
    subst L t.

  simpl; apply wfe_equal.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H3; auto
    |eapply closed_decl_equal; eauto].

  (*decl value*)
  destruct d' as [|l' e' t''];
    inversion H3;
    subst l e t.

  destruct (typing_exists_subst_exp t0)
    with
      (G1:=G1)(G2:=G2)
      (r0:=r)(n0:=n)
      (e'0:=e')
    as [t''' Ha];
    auto;
    [inversion H4; auto
    |eapply closed_decl_value; eauto
    |destruct Ha as [Ha Hb];
     subst t'].

  rename t''' into t'.
  simpl; apply wfe_value with (t':=[p2 /t n] t').

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decl_value; eauto].

  apply H0 with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decl_value; eauto].

  apply (typing_subst_exp t0) with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decl_value; eauto
    |eapply closed_typing_exp;
     eauto;
     eapply closed_decl_value;
     eauto].

  apply (subtyping_subst_type s)
    with
      (r0:=r)(tp1:=tp)(tp2:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_typing_exp;
     eauto;
     eapply closed_decl_value;
     eauto
    |eapply closed_decl_value;
     eauto].

  (*decls nil*)
  destruct ds';
    inversion H1;
    auto.

  (*decls con*)
  destruct ds' as [|d' ds'];
    inversion H3;
    subst d ds.
  
  simpl; apply wfe_con.

  apply H with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decls_con;
     eauto].

  apply H0 with (r0:=r)(tp:=tp);
    auto;
    [inversion H4; auto
    |eapply closed_decls_con;
     eauto].

  intros.
  destruct ind_idd_subst_switch
    with
      (ds:=ds')(d:=d'0)
      (p:=p2)(n:=n0)(p':=c_ r)
    as [d'' Ha];
    auto;
    destruct Ha as [Ha Hb];
    rewrite Ha.
  destruct in_d_subst
    with
      (ds:=ds')(d:=d'')
      (p:=c_ r)(n:=n0)
    as [d0 Hc];
    auto.
  rewrite idd_subst;
    rewrite idd_subst in n.
  apply n; auto.
Qed.

Lemma wf_subst_type :
  (forall Sig G t,
      Sig en G vdash t wf_t ->
      Sig wf_st ->
      forall r n G1 G2 t',
        G = ([c_ r /env 0] G1) ++ G2 ->
        t = ([c_ r /t n] t') ->
        (c_ r) notin_t t' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_ty t 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /t n] t') wf_t).
Proof.
  destruct wf_subst_mutind; crush.
Qed.

Lemma wf_subst_decl_ty :
  (forall Sig G s,
      Sig en G vdash s wf_s ->
      Sig wf_st ->
      forall r n G1 G2 s',
        G = ([c_ r /env 0] G1) ++ G2 ->
        s = ([c_ r /s n] s') ->
        (c_ r) notin_s s' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decl_ty s 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /s n] s') wf_s).
Proof.
  destruct wf_subst_mutind; crush.
Qed.

Lemma wf_subst_decl_tys :
  (forall Sig G ss,
      Sig en G vdash ss wf_ss ->
      Sig wf_st ->
      forall r n G1 G2 ss',
        G = ([c_ r /env 0] G1) ++ G2 ->
        ss = ([c_ r /ss n] ss') ->
        (c_ r) notin_ss ss' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decl_tys ss 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /ss n] ss') wf_ss).
Proof.
  destruct wf_subst_mutind; crush.
Qed.

Lemma wf_subst_exp :
  (forall Sig G e,
      Sig en G vdash e wf_e ->
      Sig wf_st ->
      forall r n G1 G2 e',
        G = ([c_ r /env 0] G1) ++ G2 ->
        e = ([c_ r /e n] e') ->
        (c_ r) notin_e e' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_exp e 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /e n] e') wf_e).
Proof.
  destruct wf_subst_mutind; crush.
Qed.

Lemma wf_subst_decl :    
  (forall Sig G d,
      Sig en G vdash d wf_d ->
      Sig wf_st ->
      forall r n G1 G2 d',
        G = ([c_ r /env 0] G1) ++ G2 ->
        d = ([c_ r /d n] d') ->
        (c_ r) notin_d d' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decl d 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /d n] d') wf_d).
Proof.
  destruct wf_subst_mutind; crush.
Qed.

Lemma wf_subst_decls :
  (forall Sig G ds,
      Sig en G vdash ds wf_ds ->
      Sig wf_st ->
      forall r n G1 G2 ds',
        G = ([c_ r /env 0] G1) ++ G2 ->
        ds = ([c_ r /ds n] ds') ->
        (c_ r) notin_ds ds' ->
        (c_ r) notin_env (G1 ++ G2) ->
        (c_ r) notin_env Sig ->
        n = length G1 ->
        closed_env G 0 ->
        closed_env Sig 0 ->
        closed_decls ds 0 ->
        Sig evdash G2 wf_env ->
        forall p2 tp,
          closed_env (([p2 /env 0] G1) ++ G2) 0 ->
          Sig en G2 vdash (c_ r) pathType tp ->
          Sig en G2 vdash p2 pathType tp ->
          Sig en G2 vdash (c_ r) wf_e ->
          Sig en G2 vdash p2 wf_e ->
          Sig en G2 vdash tp wf_t ->
          is_path p2 ->
          Sig en (([p2 /env 0] G1) ++ G2) vdash ([p2 /ds n] ds') wf_ds).
Proof.
  destruct wf_subst_mutind; crush.
Qed.

Lemma wf_subst_type_actual :
  forall Sig G t' t, Sig en t'::G vdash ([c_ length G /t 0]t) wf_t ->
              Sig wf_st ->
              Sig evdash t'::G wf_env ->
              length G unbound_t t ->
              forall p, Sig en G vdash p wf_e ->
                   Sig en G vdash p pathType t' ->
                   Sig en G vdash ([p /t 0]t) wf_t.
Proof.
  intros.

  assert (Hunbound_t' : (length G) unbound_t t');
    [inversion H1;
     subst;
     eapply wf_unbound_type;
     eauto|].
  assert (Hunbound_p : (length G) unbound_e p);
    [eapply wf_unbound_exp;
     eauto|].

  apply wf_subst_type
    with
      (G2:=t'::G)
      (t:=[c_ (length G) /t 0] t)
      (r:=length G)(n:=0)
      (G1:=nil)
      (tp:=t')
      (t':=t)(p2:=p)
    in H;
    simpl;
    auto;
    try solve [eapply wf_closed_env;
               eauto].

  simpl in H;
    apply wf_strengthening_type_actual with (t':=t')(i:=length G);
    auto;
    [inversion H1;
     auto
    |inversion H1;
     eapply wf_notin_env;
     eauto].

  intros t'' Hin;
    inversion Hin;
    subst;
    auto.
  inversion H1;
    subst.
  apply wf_notin_env with (r:=length G) in H10;
    auto.

  apply wf_notin_store_type;
    auto.

  apply wf_closed_store_type;
    auto.

  intros t'' Hin; eapply wf_closed_type;
    eauto.

  apply pt_var;
    unfold mapping;
    simpl;
    rewrite get_app_r;
    rewrite rev_length;
    auto;
    rewrite Nat.sub_diag;
    auto.
  
  apply typing_p_weakening_actual with (G':=t'::nil) in H4;
    auto;
    try solve [inversion H1; auto].

  apply wf_weakening_actual_exp with (G':=t'::nil) in H3;
    auto;
    try solve [inversion H1; auto].

  inversion H1;
    subst.
  apply wf_weakening_actual_type with (G':=t'::nil) in H8;
    auto.

  inversion H4; auto.
Qed.

Lemma wf_subst_decl_ty_actual :
  forall Sig G t s, Sig en t::G vdash ([c_ length G /s 0]s) wf_s ->
              Sig wf_st ->
              Sig evdash t::G wf_env ->
              length G unbound_s s ->
              forall p, Sig en G vdash p wf_e ->
                   Sig en G vdash p pathType t ->
                   Sig en G vdash ([p /s 0]s) wf_s.
Proof.
  intros.

  assert (Hunbound_t : (length G) unbound_t t);
    [inversion H1;
     subst;
     eapply wf_unbound_type;
     eauto|].
  assert (Hunbound_p : (length G) unbound_e p);
    [eapply wf_unbound_exp;
     eauto|].

  apply wf_subst_decl_ty
    with
      (G2:=t::G)
      (s:=[c_ (length G) /s 0] s)
      (r:=length G)(n:=0)
      (G1:=nil)
      (tp:=t)
      (s':=s)(p2:=p)
    in H;
    simpl;
    auto;
    try solve [eapply wf_closed_env;
               eauto].

  simpl in H;
    apply wf_strengthening_decl_ty_actual with (t:=t)(i:=length G);
    auto;
    [inversion H1;
     auto
    |inversion H1;
     eapply wf_notin_env;
     eauto].

  intros t'' Hin;
    inversion Hin;
    subst;
    auto.
  inversion H1;
    subst.
  apply wf_notin_env with (r:=length G) in H10;
    auto.

  apply wf_notin_store_type;
    auto.

  apply wf_closed_store_type;
    auto.

  intros t'' Hin; eapply wf_closed_decl_ty;
    eauto.

  apply pt_var;
    unfold mapping;
    simpl;
    rewrite get_app_r;
    rewrite rev_length;
    auto;
    rewrite Nat.sub_diag;
    auto.
  
  apply typing_p_weakening_actual with (G':=t::nil) in H4;
    auto;
    try solve [inversion H1; auto].

  apply wf_weakening_actual_exp with (G':=t::nil) in H3;
    auto;
    try solve [inversion H1; auto].

  inversion H1;
    subst.
  apply wf_weakening_actual_type with (G':=t::nil) in H8;
    auto.

  inversion H4; auto.
Qed.

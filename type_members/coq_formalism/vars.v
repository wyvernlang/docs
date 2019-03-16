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



Lemma has_contains_wf_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash p wf_e ->
              Sig en G vdash s wf_s) /\
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash t wf_t ->
              forall p, Sig en G vdash p pathType t ->
                   Sig en G vdash s wf_s).
Proof.
  apply has_contains_mutind;
    intros; auto.

  (*has*)
  
Qed.


Reserved Notation "Sig 'en' G 'vdash' p 'ni_w' s" (at level 80).
Reserved Notation "s 'cont_w' t" (at level 80).


Inductive struct_contains : ty -> decl_ty -> Prop :=
| cont_wf : forall ss s, in_dty s ss ->
                    s cont_w (str ss rts)
where "s 'cont_w' t" := (struct_contains t s).


Inductive alt_has : env -> env -> exp -> decl_ty -> Prop :=
| h_struct : forall Sig G p ss s, Sig en G vdash p pathType (str ss rts) ->
                           s cont_w (str ss rts) ->
                           Sig en G vdash p ni_w ([p /s 0] s)
| h_upper : forall Sig G p p' l' t s, Sig en G vdash p pathType (sel p' l') ->
                               Sig en G vdash p' ni_w (type l' ext t) ->
                               Sig en G vdash p ni_w s ->
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
      (Sig:=Sig)(G:=str ss rts::G)
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
  apply struct_contains_wf with (t:=str ss rts);
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

Lemma has_wf :
  forall Sig G p s, Sig en G vdash p ni s ->
             Sig wf_st ->
             Sig evdash G wf_env ->
             Sig en G vdash p wf_e ->
             Sig en G vdash s wf_s.
Proof.
  intros.

  apply alt_has_wf with (p:=p);
    auto.
  apply has_implies_alt;
    auto.
  intros n Hle;
    eapply wf_closed_exp;
    eauto.
  eapply wf_closed_env;
    eauto.
  apply wf_closed_store_type;
    auto.
Qed.



Lemma member_wf :
  forall Sig G e s, Sig en G vdash e mem s ->
             Sig wf_st ->
             Sig evdash G wf_env ->
             Sig en G vdash e wf_e ->
             Sig en G vdash s wf_s.
Proof.
  intros Sig G e s Hmem;
    induction Hmem;
    intros.

  eapply has_wf;
    eauto.

  eapply closed_contains_wf;
    eauto.
  eapply typing_wf_exp;
    eauto.

  intros n Hle;
    destruct n as [|n'];
    auto.
  apply closed_contains in H0;
    auto.
  apply H0;
    crush.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  eapply closed_typing_exp;
    eauto.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  intros n'' Hle';
    eapply wf_closed_exp;
    eauto.
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
  eapply h_upper;
    eauto.
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

Lemma has_implies_alt :
  (forall Sig G p s, Sig en G vdash p ni s ->
              closed_exp p 0 ->
              closed_env G 0 ->
              closed_env Sig 0 ->
              Sig en G vdash p ni_w s).
Proof.
  intros.
  assert (closed_decl_ty s 0);
    [eapply closed_has;
     eauto|].
  destruct has_contains_equivalence_mutind; crush.
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

Lemma has_wf :
  forall Sig G p s, Sig en G vdash p ni s ->
             Sig wf_st ->
             Sig evdash G wf_env ->
             Sig en G vdash p wf_e ->
             Sig en G vdash s wf_s.
Proof.
  intros.

  apply alt_has_wf with (p:=p);
    auto.
  apply has_implies_alt;
    auto.
  intros n Hle;
    eapply wf_closed_exp;
    eauto.
  eapply wf_closed_env;
    eauto.
  apply wf_closed_store_type;
    auto.
Qed.

Lemma closed_raise_inverse_mutind :
  (forall t n, forall m,  m <= n ->
                closed_t (S n) (t raise_t m) ->
                closed_t n t) /\

  (forall s n, forall m,  m <= n ->
                closed_s (S n) (s raise_s m) ->
                closed_s n s) /\

  (forall ss n, forall m,  m <= n ->
                 closed_ss (S n) (ss raise_ss m) ->
                 closed_ss n ss) /\

  (forall e n, forall m,  m <= n ->
                closed_e (S n) (e raise_e m) ->
                closed_e n e) /\

  (forall d n, forall m,  m <= n ->
                closed_d (S n) (d raise_d m) ->
                closed_d n d) /\

  (forall ds n, forall m,  m <= n ->
                 closed_ds (S n) (ds raise_ds m) ->
                 closed_ds n ds).
Proof.
  apply type_exp_mutind;
    intros;
    auto;
    try solve [inversion H1;
               subst;
               try apply cl_sel;
               try apply cl_acc;
               try apply cls_upper;
               try apply cls_lower;
               try apply cls_equal;
               try apply cls_value;
               try apply cld_equal;
               apply H with (m:=m);
               crush];
    try solve [inversion H2;
               subst;
               try apply cls_cons;
               try apply cl_app;
               try apply cl_cast;
               try apply cld_value;
               try apply cld_con;
               [apply H with (m:=m)
               |apply H0 with (m:=m)];
               crush];
    try solve [inversion H1;
               subst;
               try apply cl_str;
               try apply cl_new;
               apply H with (m:=S m);
               crush].

  (*arr*)
  inversion H2;
    subst;
    apply cl_arr;
    [apply H with (m:=m)
    |apply H0 with (m:=S m)];
    crush.

  (*fn*)
  inversion H3;
    subst;
    apply cl_fn;
    [apply H with (m:=m)
    |apply H0 with (m:=S m)
    |apply H1 with (m:=S m)];
    crush.

  destruct v as [x|x];
    auto.
  simpl in H0.
  
Abort.

Axiom excluded_middle :
  forall A, A \/ ~ A.

Lemma not_and :
  forall A B, ~ (A /\ B) -> (~ A) \/ (~ B).
Proof.
  intros.
  
  destruct (excluded_middle A);
    auto.
Qed.

Lemma not_closed_raise_mutind :
  (forall t n, ~ closed_t n t ->
          forall m, m <= n ->
               ~ closed_t (S n) (t raise_t m)) /\

  (forall s n, ~ closed_s n s ->
          forall m, m <= n ->
               ~ closed_s (S n) (s raise_s m)) /\

  (forall ss n, ~ closed_ss n ss ->
           forall m, m <= n ->
                ~ closed_ss (S n) (ss raise_ss m)) /\

  (forall e n, ~ closed_e n e ->
          forall m, m <= n ->
               ~ closed_e (S n) (e raise_e m)) /\

  (forall d n, ~ closed_d n d ->
          forall m, m <= n ->
               ~ closed_d (S n) (d raise_d m)) /\

  (forall ds n, ~ closed_ds n ds ->
           forall m, m <= n ->
                ~ closed_ds (S n) (ds raise_ds m)).
Proof.
  apply type_exp_mutind;
    intros;
    auto;
    try solve [assert (Hncl : ~ closed_t n t);
               [intro Hcontra;
                contradiction H0;
                auto|];
               apply H
                 with
                   (m:=m)
                 in Hncl;
               [|crush];
               intros Hcontra;
               inversion Hcontra;
               subst;
               auto];

    try solve [assert (Hncl : ~ closed_e n e);
               [intro Hcontra;
                contradiction H0;
                auto|];
               apply H
                 with
                   (m:=m)
                 in Hncl;
               [|crush];
               intros Hcontra;
               inversion Hcontra;
               subst;
               auto];

    try solve [assert (Hncl : ~ ((closed_e n e) /\ (closed_t n t)));
               [intro Hcontra;
                destruct Hcontra as [Ha Hb];
                contradiction H1;
                auto
               |apply not_and in Hncl;
                destruct Hncl as [Hncl|Hncl]];
               [apply H
                  with
                    (m:=m)
                 in Hncl;
                [|crush];
                intros Hcontra;
                inversion Hcontra;
                subst;
                auto
               |apply H0
                  with
                    (m:=m)
                 in Hncl;
                [|crush];
                intros Hcontra;
                inversion Hcontra;
                subst;
                auto]].

  (*str*)
  assert (Hncl : ~ closed_ss (S n) d);
    [intro Hcontra;
     contradiction H0;
     auto|].
  apply H
    with
      (m:=S m)
    in Hncl;
    [|crush]. 
  intros Hcontra.
  inversion Hcontra;
    subst;    
    auto.

  (*arr*)
  assert (Hncl : ~ ((closed_t n t) /\ (closed_t (S n) t0)));
    [intro Hcontra;
     destruct Hcontra as [Ha Hb];
     contradiction H1;
     auto
    |apply not_and in Hncl;
     destruct Hncl as [Hncl|Hncl]].
  apply H
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
  apply H0
    with
      (m:=S m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.

  (*dt_con*)
  assert (Hncl : ~ ((closed_s n d) /\ (closed_ss n d0)));
    [intro Hcontra;
     destruct Hcontra as [Ha Hb];
     contradiction H1;
     auto
    |apply not_and in Hncl;
     destruct Hncl as [Hncl|Hncl]].
  apply H
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
  apply H0
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.

  (*new*)
  assert (Hncl : ~ closed_ds (S n) d);
    [intro Hcontra;
     contradiction H0;
     auto|].
  apply H
    with
      (m:=S m)
    in Hncl;
    [|crush]. 
  intros Hcontra.
  inversion Hcontra;
    subst;    
    auto.

  (*app*)
  assert (Hncl : ~ ((closed_e n e) /\ (closed_e n e0)));
    [intro Hcontra;
     destruct Hcontra as [Ha Hb];
     contradiction H1;
     auto
    |apply not_and in Hncl;
     destruct Hncl as [Hncl|Hncl]].
  apply H
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
  apply H0
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.

  (*fn*)
  assert (Hncl : ~ ((closed_t n t) /\ (closed_e (S n) e) /\ (closed_t (S n) t0)));
    [intro Hcontra;
     destruct Hcontra as [Ha Hb];
     destruct Hb as [Hb Hc];
     contradiction H2;
     auto
    |apply not_and in Hncl;
     destruct Hncl as [Hncl|Hncl];
     [|apply not_and in Hncl;
       destruct Hncl as [Hncl|Hncl]]].
  apply H
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
  apply H0
    with
      (m:=S m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
  apply H1
    with
      (m:=S m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.

  (*var*)
  destruct v as [x|x];
    auto.
  intro Hcontra;
    simpl in Hcontra.
  inversion Hcontra;
    subst.
  inversion H3;
    subst.
  unfold raise_nat in H4.
  destruct (lt_dec x m) as [Hlt|Hlt];
    [
    |assert (Hltb:=Hlt);
     apply Nat.ltb_nlt in Hltb;
     rewrite Hltb in H4];
    contradiction H;
    apply cl_var, cl_abstract;
    crush.

  (*app*)
  assert (Hncl : ~ ((closed_d n d) /\ (closed_ds n d0)));
    [intro Hcontra;
     destruct Hcontra as [Ha Hb];
     contradiction H1;
     auto
    |apply not_and in Hncl;
     destruct Hncl as [Hncl|Hncl]].
  apply H
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
  apply H0
    with
      (m:=m)
    in Hncl;
    [|crush];
    intros Hcontra;
    inversion Hcontra;
    subst;
    auto.
Qed.

Lemma not_closed_raise_type :
  (forall t n, ~ closed_t n t ->
          forall m, m <= n ->
               ~ closed_t (S n) (t raise_t m)).
Proof.
  destruct not_closed_raise_mutind; crush.
Qed.

Lemma not_closed_raise_decl_ty :
  (forall s n, ~ closed_s n s ->
          forall m, m <= n ->
               ~ closed_s (S n) (s raise_s m)).
Proof.
  destruct not_closed_raise_mutind; crush.
Qed.

Lemma not_closed_raise_decl_tys :
  (forall ss n, ~ closed_ss n ss ->
           forall m, m <= n ->
                ~ closed_ss (S n) (ss raise_ss m)).
Proof.
  destruct not_closed_raise_mutind; crush.
Qed.

Lemma not_closed_raise_exp :
  (forall e n, ~ closed_e n e ->
          forall m, m <= n ->
               ~ closed_e (S n) (e raise_e m)).
Proof.
  destruct not_closed_raise_mutind; crush.
Qed.

Lemma not_closed_raise_decl :
  (forall d n, ~ closed_d n d ->
          forall m, m <= n ->
               ~ closed_d (S n) (d raise_d m)).
Proof.
  destruct not_closed_raise_mutind; crush.
Qed.

Lemma not_closed_raise_decls :
  (forall ds n, ~ closed_ds n ds ->
           forall m, m <= n ->
                ~ closed_ds (S n) (ds raise_ds m)).
Proof.
  destruct not_closed_raise_mutind; crush.
Qed.

Lemma closed_subst_components_inverse_mutind :
  (forall i t, closed_t i t ->
          forall p n t', t = ([p /t n] t') ->
                    ~ closed_e i p ->
                    closed_t n t') /\

  (forall i s, closed_s i s ->
          forall p n s', s = ([p /s n] s') ->
                    ~ closed_e i p ->
                    closed_s n s') /\

  (forall i ss, closed_ss i ss ->
           forall p n ss', ss = ([p /ss n] ss') ->
                      ~ closed_e i p ->
                      closed_ss n ss') /\

  (forall i e, closed_e i e ->
          forall p n e', e = ([p /e n] e') ->
                    ~ closed_e i p ->
                    closed_e n e') /\

  (forall i d, closed_d i d ->
          forall p n d', d = ([p /d n] d') ->
                    ~ closed_e i p ->
                    closed_d n d') /\

  (forall i ds, closed_ds i ds ->
           forall p n ds', ds = ([p /ds n] ds') ->
                      ~ closed_e i p ->
                      closed_ds n ds').
Proof.
  apply closed_mutind;
    intros;
    auto;
    try solve [destruct t';
               try inversion H;
               try inversion H0;
               eauto];
    try solve [destruct s';
               try inversion H;
               try inversion H0;
               eauto];
    try solve [destruct ss';
               try inversion H;
               try inversion H1;
               eauto];
    try solve [destruct e';
               try inversion H;
               try inversion H0;
               eauto];
    try solve [destruct ds';
               try inversion H;
               try inversion H1;
               eauto].

  (*arr*)
  destruct t';
    inversion H1;
    subst.
  apply cl_arr;
    eauto.
  apply H0 with (p0:=p raise_e 0);
    auto.
  apply not_closed_raise_exp;
    crush.

  (*str*)
  destruct t';
    inversion H0;
    subst.
  apply cl_str;
    eauto.
  apply H with (p0:=p raise_e 0);
    auto.
  apply not_closed_raise_exp;
    crush.
  
  (*var*)
  destruct e';
    inversion H;
    subst.
  destruct v as [y|y];
    auto.
  destruct (Nat.eq_dec n0 y) as [|Hneq];
    [subst;
     rewrite <- beq_nat_refl in H2;
     subst;
     contradiction H0;
     auto
    |auto].

  (*loc*)
  destruct e';
    inversion H;
    subst;
    auto.
  destruct v as [y|y];
    [inversion H2|].
  destruct (n0 =? y);
    [|inversion H2];
    subst p;
    contradiction H0;
    auto.

  (*cast*)
  destruct e';
    inversion H1;
    subst;
    eauto.
  destruct v as [y|y];
    auto;
    destruct (n0 =? y);
    [|inversion H4];
    subst;
    contradiction H2;
    auto.

  (*new*)
  destruct e';
    inversion H0;
    subst.
  apply cl_new.
  apply H with (p0:=p raise_e 0); auto.
  apply not_closed_raise_exp;
    crush.
  destruct v as [y|y];
    auto;
    destruct (n0 =? y);
    [|inversion H3];
    subst;
    contradiction H1;
    auto.

  (*app*)
  destruct e';
    inversion H1;
    subst;
    eauto.
  destruct v as [y|y];
    auto;
    destruct (n0 =? y);
    [|inversion H4];
    subst;
    contradiction H2;
    auto.

  (*acc*)
  destruct e';
    inversion H0;
    subst;
    eauto.
  destruct v as [y|y];
    auto;
    destruct (n0 =? y);
    [|inversion H3];
    subst;
    contradiction H1;
    auto.

  (*fn*)
  destruct e';
    inversion H2;
    subst.
  apply cl_fn;
    eauto.
  apply H0 with (p0:=p raise_e 0); auto.
  apply not_closed_raise_exp;
    crush.
  apply H1 with (p0:=p raise_e 0); auto.
  apply not_closed_raise_exp;
    crush.
  destruct v as [y|y];
    auto;
    destruct (n0 =? y);
    [|inversion H5];
    subst;
    contradiction H3;
    auto.

  (*decl equal*)
  destruct d';
    inversion H0;
    subst;
    eauto.

  (*decl value*)
  destruct d';
    inversion H1;
    subst;
    eauto.
Qed.

Lemma closed_subst_components_inverse_type :
  (forall i t, closed_t i t ->
          forall p n t', t = ([p /t n] t') ->
                    ~ closed_e i p ->
                    closed_t n t').
Proof.
  destruct closed_subst_components_inverse_mutind; crush.
Qed.

Lemma closed_subst_components_inverse_decl_ty :
  (forall i s, closed_s i s ->
          forall p n s', s = ([p /s n] s') ->
                    ~ closed_e i p ->
                    closed_s n s').
Proof.
  destruct closed_subst_components_inverse_mutind; crush.
Qed.

Lemma closed_subst_components_inverse_decl_tys :
  (forall i ss, closed_ss i ss ->
           forall p n ss', ss = ([p /ss n] ss') ->
                      ~ closed_e i p ->
                      closed_ss n ss').
Proof.
  destruct closed_subst_components_inverse_mutind; crush.
Qed.

Lemma closed_subst_components_inverse_exp :
  (forall i e, closed_e i e ->
          forall p n e', e = ([p /e n] e') ->
                    ~ closed_e i p ->
                    closed_e n e').
Proof.
  destruct closed_subst_components_inverse_mutind; crush.
Qed.

Lemma closed_subst_components_inverse_decl :
  (forall i d, closed_d i d ->
          forall p n d', d = ([p /d n] d') ->
                    ~ closed_e i p ->
                    closed_d n d').
Proof.
  destruct closed_subst_components_inverse_mutind; crush.
Qed.

Lemma closed_subst_components_inverse_decls :
  (forall i ds, closed_ds i ds ->
           forall p n ds', ds = ([p /ds n] ds') ->
                      ~ closed_e i p ->
                      closed_ds n ds').
Proof.
  destruct closed_subst_components_inverse_mutind; crush.
Qed.

Lemma closed_contains_wf :
  forall Sig G t s, Sig en G vdash s cont t ->
             Sig wf_st ->
             Sig evdash G wf_env ->
             Sig en G vdash t wf_t ->
             closed_decl_ty s 0 ->
             Sig en G vdash s wf_s.
Proof.
  intros Sig G t s Hcont;
    induction Hcont;
    intros.

  (*struct*)
  assert (d cont_w (str ds));
    auto.
  assert (Hwf : Sig en (str ds)::G vdash [c_ (length G) /s 0]d wf_s);
    [apply struct_contains_wf';
     auto|].
  rewrite closed_subst_decl_ty in Hwf;
    auto.
  apply wf_strengthening_decl_ty_actual
    with
      (t:=str ds)
      (i:=length G);
    auto.
  apply wf_unbound_type
    with
      (r:=length G)
    in H2;
    auto;
    inversion H2;
    auto.
  eapply unbound_in_dty;
    eauto.
  eapply wf_notin_env;
    eauto.

  (*upper*)
  assert (Hwfp : Sig en G vdash p wf_e);
    [inversion H2;
     auto|].
  assert (Hwt : Sig en G vdash t wf_t);
    [apply has_wf in H;
     auto;
     inversion H;
     auto|].
  eapply closed_subst_components_inverse_decl_ty in H3;
    eauto;
    [rewrite closed_subst_decl_ty;
     auto;
     apply IHHcont;
     auto|].
  intros n' Hle;
    destruct n' as [|n''];
    auto.
  apply closed_contains in Hcont;
    auto.
  apply Hcont;
    crush.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  intros n' Hle';
    eapply wf_closed_type;
    eauto.
  intros Hcontra;
    auto;
    inversion Hcontra;
    subst.
  inversion H7;
    subst.
  inversion H6;
    auto.

  (*equal*)
  assert (Hwfp : Sig en G vdash p wf_e);
    [inversion H2;
     auto|].
  assert (Hwt : Sig en G vdash t wf_t);
    [apply has_wf in H;
     auto;
     inversion H;
     auto|].
  eapply closed_subst_components_inverse_decl_ty in H3;
    eauto;
    [rewrite closed_subst_decl_ty;
     auto;
     apply IHHcont;
     auto|].
  intros n' Hle;
    destruct n' as [|n''];
    auto.
  apply closed_contains in Hcont;
    auto.
  apply Hcont;
    crush.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  intros n' Hle';
    eapply wf_closed_type;
    eauto.
  intros Hcontra;
    auto;
    inversion Hcontra;
    subst.
  inversion H7;
    subst.
  inversion H6;
    auto.
Qed.

Lemma typing_wf_decl :
  (forall Sig G d s, Sig en G vdash d hasType_d s ->
              Sig en G vdash d wf_d ->
              Sig en G vdash s wf_s).
Proof.
  intros Sig G d s Htyp;
    destruct Htyp;
    intros.

  (*equal*)
  inversion H;
    auto.

  (*value*)
  inversion H1;
    auto.
Qed.

Lemma decl_typing_same_id :
  forall Sig G d s, Sig en G vdash d hasType_d s ->
             id_d d = id_t s.
Proof.
  intros Sig G d s Htyp;
    destruct Htyp;
    auto.
Qed.

Lemma decls_typing_same_ids :
  forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
               forall d, in_d d ds ->
                    exists s, (in_dty s ss /\ id_d d = id_t s).
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp;
    intros;
    auto.

  inversion H.

  inversion H0;
    subst.
  exists s;
    split;
    [apply in_head_dty|].
  eapply decl_typing_same_id;
    eauto.

  destruct IHHtyp
    with
      (d:=d0)
    as [s' Ha];
    auto;
    destruct Ha as [Ha Hb].
  exists s';
    split;
    auto.
  apply in_tail_dty;
    auto.
Qed.

Lemma decls_typing_exists_decl_typing :
  forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
               forall d, in_d d ds ->
                    exists s, (in_dty s ss /\ Sig en G vdash d hasType_d s).
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp;
    intros;
    auto.

  inversion H.

  inversion H0;
    subst.

  exists s;
    split;
    auto.
  apply in_head_dty.

  destruct (IHHtyp d0) as [s' Ha];
    auto;
    destruct Ha as [Ha Hb].
  exists s';
    split;
    auto.
  apply in_tail_dty;
    auto.
Qed.

Lemma decls_typing_exists_decl_typing' :
  forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
               forall s, in_dty s ss ->
                    exists d, (in_d d ds /\ Sig en G vdash d hasType_d s).
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp;
    intros;
    auto.

  inversion H.

  inversion H0;
    subst.

  exists d;
    split;
    auto.
  apply in_head_d.

  destruct (IHHtyp s0) as [d' Ha];
    auto;
    destruct Ha as [Ha Hb].
  exists d';
    split;
    auto.
  apply in_tail_d;
    auto.
Qed.

Lemma typing_wf_decls :
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                Sig en G vdash ds wf_ds ->
                Sig en G vdash ss wf_ss).
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp;
    intros;
    auto.

  (*value*)
  inversion H0;
    subst;
    auto.
  apply wft_con;
    auto.
  eapply typing_wf_decl;
    eauto.
  intros s' Hin Hcontra.
  apply decl_typing_same_id in H.
  destruct decls_typing_exists_decl_typing'
    with
      (Sig:=Sig)(G:=G)
      (ds:=ds)(ss:=ss)
      (s:=s')
    as [d' Ha];
    auto;
    destruct Ha as [Ha Hb].
  apply decl_typing_same_id in Hb.
  contradiction (H7 d' Ha).
  rewrite Hb, H;
    auto.
Qed.

Lemma typing_unique_decl :
  forall Sig G d s, Sig en G vdash d hasType_d s ->
             forall Sig' G' s', Sig' en G' vdash d hasType_d s' ->
                           s' = s.
Proof.
  intros Sig G d s Htyp;
    destruct Htyp;
    intros.

  inversion H; auto.

  inversion H1; auto.
  
Qed.

Lemma typing_unique_decls :
  forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
               forall Sig' G' ss', Sig' en G' vdash ds hasType_ds ss' ->
                              ss' = ss.
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp;
    intros.

  inversion H; auto.

  inversion H0;
    subst;
    auto.
  apply IHHtyp in H7;
    subst ss0.
  eapply typing_unique_decl with (s:=s) in H5;
    eauto;
    subst;
    auto.
Qed.

Lemma typing_wf_exp :
  (forall Sig G e t, Sig en G vdash e hasType t ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash e wf_e ->
              Sig en G vdash t wf_t).
Proof.
  intros Sig G e t Htyp;
    induction Htyp;
    intros;
    auto.

  (*var*)
  apply wf_in_env;
    auto.
  apply in_rev, get_in with (n0:=n);
    auto.

  (*loc*)
  apply wf_in_store_type;
    auto.
  apply in_rev, get_in with (n:=i);
    auto.

  (*cast*)
  inversion H2;
    auto.

  (*fn*)
  inversion H1;
    subst.
  apply wf_arr;
    auto.

  (*app closed*)
  inversion H3;
    subst.
  assert (Hwf_arr : Sig en G vdash t1 arr t2 wf_t);
    [apply IHHtyp1;
     auto
    |inversion Hwf_arr;
     subst].
  assert (closed_t 0 t2);
    [apply H0;
     eapply wf_closed_type;
     eauto
    |rewrite closed_subst_type in H14;
     auto].
  apply wf_strengthening_type_actual
    with
      (t':=t1)(i:=length G);
    auto.
  eapply wf_notin_env;
    eauto.

  (*app path*)
  assert (Hwf_arr : Sig en G vdash (t1 arr t2) wf_t);
    [apply IHHtyp;
     inversion H3;
     auto|].
  inversion Hwf_arr;
    subst.
  apply wf_subst_type_actual
    with
      (p:=p cast t1)
    in H10;
    eauto.
  apply wf_con;
    auto.
  apply wf_cast with (t':=t');
    eauto.
  inversion H3;
    auto.
  apply path_typing_implies_typing;
    auto.
  inversion H3;
    auto.

  (*new*)
  inversion H3;
    subst.
  apply typing_wf_decls in H;
    auto.
  inversion H5;
    subst.
  apply typing_unique_decls
    with
      (Sig:=Sig)(G:=str ss ::G)(ss:=[v_ Var (length G) /ss 0] ss)
    in H11;
    auto.  
  apply subst_equality_decl_tys in H11;
    auto;
    subst ss0;
    auto.

  (*acc path*)
  apply has_wf in H;
    auto.
  inversion H; auto.
  inversion H2; auto.

  (*acc closed*)
  apply closed_contains_wf in H;
    auto.
  inversion H;
    auto.
  apply IHHtyp;
    auto.
  inversion H3;
    auto.
  apply closed_decl_ty_value.
  intros n' Hle; apply H0.
  apply closed_typing_exp in Htyp;
    auto.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  intros n'' Hle';
    apply wf_closed_exp with (Sig:=Sig)(G:=G).
  inversion H3;
    auto.
Qed.


Lemma member_wf :
  forall Sig G e s, Sig en G vdash e mem s ->
             Sig wf_st ->
             Sig evdash G wf_env ->
             Sig en G vdash e wf_e ->
             Sig en G vdash s wf_s.
Proof.
  intros Sig G e s Hmem;
    induction Hmem;
    intros.

  eapply has_wf;
    eauto.

  eapply closed_contains_wf;
    eauto.
  eapply typing_wf_exp;
    eauto.

  intros n Hle;
    destruct n as [|n'];
    auto.
  apply closed_contains in H0;
    auto.
  apply H0;
    crush.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  eapply closed_typing_exp;
    eauto.
  apply wf_closed_store_type;
    auto.
  eapply wf_closed_env;
    eauto.
  intros n'' Hle';
    eapply wf_closed_exp;
    eauto.
Qed.

Lemma wf_decls_in_dty_unique :
  forall s ss, in_dty s ss ->
          forall Sig G, Sig en G vdash ss wf_ss ->
                 forall s', in_dty s' ss ->
                       id_t s' = id_t s ->
                       s' = s.
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    auto.

  inversion H0;
    subst;
    auto.
  inversion H;
    subst.
  apply H9 in H4;
    crush.

  inversion H0;
    subst.
  inversion H;
    subst.
  apply H8 in Hin;
    crush.
  inversion H;
    subst.
  eapply IHHin;
    eauto.
Qed.

Lemma has_contains_unique_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash p wf_e ->
              forall s', Sig en G vdash p ni s' ->
                    id_t s' = id_t s ->
                    s' = s) /\
  
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash t wf_t ->
              forall s', Sig en G vdash s' cont t ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  apply has_contains_mutind;
    intros;
    auto.

  (*has path*)
  inversion H3;
    subst.
  apply path_typing_uniqueness
    with
      (t:=t)
    in H5;
    auto;
    subst t1.
  apply H in H6;
    auto;
    [subst d0;
     auto
    |eapply path_typing_wf;
     eauto
    |].
  repeat rewrite idt_subst in H4;
    auto.

  (*struct*)
  inversion H2;
    subst.
  inversion H1;
    subst.
  assert (Hin1 := i);
    assert (Hin2 := H7).
  apply subst_in_dty
    with
      (p:=c_ (length G))(n:=0)
    in i.
  apply subst_in_dty
    with
      (p:=c_ (length G))(n:=0)
    in H7.
  rewrite <- idt_subst
    with
      (p:=c_ (length G))(n:=0)
    in H3.
  rewrite <- idt_subst
    with
      (p:=c_ (length G))(n:=0)
      (s:=d)
    in H3.
  apply wf_decls_in_dty_unique
    with
      (Sig:=Sig)(G:=str ds :: G)
      (ss:=[c_ (length G) /ss 0]ds)
    in H3;
    auto.
  apply subst_equality_decl_ty in H3;
    auto;
    eapply unbound_var_notin_decl_ty, unbound_in_dty;
    eauto.
  
  
  
  (*upper*)
  inversion H4;
    subst;
  apply H in H10;
    auto;
    try solve [inversion H3; auto].
  inversion H10;
    subst.
  apply H0 in H12;
    auto;
    subst;
    auto;
    [|repeat rewrite idt_subst in H5; auto].
  apply has_wf in h;
    auto;
    [inversion h;
     auto
    |inversion H3;
     auto].

  inversion H10.

  inversion H4;
    subst;
  apply H in H10;
    auto;
    try solve [inversion H3; auto].
  inversion H10.
  
  inversion H10;
    subst.
  apply H0 in H12;
    auto;
    subst;
    auto;
    [|repeat rewrite idt_subst in H5; auto].
  apply has_wf in h;
    auto;
    [inversion h;
     auto
    |inversion H3;
     auto].
Qed.

Lemma has_unique :
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash p wf_e ->
              forall s', Sig en G vdash p ni s' ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  destruct has_contains_unique_mutind; crush.
Qed.

Lemma contains_unique :
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash t wf_t ->
              forall s', Sig en G vdash s' cont t ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  destruct has_contains_unique_mutind; crush.
Qed.

(*perhaps misnamed. This denotes a type that could super type a function*)
Inductive fn_type : env -> env -> ty -> Prop :=
| fn_top : forall Sig G, fn_type Sig G top
| fn_arr : forall Sig G t1 t2, fn_type Sig G (t1 arr t2)
| fn_upper : forall Sig G p l t, Sig en G vdash p ni (type l ext t) ->
                          fn_type Sig G t ->
                          fn_type Sig G (sel p l)
| fn_lower : forall Sig G p l t, Sig en G vdash p ni (type l sup t) ->
                          fn_type Sig G t ->
                          fn_type Sig G (sel p l)
| fn_equal : forall Sig G p l t, Sig en G vdash p ni (type l eqt t) ->
                          fn_type Sig G t ->
                          fn_type Sig G (sel p l).

Hint Constructors fn_type.

Inductive is_func : exp -> Prop :=
| isf_func : forall t1 e t2, is_func (fn t1 in_exp e off t2)
| isf_cast : forall f t, is_func f ->
                    is_func (f cast t).

Hint Constructors is_func.
    
Lemma is_path_or_non_object :
  forall v, is_value v ->
       (is_path v) \/ (is_func v).
Proof.
  intros v Hval;
    induction Hval;
    auto.

  destruct IHHval;
    auto.
Qed.

Lemma subtype_func_type :
  forall Sig G t1 t2 G', Sig en G vdash t1 <; t2 dashv G' ->
                   Sig wf_st ->
                   Sig evdash G wf_env ->
                   Sig en G vdash t1 wf_t ->
                   Sig en G vdash t2 wf_t ->
                   G' = G ->
                   fn_type Sig G t1 ->
                   fn_type Sig G t2.
Proof.
  intros Sig G t1 t2 G' Hsub;
    induction Hsub;
    intros;
    subst G2;
    auto.

  inversion H4.

  (*s-upper*)
  assert (Hwf_p : Sig en G1 vdash p wf_e);
    [inversion H2;
     auto
    |].
  assert (Hwf_t1 : Sig en G1 vdash t1 wf_t);
    [apply has_wf in H;
     auto;
     inversion H;
     auto|].
  apply IHHsub;
    auto.
  inversion H5;
    subst;
    auto;
    apply has_unique
    with
      (s:=type L ext t1)
    in H9;
    auto;
    inversion H9;
    subst;
    auto.

  (*s-lower*)
  assert (Hwf_p : Sig en G1 vdash p wf_e);
    [inversion H3;
     auto
    |].
  assert (Hwf_t1 : Sig en G1 vdash t2 wf_t);
    [apply has_wf in H;
     auto;
     inversion H;
     auto|].
  apply fn_lower with (t:=t2);
    auto.

  (*s-equal1*)
  assert (Hwf_p : Sig en G1 vdash p wf_e);
    [inversion H2;
     auto
    |].
  assert (Hwf_t1 : Sig en G1 vdash t1 wf_t);
    [apply has_wf in H;
     auto;
     inversion H;
     auto|].
  apply IHHsub;
    auto.
  inversion H5;
    subst;
    auto;
    apply has_unique
    with
      (s:=type L eqt t1)
    in H9;
    auto;
    inversion H9;
    subst;
    auto.

  (*s-equal2*)
  assert (Hwf_p : Sig en G1 vdash p wf_e);
    [inversion H3;
     auto
    |].
  assert (Hwf_t1 : Sig en G1 vdash t2 wf_t);
    [apply has_wf in H;
     auto;
     inversion H;
     auto|].
  apply fn_equal with (t:=t2);
    auto.

  inversion H7.
Qed.

Inductive cont_type : env -> env -> ty -> Prop :=
| ct_str : forall Sig G ss, cont_type Sig G (str ss)
| ct_upper :forall Sig G p l t, Sig en G vdash p ni (type l ext t) ->
                         cont_type Sig G t ->
                         cont_type Sig G (sel p l)
| ct_equal :forall Sig G p l t, Sig en G vdash p ni (type l eqt t) ->
                         cont_type Sig G t ->
                         cont_type Sig G (sel p l)
| ct_bot : forall Sig G, cont_type Sig G bot.

Hint Constructors cont_type.



Lemma is_func_has_func_type :
  forall f, is_func f ->
       forall Sig G t, Sig en G vdash f hasType t ->
                Sig wf_st ->
                Sig evdash G wf_env ->
                Sig en G vdash f wf_e ->
                fn_type Sig G t.
Proof.
  intros f Hfn;
    induction Hfn;
    intros;
    auto.

  inversion H;
    subst;
    auto.

  inversion H;
    subst.
  eapply subtype_func_type;
    eauto.
  apply typing_wf_exp with (e:=f);
    auto.
  inversion H2;
    auto.
  inversion H2;
    auto.
  apply IHHfn;
    auto.
  inversion H2;
    auto.
Qed.




Scheme wf_ty_mut_ind := Induction for wf_ty Sort Prop
  with wf_decl_ty_mut_ind := Induction for wf_decl_ty Sort Prop
  with wf_decl_tys_mut_ind := Induction for wf_decl_tys Sort Prop
  with wf_exp_mut_ind := Induction for wf_exp Sort Prop
  with wf_decl_mut_ind := Induction for wf_decl Sort Prop
  with wf_decls_mut_ind := Induction for wf_decls Sort Prop.

Combined Scheme wf_mutind from wf_ty_mut_ind, wf_decl_ty_mut_ind, wf_decl_tys_mut_ind,
wf_exp_mut_ind, wf_decl_mut_ind, wf_decls_mut_ind.

Lemma non_path_substitution_wf :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall v tf, Sig en G vdash v hasType tf ->
                    fn_type Sig G tf ->
                    forall t' n, t = ([v /t n] t') ->
                            closed_t n t') /\

  (forall Sig G s, Sig en G vdash s wf_s ->
            forall v tf, Sig en G vdash v hasType tf ->
                    fn_type Sig G tf ->
                    forall s' n, s = ([v /s n] s') ->
                            closed_s n s') /\

  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall v tf, Sig en G vdash v hasType tf ->
                     fn_type Sig G tf ->
                     forall ss' n, ss = ([v /ss n] ss') ->
                              closed_ss n ss') /\

  (forall Sig G p, Sig en G vdash p wf_e ->
            is_path p ->
            forall v tf, Sig en G vdash v hasType tf ->
                    fn_type Sig G tf ->
                    forall p' n, p = ([v /e n] p') ->
                            closed_e n p').
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

Inductive mem_unique : ty -> Prop :=
| uniq_top : mem_unique top
| uniq_bot : mem_unique bot
| uniq_arr : forall t1 t2, mem_unique t1 ->
                      mem_unique t2 ->
                      mem_unique (t1 arr t2)
| uniq_sel : forall p l, mem_unique_p p ->
                    mem_unique (sel p l)
| uniq_str : forall ss, mem_unique_ss ss ->
                   mem_unique (str ss rts)

with
mem_unique_s : decl_ty -> Prop :=
| uniq_upp : forall l t, mem_unique t ->
                    mem_unique_s (type l ext t)
| uniq_low : forall l t, mem_unique t ->
                    mem_unique_s (type l sup t)
| uniq_equ : forall l t, mem_unique t ->
                    mem_unique_s (type l eqt t)
| uniq_val : forall l t, mem_unique t ->
                    mem_unique_s (val l oft t)

with
mem_unique_ss : decl_tys -> Prop :=
| uniq_nil : mem_unique_ss dt_nil
| uniq_con : forall s ss, mem_unique_s s ->
                     mem_unique_ss ss ->
                     (forall s', in_dty s' ss ->
                            id_t s' <> id_t s) ->
                     mem_unique_ss (dt_con s ss)

with
mem_unique_p : exp -> Prop :=
| uniq_var : forall r, mem_unique_p (v_ r)
| uniq_loc : forall i, mem_unique_p (i_ i)
| uniq_cast : forall p t, mem_unique t ->
                     mem_unique_p (p cast t)
| uniq_fn : forall t1 e t2, mem_unique_p (fn t1 in_exp e off t2)
| uniq_app : forall e1 e2, mem_unique_p (e_app e1 e2)
| uniq_acc : forall e l, mem_unique_p (e_acc e l)
| uniq_new : forall ds, mem_unique_p (new ds).

Hint Constructors mem_unique mem_unique_s mem_unique_ss mem_unique_p.

Scheme uniq_t_mut_ind := Induction for mem_unique Sort Prop
  with uniq_s_mut_ind := Induction for mem_unique_s Sort Prop
  with uniq_ss_mut_ind := Induction for mem_unique_ss Sort Prop
  with uniq_p_mut_ind := Induction for mem_unique_p Sort Prop.

Combined Scheme uniq_mutind from uniq_t_mut_ind, uniq_s_mut_ind, uniq_ss_mut_ind, uniq_p_mut_ind.

Definition mem_unique_ctx (G : env) := forall t, In t G -> mem_unique t.


Lemma mem_unique_path_typing :
  forall Sig G p t, Sig en G vdash p pathType t ->
             mem_unique_ctx Sig ->
             mem_unique_ctx G ->
             mem_unique_p p ->
             mem_unique t.
Proof.
  intros.
  induction H.

  (*var*)
  apply H1.
  apply in_rev;
    eapply get_in;
    eauto.

  (*loc*)
  apply H0.
  apply in_rev;
    eapply get_in;
    eauto.

  inversion H2;
    auto.
  
Qed.

Lemma in_dty_exists_raise :
  forall s ss, in_dty s ss ->
          forall ss' n, ss = (ss' raise_ss n) ->
                   exists s', s = (s' raise_s n).
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    auto.

  destruct ss' as [|s' ss'];
    inversion H; subst.

  eauto.

  destruct ss' as [|s' ss'];
    inversion H; subst.
  apply  IHHin with (ss'0:=ss');
    auto.
Qed.

Lemma in_dty_raise :
  forall s ss, in_dty s ss -> forall n, in_dty (s raise_s n) (ss raise_ss n).
Proof.
  
  intros s ss Hin;
    induction Hin;
    intros;
    simpl.
  apply in_head_dty.
  apply in_tail_dty.
  apply IHHin.
Qed.

Lemma in_dty_raise_id :
  forall s ss n, in_dty (s raise_s n) (ss raise_ss n) ->
            exists s', id_t s = id_t s' /\
                  in_dty s' ss.
Proof.
  intros s ss;
    induction ss as [|s' ss'];
    intros.

  simpl in H;
    inversion H.

  inversion H;
    subst.
  exists s';
    split; [|apply in_head_dty].
  destruct s, s';
    simpl in H2;
    inversion H2;
    subst;
    auto.

  apply IHss' in H2.
  destruct H2 as [s'' Ha];
    destruct Ha as [Ha Hb].
  exists s'';
    split; [auto|apply in_tail_dty; auto].
Qed.

Lemma id_t_raise :
  forall s n, id_t (s raise_s n) = id_t s.
Proof.
  intros s;
    destruct s;
    intros;
    simpl;
    auto.
Qed.

Lemma mem_unique_raise_mutind :
  (forall t, mem_unique t ->
        forall n, mem_unique (t raise_t n)) /\

  (forall s, mem_unique_s s ->
        forall n, mem_unique_s (s raise_s n)) /\

  (forall ss, mem_unique_ss ss ->
         forall n, mem_unique_ss (ss raise_ss n)) /\

  (forall p, mem_unique_p p ->
        forall n, mem_unique_p (p raise_e n)).
Proof.
  apply uniq_mutind;
    intros;
    simpl;
    auto.

  apply uniq_con;
    auto.
  intros.
  intros Hcontra.

  destruct (in_dty_exists_raise H1)
    with
      (ss':=ss)(n:=n0)
    as [s'' Ha];
    auto;
    subst s'.
  apply in_dty_raise_id in H1;
    destruct H1 as [s' Ha];
    destruct Ha as [Ha Hb].
  apply n in Hb.
  repeat rewrite id_t_raise in Hcontra.
  rewrite Ha in Hcontra; auto.
Qed.

Lemma mem_unique_raise_p :
  (forall p, mem_unique_p p ->
        forall n, mem_unique_p (p raise_e n)).
Proof.
  destruct mem_unique_raise_mutind; crush.
Qed.

Lemma in_dty_subst_id :
  forall s ss p n, in_dty s ([p /ss n] ss) ->
              exists s', id_t s = id_t s' /\
                    in_dty s' ss.
Proof.
  intros s ss;
    induction ss as [|s' ss];
    intros.

  simpl in H;
    inversion H.

  inversion H;
    subst.
  exists s'; split; [|apply in_head_dty].
  apply idt_subst.

  destruct IHss
    with
      (p:=p)(n:=n)
    as [s'' Ha];
    auto;
    destruct Ha as [Ha Hb].
  exists s'';
    split;
    auto;
    apply in_tail_dty;
    auto.
Qed.

Lemma in_dty_subst_id_converse :
  forall s ss, in_dty s ss ->
          forall p n, exists s', id_t s = id_t s' /\
                       in_dty s' ([p /ss n]ss).
Proof.
  intros s ss Hin;
    induction Hin;
    intros.

  exists ([p /s n] d);
    split;
    [symmetry; apply idt_subst
    |apply in_head_dty].

  destruct IHHin
    with
      (p:=p)(n:=n)
    as [s' Ha];
    destruct Ha as [Ha Hb].
  exists s';
    split;
    auto.
  apply in_tail_dty;
    auto.
Qed.

Lemma mem_unique_subst_mutind :
  (forall t, mem_unique t ->
        forall p n, mem_unique_p p ->
               mem_unique ([p /t n] t)) /\

  (forall s, mem_unique_s s ->
        forall p n, mem_unique_p p ->
               mem_unique_s ([p /s n] s)) /\

  (forall ss, mem_unique_ss ss ->
         forall p n, mem_unique_p p ->
                mem_unique_ss ([p /ss n] ss)) /\

  (forall p, mem_unique_p p ->
        forall p' n, mem_unique_p p' ->
                mem_unique_p ([p' /e n] p)).
Proof.
  apply uniq_mutind;
    intros;
    simpl;
    auto.

  apply uniq_arr;
    auto.
  apply H0.
  apply mem_unique_raise_p;
    auto.
    
  apply uniq_str.
  apply H.
  apply mem_unique_raise_p;
    auto.

  apply uniq_con; auto.
  intros.
  destruct in_dty_subst_id
    with
      (ss:=ss)(s:=s')
      (p:=p)(n:=n0)
    as [s'' Ha];
    auto;
    destruct Ha as [Ha Hb].
  apply n in Hb.
  rewrite idt_subst;
    intros Hcontra.
  rewrite Ha in Hcontra;
    auto.

  destruct r as [|m];
    auto;
    destruct (n =? m);
    auto.
Qed.

Lemma mem_unique_subst_type :
  (forall t, mem_unique t ->
        forall p n, mem_unique_p p ->
               mem_unique ([p /t n] t)).
Proof.
  destruct mem_unique_subst_mutind;
    auto.
Qed.

Lemma mem_unique_subst_decl_ty :
  (forall s, mem_unique_s s ->
        forall p n, mem_unique_p p ->
               mem_unique_s ([p /s n] s)).
Proof.
  destruct mem_unique_subst_mutind; crush.
Qed.

Lemma mem_unique_subst_decl_tys :
  (forall ss, mem_unique_ss ss ->
        forall p n, mem_unique_p p ->
               mem_unique_ss ([p /ss n] ss)).
Proof.
  destruct mem_unique_subst_mutind; crush.
Qed.

Scheme type_exp_uniq_t_mut_ind := Induction for ty Sort Prop
  with type_exp_uniq_s_mut_ind := Induction for decl_ty Sort Prop
  with type_exp_uniq_ss_mut_ind := Induction for decl_tys Sort Prop
  with type_exp_uniq_p_mut_ind := Induction for exp Sort Prop.

Combined Scheme type_exp_uniq_mutind from type_exp_uniq_t_mut_ind, type_exp_uniq_s_mut_ind, type_exp_uniq_ss_mut_ind, type_exp_uniq_p_mut_ind.

Lemma mem_unique_subst_components_mutind :
  (forall t p n, mem_unique ([p /t n] t) ->
            mem_unique t) /\

  (forall s p n, mem_unique_s ([p /s n] s) ->
            mem_unique_s s) /\

  (forall ss p n, mem_unique_ss ([p /ss n] ss) ->
             mem_unique_ss ss) /\

  (forall e p n, mem_unique_p ([p /e n] e) ->
            mem_unique_p e).
Proof.
  apply type_exp_uniq_mutind;
    intros;
    auto;
    try solve [inversion H0;
               eauto].

  inversion H1;
    subst;
    eauto.
  
  inversion H1;
    subst.
  apply uniq_con;
    eauto.
  intros.
  destruct in_dty_subst_id_converse
    with
      (s:=s')(ss:=d0)
      (p:=p)(n:=n)
    as [s'' Ha];
    auto;
    destruct Ha as [Ha Hb].
  apply H6 in Hb.
  rewrite idt_subst, <- Ha in Hb;
    auto.

  inversion H1;
    eauto.
Qed.
  
Lemma mem_unique_in_dty :
  forall ss, mem_unique_ss ss ->
        forall s, in_dty s ss ->
             mem_unique_s s.
Proof.
  intros ss Huniq;
    induction Huniq;
    intros.

  inversion H.

  inversion H1;
    subst;
    auto.
Qed.

Lemma mem_unique_has_contains_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique_p p ->
              mem_unique_s s) /\
  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique t ->
              mem_unique_s s).
Proof.
  apply has_contains_mutind;
    intros.
  
  apply mem_unique_subst_decl_ty;
    auto.
  apply H;
    auto.
  eapply mem_unique_path_typing;
    eauto.

  inversion H1;
    subst;
    auto.
  eapply mem_unique_in_dty;
    eauto.

  apply H0;
    auto.
  inversion H3;
    subst.
  apply H in H5;
    auto.
  inversion H5;
    auto.

  apply H0;
    auto.
  inversion H3;
    subst.
  apply H in H5;
    auto.
  inversion H5;
    auto.
Qed.

Lemma mem_unique_has :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique_p p ->
              mem_unique_s s).
Proof.
  destruct mem_unique_has_contains_mutind; crush.
Qed.

Lemma mem_unique_contains :
  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique t ->
              mem_unique_s s).
Proof.
  destruct mem_unique_has_contains_mutind; crush.
Qed.

Lemma mem_unique_decl_tys :
  forall ss, mem_unique_ss ss ->
        forall s1 s2, in_dty s1 ss ->
                 in_dty s2 ss ->
                 id_t s1 = id_t s2 ->
                 s1 = s2.
Proof.
  intros ss Hmem;
    induction Hmem;
    intros.
  
  inversion H.

  inversion H1;
    subst.
  inversion H2;
    subst;
    auto.
  apply H0 in H6.
  contradiction H6;
    auto.

  inversion H2;
    subst.
  apply H0 in H6.
  contradiction H6;
    auto.
  
  apply IHHmem;
    auto.
Qed.

Lemma unique_has_contains_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique_p p ->
              forall s', Sig en G vdash p ni s' ->
                    id_t s' = id_t s ->
                    s' = s) /\
  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique t ->
              forall s', Sig en G vdash s' cont t ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  apply has_contains_mutind;
    intros.

  (*has*)
  inversion H3;
    subst.
  apply path_typing_uniqueness
    with
      (t:=t)
    in H5;
    auto;
    subst t1.
  apply H in H6;
    subst;
    auto.
  eapply mem_unique_path_typing; eauto.
  repeat rewrite idt_subst in H4; auto.
  
  (*cont*)
  inversion H2;
    subst.
  inversion H1;
    subst.
  eapply mem_unique_decl_tys;
    eauto.
  
  (*upper*)
  inversion H3;
    subst.
  inversion H4;
    subst.
  apply H in H11;
    auto.
  inversion H11;
    subst.
  apply H0;
    auto.
  apply mem_unique_has in h;
    auto;
    inversion h;
    auto.

  apply H in H11;
    auto.
  inversion H11.
  
  (*equal*)
  inversion H3;
    subst.
  inversion H4;
    subst.

  apply H in H11;
    auto.
  inversion H11.
  
  apply H in H11;
    auto.
  inversion H11;
    subst.
  apply H0;
    auto.
  apply mem_unique_has in h;
    auto;
    inversion h;
    auto.
Qed.

Lemma unique_has :
  (forall Sig G p s, Sig en G vdash p ni s ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique_p p ->
              forall s', Sig en G vdash p ni s' ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  destruct unique_has_contains_mutind;
    crush.
Qed.

Lemma unique_contains :
  (forall Sig G t s, Sig en G vdash s cont t ->
              mem_unique_ctx Sig ->
              mem_unique_ctx G ->
              mem_unique t ->
              forall s', Sig en G vdash s' cont t ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  destruct unique_has_contains_mutind;
    crush.
Qed.

Scheme wf_uniq_t_mut_ind := Induction for wf_ty Sort Prop
  with wf_uniq_s_mut_ind := Induction for wf_decl_ty Sort Prop
  with wf_uniq_ss_mut_ind := Induction for wf_decl_tys Sort Prop
  with wf_uniq_p_mut_ind := Induction for wf_exp Sort Prop.

Combined Scheme wf_uniq_mutind from wf_uniq_t_mut_ind, wf_uniq_s_mut_ind, wf_uniq_ss_mut_ind, wf_uniq_p_mut_ind.

Lemma wf_implies_unique_mutind :
  (forall Sig G t, Sig en G vdash t wf_t ->
            mem_unique t) /\

  (forall Sig G s, Sig en G vdash s wf_s ->
            mem_unique_s s) /\

  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             mem_unique_ss ss) /\

  (forall Sig G e, Sig en G vdash e wf_e ->
            mem_unique_p e).
Proof.
  apply wf_uniq_mutind;
    intros;
    auto.

  apply mem_unique_subst_components_mutind in H0;
    auto.

  apply mem_unique_subst_components_mutind in H;
    auto.
  
Qed.

Lemma wf_implies_unique_env :
  forall Sig G, Sig evdash G wf_env ->
         mem_unique_ctx G.
Proof.
  intros.
  induction H;
    intros t' Hin.
  
  inversion Hin.

  inversion Hin;
    subst.

  apply wf_implies_unique_mutind in H;
    auto.

  apply IHwf_environment;
    auto.
Qed.

Lemma wf_implies_unique_store_type :
  forall Sig, Sig wf_st ->
       mem_unique_ctx Sig.
Proof.
  intros.
  induction H;
    intros t' Hin.
  
  inversion Hin.

  inversion Hin;
    subst.

  apply wf_implies_unique_mutind in H;
    auto.

  apply IHwf_store_typing;
    auto.
Qed.


Lemma wf_implies_unique_has :
  (forall Sig G p s, Sig en G vdash p ni s ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash p wf_e ->
              forall s', Sig en G vdash p ni s' ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  intros.

  apply unique_has
    with (Sig:=Sig)(G:=G)(p:=p);
    auto.
  apply wf_implies_unique_store_type;
    auto.
  eapply wf_implies_unique_env;
    eauto.
  eapply wf_implies_unique_mutind;
    eauto.
Qed.

Lemma wf_implies_unique_contains :
  (forall Sig G t s, Sig en G vdash s cont t ->
              Sig wf_st ->
              Sig evdash G wf_env ->
              Sig en G vdash t wf_t ->
              forall s', Sig en G vdash s' cont t ->
                    id_t s' = id_t s ->
                    s' = s).
Proof.
  intros.

  apply unique_contains
    with (Sig:=Sig)(G:=G)(t:=t);
    auto.
  apply wf_implies_unique_store_type;
    auto.
  eapply wf_implies_unique_env;
    eauto.
  eapply wf_implies_unique_mutind;
    eauto.
Qed.
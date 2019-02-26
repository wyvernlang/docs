Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Set Implicit Arguments.


(*get & mapsto*)

Lemma get_empty :
  forall {A : Type} (G : list A) n, G = nil -> get n G = None.
Proof.
  intros A G n; induction n as [| n']; 
    crush.
Qed.

Hint Resolve (get_empty (A:=ty)).
Hint Rewrite (get_empty (A:=ty)).


Lemma get_map :
  forall {A : Type} (G : list A) n t, get n G = Some t ->
                                 forall {B : Type} (f : A -> B), get n (map f G) = Some (f t).
Proof.
  intros A G; induction G as [|t' G']; intros.

  rewrite get_empty in H; crush.

  destruct n as [|n']; crush.
Qed.

Hint Resolve (get_map (A:=ty)).
Hint Rewrite (get_map (A:=ty)).


Lemma get_cons :
  forall {A : Type} n G (t1 t2 : A), get (S n) (t1::G) = Some t2 ->
                                get n G = Some t2.
Proof.
  intros A n; induction n as [|n']; intros; crush.
Qed.

Hint Resolve (get_cons (A:=ty)).
Hint Rewrite (get_cons (A:=ty)).


Lemma get_some_index :
  forall A G n (t : A), get n G = Some t ->
                   n < length G.
Proof.
  intros A G ; induction G as [|t' G'] ; intros.

  rewrite get_empty in H; inversion H; auto.

  destruct n as [|n']; crush.
  simpl in H; inversion H; subst.
  apply gt_n_S.
  apply IHG' with (t:=t); auto.
Qed.

Lemma get_app :
  forall A G G' n (t : A), get n G = Some t ->
                      get n (G++G') = Some t.
Proof.
  intros A G; induction G; intros; simpl.
  rewrite get_empty in H; inversion H; auto.

  destruct n as [|n']; auto.

  simpl; simpl in H; auto.
Qed.

Hint Resolve get_app.

Lemma get_dec :
  forall A (G : list A) n, {n < length G /\ exists t, get n G = Some t} + {n >= length G /\ get n G = None}.
Proof.
  intros A G; induction G as [|t' G']; intros.

  right; rewrite get_empty; split; crush.

  destruct n as [|n'];
    [left; crush; exists t'; auto|simpl].

  destruct (IHG' n') as [Hdec|Hdec];
    [left|right]; crush.
Qed.

Lemma get_some_app :
  forall A (G1 G2 : list A) n, {(n < length G1) /\ get n (G1 ++ G2) = get n G1} +
                          {n >= length G1 /\ get n (G1 ++ G2) = get (n - length G1) G2}.
Proof.
  intros A G1; induction G1 as [|t' G1']; intros; simpl;
    [right; split;
     [| rewrite <- minus_n_O]; crush|].

  destruct n as [|n'];
    [crush|destruct (IHG1' G2 n') as [Hdec|Hdec]; crush].
Qed.

Lemma get_app_l :
  forall A (G1 G2 : list A) n, n < length G1 ->
                          get n (G1++G2) = get n G1.
Proof.  
  intros A G1; induction G1 as [|t' G1']; intros; auto.
  
  simpl in H.
  inversion H.

  simpl in H.
  destruct n as [|n']; crush.
Qed.

Hint Resolve get_app_l.

Lemma get_app_r :
  forall A (G1 G2 : list A) n, n >= length G1 ->
                          get n (G1++G2) = get (n - length G1) G2.
Proof.  
  intros A G1; induction G1 as [|t' G1']; intros; simpl; auto.

  rewrite <- minus_n_O; auto.

  destruct n as [|n']; auto.
  unfold ge in H; simpl in H.
  apply le_n_0_eq in H; inversion H.

  unfold ge in H.
  simpl in H; apply le_S_n in H.
  apply (IHG1' G2) in H; auto.
Qed.

Hint Resolve get_app_r.

Lemma get_in :
  forall {A : Type} G n (t : A), get n G = Some t ->
                            In t G.
Proof.
  intros A G; induction G as [|t' G']; intros.

  rewrite get_empty in H; inversion H; auto.

  destruct n as [|n'].
  simpl in H; inversion H; subst; crush.
  simpl in H; apply IHG' in H; apply in_cons; auto.
Qed.


Lemma get_cons_dec :
  forall (A : Type) G n (t1 t2 : A), get n (G++(t1::nil)) = Some t2 ->
                                ((n < length G) /\ get n G = Some t2) \/ ((n = length G) /\ t1 = t2).
Proof.
  intros A G; induction G as [|t' G']; intros;
    destruct n as [|n']; simpl; simpl in H.

  inversion H; subst; auto.

  rewrite get_empty in H; inversion H; auto.

  inversion H; subst; left; split; crush.
  
  apply IHG' in H.
  destruct H as [H|H]; destruct H as [Heq Hnth];  [left|right]; split; auto.
  crush.
Qed.

Hint Resolve get_cons_dec.

(*Right Jump/Raise/Substitution*)

Lemma raise_rjump_distr_mutind :
  (forall t i n m, ((t [i] rjump_t n) raise_t m) = ((t raise_t m) [i] rjump_t n)) /\
  (forall s i n m, ((s [i] rjump_s n) raise_s m) = ((s raise_s m) [i] rjump_s n)) /\
  (forall ss i n m, ((ss [i] rjump_ss n) raise_ss m) = ((ss raise_ss m) [i] rjump_ss n)) /\
  (forall e i n m, ((e [i] rjump_e n) raise_e m) = ((e raise_e m) [i] rjump_e n)) /\
  (forall d i n m, ((d [i] rjump_d n) raise_d m) = ((d raise_d m) [i] rjump_d n)) /\
  (forall ds i n m, ((ds [i] rjump_ds n) raise_ds m) = ((ds raise_ds m) [i] rjump_ds n)).
Proof.
  apply type_exp_mutind; intros;
    try solve [crush].

  destruct v as [r|r]; auto.
  
Qed.

Lemma raise_rjump_distr_type :
  (forall t i n m, ((t [i] rjump_t n) raise_t m) = ((t raise_t m) [i] rjump_t n)).
Proof.
  destruct raise_rjump_distr_mutind; crush.
Qed.

Lemma raise_rjump_distr_decl_ty :
  (forall s i n m, ((s [i] rjump_s n) raise_s m) = ((s raise_s m) [i] rjump_s n)).
Proof.
  destruct raise_rjump_distr_mutind; crush.
Qed.

Lemma raise_rjump_distr_decl_tys :
  (forall ss i n m, ((ss [i] rjump_ss n) raise_ss m) = ((ss raise_ss m) [i] rjump_ss n)).
Proof.
  destruct raise_rjump_distr_mutind; crush.
Qed.

Lemma raise_rjump_distr_exp :
  (forall e i n m, ((e [i] rjump_e n) raise_e m) = ((e raise_e m) [i] rjump_e n)).
Proof.
  destruct raise_rjump_distr_mutind; crush.
Qed.

Lemma raise_rjump_distr_decl :
  (forall d i n m, ((d [i] rjump_d n) raise_d m) = ((d raise_d m) [i] rjump_d n)).
Proof.
  destruct raise_rjump_distr_mutind; crush.
Qed.

Lemma raise_rjump_distr_decls :
  (forall ds i n m, ((ds [i] rjump_ds n) raise_ds m) = ((ds raise_ds m) [i] rjump_ds n)).
Proof.
  destruct raise_rjump_distr_mutind; crush.
Qed.


Lemma rjump_subst_distr_mutind :
  (forall t p n i m, (([p /t n] t) [i] rjump_t m) = [(p [i] rjump_e m) /t n] (t [i] rjump_t m)) /\ 
  (forall s p n i m, (([p /s n] s) [i] rjump_s m) = [(p [i] rjump_e m) /s n] (s [i] rjump_s m)) /\
  (forall ss p n i m, (([p /ss n] ss) [i] rjump_ss m) = [(p [i] rjump_e m) /ss n] (ss [i] rjump_ss m)) /\
  (forall e p n i m, (([p /e n] e) [i] rjump_e m) = [(p [i] rjump_e m) /e n] (e [i] rjump_e m)) /\
  (forall d p n i m, (([p /d n] d) [i] rjump_d m) = [(p [i] rjump_e m) /d n] (d [i] rjump_d m)) /\
  (forall ds p n i m, (([p /ds n] ds) [i] rjump_ds m) = [(p [i] rjump_e m) /ds n] (ds [i] rjump_ds m)).
Proof.
  apply type_exp_mutind; intros;
    try solve [simpl;
               rewrite raise_rjump_distr_exp;
               crush];
    try solve [crush].

  simpl.
  destruct v as [r|r]; auto; simpl.
  destruct (Nat.eq_dec n r) as [Heq|Heq];
    subst;
    [rewrite <- beq_nat_refl; auto|].
  destruct (Nat.eqb_neq n r) as [Htemp Hbeq];
    apply Hbeq in Heq;
    rewrite Heq; auto.
Qed.

Lemma rjump_subst_distr_type :
  (forall t p n i m, (([p /t n] t) [i] rjump_t m) = [(p [i] rjump_e m) /t n] (t [i] rjump_t m)).
Proof.
  destruct rjump_subst_distr_mutind; crush.
Qed.

Lemma rjump_subst_distr_decl_ty :
  (forall s p n i m, (([p /s n] s) [i] rjump_s m) = [(p [i] rjump_e m) /s n] (s [i] rjump_s m)).
Proof.
  destruct rjump_subst_distr_mutind; crush.
Qed.

Lemma rjump_subst_distr_decl_tys :
  (forall ss p n i m, (([p /ss n] ss) [i] rjump_ss m) = [(p [i] rjump_e m) /ss n] (ss [i] rjump_ss m)).
Proof.
  destruct rjump_subst_distr_mutind; crush.
Qed.

Lemma rjump_subst_distr_exp :
  (forall e p n i m, (([p /e n] e) [i] rjump_e m) = [(p [i] rjump_e m) /e n] (e [i] rjump_e m)).
Proof.
  destruct rjump_subst_distr_mutind; crush.
Qed.

Lemma rjump_subst_distr_decl :
  (forall d p n i m, (([p /d n] d) [i] rjump_d m) = [(p [i] rjump_e m) /d n] (d [i] rjump_d m)).
Proof.
  destruct rjump_subst_distr_mutind; crush.
Qed.

Lemma rjump_subst_distr_decls :
  (forall ds p n i m, (([p /ds n] ds) [i] rjump_ds m) = [(p [i] rjump_e m) /ds n] (ds [i] rjump_ds m)).
Proof.
  destruct rjump_subst_distr_mutind; crush.
Qed.

Lemma rjump_length :
  forall G i n, length (G [i] rjump_env n) = length G.
Proof.
  intros; unfold right_jump_env; rewrite map_length; auto.
Qed.

Lemma in_dty_rjump :
  forall d ds, in_dty d ds -> forall i n, in_dty (d [i] rjump_s n) (ds [i] rjump_ss n).
Proof.
  intros d ds Hin; induction Hin; intros.

  simpl; apply in_head_dty.

  simpl; apply in_tail_dty; auto.
Qed.

Lemma in_dty_rjump_converse :
  forall s ss, in_dty s ss ->
               forall i n ss', ss = (ss' [i] rjump_ss n) ->
                               exists s', in_dty s' ss' /\ (s' [i] rjump_s n) = s.
Proof.
  intros s ss Hin; induction Hin; intros.
  destruct ss'; [inversion H|].
  simpl in H; inversion H; subst.
  exists d0; split; auto.
  apply in_head_dty.

  destruct ss'; inversion H; subst.

  destruct (IHHin i n ss'); auto.
  exists x; split; crush.
  apply in_tail_dty; crush.
Qed.

Lemma in_d_rjump_converse :
  forall d ds, in_d d ds ->
               forall i n ds', ds = (ds' [i] rjump_ds n) ->
                               exists d', in_d d' ds' /\ (d' [i] rjump_d n) = d.
Proof.
  intros d ds Hin; induction Hin; intros.
  destruct ds'; [inversion H|].
  simpl in H; inversion H; subst.
  exists d0; split; auto.
  apply in_head_d.

  destruct ds'; inversion H; subst.

  destruct (IHHin i n ds'); auto.
  exists x; split; crush.
  apply in_tail_d; crush.
Qed.

Lemma id_t_rjump :
  forall s i n, id_t s = id_t (s [i] rjump_s n).
Proof.
  intros.
  destruct s; crush.
Qed.

Lemma id_d_rjump :
  forall d i n, id_d d = id_d (d [i] rjump_d n).
Proof.
  intros.
  destruct d; crush.
Qed.

(*
  Lemma in_dty_subst :
    forall ss s p n, in_dty s ([p /ss n] ss) ->
                exists s', s = ([p /s n] s').
  Proof.
    intro ss; induction ss as [|s' ss']; intros; simpl in H;
      inversion H; subst.

    exists s'; auto.

    apply IHss' in H2; destruct H2 as [s''];
      exists s''; auto.
  Qed.

  Lemma in_dty_subst_notin :
    forall ss s p n, in_dty s ([p /ss n] ss)->
                forall e, e notin_ss ss ->
                     exists s', s = ([p /s n] s') /\
                           e notin_s s'.
  Proof.
    intro ss; induction ss as [|s' ss']; intros; simpl in H;
      inversion H; subst.

    exists s'; split; inversion H0; auto.

    apply IHss' with (e:=e) in H3; [|inversion H0; auto].
    destruct H3 as [s''];
      exists s''; auto.
  Qed.

  Lemma in_dty_subst_switch :
    forall ss s p1 n, in_dty ([p1 /s n] s) ([p1 /ss n] ss) ->
                 p1 notin_ss ss ->
                 p1 notin_s s ->
                 forall p2, in_dty ([p2 /s n] s) ([p2 /ss n] ss).
  Proof.
    intro ss; induction ss; intros; simpl in H;
      inversion H; subst.

    
  Qed.*)

Lemma not_in_decl_tys_rjump :
  forall s ss, (forall s', in_dty s' ss ->
                           id_t s' <> id_t s) ->
               forall i n,
                 (forall s', in_dty s' (ss [i] rjump_ss n) ->
                             id_t s' <> id_t (s [i] rjump_s n)).
Proof.
  intros.
  intros Hcontra.
  apply in_dty_rjump_converse with (i:=i)(n:=n)(ss':=ss) in H0; auto.
  destruct H0 as [s'' Ha];
    destruct Ha as [Ha Hb]; subst.
  repeat rewrite <- id_t_rjump in Hcontra.
  apply H in Ha.
  rewrite Hcontra in Ha;
    contradiction Ha; auto.
Qed.

Lemma not_in_decls_rjump :
  forall d ds, (forall d', in_d d' ds ->
                           id_d d' <> id_d d) ->
               forall i n,
                 (forall d', in_d d' (ds [i] rjump_ds n) ->
                             id_d d' <> id_d (d [i] rjump_d n)).
Proof.
  intros.
  intros Hcontra.
  apply in_d_rjump_converse with (i:=i)(n:=n)(ds':=ds) in H0; auto.
  destruct H0 as [d'' Ha];
    destruct Ha as [Ha Hb]; subst.
  repeat rewrite <- id_d_rjump in Hcontra.
  apply H in Ha.
  rewrite Hcontra in Ha;
    contradiction Ha; auto.
Qed.

Lemma unbound_rjump_mutind :
  (forall n t, n unbound_t t ->
               forall i m, (n [i] rjump_n m) unbound_t (t [i] rjump_t m)) /\
  (forall n s, n unbound_s s ->
               forall i m, (n [i] rjump_n m) unbound_s (s [i] rjump_s m)) /\
  (forall n ss, n unbound_ss ss ->
                forall i m, (n [i] rjump_n m) unbound_ss (ss [i] rjump_ss m)) /\
  (forall n e, n unbound_e e ->
               forall i m, (n [i] rjump_n m) unbound_e (e [i] rjump_e m)) /\
  (forall n d, n unbound_d d ->
               forall i m, (n [i] rjump_n m) unbound_d (d [i] rjump_d m)) /\
  (forall n ds, n unbound_ds ds ->
                forall i m, (n [i] rjump_n m) unbound_ds (ds [i] rjump_ds m)).
Proof.
  apply unbound_mutind; intros; crush.

  destruct v as [r|r]; simpl; auto.
  inversion u; subst.
  unfold right_jump_n.
  destruct (le_gt_dec i n) as [Heq1|Heq1];
    [rewrite (leb_correct i n Heq1)
    |rewrite (leb_correct_conv n i Heq1)];
    (destruct (le_gt_dec i r) as [Heq2|Heq2];
     [rewrite (leb_correct i r Heq2)
     |rewrite (leb_correct_conv r i Heq2)]); crush.
Qed.

Lemma unbound_rjump_type :
  (forall n t, n unbound_t t ->
               forall i m, (n [i] rjump_n m) unbound_t (t [i] rjump_t m)).
Proof.
  destruct unbound_rjump_mutind; crush.
Qed.

Lemma unbound_rjump_decl_ty :
  (forall n s, n unbound_s s ->
               forall i m, (n [i] rjump_n m) unbound_s (s [i] rjump_s m)).
Proof.
  destruct unbound_rjump_mutind; crush.
Qed.

Lemma unbound_rjump_decl_tys :
  (forall n ss, n unbound_ss ss ->
                forall i m, (n [i] rjump_n m) unbound_ss (ss [i] rjump_ss m)).
Proof.
  destruct unbound_rjump_mutind; crush.
Qed.

Lemma unbound_rjump_exp :
  (forall n e, n unbound_e e ->
               forall i m, (n [i] rjump_n m) unbound_e (e [i] rjump_e m)).
Proof.
  destruct unbound_rjump_mutind; crush.
Qed.

Lemma unbound_rjump_decl :
  (forall n d, n unbound_d d ->
               forall i m, (n [i] rjump_n m) unbound_d (d [i] rjump_d m)).
Proof.
  destruct unbound_rjump_mutind; crush.
Qed.

Lemma unbound_rjump_decls :
  (forall n ds, n unbound_ds ds ->
                forall i m, (n [i] rjump_n m) unbound_ds (ds [i] rjump_ds m)).
Proof.
  destruct unbound_rjump_mutind; crush.
Qed.


Lemma lt_n_Sn_mutind :
  (forall t n, lt_t t n ->
               lt_t t (S n)) /\
  (forall s n, lt_s s n ->
               lt_s s (S n)) /\
  (forall ss n, lt_ss ss n ->
                lt_ss ss (S n)) /\
  (forall e n, lt_e e n ->
               lt_e e (S n)) /\
  (forall d n, lt_d d n ->
               lt_d d (S n)) /\
  (forall ds n, lt_ds ds n ->
                lt_ds ds (S n)).
Proof.
  apply lt_mutind; intros; auto.
Qed.

Lemma lt_n_Sn_type :
  (forall t n, lt_t t n ->
               lt_t t (S n)).
Proof.
  destruct lt_n_Sn_mutind; crush.
Qed.

Lemma lt_n_Sn_decl_ty :
  (forall s n, lt_s s n ->
               lt_s s (S n)).
Proof.
  destruct lt_n_Sn_mutind; crush.
Qed.

Lemma lt_n_Sn_decl_tys :
  (forall ss n, lt_ss ss n ->
                lt_ss ss (S n)).
Proof.
  destruct lt_n_Sn_mutind; crush.
Qed.

Lemma lt_n_Sn_exp :
  (forall e n, lt_e e n ->
               lt_e e (S n)).
Proof.
  destruct lt_n_Sn_mutind; crush.
Qed.

Lemma lt_n_Sn_decl :
  (forall d n, lt_d d n ->
               lt_d d (S n)).
Proof.
  destruct lt_n_Sn_mutind; crush.
Qed.

Lemma lt_n_Sn_decls :
  (forall ds n, lt_ds ds n ->
                lt_ds ds (S n)).
Proof.
  destruct lt_n_Sn_mutind; crush.
Qed.

Lemma lt_n_ge_mutind :
  (forall t n, lt_t t n ->
          forall m, n <= m ->
               lt_t t m) /\
  (forall s n, lt_s s n ->
          forall m, n <= m ->
               lt_s s m) /\
  (forall ss n, lt_ss ss n ->
           forall m, n <= m ->
                lt_ss ss m) /\
  (forall e n, lt_e e n ->
          forall m, n <= m ->
               lt_e e m) /\
  (forall d n, lt_d d n ->
          forall m, n <= m ->
               lt_d d m) /\
  (forall ds n, lt_ds ds n ->
           forall m, n <= m ->
                lt_ds ds m).
Proof.
  apply lt_mutind; intros; crush.
Qed.

Lemma lt_n_ge_type :
  (forall t n, lt_t t n ->
          forall m, n <= m ->
               lt_t t m).
Proof.
  destruct lt_n_ge_mutind; crush.
Qed.

Lemma lt_n_ge_decl_ty :
  (forall s n, lt_s s n ->
          forall m, n <= m ->
               lt_s s m).
Proof.
  destruct lt_n_ge_mutind; crush.
Qed.

Lemma lt_n_ge_decl_tys :
  (forall ss n, lt_ss ss n ->
           forall m, n <= m ->
                lt_ss ss m).
Proof.
  destruct lt_n_ge_mutind; crush.
Qed.

Lemma lt_n_ge_exp :
  (forall e n, lt_e e n ->
          forall m, n <= m ->
               lt_e e m).
Proof.
  destruct lt_n_ge_mutind; crush.
Qed.

Lemma lt_n_ge_decl :
  (forall d n, lt_d d n ->
          forall m, n <= m ->
               lt_d d m).
Proof.
  destruct lt_n_ge_mutind; crush.
Qed.

Lemma lt_n_ge_decls :
  (forall ds n, lt_ds ds n ->
           forall m, n <= m ->
                lt_ds ds m).
Proof.
  destruct lt_n_ge_mutind; crush.
Qed.

Lemma lt_n_ge_ctx :
  forall G n, lt_ctx G n ->
         forall m, n <= m ->
              lt_ctx G m.
Proof.
  intros; intros t Hin.
  apply lt_n_ge_type with (n:=n);
    auto.
Qed.

Lemma lt_n_ge_env :
  forall G n, lt_env G n ->
         forall m, n <= m ->
              lt_env G m.
Proof.
  intros G n Hlt; induction Hlt; intros; auto.

  destruct m as [|m'];
    [inversion H0|].
  apply lt_cons.
  apply lt_n_ge_type with (n:=n); crush.
  apply IHHlt; crush.
Qed.

Lemma lt_rjump_mutind :
  (forall t i, lt_t t i ->
               forall n, (t [i] rjump_t n) = t) /\
  (forall s i, lt_s s i ->
               forall n, (s [i] rjump_s n) = s) /\
  (forall ss i, lt_ss ss i ->
                forall n, (ss [i] rjump_ss n) = ss) /\
  (forall e i, lt_e e i ->
               forall n, (e [i] rjump_e n) = e) /\
  (forall d i, lt_d d i ->
               forall n, (d [i] rjump_d n) = d) /\
  (forall ds i, lt_ds ds i ->
                forall n, (ds [i] rjump_ds n) = ds).
Proof.
  apply lt_mutind; intros; crush.

  unfold right_jump_n;
    rewrite leb_correct_conv; auto.
Qed.

Lemma lt_rjump_type :
  (forall t i, lt_t t i ->
               forall n, (t [i] rjump_t n) = t).
Proof.
  destruct lt_rjump_mutind; crush.
Qed.

Lemma lt_rjump_decl_ty :
  (forall s i, lt_s s i ->
               forall n, (s [i] rjump_s n) = s).
Proof.
  destruct lt_rjump_mutind; crush.
Qed.


Lemma lt_rjump_decl_tys :
  (forall ss i, lt_ss ss i ->
                forall n, (ss [i] rjump_ss n) = ss).
Proof.
  destruct lt_rjump_mutind; crush.
Qed.


Lemma lt_rjump_exp :
  (forall e i, lt_e e i ->
               forall n, (e [i] rjump_e n) = e).
Proof.
  destruct lt_rjump_mutind; crush.
Qed.


Lemma lt_rjump_decl :
  (forall d i, lt_d d i ->
               forall n, (d [i] rjump_d n) = d).
Proof.
  destruct lt_rjump_mutind; crush.
Qed.


Lemma lt_rjump_decls :
  (forall ds i, lt_ds ds i ->
                forall n, (ds [i] rjump_ds n) = ds).
Proof.
  destruct lt_rjump_mutind; crush.
Qed.

Lemma lt_rjump_ctx :
  forall G i, lt_ctx G i ->
         forall n, (G [i] rjump_env n) = G.
Proof.
  intro G; induction G as [|t' G']; intros; simpl; auto.

  rewrite lt_rjump_type; [|apply H; apply in_eq].
  rewrite IHG'; auto.

  intros t Hin; apply H; crush.
Qed.

Lemma lt_env_implies_lt_ctx :
  forall G i, lt_env G i ->
         lt_ctx G i.
Proof.
  intro G; induction G as [|t G']; intros;
    intros t' Hin; [inversion Hin|].

  inversion Hin; subst.
  inversion H; subst.
  apply lt_n_ge_type with (n:=n); crush.
  
  inversion H; subst.
  apply IHG' in H5.
  apply lt_n_ge_type with (n:=n); auto.
Qed.

Lemma lt_rjump_env :
  forall G i, lt_env G i ->
         forall n, (G [i] rjump_env n) = G.
Proof.
  intros.
  apply lt_rjump_ctx;
    apply lt_env_implies_lt_ctx; auto.
Qed.

Lemma lt_unbound_S_n_mutind :
  (forall n t, n unbound_t t ->
               lt_t t (S n) ->
               lt_t t n) /\
  (forall n s, n unbound_s s ->
               lt_s s (S n) ->
               lt_s s n) /\
  (forall n ss, n unbound_ss ss ->
                lt_ss ss (S n) ->
                lt_ss ss n) /\
  (forall n e, n unbound_e e ->
               lt_e e (S n) ->
               lt_e e n) /\
  (forall n d, n unbound_d d ->
               lt_d d (S n) ->
               lt_d d n) /\
  (forall n ds, n unbound_ds ds ->
                lt_ds ds (S n) ->
                lt_ds ds n).
Proof.
  apply unbound_mutind; intros; auto;
    try solve
        [try (inversion H0);
         try (inversion H1);
         try (inversion H2);
         try (crush)].

  inversion H; subst;
    auto.
  inversion u; subst; crush.
Qed.

Lemma lt_unbound_S_n_type :
  (forall n t, n unbound_t t ->
               lt_t t (S n) ->
               lt_t t n).
Proof.
  destruct lt_unbound_S_n_mutind; crush.
Qed.

Lemma lt_unbound_S_n_decl_ty :
  (forall n s, n unbound_s s ->
               lt_s s (S n) ->
               lt_s s n).
Proof.
  destruct lt_unbound_S_n_mutind; crush.
Qed.

Lemma lt_unbound_S_n_decl_tys :
  (forall n ss, n unbound_ss ss ->
                lt_ss ss (S n) ->
                lt_ss ss n).
Proof.
  destruct lt_unbound_S_n_mutind; crush.
Qed.

Lemma lt_unbound_S_n_exp :
  (forall n e, n unbound_e e ->
               lt_e e (S n) ->
               lt_e e n).
Proof.
  destruct lt_unbound_S_n_mutind; crush.
Qed.

Lemma lt_unbound_S_n_decl :
  (forall n d, n unbound_d d ->
               lt_d d (S n) ->
               lt_d d n).
Proof.
  destruct lt_unbound_S_n_mutind; crush.
Qed.

Lemma lt_unbound_S_n_decls :
  (forall n ds, n unbound_ds ds ->
                lt_ds ds (S n) ->
                lt_ds ds n).
Proof.
  destruct lt_unbound_S_n_mutind; crush.
Qed.

Lemma lt_subst_components_mutind :
  (forall t n, lt_t t n ->
               forall p m t', t = ([p /t m] t') ->
                              lt_t t' n) /\
  (forall s n, lt_s s n ->
               forall p m s', s = ([p /s m] s') ->
                              lt_s s' n) /\
  (forall ss n, lt_ss ss n ->
                forall p m ss', ss = ([p /ss m] ss') ->
                                lt_ss ss' n) /\
  (forall e n, lt_e e n ->
               forall p m e', e = ([p /e m] e') ->
                              lt_e e' n) /\
  (forall d n, lt_d d n ->
               forall p m d', d = ([p /d m] d') ->
                              lt_d d' n) /\
  (forall ds n, lt_ds ds n ->
                forall p m ds', ds = ([p /ds m] ds') ->
                                lt_ds ds' n).
Proof.
  apply lt_mutind; intros;
    try solve [try (destruct t');
               try (destruct s');
               try (destruct ss');
               try (destruct d');
               try (destruct ds');
               try (simpl in H; inversion H);
               try (simpl in H0; inversion H0);
               try (simpl in H1; inversion H1);
               eauto];
    try solve [destruct e';
               try (simpl in H; inversion H);
               try (simpl in H0; inversion H0);
               try (simpl in H1; inversion H1);
               try (simpl in H2; inversion H2);
               eauto;
               destruct v; auto;
               try (inversion H);
               try (inversion H0);
               try (inversion H1);
               try (inversion H2);
               subst; auto].
Qed.

Lemma lt_subst_components_type :
  (forall t n, lt_t t n ->
               forall p m t', t = ([p /t m] t') ->
                              lt_t t' n).
Proof.
  destruct lt_subst_components_mutind; crush.
Qed.

Lemma lt_subst_components_decl_ty :
  (forall s n, lt_s s n ->
               forall p m s', s = ([p /s m] s') ->
                              lt_s s' n).
Proof.
  destruct lt_subst_components_mutind; crush.
Qed.

Lemma lt_subst_components_decl_tys :
  (forall ss n, lt_ss ss n ->
                forall p m ss', ss = ([p /ss m] ss') ->
                                lt_ss ss' n).
Proof.
  destruct lt_subst_components_mutind; crush.
Qed.

Lemma lt_subst_components_exp :
  (forall e n, lt_e e n ->
               forall p m e', e = ([p /e m] e') ->
                              lt_e e' n).
Proof.
  destruct lt_subst_components_mutind; crush.
Qed.

Lemma lt_subst_components_decl :
  (forall d n, lt_d d n ->
               forall p m d', d = ([p /d m] d') ->
                              lt_d d' n).
Proof.
  destruct lt_subst_components_mutind; crush.
Qed.

Lemma lt_subst_components_decls :
  (forall ds n, lt_ds ds n ->
                forall p m ds', ds = ([p /ds m] ds') ->
                                lt_ds ds' n).
Proof.
  destruct lt_subst_components_mutind; crush.
Qed.

Lemma wf_lt_mutind :
  (forall Sig G t, Sig en G vdash t wf_t ->
                   lt_t t (length G)) /\
  (forall Sig G s, Sig en G vdash s wf_s ->
                   lt_s s (length G)) /\
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
                    lt_ss ss (length G)) /\
  (forall Sig G e, Sig en G vdash e wf_e ->
                   lt_e e (length G)) /\
  (forall Sig G d, Sig en G vdash d wf_d ->
                   lt_d d (length G)) /\
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
                    lt_ds ds (length G)).
Proof.
  apply wf_mutind; crush.

  apply lt_subst_components_type with (p:=v_ Var (length G))
                                      (m:=0)(t':=t2)in H0; auto.
  apply lt_unbound_S_n_type in H0; auto.

  apply lt_subst_components_decl_tys with (p:=v_ Var (length G))
                                          (m:=0)(ss':=ss)in H; auto.
  apply lt_unbound_S_n_decl_tys in H; auto.

  apply lt_subst_components_type with (p:=v_ Var (length G))
                                      (m:=0)(t':=t2)in H1; auto.
  apply lt_unbound_S_n_type in H1; auto.
  apply lt_subst_components_exp with (p:=v_ Var (length G))
                                     (m:=0)(e':=e)in H0; auto.
  apply lt_unbound_S_n_exp in H0; auto.

  apply lt_subst_components_decls with (p:=v_ Var (length G))
                                       (m:=0)(ds':=ds)in H; auto.
  apply lt_unbound_S_n_decls in H; auto.

Qed.

Lemma wf_lt_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
                   lt_t t (length G)).
Proof.
  destruct wf_lt_mutind; crush.
Qed.

Lemma wf_lt_decl_ty :
  (forall Sig G s, Sig en G vdash s wf_s ->
                   lt_s s (length G)).
Proof.
  destruct wf_lt_mutind; crush.
Qed.

Lemma wf_lt_decl_tys :
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
                    lt_ss ss (length G)).
Proof.
  destruct wf_lt_mutind; crush.
Qed.

Lemma wf_lt_exp :
  (forall Sig G e, Sig en G vdash e wf_e ->
                   lt_e e (length G)).
Proof.
  destruct wf_lt_mutind; crush.
Qed.

Lemma wf_lt_decl :
  (forall Sig G d, Sig en G vdash d wf_d ->
                   lt_d d (length G)).
Proof.
  destruct wf_lt_mutind; crush.
Qed.

Lemma wf_lt_decls :
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
                    lt_ds ds (length G)).
Proof.
  destruct wf_lt_mutind; crush.
Qed.

Lemma wf_lt_ctx :
  forall Sig G, Sig evdash G wf_env ->
         lt_ctx G (length G).
Proof.
  intros Sig G Hwf; induction Hwf;
    intros t' Hin;
    inversion Hin; subst; simpl.
  
  apply wf_lt_type in H; apply lt_n_Sn_type; auto.

  apply lt_n_Sn_type;
    apply IHHwf; auto.
  
Qed.

Lemma wf_lt_env :
  forall Sig G, Sig evdash G wf_env ->
         lt_env G (length G).
Proof.
  intros Sig G Hwf; induction Hwf; simpl; auto.

  apply lt_cons; auto.  
  apply wf_lt_type in H; auto.
Qed.

Lemma wf_lt_store_type :
  forall Sig, Sig wf_st ->
       forall n, lt_ctx Sig n.
Proof.
  intros Sig Hwf; induction Hwf; intros;
    intros t Hin; inversion Hin; subst.

  apply lt_n_ge_type with (n:=0); [|crush].
  apply wf_lt_type in H; simpl; auto.
  apply IHHwf; auto.
Qed.

(*closed*)

Lemma closed_subst_mutind :
  (forall n t, closed_t n t ->
          forall e, ([e /t n] t) = t) /\

  (forall n s, closed_s n s ->
          forall e, ([e /s n] s) = s) /\

  (forall n ss, closed_ss n ss ->
           forall e, ([e /ss n] ss) = ss) /\

  (forall n e, closed_e n e ->
          forall e', ([e' /e n] e) = e) /\

  (forall n d, closed_d n d ->
          forall e, ([e /d n] d) = d) /\

  (forall n ds, closed_ds n ds ->
           forall e, ([e /ds n] ds) = ds).
Proof.
  apply closed_mutind;
    intros;
    auto;
    try solve [simpl;
               rewrite H;
               try rewrite H0;
               try rewrite H1;
               eauto].

  destruct x as [y|y];
    auto.

  simpl.
  inversion c; subst.
  apply Nat.eqb_neq in H1;
    rewrite H1;
    auto.
                 
Qed.

Lemma closed_subst_type :
  forall n t, closed_t n t -> forall e, ([e /t n] t) = t.
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_subst_exp :
  forall n e, closed_e n e -> forall e', ([e' /e n] e) = e.
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_subst_decls :
  forall n ds, closed_ds n ds -> forall e, ([e /ds n] ds) = ds.
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_subst_decl_tys :
  forall n ss, closed_ss n ss -> forall e, ([e /ss n] ss) = ss.
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_subst_decl_ty :
  forall n s, closed_s n s -> forall e, ([e /s n] s) = s.
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_subst_decl :
  forall n d, closed_d n d -> forall e, ([e /d n] d) = d.
Proof.
  destruct closed_subst_mutind; crush.
Qed.

Lemma closed_rjump_mutind :
  (forall n t, closed_t n t -> forall i m, closed_t n (t [i] rjump_t m)) /\
  (forall n s, closed_s n s -> forall i m, closed_s n (s [i] rjump_s m)) /\
  (forall n ss, closed_ss n ss -> forall i m, closed_ss n (ss [i] rjump_ss m)) /\
  (forall n p, closed_e n p -> forall i m, closed_e n (p [i] rjump_e m)) /\
  (forall n d, closed_d n d -> forall i m, closed_d n (d [i] rjump_d m)) /\
  (forall n ds, closed_ds n ds -> forall i m, closed_ds n (ds [i] rjump_ds m)).
Proof.
  apply closed_mutind; intros;
    try solve [crush].

  

  apply cl_var.
  destruct x; simpl; auto.
Qed.  

Lemma closed_rjump_type :
  (forall n t, closed_t n t -> forall i m, closed_t n (t [i] rjump_t m)).
Proof.
  destruct closed_rjump_mutind; auto.
Qed.

Lemma closed_rjump_decl_ty :
  (forall n s, closed_s n s -> forall i m, closed_s n (s [i] rjump_s m)).
Proof.
  destruct closed_rjump_mutind; crush.
Qed.

Lemma rjump_closed_mutind :
  (forall t n i m, closed_t n (t [i] rjump_t m) ->
                   closed_t n t) /\
  
  (forall s n i m, closed_s n (s [i] rjump_s m) ->
                   closed_s n s) /\
  
  (forall ss n i m, closed_ss n (ss [i] rjump_ss m) ->
                    closed_ss n ss) /\
  
  (forall e n i m, closed_e n (e [i] rjump_e m) ->
                   closed_e n e) /\
  
  (forall d n i m, closed_d n (d [i] rjump_d m) ->
                   closed_d n d) /\
  
  (forall ds n i m, closed_ds n (ds [i] rjump_ds m) ->
                    closed_ds n ds).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [inversion H0; eauto];
    try solve [inversion H1; eauto];
    try solve [inversion H2; eauto].

  destruct v as [r|r]; auto.
  
Qed.

Lemma rjump_closed_type :
  (forall t n i m, closed_t n (t [i] rjump_t m) ->
                   closed_t n t).
Proof.
  destruct rjump_closed_mutind; crush.
Qed.

Lemma rjump_closed_decl_ty :  
  (forall s n i m, closed_s n (s [i] rjump_s m) ->
              closed_s n s).
Proof.
  destruct rjump_closed_mutind; crush.
Qed.

Lemma rjump_closed_decl_tys :
  (forall ss n i m, closed_ss n (ss [i] rjump_ss m) ->
               closed_ss n ss).
Proof.
  destruct rjump_closed_mutind; crush.
Qed.

Lemma rjump_closed_exp :
  (forall e n i m, closed_e n (e [i] rjump_e m) ->
              closed_e n e).
Proof.
  destruct rjump_closed_mutind; crush.
Qed.

Lemma rjump_closed_decl :  
  (forall d n i m, closed_d n (d [i] rjump_d m) ->
              closed_d n d).
Proof.
  destruct rjump_closed_mutind; crush.
Qed.

Lemma rjump_closed_decls :  
  (forall ds n i m, closed_ds n (ds [i] rjump_ds m) ->
               closed_ds n ds).
Proof.
  destruct rjump_closed_mutind; crush.
Qed.

Lemma is_path_rjump :
  (forall p, is_path p ->
        forall i n, is_path (p [i] rjump_e n)).
Proof.
  intros p H; induction H; intros; simpl.
  apply isp_loc.
  apply isp_var.
  apply isp_cast; auto.
Qed.

Lemma path_typing_uniqueness :
  forall Sig G p t, Sig en G vdash p pathType t ->
             forall t', Sig en G vdash p pathType t' ->
                   t' = t.
Proof.
  intros Sig G p t Htyp;
    induction Htyp; intros t' Htyp;
      try solve [inversion Htyp; subst; rewrite H3 in H; inversion H; auto].
  inversion Htyp; auto.
Qed.



Lemma rjump_is_path :
  forall p, is_path p ->
       forall i n, is_path (p [i] rjump_e n).
Proof.
  intros p Hpath;
    induction Hpath; crush.
Qed.


Lemma closed_subst_neq_mutind :
  (forall n t, closed_t n t ->
          forall p m t', t = ([p /t m] t') ->
                    n <> m ->
                    closed_t n t') /\
  (forall n s, closed_s n s ->
          forall p m s', s = ([p /s m] s') ->
                    n <> m ->
                    closed_s n s') /\
  (forall n ss, closed_ss n ss ->
           forall p m ss', ss = ([p /ss m] ss') ->
                      n <> m ->
                      closed_ss n ss') /\
  (forall n e, closed_e n e ->
          forall p m e', e = ([p /e m] e') ->
                    n <> m ->
                    closed_e n e') /\
  (forall n d, closed_d n d ->
          forall p m d', d = ([p /d m] d') ->
                    n <> m ->
                    closed_d n d') /\
  (forall n ds, closed_ds n ds ->
           forall p m ds', ds = ([p /ds m] ds') ->
                      n <> m ->
                      closed_ds n ds').
Proof.
  apply closed_mutind; intros.

  (*top*)
  destruct t'; simpl in H; inversion H; subst; auto.
  
  (*bot*)
  destruct t'; simpl in H; inversion H; subst; auto.

  (*sel*)
  destruct t'; simpl in H0; inversion H0; subst; auto.
  apply cl_sel.
  apply H with (p:=p0)(m0:=m); auto.

  (*arr*)
  destruct t'; simpl in H1; inversion H1; subst; auto.
  apply cl_arr.
  apply H with (p0:= p)(m0:=m); auto.
  apply H0 with (p0:= p raise_e 0)(m0:=S m); auto.

  (*str*)
  destruct t'; simpl in H0; inversion H0; subst; auto.
  apply cl_str.
  apply H with (p0:=p raise_e 0)(m0:=S m); auto.

  (*dt_upper*)
  destruct s'; simpl in H0; inversion H0; subst; auto.
  apply cls_upper;
    eapply H; auto.

  (*dt_lower*)
  destruct s'; simpl in H0; inversion H0; subst; auto.
  apply cls_lower;
    eapply H; auto.

  (*dt_equal*)
  destruct s'; simpl in H0; inversion H0; subst; auto.
  apply cls_equal;
    eapply H; auto.

  (*dt_val*)
  destruct s'; simpl in H0; inversion H0; subst; auto.
  apply cls_value;
    eapply H; auto.

  (*dt_nil*)
  destruct ss'; simpl in H; inversion H; subst; auto.

  (*dt_con*)
  destruct ss'; simpl in H1; inversion H1; subst; auto.
  apply cls_cons;
    [eapply H; auto
    |eapply H0; auto].
  
  (*var*)
  destruct e'; simpl in H; inversion H; subst; auto.
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r);
    [subst|].
  rewrite <- beq_nat_refl in H; inversion H; subst;
    auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H; inversion H; subst; auto.

  (*loc*)
  destruct e'; simpl in H; inversion H; subst; auto.
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r); subst; auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H; inversion H; subst; auto.

  (*cast*)
  destruct e'; simpl in H1; inversion H1; subst; auto.
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r); subst; auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H1; inversion H1; subst; auto.
  apply cl_cast;
    [eapply H; auto
    |eapply H0; auto].

  (*new*)
  destruct e'; simpl in H0; inversion H0; subst; auto.
  apply cl_new;
    eapply H; auto.
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r); subst; auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H0; inversion H0; subst; auto.
  
  (*app*)
  destruct e'; simpl in H1; inversion H1; subst; auto.
  apply cl_app;
    [eapply H; auto
    |eapply H0; auto].
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r); subst; auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H1; inversion H1; subst; auto.

  (*acc*)
  destruct e'; simpl in H0; inversion H0; subst; auto.
  apply cl_acc; eauto.
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r); subst; auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H0; inversion H0; subst; auto.
  
  (*fn*)
  destruct e'; simpl in H2; inversion H2; subst; auto.
  apply cl_fn; eauto.
  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec m r); subst; auto.
  apply Nat.eqb_neq in n0;
    rewrite n0 in H2; inversion H2; subst; auto.

  (*equals decl*)
  destruct d'; simpl in H0; inversion H0; subst; eauto.

  (*val decl*)
  destruct d'; simpl in H1; inversion H1; subst; eauto.

  (*d_nil*)
  destruct ds'; simpl in H; inversion H; subst; auto.

  (*d_con*)
  destruct ds'; simpl in H1; inversion H1; subst; eauto.
  
Qed.

Lemma closed_subst_neq_type :
  (forall n t, closed_t n t ->
               forall p m t', t = ([p /t m] t') ->
                              n <> m ->
                              closed_t n t').
Proof.
  destruct closed_subst_neq_mutind; crush.
Qed.


Lemma closed_subst_neq_decl_ty :
  (forall n s, closed_s n s ->
               forall p m s', s = ([p /s m] s') ->
                              n <> m ->
                              closed_s n s').
Proof.
  destruct closed_subst_neq_mutind; crush.
Qed.


Lemma closed_subst_neq_decl_tys :
  (forall n ss, closed_ss n ss ->
                forall p m ss', ss = ([p /ss m] ss') ->
                                n <> m ->
                                closed_ss n ss').
Proof.
  destruct closed_subst_neq_mutind; crush.
Qed.

Lemma closed_subst_neq_exp :
  (forall n e, closed_e n e ->
               forall p m e', e = ([p /e m] e') ->
                              n <> m ->
                              closed_e n e').
Proof.
  destruct closed_subst_neq_mutind; crush.
Qed.

Lemma closed_subst_neq_decls :
  (forall n ds, closed_ds n ds ->
                forall p m ds', ds = ([p /ds m] ds') ->
                                n <> m ->
                                closed_ds n ds').
Proof.
  destruct closed_subst_neq_mutind; crush.
Qed.

Lemma subst_nil :
  forall p n, ([p /env n] nil) = nil.
Proof.
  intros; unfold subst_env; simpl; auto.
Qed.

Hint Rewrite subst_nil.

Lemma subst_environment_app_distr :
  forall G1 G2 p n, subst_environment n p (G1 ++ G2) =
                    (subst_environment n p G1)++ (subst_environment (n + length G1) p G2).
Proof.
  intro G1; induction G1 as [|t G]; intros; simpl.

  rewrite plus_0_r; auto.

  rewrite IHG.
  rewrite plus_Snm_nSm; auto.
Qed.

Lemma subst_cons :
  forall G p n t, ([p /env n] (t::G)) = ([p /t n + length G] t)::([p /env n] G).
Proof.
  intro G; induction G as [|t' G']; intros; simpl.

  rewrite subst_nil, plus_0_r; auto.

  unfold subst_env.
  simpl.
  repeat rewrite subst_environment_app_distr.
  repeat rewrite rev_app_distr.
  simpl.
  rewrite app_length; simpl.
  repeat rewrite rev_length.
  rewrite Nat.add_1_r; auto.
Qed.

Lemma subst_length :
  forall G p n, length ([p /env n] G) = length G.
Proof.

  intro G; induction G as [|t' G']; intros; auto.

  rewrite subst_cons; simpl; auto.

Qed.



Lemma subst_synsize_mutind :
  (forall t e n, synsize_t ([e /t n] t) >= synsize_t t) /\
  (forall s e n, synsize_s ([e /s n] s) >= synsize_s s) /\
  (forall ss e n, synsize_ss ([e /ss n] ss) >= synsize_ss ss) /\
  (forall e' e n, synsize_e ([e /e n] e') >= synsize_e e') /\
  (forall d e n, synsize_d ([e /d n] d) >= synsize_d d) /\
  (forall ds e n, synsize_ds ([e /ds n] ds) >= synsize_ds ds).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto;
    try solve [try apply le_n_S;
               repeat apply plus_le_compat;
               try apply H;
               try apply H0;
               try apply H1;
               crush].
Qed.

Lemma synsize_raise_mutind :
  (forall t n, synsize_t (t raise_t n) = synsize_t t) /\
  (forall s n, synsize_s (s raise_s n) = synsize_s s) /\
  (forall ss n, synsize_ss (ss raise_ss n) = synsize_ss ss) /\
  (forall e n, synsize_e (e raise_e n) = synsize_e e) /\
  (forall d n, synsize_d (d raise_d n) = synsize_d d) /\
  (forall ds n, synsize_ds (ds raise_ds n) = synsize_ds ds).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto.
Qed.

Lemma synsize_raise_type :
  (forall t n, synsize_t (t raise_t n) = synsize_t t).
Proof.
  destruct synsize_raise_mutind; crush.
Qed.

Hint Rewrite synsize_raise_type.

Lemma synsize_raise_decl_ty :
  (forall s n, synsize_s (s raise_s n) = synsize_s s).
Proof.
  destruct synsize_raise_mutind; crush.
Qed.

Hint Rewrite synsize_raise_decl_ty.

Lemma synsize_raise_decl_tys :
  (forall ss n, synsize_ss (ss raise_ss n) = synsize_ss ss).
Proof.
  destruct synsize_raise_mutind; crush.
Qed.

Hint Rewrite synsize_raise_decl_tys.

Lemma synsize_raise_exp :
  (forall e n, synsize_e (e raise_e n) = synsize_e e).
Proof.
  destruct synsize_raise_mutind; crush.
Qed.

Hint Rewrite synsize_raise_exp.

Lemma synsize_raise_decl :
  (forall d n, synsize_d (d raise_d n) = synsize_d d).
Proof.
  destruct synsize_raise_mutind; crush.
Qed.

Hint Rewrite synsize_raise_decl.

Lemma synsize_raise_decls :
  (forall ds n, synsize_ds (ds raise_ds n) = synsize_ds ds).
Proof.
  destruct synsize_raise_mutind; crush.
Qed.

Hint Rewrite synsize_raise_decls.



Lemma synsize_raise_subst_mutind :
  (forall t e n m, synsize_t ([e raise_e m /t n] t) = synsize_t ([e /t n] t)) /\
  (forall s e n m, synsize_s ([e raise_e m /s n] s) = synsize_s ([e /s n] s)) /\
  (forall ss e n m, synsize_ss ([e raise_e m /ss n] ss) = synsize_ss ([e /ss n] ss)) /\
  (forall e' e n m, synsize_e ([e raise_e m /e n] e') = synsize_e ([e /e n] e')) /\
  (forall d e n m, synsize_d ([e raise_e m /d n] d) = synsize_d ([e /d n] d)) /\
  (forall ds e n m, synsize_ds ([e raise_e m /ds n] ds) = synsize_ds ([e /ds n] ds)).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto;
    try solve [repeat rewrite H;
               repeat rewrite H0;
               repeat rewrite H1;
               auto].

  destruct v as [r|r]; auto.
  destruct (Nat.eq_dec n r) as [|Hneq];
    [subst; rewrite <- beq_nat_refl; rewrite synsize_raise_exp; auto
    |apply Nat.eqb_neq in Hneq;
     rewrite Hneq; auto].
Qed.

Lemma synsize_raise_subst_type :
  (forall t e n m, synsize_t ([e raise_e m /t n] t) = synsize_t ([e /t n] t)).
Proof.
  destruct synsize_raise_subst_mutind; crush.
Qed.

Hint Rewrite synsize_raise_subst_type.

Lemma synsize_raise_subst_decl_ty :
  (forall s e n m, synsize_s ([e raise_e m /s n] s) = synsize_s ([e /s n] s)).
Proof.
  destruct synsize_raise_subst_mutind; crush.
Qed.

Hint Rewrite synsize_raise_subst_decl_ty.

Lemma synsize_raise_subst_decl_tys :
  (forall ss e n m, synsize_ss ([e raise_e m /ss n] ss) = synsize_ss ([e /ss n] ss)).
Proof.
  destruct synsize_raise_subst_mutind; crush.
Qed.

Hint Rewrite synsize_raise_subst_decl_tys.

Lemma synsize_raise_subst_exp :
  (forall e' e n m, synsize_e ([e raise_e m /e n] e') = synsize_e ([e /e n] e')).
Proof.
  destruct synsize_raise_subst_mutind; crush.
Qed.

Hint Rewrite synsize_raise_subst_exp.

Lemma synsize_raise_subst_decl :
  (forall d e n m, synsize_d ([e raise_e m /d n] d) = synsize_d ([e /d n] d)).
Proof.
  destruct synsize_raise_subst_mutind; crush.
Qed.

Hint Rewrite synsize_raise_subst_decl.

Lemma synsize_raise_subst_decls :
  (forall ds e n m, synsize_ds ([e raise_e m /ds n] ds) = synsize_ds ([e /ds n] ds)).
Proof.
  destruct synsize_raise_subst_mutind; crush.
Qed.

Hint Rewrite synsize_raise_subst_decls.

Lemma subst_synsize_alt_mutind :
  (forall t e n, synsize_t ([e /t n] t) >= synsize_e e \/ closed_t n t) /\
  (forall s e n, synsize_s ([e /s n] s) >= synsize_e e \/ closed_s n s) /\
  (forall ss e n, synsize_ss ([e /ss n] ss) >= synsize_e e \/ closed_ss n ss) /\
  (forall e' e n, (synsize_e ([e /e n] e') > synsize_e e) \/ closed_e n e' \/ (e' = a_ n)) /\
  (forall d e n, synsize_d ([e /d n] d) >= synsize_e e \/ closed_d n d) /\
  (forall ds e n, synsize_ds ([e /ds n] ds) >= synsize_e e \/ closed_ds n ds).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto;
    try solve [ try (edestruct H; [left|right; eauto]);
                try (edestruct H0; [left|right; eauto]);
                try apply le_S;
                try rewrite synsize_raise_subst_decl_tys; eauto].
  
  (*sel*)
  destruct (H e0 n) as [|Ha];
    [left; apply le_S; crush
    |destruct Ha as [Ha|Ha];
     [right; eauto
     |subst; simpl; rewrite <- beq_nat_refl; crush]].

  (*arr*)
  destruct (H e n), (H0 (e raise_e 0) (S n)); [left|left|left|right]; eauto;
    try solve [apply le_S;
               apply le_plus_trans;
               auto].
  rewrite plus_comm.
  apply le_S.
  apply le_plus_trans.
  crush.

  (*t-con*)
  destruct (H e n), (H0 e n); [left|left|left|right]; eauto;
    try solve [apply le_S;
               apply le_plus_trans;
               auto].
  rewrite plus_comm.
  apply le_S.
  apply le_plus_trans.
  crush.

  (*new*)
  destruct (H (e raise_e 0)  (S n)); [left|right]; eauto.
  rewrite synsize_raise_subst_decls in *.
  rewrite synsize_raise_exp in H0; crush.
  
  (*app*)
  destruct (H e1 n) as [Ha|Ha], (H0 e1 n) as [Hb|Hb];
    [crush
    |destruct Hb as [Hb|Hb]; crush
    |destruct Ha as [Ha|Ha]; crush
    |destruct Ha as [Ha|Ha], Hb as [Hb|Hb];
     [crush| | |]];
    subst; simpl; rewrite <- beq_nat_refl; crush.

  (*fn*)
  destruct (H e0 n);
    [left; crush
    |destruct (H0 (e0 raise_e 0) (S n)) as [|Ha];
     [left; crush
     |destruct (H1 (e0 raise_e 0) (S n));
      [left; crush|]]].
  destruct Ha as [Ha|Ha];
    [crush|subst; simpl; rewrite <- beq_nat_refl].
  rewrite synsize_raise_exp; crush.

  (*acc*)
  destruct (H e0 n) as [|Ha];
    [crush
    |destruct Ha;
     [crush|subst]].
  simpl; rewrite <- beq_nat_refl; crush.

  (*var*)
  destruct v as [r|r];
    [crush|destruct (Nat.eq_dec n r); subst; auto].

  (*cast*)
  destruct (H e0 n) as [Ha|Ha];
    [left; crush
    |destruct (H0 e0 n) as [Hb|Hb];
     [left; crush|]].
  destruct Ha as [Ha|Ha];
    [right; left; crush|subst].
  simpl; rewrite <- beq_nat_refl; left; crush.

  (*e value*)
  destruct (H e0 n) as [|Ha];
    [left; crush|].
  destruct (H0 e0 n) as [|Hb];
    [left; crush|].
  destruct Ha; [right; crush|subst].
  simpl; rewrite <- beq_nat_refl; crush.

  (*e con*)
  destruct (H e n) as [|Ha];
    [left; crush|].
  destruct (H0 e n) as [|Hb];
    [left; crush|crush].
Qed.

Lemma subst_synsize_alt_exp :
  (forall e' e n, (synsize_e ([e /e n] e') > synsize_e e) \/ closed_e n e' \/ (e' = a_ n)).
Proof.
  destruct subst_synsize_alt_mutind; crush.
Qed.

Lemma subst_notin_itself :
  (forall e n e', ([e /e n] e') = e ->
                  e notin_e e' ->
                  e' = (a_ n)).
Proof.
  intros.
  destruct (subst_synsize_alt_exp e' e n) as [Ha|Ha];
    [rewrite H in Ha; crush
    |destruct Ha as [Ha|Ha];
     [|inversion Ha]]; auto.
  rewrite closed_subst_exp in H;
    subst; inversion H0; crush.
Qed.

Lemma subst_equality_mutind :
  (forall t1 t2 p n, ([p /t n] t1) = ([p /t n] t2) ->
                     p notin_t t1 ->
                     p notin_t t2 ->
                     t1 = t2) /\
  (forall s1 s2 p n, ([p /s n] s1) = ([p /s n] s2) ->
                     p notin_s s1 ->
                     p notin_s s2 ->
                     s1 = s2) /\
  (forall ss1 ss2 p n, ([p /ss n] ss1) = ([p /ss n] ss2) ->
                       p notin_ss ss1 ->
                       p notin_ss ss2 ->
                       ss1 = ss2) /\
  (forall e1 e2 p n, ([p /e n] e1) = ([p /e n] e2) ->
                     p notin_e e1 ->
                     p notin_e e2 ->
                     e1 = e2) /\
  (forall d1 d2 p n, ([p /d n] d1) = ([p /d n] d2) ->
                     p notin_d d1 ->
                     p notin_d d2 ->
                     d1 = d2) /\
  (forall ds1 ds2 p n, ([p /ds n] ds1) = ([p /ds n] ds2) ->
                       p notin_ds ds1 ->
                       p notin_ds ds2 ->
                       ds1 = ds2).
Proof.
  apply type_exp_mutind; intros; simpl;
    try solve [try (destruct t2);
               try (destruct s2);
               try (destruct ss2);
               try (destruct d2);
               try (destruct ds2);
               try (simpl in H);
               try (simpl in H0);
               try (simpl in H1);
               try (inversion H);
               try (inversion H0);
               try (inversion H1);
               try (erewrite H; eauto);
               try (erewrite H0; eauto);
               try (inversion H1);
               try (inversion H2);
               try (inversion H3);
               auto].

  (*new*)
  destruct e2;
    try solve [simpl in H0;
               inversion H0; subst].
  simpl in H0;
    inversion H0; subst.
  erewrite H; eauto.
  inversion H1; auto.
  inversion H2; auto.

  remember (new d) as e;
    simpl in H0.
  destruct v as [|r]; [subst; inversion H0|].
  destruct (Nat.eq_dec n r) as [|Heq];
    [subst; rewrite <- beq_nat_refl in H0
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H0;
     subst; inversion H0].
  apply subst_notin_itself in H0;
    [inversion H0|auto].

  (*app*)
  destruct e2;
    try solve [simpl in H1;
               inversion H1; subst].
  simpl in H1;
    inversion H1; subst.
  erewrite H, H0;
    try solve [inversion H2;
               inversion H3;
               eauto].

  remember (e_app e e0) as e';
    simpl in H1.
  destruct v as [|r]; [subst; inversion H1|].
  destruct (Nat.eq_dec n r) as [|Heq];
    [subst; rewrite <- beq_nat_refl in H1
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H1;
     subst; inversion H1].
  apply subst_notin_itself in H1;
    [inversion H1|auto].

  (*fn*)
  destruct e2;
    try solve [simpl in H2;
               inversion H2; subst].
  simpl in H2;
    inversion H2; subst.
  erewrite H, H0, H1;
    try solve [inversion H3;
               inversion H4;
               eauto].

  remember (fn t in_exp e off t0) as e';
    simpl in H2.
  destruct v as [|r]; [subst; inversion H2|].
  destruct (Nat.eq_dec n r) as [|Heq];
    [subst; rewrite <- beq_nat_refl in H2
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H2;
     subst; inversion H2].
  apply subst_notin_itself in H2;
    [inversion H2|auto].

  (*acc*)
  destruct e2;
    try solve [simpl in H0;
               inversion H0; subst].
  simpl in H0;
    inversion H0; subst.
  erewrite H;
    try solve [inversion H1;
               inversion H2;
               eauto].

  remember (e_acc e l) as e';
    simpl in H0.
  destruct v as [|r]; [subst; inversion H0|].
  destruct (Nat.eq_dec n r) as [|Heq];
    [subst; rewrite <- beq_nat_refl in H0
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H0;
     subst; inversion H0].
  apply subst_notin_itself in H0;
    [inversion H0|auto].

  (*var*)
  remember e2 as e'.
  destruct e2;
    try solve [simpl in H;
               inversion H; subst];

    try solve [destruct v as [|r]; [subst; inversion H|];
               destruct (Nat.eq_dec n r) as [Heq|Heq];
               [rewrite Heq in H; simpl in H; rewrite <- beq_nat_refl in H
               |simpl in H;
                apply Nat.eqb_neq in Heq;
                rewrite Heq in H;
                subst; inversion H];
               symmetry in H; apply subst_notin_itself in H;
               [subst; inversion H|auto]];
    subst.
  destruct v as [r1|r1]; destruct v0 as [r2|r2]; simpl in H; auto.
  destruct (Nat.eq_dec n r2) as [Heq1|Heq1];
    [subst; rewrite <- beq_nat_refl in H; subst; inversion H0; crush
    |apply Nat.eqb_neq in Heq1;
     rewrite Heq1 in H; inversion H].
  destruct (Nat.eq_dec n r1) as [Heq1|Heq1];
    [subst; rewrite <- beq_nat_refl in H;
     subst; inversion H1; crush
    |apply Nat.eqb_neq in Heq1;
     rewrite Heq1 in H; inversion H].
  destruct (Nat.eq_dec n r1) as [Heq1|Heq1];
    [subst; rewrite <- beq_nat_refl in H;
     subst; inversion H1; crush
    |apply Nat.eqb_neq in Heq1;
     rewrite Heq1 in H; inversion H].
  destruct (Nat.eq_dec r1 r2) as [Heq1|Heq1];
    [subst; auto
    |apply Nat.eqb_neq in Heq1;
     rewrite Heq1 in H; crush].
  destruct (Nat.eq_dec n r2) as [Heq2|Heq2];
    [subst; rewrite <- beq_nat_refl in H; inversion H0; crush
    |apply Nat.eqb_neq in Heq2;
     rewrite Heq2 in H; crush].

  (*loc*)
  simpl in *.
  destruct e2; 
    try solve [simpl in H;
               inversion H; subst].
  simpl in H;
    inversion H; subst.

  destruct v as [|r]; [subst; inversion H|].
  destruct (Nat.eq_dec n0 r) as [|Heq];
    [subst; rewrite <- beq_nat_refl in H
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H;
     subst; inversion H].
  inversion H0; crush.
  simpl in H; auto.

  (*cast*)
  destruct e2;
    try solve [simpl in H1;
               inversion H1; subst].

  remember (e cast t) as e';
    simpl in H1.
  destruct v as [|r]; [subst; inversion H1|].
  destruct (Nat.eq_dec n r) as [|Heq];
    [subst; rewrite <- beq_nat_refl in H1
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H1;
     subst; inversion H1].
  apply subst_notin_itself in H1;
    [inversion H1|auto].
  
  simpl in H1;
    inversion H1; subst.
  erewrite H, H0;
    try solve [inversion H2;
               inversion H3;
               eauto].
Qed.

Lemma subst_equality_type :
  (forall t1 t2 p n, ([p /t n] t1) = ([p /t n] t2) ->
                     p notin_t t1 ->
                     p notin_t t2 ->
                     t1 = t2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_decl_ty :
  (forall s1 s2 p n, ([p /s n] s1) = ([p /s n] s2) ->
                     p notin_s s1 ->
                     p notin_s s2 ->
                     s1 = s2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_decl_tys :
  (forall ss1 ss2 p n, ([p /ss n] ss1) = ([p /ss n] ss2) ->
                       p notin_ss ss1 ->
                       p notin_ss ss2 ->
                       ss1 = ss2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_exp :
  (forall e1 e2 p n, ([p /e n] e1) = ([p /e n] e2) ->
                     p notin_e e1 ->
                     p notin_e e2 ->
                     e1 = e2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_decl :
  (forall d1 d2 p n, ([p /d n] d1) = ([p /d n] d2) ->
                     p notin_d d1 ->
                     p notin_d d2 ->
                     d1 = d2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.

Lemma subst_equality_decls :
  (forall ds1 ds2 p n, ([p /ds n] ds1) = ([p /ds n] ds2) ->
                  p notin_ds ds1 ->
                  p notin_ds ds2 ->
                  ds1 = ds2).
Proof.
  destruct subst_equality_mutind; crush.
Qed.



Lemma in_dty_subst :
  forall ss s p n, in_dty s ([p /ss n] ss) ->
              exists s', s = ([p /s n] s').
Proof.
  intro ss; induction ss as [|s' ss']; intros; simpl in H;
    inversion H; subst.

  exists s'; auto.

  apply IHss' in H2; destruct H2 as [s''];
    exists s''; auto.
Qed.

Lemma in_dty_subst_notin :
  forall ss s p n, in_dty s ([p /ss n] ss)->
              forall e, e notin_ss ss ->
                   exists s', s = ([p /s n] s') /\
                         e notin_s s'.
Proof.
  intro ss; induction ss as [|s' ss']; intros; simpl in H;
    inversion H; subst.

  exists s'; split; inversion H0; auto.

  apply IHss' with (e:=e) in H3; [|inversion H0; auto].
  destruct H3 as [s''];
    exists s''; auto.
Qed.

Lemma in_dty_subst_switch :
  forall ss s p1 n, in_dty ([p1 /s n] s) ([p1 /ss n] ss) ->
               p1 notin_ss ss ->
               p1 notin_s s ->
               forall p2, in_dty ([p2 /s n] s) ([p2 /ss n] ss).
Proof.
  intro ss; induction ss; intros; simpl in H;
    inversion H; subst.

  apply subst_equality_decl_ty in H4; subst; auto;
    [|inversion H0; auto].
  simpl; apply in_head_dty.

  apply IHss with (p2:=p2) in H4; auto;
    [|inversion H0; auto].
  simpl; apply in_tail_dty; auto.
Qed.

Lemma idt_subst :
  (forall s p n, id_t ([p /s n]s) = id_t s).
Proof.
  destruct s; intros; simpl; auto.
Qed.

Lemma in_dty_idt_subst_switch :
  (forall ss s p n, in_dty s ([p /ss n] ss) ->
               forall p', exists s', id_t s = id_t s' /\
                           in_dty s' ([p' /ss n]ss)).
Proof.
  intro ss;
    induction ss;
    intros;
    simpl in H;
    inversion H;
    subst.
  
  exists ([p' /s n]d); split;
    [|simpl; apply in_head_dty].
  repeat rewrite idt_subst; auto.

  apply IHss
    with
      (p':=p')
    in H2.
  destruct H2 as [s' Ha];
    destruct Ha as [Ha Hb].
  exists s'; split; auto;
    apply in_tail_dty;
    auto.
Qed.

Lemma  idd_subst:
  (forall d p n, id_d ([p /d n]d) = id_d d).
Proof.
  destruct d; intros; simpl; auto.
Qed.

Lemma ind_idd_subst_switch:
  (forall ds d p n, in_d d ([p /ds n] ds) ->
               forall p', exists d', id_d d = id_d d' /\
                           in_d d' ([p' /ds n]ds)).
Proof.
  intro ds;
    induction ds;
    intros;
    simpl in H;
    inversion H;
    subst.
  
  exists ([p' /d n]d); split;
    [|simpl; apply in_head_d].
  repeat rewrite idd_subst; auto.

  apply IHds
    with
      (p':=p')
    in H2.
  destruct H2 as [d' Ha];
    destruct Ha as [Ha Hb].
  exists d'; split; auto;
    apply in_tail_d;
    auto.
Qed.

Lemma in_d_subst :
  forall ds d p n, in_d d ([p /ds n] ds) ->
              exists d', d = ([p /d n] d').
Proof.
  intro ds; induction ds as [|d' ds']; intros; simpl in H;
    inversion H; subst.

  exists d'; auto.

  apply IHds' in H2; destruct H2 as [d''];
    exists d''; auto.
Qed.




Lemma wf_closed_mutind :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall n, closed_t n t) /\
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall n, closed_s n s) /\
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall n, closed_ss n ss) /\
  (forall Sig G e, Sig en G vdash e wf_e ->
            forall n, closed_e n e) /\
  (forall Sig G d, Sig en G vdash d wf_d ->
            forall n, closed_d n d) /\
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
             forall n, closed_ds n ds).
Proof.
  apply wf_mutind; intros; crush.

  eapply closed_subst_neq_type with (n:=S n) in H0; auto.
  auto.
  
  eapply closed_subst_neq_decl_tys with (n:=S n) in H; auto.
  auto.

  eapply closed_subst_neq_exp with (n:=S n) in H0; auto.
  eapply closed_subst_neq_type with (n:=S n) in H1; auto.
  auto.

  eapply closed_subst_neq_decls with (n:=S n) in H; auto.
  auto.
Qed.

Lemma wf_closed_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall n, closed_t n t).
Proof.
  destruct wf_closed_mutind; auto.
Qed.

Lemma wf_closed_decl_ty :
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall n, closed_s n s).
Proof.
  destruct wf_closed_mutind; crush.
Qed.

Lemma wf_closed_decl_tys :
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall n, closed_ss n ss).
Proof.
  destruct wf_closed_mutind; crush.
Qed.

Lemma wf_closed_exp :
  (forall Sig G e, Sig en G vdash e wf_e ->
                   forall n, closed_e n e).
Proof.
  destruct wf_closed_mutind; crush.
Qed.

Lemma wf_closed_decl :
  (forall Sig G d, Sig en G vdash d wf_d ->
            forall n, closed_d n d).
Proof.
  destruct wf_closed_mutind; crush.
Qed.

Lemma wf_closed_decls :
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
            forall n, closed_ds n ds).
Proof.
  destruct wf_closed_mutind; crush.
Qed.

Lemma wf_closed_env :
  (forall Sig G, Sig evdash G wf_env ->
          forall n, closed_env G n).
Proof.
  intros Sig G Hwf;
    induction Hwf;
    intros.

  intros t' Hin;
    inversion Hin.

  intros t' Hin;
    inversion Hin;
    [subst t'
    |apply IHHwf;
     auto].
  intros n' Hle.
  eapply wf_closed_type;
    eauto.
Qed.

Lemma wf_closed_store_type :
  (forall Sig, Sig wf_st ->
        forall n, closed_env Sig n).
Proof.
  intros Sig Hwf;
    induction Hwf;
    intros.

  intros t' Hin;
    inversion Hin.

  intros t' Hin;
    inversion Hin;
    [subst t'
    |apply IHHwf;
     auto].
  intros n' Hle.
  eapply wf_closed_type;
    eauto.
Qed.

Lemma raise_n_t_top_simpl :
  forall n i, raise_n_t n top i = top.
Proof.
  intro n; induction n as [|n']; simpl; auto.
Qed.

Hint Rewrite raise_n_t_top_simpl.
Hint Resolve raise_n_t_top_simpl.

Lemma raise_n_t_bot_simpl :
  forall n i, raise_n_t n bot i = bot.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_t_bot_simpl.
Hint Resolve raise_n_t_bot_simpl.

Lemma raise_n_t_arr_simpl :
  forall n i t1 t2, raise_n_t n (t1 arr t2) i = ((raise_n_t n t1 i) arr (raise_n_t n t2 (S i))).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_t_arr_simpl.
Hint Resolve raise_n_t_arr_simpl.

Lemma raise_n_t_sel_simpl :
  forall n i p l, raise_n_t n (sel p l) i = (sel (raise_n_e n p i) l).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_t_sel_simpl.
Hint Resolve raise_n_t_sel_simpl.

Lemma raise_n_t_str_simpl :
  forall n i ss, raise_n_t n (str ss rts) i = str (raise_n_ss n ss (S i)) rts.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_t_str_simpl.
Hint Resolve raise_n_t_str_simpl.

Lemma raise_n_s_upper_simpl :
  forall n i L t, raise_n_s n (type L ext t) i = type L ext (raise_n_t n t i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_s_upper_simpl.
Hint Resolve raise_n_s_upper_simpl.

Lemma raise_n_s_lower_simpl :
  forall n i L t, raise_n_s n (type L sup t) i = type L sup (raise_n_t n t i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_s_lower_simpl.
Hint Resolve raise_n_s_lower_simpl.

Lemma raise_n_s_equal_simpl :
  forall n i L t, raise_n_s n (type L eqt t) i = type L eqt (raise_n_t n t i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_s_equal_simpl.
Hint Resolve raise_n_s_equal_simpl.

Lemma raise_n_s_value_simpl :
  forall n i l t, raise_n_s n (val l oft t) i = val l oft (raise_n_t n t i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_s_value_simpl.
Hint Resolve raise_n_s_value_simpl.

Lemma raise_n_ss_nil_simpl :
  forall n i, raise_n_ss n dt_nil i = dt_nil.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_ss_nil_simpl.
Hint Resolve raise_n_ss_nil_simpl.

Lemma raise_n_ss_cons_simpl :
  forall n i s ss, raise_n_ss n (dt_con s ss) i = dt_con (raise_n_s n s i) (raise_n_ss n ss i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_ss_cons_simpl.
Hint Resolve raise_n_ss_cons_simpl.

Lemma raise_n_e_loc_simpl :
  forall n i l, raise_n_e n (i_ l) i = i_ l.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_loc_simpl.
Hint Resolve raise_n_e_loc_simpl.

Lemma raise_n_e_concrete_simpl :
  forall n i r, raise_n_e n (c_ r) i = c_ r.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_concrete_simpl.
Hint Resolve raise_n_e_concrete_simpl.

Lemma raise_n_e_abstract_ge_simpl :
  forall n i r, i <= r -> raise_n_e n (a_ r) i = a_ (r + n).
Proof.
  intro n; induction n as [|n'];
    intros; simpl;
      [rewrite plus_0_r|];
      auto.

  rewrite IHn';
    unfold raise_nat.
  apply <- Nat.ltb_ge in H;
    rewrite H.
  rewrite <- plus_assoc;
    rewrite Nat.add_1_l; auto.

  assert (Ha : r <? i = false);
    [apply Nat.ltb_ge; auto
    |rewrite Ha];
    crush.
Qed.

Hint Rewrite raise_n_e_abstract_ge_simpl.
Hint Resolve raise_n_e_abstract_ge_simpl.

Lemma raise_n_e_abstract_lt_simpl :
  forall n i r, r < i -> raise_n_e n (a_ r) i = a_ r.
Proof.
  intro n; induction n as [|n']; intros; simpl; auto.
  rewrite IHn'.
  unfold raise_nat.
  apply Nat.ltb_lt in H;
    rewrite H; auto.
  unfold raise_nat.
  assert (Ha : r <? i = true);
    [apply Nat.ltb_lt; auto
    |rewrite Ha; auto].
Qed.

Hint Rewrite raise_n_e_abstract_lt_simpl.
Hint Resolve raise_n_e_abstract_lt_simpl.



Lemma raise_n_e_fn_simpl :
  forall n i t1 e t2, raise_n_e n (fn t1 in_exp e off t2) i =
                 fn (raise_n_t n t1 i) in_exp (raise_n_e n e (S i)) off (raise_n_t n t2 (S i)).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_fn_simpl.
Hint Resolve raise_n_e_fn_simpl.

Lemma raise_n_e_app_simpl :
  forall n i e1 e2, raise_n_e n (e_app e1 e2) i = e_app (raise_n_e n e1 i) (raise_n_e n e2 i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_app_simpl.
Hint Resolve raise_n_e_app_simpl.

Lemma raise_n_e_acc_simpl :
  forall n i e l, raise_n_e n (e_acc e l) i = e_acc (raise_n_e n e i) l.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_acc_simpl.
Hint Resolve raise_n_e_acc_simpl.

Lemma raise_n_e_new_simpl :
  forall n i ds, raise_n_e n (new ds) i = new (raise_n_ds n ds (S i)).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_new_simpl.
Hint Resolve raise_n_e_new_simpl.

Lemma raise_n_e_cast_simpl :
  forall n i e t, raise_n_e n (e cast t) i = ((raise_n_e n e i) cast (raise_n_t n t i)).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_e_cast_simpl.
Hint Resolve raise_n_e_cast_simpl.

Lemma raise_n_d_equal_simpl :
  forall n i L t, raise_n_d n (type L eqe t) i = type L eqe (raise_n_t n t i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_d_equal_simpl.
Hint Resolve raise_n_d_equal_simpl.

Lemma raise_n_d_value_simpl :
  forall n i l e t, raise_n_d n (val l assgn e oft t) i = val l assgn (raise_n_e n e i) oft (raise_n_t n t i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_d_value_simpl.
Hint Resolve raise_n_d_value_simpl.

Lemma raise_n_ds_nil_simpl :
  forall n i, raise_n_ds n d_nil i = d_nil.
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_ds_nil_simpl.
Hint Resolve raise_n_ds_nil_simpl.

Lemma raise_n_ds_con_simpl :
  forall n i d ds, raise_n_ds n (d_con d ds) i = d_con (raise_n_d n d i) (raise_n_ds n ds i).
Proof.
  intro n; induction n as [|n']; simpl; auto.    
Qed.

Hint Rewrite raise_n_ds_con_simpl.
Hint Resolve raise_n_ds_con_simpl.

Lemma closed_ty_top :
  forall i, closed_ty top i.
Proof.
  intros i n; auto.
Qed.

Hint Resolve closed_ty_top.
Hint Rewrite closed_ty_top.

Lemma closed_ty_bot :
  forall i, closed_ty bot i.
Proof.
  intros i n; auto.
Qed.

Hint Resolve closed_ty_bot.
Hint Rewrite closed_ty_bot.

Lemma closed_ty_sel :
  forall i p l, closed_ty (sel p l) i <-> closed_exp p i.
Proof.
  intros; split; intros; intros n Ha; auto.

  assert (closed_t n (sel p l));
    auto.
  inversion H0; auto.
Qed.

Hint Resolve closed_ty_sel.
Hint Rewrite closed_ty_sel.

Lemma closed_ty_arr :
  forall i t1 t2, closed_ty (t1 arr t2) i <-> closed_ty t1 i /\ closed_ty t2 (S i).
Proof.
  intros; split; intros.
  split;
    intros n Ha.
  assert (Hb : closed_t n (t1 arr t2)); auto.
  inversion Hb; auto.

  destruct n as [|n'];
    [inversion Ha|].
  assert (Hb : closed_t n' (t1 arr t2));
    [apply H; crush|].
  inversion Hb; auto.

  destruct H as [Ha Hb];
    intros n Hc; auto.
  assert (closed_t (S n) t2);
    [apply Hb; crush|auto].
Qed.

Hint Resolve closed_ty_arr.
Hint Rewrite closed_ty_arr.

Lemma closed_ty_str :
  forall i ss, closed_ty (str ss rts) i <-> closed_decl_tys ss (S i).
Proof.
  intros; split; intros; intros n Ha.

  destruct n as [|n'];
    [inversion Ha|].
  assert (closed_t n' (str ss rts));
    [apply H; crush|].
  inversion H0; auto.

  assert (closed_ss (S n) ss);
    [apply H; crush|auto].
Qed.

Hint Resolve closed_ty_str.
Hint Rewrite closed_ty_str.

Lemma closed_decl_ty_upper :
  forall i L t, closed_decl_ty (type L ext t) i <-> closed_ty t i.
Proof.
  intros; split; intros; intros n Ha; auto.

  assert (closed_s n (type L ext t));
    auto.
  inversion H0; auto.
Qed.

Hint Resolve closed_decl_ty_upper.
Hint Rewrite closed_decl_ty_upper.

Lemma closed_decl_ty_lower :
  forall i L t, closed_decl_ty (type L sup t) i <-> closed_ty t i.
Proof.
  intros; split; intros; intros n Ha; auto.

  assert (closed_s n (type L sup t));
    auto.
  inversion H0; auto.
Qed.

Hint Resolve closed_decl_ty_lower.
Hint Rewrite closed_decl_ty_lower.

Lemma closed_decl_ty_equal :
  forall i L t, closed_decl_ty (type L eqt t) i <-> closed_ty t i.
Proof.
  intros; split; intros; intros n Ha; auto.

  assert (closed_s n (type L eqt t));
    auto.
  inversion H0; auto.
Qed.

Hint Resolve closed_decl_ty_equal.
Hint Rewrite closed_decl_ty_equal.

Lemma closed_decl_ty_value :
  forall i l t, closed_decl_ty (val l oft t) i <-> closed_ty t i.
Proof.
  intros; split; intros; intros n Ha; auto.

  assert (closed_s n (val l oft t));
    auto.
  inversion H0; auto.
Qed.

Hint Resolve closed_decl_ty_value.
Hint Rewrite closed_decl_ty_value.

Lemma closed_decl_tys_nil :
  forall i, closed_decl_tys dt_nil i.
Proof.
  intros i n; auto.
Qed.

Hint Resolve closed_decl_tys_nil.
Hint Rewrite closed_decl_tys_nil.

Lemma closed_decl_tys_con :
  forall i s ss, closed_decl_tys (dt_con s ss) i <-> closed_decl_ty s i /\ closed_decl_tys ss i.
Proof.
  intros; split; intros;
    [split;
     intros n Ha;
     apply H in Ha;
     inversion Ha;
     auto|
     intros n Ha].

  destruct H as [Hb Hc]; auto.
Qed.

Hint Resolve closed_decl_tys_con.
Hint Rewrite closed_decl_tys_con.

Lemma closed_exp_var :
  forall i n, closed_exp (c_ n) i.
Proof.
  intros i n m; auto. 
Qed.

Hint Resolve closed_exp_var.
Hint Rewrite closed_exp_var.


Lemma closed_exp_loc :
  forall i l, closed_exp (i_ l) i.
Proof.
  intros i n m; auto. 
Qed.

Hint Resolve closed_exp_loc.
Hint Rewrite closed_exp_loc.


Lemma closed_exp_cast :
  forall i e t, closed_exp (e cast t) i <-> (closed_exp e i) /\ (closed_ty t i).
Proof.
  intros; split; intros;
    [split|];intros n Ha; auto.

  apply H in Ha; inversion Ha; auto.
  apply H in Ha; inversion Ha; auto.
  destruct H as [Hb Hc]; auto.
Qed.

Hint Resolve closed_exp_cast.
Hint Rewrite closed_exp_cast.


Lemma closed_exp_fn :
  forall i t1 e t2, closed_exp (fn t1 in_exp e off t2) i <-> (closed_ty t1 i) /\
                                                             (closed_exp e (S i)) /\
                                                             (closed_ty t2 (S i)).
Proof.
  intros; split; intros;
    [split;
     [|split]|];
    intros n Ha;
    auto;
    try solve [apply H in Ha; inversion Ha; auto];
    try solve [destruct n as [|n'];
               [inversion Ha|
                apply le_S_n, H in Ha; inversion Ha; auto]].

  destruct H as [Hb Hc];
    destruct Hc as [Hc Hd].
  apply cl_fn; auto.
  apply le_n_S, Hc in Ha; auto.
  apply le_n_S, Hd in Ha; auto.
Qed.

Hint Resolve closed_exp_fn.
Hint Rewrite closed_exp_fn.


Lemma closed_exp_app :
  forall i e1 e2, closed_exp (e_app e1 e2) i <-> (closed_exp e1 i) /\ (closed_exp e2 i).
Proof.
  intros; split; intros;
    [split|]; intros n Ha;
      try solve [apply H in Ha; inversion Ha; auto].
  destruct H as [Hb Hc].
  apply cl_app;
    [apply Hb in Ha
    |apply Hc in Ha]; auto.
Qed.

Hint Resolve closed_exp_app.
Hint Rewrite closed_exp_app.


Lemma closed_exp_acc :
  forall i e l, closed_exp (e_acc e l) i <-> closed_exp e i.
Proof.
  intros; split; intros; intros n Ha; auto.

  apply H in Ha; inversion Ha; auto.
  
Qed.

Hint Resolve closed_exp_acc.
Hint Rewrite closed_exp_acc.


Lemma closed_exp_new :
  forall i ds, closed_exp (new ds) i <-> closed_decls ds (S i).
Proof.
  intros; split; intros; intros n Ha; auto.

  destruct n as [|n'];
    [inversion Ha|];
    apply le_S_n, H in Ha;
    inversion Ha; auto.

  apply le_n_S, H in Ha; auto.
Qed.

Hint Resolve closed_exp_new.
Hint Rewrite closed_exp_new.

Lemma closed_decl_equal :
  forall i L t, closed_decl (type L eqe t) i <-> closed_ty t i.
Proof.
  intros; split; intros; intros n Ha; auto.

  apply H in Ha; inversion Ha; auto.
Qed.

Hint Resolve closed_decl_equal.
Hint Rewrite closed_decl_equal.

Lemma closed_decl_value:
  forall i l e t, closed_decl (val l assgn e oft t) i <-> (closed_exp e i) /\ (closed_ty t i).
Proof.
  intros; split; intros;
    [split|];
    intros n Ha;
    try solve [apply H in Ha; inversion Ha; auto].

  destruct H as [Hb Hc];
    apply cld_value; auto.
Qed.

Hint Resolve closed_decl_value.
Hint Rewrite closed_decl_value.


Lemma closed_decls_nil :
  forall i, closed_decls d_nil i.
Proof.
  intros i n Ha; auto.
Qed.

Hint Resolve closed_decls_nil.
Hint Rewrite closed_decls_nil.

Lemma closed_decls_con :
  forall i d ds, closed_decls (d_con d ds) i <-> (closed_decl d i) /\ (closed_decls ds i).
Proof.
  intros; split; intros;
    [split|];
    intros n Ha;
    try solve [apply H in Ha; inversion Ha; auto].

  destruct  H as [Hb Hc];
    auto.
Qed.

Hint Resolve closed_decls_con.
Hint Rewrite closed_decls_con.

Lemma closed_ty_le :
  forall t n, closed_ty t n ->
              forall m, n <= m ->
                        closed_ty t m.
Proof.
  intros.

  intros n' Hle;
    apply H; crush.
Qed.

Lemma closed_decl_ty_le :
  forall s n, closed_decl_ty s n ->
              forall m, n <= m ->
                        closed_decl_ty s m.
Proof.
  intros.

  intros n' Hle;
    apply H; crush.
Qed.

Lemma closed_decl_tys_le :
  forall ss n, closed_decl_tys ss n ->
               forall m, n <= m ->
                         closed_decl_tys ss m.
Proof.
  intros.

  intros n' Hle;
    apply H; crush.
Qed.

Lemma closed_exp_le :
  forall e n, closed_exp e n ->
              forall m, n <= m ->
                        closed_exp e m.
Proof.
  intros.

  intros n' Hle;
    apply H; crush.
Qed.

Lemma closed_decl_le :
  forall d n, closed_decl d n ->
              forall m, n <= m ->
                        closed_decl d m.
Proof.
  intros.

  intros n' Hle;
    apply H; crush.
Qed.

Lemma closed_decls_le :
  forall ds n, closed_decls ds n ->
               forall m, n <= m ->
                         closed_decls ds m.
Proof.
  intros.

  intros n' Hle;
    apply H; crush.
Qed.

Hint Rewrite closed_ty_le closed_decl_ty_le closed_decl_tys_le
     closed_exp_le closed_decl_le closed_decls_le.
Hint Resolve closed_ty_le closed_decl_ty_le closed_decl_tys_le
     closed_exp_le closed_decl_le closed_decls_le.

Lemma raise_closed_substitution :
  (forall t n, closed_ty t n ->
               forall p t', t = ([p /t n] t') ->
                            forall m, t = [p /t n + m] (raise_n_t m t' n)) /\
  (forall s n, closed_decl_ty s n ->
               forall p s', s = ([p /s n] s') ->
                            forall m, s = [p /s n + m] (raise_n_s m s' n)) /\
  (forall ss n, closed_decl_tys ss n ->
                forall p ss', ss = ([p /ss n] ss') ->
                              forall m, ss = [p /ss n + m] (raise_n_ss m ss' n)) /\
  (forall e n, closed_exp e n ->
               forall p e', e = ([p /e n] e') ->
                            forall m, e = [p /e n + m] (raise_n_e m e' n)) /\
  (forall d n, closed_decl d n ->
               forall p d', d = ([p /d n] d') ->
                            forall m, d = [p /d n + m] (raise_n_d m d' n)) /\
  (forall ds n, closed_decls ds n ->
                forall p ds', ds = ([p /ds n] ds') ->
                              forall m, ds = [p /ds n + m] (raise_n_ds m ds' n)).
Proof.
  apply type_exp_mutind; intros;
    try (destruct t');
    try (destruct s');
    try (destruct ss');
    try (destruct e');
    try (destruct d');
    try (destruct ds');
    try solve [crush].

  simpl in H1; inversion H1; subst.
  rewrite raise_n_t_str_simpl.
  erewrite H with (m:=m); simpl; auto.
  rewrite plus_Sn_m; auto.
  apply closed_ty_str; auto.
  
  simpl in H1; inversion H1; subst.
  rewrite raise_n_t_sel_simpl.
  erewrite H with (m:=m); simpl; auto.
  apply -> closed_ty_sel; eauto.

  destruct closed_ty_arr with (i:=n)
                              (t1:=t)
                              (t2:=t0)as [Ha Htmp];
    destruct (Ha H1) as [Hb Hc].
  simpl in H2; inversion H2; subst.
  rewrite raise_n_t_arr_simpl.
  erewrite H with (m:=m), H0 with (m:=m); simpl; auto.
  rewrite plus_Sn_m; auto.
  auto.
  auto.
  
  simpl in H1; inversion H1; subst.
  rewrite raise_n_s_upper_simpl.
  erewrite H with (m:=m); simpl; auto.
  apply -> closed_decl_ty_upper; eauto.

  simpl in H1; inversion H1; subst.
  rewrite raise_n_s_lower_simpl.
  erewrite H with (m:=m); simpl; auto.
  apply -> closed_decl_ty_lower; eauto.

  simpl in H1; inversion H1; subst.
  rewrite raise_n_s_equal_simpl.
  erewrite H with (m:=m); simpl; auto.
  apply -> closed_decl_ty_equal; eauto.

  simpl in H1; inversion H1; subst.
  rewrite raise_n_s_value_simpl.
  erewrite H with (m:=m); simpl; auto.
  apply -> closed_decl_ty_value; eauto.

  simpl in H2; inversion H2; subst.
  rewrite raise_n_ss_cons_simpl.
  erewrite H, H0 with (m:=m); simpl; auto.
  apply -> closed_decl_tys_con; eauto.
  apply -> closed_decl_tys_con; eauto.

  simpl in H1; inversion H1; subst.
  rewrite raise_n_e_new_simpl.
  erewrite H with (m:=m); simpl; auto.
  rewrite plus_Sn_m; auto.
  apply -> closed_exp_new; eauto.

  simpl in H1; inversion H1; subst.
  destruct v as [r|r];
    [inversion H1|].
  destruct (le_lt_dec n r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n r);
    subst;
    simpl;
    [rewrite <- beq_nat_refl;
     rewrite <- beq_nat_refl in H1;
     auto|].
  apply Nat.eqb_neq in n0;
    rewrite n0 in H1;
    inversion H1.
  apply Nat.lt_neq, Nat.eqb_neq in l;
    rewrite Nat.eqb_sym in H1;
    rewrite l in H1;
    inversion H1.

  simpl in H2; inversion H2; subst.
  rewrite raise_n_e_app_simpl.
  erewrite H, H0 with (m:=m); simpl; auto;
    apply closed_exp_app in H1; destruct H1; auto.

  simpl in H2; inversion H2; subst.
  destruct v as [r|r];
    [inversion H2|].
  destruct (le_lt_dec n r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n r);
    subst;
    simpl;
    [rewrite <- beq_nat_refl;
     rewrite <- beq_nat_refl in H2;
     auto|].
  apply Nat.eqb_neq in n0;
    rewrite n0 in H2;
    inversion H2.
  apply Nat.lt_neq, Nat.eqb_neq in l;
    rewrite Nat.eqb_sym in H2;
    rewrite l in H2;
    inversion H2.

  simpl in H3; inversion H3; subst.
  rewrite raise_n_e_fn_simpl.
  erewrite H, H0, H1 with (m:=m); simpl; auto;
    apply closed_exp_fn in H2; crush.

  simpl in H3; inversion H3; subst.
  destruct v as [r|r];
    [inversion H3|].
  destruct (le_lt_dec n r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n r);
    subst;
    simpl;
    [rewrite <- beq_nat_refl;
     rewrite <- beq_nat_refl in H3;
     auto|].
  apply Nat.eqb_neq in n0;
    rewrite n0 in H3;
    inversion H3.
  apply Nat.lt_neq, Nat.eqb_neq in l;
    rewrite Nat.eqb_sym in H3;
    rewrite l in H3;
    inversion H3.

  simpl in H1; inversion H1; subst.
  rewrite raise_n_e_acc_simpl.
  erewrite H with (m:=m); simpl; auto;
    apply closed_exp_acc in H0; auto.

  simpl in H1; inversion H1; subst.
  destruct v as [r|r];
    [inversion H1|].
  destruct (le_lt_dec n r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n r);
    subst;
    simpl;
    [rewrite <- beq_nat_refl;
     rewrite <- beq_nat_refl in H1;
     auto|].
  apply Nat.eqb_neq in n0;
    rewrite n0 in H1;
    inversion H1.
  apply Nat.lt_neq, Nat.eqb_neq in l0;
    rewrite Nat.eqb_sym in H1;
    rewrite l0 in H1;
    inversion H1.

  destruct v0 as [r|r];
    simpl in H0.
  rewrite raise_n_e_concrete_simpl; simpl; auto.
  destruct (le_lt_dec n r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n r); subst;
    [rewrite <- beq_nat_refl in H0;
     simpl;
     rewrite <- beq_nat_refl;
     auto
    |].
  apply Nat.eqb_neq in n0;
    rewrite n0 in H0;
    rewrite H0 in H.
  apply H in l; inversion l; subst.
  inversion H3; crush.
  assert (Ha : r <> n);
    [apply Nat.lt_neq; auto|];
    apply Nat.eqb_neq in Ha;
    rewrite Nat.eqb_sym in H0;
    rewrite Ha in H0;
    rewrite H0 in H.
  rewrite raise_n_e_abstract_lt_simpl; auto.
  simpl.
  assert (Hb : n + m <> r);
    [crush|].
  apply Nat.eqb_neq in Hb;
    rewrite Hb; auto.

  simpl in H0; inversion H0; subst.
  destruct v as [r|r];
    [inversion H0|].
  destruct (le_lt_dec n0 r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n0 r);
    subst;
    simpl;
    [rewrite <- beq_nat_refl;
     rewrite <- beq_nat_refl in H0;
     auto|].
  apply Nat.eqb_neq in n1;
    rewrite n1 in H0;
    inversion H0.
  apply Nat.lt_neq, Nat.eqb_neq in l;
    rewrite Nat.eqb_sym in H0;
    rewrite l in H0;
    inversion H0.

  simpl in H2; inversion H2; subst.
  destruct v as [r|r];
    [inversion H2|].
  destruct (le_lt_dec n r).
  rewrite raise_n_e_abstract_ge_simpl; auto.
  destruct (Nat.eq_dec n r);
    subst;
    simpl;
    [rewrite <- beq_nat_refl;
     rewrite <- beq_nat_refl in H2;
     auto|].
  apply Nat.eqb_neq in n0;
    rewrite n0 in H2;
    inversion H2.
  apply Nat.lt_neq, Nat.eqb_neq in l;
    rewrite Nat.eqb_sym in H2;
    rewrite l in H2;
    inversion H2.

  simpl in H2; inversion H2; subst.
  rewrite raise_n_e_cast_simpl.
  erewrite H, H0 with (m:=m); simpl; auto;
    apply closed_exp_cast in H1; destruct H1; auto.

  simpl in H1; inversion H1; subst.
  rewrite raise_n_d_equal_simpl.
  erewrite H with (m:=m); simpl; auto;
    apply closed_decl_equal in H0; auto.

  simpl in H2; inversion H2; subst.
  rewrite raise_n_d_value_simpl.
  erewrite H, H0 with (m:=m); simpl; auto;
    apply closed_decl_value in H1; crush.

  simpl in H2; inversion H2; subst.
  rewrite raise_n_ds_con_simpl.
  erewrite H, H0 with (m:=m); simpl; auto;
    apply closed_decls_con in H1; destruct H1; auto.
Qed.

Lemma raise_closed_substitution_type :
  (forall t n, closed_ty t n ->
               forall p t', t = ([p /t n] t') ->
                            forall m, t = [p /t n + m] (raise_n_t m t' n)).
Proof.
  destruct raise_closed_substitution; crush.
Qed.

Lemma raise_closed_substitution_decl_ty :
  (forall s n, closed_decl_ty s n ->
               forall p s', s = ([p /s n] s') ->
                            forall m, s = [p /s n + m] (raise_n_s m s' n)).
Proof.
  destruct raise_closed_substitution; crush.
Qed.

Lemma raise_closed_substitution_decl_tys :
  (forall ss n, closed_decl_tys ss n ->
                forall p ss', ss = ([p /ss n] ss') ->
                              forall m, ss = [p /ss n + m] (raise_n_ss m ss' n)).
Proof.
  destruct raise_closed_substitution; crush.
Qed.

Lemma raise_closed_substitution_exp :
  (forall e n, closed_exp e n ->
               forall p e', e = ([p /e n] e') ->
                            forall m, e = [p /e n + m] (raise_n_e m e' n)).
Proof.
  destruct raise_closed_substitution; crush.
Qed.

Lemma raise_closed_substitution_decl :
  (forall d n, closed_decl d n ->
               forall p d', d = ([p /d n] d') ->
                            forall m, d = [p /d n + m] (raise_n_d m d' n)).
Proof.
  destruct raise_closed_substitution; crush.
Qed.

Lemma raise_closed_substitution_decls :
  (forall ds n, closed_decls ds n ->
                forall p ds', ds = ([p /ds n] ds') ->
                              forall m, ds = [p /ds n + m] (raise_n_ds m ds' n)).
Proof.
  destruct raise_closed_substitution; crush.
Qed.

Lemma rename_eq :
  forall n m, rename n n m = m.
Proof.
  intros n; destruct n as [|n']; intros; auto.

  simpl; rewrite <- beq_nat_refl; auto.
Qed.

Lemma rename_neq :
  forall r n m, r <> n ->
                rename r n m = r.
Proof.    
  intros r n; destruct r as [|r'];
    destruct n as [|n']; intros; auto.

  crush.

  simpl.
  assert (Hneq : r' <> n'); [crush|].
  apply Nat.eqb_neq in Hneq;
    rewrite Hneq; auto.
Qed.

Lemma rename_rewrite :
  forall r n m, rename r n m = (if r =? n then m else r).
Proof.
  intro r; destruct r as [|r']; auto.
Qed.

Lemma rename_S :
  forall r n m, rename (S r) (S n) (S m) = S (rename r n m).
Proof.
  intros.

  destruct (Nat.eq_dec r n) as [|Hneq];
    [subst;
     repeat rewrite rename_eq;
     auto
    |repeat rewrite rename_neq; auto].
Qed.

Hint Rewrite rename_eq.
Hint Rewrite rename_neq.
Hint Rewrite rename_rewrite.
Hint Rewrite rename_S.
Hint Resolve rename_eq.
Hint Resolve rename_neq.
Hint Resolve rename_rewrite.
Hint Resolve rename_S.


Lemma rename_closed_subst_mutind :
  (forall t p n m, closed_t m ([p /t n] t) ->
                   ([p /t n] t) = ([p /t m] (t [n maps_t m]))) /\
  (forall s p n m, closed_s m ([p /s n] s) ->
                   ([p /s n] s) = ([p /s m] (s [n maps_s m]))) /\
  (forall ss p n m, closed_ss m ([p /ss n] ss) ->
                    ([p /ss n] ss) = ([p /ss m] (ss [n maps_ss m]))) /\
  (forall e p n m, closed_e m ([p /e n] e) ->
                   ([p /e n] e) = ([p /e m] (e [n maps_e m]))) /\
  (forall d p n m, closed_d m ([p /d n] d) ->
                   ([p /d n] d) = ([p /d m] (d [n maps_d m]))) /\
  (forall ds p n m, closed_ds m ([p /ds n] ds) ->
                    ([p /ds n] ds) = ([p /ds m] (ds [n maps_ds m]))).
Proof.
  apply type_exp_mutind; intros; simpl; auto;
    try solve [try (erewrite H; inversion H0; crush);
               try (erewrite H, H0; inversion H1; crush);
               try (erewrite H, H0, H1; inversion H2; crush)].

  (*var*)
  simpl; destruct v as [|r]; [auto|simpl].
  destruct (Nat.eq_dec n r) as [Heq|Heq];
    [subst; simpl; rewrite rename_eq; repeat rewrite <- beq_nat_refl; auto
    |assert (Heq' : r <> n); [crush|]].
  apply Nat.eqb_neq in Heq;
    apply Nat.eqb_neq in Heq'.
  rewrite rename_rewrite; simpl in *.
  rewrite Heq, Heq'.
  simpl in H; rewrite Heq in H;
    inversion H; subst.
  inversion H2; subst.
  apply Nat.eqb_neq in H3; rewrite H3; auto.
Qed.

Lemma rename_closed_subst_type :
  (forall t p n m, closed_t m ([p /t n] t) ->
                   ([p /t n] t) = ([p /t m] (t [n maps_t m]))).
Proof.
  destruct rename_closed_subst_mutind; crush.
Qed.

Lemma rename_closed_subst_decl_ty :
  (forall s p n m, closed_s m ([p /s n] s) ->
                   ([p /s n] s) = ([p /s m] (s [n maps_s m]))).
Proof.
  destruct rename_closed_subst_mutind; crush.
Qed.

Lemma rename_closed_subst_decl_tys :
  (forall ss p n m, closed_ss m ([p /ss n] ss) ->
                    ([p /ss n] ss) = ([p /ss m] (ss [n maps_ss m]))).
Proof.
  destruct rename_closed_subst_mutind; crush.
Qed.

Lemma rename_closed_subst_exp :
  (forall e p n m, closed_e m ([p /e n] e) ->
                   ([p /e n] e) = ([p /e m] (e [n maps_e m]))).
Proof.
  destruct rename_closed_subst_mutind; crush.
Qed.

Lemma rename_closed_subst_decl :
  (forall d p n m, closed_d m ([p /d n] d) ->
                   ([p /d n] d) = ([p /d m] (d [n maps_d m]))).
Proof.
  destruct rename_closed_subst_mutind; crush.
Qed.

Lemma rename_closed_subst_decls :
  (forall ds p n m, closed_ds m ([p /ds n] ds) ->
                    ([p /ds n] ds) = ([p /ds m] (ds [n maps_ds m]))).
Proof.
  destruct rename_closed_subst_mutind; crush.
Qed.

Lemma raise_closed_le_mutind :
  (forall t n, closed_ty t n ->
               forall m, n <= m ->
                         (t raise_t m) = t) /\
  
  (forall s n, closed_decl_ty s n ->
               forall m, n <= m ->
                         (s raise_s m) = s) /\
  
  (forall ss n, closed_decl_tys ss n ->
                forall m, n <= m ->
                          (ss raise_ss m) = ss) /\
  
  (forall e n, closed_exp e n ->
               forall m, n <= m ->
                         (e raise_e m) = e) /\
  
  (forall d n, closed_decl d n ->
               forall m, n <= m ->
                         (d raise_d m) = d) /\
  
  (forall ds n, closed_decls ds n ->
                forall m, n <= m ->
                          (ds raise_ds m) = ds).
Proof.
  apply type_exp_mutind; intros; simpl; auto.

  (*struct type*)
  rewrite H with (n:=S n); crush.

  (*selection type*)
  rewrite H with (n:=n); auto.
  apply -> closed_ty_sel; eauto.

  (*arrow type*)
  apply closed_ty_arr in H1; destruct H1.
  rewrite H with (n:=n), H0 with (n:=S n); crush.

  (*upper*)
  apply closed_decl_ty_upper in H0.
  rewrite H with (n:=n); auto.

  (*lower*)
  apply closed_decl_ty_lower in H0.
  rewrite H with (n:=n); auto.

  (*equal*)
  apply closed_decl_ty_equal in H0.
  rewrite H with (n:=n); auto.

  (*value*)
  apply closed_decl_ty_value in H0.
  rewrite H with (n:=n); auto.

  (*dt_con*)
  apply closed_decl_tys_con in H1; destruct H1.
  rewrite H with (n:=n), H0 with (n:=n); auto.

  (*new*)
  apply closed_exp_new in H0.
  rewrite H with (n:=S n); crush.

  (*app*)
  apply closed_exp_app in H1; destruct H1.
  rewrite H with (n:=n), H0 with (n:=n); auto.

  (*fn*)
  apply closed_exp_fn in H2;
    destruct H2 as [Ha Hb];
    destruct Hb.
  rewrite H with (n:=n), H0 with (n:=S n), H1 with (n:=S n); crush.

  (*acc*)
  apply closed_exp_acc in H0.
  rewrite H with (n:=n); auto.

  (*var*)
  destruct v as [r|r]; auto.
  simpl. unfold raise_nat.
  destruct (le_lt_dec m r).
  assert (Hle : n <= r); [crush|].
  apply H in Hle.
  inversion Hle; subst.
  inversion H3; crush.
  apply Nat.ltb_lt in l;
    rewrite l; auto.
  
  (*cast*)
  apply closed_exp_cast in H1; destruct H1.
  rewrite H with (n:=n), H0 with (n:=n); auto.

  (*equal decl*)
  apply closed_decl_equal in H0.
  rewrite H with (n:=n); auto.

  (*value decl*)
  apply closed_decl_value in H1; destruct H1.
  rewrite H with (n:=n), H0 with (n:=n); auto.

  (*d_con*)
  apply closed_decls_con in H1; destruct H1.
  rewrite H with (n:=n), H0 with (n:=n); auto.
  
Qed.

Lemma raise_closed_le_type :
  (forall t n, closed_ty t n ->
               forall m, n <= m ->
                         (t raise_t m) = t).
Proof.
  destruct raise_closed_le_mutind; crush.
Qed.

Lemma raise_closed_le_decl_ty :
  (forall s n, closed_decl_ty s n ->
               forall m, n <= m ->
                         (s raise_s m) = s).
Proof.
  destruct raise_closed_le_mutind; crush.
Qed.

Lemma raise_closed_le_decl_tys :
  (forall ss n, closed_decl_tys ss n ->
                forall m, n <= m ->
                          (ss raise_ss m) = ss).
Proof.
  destruct raise_closed_le_mutind; crush.
Qed.

Lemma raise_closed_le_exp :
  (forall e n, closed_exp e n ->
               forall m, n <= m ->
                         (e raise_e m) = e).
Proof.
  destruct raise_closed_le_mutind; crush.
Qed.

Lemma raise_closed_le_decl :
  (forall d n, closed_decl d n ->
               forall m, n <= m ->
                         (d raise_d m) = d).
Proof.
  destruct raise_closed_le_mutind; crush.
Qed.

Lemma raise_closed_le_decls :
  (forall ds n, closed_decls ds n ->
                forall m, n <= m ->
                          (ds raise_ds m) = ds).
Proof.
  destruct raise_closed_le_mutind; crush.
Qed.

Lemma raise_closed_S_n_mutind :
  (forall t n, closed_ty t n ->
               forall m, closed_ty (t raise_t m) (S n)) /\
  
  (forall s n, closed_decl_ty s n ->
               forall m, closed_decl_ty (s raise_s m) (S n)) /\
  
  (forall ss n, closed_decl_tys ss n ->
                forall m, closed_decl_tys (ss raise_ss m) (S n)) /\
  
  (forall e n, closed_exp e n ->
               forall m, closed_exp (e raise_e m) (S n)) /\
  
  (forall d n, closed_decl d n ->
               forall m, closed_decl (d raise_d m) (S n)) /\
  
  (forall ds n, closed_decls ds n ->
                forall m, closed_decls (ds raise_ds m) (S n)).
Proof.
  apply type_exp_mutind; intros; simpl; auto;
    try solve [crush].
  
  (*var*)
  destruct v as [|r]; simpl; auto.
  unfold raise_nat.
  unfold closed_exp in H.
  intros n' Hle.
  destruct (lt_dec r m) as [Hlt|Hlt];
    [apply Nat.ltb_lt in Hlt
    |apply Nat.ltb_nlt in Hlt];
    rewrite Hlt; [crush|].
  destruct n' as [|n'']; [crush|].
  apply le_S_n in Hle; apply H in Hle.
  inversion Hle; subst.
  inversion H2; subst.
  crush.
Qed.    

Lemma raise_closed_S_n_type :
  (forall t n, closed_ty t n ->
               forall m, closed_ty (t raise_t m) (S n)).
Proof.
  destruct raise_closed_S_n_mutind; crush.
Qed.

Hint Rewrite raise_closed_S_n_type.
Hint Resolve raise_closed_S_n_type.

Lemma raise_closed_S_n_decl_ty :    
  (forall s n, closed_decl_ty s n ->
               forall m, closed_decl_ty (s raise_s m) (S n)).
Proof.
  destruct raise_closed_S_n_mutind; crush.
Qed.

Hint Rewrite raise_closed_S_n_decl_ty.
Hint Resolve raise_closed_S_n_decl_ty.

Lemma raise_closed_S_n_decl_tys :    
  (forall ss n, closed_decl_tys ss n ->
                forall m, closed_decl_tys (ss raise_ss m) (S n)).
Proof.
  destruct raise_closed_S_n_mutind; crush.
Qed.

Hint Rewrite raise_closed_S_n_decl_tys.
Hint Resolve raise_closed_S_n_decl_tys.

Lemma raise_closed_S_n_exp :
  (forall e n, closed_exp e n ->
               forall m, closed_exp (e raise_e m) (S n)).
Proof.
  destruct raise_closed_S_n_mutind; crush.
Qed.

Hint Rewrite raise_closed_S_n_exp.
Hint Resolve raise_closed_S_n_exp.

Lemma raise_closed_S_n_decl :    
  (forall d n, closed_decl d n ->
               forall m, closed_decl (d raise_d m) (S n)).
Proof.
  destruct raise_closed_S_n_mutind; crush.
Qed.

Hint Rewrite raise_closed_S_n_decl.
Hint Resolve raise_closed_S_n_decl.

Lemma raise_closed_S_n_decls :
  (forall ds n, closed_decls ds n ->
                forall m, closed_decls (ds raise_ds m) (S n)).
Proof.
  destruct raise_closed_S_n_mutind; crush.
Qed.

Hint Rewrite raise_closed_S_n_decls.
Hint Resolve raise_closed_S_n_decls.

Lemma raise_add_mutind :
  (forall t n m, n <= m -> ((t raise_t n) raise_t S m)  = ((t raise_t m) raise_t n)) /\
  (forall s n m, n <= m -> ((s raise_s n) raise_s S m)  = ((s raise_s m) raise_s n)) /\
  (forall ss n m, n <= m -> ((ss raise_ss n) raise_ss S m)  = ((ss raise_ss m) raise_ss n)) /\
  (forall e n m, n <= m -> ((e raise_e n) raise_e S m)  = ((e raise_e m) raise_e n)) /\
  (forall d n m, n <= m -> ((d raise_d n) raise_d S m)  = ((d raise_d m) raise_d n)) /\
  (forall ds n m, n <= m -> ((ds raise_ds n) raise_ds S m)  = ((ds raise_ds m) raise_ds n)).
Proof.
  apply type_exp_mutind; intros;
    try solve [crush];
    simpl.

  destruct v as [r|r]; simpl; auto.
  unfold raise_nat.
  destruct (lt_dec r n) as [Hlt1|Hnlt1].
  assert (Hlt2 : r < m); [crush|].
  assert (Hlt3 : r < S m); [crush|].
  apply Nat.ltb_lt in Hlt1;
    apply Nat.ltb_lt in Hlt2;
    apply Nat.ltb_lt in Hlt3;
    rewrite Hlt1, Hlt2, Hlt1, Hlt3; auto.

  apply Nat.ltb_nlt in Hnlt1;
    rewrite Hnlt1.
  destruct (lt_dec r m) as [Hlt1|Hnlt2].
  assert (Hlt2 : r + 1 < S m); [crush|].
  apply Nat.ltb_lt in Hlt1;
    apply Nat.ltb_lt in Hlt2;
    rewrite Hlt1, Hlt2, Hnlt1; auto.

  assert (Hnlt3 : ~r + 1 < S m); [crush|].
  apply Nat.ltb_nlt in Hnlt2;
    apply Nat.ltb_nlt in Hnlt3.
  rewrite Hnlt2, Hnlt3.
  assert (Hnlt4: r + 1 <? n = false);
    [apply Nat.ltb_nlt; apply Nat.ltb_nlt in Hnlt1; crush|].
  rewrite Hnlt4; auto.
Qed.

Lemma raise_add_type :
  (forall t n m, n <= m -> ((t raise_t n) raise_t S m)  = ((t raise_t m) raise_t n)).
Proof.
  destruct raise_add_mutind; crush.
Qed.

Lemma raise_add_decl_ty :
  (forall s n m, n <= m -> ((s raise_s n) raise_s S m)  = ((s raise_s m) raise_s n)).
Proof.
  destruct raise_add_mutind; crush.
Qed.

Lemma raise_add_decl_tys :
  (forall ss n m, n <= m -> ((ss raise_ss n) raise_ss S m)  = ((ss raise_ss m) raise_ss n)).
Proof.
  destruct raise_add_mutind; crush.
Qed.

Lemma raise_add_exp :
  (forall e n m, n <= m -> ((e raise_e n) raise_e S m)  = ((e raise_e m) raise_e n)).
Proof.
  destruct raise_add_mutind; crush.
Qed.

Lemma raise_add_decl :
  (forall d n m, n <= m -> ((d raise_d n) raise_d S m)  = ((d raise_d m) raise_d n)).
Proof.
  destruct raise_add_mutind; crush.
Qed.

Lemma raise_add_decls :
  (forall ds n m, n <= m -> ((ds raise_ds n) raise_ds S m)  = ((ds raise_ds m) raise_ds n)).
Proof.
  destruct raise_add_mutind; crush.
Qed.

Lemma raise_S :
  forall n m, (S n raise_n S m) = S (n raise_n m).
Proof.
  intros.

  unfold raise_nat.
  destruct (lt_dec n m) as [Hlt1|Hlt1];
    [assert (Hlt2 : S n < S m); [crush|];
     apply Nat.ltb_lt in Hlt1;
     apply Nat.ltb_lt in Hlt2
    |assert (Hlt2 : ~S n < S m); [crush|];
     apply Nat.ltb_nlt in Hlt1;
     apply Nat.ltb_nlt in Hlt2];
    rewrite Hlt1, Hlt2; auto.
Qed.

Lemma raise_subst_distr_mutind :
  (forall t p n m, (([p /t n] t) raise_t m) = ([p raise_e m /t n raise_n m] (t raise_t m))) /\
  (forall s p n m, (([p /s n] s) raise_s m) = ([p raise_e m /s n raise_n m] (s raise_s m))) /\
  (forall ss p n m, (([p /ss n] ss) raise_ss m) = ([p raise_e m /ss n raise_n m] (ss raise_ss m))) /\
  (forall e p n m, (([p /e n] e) raise_e m) = ([p raise_e m /e n raise_n m] (e raise_e m))) /\
  (forall d p n m, (([p /d n] d) raise_d m) = ([p raise_e m /d n raise_n m] (d raise_d m))) /\
  (forall ds p n m, (([p /ds n] ds) raise_ds m) = ([p raise_e m /ds n raise_n m] (ds raise_ds m))).
Proof.
  apply type_exp_mutind;
    try solve [crush];
    intros; simpl.

  (*struct type*)
  rewrite H.
  rewrite raise_add_exp; [|crush].
  rewrite raise_S; auto.

  (*arrow type*)
  rewrite H, H0.
  rewrite raise_add_exp; [|crush].
  rewrite raise_S; auto.

  (*new*)
  rewrite H.
  rewrite raise_add_exp; [|crush].
  rewrite raise_S; auto.

  (*funciton*)
  rewrite H, H0, H1.
  rewrite raise_add_exp; [|crush].
  rewrite raise_S; auto.

  (*variable*)
  destruct v as [r|r]; simpl; auto.
  destruct (Nat.eq_dec n r) as [Heq|Heq]; subst;
    [repeat rewrite <- beq_nat_refl; auto
    |unfold raise_nat;
     assert (Htmp : n <> r); [auto|];
     apply (Nat.eqb_neq) in Htmp;
     rewrite Htmp].
  simpl.
  unfold raise_nat.
  destruct (lt_dec r m) as [Hlt1|Hlt1].
  apply Nat.ltb_lt in Hlt1;
    rewrite Hlt1.
  destruct (lt_dec n m) as [Hlt2|Hlt2].
  apply Nat.ltb_lt in Hlt2;
    rewrite Hlt2.
  rewrite Htmp; auto.
  apply (Nat.ltb_nlt) in Hlt2;
    rewrite Hlt2.
  destruct (Nat.eq_dec (n + 1) r) as [Heq2|Heq2]; subst;
    [|apply Nat.eqb_neq in Heq2; rewrite Heq2; auto].
  apply Nat.ltb_lt in Hlt1;
    apply Nat.ltb_nlt in Hlt2; crush.

  apply Nat.ltb_nlt in Hlt1;
    rewrite Hlt1.
  destruct (lt_dec n m) as [Hlt2|Hlt2];
    [apply Nat.ltb_lt in Hlt2;
     rewrite Hlt2|].
  assert (Hneq : n <> r + 1); [|apply Nat.eqb_neq in Hneq; rewrite Hneq; auto].
  apply Nat.ltb_lt in Hlt2;
    apply Nat.ltb_nlt in Hlt1;
    crush.
  apply Nat.ltb_nlt in Hlt2;
    rewrite Hlt2.
  assert (Hneq' : n + 1 <> r + 1);
    [crush
    |apply Nat.eqb_neq in Hneq';
     rewrite Hneq'; auto].
Qed.

Lemma raise_subst_distr_type :
  (forall t p n m, (([p /t n] t) raise_t m) = ([p raise_e m /t n raise_n m] (t raise_t m))).
Proof.
  destruct raise_subst_distr_mutind; crush.
Qed.

Lemma raise_subst_distr_decl_ty :
  (forall s p n m, (([p /s n] s) raise_s m) = ([p raise_e m /s n raise_n m] (s raise_s m))).
Proof.
  destruct raise_subst_distr_mutind; crush.
Qed.

Lemma raise_subst_distr_decl_tys :
  (forall ss p n m, (([p /ss n] ss) raise_ss m) = ([p raise_e m /ss n raise_n m] (ss raise_ss m))).
Proof.
  destruct raise_subst_distr_mutind; crush.
Qed.

Lemma raise_subst_distr_exp :
  (forall e p n m, (([p /e n] e) raise_e m) = ([p raise_e m /e n raise_n m] (e raise_e m))).
Proof.
  destruct raise_subst_distr_mutind; crush.
Qed.

Lemma raise_subst_distr_decl :
  (forall d p n m, (([p /d n] d) raise_d m) = ([p raise_e m /d n raise_n m] (d raise_d m))).
Proof.
  destruct raise_subst_distr_mutind; crush.
Qed.

Lemma raise_subst_distr_decls :
  (forall ds p n m, (([p /ds n] ds) raise_ds m) = ([p raise_e m /ds n raise_n m] (ds raise_ds m))).
Proof.
  destruct raise_subst_distr_mutind; crush.
Qed.

Lemma subst_distr_mutind :
  (forall t n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /t n] ([p2 /t m] t)) = [([p1 /e n] p2) /t m] ([p1 /t n] t)) /\
  (forall s n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /s n] ([p2 /s m] s)) = [([p1 /e n] p2) /s m] ([p1 /s n] s)) /\
  (forall ss n m, n <> m ->
                  forall p1 p2, closed_exp p1 0 ->
                                ([p1 /ss n] ([p2 /ss m] ss)) = [([p1 /e n] p2) /ss m] ([p1 /ss n] ss)) /\
  (forall e n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /e n] ([p2 /e m] e)) = [([p1 /e n] p2) /e m] ([p1 /e n] e)) /\
  (forall d n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /d n] ([p2 /d m] d)) = [([p1 /e n] p2) /d m] ([p1 /d n] d)) /\
  (forall ds n m, n <> m ->
                  forall p1 p2, closed_exp p1 0 ->
                                ([p1 /ds n] ([p2 /ds m] ds)) = [([p1 /e n] p2) /ds m] ([p1 /ds n] ds)).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               try (rewrite H);
               try (rewrite H0);
               try (rewrite H1);
               try (rewrite raise_closed_le_exp with (n:=0); auto);
               try (rewrite raise_subst_distr_exp; simpl;
                    unfold raise_nat;
                    assert (Hnlt : ~ n < 0); [crush|apply Nat.ltb_nlt in Hnlt];
                    rewrite Hnlt, Nat.add_1_r, raise_closed_le_exp with (e:=p1)(n:=0); auto);
               auto].

  (*var*)
  destruct v as [r|r]; simpl; auto.
  destruct (Nat.eq_dec m r) as [Heq1|Heq1];
    destruct (Nat.eq_dec n r) as [Heq2|Heq2];
    [subst;
     contradiction H; auto
    |subst;
     rewrite <- beq_nat_refl;
     apply Nat.eqb_neq in Heq2;
     rewrite Heq2;
     simpl;
     rewrite <- beq_nat_refl;
     auto
    |subst;
     rewrite <- beq_nat_refl;
     apply Nat.eqb_neq in Heq1;
     rewrite Heq1;
     simpl;
     rewrite <- beq_nat_refl;
     rewrite closed_subst_exp;
     auto
    |apply Nat.eqb_neq in Heq1;
     apply Nat.eqb_neq in Heq2;
     rewrite Heq1, Heq2; simpl;
     rewrite Heq1, Heq2; simpl;
     auto].
  apply H0; crush.

Qed.

Lemma subst_distr_type :
  (forall t n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /t n] ([p2 /t m] t)) = [([p1 /e n] p2) /t m] ([p1 /t n] t)).
Proof.
  destruct subst_distr_mutind; crush.
Qed.

Lemma subst_distr_decl_ty :
  (forall s n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /s n] ([p2 /s m] s)) = [([p1 /e n] p2) /s m] ([p1 /s n] s)).
Proof.
  destruct subst_distr_mutind; crush.
Qed.

Lemma subst_distr_decl_tys :
  (forall ss n m, n <> m ->
                  forall p1 p2, closed_exp p1 0 ->
                                ([p1 /ss n] ([p2 /ss m] ss)) = [([p1 /e n] p2) /ss m] ([p1 /ss n] ss)).
Proof.
  destruct subst_distr_mutind; crush.
Qed.

Lemma subst_distr_exp :
  (forall e n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /e n] ([p2 /e m] e)) = [([p1 /e n] p2) /e m] ([p1 /e n] e)).
Proof.
  destruct subst_distr_mutind; crush.
Qed.

Lemma subst_distr_decl :
  (forall d n m, n <> m ->
                 forall p1 p2, closed_exp p1 0 ->
                               ([p1 /d n] ([p2 /d m] d)) = [([p1 /e n] p2) /d m] ([p1 /d n] d)).
Proof.
  destruct subst_distr_mutind; crush.
Qed.

Lemma subst_distr_decls :
  (forall ds n m, n <> m ->
                  forall p1 p2, closed_exp p1 0 ->
                                ([p1 /ds n] ([p2 /ds m] ds)) = [([p1 /e n] p2) /ds m] ([p1 /ds n] ds)).
Proof.
  destruct subst_distr_mutind; crush.
Qed.

Lemma closed_subst_distr_mutind :
  (forall t n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /t n] ([p2 /t m] t)) = ([p2 /t m]([p1 /t n] t))) /\
  
  (forall s n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /s n] ([p2 /s m] s)) = ([p2 /s m]([p1 /s n] s))) /\
  
  (forall ss n m, n <> m ->
                  forall p1 p2, closed_exp p1 0  ->
                                closed_exp p2 0 ->
                                ([p1 /ss n] ([p2 /ss m] ss)) = ([p2 /ss m]([p1 /ss n] ss))) /\
  
  (forall e n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /e n] ([p2 /e m] e)) = ([p2 /e m]([p1 /e n] e))) /\
  
  (forall d n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /d n] ([p2 /d m] d)) = ([p2 /d m]([p1 /d n] d))) /\
  
  (forall ds n m, n <> m ->
                  forall p1 p2, closed_exp p1 0  ->
                                closed_exp p2 0 ->
                                ([p1 /ds n] ([p2 /ds m] ds)) = ([p2 /ds m]([p1 /ds n] ds))).
Proof.

  apply type_exp_mutind; intros; auto;
    try solve [
          simpl;
          try (rewrite H);
          try (rewrite H0);
          try (rewrite H1);
          auto;
          try (rewrite raise_closed_le_exp with (n:=0); auto)
        ].

  (*var*)
  destruct v as [r|r]; simpl; auto.
  destruct (Nat.eq_dec m r) as [Heq1|Heq1];
    destruct (Nat.eq_dec n r) as [Heq2|Heq2];
    subst;
    [contradiction H; auto
    |apply Nat.eqb_neq in Heq2;
     rewrite Heq2;
     simpl;
     rewrite <- beq_nat_refl;
     rewrite closed_subst_exp;
     auto;
     apply H1;
     crush
    |apply Nat.eqb_neq in Heq1;
     rewrite Heq1;
     simpl;
     rewrite <- beq_nat_refl;
     rewrite closed_subst_exp;
     auto;
     apply H0;
     crush
    |apply Nat.eqb_neq in Heq1;
     apply Nat.eqb_neq in Heq2;
     rewrite Heq1, Heq2;
     simpl;
     rewrite Heq1, Heq2;
     auto].
  
Qed.

Lemma closed_subst_distr_type :
  (forall t n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /t n] ([p2 /t m] t)) = ([p2 /t m]([p1 /t n] t))).
Proof.
  destruct closed_subst_distr_mutind; crush.
Qed.

Lemma closed_subst_distr_decl_ty :    
  (forall s n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /s n] ([p2 /s m] s)) = ([p2 /s m]([p1 /s n] s))).
Proof.
  destruct closed_subst_distr_mutind; crush.
Qed.

Lemma closed_subst_distr_decl_tys :
  (forall ss n m, n <> m ->
                  forall p1 p2, closed_exp p1 0  ->
                                closed_exp p2 0 ->
                                ([p1 /ss n] ([p2 /ss m] ss)) = ([p2 /ss m]([p1 /ss n] ss))).
Proof.
  destruct closed_subst_distr_mutind; crush.
Qed.

Lemma closed_subst_distr_exp :
  (forall e n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /e n] ([p2 /e m] e)) = ([p2 /e m]([p1 /e n] e))).
Proof.
  destruct closed_subst_distr_mutind; crush.
Qed.

Lemma closed_subst_distr_decl :    
  (forall d n m, n <> m ->
                 forall p1 p2, closed_exp p1 0  ->
                               closed_exp p2 0 ->
                               ([p1 /d n] ([p2 /d m] d)) = ([p2 /d m]([p1 /d n] d))).
Proof.
  destruct closed_subst_distr_mutind; crush.
Qed.

Lemma closed_subst_distr_decls :    
  (forall ds n m, n <> m ->
                  forall p1 p2, closed_exp p1 0  ->
                                closed_exp p2 0 ->
                                ([p1 /ds n] ([p2 /ds m] ds)) = ([p2 /ds m]([p1 /ds n] ds))).
Proof.
  destruct closed_subst_distr_mutind; crush.
Qed.


Lemma closed_ge_type :
  forall i t n, closed_ty t i ->
                i <= n -> closed_ty t n.
Proof.    
Admitted.

Lemma closed_ge_exp :
  forall i t n, closed_exp t i ->
                i <= n -> closed_exp t n.
Proof.    
Admitted.

Lemma closed_raise_mutind :
  (forall n t, closed_t n t ->
               forall m, m <= n ->
                         closed_t (S n) (t raise_t m)) /\
  
  (forall n s, closed_s n s ->
               forall m, m <= n ->
                         closed_s (S n) (s raise_s m)) /\
  
  (forall n ss, closed_ss n ss ->
                forall m, m <= n ->
                          closed_ss (S n) (ss raise_ss m)) /\
  
  (forall n e, closed_e n e ->
               forall m, m <= n ->
                         closed_e (S n) (e raise_e m)) /\
  
  (forall n d, closed_d n d ->
               forall m, m <= n ->
                         closed_d (S n) (d raise_d m)) /\
  
  (forall n ds, closed_ds n ds ->
                forall m, m <= n ->
                          closed_ds (S n) (ds raise_ds m)).
Proof.
  apply closed_mutind; intros; simpl; auto;
    try solve [assert (Hle1 : S m <= S n);
               crush].

  (*var*)
  destruct x as [r|r]; simpl; auto.
  inversion c; subst.
  apply cl_var, cl_abstract.
  unfold raise_nat.
  destruct (lt_dec r m) as [Hlt|Hlt];
    assert (Hlt' := Hlt);
    [apply Nat.ltb_lt in Hlt
    |apply Nat.ltb_nlt in Hlt];
    rewrite Hlt;
    crush.
Qed.

Lemma closed_raise_type :
  (forall n t, closed_t n t ->
               forall m, m <= n ->
                         closed_t (S n) (t raise_t m)).
Proof.
  destruct closed_raise_mutind; crush.
Qed.

Hint Rewrite closed_raise_type.

Lemma closed_raise_decl_ty :  
  (forall n s, closed_s n s ->
               forall m, m <= n ->
                         closed_s (S n) (s raise_s m)).
Proof.
  destruct closed_raise_mutind; crush.
Qed.

Hint Rewrite closed_raise_decl_ty.

Lemma closed_raise_decl_tys :
  (forall n ss, closed_ss n ss ->
                forall m, m <= n ->
                          closed_ss (S n) (ss raise_ss m)).
Proof.
  destruct closed_raise_mutind; crush.
Qed.

Hint Rewrite closed_raise_decl_tys.

Lemma closed_raise_exp :
  (forall n e, closed_e n e ->
               forall m, m <= n ->
                         closed_e (S n) (e raise_e m)).
Proof.
  destruct closed_raise_mutind; crush.
Qed.

Hint Rewrite closed_raise_exp.

Lemma closed_raise_decl :  
  (forall n d, closed_d n d ->
               forall m, m <= n ->
                         closed_d (S n) (d raise_d m)).
Proof.
  destruct closed_raise_mutind; crush.
Qed.

Hint Rewrite closed_raise_decl.

Lemma closed_raise_decls :
  (forall n ds, closed_ds n ds ->
                forall m, m <= n ->
                          closed_ds (S n) (ds raise_ds m)).
Proof.
  destruct closed_raise_mutind; crush.
Qed.

Hint Rewrite closed_raise_decls.



Lemma closed_subst_eq_mutind :
  (forall t p n, closed_e n p -> closed_t n ([p /t n]t)) /\
  
  (forall s p n, closed_e n p -> closed_s n ([p /s n]s)) /\
  
  (forall ss p n, closed_e n p -> closed_ss n ([p /ss n]ss)) /\
  
  (forall e p n, closed_e n p -> closed_e n ([p /e n]e)) /\
  
  (forall d p n, closed_e n p -> closed_d n ([p /d n]d)) /\
  
  (forall ds p n, closed_e n p -> closed_ds n ([p /ds n]ds)).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               try (apply cl_str);
               try (apply cl_arr);
               try (apply cl_new);
               try (apply cl_fn);
               try (apply H);
               try (apply H0);
               try (apply H1);
               try apply closed_raise_exp;
               crush].

  destruct v as [x|x]; simpl; auto.
  destruct (Nat.eq_dec n x) as [|Hneq];
    [subst n;
     rewrite <- beq_nat_refl;
     auto
    |assert (Hneqb := Hneq);
     apply Nat.eqb_neq in Hneqb;
     rewrite Hneqb;
     auto].
Qed.

Lemma closed_subst_eq_type :
  (forall t p n, closed_e n p -> closed_t n ([p /t n]t)).
Proof.
  destruct closed_subst_eq_mutind; crush.
Qed.

Lemma closed_subst_eq_decl_ty :
  (forall s p n, closed_e n p -> closed_s n ([p /s n]s)).
Proof.
  destruct closed_subst_eq_mutind; crush.
Qed.

Lemma closed_subst_eq_decl_tys :
  (forall ss p n, closed_e n p -> closed_ss n ([p /ss n]ss)).
Proof.
  destruct closed_subst_eq_mutind; crush.
Qed.

Lemma closed_subst_eq_exp :  
  (forall e p n, closed_e n p -> closed_e n ([p /e n]e)).
Proof.
  destruct closed_subst_eq_mutind; crush.
Qed.

Lemma closed_subst_eq_decl :
  (forall d p n, closed_e n p -> closed_d n ([p /d n]d)).
Proof.
  destruct closed_subst_eq_mutind; crush.
Qed.

Lemma closed_subst_eq_decls :
  (forall ds p n, closed_e n p -> closed_ds n ([p /ds n]ds)).
Proof.
  destruct closed_subst_eq_mutind; crush.
Qed.

Lemma closed_rename_mutind :
  (forall t n m, closed_t m (t [n maps_t m]) ->
                 closed_t n t) /\
  
  (forall s n m, closed_s m (s [n maps_s m]) ->
                 closed_s n s) /\
  
  (forall ss n m, closed_ss m (ss [n maps_ss m]) ->
                  closed_ss n ss) /\
  
  (forall e n m, closed_e m (e [n maps_e m]) ->
                 closed_e n e) /\
  
  (forall d n m, closed_d m (d [n maps_d m]) ->
                 closed_d n d) /\
  
  (forall ds n m, closed_ds m (ds [n maps_ds m]) ->
                  closed_ds n ds).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto;
    try solve [inversion H0; subst; eauto];
    try solve [inversion H1; subst; eauto];
    try solve [inversion H2; subst; eauto].

  (*var*)
  destruct v as [r|r]; simpl in H; auto.
  rewrite rename_rewrite in H.
  destruct (Nat.eq_dec r n) as [Heq|Heq];
    [subst; rewrite <- beq_nat_refl in H;
     inversion H; subst;
     inversion H2; auto
    |auto].
Qed.

Lemma closed_rename_type :
  (forall t n m, closed_t m (t [n maps_t m]) ->
                 closed_t n t).
Proof.
  destruct closed_rename_mutind; crush.
Qed.

Lemma closed_rename_decl_ty :
  (forall s n m, closed_s m (s [n maps_s m]) ->
                 closed_s n s).
Proof.
  destruct closed_rename_mutind; crush.
Qed.

Lemma closed_rename_decl_tys :
  (forall ss n m, closed_ss m (ss [n maps_ss m]) ->
                  closed_ss n ss).
Proof.
  destruct closed_rename_mutind; crush.
Qed.

Lemma closed_rename_exp :
  (forall e n m, closed_e m (e [n maps_e m]) ->
                 closed_e n e).
Proof.
  destruct closed_rename_mutind; crush.
Qed.

Lemma closed_rename_decl :
  (forall d n m, closed_d m (d [n maps_d m]) ->
                 closed_d n d).
Proof.
  destruct closed_rename_mutind; crush.
Qed.

Lemma closed_rename_decls :
  (forall ds n m, closed_ds m (ds [n maps_ds m]) ->
                  closed_ds n ds).
Proof.
  destruct closed_rename_mutind; crush.
Qed.

Lemma closed_rename_rewrite_mutind :
  (forall n t, closed_t n t ->
               forall m, (t [n maps_t m]) = t) /\
  
  (forall n s, closed_s n s ->
               forall m, (s [n maps_s m]) = s) /\
  
  (forall n ss, closed_ss n ss ->
                forall m, (ss [n maps_ss m]) = ss) /\
  
  (forall n e, closed_e n e ->
               forall m, (e [n maps_e m]) = e) /\
  
  (forall n d, closed_d n d ->
               forall m, (d [n maps_d m]) = d) /\
  
  (forall n ds, closed_ds n ds ->
                forall m, (ds [n maps_ds m]) = ds).
Proof.
  apply closed_mutind; intros; simpl in *; eauto;
    try solve [try (rewrite H);
               try (rewrite H0);
               try (rewrite H1);
               auto].

  (*var*)
  destruct x as [r|r]; simpl; auto.
  inversion c; subst.
  rewrite rename_rewrite.
  assert (Heq : r <> n);
    [crush
    |apply Nat.eqb_neq in Heq].
  rewrite Heq; auto.
Qed.

Lemma closed_rename_rewrite_type :
  (forall n t, closed_t n t ->
               forall m, (t [n maps_t m]) = t).
Proof.
  destruct closed_rename_rewrite_mutind; crush.
Qed.

Hint Rewrite closed_rename_rewrite_type.
Hint Resolve closed_rename_rewrite_type.

Lemma closed_rename_rewrite_decl_ty :
  (forall n s, closed_s n s ->
               forall m, (s [n maps_s m]) = s).
Proof.
  destruct closed_rename_rewrite_mutind; crush.
Qed.

Hint Rewrite closed_rename_rewrite_decl_ty.
Hint Resolve closed_rename_rewrite_decl_ty.

Lemma closed_rename_rewrite_decl_tys :
  (forall n ss, closed_ss n ss ->
                forall m, (ss [n maps_ss m]) = ss).
Proof.
  destruct closed_rename_rewrite_mutind; crush.
Qed.

Hint Rewrite closed_rename_rewrite_decl_tys.
Hint Resolve closed_rename_rewrite_decl_tys.

Lemma closed_rename_rewrite_exp :
  (forall n e, closed_e n e ->
               forall m, (e [n maps_e m]) = e).
Proof.
  destruct closed_rename_rewrite_mutind; crush.
Qed.

Hint Rewrite closed_rename_rewrite_exp.
Hint Resolve closed_rename_rewrite_exp.

Lemma closed_rename_rewrite_decl :
  (forall n d, closed_d n d ->
               forall m, (d [n maps_d m]) = d).
Proof.
  destruct closed_rename_rewrite_mutind; crush.
Qed.

Hint Rewrite closed_rename_rewrite_decl.
Hint Resolve closed_rename_rewrite_decl.

Lemma closed_rename_rewrite_decls :
  (forall n ds, closed_ds n ds ->
                forall m, (ds [n maps_ds m]) = ds).
Proof.
  destruct closed_rename_rewrite_mutind; crush.
Qed.

Hint Rewrite closed_rename_rewrite_decls.
Hint Resolve closed_rename_rewrite_decls.

Lemma notin_rename_mutind :
  (forall e t, e notin_t t ->
               forall n, closed_e n e ->
                         forall m, e notin_t (t [m maps_t n])) /\
  
  (forall e s, e notin_s s ->
               forall n, closed_e n e ->
                         forall m, e notin_s (s [m maps_s n])) /\
  
  (forall e ss, e notin_ss ss ->
                forall n, closed_e n e ->
                          forall m, e notin_ss (ss [m maps_ss n])) /\
  
  (forall e e', e notin_e e' ->
                forall n, closed_e n e ->
                          forall m, e notin_e (e' [m maps_e n])) /\
  
  (forall e d, e notin_d d ->
               forall n, closed_e n e ->
                         forall m, e notin_d (d [m maps_d n])) /\
  
  (forall e ds, e notin_ds ds ->
                forall n, closed_e n e ->
                          forall m, e notin_ds (ds [m maps_ds n])).
Proof.
  apply notin_mutind; intros;
    try solve [simpl; auto];
    try solve [try (apply ni_arr; auto; apply H0);
               try (apply ni_str; auto; apply H);
               apply closed_raise_exp; crush].

  (*var*)
  simpl.
  destruct x as [r|r]; auto.
  simpl.
  rewrite rename_rewrite.
  destruct (Nat.eq_dec r m) as [Heq|Heq];
    [subst; rewrite <- beq_nat_refl
    |apply Nat.eqb_neq in Heq;
     rewrite Heq; auto].
  apply ni_var;
    intro Hcontra; subst.
  inversion H; subst.
  inversion H2; auto.

  (*cast*)
  simpl;
    apply ni_cast; auto.
  assert (Hrem : (e' cast t) [m maps_e n2] = ((e' [m maps_e n2]) cast (t [m maps_t n2])));
    [auto
    |rewrite <- Hrem].
  intro Hcontra;
    rewrite Hcontra in H1.
  apply closed_rename_exp in H1.
  rewrite closed_rename_rewrite_exp in Hcontra; auto.

  (*fn*)
  simpl; apply ni_fn; auto;
    try (try (apply H0);
         try (apply H1);
         apply closed_raise_exp; crush).
  assert (Hrem : (fn t1 [m maps_t n3] in_exp e' [S m maps_e S n3] off (t2 [S m maps_t S n3])) = ((fn t1 in_exp e' off t2)[m maps_e n3]));
    [auto
    |rewrite Hrem].
  intro Hcontra;
    rewrite Hcontra in H2.
  apply closed_rename_exp in H2.
  rewrite closed_rename_rewrite_exp in Hcontra; auto.

  (*app*)
  simpl; apply ni_app; auto.
  assert (Hrem : (e_app (e1 [m maps_e n2]) (e2 [m maps_e n2]) = ((e_app e1 e2)[m maps_e n2])));
    [auto
    |rewrite Hrem].
  intro Hcontra;
    rewrite Hcontra in H1.
  apply closed_rename_exp in H1.
  rewrite closed_rename_rewrite_exp in Hcontra; auto.

  (*fn*)
  simpl; apply ni_acc; auto.
  assert (Hrem : (e_acc (e' [m maps_e n1]) l) = ((e_acc e' l)[m maps_e n1]));
    [auto
    |rewrite Hrem].
  intro Hcontra;
    rewrite Hcontra in H0.
  apply closed_rename_exp in H0.
  rewrite closed_rename_rewrite_exp in Hcontra; auto.

  (*new*)
  simpl; apply ni_new; auto;
    try (try (apply H);
         apply closed_raise_exp; crush).
  assert (Hrem : (new (ds [S m maps_ds S n1])) = ((new ds)[m maps_e n1]));
    [auto
    |rewrite Hrem].
  intro Hcontra;
    rewrite Hcontra in H0.
  apply closed_rename_exp in H0.
  rewrite closed_rename_rewrite_exp in Hcontra; auto.
Qed.

Lemma notin_rename_type :
  (forall e t, e notin_t t ->
               forall n, closed_e n e ->
                         forall m, e notin_t (t [m maps_t n])).
Proof.
  destruct notin_rename_mutind; crush.
Qed.

Lemma notin_rename_decl_ty :
  (forall e s, e notin_s s ->
               forall n, closed_e n e ->
                         forall m, e notin_s (s [m maps_s n])).
Proof.
  destruct notin_rename_mutind; crush.
Qed.

Lemma notin_rename_decl_tys :    
  (forall e ss, e notin_ss ss ->
                forall n, closed_e n e ->
                          forall m, e notin_ss (ss [m maps_ss n])).
Proof.
  destruct notin_rename_mutind; crush.
Qed.

Lemma notin_rename_exp :    
  (forall e e', e notin_e e' ->
                forall n, closed_e n e ->
                          forall m, e notin_e (e' [m maps_e n])).
Proof.
  destruct notin_rename_mutind; crush.
Qed.

Lemma notin_rename_decl :
  (forall e d, e notin_d d ->
               forall n, closed_e n e ->
                         forall m, e notin_d (d [m maps_d n])).
Proof.
  destruct notin_rename_mutind; crush.
Qed.

Lemma notin_rename_decls :
  (forall e ds, e notin_ds ds ->
                forall n, closed_e n e ->
                          forall m, e notin_ds (ds [m maps_ds n])).
Proof.
  destruct notin_rename_mutind; crush.
Qed.

Lemma synsize_notin_mutind :
  (forall t e, synsize_e e > synsize_t t ->
               e notin_t t) /\
  (forall s e, synsize_e e > synsize_s s ->
               e notin_s s) /\
  (forall ss e, synsize_e e > synsize_ss ss ->
                e notin_ss ss) /\
  (forall e' e, synsize_e e > synsize_e e' ->
                e notin_e e') /\
  (forall d e, synsize_e e > synsize_d d ->
               e notin_d d) /\
  (forall ds e, synsize_e e > synsize_ds ds ->
                e notin_ds ds).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto;
    try solve [crush].

  (*str*)
  apply ni_str.
  rewrite <- synsize_raise_exp with (n:=0) in H0.
  crush.

  (*arr*)
  apply ni_arr.
  apply H; crush.
  rewrite <- synsize_raise_exp with (n:=0) in H1;
    apply H0;
    crush.

  (*new*)
  apply ni_new;
    [|crush].
  rewrite <- synsize_raise_exp with (n:=0) in H0.
  crush.

  (*app*)
  apply ni_app;
    crush.

  (*fn*)
  apply ni_fn;
    [crush
    |
    |
    |crush];
    rewrite <- synsize_raise_exp with (n:=0) in H2;
    crush.

  (*acc*)
  apply ni_acc;
    crush.

  (*var*)
  apply ni_var; crush.

  (*loc*)
  apply ni_loc; crush.

  (*cast*)
  apply ni_cast; crush.
Qed.

Lemma synsize_notin_type :
  (forall t e, synsize_e e > synsize_t t ->
               e notin_t t).
Proof.
  destruct synsize_notin_mutind; crush.
Qed.

Lemma synsize_notin_decl_ty :
  (forall s e, synsize_e e > synsize_s s ->
               e notin_s s).
Proof.
  destruct synsize_notin_mutind; crush.
Qed.

Lemma synsize_notin_decl_tys :
  (forall ss e, synsize_e e > synsize_ss ss ->
                e notin_ss ss).
Proof.
  destruct synsize_notin_mutind; crush.
Qed.

Lemma synsize_notin_exp :
  (forall e' e, synsize_e e > synsize_e e' ->
                e notin_e e').
Proof.
  destruct synsize_notin_mutind; crush.
Qed.

Lemma synsize_notin_decl :
  (forall d e, synsize_e e > synsize_d d ->
               e notin_d d).
Proof.
  destruct synsize_notin_mutind; crush.
Qed.

Lemma synsize_notin_decls :
  (forall ds e, synsize_e e > synsize_ds ds ->
                e notin_ds ds).
Proof.
  destruct synsize_notin_mutind; crush.
Qed.



Lemma root_raise_alt :
  (forall r p, root r p ->
               forall n, root (r raise_e n) (p raise_e n)).
Proof.
  intros r p Hroot;
    induction Hroot; simpl in *; auto.
Qed.

Hint Rewrite root_raise_alt.
Hint Resolve root_raise_alt.

Lemma root_in_exp :
  forall r p, root r p ->
              ~ (r notin_e p).
Proof.
  intros r p Hroot;
    induction Hroot; simpl in *;
      intros Hcontra;
      try solve [inversion Hcontra; auto].
Qed.

Lemma root_notin_mutind :
  (forall t r p, root r p ->
                 r notin_t t ->
                 p notin_t t) /\
  
  (forall s r p, root r p ->
                 r notin_s s ->
                 p notin_s s) /\
  
  (forall ss r p, root r p ->
                  r notin_ss ss ->
                  p notin_ss ss) /\
  
  (forall e r p, root r p ->
                 r notin_e e ->
                 p notin_e e) /\
  
  (forall d r p, root r p ->
                 r notin_d d ->
                 p notin_d d) /\
  
  (forall ds r p, root r p ->
                  r notin_ds ds ->
                  p notin_ds ds).
Proof.
  apply type_exp_mutind; intros; simpl; auto;
    try solve [try (inversion H1; apply ni_str);
               try (inversion H1; apply ni_sel);
               try (inversion H2; apply ni_arr);
               try (inversion H1; apply nit_upper);
               try (inversion H1; apply nit_lower);
               try (inversion H1; apply nit_equal);
               try (inversion H1; apply nit_value);
               try (inversion H2; apply nit_con);
               try (inversion H1; apply nie_equal);
               try (inversion H2; apply nie_value);
               try (inversion H2; apply nie_con);
               try (eapply H; eauto);
               try (eapply H0; eauto)].

  (*new*)
  inversion H1; subst.
  apply ni_new.
  eapply H; eauto.
  intro Hcontra; subst.
  contradiction (root_in_exp H0).

  (*app*)
  inversion H2; subst.
  apply ni_app.
  eapply H; eauto.
  eapply H0; eauto.
  intro Hcontra; subst.
  contradiction (root_in_exp H1).

  (*fn*)
  inversion H3; subst.
  apply ni_fn.
  eapply H; eauto.
  eapply H0; eauto.
  eapply H1; eauto.
  intro Hcontra; subst.
  contradiction (root_in_exp H2).

  (*acc*)
  inversion H1; subst.
  apply ni_acc.
  eapply H; eauto.
  intro Hcontra; subst.
  contradiction (root_in_exp H0).

  (*var*)
  destruct v as [x|x];
    inversion H0; subst;
      apply ni_var;
      intro Hcontra;
      subst;
      inversion H; subst; auto.

  (*loc*)
  inversion H0; subst;
    apply ni_loc;
    intro Hcontra;
    subst;
    inversion H; subst; auto.

  (*cast*)
  inversion H2; subst.
  apply ni_cast.
  eapply H; eauto.
  eapply H0; eauto.
  intro Hcontra; subst.
  contradiction (root_in_exp H1).
Qed.

Lemma root_notin_type :
  (forall t r p, root r p ->
                 r notin_t t ->
                 p notin_t t).
Proof.
  destruct root_notin_mutind; crush.
Qed.

Lemma root_notin_decl_ty :
  (forall s r p, root r p ->
                 r notin_s s ->
                 p notin_s s).
Proof.
  destruct root_notin_mutind; crush.
Qed.

Lemma root_notin_decl_tys :    
  (forall ss r p, root r p ->
                  r notin_ss ss ->
                  p notin_ss ss).
Proof.
  destruct root_notin_mutind; crush.
Qed.

Lemma root_notin_exp :    
  (forall e r p, root r p ->
                 r notin_e e ->
                 p notin_e e).
Proof.
  destruct root_notin_mutind; crush.
Qed.

Lemma root_notin_decl :    
  (forall d r p, root r p ->
                 r notin_d d ->
                 p notin_d d).
Proof.
  destruct root_notin_mutind; crush.
Qed.

Lemma root_notin_decls :
  (forall ds r p, root r p ->
             r notin_ds ds ->
             p notin_ds ds).
Proof.
  destruct root_notin_mutind; crush.
Qed.

Lemma root_notin_env :
  forall G r p, root r p ->
           r notin_env G ->
           p notin_env G.
Proof.
  intros;
    intros t Hin.
  eapply root_notin_type; eauto.
Qed.

Lemma root_closed :
  forall r p, root r p ->
         forall n, closed_exp r n.
Proof.
  intros r p Hroot;
    induction Hroot;
    simpl in *;
    auto.
Qed.


Lemma wf_rjump_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall i n, length G <= i ->
                   (t [i] rjump_t n) = t).
Proof.
  intros.
  apply wf_lt_type in H; auto.
  apply lt_n_ge_type with (m:=i) in H; auto.
  apply lt_rjump_type; auto.
Qed.

Lemma wf_rjump_decl_ty :
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall i n, length G <= i ->
                   (s [i] rjump_s n) = s).
Proof.
  intros.
  apply wf_lt_decl_ty in H; auto.
  apply lt_n_ge_decl_ty with (m:=i) in H; auto.
  apply lt_rjump_decl_ty; auto.
Qed.

Lemma wf_rjump_decl_tys :
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall i n, length G <= i ->
                    (ss [i] rjump_ss n) = ss).
Proof.
  intros.
  apply wf_lt_decl_tys in H; auto.
  apply lt_n_ge_decl_tys with (m:=i) in H; auto.
  apply lt_rjump_decl_tys; auto.
Qed.

Lemma wf_rjump_exp :
  (forall Sig G e, Sig en G vdash e wf_e ->
            forall i n, length G <= i ->
                   (e [i] rjump_e n) = e).
Proof.
  intros.
  apply wf_lt_exp in H; auto.
  apply lt_n_ge_exp with (m:=i) in H; auto.
  apply lt_rjump_exp; auto.
Qed.

Lemma wf_rjump_decl :
  (forall Sig G d, Sig en G vdash d wf_d ->
                   forall i n, length G <= i ->
                               (d [i] rjump_d n) = d).
Proof.
  intros.
  apply wf_lt_decl in H; auto.
  apply lt_n_ge_decl with (m:=i) in H; auto.
  apply lt_rjump_decl; auto.
Qed.

Lemma wf_rjump_decls :
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
                    forall i n, length G <= i ->
                                (ds [i] rjump_ds n) = ds).
Proof.
  intros.
  apply wf_lt_decls in H; auto.
  apply lt_n_ge_decls with (m:=i) in H; auto.
  apply lt_rjump_decls; auto.
Qed.

Lemma closed_mapping :
  forall G n t, n mapsto t elem G ->
                forall m, closed_env G m ->
                          closed_ty t m.
Proof.
  intros.
  unfold mapping in H.
  apply get_in in H;
    apply in_rev in H;
    apply H0 in H; auto.
Qed.

Lemma closed_typing_p :
  forall Sig G p t, Sig en G vdash p pathType t ->
                    forall m, closed_env Sig m ->
                              closed_env G m ->
                              closed_exp p m ->
                              closed_ty t m.
Proof.
  intros Sig G p t Htyp; inversion Htyp; intros; subst.

  apply closed_mapping with (G:=G)(n:=n); auto.

  apply closed_mapping with (G:=Sig)(n:=i); auto.

  apply closed_exp_cast in H6; crush.
  
Qed.

(*
  Lemma closed_raise_zero :
    (forall t n, closed_ty t n ->
            closed_ty (t raise_t 0) (S n)) /\
    (forall s n, closed_decl_ty s n ->
            closed_decl_ty (s raise_s 0) (S n)) /\
    (forall ss n, closed_decl_tys ss n ->
             closed_decl_tys (ss raise_ss 0) (S n)) /\
    (forall e n, closed_exp e n ->
            closed_exp (e raise_e 0) (S n)) /\
    (forall d n, closed_decl d n ->
            closed_decl (d raise_d 0) (S n)) /\
    (forall ds n, closed_decls ds n ->
             closed_decls (ds raise_ds 0) (S n)).
  Proof.
    apply type_exp_mutind; intros; auto.

    simpl.
  Qed.*)

Lemma closed_subst_hole_mutind :
  (forall t n, closed_ty t (S n) ->
               forall e, closed_exp e n ->
                         closed_ty ([e /t n] t) n) /\
  
  (forall s n, closed_decl_ty s (S n) ->
               forall e, closed_exp e n ->
                         closed_decl_ty ([e /s n] s) n) /\
  
  (forall ss n, closed_decl_tys ss (S n) ->
                forall e, closed_exp e n ->
                          closed_decl_tys ([e /ss n] ss) n) /\
  
  (forall e n, closed_exp e (S n) ->
               forall e', closed_exp e' n ->
                          closed_exp ([e' /e n] e) n) /\
  
  (forall d n, closed_decl d (S n) ->
               forall e, closed_exp e n ->
                         closed_decl ([e /d n] d) n) /\
  
  (forall ds n, closed_decls ds (S n) ->
                forall e, closed_exp e n ->
                          closed_decls ([e /ds n] ds) n).
Proof.
  apply type_exp_mutind; intros; simpl; auto;
    try solve [crush].

  (*var*)
  destruct v as [|r]; [crush|].
  destruct (Nat.eq_dec n r) as [Heq|Heq];
    [subst; rewrite <- beq_nat_refl; auto
    |apply Nat.eqb_neq in Heq;
     rewrite Heq].
  intros n' Hle.
  destruct (le_lt_or_eq n n'); subst; auto.
  apply cl_var, cl_abstract.
  apply Nat.eqb_neq in Heq; auto.
Qed.

Lemma closed_subst_hole_type :
  (forall t n, closed_ty t (S n) ->
               forall e, closed_exp e n ->
                         closed_ty ([e /t n] t) n).
Proof.
  destruct closed_subst_hole_mutind; crush.
Qed.

Hint Rewrite closed_subst_hole_type.
Hint Resolve closed_subst_hole_type.

Lemma closed_subst_hole_decl_ty :
  (forall s n, closed_decl_ty s (S n) ->
               forall e, closed_exp e n ->
                         closed_decl_ty ([e /s n] s) n).
Proof.
  destruct closed_subst_hole_mutind; crush.
Qed.

Hint Rewrite closed_subst_hole_decl_ty.
Hint Resolve closed_subst_hole_decl_ty.

Lemma closed_subst_hole_decl_tys :
  (forall ss n, closed_decl_tys ss (S n) ->
                forall e, closed_exp e n ->
                          closed_decl_tys ([e /ss n] ss) n).
Proof.
  destruct closed_subst_hole_mutind; crush.
Qed.

Hint Rewrite closed_subst_hole_decl_tys.
Hint Resolve closed_subst_hole_decl_tys.

Lemma closed_subst_hole_exp :
  (forall e n, closed_exp e (S n) ->
               forall e', closed_exp e' n ->
                          closed_exp ([e' /e n] e) n).
Proof.
  destruct closed_subst_hole_mutind; crush.
Qed.

Hint Rewrite closed_subst_hole_exp.
Hint Resolve closed_subst_hole_exp.

Lemma closed_subst_hole_decl :
  (forall d n, closed_decl d (S n) ->
               forall e, closed_exp e n ->
                         closed_decl ([e /d n] d) n).
Proof.
  destruct closed_subst_hole_mutind; crush.
Qed.

Hint Rewrite closed_subst_hole_decl.
Hint Resolve closed_subst_hole_decl.

Lemma closed_subst_hole_decls :
  (forall ds n, closed_decls ds (S n) ->
                forall e, closed_exp e n ->
                          closed_decls ([e /ds n] ds) n).
Proof.
  destruct closed_subst_hole_mutind; crush.
Qed.

Hint Rewrite closed_subst_hole_decls.
Hint Resolve closed_subst_hole_decls.

Lemma closed_in_dty :
  forall s ss, in_dty s ss ->
               forall n, closed_decl_tys ss n ->
                         closed_decl_ty s n.
Proof.
  intros s ss Hin; induction Hin; intros;

    apply closed_decl_tys_con in H; destruct H; auto.
Qed.

Lemma closed_remove_subst_hole_mutind :
  (forall t e n, closed_ty ([e /t n] t) n ->
                 closed_ty t (S n)) /\
  
  (forall s e n, closed_decl_ty ([e /s n] s) n ->
                 closed_decl_ty s (S n)) /\
  
  (forall ss e n, closed_decl_tys ([e /ss n] ss) n ->
                  closed_decl_tys ss (S n)) /\
  
  (forall e e' n, closed_exp ([e' /e n] e) n ->
                  closed_exp e (S n)) /\
  
  (forall d e n, closed_decl ([e /d n] d) n ->
                 closed_decl d (S n)) /\
  
  (forall ds e n, closed_decls ([e /ds n] ds) n ->
                  closed_decls ds (S n)).
Proof.
  apply type_exp_mutind; intros; auto.

  (*str*)
  simpl in H0;
    apply closed_ty_str in H0.
  eapply closed_ty_str.
  eapply H; eauto.

  (*sel*)
  simpl in H0;
    apply closed_ty_sel in H0.
  eapply closed_ty_sel.
  eapply H; eauto.

  (*arr*)
  simpl in H1;
    apply closed_ty_arr in H1;
    destruct H1.
  eapply closed_ty_arr; split;
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto].

  (*upper type*)
  simpl in H0;
    apply closed_decl_ty_upper in H0.
  eapply closed_decl_ty_upper.
  eapply H; eauto.

  (*lower type*)
  simpl in H0;
    apply closed_decl_ty_lower in H0.
  eapply closed_decl_ty_lower.
  eapply H; eauto.

  (*equal type*)
  simpl in H0;
    apply closed_decl_ty_equal in H0.
  eapply closed_decl_ty_equal.
  eapply H; eauto.

  (*value type*)
  simpl in H0;
    apply closed_decl_ty_value in H0.
  eapply closed_decl_ty_value.
  eapply H; eauto.

  (*cons type*)
  simpl in H1;
    apply closed_decl_tys_con in H1;
    destruct H1.
  eapply closed_decl_tys_con; split;
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto].

  (*new*)
  simpl in H0;
    apply closed_exp_new in H0.
  eapply closed_exp_new.
  eapply H; eauto.

  (*app*)
  simpl in H1;
    apply closed_exp_app in H1;
    destruct H1.
  eapply closed_exp_app; split;
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto].

  (*fn*)
  simpl in H2;
    apply closed_exp_fn in H2;
    destruct H2 as [Ha Hb];
    destruct Hb.
  eapply closed_exp_fn; split; [|split];
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto];
    try solve [eapply H1; eauto].

  (*acc*)
  simpl in H0;
    apply closed_exp_acc in H0.
  eapply closed_exp_acc.
  eapply H; eauto.

  (*var*)
  destruct v as [x|x]; simpl in H;
    auto.
  destruct (Nat.eq_dec n x) as [|Heq];
    [subst; intros m Hle; auto
    |apply Nat.eqb_neq in Heq;
     rewrite Heq in H;
     intros m Hle;
     apply H; crush].
  apply cl_var, cl_abstract; crush.

  (*cast*)
  simpl in H1;
    apply closed_exp_cast in H1;
    destruct H1.
  eapply closed_exp_cast; split;
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto].

  (*equal decl*)
  simpl in H0;
    apply closed_decl_equal in H0.
  eapply closed_decl_equal.
  eapply H; eauto.

  (*value decl*)
  simpl in H1;
    apply closed_decl_value in H1;
    destruct H1.
  eapply closed_decl_value; split;
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto].
  
  (*cons decl*)
  simpl in H1;
    apply closed_decls_con in H1;
    destruct H1.
  eapply closed_decls_con; split;
    try solve [eapply H; eauto];
    try solve [eapply H0; eauto].
  
Qed.

Lemma closed_remove_subst_hole_type :
  (forall t e n, closed_ty ([e /t n] t) n ->
                 closed_ty t (S n)).
Proof.
  destruct closed_remove_subst_hole_mutind; crush.
Qed.

Lemma closed_remove_subst_hole_decl_ty :
  (forall s e n, closed_decl_ty ([e /s n] s) n ->
                 closed_decl_ty s (S n)).
Proof.
  destruct closed_remove_subst_hole_mutind; crush.
Qed.

Lemma closed_remove_subst_hole_decl_tys :
  (forall ss e n, closed_decl_tys ([e /ss n] ss) n ->
                  closed_decl_tys ss (S n)).
Proof.
  destruct closed_remove_subst_hole_mutind; crush.
Qed.

Lemma closed_remove_subst_hole_exp :
  (forall e e' n, closed_exp ([e' /e n] e) n ->
                  closed_exp e (S n)).
Proof.
  destruct closed_remove_subst_hole_mutind; crush.
Qed.

Lemma closed_remove_subst_hole_decl :
  (forall d e n, closed_decl ([e /d n] d) n ->
                 closed_decl d (S n)).
Proof.
  destruct closed_remove_subst_hole_mutind; crush.
Qed.

Lemma closed_remove_subst_hole_decls :
  (forall ds e n, closed_decls ([e /ds n] ds) n ->
                  closed_decls ds (S n)).
Proof.
  destruct closed_remove_subst_hole_mutind; crush.
Qed.

Lemma closed_n_subst_components_mutind :
  (forall t n, closed_t n t ->
               forall p, closed_e n p ->
                         forall m, closed_t n ([p /t m] t)) /\
  
  (forall s n, closed_s n s->
               forall p, closed_e n p ->
                         forall m, closed_s n ([p /s m] s)) /\
  
  (forall ss n, closed_ss n ss ->
                forall p, closed_e n p ->
                          forall m, closed_ss n ([p /ss m] ss)) /\
  
  (forall e n, closed_e n e ->
               forall p, closed_e n p ->
                         forall m, closed_e n ([p /e m] e)) /\
  
  (forall d n, closed_d n d ->
               forall p, closed_e n p ->
                         forall m, closed_d n ([p /d m] d)) /\
  
  (forall ds n, closed_ds n ds ->
                forall p, closed_e n p ->
                          forall m, closed_ds n ([p /ds m] ds)).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               apply cl_fn;
               try (apply H);
               try (apply H0);
               try (apply H1);
               try (inversion H2; auto);
               try apply closed_raise_exp;
               crush];
    try solve [simpl;
               try (apply cl_sel);
               try (apply cl_str);
               try (apply cls_upper);
               try (apply cls_lower);
               try (apply cls_equal);
               try (apply cls_value);
               try (apply cl_new);
               try (apply cl_acc);
               try (apply cld_equal);
               apply H;
               inversion H0; auto;
               try apply closed_raise_exp;
               crush];
    try solve [simpl;
               try (apply cl_arr);
               try (apply cl_cast);
               try (apply cl_app);
               try (apply cls_con);
               try (apply cld_con);
               try (apply H);
               try (apply H0);
               inversion H1; auto;
               try apply closed_raise_exp;
               crush].

  destruct v as [|x]; auto.
  simpl; destruct (m =? x); auto.
Qed.

Lemma closed_n_subst_components_type :
  (forall t n, closed_t n t ->
               forall p, closed_e n p ->
                         forall m, closed_t n ([p /t m] t)).
Proof.
  destruct closed_n_subst_components_mutind; crush.
Qed.

Lemma closed_n_subst_components_decl_ty :
  (forall s n, closed_s n s->
               forall p, closed_e n p ->
                         forall m, closed_s n ([p /s m] s)).
Proof.
  destruct closed_n_subst_components_mutind; crush.
Qed.

Lemma closed_n_subst_components_decl_tys :
  (forall ss n, closed_ss n ss ->
                forall p, closed_e n p ->
                          forall m, closed_ss n ([p /ss m] ss)).
Proof.
  destruct closed_n_subst_components_mutind; crush.
Qed.

Lemma closed_n_subst_components_exp :    
  (forall e n, closed_e n e ->
               forall p, closed_e n p ->
                         forall m, closed_e n ([p /e m] e)).
Proof.
  destruct closed_n_subst_components_mutind; crush.
Qed.

Lemma closed_n_subst_components_decl :    
  (forall d n, closed_d n d ->
               forall p, closed_e n p ->
                         forall m, closed_d n ([p /d m] d)).
Proof.
  destruct closed_n_subst_components_mutind; crush.
Qed.

Lemma closed_n_subst_components_decls :    
  (forall ds n, closed_ds n ds ->
                forall p, closed_e n p ->
                          forall m, closed_ds n ([p /ds m] ds)).
Proof.
  destruct closed_n_subst_components_mutind; crush.
Qed.

Lemma closed_subst_components_mutind :
  (forall t n, closed_ty t n ->
               forall p, closed_exp p n ->
                         forall m, closed_ty ([p /t m] t) n) /\
  
  (forall s n, closed_decl_ty s n ->
               forall p, closed_exp p n ->
                         forall m, closed_decl_ty ([p /s m] s) n) /\
  
  (forall ss n, closed_decl_tys ss n ->
                forall p, closed_exp p n ->
                          forall m, closed_decl_tys ([p /ss m] ss) n) /\
  
  (forall e n, closed_exp e n ->
               forall p, closed_exp p n ->
                         forall m, closed_exp ([p /e m] e) n) /\
  
  (forall d n, closed_decl d n ->
               forall p, closed_exp p n ->
                         forall m, closed_decl ([p /d m] d) n) /\
  
  (forall ds n, closed_decls ds n ->
                forall p, closed_exp p n ->
                          forall m, closed_decls ([p /ds m] ds) n).
Proof.
  apply type_exp_mutind; intros;
    try solve [crush].

  (*var*)
  destruct v as [|r]; [crush|simpl].
  destruct (Nat.eq_dec m r) as [Heq|Heq];
    [subst; rewrite <- beq_nat_refl; auto
    |apply Nat.eqb_neq in Heq;
     rewrite Heq; auto].
Qed.

Lemma closed_subst_components_type :
  (forall t n, closed_ty t n ->
               forall p, closed_exp p n ->
                         forall m, closed_ty ([p /t m] t) n).
Proof.
  destruct closed_subst_components_mutind; crush.
Qed.

Hint Rewrite closed_subst_components_type.
Hint Resolve closed_subst_components_type.

Lemma closed_subst_components_decl_ty :
  (forall s n, closed_decl_ty s n ->
               forall p, closed_exp p n ->
                         forall m, closed_decl_ty ([p /s m] s) n).
Proof.
  destruct closed_subst_components_mutind; crush.
Qed.

Hint Rewrite closed_subst_components_decl_ty.
Hint Resolve closed_subst_components_decl_ty.

Lemma closed_subst_components_decl_tys :
  (forall ss n, closed_decl_tys ss n ->
                forall p, closed_exp p n ->
                          forall m, closed_decl_tys ([p /ss m] ss) n).
Proof.
  destruct closed_subst_components_mutind; crush.
Qed.

Hint Rewrite closed_subst_components_decl_tys.
Hint Resolve closed_subst_components_decl_tys.

Lemma closed_subst_components_exp :
  (forall e n, closed_exp e n ->
               forall p, closed_exp p n ->
                         forall m, closed_exp ([p /e m] e) n).
Proof.
  destruct closed_subst_components_mutind; crush.
Qed.

Hint Rewrite closed_subst_components_exp.
Hint Resolve closed_subst_components_exp.

Lemma closed_subst_components_decl :
  (forall d n, closed_decl d n ->
               forall p, closed_exp p n ->
                         forall m, closed_decl ([p /d m] d) n).
Proof.
  destruct closed_subst_components_mutind; crush.
Qed.

Hint Rewrite closed_subst_components_decl.
Hint Resolve closed_subst_components_decl.

Lemma closed_subst_components_decls :
  (forall ds n, closed_decls ds n ->
                forall p, closed_exp p n ->
                          forall m, closed_decls ([p /ds m] ds) n).
Proof.
  destruct closed_subst_components_mutind; crush.
Qed.

Hint Rewrite closed_subst_components_decls.
Hint Resolve closed_subst_components_decls.

Lemma closed_has_contains_mutind :
  (forall Sig G p s, Sig en G vdash p ni s ->
                     closed_env Sig 0 ->
                     closed_env G 0 ->
                     closed_exp p 0 ->
                     closed_decl_ty s 0) /\
  (forall Sig G t s, Sig en G vdash s cont t ->
                     closed_env Sig 0 ->
                     closed_env G 0 ->
                     closed_ty t 0 ->
                     closed_decl_ty s 1).
Proof.
  apply has_contains_mutind; intros.

  apply closed_subst_hole_decl_ty; [|auto].
  apply H; auto.
  apply closed_typing_p with (Sig:=Sig)(G:=G)(p:=p); auto.

  apply -> closed_ty_str in H1;
    apply closed_in_dty with (s:=d) in H1; auto.
  
  assert (Hclosed : closed_ty t 0);
    [apply -> closed_decl_ty_upper;
     apply H; auto;
     apply -> closed_ty_sel; eauto|auto].
  
  assert (Hclosed : closed_ty t 0);
    [apply -> closed_decl_ty_equal;
     apply H; auto;
     apply -> closed_ty_sel; eauto|auto].
Qed.


Lemma closed_has :
  (forall Sig G p s, Sig en G vdash p ni s ->
                     closed_env Sig 0 ->
                     closed_env G 0 ->
                     closed_exp p 0 ->
                     closed_decl_ty s 0).
Proof.
  destruct closed_has_contains_mutind; crush.
Qed.


Lemma closed_contains :
  (forall Sig G t s, Sig en G vdash s cont t ->
                     closed_env Sig 0 ->
                     closed_env G 0 ->
                     closed_ty t 0 ->
                     closed_decl_ty s 1).
Proof.
  destruct closed_has_contains_mutind; crush.
Qed.

Hint Rewrite closed_has closed_contains.
Hint Resolve closed_has closed_contains.

Lemma closed_subst_switch_mutind :
  (forall t p1 n m, closed_ty ([p1 /t n] t) m ->
                    forall p2, closed_exp p2 m ->
                               closed_ty ([p2 /t n] t) m) /\
  (forall s p1 n m, closed_decl_ty ([p1 /s n] s) m ->
                    forall p2, closed_exp p2 m ->
                               closed_decl_ty ([p2 /s n] s) m) /\
  (forall ss p1 n m, closed_decl_tys ([p1 /ss n] ss) m ->
                     forall p2, closed_exp p2 m ->
                                closed_decl_tys ([p2 /ss n] ss) m) /\
  (forall e p1 n m, closed_exp ([p1 /e n] e) m ->
                    forall p2, closed_exp p2 m ->
                               closed_exp ([p2 /e n] e) m) /\
  (forall d p1 n m, closed_decl ([p1 /d n] d) m ->
                    forall p2, closed_exp p2 m ->
                               closed_decl ([p2 /d n] d) m) /\
  (forall ds p1 n m, closed_decls ([p1 /ds n] ds) m ->
                     forall p2, closed_exp p2 m ->
                                closed_decls ([p2 /ds n] ds) m).
Proof.
  apply type_exp_mutind; intros; simpl; auto;
    try solve [crush; eauto].

  (*var*)
  destruct v as [|r]; [crush|].
  simpl in H.
  destruct (Nat.eq_dec n r) as [Heq|Heq];
    [subst;
     rewrite <- beq_nat_refl;
     auto
    |apply Nat.eqb_neq in Heq;
     rewrite Heq;
     rewrite Heq in H;
     auto].
Qed.

Lemma closed_subst_switch_type :
  (forall t p1 n m, closed_ty ([p1 /t n] t) m ->
                    forall p2, closed_exp p2 m ->
                               closed_ty ([p2 /t n] t) m).
Proof.
  destruct closed_subst_switch_mutind; crush.
Qed.

Hint Rewrite closed_subst_switch_type.
Hint Resolve closed_subst_switch_type.

Lemma closed_subst_switch_decl_ty :
  (forall s p1 n m, closed_decl_ty ([p1 /s n] s) m ->
                    forall p2, closed_exp p2 m ->
                               closed_decl_ty ([p2 /s n] s) m).
Proof.
  destruct closed_subst_switch_mutind; crush.
Qed.

Hint Rewrite closed_subst_switch_decl_ty.
Hint Resolve closed_subst_switch_decl_ty.

Lemma closed_subst_switch_decl_tys :
  (forall ss p1 n m, closed_decl_tys ([p1 /ss n] ss) m ->
                     forall p2, closed_exp p2 m ->
                                closed_decl_tys ([p2 /ss n] ss) m).
Proof.
  destruct closed_subst_switch_mutind; crush.
Qed.

Hint Rewrite closed_subst_switch_decl_tys.
Hint Resolve closed_subst_switch_decl_tys.

Lemma closed_subst_switch_exp :
  (forall e p1 n m, closed_exp ([p1 /e n] e) m ->
                    forall p2, closed_exp p2 m ->
                               closed_exp ([p2 /e n] e) m).
Proof.
  destruct closed_subst_switch_mutind; crush.
Qed.

Hint Rewrite closed_subst_switch_exp.
Hint Resolve closed_subst_switch_exp.

Lemma closed_subst_switch_decl :
  (forall d p1 n m, closed_decl ([p1 /d n] d) m ->
                    forall p2, closed_exp p2 m ->
                               closed_decl ([p2 /d n] d) m).
Proof.
  destruct closed_subst_switch_mutind; crush.
Qed.

Hint Rewrite closed_subst_switch_decl.
Hint Resolve closed_subst_switch_decl.

Lemma closed_subst_switch_decls :
  (forall ds p1 n m, closed_decls ([p1 /ds n] ds) m ->
                     forall p2, closed_exp p2 m ->
                                closed_decls ([p2 /ds n] ds) m).
Proof.
  destruct closed_subst_switch_mutind; crush.
Qed.

Hint Rewrite closed_subst_switch_decls.
Hint Resolve closed_subst_switch_decls.

Lemma closed_subst_switch_env :
  (forall G p1 n m, closed_env ([p1 /env n] G) m ->
                    forall p2, closed_exp p2 m ->
                               closed_env ([p2 /env n] G) m).
Proof.
  intros G; induction G as [|t G']; intros.

  intros t' Hin;
    inversion Hin.

  rewrite subst_cons; simpl;
    intros t' Hin;
    inversion Hin;
    [subst t'|].
  apply closed_subst_switch_type with (p1:=p1);
    auto.
  apply H; rewrite subst_cons;
    apply in_eq.

  assert (Hclosed_G : closed_env ([p1 /env n]G') m);
    [intros t'' Hin'';
     apply H;
     rewrite subst_cons;
     apply in_cons;
     auto|].
  apply IHG'
    with
      (p2:=p2)
    in Hclosed_G;
    auto.
Qed.

Lemma notin_subst_closed_mutind :
  (forall t e n, e notin_t ([e /t n] t) -> closed_t n t) /\
  (forall s e n, e notin_s ([e /s n] s) -> closed_s n s) /\
  (forall ss e n, e notin_ss ([e /ss n] ss) -> closed_ss n ss) /\
  (forall e' e n, e notin_e ([e /e n] e') -> closed_e n e') /\
  (forall d e n, e notin_d ([e /d n] d) -> closed_d n d) /\
  (forall ds e n, e notin_ds ([e /ds n] ds) -> closed_ds n ds).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [try (inversion H0; subst);
               try (inversion H1; subst);
               try (inversion H2; subst);
               try (eapply H);
               try (eapply H0);
               try (eapply H1);
               eauto].

  (*var*)
  destruct v as [|r]; auto.
  simpl in H;
    destruct (Nat.eq_dec n r) as [Heq|Heq];
    [subst; rewrite <- beq_nat_refl in H;
     inversion H; auto
    |auto].
Qed.

Lemma notin_subst_closed_type :
  (forall t e n, e notin_t ([e /t n] t) -> closed_t n t).
Proof.
  destruct notin_subst_closed_mutind; crush.
Qed.

Lemma notin_subst_closed_decl_ty :
  (forall s e n, e notin_s ([e /s n] s) -> closed_s n s).
Proof.
  destruct notin_subst_closed_mutind; crush.
Qed.

Lemma notin_subst_closed_decl_tys :
  (forall ss e n, e notin_ss ([e /ss n] ss) -> closed_ss n ss).
Proof.
  destruct notin_subst_closed_mutind; crush.
Qed.

Lemma notin_subst_closed_exp :
  (forall e' e n, e notin_e ([e /e n] e') -> closed_e n e').
Proof.
  destruct notin_subst_closed_mutind; crush.
Qed.

Lemma notin_subst_closed_decl :
  (forall d e n, e notin_d ([e /d n] d) -> closed_d n d).
Proof.
  destruct notin_subst_closed_mutind; crush.
Qed.

Lemma notin_subst_closed_decls :
  (forall ds e n, e notin_ds ([e /ds n] ds) -> closed_ds n ds).
Proof.
  destruct notin_subst_closed_mutind; crush.
Qed.

Lemma is_path_subst :
  forall p, is_path p ->
       forall p' n, is_path p' ->
               is_path ([p' /e n] p).
Proof.
  intros p Hpath;
    induction Hpath; intros; simpl; auto.
  destruct x as [|r]; auto.
  destruct (n =? r); auto.
Qed.

Hint Resolve is_path_subst.

Lemma subst_is_path :
  forall p p' n, is_path ([p' /e n] p) ->
            is_path p.
Proof.
  intros p; induction p; intros; auto;
    try solve [inversion H].

  inversion H; subst.
  apply IHp in H1; auto.
Qed.

Hint Resolve is_path_subst.


Lemma unbound_var_notin_mutind :
  (forall r t, r unbound_t t ->
          (c_ r) notin_t t) /\
  
  (forall r s, r unbound_s s ->
          (c_ r) notin_s s) /\
  
  (forall r ss, r unbound_ss ss ->
           (c_ r) notin_ss ss) /\
  
  (forall r e, r unbound_e e ->
          (c_ r) notin_e e) /\
  
  (forall r d, r unbound_d d ->
          (c_ r) notin_d d) /\
  
  (forall r ds, r unbound_ds ds ->
           (c_ r) notin_ds ds).
Proof.
  apply unbound_mutind; intros; auto.

  inversion u; subst;
    apply ni_var; crush.

  apply ni_loc; crush.

  apply ni_cast; crush.

  apply ni_fn; crush.

  apply ni_app; crush.

  apply ni_acc; crush.

  apply ni_new; crush.
  
Qed.

Hint Rewrite unbound_var_notin_mutind.
Hint Resolve unbound_var_notin_mutind.

Lemma unbound_var_notin_type :
  (forall r t, r unbound_t t ->
          (c_ r) notin_t t).
Proof.
  destruct unbound_var_notin_mutind; crush.
Qed.

Hint Rewrite unbound_var_notin_type.
Hint Resolve unbound_var_notin_type.

Lemma unbound_var_notin_decl_ty :    
  (forall r s, r unbound_s s ->
               (c_ r) notin_s s).
Proof.
  destruct unbound_var_notin_mutind; crush.
Qed.

Hint Rewrite unbound_var_notin_decl_ty.
Hint Resolve unbound_var_notin_decl_ty.

Lemma unbound_var_notin_decl_tys :    
  (forall r ss, r unbound_ss ss ->
                (c_ r) notin_ss ss).
Proof.
  destruct unbound_var_notin_mutind; crush.
Qed.

Hint Rewrite unbound_var_notin_decl_tys.
Hint Resolve unbound_var_notin_decl_tys.

Lemma unbound_var_notin_exp :    
  (forall r e, r unbound_e e ->
               (c_ r) notin_e e).
Proof.
  destruct unbound_var_notin_mutind; crush.
Qed.

Hint Rewrite unbound_var_notin_exp.
Hint Resolve unbound_var_notin_exp.

Lemma unbound_var_notin_decl :    
  (forall r d, r unbound_d d ->
               (c_ r) notin_d d).
Proof.
  destruct unbound_var_notin_mutind; crush.
Qed.

Hint Rewrite unbound_var_notin_decl.
Hint Resolve unbound_var_notin_decl.

Lemma unbound_var_notin_decls :    
  (forall r ds, r unbound_ds ds ->
                (c_ r) notin_ds ds).
Proof.
  destruct unbound_var_notin_mutind; crush.
Qed.

Hint Rewrite unbound_var_notin_decls.
Hint Resolve unbound_var_notin_decls.

Lemma notin_var_unbound_mutind :
  (forall x t, x notin_t t ->
               forall r, (x = c_ r) ->
                         r unbound_t t) /\
  
  (forall x s, x notin_s s ->
               forall r, (x = c_ r) ->
                         r unbound_s s) /\
  
  (forall x ss, x notin_ss ss ->
                forall r, (x = c_ r) ->
                          r unbound_ss ss) /\
  
  (forall x e, x notin_e e ->
               forall r, (x = c_ r) ->
                         r unbound_e e) /\
  
  (forall x d, x notin_d d ->
               forall r, (x = c_ r) ->
                         r unbound_d d) /\
  
  (forall x ds, x notin_ds ds ->
                forall r, (x = c_ r) ->
                          r unbound_ds ds).
Proof.
  apply notin_mutind; intros; subst; simpl in *; auto.

  destruct x; auto.
  apply ub_var; auto.
  apply ub_con; crush.
Qed.

Hint Rewrite notin_var_unbound_mutind.
Hint Resolve notin_var_unbound_mutind.

Lemma notin_var_unbound_type :
  (forall r t, (c_ r) notin_t t ->
               r unbound_t t).
Proof.
  destruct notin_var_unbound_mutind as [Ha Hb]; 
    destruct Hb as [Hb Hc];
    destruct Hc as [Hc Hd];
    destruct Hd as [Hd He];
    destruct He as [He Hf]; intros; simpl in *; eauto.
Qed.

Hint Rewrite notin_var_unbound_type.
Hint Resolve notin_var_unbound_type.

Lemma notin_var_unbound_decl_ty :    
  (forall r s, (c_ r) notin_s s ->
               r unbound_s s).
Proof.
  destruct notin_var_unbound_mutind as [Ha Hb];
    destruct Hb as [Hb Hc];
    destruct Hc as [Hc Hd];
    destruct Hd as [Hd He];
    destruct He as [He Hf]; intros; simpl in *; eauto.
Qed.

Hint Rewrite notin_var_unbound_decl_ty.
Hint Resolve notin_var_unbound_decl_ty.

Lemma notin_var_unbound_decl_tys :    
  (forall r ss, (c_ r) notin_ss ss ->
                r unbound_ss ss).
Proof.
  destruct notin_var_unbound_mutind as [Ha Hb];
    destruct Hb as [Hb Hc];
    destruct Hc as [Hc Hd];
    destruct Hd as [Hd He];
    destruct He as [He Hf]; intros; simpl in *; eauto.
Qed.

Hint Rewrite notin_var_unbound_decl_tys.
Hint Resolve notin_var_unbound_decl_tys.

Lemma notin_var_unbound_exp :    
  (forall r e, (c_ r) notin_e e ->
               r unbound_e e).
Proof.
  destruct notin_var_unbound_mutind as [Ha Hb];
    destruct Hb as [Hb Hc];
    destruct Hc as [Hc Hd];
    destruct Hd as [Hd He];
    destruct He as [He Hf]; intros; simpl in *; eauto.
Qed.

Hint Rewrite notin_var_unbound_exp.
Hint Resolve notin_var_unbound_exp.

Lemma notin_var_unbound_decl :
  (forall r d, (c_ r) notin_d d ->
               r unbound_d d).
Proof.
  destruct notin_var_unbound_mutind as [Ha Hb];
    destruct Hb as [Hb Hc];
    destruct Hc as [Hc Hd];
    destruct Hd as [Hd He];
    destruct He as [He Hf]; intros; simpl in *; eauto.
Qed.

Hint Rewrite notin_var_unbound_decl.
Hint Resolve notin_var_unbound_decl.

Lemma notin_var_unbound_decls :    
  (forall r ds, (c_ r) notin_ds ds ->
                r unbound_ds ds).
Proof.
  destruct notin_var_unbound_mutind as [Ha Hb];
    destruct Hb as [Hb Hc];
    destruct Hc as [Hc Hd];
    destruct Hd as [Hd He];
    destruct He as [He Hf]; intros; simpl in *; eauto.
Qed.

Hint Rewrite notin_var_unbound_decls.
Hint Resolve notin_var_unbound_decls.

Lemma unbound_raise_mutind :
  (forall r t, r unbound_t t ->
               forall n, r unbound_t (t raise_t n)) /\
  
  (forall r s, r unbound_s s ->
               forall n, r unbound_s (s raise_s n)) /\
  
  (forall r ss, r unbound_ss ss ->
                forall n, r unbound_ss (ss raise_ss n)) /\
  
  (forall r e, r unbound_e e ->
               forall n, r unbound_e (e raise_e n)) /\
  
  (forall r d, r unbound_d d ->
               forall n, r unbound_d (d raise_d n)) /\
  
  (forall r ds, r unbound_ds ds ->
                forall n, r unbound_ds (ds raise_ds n)).
Proof.
  apply unbound_mutind; intros; simpl in *; auto.

  inversion u; subst; simpl; auto.
Qed.

Lemma unbound_raise_type :
  (forall r t, r unbound_t t ->
               forall n, r unbound_t (t raise_t n)).
Proof.
  destruct unbound_raise_mutind; crush.
Qed.

Hint Rewrite unbound_raise_type.
Hint Resolve unbound_raise_type.

Lemma unbound_raise_decl_ty :    
  (forall r s, r unbound_s s ->
               forall n, r unbound_s (s raise_s n)).
Proof.
  destruct unbound_raise_mutind; crush.
Qed.

Hint Rewrite unbound_raise_decl_ty.
Hint Resolve unbound_raise_decl_ty.

Lemma unbound_raise_decl_tys :
  (forall r ss, r unbound_ss ss ->
                forall n, r unbound_ss (ss raise_ss n)).
Proof.
  destruct unbound_raise_mutind; crush.
Qed.

Hint Rewrite unbound_raise_decl_tys.
Hint Resolve unbound_raise_decl_tys.

Lemma unbound_raise_exp :    
  (forall r e, r unbound_e e ->
               forall n, r unbound_e (e raise_e n)).
Proof.
  destruct unbound_raise_mutind; crush.
Qed.

Hint Rewrite unbound_raise_exp.
Hint Resolve unbound_raise_exp.

Lemma unbound_raise_decl :    
  (forall r d, r unbound_d d ->
               forall n, r unbound_d (d raise_d n)).
Proof.
  destruct unbound_raise_mutind; crush.
Qed.

Hint Rewrite unbound_raise_decl.
Hint Resolve unbound_raise_decl.

Lemma unbound_raise_decls :    
  (forall r ds, r unbound_ds ds ->
                forall n, r unbound_ds (ds raise_ds n)).
Proof.
  destruct unbound_raise_mutind; crush.
Qed.

Hint Rewrite unbound_raise_decls.
Hint Resolve unbound_raise_decls.

Lemma unbound_subst_components_mutind :
  (forall t p n r, r unbound_t t ->
                   r unbound_e p ->
                   r unbound_t ([p /t n] t)) /\
  
  (forall s p n r, r unbound_s s ->
                   r unbound_e p ->
                   r unbound_s ([p /s n] s)) /\
  
  (forall ss p n r, r unbound_ss ss ->
                    r unbound_e p ->
                    r unbound_ss ([p /ss n] ss)) /\
  
  (forall e p n r, r unbound_e e ->
                   r unbound_e p ->
                   r unbound_e ([p /e n] e)) /\
  
  (forall d p n r, r unbound_d d ->
                   r unbound_e p ->
                   r unbound_d ([p /d n] d)) /\
  
  (forall ds p n r, r unbound_ds ds ->
                    r unbound_e p ->
                    r unbound_ds ([p /ds n] ds)).
Proof.
  apply type_exp_mutind; intros; simpl in *; auto;
    try solve [try inversion H0; subst; auto];
    try solve [try inversion H1; subst; auto];
    try solve [try inversion H2; subst; auto].

  inversion H; subst.
  inversion H3; subst; auto.
  destruct (Nat.eq_dec n m) as [|Hneq];
    [subst;
     rewrite <- beq_nat_refl;
     auto
    |apply Nat.eqb_neq in Hneq;
     rewrite Hneq;
     auto].
Qed.

Hint Rewrite unbound_subst_components_mutind.
Hint Resolve unbound_subst_components_mutind. 

Lemma unbound_subst_components_type :
  (forall t p n r, r unbound_t t ->
                   r unbound_e p ->
                   r unbound_t ([p /t n] t)).
Proof.
  destruct unbound_subst_components_mutind; crush.
Qed.

Hint Rewrite unbound_subst_components_type.
Hint Resolve unbound_subst_components_type.

Lemma unbound_subst_components_decl_ty :    
  (forall s p n r, r unbound_s s ->
                   r unbound_e p ->
                   r unbound_s ([p /s n] s)).
Proof.
  destruct unbound_subst_components_mutind; crush.
Qed.

Hint Rewrite unbound_subst_components_decl_ty.
Hint Resolve unbound_subst_components_decl_ty.

Lemma unbound_subst_components_decl_tys :    
  (forall ss p n r, r unbound_ss ss ->
                    r unbound_e p ->
                    r unbound_ss ([p /ss n] ss)).
Proof.
  destruct unbound_subst_components_mutind; crush.
Qed.

Hint Rewrite unbound_subst_components_decl_tys.
Hint Resolve unbound_subst_components_decl_tys.

Lemma unbound_subst_components_exp :    
  (forall e p n r, r unbound_e e ->
                   r unbound_e p ->
                   r unbound_e ([p /e n] e)).
Proof.
  destruct unbound_subst_components_mutind; crush.
Qed.

Hint Rewrite unbound_subst_components_exp.
Hint Resolve unbound_subst_components_exp.

Lemma unbound_subst_components_decl :    
  (forall d p n r, r unbound_d d ->
                   r unbound_e p ->
                   r unbound_d ([p /d n] d)).
Proof.
  destruct unbound_subst_components_mutind; crush.
Qed.

Hint Rewrite unbound_subst_components_decl.
Hint Resolve unbound_subst_components_decl.

Lemma unbound_subst_components_decls :    
  (forall ds p n r, r unbound_ds ds ->
                    r unbound_e p ->
                    r unbound_ds ([p /ds n] ds)).
Proof.
  destruct unbound_subst_components_mutind; crush.
Qed.

Hint Rewrite unbound_subst_components_decls.
Hint Resolve unbound_subst_components_decls.

Lemma unbound_subst_mutind :
  (forall t p n r, r unbound_t ([p /t n] t) ->
                   r unbound_t t) /\
  
  (forall s p n r, r unbound_s ([p /s n] s) ->
                   r unbound_s s) /\
  
  (forall ss p n r, r unbound_ss ([p /ss n] ss) ->
                    r unbound_ss ss) /\
  
  (forall e p n r, r unbound_e ([p /e n] e) ->
                   r unbound_e e) /\
  
  (forall d p n r, r unbound_d ([p /d n] d) ->
                   r unbound_d d) /\
  
  (forall ds p n r, r unbound_ds ([p /ds n] ds) ->
                    r unbound_ds ds).
Proof.
  apply type_exp_mutind; intros; eauto;
    try solve [try (inversion H0);
               try (inversion H1);
               try (inversion H2);
               eauto].

  destruct v; auto.
Qed.

Lemma unbound_subst_type :
  (forall t p n r, r unbound_t ([p /t n] t) ->
                   r unbound_t t).
Proof.
  destruct unbound_subst_mutind; crush.
Qed.

Lemma unbound_subst_decl_ty :    
  (forall s p n r, r unbound_s ([p /s n] s) ->
                   r unbound_s s).
Proof.
  destruct unbound_subst_mutind; crush.
Qed.

Lemma unbound_subst_decl_tys :    
  (forall ss p n r, r unbound_ss ([p /ss n] ss) ->
                    r unbound_ss ss).
Proof.
  destruct unbound_subst_mutind; crush.
Qed.

Lemma unbound_subst_exp :
  (forall e p n r, r unbound_e ([p /e n] e) ->
                   r unbound_e e).
Proof.
  destruct unbound_subst_mutind; crush.
Qed.

Lemma unbound_subst_decl :    
  (forall d p n r, r unbound_d ([p /d n] d) ->
                   r unbound_d d).
Proof.
  destruct unbound_subst_mutind; crush.
Qed.

Lemma unbound_subst_decls :
  (forall ds p n r, r unbound_ds ([p /ds n] ds) ->
                    r unbound_ds ds).
Proof.
  destruct unbound_subst_mutind; crush.
Qed.

Lemma rename_raise_mutind :
  (forall t i n m, n >= i ->
                   m >= i ->
                   ((t raise_t i) [S n maps_t S m]) =
                   ((t [n maps_t m] raise_t i))) /\
  
  (forall s i n m, n >= i ->
                   m >= i ->
                   ((s raise_s i) [S n maps_s S m]) =
                   ((s [n maps_s m] raise_s i))) /\
  
  (forall ss i n m, n >= i ->
                    m >= i ->
                    ((ss raise_ss i) [S n maps_ss S m]) =
                    ((ss [n maps_ss m] raise_ss i))) /\
  
  (forall e i n m, n >= i ->
                   m >= i ->
                   ((e raise_e i) [S n maps_e S m]) =
                   ((e [n maps_e m] raise_e i))) /\
  
  (forall d i n m, n >= i ->
                   m >= i ->
                   ((d raise_d i) [S n maps_d S m]) =
                   ((d [n maps_d m] raise_d i))) /\
  
  (forall ds i n m, n >= i ->
                    m >= i ->
                    ((ds raise_ds i) [S n maps_ds S m]) =
                    ((ds [n maps_ds m] raise_ds i))).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               rewrite H;
               try (rewrite H0);
               try (rewrite H1);
               crush].
  
  destruct v as [|r]; simpl;
    [auto
    |].
  destruct (lt_dec r i) as [Hlt|Hlt].
  unfold raise_nat;
    apply Nat.ltb_lt in Hlt;
    rewrite Hlt.
  destruct (Nat.eq_dec r (S n)) as [Heq|Heq];
    [subst;
     rewrite Nat.ltb_lt in Hlt; crush
    |rewrite rename_neq;
     [|auto]].
  repeat rewrite rename_neq;
    [
     |apply Nat.ltb_lt in Hlt;
      crush].
  rewrite Hlt; auto.
  unfold raise_nat;
    apply Nat.ltb_nlt in Hlt;
    rewrite Hlt.
  destruct (Nat.eq_dec r n) as [|Heq];
    [subst;
     repeat rewrite Nat.add_1_r;
     repeat rewrite rename_eq
    |repeat rewrite Nat.add_1_r;
     repeat rewrite rename_neq; crush].
  apply le_not_gt in H0.
  apply Nat.ltb_nlt in H0;
    rewrite H0; auto.
Qed.

Lemma rename_raise_type :
  (forall t i n m, n >= i ->
                   m >= i ->
                   ((t raise_t i) [S n maps_t S m]) =
                   ((t [n maps_t m] raise_t i))).
Proof.
  destruct rename_raise_mutind; crush.
Qed.

Lemma rename_raise_decl_ty :
  (forall s i n m, n >= i ->
                   m >= i ->
                   ((s raise_s i) [S n maps_s S m]) =
                   ((s [n maps_s m] raise_s i))).
Proof.
  destruct rename_raise_mutind; crush.
Qed.

Lemma rename_raise_decl_tys :  
  (forall ss i n m, n >= i ->
                    m >= i ->
                    ((ss raise_ss i) [S n maps_ss S m]) =
                    ((ss [n maps_ss m] raise_ss i))).
Proof.
  destruct rename_raise_mutind; crush.
Qed.

Lemma rename_raise_exp :  
  (forall e i n m, n >= i ->
                   m >= i ->
                   ((e raise_e i) [S n maps_e S m]) =
                   ((e [n maps_e m] raise_e i))).
Proof.
  destruct rename_raise_mutind; crush.
Qed.

Lemma rename_raise_decl :  
  (forall d i n m, n >= i ->
                   m >= i ->
                   ((d raise_d i) [S n maps_d S m]) =
                   ((d [n maps_d m] raise_d i))).
Proof.
  destruct rename_raise_mutind; crush.
Qed.

Lemma rename_raise_decls :  
  (forall ds i n m, n >= i ->
                    m >= i ->
                    ((ds raise_ds i) [S n maps_ds S m]) =
                    ((ds [n maps_ds m] raise_ds i))).
Proof.
  destruct rename_raise_mutind; crush.
Qed.

Lemma rename_subst_distr_mutind :
  (forall t p r n m, closed_t m t ->
                     r <> m ->
                     (([p /t r] t)[n maps_t m]) =
                     ([p [n maps_e m] /t rename r n m] (t[n maps_t m]))) /\
  
  (forall s p r n m, closed_s m s ->
                     r <> m ->
                     (([p /s r] s)[n maps_s m]) =
                     ([p [n maps_e m] /s rename r n m] (s[n maps_s m]))) /\
  
  (forall ss p r n m, closed_ss m ss ->
                      r <> m ->
                      (([p /ss r] ss)[n maps_ss m]) =
                      ([p [n maps_e m] /ss rename r n m] (ss[n maps_ss m]))) /\
  
  (forall e p r n m, closed_e m e ->
                     r <> m ->
                     (([p /e r] e)[n maps_e m]) =
                     ([p [n maps_e m] /e rename r n m] (e[n maps_e m]))) /\
  
  (forall d p r n m, closed_d m d ->
                     r <> m ->
                     (([p /d r] d)[n maps_d m]) =
                     ([p [n maps_e m] /d rename r n m] (d[n maps_d m]))) /\
  
  (forall ds p r n m, closed_ds m ds ->
                      r <> m ->
                      (([p /ds r] ds)[n maps_ds m]) =
                      ([p [n maps_e m] /ds rename r n m] (ds[n maps_ds m]))).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl in *;
               try (inversion H0; subst);
               try (inversion H1; subst);
               try (inversion H2; subst);
               rewrite H;
               try (rewrite H0);
               try (rewrite H1);
               try (rewrite rename_raise_exp; [|crush|crush]);
               try (rewrite rename_S);
               auto].

  destruct v as [x|x]; auto.
  simpl.
  destruct (Nat.eq_dec r x) as [|Hneq1];
    [subst;
     repeat rewrite <- beq_nat_refl;
     auto
    |apply Nat.eqb_neq in Hneq1;
     rewrite Hneq1; simpl].
  destruct (Nat.eq_dec r n) as [|Hneq2];
    [subst;
     rewrite rename_eq;
     rewrite rename_neq;
     [|apply Nat.eqb_neq in Hneq1; auto]
    |].
  inversion H; subst;
    inversion H3; subst.
  apply Nat.eqb_neq in H4;
    rewrite H4;
    auto.
  rewrite (rename_neq m Hneq2).
  destruct (Nat.eq_dec x n) as [|Hneq3];
    [subst;
     rewrite rename_eq;
     apply Nat.eqb_neq in H0;
     rewrite H0;
     auto
    |rewrite rename_neq; auto;
     rewrite Hneq1;
     auto].
Qed.

Lemma rename_subst_distr_type :
  (forall t p r n m, closed_t m t ->
                     r <> m ->
                     (([p /t r] t)[n maps_t m]) =
                     ([p [n maps_e m] /t rename r n m] (t[n maps_t m]))).
Proof.
  destruct rename_subst_distr_mutind; crush.
Qed.

Lemma rename_subst_distr_decl_ty :    
  (forall s p r n m, closed_s m s ->
                     r <> m ->
                     (([p /s r] s)[n maps_s m]) =
                     ([p [n maps_e m] /s rename r n m] (s[n maps_s m]))).
Proof.
  destruct rename_subst_distr_mutind; crush.
Qed.

Lemma rename_subst_distr_decl_tys :    
  (forall ss p r n m, closed_ss m ss ->
                      r <> m ->
                      (([p /ss r] ss)[n maps_ss m]) =
                      ([p [n maps_e m] /ss rename r n m] (ss[n maps_ss m]))).
Proof.
  destruct rename_subst_distr_mutind; crush.
Qed.

Lemma rename_subst_distr_exp :
  (forall e p r n m, closed_e m e ->
                     r <> m ->
                     (([p /e r] e)[n maps_e m]) =
                     ([p [n maps_e m] /e rename r n m] (e[n maps_e m]))).
Proof.
  destruct rename_subst_distr_mutind; crush.
Qed.

Lemma rename_subst_distr_decl :
  (forall d p r n m, closed_d m d ->
                     r <> m ->
                     (([p /d r] d)[n maps_d m]) =
                     ([p [n maps_e m] /d rename r n m] (d[n maps_d m]))).
Proof.
  destruct rename_subst_distr_mutind; crush.
Qed.

Lemma rename_subst_distr_decls :
  (forall ds p r n m, closed_ds m ds ->
                      r <> m ->
                      (([p /ds r] ds)[n maps_ds m]) =
                      ([p [n maps_e m] /ds rename r n m] (ds[n maps_ds m]))).
Proof.
  destruct rename_subst_distr_mutind; crush.
Qed.

Lemma rename_eq_subst_distr_mutind :
  (forall t p n m, (([p /t n] t)[n maps_t m]) =
                   ([p [n maps_e m] /t n] t)) /\
  
  (forall s p n m, (([p /s n] s)[n maps_s m]) =
                   ([p [n maps_e m] /s n] s)) /\
  
  (forall ss p n m, (([p /ss n] ss)[n maps_ss m]) =
                    ([p [n maps_e m] /ss n] ss)) /\
  
  (forall e p n m, (([p /e n] e)[n maps_e m]) =
                   ([p [n maps_e m] /e n] e)) /\
  
  (forall d p n m, (([p /d n] d)[n maps_d m]) =
                   ([p [n maps_e m] /d n] d)) /\
  
  (forall ds p n m, (([p /ds n] ds)[n maps_ds m]) =
                    ([p [n maps_e m] /ds n] ds)).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               rewrite H;
               try (rewrite H0);
               try (rewrite H1);
               try (rewrite rename_raise_exp);
               crush].

  destruct v as [x|x]; simpl; auto.
  destruct (Nat.eq_dec n x) as [|Hneq];
    [subst;
     rewrite <- beq_nat_refl;
     auto
    |assert (Hneqb := Hneq);
     apply Nat.eqb_neq in Hneqb;
     rewrite Hneqb].
  simpl.
  rewrite rename_neq; auto.
Qed.

Lemma rename_eq_subst_distr_type :
  (forall t p n m, (([p /t n] t)[n maps_t m]) =
                   ([p [n maps_e m] /t n] t)).
Proof.
  destruct rename_eq_subst_distr_mutind; crush.
Qed.

Lemma rename_eq_subst_distr_decl_ty :
  (forall s p n m, (([p /s n] s)[n maps_s m]) =
                   ([p [n maps_e m] /s n] s)).
Proof.
  destruct rename_eq_subst_distr_mutind; crush.
Qed.

Lemma rename_eq_subst_distr_decl_tys :
  (forall ss p n m, (([p /ss n] ss)[n maps_ss m]) =
                    ([p [n maps_e m] /ss n] ss)).
Proof.
  destruct rename_eq_subst_distr_mutind; crush.
Qed.

Lemma rename_eq_subst_distr_exp :
  (forall e p n m, (([p /e n] e)[n maps_e m]) =
                   ([p [n maps_e m] /e n] e)).
Proof.
  destruct rename_eq_subst_distr_mutind; crush.
Qed.

Lemma rename_eq_subst_distr_decl :
  (forall d p n m, (([p /d n] d)[n maps_d m]) =
                   ([p [n maps_e m] /d n] d)).
Proof.
  destruct rename_eq_subst_distr_mutind; crush.
Qed.

Lemma rename_eq_subst_distr_decls :
  (forall ds p n m, (([p /ds n] ds)[n maps_ds m]) =
                    ([p [n maps_e m] /ds n] ds)).
Proof.
  destruct rename_eq_subst_distr_mutind; crush.
Qed.

Lemma rename_closed_mutind :
  (forall n t, closed_t n t ->
               forall m, (t [n maps_t m]) = t) /\
  
  (forall n s, closed_s n s ->
               forall m, (s [n maps_s m]) = s) /\
  
  (forall n ss, closed_ss n ss ->
                forall m, (ss [n maps_ss m]) = ss) /\
  
  (forall n e, closed_e n e ->
               forall m, (e [n maps_e m]) = e) /\
  
  (forall n d, closed_d n d ->
               forall m, (d [n maps_d m]) = d) /\
  
  (forall n ds, closed_ds n ds ->
                forall m, (ds [n maps_ds m]) = ds).
Proof.
  apply closed_mutind; intros; auto.
Qed.

Lemma rename_closed_type :
  (forall n t, closed_t n t ->
               forall m, (t [n maps_t m]) = t).
Proof.
  destruct rename_closed_mutind; crush.
Qed.

Lemma rename_closed_decl_ty :    
  (forall n s, closed_s n s ->
               forall m, (s [n maps_s m]) = s).
Proof.
  destruct rename_closed_mutind; crush.
Qed.

Lemma rename_closed_decl_tys :
  (forall n ss, closed_ss n ss ->
                forall m, (ss [n maps_ss m]) = ss).
Proof.
  destruct rename_closed_mutind; crush.
Qed.

Lemma rename_closed_exp :
  (forall n e, closed_e n e ->
               forall m, (e [n maps_e m]) = e).
Proof.
  destruct rename_closed_mutind; crush.
Qed.

Lemma rename_closed_decl :
  (forall n d, closed_d n d ->
               forall m, (d [n maps_d m]) = d).
Proof.
  destruct rename_closed_mutind; crush.
Qed.

Lemma rename_closed_decls :
  (forall n ds, closed_ds n ds ->
                forall m, (ds [n maps_ds m]) = ds).
Proof.
  destruct rename_closed_mutind; crush.
Qed.

Lemma rename_inverse_mutind :
  (forall n t, closed_t n t ->
               forall m, (t [m maps_t n] [n maps_t m]) = t) /\
  
  (forall n s, closed_s n s ->
               forall m, (s [m maps_s n] [n maps_s m]) = s) /\
  
  (forall n ss, closed_ss n ss ->
                forall m, (ss [m maps_ss n] [n maps_ss m]) = ss) /\
  
  (forall n e, closed_e n e ->
               forall m, (e [m maps_e n] [n maps_e m]) = e) /\
  
  (forall n d, closed_d n d ->
               forall m, (d [m maps_d n] [n maps_d m]) = d) /\
  
  (forall n ds, closed_ds n ds ->
                forall m, (ds [m maps_ds n] [n maps_ds m]) = ds).
Proof.
  apply closed_mutind; intros; simpl; auto;
    try solve [rewrite H;
               try (rewrite H0);
               try (rewrite H1);
               auto].
  
  (*var*)
  destruct x as [r|r]; simpl; auto.
  inversion c; subst.
  destruct (Nat.eq_dec r m) as [|Hneq];
    [subst;
     repeat rewrite rename_eq;
     auto
    |repeat rewrite rename_neq;
     auto].
Qed.

Lemma rename_inverse_type :
  (forall n t, closed_t n t ->
               forall m, (t [m maps_t n] [n maps_t m]) = t).
Proof.
  destruct rename_inverse_mutind; crush.
Qed.

Hint Rewrite rename_inverse_type.
Hint Resolve rename_inverse_type.

Lemma rename_inverse_decl_ty :
  (forall n s, closed_s n s ->
               forall m, (s [m maps_s n] [n maps_s m]) = s).
Proof.
  destruct rename_inverse_mutind; crush.
Qed.

Hint Rewrite rename_inverse_decl_ty.
Hint Resolve rename_inverse_decl_ty.

Lemma rename_inverse_decl_tys :
  (forall n ss, closed_ss n ss ->
                forall m, (ss [m maps_ss n] [n maps_ss m]) = ss).
Proof.
  destruct rename_inverse_mutind; crush.
Qed.

Hint Rewrite rename_inverse_decl_tys.
Hint Resolve rename_inverse_decl_tys.

Lemma rename_inverse_exp :
  (forall n e, closed_e n e ->
          forall m, (e [m maps_e n] [n maps_e m]) = e).
Proof.
  destruct rename_inverse_mutind; crush.
Qed.

Hint Rewrite rename_inverse_exp.
Hint Resolve rename_inverse_exp.

Lemma rename_inverse_decl :
  (forall n d, closed_d n d ->
          forall m, (d [m maps_d n] [n maps_d m]) = d).
Proof.
  destruct rename_inverse_mutind; crush.
Qed.

Hint Rewrite rename_inverse_decl.
Hint Resolve rename_inverse_decl.

Lemma rename_inverse_decls :  
  (forall n ds, closed_ds n ds ->
           forall m, (ds [m maps_ds n] [n maps_ds m]) = ds).
Proof.
  destruct rename_inverse_mutind; crush.
Qed.

Hint Rewrite rename_inverse_decls.
Hint Resolve rename_inverse_decls.




Lemma closed_cons :
  forall G t n, closed_ty t n ->
           closed_env G n ->
           closed_env (t::G) n.
Proof.
  intros; intros t' Hin.
  destruct Hin as [Hin|Hin]; subst; auto.
Qed.





Lemma path_typing_implies_typing :
  (forall Sig G p t, Sig en G vdash p pathType t ->
              Sig en G vdash p wf_e ->
              Sig en G vdash p hasType t).
Proof.
  intros Sig G p t Htyp Hwf.

  inversion Htyp; subst; auto.

  inversion Hwf; subst; auto.
  apply t_cast with (t':=t'); auto.
Qed.

Lemma closed_typing_decl :
  (forall Sig G d s, Sig en G vdash d hasType_d s ->
              forall n, closed_decl d n ->
                   closed_decl_ty s n).
Proof.
  intros Sig G d s Htyp;
    induction Htyp; intros; auto.
  apply closed_decl_equal in H; eauto.
  eapply closed_decl_ty_equal; eauto.
  
  apply closed_decl_value in H1; eauto.
  eapply closed_decl_ty_value; crush.
Qed.


Lemma closed_typing_decls :
  (forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
                       forall n, closed_decls ds n ->
                                 closed_decl_tys ss n).
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp; intros; auto.
  apply closed_decls_con in H0.
  eapply closed_decl_tys_con; split; [|crush].
  apply closed_typing_decl with (Sig:=Sig)(G:=G)(d:=d);
    crush.
Qed.

Lemma closed_typing_exp :
  (forall Sig G e t, Sig en G vdash e hasType t ->
                     closed_env Sig 0 ->
                     closed_env G 0 ->
                     closed_exp e 0 ->
                     closed_ty t 0).
Proof.
  intros Sig G e t Htyp;
    induction Htyp; intros; auto.

  (*var*)
  apply closed_typing_p with (Sig:=Sig)(G:=G)(p:=c_ n); auto.

  (*loc*)
  apply closed_typing_p with (Sig:=Sig)(G:=G)(p:=i_ i); auto.

  (*cast*)
  eapply closed_exp_cast; eauto.

  (*fn*)
  apply closed_exp_fn in H1;
    destruct H1 as [Ha Hb];
    destruct Hb as [Hb Hc].
  intros n' Hin; apply cl_arr; auto;
    apply Hc; crush.
  
  (*app*)
  apply IHHtyp1 in H1; auto;
    [|apply closed_exp_app in H3; crush].
  intros n' Hin.
  apply closed_ty_arr in H1;
    destruct H1 as [Ha Hb].
  destruct n' as [|n'']; auto.

  (*app-path*)
  apply IHHtyp in H1; auto;
    [|apply closed_exp_app in H3; crush].
  apply closed_subst_hole_type; auto;
    [eapply closed_ty_arr; eauto|].
  apply closed_exp_cast; split; eauto;
    [eapply closed_exp_app; eauto
    |eapply closed_ty_arr; eauto].

  (*str*)
  apply closed_typing_decls with (n:=0) in H; auto.
  apply closed_remove_subst_hole_decl_tys in H; auto.
  intros n Hle.
  apply cl_str; crush.
  apply closed_subst_hole_decls; auto.
  apply closed_exp_new; auto.

  (*acc*)
  apply closed_has in H; auto.
  eapply closed_decl_ty_value; eauto.
  eapply closed_exp_acc; eauto.

  (*acc path*)
  intros n Hle; apply H0, IHHtyp; auto.
  eapply closed_exp_acc; eauto.
Qed.



Lemma closed_membership :
  (forall Sig G e s, Sig en G vdash e mem s ->
              closed_env Sig 0 ->
              closed_env G 0 ->
              closed_exp e 0 ->
              closed_decl_ty s 0).
Proof.
  intros Sig G e s Hmem;
    destruct Hmem; intros.

  eapply closed_has; eauto.

  intros n Hle;
    destruct n as [|n'];
    [auto
    |apply closed_contains in H0;
     auto].
  apply H0; crush.

  eapply closed_typing_exp; eauto.
  
Qed.


Lemma notin_refl_contra :
  forall e, e notin_e e -> False.
Proof.
  intros;
    destruct e;
    inversion H; crush.
Qed.

Lemma raise_neq_mutind :
  (forall t1 t2, t1 <> t2 ->
            forall n, (t1 raise_t n) <> (t2 raise_t n)) /\
  
  (forall s1 s2, s1 <> s2 ->
            forall n, (s1 raise_s n) <> (s2 raise_s n)) /\
  
  (forall ss1 ss2, ss1 <> ss2 ->
              forall n, (ss1 raise_ss n) <> (ss2 raise_ss n)) /\
  
  (forall e1 e2, e1 <> e2 ->
            forall n, (e1 raise_e n) <> (e2 raise_e n)) /\
  
  (forall d1 d2, d1 <> d2 ->
                 forall n, (d1 raise_d n) <> (d2 raise_d n)) /\
  
  (forall ds1 ds2, ds1 <> ds2 ->
                   forall n, (ds1 raise_ds n) <> (ds2 raise_ds n)).
Proof.
  apply type_exp_mutind; intros.

  (*str*)
  destruct t2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : d <> d0);
    [crush
    |eapply H in Hneq; eauto].

  (*sel*)
  destruct t2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : e <> e0);
    [crush
    |eapply H in Hneq; eauto].

  (*arr*)
  destruct t2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t2_1);
    [intro Hcontra1;
     subst t
    |eapply H in Hneq; eauto];
    assert (Hneq : t0 <> t2_2);
    [crush
    |eapply H0 in Hneq; eauto].

  (*top*)
  destruct t2;
    simpl;
    try solve [crush].

  (*bot*)
  destruct t2;
    simpl;
    try solve [crush].

  (*upper type*)
  destruct s2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t0);
    [crush
    |eapply H in Hneq; eauto].

  (*lower type*)
  destruct s2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t0);
    [crush
    |eapply H in Hneq; eauto].

  (*equal type*)
  destruct s2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t0);
    [crush
    |eapply H in Hneq; eauto].

  (*value type*)
  destruct s2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t0);
    [crush
    |eapply H in Hneq; eauto].

  (*nil type*)
  destruct ss2;
    simpl;
    try solve [crush].

  (*con type*)
  destruct ss2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : d <> d1);
    [intro Hcontra1;
     subst d
    |eapply H in Hneq; eauto];
    assert (Hneq : d0 <> ss2);
    [crush
    |eapply H0 in Hneq; eauto].

  (*new*)
  destruct e2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : d <> d0);
    [crush
    |eapply H in Hneq; eauto].

  (*app*)
  destruct e2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : e <> e2_1);
    [intro Hcontra1;
     subst e
    |eapply H in Hneq; eauto];
    assert (Hneq : e0 <> e2_2);
    [crush
    |eapply H0 in Hneq; eauto].

  (*fn*)
  destruct e2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t1);
    [intro Hcontra1;
     subst t
    |eapply H in Hneq; eauto];
    assert (Hneq : e <> e2);
    [intro Hcontra1;
     subst e
    |eapply H0 in Hneq; eauto];
    assert (Hneq : t0 <> t2);
    [crush
    |eapply H1 in Hneq; eauto].

  (*acc*)
  destruct e2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : e <> e2);
    [crush
    |eapply H in Hneq; eauto].

  (*var*)
  destruct e2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  destruct v, v0;
    try solve [crush].
  simpl in H1; unfold raise_nat in H1.
  destruct (lt_dec n0 n) as [Hlt1|Hlt1];
    assert (Hlt1' := Hlt1);
    [apply Nat.ltb_lt in Hlt1
    |apply Nat.ltb_nlt in Hlt1];
    rewrite Hlt1 in H1;
    [destruct (lt_dec n1 n) as [Hlt2|Hlt2];
     assert (Hlt2' := Hlt2);
     [apply Nat.ltb_lt in Hlt2
     |apply Nat.ltb_nlt in Hlt2];
     rewrite Hlt2 in H1
    |destruct (lt_dec n1 n) as [Hlt2|Hlt2];
     assert (Hlt2' := Hlt2);
     [apply Nat.ltb_lt in Hlt2
     |apply Nat.ltb_nlt in Hlt2];
     rewrite Hlt2 in H1];
    inversion H1; subst;
      try solve [crush].
  apply Nat.add_cancel_r in H2; subst n0; crush.

  (*loc*)
  destruct e2; simpl;
    try solve [crush].

  (*cast*)
  destruct e2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : e <> e2);
    [intro Hcontra1;
     subst e
    |eapply H in Hneq; eauto];
    assert (Hneq : t <> t0);
    [crush
    |eapply H0 in Hneq; eauto].

  (*equal exp*)
  destruct d2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : t <> t0);
    [crush
    |eapply H in Hneq; eauto].

  (*value exp*)
  destruct d2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : e <> e0);
    [intro Hcontra1;
     subst e
    |eapply H in Hneq; eauto];
    assert (Hneq : t <> t0);
    [crush
    |eapply H0 in Hneq; eauto].

  (*nil exp*)
  destruct ds2;
    crush.

  (*con exp*)
  destruct ds2; simpl;
    try solve [crush].
  intro Hcontra;
    inversion Hcontra.
  assert (Hneq : d <> d1);
    [intro Hcontra1;
     subst d
    |eapply H in Hneq; eauto];
    assert (Hneq : d0 <> ds2);
    [crush
    |eapply H0 in Hneq; eauto].    
Qed.

Lemma raise_neq_type :
  (forall t1 t2, t1 <> t2 ->
                 forall n, (t1 raise_t n) <> (t2 raise_t n)).
Proof.
  destruct raise_neq_mutind; crush.
Qed.

Lemma raise_neq_decl_ty :
  (forall s1 s2, s1 <> s2 ->
                 forall n, (s1 raise_s n) <> (s2 raise_s n)).
Proof.
  destruct raise_neq_mutind; crush.
Qed.

Lemma raise_neq_decl_tys :
  (forall ss1 ss2, ss1 <> ss2 ->
                   forall n, (ss1 raise_ss n) <> (ss2 raise_ss n)).
Proof.
  destruct raise_neq_mutind; crush.
Qed.

Lemma raise_neq_exp :    
  (forall e1 e2, e1 <> e2 ->
                 forall n, (e1 raise_e n) <> (e2 raise_e n)).
Proof.
  destruct raise_neq_mutind; crush.
Qed.

Lemma raise_neq_decl :    
  (forall d1 d2, d1 <> d2 ->
                 forall n, (d1 raise_d n) <> (d2 raise_d n)).
Proof.
  destruct raise_neq_mutind; crush.
Qed.

Lemma raise_neq_decls :
  (forall ds1 ds2, ds1 <> ds2 ->
                   forall n, (ds1 raise_ds n) <> (ds2 raise_ds n)).
Proof.
  destruct raise_neq_mutind; crush.
Qed.

Lemma notin_raise_mutind :
  (forall e t, e notin_t t ->
               forall n, (e raise_e n) notin_t  (t raise_t n)) /\
  
  (forall e s, e notin_s s ->
               forall n, (e raise_e n) notin_s  (s raise_s n)) /\
  
  (forall e ss, e notin_ss ss ->
                forall n, (e raise_e n) notin_ss  (ss raise_ss n)) /\
  
  (forall e e', e notin_e e' ->
                forall n, (e raise_e n) notin_e  (e' raise_e n)) /\
  
  (forall e d, e notin_d d ->
               forall n, (e raise_e n) notin_d  (d raise_d n)) /\
  
  (forall e ds, e notin_ds ds ->
                forall n, (e raise_e n) notin_ds  (ds raise_ds n)).
Proof.
  apply notin_mutind; intros; simpl; eauto;
    try solve [apply raise_neq_exp with (n:=n0) in n; auto];
    try solve [apply raise_neq_exp with (n:=n1) in n0; auto];
    try solve [apply raise_neq_exp with (n:=n2) in n1; auto].

  (*arr*)
  apply ni_arr; auto;
    assert (Hni : ((e raise_e 0) raise_e (S n1)) notin_t (t2 raise_t (S n1)));
    [eauto
    |rewrite raise_add_exp in Hni;
     [auto|crush]].

  (*str*)
  apply ni_str; auto;
    assert (Hni : ((e raise_e 0) raise_e (S n0)) notin_ss (ss raise_ss (S n0)));
    [eauto
    |rewrite raise_add_exp in Hni;
     [auto|crush]].

  (*fn*)
  apply ni_fn; eauto;
    apply raise_neq_exp with (n:=n3) in n2;
    eauto;
    assert (Hni1 := (H0 (S n3)));
    assert (Hni2 := (H1 (S n3)));
    rewrite raise_add_exp in Hni1, Hni2;
    crush.

  (*new*)
  apply raise_neq_exp with (n:=n1) in n0; auto.
  apply ni_new; auto.
  assert (Hni := H (S n1));
    rewrite raise_add_exp in Hni;
    crush.
  
Qed.

Lemma notin_raise_type :
  (forall e t, e notin_t t ->
               forall n, (e raise_e n) notin_t  (t raise_t n)).
Proof.
  destruct notin_raise_mutind; crush.
Qed.

Lemma notin_raise_decl_ty :
  (forall e s, e notin_s s ->
               forall n, (e raise_e n) notin_s  (s raise_s n)).
Proof.
  destruct notin_raise_mutind; crush.
Qed.

Lemma notin_raise_decl_tys :
  (forall e ss, e notin_ss ss ->
                forall n, (e raise_e n) notin_ss  (ss raise_ss n)).
Proof.
  destruct notin_raise_mutind; crush.
Qed.

Lemma notin_raise_exp :
  (forall e e', e notin_e e' ->
                forall n, (e raise_e n) notin_e  (e' raise_e n)).
Proof.
  destruct notin_raise_mutind; crush.
Qed.

Lemma notin_raise_decl :
  (forall e d, e notin_d d ->
               forall n, (e raise_e n) notin_d  (d raise_d n)).
Proof.
  destruct notin_raise_mutind; crush.
Qed.

Lemma notin_raise_decls :
  (forall e ds, e notin_ds ds ->
                forall n, (e raise_e n) notin_ds  (ds raise_ds n)).
Proof.
  destruct notin_raise_mutind; crush.
Qed.

Lemma differing_subst_equality_mutind :
  (forall t1 p1 n1
          t2 p2 n2, ([p1 /t n1] t1) = ([p2 /t n2] t2) ->
                    p1 notin_t t1 ->
                    p2 notin_t t2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists t, t1 = ([p2 /t n2] t) /\
                              (p2 notin_t t)) /\
  
  (forall s1 p1 n1
          s2 p2 n2, ([p1 /s n1] s1) = ([p2 /s n2] s2) ->
                    p1 notin_s s1 ->
                    p2 notin_s s2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists s, s1 = ([p2 /s n2] s) /\
                              (p2 notin_s s)) /\
  
  (forall ss1 p1 n1
          ss2 p2 n2, ([p1 /ss n1] ss1) = ([p2 /ss n2] ss2) ->
                     p1 notin_ss ss1 ->
                     p2 notin_ss ss2 ->
                     p1 notin_e p2 ->
                     p2 notin_e p1 ->
                     n1 <> n2 ->
                     closed_exp p2 0 ->
                     exists ss, ss1 = ([p2 /ss n2] ss) /\
                                (p2 notin_ss ss)) /\
  
  (forall e1 p1 n1
          e2 p2 n2, ([p1 /e n1] e1) = ([p2 /e n2] e2) ->
                    p1 notin_e e1 ->
                    p2 notin_e e2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists e, e1 = ([p2 /e n2] e) /\
                              (p2 notin_e e)) /\
  
  (forall d1 p1 n1
          d2 p2 n2, ([p1 /d n1] d1) = ([p2 /d n2] d2) ->
                    p1 notin_d d1 ->
                    p2 notin_d d2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists d, d1 = ([p2 /d n2] d) /\
                              (p2 notin_d d)) /\
  
  (forall ds1 p1 n1
          ds2 p2 n2, ([p1 /ds n1] ds1) = ([p2 /ds n2] ds2) ->
                     p1 notin_ds ds1 ->
                     p2 notin_ds ds2 ->
                     p1 notin_e p2 ->
                     p2 notin_e p1 ->
                     n1 <> n2 ->
                     closed_exp p2 0 ->
                     exists ds, ds1 = ([p2 /ds n2] ds) /\
                                (p2 notin_ds ds)).
Proof.
  apply type_exp_mutind; intros; auto.

  (*str*)
  destruct t2 as [ss'| | | |];
    inversion H0.
  apply H in H8; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto];
    try solve [apply notin_raise_exp; auto].
  destruct H8 as [ss Ha];
    destruct Ha as [Ha Hb].
  exists (str ss rts); subst; auto.
  
  (*sel*)
  destruct t2 as [|p' l'| | |];
    inversion H0;
    subst.
  apply H in H8; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto].
  destruct H8 as [e' Ha];
    destruct Ha as [Ha Hb].
  exists (sel e' l'); split; subst; auto.

  (*arr*)
  destruct t2 as [| |t1' t2'| |];
    inversion H1;
    subst.
  apply H in H9;
    apply H0 in H10;
    auto;
    try solve [inversion H2; auto];
    try solve [inversion H3; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  destruct H9 as [t1 Ha];
    destruct Ha as [Ha Hb];
    destruct H10 as [t2 Hc];
    destruct Hc as [Hc Hd].
  exists (t1 arr t2); split; subst; auto.

  (*top*)
  exists top; auto.

  (*bot*)
  exists bot; auto.

  (*upper type*)
  destruct s2 as [l' t'| | |];
    inversion H0;
    subst.
  apply H in H9; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto].
  destruct H9 as [t'' Ha];
    destruct Ha as [Ha Hb].
  exists (type l' ext t''); split; subst; auto.

  (*lower type*)
  destruct s2 as [|l' t'| |];
    inversion H0;
    subst.
  apply H in H9; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto].
  destruct H9 as [t'' Ha];
    destruct Ha as [Ha Hb].
  exists (type l' sup t''); split; subst; auto.

  (*equal type*)
  destruct s2 as [| |l' t'|];
    inversion H0;
    subst.
  apply H in H9; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto].
  destruct H9 as [t'' Ha];
    destruct Ha as [Ha Hb].
  exists (type l' eqt t''); split; subst; auto.

  (*value type*)
  destruct s2 as [| | |l' t'];
    inversion H0;
    subst.
  apply H in H9; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto].
  destruct H9 as [t'' Ha];
    destruct Ha as [Ha Hb].
  exists (val l' oft t''); split; subst; auto.

  (*nil type*)
  exists dt_nil; auto.

  (*con type*)
  destruct ss2 as [|d' ds'];
    inversion H1;
    subst.
  apply H in H9;
    apply H0 in H10;
    auto;
    try solve [inversion H2; auto];
    try solve [inversion H3; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  destruct H9 as [s Ha];
    destruct Ha as [Ha Hb];
    destruct H10 as [ss Hc];
    destruct Hc as [Hc Hd].
  exists (dt_con s ss); split; subst; auto.

  (*new*)
  destruct e2 as [ds| | | | | |];
    inversion H0.
  apply H in H8; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  destruct H8 as [ds' Ha];
    destruct Ha as [Ha Hb].
  exists (new ds'); split; subst; auto.
  apply ni_new; auto.
  intro Hcontra; subst.
  apply closed_exp_new in H6.
  rewrite closed_subst_decls with (n:=S n2)(ds:=ds') in H0;
    try solve [apply H6; crush].
  rewrite closed_subst_exp with (n:=n1) in H0;
    [|apply <- closed_exp_new; eauto; crush].
  apply subst_notin_itself with (n:=n2) in H2; crush.

  destruct v as [x|x];
    try solve [inversion H8].
  destruct (n2 =? x);
    [|inversion H8].
  assert (Hrewrite : new ([p1 raise_e 0 /ds S n1] d) = [p1 /e n1] (new d));
    [auto|rewrite Hrewrite in H8].
  rewrite <- H8 in H3;
    apply notin_subst_closed_exp in H3;
    rewrite closed_subst_exp in H8; auto.
  exists (a_ n2); split; [|apply ni_var; subst; crush].
  simpl; rewrite <- beq_nat_refl; auto.

  (*app*)
  destruct e2 as [|e1 e2| | | | |];
    inversion H1.
  apply H in H9; auto;
    try solve [inversion H2; auto];
    try solve [inversion H3; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  apply H0 in H10; auto;
    try solve [inversion H2; auto];
    try solve [inversion H3; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  destruct H9 as [e1' Ha];
    destruct Ha as [Ha Hb];
    destruct H10 as [e2' Hc];
    destruct Hc as [Hc Hd].
  exists (e_app e1' e2'); subst; split; auto.
  apply ni_app; auto.
  intro Hcontra; subst.
  apply closed_exp_app in H7;
    destruct H7 as [He Hf].
  rewrite closed_subst_exp with (n:=n2)(e:=e1') in H1;
    try solve [apply He; crush].
  rewrite closed_subst_exp with (n:=n2)(e:=e2') in H1;
    try solve [apply Hf; crush].
  rewrite closed_subst_exp with (n:=n1) in H1;
    [|apply <- (closed_exp_app 0); crush].
  apply subst_notin_itself with (n:=n2) in H3; crush.

  destruct v as [x|x];
    try solve [inversion H9].
  destruct (n2 =? x);
    [|inversion H9].
  assert (Hrewrite : e_app ([p1 /e n1] e) ([p1 /e n1] e0) = [p1 /e n1](e_app e e0));
    [auto|rewrite Hrewrite in H9].
  rewrite <- H9 in H4;
    apply notin_subst_closed_exp in H4;
    rewrite closed_subst_exp in H9; auto.
  exists (a_ n2); split; [|apply ni_var; subst; crush].
  simpl; rewrite <- beq_nat_refl; auto.

  (*fn*)
  destruct e2 as [| |t1 e0 t2| | | |];
    inversion H2.
  apply H in H10; auto;
    try solve [inversion H3; auto];
    try solve [inversion H4; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  apply H0 in H11; auto;
    try solve [inversion H3; auto];
    try solve [inversion H4; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  apply H1 in H12; auto;
    try solve [inversion H3; auto];
    try solve [inversion H4; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  destruct H10 as [t1' Ha];
    destruct Ha as [Ha Hb];
    destruct H11 as [e0' Hc];
    destruct Hc as [Hc Hd];
    destruct H12 as [t2' He];
    destruct He as [He Hf].
  exists (fn t1' in_exp e0' off t2'); subst; split; auto.
  apply ni_fn; auto.
  intro Hcontra; subst.
  apply closed_exp_fn in H8;
    destruct H8 as [Hg Hh];
    destruct Hh as [Hh Hi].
  rewrite closed_subst_type with (n:=n2)(t:=t1') in H2;
    try solve [apply Hg; crush].
  rewrite closed_subst_exp with (n:=S n2)(e:=e0') in H2;
    try solve [apply Hh; crush].
  rewrite closed_subst_type with (n:=S n2)(t:=t2') in H2;
    try solve [apply Hi; crush].
  rewrite closed_subst_exp with (n:=n1) in H2;
    [|apply <- (closed_exp_fn 0); crush].
  apply subst_notin_itself with (n:=n2) in H4; crush.
  
  destruct v as [x|x];
    try solve [inversion H10].
  destruct (n2 =? x);
    [|inversion H10].
  assert (Hrewrite : (fn ([p1 /t n1] t) in_exp ([p1 raise_e 0 /e S n1] e) off ([p1 raise_e 0 /t S n1] t0)) = [p1 /e n1](fn t in_exp e off t0));
    [auto|rewrite Hrewrite in H10].
  rewrite <- H10 in H5;
    apply notin_subst_closed_exp in H5;
    rewrite closed_subst_exp in H10; auto.
  exists (a_ n2); split; [|apply ni_var; subst; crush].
  simpl; rewrite <- beq_nat_refl; auto.

  (*acc*)
  destruct e2 as [| | |e' l'| | |];
    inversion H0.
  apply H in H8; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto];
    try solve [apply notin_raise_exp; auto];
    try solve [rewrite raise_closed_le_exp with (n:=0); auto].
  destruct H8 as [e'' Ha];
    destruct Ha as [Ha Hb].
  exists (e_acc e'' l'); split; subst; auto.
  apply ni_acc; auto.
  intro Hcontra; subst.
  apply closed_exp_acc in H6.
  rewrite closed_subst_exp with (n:=n2)(e:=e'') in H0;
    try solve [apply H6; crush].
  rewrite closed_subst_exp with (n:=n1) in H0;
    [|apply <- closed_exp_acc; eauto; crush].
  apply subst_notin_itself with (n:=n2) in H2; crush.

  destruct v as [x|x];
    try solve [inversion H8].
  destruct (n2 =? x);
    [|inversion H8].
  assert (Hrewrite : e_acc ([p1 /e n1] e) l = [p1 /e n1] (e_acc e l));
    [auto|rewrite Hrewrite in H8].
  rewrite <- H8 in H3;
    apply notin_subst_closed_exp in H3;
    rewrite closed_subst_exp in H8; auto.
  exists (a_ n2); split; [|apply ni_var; subst; crush].
  simpl; rewrite <- beq_nat_refl; auto.
  
  (*var*)
  destruct e2 as [| | | |v'| |];
    try solve [destruct v;
               inversion H];
    try solve [destruct v as [x|x];
               inversion H;
               destruct (n1 =? x);
               [|inversion H7];
               exists (a_ x); split;
               [assert (x = n1);
                [simpl in H ;
                 destruct (Nat.eq_dec n1 x) as [|Hneq];
                 [subst; auto
                 |apply Nat.eqb_neq in Hneq;
                  rewrite Hneq in H;
                  inversion H]
                |subst x];
                simpl;
                apply Nat.eqb_neq in H4;
                rewrite Nat.eqb_sym, H4; auto|];
               apply ni_var;
               intro Hcontra;
               subst p2;
               assert (Hle : 0<=x);
               [crush
               |apply H5 in Hle];
               inversion Hle;
               subst;
               inversion H9; crush].
  destruct v as [x|x];
    destruct v' as [y|y];
    try solve [simpl in H;
               inversion H;
               subst;
               exists (c_ y);
               simpl; split; auto].
  simpl in H;
    exists (a_ y); split; auto.
  simpl in H;
    exists (a_ x);
    simpl;
    destruct (Nat.eq_dec n1 x) as [|Hneq];
    [subst;
     rewrite Nat.eqb_sym;
     apply Nat.eqb_neq in H4;
     rewrite H4;
     split; auto;
     apply ni_var;
     intro Hcontra;
     subst p2;
     assert (Hle : 0 <= x);
     [crush
     |apply H5 in Hle;
      inversion Hle;
      inversion H8;
      crush]
    |apply Nat.eqb_neq in Hneq;
     rewrite Hneq in H;
     inversion H].
  simpl in H;
    destruct (Nat.eq_dec n1 x) as [|Hneq1]; [subst|];
      destruct (Nat.eq_dec n2 y) as [|Hneq2];
      [subst;
       repeat rewrite <- beq_nat_refl in H;
       subst;
       contradiction (notin_refl_contra H2)
      |exists (a_ x);
       simpl;
       apply Nat.eqb_neq in H4;
       rewrite Nat.eqb_sym, H4;
       split;
       auto;
       apply ni_var;
       intro Hcontra;
       subst;
       assert (Hle : 0 <= x);
       [crush
       |apply H5 in Hle;
        inversion Hle;
        inversion H8;
        crush]
      |subst;
       apply Nat.eqb_neq in Hneq1;
       rewrite Hneq1 in H;
       exists (a_ y); simpl;
       split; auto
      |apply Nat.eqb_neq in Hneq1;
       rewrite Hneq1 in H;
       exists (a_ y); split; auto].

  (*loc*)
  destruct e2 as [| | | | |i|];
    inversion H.
  destruct v as [|x];
    [inversion H7|].
  destruct (n2 =? x);
    [subst|inversion H7].
  exists (a_ n2); simpl; rewrite <- beq_nat_refl; split; auto.
  apply ni_var; crush.

  subst; exists (i_ i); split; auto.
  
  (*cast*)
  destruct e2 as [| | | | | |e' t'];
    inversion H1;
    subst.

  destruct v as [x|x];
    try solve [inversion H9].
  destruct (n2 =? x);
    [|inversion H9].
  assert (Hrewrite : (([p1 /e n1] e) cast ([p1 /t n1] t)) = [p1 /e n1] (e cast t));
    [auto|rewrite Hrewrite in H9].
  rewrite <- H9 in H4;
    apply notin_subst_closed_exp in H4;
    rewrite closed_subst_exp in H9; auto.
  exists (a_ n2); split; [|apply ni_var; subst; crush].
  simpl; rewrite <- beq_nat_refl; auto.
  
  apply H in H9; auto;
    try solve [inversion  H2; auto];
    try solve [inversion  H3; auto].
  apply H0 in H10; auto;
    try solve [inversion  H2; auto];
    try solve [inversion  H3; auto].
  destruct H9 as [e0 Ha];
    destruct Ha as [Ha Hb];
    destruct H10 as [t0 Hc];
    destruct Hc as [Hc Hd].
  exists (e0 cast t0); split; subst; auto.
  apply ni_cast; auto.
  intro Hcontra; subst.
  apply closed_exp_cast in H7;
    destruct H7 as [Ha Hc].
  rewrite closed_subst_exp with (n:=n2)(e:=e0), closed_subst_type with (n:=n2)(t:=t0) in H1;
    try solve [apply Ha; crush];
    try solve [apply Hc; crush].
  rewrite closed_subst_exp with (n:=n1) in H1;
    [|apply <- closed_exp_cast; eauto; crush].
  apply subst_notin_itself with (n:=n2) in H3; crush.

  (*equal exp*)
  destruct d2 as [l' t'|];
    inversion H0;
    subst.
  apply H in H9; auto;
    try solve [inversion H1; auto];
    try solve [inversion H2; auto].
  destruct H9 as [t'' Ha];
    destruct Ha as [Ha Hb].
  exists (type l' eqe t''); split; subst; auto.

  (*value exp*)
  destruct d2 as [|l' e' t'];
    inversion H1;
    subst.
  apply H in H10;
    apply H0 in H11; auto;
      try solve [inversion H2; auto];
      try solve [inversion H3; auto].
  destruct H10 as [e'' Ha];
    destruct Ha as [Ha Hb];
    destruct H11 as [t'' Hc];
    destruct Hc as [Hc Hd].
  exists (val l' assgn e'' oft t''); split; subst; auto.

  (*nil exp*)
  exists d_nil; split; auto.

  (*con exp*)
  destruct ds2 as [|d2' ds2'];
    inversion H1;
    subst.
  apply H in H9;
    apply H0 in H10; auto;
      try solve [inversion H2; auto];
      try solve [inversion H3; auto].
  destruct H9 as [d'' Ha];
    destruct Ha as [Ha Hb];
    destruct H10 as [ds'' Hc];
    destruct Hc as [Hc Hd].
  exists (d_con d'' ds''); split; subst; auto.
Qed.

Lemma differing_subst_equality_type :
  (forall t1 p1 n1
          t2 p2 n2, ([p1 /t n1] t1) = ([p2 /t n2] t2) ->
                    p1 notin_t t1 ->
                    p2 notin_t t2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists t, t1 = ([p2 /t n2] t) /\
                              (p2 notin_t t)).
Proof.
  destruct differing_subst_equality_mutind; crush.
Qed.

Lemma differing_subst_equality_decl_ty :
  (forall s1 p1 n1
          s2 p2 n2, ([p1 /s n1] s1) = ([p2 /s n2] s2) ->
                    p1 notin_s s1 ->
                    p2 notin_s s2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists s, s1 = ([p2 /s n2] s) /\
                              (p2 notin_s s)).
Proof.
  destruct differing_subst_equality_mutind; crush.
Qed.

Lemma differing_subst_equality_decl_tys :  
  (forall ss1 p1 n1
          ss2 p2 n2, ([p1 /ss n1] ss1) = ([p2 /ss n2] ss2) ->
                     p1 notin_ss ss1 ->
                     p2 notin_ss ss2 ->
                     p1 notin_e p2 ->
                     p2 notin_e p1 ->
                     n1 <> n2 ->
                     closed_exp p2 0 ->
                     exists ss, ss1 = ([p2 /ss n2] ss) /\
                                (p2 notin_ss ss)).
Proof.
  destruct differing_subst_equality_mutind; crush.
Qed.

Lemma differing_subst_equality_exp :  
  (forall e1 p1 n1
          e2 p2 n2, ([p1 /e n1] e1) = ([p2 /e n2] e2) ->
                    p1 notin_e e1 ->
                    p2 notin_e e2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists e, e1 = ([p2 /e n2] e) /\
                              (p2 notin_e e)).
Proof.
  destruct differing_subst_equality_mutind; crush.
Qed.

Lemma differing_subst_equality_decl :  
  (forall d1 p1 n1
          d2 p2 n2, ([p1 /d n1] d1) = ([p2 /d n2] d2) ->
                    p1 notin_d d1 ->
                    p2 notin_d d2 ->
                    p1 notin_e p2 ->
                    p2 notin_e p1 ->
                    n1 <> n2 ->
                    closed_exp p2 0 ->
                    exists d, d1 = ([p2 /d n2] d) /\
                              (p2 notin_d d)).
Proof.
  destruct differing_subst_equality_mutind; crush.
Qed.

Lemma differing_subst_equality_decls :  
  (forall ds1 p1 n1
          ds2 p2 n2, ([p1 /ds n1] ds1) = ([p2 /ds n2] ds2) ->
                     p1 notin_ds ds1 ->
                     p2 notin_ds ds2 ->
                     p1 notin_e p2 ->
                     p2 notin_e p1 ->
                     n1 <> n2 ->
                     closed_exp p2 0 ->
                     exists ds, ds1 = ([p2 /ds n2] ds) /\
                                (p2 notin_ds ds)).
Proof.
  destruct differing_subst_equality_mutind; crush.
Qed.

Lemma wf_unbound_mutind :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall r, r >= length G ->
                 r unbound_t t) /\
  
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall r, r >= length G ->
                 r unbound_s s) /\
  
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall r, r >= length G ->
                  r unbound_ss ss) /\
  
  (forall Sig G e, Sig en G vdash e wf_e ->
            forall r, r >= length G ->
                 r unbound_e e) /\
  
  (forall Sig G d, Sig en G vdash d wf_d ->
            forall r, r >= length G ->
                 r unbound_d d) /\
  
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
             forall r, r >= length G ->
                  r unbound_ds ds).
Proof.
  apply wf_mutind; intros; auto.

  (*arr*)
  apply ub_arr; auto;
    apply le_lt_or_eq in H1;
    destruct H1 as [Ha|Ha];
    subst;
    auto;
    destruct r as [|r'];
    [crush|];
    eapply unbound_subst_type;
    eapply (H0 (S r')); crush.

  (*str*)
  apply ub_str; auto;
    apply le_lt_or_eq in H0;
    destruct H0 as [Ha|Ha];
    subst;
    auto;
    destruct r as [|r'];
    [crush|];
    eapply unbound_subst_decl_tys;
    eapply (H (S r')); crush.

  (*var*)
  crush.

  (*fn*)
  apply ub_fn; auto;
    apply le_lt_or_eq in H2;
    destruct H2 as [Ha|Ha];
    subst;
    auto;
    [destruct r as [|r'];
     [crush|];
     eapply unbound_subst_exp;
     eapply (H0 (S r')); crush
    |destruct r as [|r'];
     [crush|];
     eapply unbound_subst_type;
     eapply (H1 (S r')); crush].

  (*new*)
  apply ub_new; auto;
    apply le_lt_or_eq in H0;
    destruct H0 as [Ha|Ha];
    subst;
    auto;
    destruct r as [|r'];
    [crush|];
    eapply unbound_subst_decls;
    eapply (H (S r')); crush.
  
Qed.

Lemma wf_unbound_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall r, r >= length G ->
                 r unbound_t t).
Proof.
  destruct wf_unbound_mutind; crush.
Qed.

Lemma wf_unbound_decl_ty :
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall r, r >= length G ->
                 r unbound_s s).
Proof.
  destruct wf_unbound_mutind; crush.
Qed.

Lemma wf_unbound_decl_tys :
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
             forall r, r >= length G ->
                  r unbound_ss ss).
Proof.
  destruct wf_unbound_mutind; crush.
Qed.

Lemma wf_unbound_exp :
  (forall Sig G e, Sig en G vdash e wf_e ->
            forall r, r >= length G ->
                 r unbound_e e).
Proof.
  destruct wf_unbound_mutind; crush.
Qed.

Lemma wf_unbound_decl :
  (forall Sig G d, Sig en G vdash d wf_d ->
            forall r, r >= length G ->
                 r unbound_d d).
Proof.
  destruct wf_unbound_mutind; crush.
Qed.

Lemma wf_unbound_decls :
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
             forall r, r >= length G ->
                  r unbound_ds ds).
Proof.
  destruct wf_unbound_mutind; crush.
Qed.

Lemma wf_notin_env :
  (forall Sig G, Sig evdash G  wf_env ->
          forall r, r >= length G ->
               (c_ r) notin_env G).
Proof.
  intros Sig G Hwf;
    induction Hwf;
    intros;
    auto.
  intros t Hin;
    inversion Hin.

  intros t' Hin;
    inversion Hin;
    [subst t';
     apply unbound_var_notin_type;
     eapply wf_unbound_type;
     eauto|].
  simpl in  H0;
    crush.

  apply IHHwf;
    crush.
Qed.

Lemma wf_notin_store_type :
  (forall Sig, Sig wf_st ->
        forall r, (c_ r) notin_env Sig).
Proof.
  intros Sig Hwf;
    induction Hwf;
    intros.
  
  intros t Hin;
    inversion Hin.

  intros t Hin;
    inversion Hin;
    subst.

  apply unbound_var_notin_type.
  eapply wf_unbound_type;
    eauto;
    crush.

  apply IHHwf;
    auto.
  
Qed.

Lemma unbound_in_decl_unbound_in_type :
  forall d r, r unbound_d d ->
         forall Sig G s, Sig en G vdash d hasType_d s ->
                  r unbound_s s.
Proof.
  intro d; destruct d; intros.

  inversion H0; subst; auto.
  inversion H; auto.

  inversion H0; subst; auto.
  inversion H; auto.
Qed.

Lemma notin_decl_notin_type :
  forall Sig G d s, Sig en G vdash d hasType_d s ->
             forall p n d', d = ([p /d n] d') ->
                       p notin_d d' ->
                       exists s', s = ([p /s n] s') /\
                             p notin_s s'.
Proof.
  intros Sig G d s Htyp; inversion Htyp; intros; auto.

  destruct d';
    inversion H3;
    subst L t.
  exists (type l eqt t0); simpl; subst; split; auto.
  inversion H4; auto.

  destruct d';
    inversion H5;
    subst.
  exists (val l0 oft t0); simpl; subst; split; auto.
  inversion H6; auto.
Qed.

Lemma notin_decls_notin_types :
  forall Sig G ds ss, Sig en G vdash ds hasType_ds ss ->
               forall p n ds', ds = ([p /ds n] ds') ->
                          p notin_ds ds' ->
                          exists ss', ss = ([p /ss n] ss') /\
                                 p notin_ss ss'.
Proof.
  intros Sig G ds ss Htyp;
    induction Htyp; intros; auto.

  exists dt_nil; split; auto.

  destruct ds' as [|d'' ds''];
    inversion H0;
    subst d ds.
  apply notin_decl_notin_type with (p:=p)(n:=n)(d':=d'') in H; auto;
    [|inversion H1; auto].
  destruct H as [s'' Ha];
    destruct Ha as [Ha Hb];
    subst s.
  destruct IHHtyp with (p0:=p)(n0:=n)(ds':=ds'') as [ss'' Hc]; auto;
    [inversion H1; auto
    |destruct Hc as [Hc Hd]];
    subst ss.
  exists (dt_con s'' ss''); simpl; subst; split; auto.
Qed.

Lemma rename_is_closed_mutind :
  (forall t n m, n <> m -> closed_t n (t [n maps_t m])) /\
  
  (forall s n m, n <> m -> closed_s n (s [n maps_s m])) /\
  
  (forall ss n m, n <> m -> closed_ss n (ss [n maps_ss m])) /\
  
  (forall e n m, n <> m -> closed_e n (e [n maps_e m])) /\
  
  (forall d n m, n <> m -> closed_d n (d [n maps_d m])) /\
  
  (forall ds n m, n <> m -> closed_ds n (ds [n maps_ds m])).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [crush].

  (*var*)
  destruct v as [x|x]; simpl; auto.
  destruct (Nat.eq_dec x n) as [Heq|Hneq];
    [subst;
     rewrite rename_eq
    |rewrite rename_neq;
     auto].
  apply cl_var, cl_abstract; auto.
Qed.

Lemma rename_is_closed_type :
  (forall t n m, n <> m -> closed_t n (t [n maps_t m])).
Proof.
  destruct rename_is_closed_mutind; crush.
Qed.

Lemma rename_is_closed_decl_ty :
  (forall s n m, n <> m -> closed_s n (s [n maps_s m])).
Proof.
  destruct rename_is_closed_mutind; crush.
Qed.

Lemma rename_is_closed_decl_tys :
  (forall ss n m, n <> m -> closed_ss n (ss [n maps_ss m])).
Proof.
  destruct rename_is_closed_mutind; crush.
Qed.

Lemma rename_is_closed_exp :
  (forall e n m, n <> m -> closed_e n (e [n maps_e m])).
Proof.
  destruct rename_is_closed_mutind; crush.
Qed.

Lemma rename_is_closed_decl :
  (forall d n m, n <> m -> closed_d n (d [n maps_d m])).
Proof.
  destruct rename_is_closed_mutind; crush.
Qed.

Lemma rename_is_closed_decls :
  (forall ds n m, n <> m -> closed_ds n (ds [n maps_ds m])).
Proof.
  destruct rename_is_closed_mutind; crush.
Qed.
Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Import definitions.
Require Import common.
Require Import weakening.
Set Implicit Arguments.

(*left jump definitions*)

Definition left_jump_n (r i n : nat) : nat :=
  if i <=? r
  then r - n
  else r.

Notation "r '[' i ']' 'ljump_n' n" := (left_jump_n r i n) (at level  80).

Reserved Notation "v '[' i ']' 'ljump_v' n" (at level 80).
Reserved Notation "t '[' i ']' 'ljump_t' n" (at level 80).
Reserved Notation "d '[' i ']' 'ljump_s' n" (at level 80).
Reserved Notation "d '[' i ']' 'ljump_ss' n" (at level 80).
Reserved Notation "d '[' i ']' 'ljump_d' n" (at level 80).
Reserved Notation "d '[' i ']' 'ljump_ds' n" (at level 80).
Reserved Notation "p '[' i ']' 'ljump_e' n" (at level 80).


Fixpoint left_jump_v (x : var)(i n : nat) : var :=
  match x with
  | Var r => Var (r[i] ljump_n n)
  | _ => x
  end.

Notation "x '[' i ']' 'ljump_v' n" := (left_jump_v x i n) (at level  80).

Fixpoint left_jump_t (t : ty) (i n : nat) : ty  :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => (t1 [i] ljump_t n) arr (t2 [i] ljump_t n)
  | sel p l => sel (p [i] ljump_e n) l
  | str ss rts => str (ss [i] ljump_ss n) rts
  end
where "t '[' i ']' 'ljump_t' n" := (left_jump_t t i n)

with
left_jump_d_ty (s : decl_ty) (i n : nat) : decl_ty :=
  match s with
  | type l sup t => type l sup (t[i] ljump_t n)
  | type l ext t => type l ext (t[i] ljump_t n)
  | type l eqt t => type l eqt (t[i] ljump_t n)
  | val l oft t => val l oft (t[i] ljump_t n)
  end
where "d '[' i ']' 'ljump_s' n" := (left_jump_d_ty d i n)

with
left_jump_d_tys (ss : decl_tys) (i n : nat) : decl_tys :=
  match ss with 
  | dt_nil => dt_nil
  | dt_con s ss' => dt_con (s [i] ljump_s n) (ss' [i] ljump_ss n)
  end
where "d '[' i ']' 'ljump_ss' n" := (left_jump_d_tys d i n)

with
left_jump_e (e : exp) (i n : nat) : exp :=
  match e with
  | new ds => new (ds [i] ljump_ds n)
  | e_app e1 e2 => e_app (e1 [i] ljump_e n) (e2 [i] ljump_e n)
  | fn t1 in_exp e off t2 => fn (t1 [i] ljump_t n) in_exp (e [i] ljump_e n) off (t2 [i] ljump_t n)
  | e_acc e m => e_acc (e [i] ljump_e n) m
  | v_ x => v_ (x [i] ljump_v n)
  | i_ i => i_ i
  | e cast t => (e [i] ljump_e n) cast (t [i] ljump_t n)
  end
where "e '[' i ']' 'ljump_e' n" := (left_jump_e e i n)        
                                     
with
left_jump_d (d : decl) (i n : nat) : decl :=
  match d with
  | type l eqe t => type l eqe (t[i] ljump_t n)
  | val l assgn e oft t => val l assgn (e[i] ljump_e n) oft (t [i] ljump_t n)
  end
where "d '[' i ']' 'ljump_d' n" := (left_jump_d d i n)

with
left_jump_ds (ds : decls) (i n : nat) : decls :=
  match ds with
  | d_nil => d_nil
  | d_con d ds' => d_con (d [i] ljump_d n) (ds' [i] ljump_ds n)
  end
where "d '[' i ']' 'ljump_ds' n" := (left_jump_ds d i n).

Definition left_jump_env (G : env)(i n : nat) : env :=
  map (fun (t : ty) => t [i] ljump_t n) G.

Notation "G '[' i ']' 'ljump_env' n" :=(left_jump_env G i n)(at level 80).

(*range unbound definitions*)



Definition range_unbound_t (n1 n2 : nat)(t : ty):= forall r, r >= n1 ->
                                                     r < n2 ->
                                                     r unbound_t t.

Definition range_unbound_s (n1 n2 : nat)(s : decl_ty):= forall r, r >= n1 ->
                                                           r < n2 ->
                                                           r unbound_s s.

Definition range_unbound_ss (n1 n2 : nat)(ss : decl_tys):= forall r, r >= n1 ->
                                                              r < n2 ->
                                                              r unbound_ss ss.

Definition range_unbound_e (n1 n2 : nat)(e : exp):= forall r, r >= n1 ->
                                                       r < n2 ->
                                                       r unbound_e e.

Definition range_unbound_d (n1 n2 : nat)(d : decl):= forall r, r >= n1 ->
                                                     r < n2 ->
                                                     r unbound_d d.

Definition range_unbound_ds (n1 n2 : nat)(ds : decls):= forall r, r >= n1 ->
                                                           r < n2 ->
                                                           r unbound_ds ds.

Definition range_unbound_v (n1 n2 : nat)(v : var):= forall r, r >= n1 ->
                                                       r < n2 ->
                                                       r unbound_v v.

Notation "'[' n1 'dots' n2 ']' 'runbound_t' t" := (range_unbound_t n1 n2 t)(at level 80).
Notation "'[' n1 'dots' n2 ']' 'runbound_s' s" := (range_unbound_s n1 n2 s)(at level 80).
Notation "'[' n1 'dots' n2 ']' 'runbound_ss' ss" := (range_unbound_ss n1 n2 ss)(at level 80).
Notation "'[' n1 'dots' n2 ']' 'runbound_e' e" := (range_unbound_e n1 n2 e)(at level 80).
Notation "'[' n1 'dots' n2 ']' 'runbound_d' d" := (range_unbound_d n1 n2 d)(at level 80).
Notation "'[' n1 'dots' n2 ']' 'runbound_ds' ds" := (range_unbound_ds n1 n2 ds)(at level 80).
Notation "'[' n1 'dots' n2 ']' 'runbound_v' ds" := (range_unbound_v n1 n2 ds)(at level 80).

Definition range_unbound_env (n1 n2 : nat)(G : env) := forall t, In t G ->
                                                        [n1 dots n2] runbound_t t.

Notation "'[' n1 'dots' n2 ']' 'runbound_env' G" := (range_unbound_env n1 n2 G)(at level 80).

(*Lemmas*)

Lemma ljump_0_mutind :
  (forall t i, (t [i] ljump_t 0) = t) /\
  
  (forall s i, (s [i] ljump_s 0) = s) /\
  
  (forall ss i, (ss [i] ljump_ss 0) = ss) /\
  
  (forall e i, (e [i] ljump_e 0) = e) /\
  
  (forall d i, (d [i] ljump_d 0) = d) /\
  
  (forall ds i, (ds [i] ljump_ds 0) = ds).
Proof.
  apply type_exp_mutind; intros; crush.

  destruct v as [x|x]; simpl;
    auto.

  unfold left_jump_n;
    destruct (i <=? x);
    try rewrite <- minus_n_O;
    auto.
Qed.

Lemma ljump_0_type :
  (forall t i, (t [i] ljump_t 0) = t).
Proof.
  destruct ljump_0_mutind; crush.
Qed.

Hint Rewrite ljump_0_type.
Hint Resolve ljump_0_type.  

Lemma ljump_0_decl_ty :
  (forall s i, (s [i] ljump_s 0) = s).
Proof.
  destruct ljump_0_mutind; crush.
Qed.

Hint Rewrite ljump_0_decl_ty.
Hint Resolve ljump_0_decl_ty.  

Lemma ljump_0_decl_tys :
  (forall ss i, (ss [i] ljump_ss 0) = ss).
Proof.
  destruct ljump_0_mutind; crush.
Qed.

Hint Rewrite ljump_0_decl_tys.
Hint Resolve ljump_0_decl_tys.  

Lemma ljump_0_exp :
  (forall e i, (e [i] ljump_e 0) = e).
Proof.
  destruct ljump_0_mutind; crush.
Qed.

Hint Rewrite ljump_0_exp.
Hint Resolve ljump_0_exp.  

Lemma ljump_0_decl :
  (forall d i, (d [i] ljump_d 0) = d).
Proof.
  destruct ljump_0_mutind; crush.
Qed.

Hint Rewrite ljump_0_decl.
Hint Resolve ljump_0_decl.  

Lemma ljump_0_decls :
  (forall ds i, (ds [i] ljump_ds 0) = ds).
Proof.
  destruct ljump_0_mutind; crush.
Qed.

Hint Rewrite ljump_0_decls.
Hint Resolve ljump_0_decls.

Lemma ljump_0_env :
  (forall G i, (G [i] ljump_env 0) = G).
Proof.
  intro G;
    induction G as [|t' G'];
    intros;
    simpl;
    crush.
Qed.

Hint Rewrite ljump_0_env.
Hint Resolve ljump_0_env.

Lemma ljump_get_some :
  forall G r t, get r G = Some t ->
                forall i n, get r (G [i] ljump_env n) = Some (t [i] ljump_t  n).
Proof.
  intro G;
    induction G as [|t' G'];
    intros.

  rewrite get_empty in H;
    auto;
    inversion H.

  destruct r as [|r'];
    simpl in *;
    [inversion H;
     subst;
     auto|auto].
Qed.

Lemma ljump_app :
  forall G1 G2 i n, (G1 ++ G2 [i] ljump_env n) = (G1 [i] ljump_env n) ++ (G2 [i] ljump_env n).
Proof.
  intro G1;
    induction G1 as [|t' G'];
    intros;
    simpl in *;
    auto.

  rewrite IHG';
    auto.
Qed.

Lemma rev_ljump :
  forall G i n, rev (G [i] ljump_env n) = ((rev G) [i] ljump_env n).
Proof.
  intros.
  unfold left_jump_env;
    rewrite <- map_rev;
    auto.
Qed.

Lemma ljump_length :
  forall G i n, length (G [i] ljump_env n) = length G.
Proof.
  intros.
  unfold left_jump_env;
    rewrite map_length;
    auto.
Qed.


Lemma ljump_mapping :
  forall G r t, r mapsto t elem G ->
           forall i n, r mapsto (t [i] ljump_t  n) elem (G [i] ljump_env n).
Proof.
  intros.
  unfold mapping in *.
  rewrite rev_ljump.
  apply ljump_get_some;
    auto.
Qed.

Lemma ljump_is_path :
  forall p, is_path p ->
       forall i n, is_path (p [i] ljump_e n).
Proof.
  intros p Hpath;
    induction Hpath;
    intros;
    simpl;
    auto.
Qed.


Lemma unbound_range_var :
  forall i1 i2 n, [i1 dots i2] runbound_e (c_ n) <->
             n < i1 \/ n >= i2.
Proof.
  split; intros.

  destruct (le_lt_dec i1 n);
    auto.
  destruct (le_lt_dec i2 n);
    auto.
  apply H in l.
  apply l in l0.
  inversion l0; subst.
  inversion H2;
    crush.

  intros n' Hge Hlt.
  destruct H;
    crush.
Qed.



Lemma ljump_raise_mutind :
  (forall t n i m, ((t raise_t n) [i] ljump_t m) = ((t [i] ljump_t m) raise_t n)) /\
  
  (forall s n i m, ((s raise_s n) [i] ljump_s m) = ((s [i] ljump_s m) raise_s n)) /\
  
  (forall ss n i m, ((ss raise_ss n) [i] ljump_ss m) = ((ss [i] ljump_ss m) raise_ss n)) /\
  
  (forall e n i m, ((e raise_e n) [i] ljump_e m) = ((e [i] ljump_e m) raise_e n)) /\
  
  (forall d n i m, ((d raise_d n) [i] ljump_d m) = ((d [i] ljump_d m) raise_d n)) /\
  
  (forall ds n i m, ((ds raise_ds n) [i] ljump_ds m) = ((ds [i] ljump_ds m) raise_ds n)).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [simpl;
               rewrite H;
               try rewrite H0;
               try rewrite H1;
               auto].

  destruct v as [x|x]; simpl; auto.
Qed.

Lemma ljump_raise_type :
  (forall t n i m, ((t raise_t n) [i] ljump_t m) = ((t [i] ljump_t m) raise_t n)).
Proof.
  destruct ljump_raise_mutind; crush.
Qed.

Lemma ljump_raise_decl_ty :
  (forall s n i m, ((s raise_s n) [i] ljump_s m) = ((s [i] ljump_s m) raise_s n)).
Proof.
  destruct ljump_raise_mutind; crush.
Qed.

Lemma ljump_raise_decl_tys :    
  (forall ss n i m, ((ss raise_ss n) [i] ljump_ss m) = ((ss [i] ljump_ss m) raise_ss n)).
Proof.
  destruct ljump_raise_mutind; crush.
Qed.

Lemma ljump_raise_exp :    
  (forall e n i m, ((e raise_e n) [i] ljump_e m) = ((e [i] ljump_e m) raise_e n)).
Proof.
  destruct ljump_raise_mutind; crush.
Qed.

Lemma ljump_raise_decl :    
  (forall d n i m, ((d raise_d n) [i] ljump_d m) = ((d [i] ljump_d m) raise_d n)).
Proof.
  destruct ljump_raise_mutind; crush.
Qed.

Lemma ljump_raise_decls :    
  (forall ds n i m, ((ds raise_ds n) [i] ljump_ds m) = ((ds [i] ljump_ds m) raise_ds n)).
Proof.
  destruct ljump_raise_mutind; crush.
Qed.

Lemma ljump_subst_distr_mutind :
  (forall t p n i m, (([p /t n] t) [i] ljump_t m) = ([(p [i] ljump_e m) /t n] (t [i] ljump_t m))) /\
  
  (forall s p n i m, (([p /s n] s) [i] ljump_s m) = ([(p [i] ljump_e m) /s n] (s [i] ljump_s m))) /\
  
  (forall ss p n i m, (([p /ss n] ss) [i] ljump_ss m) = ([(p [i] ljump_e m) /ss n] (ss [i] ljump_ss m))) /\
  
  (forall e p n i m, (([p /e n] e) [i] ljump_e m) = ([(p [i] ljump_e m) /e n] (e [i] ljump_e m))) /\
  
  (forall d p n i m, (([p /d n] d) [i] ljump_d m) = ([(p [i] ljump_e m) /d n] (d [i] ljump_d m))) /\
  
  (forall ds p n i m, (([p /ds n] ds) [i] ljump_ds m) = ([(p [i] ljump_e m) /ds n] (ds [i] ljump_ds m))).
Proof.
  apply type_exp_mutind; intros;
    auto;
    try solve [simpl;
               try rewrite <- ljump_raise_exp;
               rewrite H;
               try rewrite H0;
               try rewrite H1;
               auto].

  (*var*)
  destruct v as [x|x]; simpl; auto.
  destruct (n =? x); simpl; auto.
  
Qed.

Lemma ljump_subst_distr_type :
  (forall t p n i m, (([p /t n] t) [i] ljump_t m) = ([(p [i] ljump_e m) /t n] (t [i] ljump_t m))).
Proof.
  destruct ljump_subst_distr_mutind; crush.
Qed.

Lemma ljump_subst_distr_decl_ty :    
  (forall s p n i m, (([p /s n] s) [i] ljump_s m) = ([(p [i] ljump_e m) /s n] (s [i] ljump_s m))).
Proof.
  destruct ljump_subst_distr_mutind; crush.
Qed.

Lemma ljump_subst_distr_decl_tys :    
  (forall ss p n i m, (([p /ss n] ss) [i] ljump_ss m) = ([(p [i] ljump_e m) /ss n] (ss [i] ljump_ss m))).
Proof.
  destruct ljump_subst_distr_mutind; crush.
Qed.

Lemma ljump_subst_distr_exp :    
  (forall e p n i m, (([p /e n] e) [i] ljump_e m) = ([(p [i] ljump_e m) /e n] (e [i] ljump_e m))).
Proof.
  destruct ljump_subst_distr_mutind; crush.
Qed.

Lemma ljump_subst_distr_decl :    
  (forall d p n i m, (([p /d n] d) [i] ljump_d m) = ([(p [i] ljump_e m) /d n] (d [i] ljump_d m))).
Proof.
  destruct ljump_subst_distr_mutind; crush.
Qed.

Lemma ljump_subst_distr_decls :    
  (forall ds p n i m, (([p /ds n] ds) [i] ljump_ds m) = ([(p [i] ljump_e m) /ds n] (ds [i] ljump_ds m))).
Proof.
  destruct ljump_subst_distr_mutind; crush.
Qed.

Lemma ljump_in_dty :
  forall s ss, in_dty s ss ->
               forall i n, in_dty (s [i] ljump_s n) (ss [i] ljump_ss n).
Proof.
  intros s ss Hin;
    induction Hin;
    intros;
    simpl.
  
  apply in_head_dty.

  apply in_tail_dty; auto.
Qed.

Lemma in_dty_ljump_converse :
  forall s ss, in_dty s ss ->
               forall i n ss', ss = (ss' [i] ljump_ss n) ->
                               exists s', in_dty s' ss' /\ (s' [i] ljump_s n) = s.
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


Lemma id_t_ljump :
  forall s i n, id_t s = id_t (s [i] ljump_s n).
Proof.
  intros.
  destruct s; crush.
Qed.

Lemma id_d_ljump :
  forall d i n, id_d d = id_d (d [i] ljump_d n).
Proof.
  intros.
  destruct d; crush.
Qed.

Lemma not_in_decl_tys_ljump:
  forall s ss,
    (forall s', in_dty s' ss -> id_t s' <> id_t s) ->
    forall i n s', in_dty s' (ss [i]ljump_ss n) -> id_t s' <> id_t (s [i]ljump_s n).
Proof.
  intros.
  intros Hcontra.
  apply in_dty_ljump_converse with (i:=i)(n:=n)(ss':=ss) in H0; auto.
  destruct H0 as [s'' Ha];
    destruct Ha as [Ha Hb]; subst.
  repeat rewrite <- id_t_ljump in Hcontra.
  apply H in Ha.
  rewrite Hcontra in Ha;
    contradiction Ha; auto.
Qed.



Lemma in_d_ljump_converse :
  forall d ds, in_d d ds ->
               forall i n ds', ds = (ds' [i] ljump_ds n) ->
                               exists d', in_d d' ds' /\ (d' [i] ljump_d n) = d.
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

Lemma not_in_decls_ljump :
  forall d ds, (forall d', in_d d' ds ->
                 id_d d' <> id_d d) ->
          forall i n,
            (forall d', in_d d' (ds [i] ljump_ds n) ->
                   id_d d' <> id_d (d [i] ljump_d n)).
Proof.
  intros.
  intros Hcontra.
  apply in_d_ljump_converse with (i:=i)(n:=n)(ds':=ds) in H0; auto.
  destruct H0 as [d'' Ha];
    destruct Ha as [Ha Hb]; subst.
  repeat rewrite <- id_d_ljump in Hcontra.
  apply H in Ha.
  rewrite Hcontra in Ha;
    contradiction Ha; auto.
Qed.

Lemma unbound_in_dty :
  forall s ss, in_dty s ss ->
          forall n, n unbound_ss ss ->
               n unbound_s s.
Proof.
  intros s ss Hin;
    induction Hin;
    intros.
  
  inversion H;
    auto.
  
  apply IHHin;
    inversion H;
    auto.
Qed.

Lemma range_unbound_in_dty :
  forall s ss, in_dty s ss ->
          forall i1 i2, [i1 dots i2] runbound_ss ss ->
                   [i1 dots i2] runbound_s s.
Proof.
  intros.

  intros n' Hin Hlt.
  apply unbound_in_dty with (ss:=ss);
    auto.
Qed.

Lemma range_unbound_ty_arr :
  forall i1 i2 t1 t2, [i1 dots i2] runbound_t (t1 arr t2) <-> ([i1 dots i2] runbound_t t1 /\
                                          [i1 dots i2] runbound_t t2).
Proof.
  split; intros.
  
  split; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  destruct H as [Ha Hb].
  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_ty_arr.
Hint Resolve range_unbound_ty_arr.

Lemma range_unbound_ty_sel :
  forall i1 i2 p l, [i1 dots i2] runbound_t (sel p l) <-> ([i1 dots i2] runbound_e p).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_ty_sel.
Hint Resolve range_unbound_ty_sel.

Lemma range_unbound_ty_str :
  forall i1 i2 ss, [i1 dots i2] runbound_t (str ss rts) <-> ([i1 dots i2] runbound_ss ss).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_ty_str.
Hint Resolve range_unbound_ty_str.

Lemma range_unbound_decl_ty_upper :
  forall i1 i2 l t, [i1 dots i2] runbound_s (type l ext t) <-> ([i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_decl_ty_upper.
Hint Resolve range_unbound_decl_ty_upper.

Lemma range_unbound_decl_ty_lower :
  forall i1 i2 l t, [i1 dots i2] runbound_s (type l sup t) <-> ([i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_decl_ty_lower.
Hint Resolve range_unbound_decl_ty_lower.

Lemma range_unbound_decl_ty_equal :
  forall i1 i2 l t, [i1 dots i2] runbound_s (type l eqt t) <-> ([i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_decl_ty_equal.
Hint Resolve range_unbound_decl_ty_equal.

Lemma range_unbound_decl_ty_value :
  forall i1 i2 l t, [i1 dots i2] runbound_s (val l oft t) <-> ([i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_decl_ty_value.
Hint Resolve range_unbound_decl_ty_value.

Lemma range_unbound_decl_tys_nil :
  forall i1 i2, [i1 dots i2] runbound_ss dt_nil.
Proof.
  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_decl_tys_nil.
Hint Resolve range_unbound_decl_tys_nil.

Lemma range_unbound_decl_tys_cons :
  forall i1 i2 s ss, [i1 dots i2] runbound_ss (dt_con s ss) <-> ([i1 dots i2] runbound_s s /\
                                                                 [i1 dots i2] runbound_ss ss).
Proof.
  split; intros.
  
  split; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt;
    crush.
Qed.

Hint Rewrite range_unbound_decl_tys_cons.
Hint Resolve range_unbound_decl_tys_cons.

Lemma range_unbound_exp_loc :
  forall i1 i2 i, [i1 dots i2] runbound_e (i_ i).
Proof.
  intros; crush.
  intros n' Hge Hlt;
    auto.
Qed.

Hint Rewrite range_unbound_exp_loc.
Hint Resolve range_unbound_exp_loc.

Lemma range_unbound_exp_cast :
  forall i1 i2 e t, [i1 dots i2] runbound_e (e cast t) <-> ([i1 dots i2] runbound_e e /\
                                                            [i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  split; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  destruct H as [Ha Hb].
  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_exp_cast.
Hint Resolve range_unbound_exp_cast.

Lemma range_unbound_exp_new :
  forall i1 i2 ds, [i1 dots i2] runbound_e (new ds) <-> ([i1 dots i2] runbound_ds ds).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_exp_new.
Hint Resolve range_unbound_exp_new.

Lemma range_unbound_exp_app :
  forall i1 i2 e1 e2, [i1 dots i2] runbound_e (e_app e1 e2) <-> ([i1 dots i2] runbound_e e1 /\
                                                                 [i1 dots i2] runbound_e e2).
Proof.
  split; intros.
  
  split; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  destruct H as [Ha Hb].
  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_exp_app.
Hint Resolve range_unbound_exp_app.

Lemma range_unbound_exp_acc :
  forall i1 i2 e l, [i1 dots i2] runbound_e (e_acc e l) <-> ([i1 dots i2] runbound_e e).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_exp_acc.
Hint Resolve range_unbound_exp_acc.

Lemma range_unbound_exp_fn :
  forall i1 i2 t1 e t2, [i1 dots i2] runbound_e (fn t1 in_exp e off t2) <-> ([i1 dots i2] runbound_t t1 /\
                                                                             [i1 dots i2] runbound_e e /\
                                                                             [i1 dots i2] runbound_t t2).
Proof.
  split; intros.
  
  split; [|split]; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  destruct H as [Ha Hb];
    destruct Hb as [Hb Hc].
  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_exp_fn.
Hint Resolve range_unbound_exp_fn.

Lemma range_unbound_decl_value :
  forall i1 i2 l e t, [i1 dots i2] runbound_d (val l assgn e oft t) <-> ([i1 dots i2] runbound_e e /\
                                                                         [i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  split; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  destruct H;
    intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_decl_value.
Hint Resolve range_unbound_decl_value.

Lemma range_unbound_decl_equal :
  forall i1 i2 l t, [i1 dots i2] runbound_d (type l eqe t) <-> ([i1 dots i2] runbound_t t).
Proof.
  split; intros.
  
  intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_decl_equal.
Hint Resolve range_unbound_decl_equal.

Lemma range_unbound_decls_nil :
  forall i1 i2, [i1 dots i2] runbound_ds d_nil.
Proof.
  intros.
  intros n' Hge Hlt;
    auto.
Qed.

Hint Rewrite range_unbound_decls_nil.
Hint Resolve range_unbound_decls_nil.

Lemma range_unbound_decls_cons :
  forall i1 i2 d ds, [i1 dots i2] runbound_ds (d_con d ds) <-> ([i1 dots i2] runbound_d d /\
                                                                [i1 dots i2] runbound_ds ds).
Proof.
  split; intros.
  
  split; intros n' Hge Hlt;
    apply H in Hge;
    apply Hge in Hlt;
    inversion Hlt; eauto.

  intros n' Hge Hlt.
  crush.
Qed.

Hint Rewrite range_unbound_decls_cons.
Hint Resolve range_unbound_decls_cons.

Lemma ljump_cons :
  forall t G i n, ((t::G) [i] ljump_env n) = ((t [i] ljump_t n)::(G [i] ljump_env n)).
Proof.
  intros.
  crush.
Qed.

Lemma range_unbound_subst_type :
  forall i1 i2 p n t, [i1 dots i2] runbound_t ([p /t n] t) ->
                      [i1 dots i2] runbound_t t.
Proof.
  intros.
  intros n' Hge Hlt.
  eapply unbound_subst_type;
    eauto.
Qed.

Lemma range_unbound_subst_decl_tys :
  forall i1 i2 p n ss, [i1 dots i2] runbound_ss ([p /ss n] ss) ->
                       [i1 dots i2] runbound_ss ss.
Proof.
  intros.
  intros n' Hge Hlt.
  eapply unbound_subst_decl_tys;
    eauto.
Qed.

Lemma range_unbound_subst_components_type :
  forall i1 i2 p n t, [i1 dots i2] runbound_e p ->
                      [i1 dots i2] runbound_t t ->
                      [i1 dots i2] runbound_t ([p /t n] t).
Proof.
  intros.
  intros n' Hge Hlt.
  apply unbound_subst_components_type;
    crush.
Qed.

Lemma range_unbound_subst_components_decl_tys :
  forall i1 i2 p n ss, [i1 dots i2] runbound_e p ->
                       [i1 dots i2] runbound_ss ss ->
                       [i1 dots i2] runbound_ss ([p /ss n] ss).
Proof.
  intros.
  intros n' Hge Hlt.
  apply unbound_subst_components_decl_tys;
    crush.
Qed.

Lemma range_unbound_subst_components_exp :
  forall i1 i2 p n e, [i1 dots i2] runbound_e p ->
                      [i1 dots i2] runbound_e e ->
                      [i1 dots i2] runbound_e ([p /e n] e).
Proof.
  intros.
  intros n' Hge Hlt.
  apply unbound_subst_components_exp;
    crush.
Qed.

Lemma range_unbound_subst_components_decls :
  forall i1 i2 p n ds, [i1 dots i2] runbound_e p ->
                  [i1 dots i2] runbound_ds ds ->
                  [i1 dots i2] runbound_ds ([p /ds n] ds).
Proof.
  intros.
  intros n' Hge Hlt.
  apply unbound_subst_components_decls;
    crush.
Qed.

Lemma range_unbound_cons :
  forall i1 i2 t G, [i1 dots i2] runbound_t t ->
               [i1 dots i2] runbound_env G ->
               [i1 dots i2] runbound_env (t::G).
Proof.
  intros.
  intros t' Hin n' Hge Hlt.
  inversion Hin;
    subst;
    auto.
  apply H0; auto.
Qed.


Lemma closed_ljump_mutind :
  (forall t n i m, closed_t n t <-> closed_t n (t [i] ljump_t m)) /\
  
  (forall s n i m, closed_s n s <-> closed_s n (s [i] ljump_s m)) /\
  
  (forall ss n i m, closed_ss n ss <-> closed_ss n (ss [i] ljump_ss m)) /\
  
  (forall e n i m, closed_e n e <-> closed_e n (e [i] ljump_e m)) /\
  
  (forall d n i m, closed_d n d <-> closed_d n (d [i] ljump_d m)) /\
  
  (forall ds n i m, closed_ds n ds <-> closed_ds n (ds [i] ljump_ds m)).
Proof.
  apply type_exp_mutind;
    intros;
    try solve [split;
               simpl;
               auto];
    try solve [split; intros Hcl;
               [try (apply cl_str);
                try (apply cl_sel);
                try (apply cl_arr);
                try (apply cls_upper);
                try (apply cls_lower);
                try (apply cls_equal);
                try (apply cls_value);
                try (apply cls_cons);
                try (apply cl_acc);
                try (apply cl_app);
                try (apply cl_fn);
                try (apply cl_cast);
                try (apply cl_new);
                try (apply cld_equal);
                try (apply cld_value);
                try (apply cld_con);
                try apply H;
                try apply H0;
                try apply H1;
                inversion Hcl;
                auto
                  
               |try (apply cl_str);
                try (apply cl_sel);
                try (apply cl_arr);
                try (apply cls_upper);
                try (apply cls_lower);
                try (apply cls_equal);
                try (apply cls_value);
                try (apply cls_cons);
                try (apply cl_acc);
                try (apply cl_app);
                try (apply cl_fn);
                try (apply cl_cast);
                try (apply cl_new);
                try (apply cld_equal);
                try (apply cld_value);
                try (apply cld_con);
                inversion Hcl;
                try apply <- H; eauto;
                try apply <- H0; eauto;
                try apply <- H1; eauto;
                auto]].

  (*var*)
  split;
    destruct v as [x|x];
    simpl;
    auto.
Qed.

Lemma closed_ljump_type :
  (forall t n i m, closed_t n t <-> closed_t n (t [i] ljump_t m)).
Proof.
  destruct closed_ljump_mutind; crush.
Qed.

Lemma closed_ljump_decl_ty :
  (forall s n i m, closed_s n s <-> closed_s n (s [i] ljump_s m)).
Proof.
  destruct closed_ljump_mutind; crush.
Qed.

Lemma closed_ljump_decl_tys :
  (forall ss n i m, closed_ss n ss <-> closed_ss n (ss [i] ljump_ss m)).
Proof.
  destruct closed_ljump_mutind; crush.
Qed.

Lemma closed_ljump_exp :
  (forall e n i m, closed_e n e <-> closed_e n (e [i] ljump_e m)).
Proof.
  destruct closed_ljump_mutind; crush.
Qed.

Lemma closed_ljump_decl :
  (forall d n i m, closed_d n d <-> closed_d n (d [i] ljump_d m)).
Proof.
  destruct closed_ljump_mutind; crush.
Qed.

Lemma closed_ljump_decls :
  (forall ds n i m, closed_ds n ds <-> closed_ds n (ds [i] ljump_ds m)).
Proof.
  destruct closed_ljump_mutind; crush.
Qed.

Lemma minus_ge_eq :
  forall n m p, n - p = m - p ->
                n >= p ->
                m >= p ->
                n = m.
Proof.
  intro n;
    induction n as [|n'];
    intros;
    [crush|].

  destruct m as [|m'].
  
  destruct p;
    [crush|crush].
  
  destruct p as [|p'];
    [simpl in H; auto|].
  simpl in H.
  apply IHn' in H; crush.
Qed.

Lemma minus_ge_lt :
  forall n m p, n < m ->
                n >= p ->
                m >= p ->
                n - p < m - p.
Proof.
  intro n;
    induction n as [|n'];
    intros;
    [crush|].

  destruct m as [|m'].

  inversion H.
  
  destruct p as [|p'];
    [simpl in H; auto|].
  assert (Hlt1 : n' < m');
    [crush|].
  apply IHn' with (p:=p') in Hlt1;
    crush.
Qed.

Lemma ljump_range_unbound_mutind :
  (forall t i1 i2, [i1 dots i2] runbound_t t ->
                   i1 <= i2 ->
                   forall n, n >= i2 ->
                             n unbound_t t ->
                             (n [i2] ljump_n (i2 - i1)) unbound_t (t [i2] ljump_t (i2 - i1))) /\
  
  (forall s i1 i2, [i1 dots i2] runbound_s s ->
                   i1 <= i2 ->
                   forall n, n >= i2 ->
                             n unbound_s s ->
                             (n [i2] ljump_n (i2 - i1)) unbound_s (s [i2] ljump_s (i2 - i1))) /\
  
  (forall ss i1 i2, [i1 dots i2] runbound_ss ss ->
                    i1 <= i2 ->
                    forall n, n >= i2 ->
                              n unbound_ss ss ->
                              (n [i2] ljump_n (i2 - i1)) unbound_ss (ss [i2] ljump_ss (i2 - i1))) /\
  
  (forall e i1 i2, [i1 dots i2] runbound_e e ->
                   i1 <= i2 ->
                   forall n, n >= i2 ->
                             n unbound_e e ->
                             (n [i2] ljump_n (i2 - i1)) unbound_e (e [i2] ljump_e (i2 - i1))) /\
  
  (forall d i1 i2, [i1 dots i2] runbound_d d ->
                   i1 <= i2 ->
                   forall n, n >= i2 ->
                             n unbound_d d ->
                             (n [i2] ljump_n (i2 - i1)) unbound_d (d [i2] ljump_d (i2 - i1))) /\
  
  (forall ds i1 i2, [i1 dots i2] runbound_ds ds ->
                    i1 <= i2 ->
                    forall n, n >= i2 ->
                              n unbound_ds ds ->
                              (n [i2] ljump_n (i2 - i1)) unbound_ds (ds [i2] ljump_ds (i2 - i1))).
Proof.
  apply type_exp_mutind; intros; auto;
    try solve [try (apply ub_str);
               try (apply ub_sel);
               try (apply ub_new);
               try (apply ub_acc);
               try (apply ubs_upper);
               try (apply ubs_lower);
               try (apply ubs_equal);
               try (apply ubs_value);
               try (apply ubd_equal);
               try (apply H);
               auto;
               
               [try solve [eapply range_unbound_ty_str; eauto];
                try solve [eapply range_unbound_ty_sel; eauto];
                try solve [eapply range_unbound_exp_new; eauto];
                try solve [eapply range_unbound_exp_acc; eauto];
                try solve [eapply range_unbound_decl_ty_upper; eauto];
                try solve [eapply range_unbound_decl_ty_lower; eauto];
                try solve [eapply range_unbound_decl_ty_equal; eauto];
                try solve [eapply range_unbound_decl_ty_value; eauto];
                try solve [eapply range_unbound_decl_equal; eauto]
               |try (inversion H3);
                auto]];
    
    try solve [try apply ub_arr;
               try apply ub_app;
               try apply ub_cast;
               try apply ubd_con;
               try apply ubd_value;
               try apply ubs_con;
               [apply H
               |apply H0];
               auto;
               try solve [eapply range_unbound_ty_arr with (t2:=t0); eauto];
               try solve [eapply range_unbound_exp_app with (e2:=e0); eauto];
               try solve [eapply range_unbound_exp_cast; eauto];
               try solve [eapply range_unbound_decls_cons; eauto];
               try solve [eapply range_unbound_decl_tys_cons; eauto];
               try solve [eapply range_unbound_decl_value; eauto];
               try solve [inversion H4; auto]];
    try solve [simpl; auto].

  (*fn*)
  apply ub_fn;
    [apply H
    |apply H0
    |apply H1];
    auto;
    try solve [eapply range_unbound_exp_fn with (t2:=t0); eauto];
    inversion H5; auto.

  (*var*)
  destruct v as [x|x];
    simpl; auto.
  apply ub_var, ub_con;
    intro Hcontra.
  unfold left_jump_n in Hcontra.
  destruct (le_dec i2 n) as [Hle1|Hle1];
    assert (Hleb1 := Hle1);
    [apply Nat.leb_le in Hleb1
    |crush];
    rewrite Hleb1 in Hcontra;
    destruct (le_dec i2 x) as [Hle2|Hle2];
    assert (Hleb2 := Hle2);
    [apply Nat.leb_le in Hleb2
    |apply Nat.leb_nle in Hleb2];
    rewrite Hleb2 in Hcontra.
  apply minus_ge_eq in Hcontra;
    [subst x;
     inversion H2;
     subst
    |crush
    |crush].
  inversion H5; crush.

  assert (Hlt : x < i2);
    [crush|].
  assert (Hge : x >= i1);
    [crush|].
  apply H in Hge;
    apply Hge in Hlt.
  inversion Hlt;
    subst.
  inversion H5;
    auto.
Qed.

Lemma ljump_range_unbound_type :
  (forall t i1 i2, [i1 dots i2] runbound_t t ->
              i1 <= i2 ->
              forall n, n >= i2 ->
                   n unbound_t t ->
                   (n [i2] ljump_n (i2 - i1)) unbound_t (t [i2] ljump_t (i2 - i1))).
Proof.
  destruct ljump_range_unbound_mutind; crush.
Qed.

Lemma ljump_range_unbound_decl_ty :    
  (forall s i1 i2, [i1 dots i2] runbound_s s ->
              i1 <= i2 ->
              forall n, n >= i2 ->
                   n unbound_s s ->
                   (n [i2] ljump_n (i2 - i1)) unbound_s (s [i2] ljump_s (i2 - i1))).
Proof.
  destruct ljump_range_unbound_mutind; crush.
Qed.

Lemma ljump_range_unbound_decl_tys :    
  (forall ss i1 i2, [i1 dots i2] runbound_ss ss ->
               i1 <= i2 ->
               forall n, n >= i2 ->
                    n unbound_ss ss ->
                    (n [i2] ljump_n (i2 - i1)) unbound_ss (ss [i2] ljump_ss (i2 - i1))).
Proof.
  destruct ljump_range_unbound_mutind; crush.
Qed.

Lemma ljump_range_unbound_exp :
  (forall e i1 i2, [i1 dots i2] runbound_e e ->
              i1 <= i2 ->
              forall n, n >= i2 ->
                   n unbound_e e ->
                   (n [i2] ljump_n (i2 - i1)) unbound_e (e [i2] ljump_e (i2 - i1))).
Proof.
  destruct ljump_range_unbound_mutind; crush.
Qed.

Lemma ljump_range_unbound_decl :
  (forall d i1 i2, [i1 dots i2] runbound_d d ->
              i1 <= i2 ->
              forall n, n >= i2 ->
                   n unbound_d d ->
                   (n [i2] ljump_n (i2 - i1)) unbound_d (d [i2] ljump_d (i2 - i1))).
Proof.
  destruct ljump_range_unbound_mutind; crush.
Qed.

Lemma ljump_range_unbound_decls :
  (forall ds i1 i2, [i1 dots i2] runbound_ds ds ->
               i1 <= i2 ->
               forall n, n >= i2 ->
                    n unbound_ds ds ->
                    (n [i2] ljump_n (i2 - i1)) unbound_ds (ds [i2] ljump_ds (i2 - i1))).
Proof.
  destruct ljump_range_unbound_mutind; crush.
Qed.

Lemma lt_ljump_mutind :
  (forall t i, lt_t t i ->
               forall n, (t [i] ljump_t n) = t) /\
  (forall s i, lt_s s i ->
               forall n, (s [i] ljump_s n) = s) /\
  (forall ss i, lt_ss ss i ->
                forall n, (ss [i] ljump_ss n) = ss) /\
  (forall e i, lt_e e i ->
               forall n, (e [i] ljump_e n) = e) /\
  (forall d i, lt_d d i ->
               forall n, (d [i] ljump_d n) = d) /\
  (forall ds i, lt_ds ds i ->
                forall n, (ds [i] ljump_ds n) = ds).
Proof.
  apply lt_mutind; intros; crush.

  unfold left_jump_n;
    rewrite leb_correct_conv; auto.
Qed.

Lemma lt_ljump_type :
  (forall t i, lt_t t i ->
               forall n, (t [i] ljump_t n) = t).
Proof.
  destruct lt_ljump_mutind; crush.
Qed.

Lemma lt_ljump_decl_ty :
  (forall s i, lt_s s i ->
               forall n, (s [i] ljump_s n) = s).
Proof.
  destruct lt_ljump_mutind; crush.
Qed.

Lemma lt_ljump_decl_tys :
  (forall ss i, lt_ss ss i ->
                forall n, (ss [i] ljump_ss n) = ss).
Proof.
  destruct lt_ljump_mutind; crush.
Qed.

Lemma lt_ljump_exp :
  (forall e i, lt_e e i ->
               forall n, (e [i] ljump_e n) = e).
Proof.
  destruct lt_ljump_mutind; crush.
Qed.

Lemma lt_ljump_decl :
  (forall d i, lt_d d i ->
               forall n, (d [i] ljump_d n) = d).
Proof.
  destruct lt_ljump_mutind; crush.
Qed.

Lemma lt_ljump_decls :
  (forall ds i, lt_ds ds i ->
                forall n, (ds [i] ljump_ds n) = ds).
Proof.
  destruct lt_ljump_mutind; crush.
Qed.

Lemma ljump_wf_type :
  (forall Sig G t, Sig en G vdash t wf_t ->
            forall i n, i >= length G ->
                   (t [i] ljump_t n) = t).
Proof.
  intros.
  rewrite lt_ljump_type;
    auto.
  eapply lt_n_ge_type;
    eauto.
  eapply wf_lt_type;
    eauto.
Qed.

Lemma ljump_wf_decl_ty :
  (forall Sig G s, Sig en G vdash s wf_s ->
            forall i n, i >= length G ->
                   (s [i] ljump_s n) = s).
Proof.
  intros.
  rewrite lt_ljump_decl_ty;
    auto.
  eapply lt_n_ge_decl_ty;
    eauto.
  eapply wf_lt_decl_ty;
    eauto.
Qed.

Lemma ljump_wf_decl_tys :
  (forall Sig G ss, Sig en G vdash ss wf_ss ->
            forall i n, i >= length G ->
                   (ss [i] ljump_ss n) = ss).
Proof.
  intros.
  rewrite lt_ljump_decl_tys;
    auto.
  eapply lt_n_ge_decl_tys;
    eauto.
  eapply wf_lt_decl_tys;
    eauto.
Qed.

Lemma ljump_wf_exp :
  (forall Sig G e, Sig en G vdash e wf_e ->
            forall i n, i >= length G ->
                   (e [i] ljump_e n) = e).
Proof.
  intros.
  rewrite lt_ljump_exp;
    auto.
  eapply lt_n_ge_exp;
    eauto.
  eapply wf_lt_exp;
    eauto.
Qed.

Lemma ljump_wf_decl :
  (forall Sig G d, Sig en G vdash d wf_d ->
            forall i n, i >= length G ->
                   (d [i] ljump_d n) = d).
Proof.
  intros.
  rewrite lt_ljump_decl;
    auto.
  eapply lt_n_ge_decl;
    eauto.
  eapply wf_lt_decl;
    eauto.
Qed.

Lemma ljump_wf_decls :
  (forall Sig G ds, Sig en G vdash ds wf_ds ->
            forall i n, i >= length G ->
                   (ds [i] ljump_ds n) = ds).
Proof.
  intros.
  rewrite lt_ljump_decls;
    auto.
  eapply lt_n_ge_decls;
    eauto.
  eapply wf_lt_decls;
    eauto.
Qed.

Lemma ljump_wf_st :
  forall Sig, Sig wf_st ->
       forall i n, (Sig [i] ljump_env n) = Sig.
Proof.
  intro Sig; induction Sig as [|t Sig'];
    intros;
    auto.

  simpl;
    inversion H;
    subst.
  apply ljump_wf_type with (i:=i)(n:=n) in H2;
    [rewrite H2|crush].
  rewrite IHSig';
    auto.
Qed.

Lemma ljump_wf_env :
  forall Sig G, Sig evdash G wf_env ->
         forall i n, i >= length G ->
                (G [i] ljump_env n) = G.
Proof.
  intros Sig G Hwf;
    induction Hwf;
    intros;
    auto.

  simpl.
  erewrite ljump_wf_type;
    eauto;
    [|crush].
  rewrite IHHwf;
    crush.
Qed.
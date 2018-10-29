Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Set Implicit Arguments.


Inductive var : Type :=
| Var : nat -> var  (*concrete variables*)
| Abs : nat -> var. (*abstract variables*)


Inductive ty_label :=
| Material : nat -> ty_label
| Shape : nat -> ty_label.

Inductive label : Type :=
| l_def : nat -> label
| l_type : ty_label -> label.

Inductive ty : Type := (*types*)
| str : decl_tys -> ty
| sel : exp -> label -> ty
| fn_t  : ty -> ty -> ty
| top   : ty
| bot  : ty
         
with
decl_ty : Type := (*declaration types*)
| dt_upp : label -> ty -> decl_ty
| dt_low : label -> ty -> decl_ty
| dt_equ : label -> ty -> decl_ty
| dt_val : label -> ty -> decl_ty

with
decl_tys : Type :=
| dt_nil : decl_tys
| dt_con : decl_ty -> decl_tys -> decl_tys

with
exp : Type := (*expressions*)
| new : decls -> exp
| e_app : exp -> exp -> exp
| e_fn : ty -> exp -> ty -> exp
| e_acc : exp -> label -> exp
| e_var : var -> exp
| e_loc : nat -> exp
| e_cast : exp -> ty -> exp

with
decl : Type := (*declarations*)
| d_typ : label -> ty -> decl
| d_val : label -> exp -> ty -> decl

with
decls : Type :=
| d_nil : decls
| d_con : decl -> decls -> decls.


(*Notation "p 'cast' t" := (p_cast p t) (at level 80).
Notation "'v_' x" := (p_var x) (at level 80).*)

Notation "'c_' x" := (e_var (Var x)) (at level 80).
Notation "'a_' x" := (e_var (Abs x)) (at level 80).
Notation "'v_' x" := (e_var x) (at level 80).
Notation "'i_' x" := (e_loc x) (at level 80).
Notation "e 'cast' t" := (e_cast e t) (at level 80).

Notation "'type' l 'sup' t" := (dt_low l t) (at level 80).
Notation "'type' l 'ext' t" := (dt_upp l t) (at level 80).
Notation "'type' l 'eqt' t" := (dt_equ l t) (at level 80).
Notation "'type' l 'eqe' t" := (d_typ l t) (at level 80).
Notation "'val' l 'oft' t" := (dt_val l t) (at level 80).
Notation "'val' l 'assgn' e 'oft' t" := (d_val l e t) (at level 80).
Notation "'fn' t1 'in_exp' e 'off' t2" := (e_fn t1 e t2) (at level 80).
Notation "t1 'arr' t2" := (fn_t t1 t2) (at level 80).

Inductive is_path : exp -> Prop :=
| isp_loc : forall i, is_path (i_ i)
| isp_var : forall x, is_path (v_ x)
| isp_cast : forall p t, is_path p ->
                    is_path (p cast t).

Hint Constructors is_path.

Scheme type_mut_ind := Induction for ty Sort Prop
  with decl_ty_mut_ind := Induction for decl_ty Sort Prop
  with decl_tys_mut_ind := Induction for decl_tys Sort Prop
  with exp_mut_ind := Induction for exp Sort Prop
  with decl_mut_ind := Induction for decl Sort Prop
  with decls_mut_ind := Induction for decls Sort Prop.

Combined Scheme type_exp_mutind from type_mut_ind, decl_ty_mut_ind, decl_tys_mut_ind, exp_mut_ind, decl_mut_ind, decls_mut_ind.

Definition id_t (s : decl_ty) : label :=
  match s with
  | type l sup _ => l
  | type l ext _ => l
  | type l eqt _ => l
  | val l oft _ => l
  end.

Definition id_d (d : decl) : label :=
  match d with
  | type L eqe _ => L
  | val l assgn _ oft _ => l
  end.


Definition env := list ty.
Definition mu := list exp.

Reserved Notation "'[' p '/t' n ']' t" (at level 80).
Reserved Notation "'[' p '/d' n ']' d" (at level 80).
Reserved Notation "'[' p1 '/p' n ']' p2" (at level 80).

(*Left Shift*)

Fixpoint left_shift_var (n : nat) (v : var) : var :=
  match v with
  | Var m => Var (n + m)
  | _ => v
  end.

Notation "v 'lshift_v' n" := (left_shift_var n v) (at level 80).
Reserved Notation "t 'lshift_t' n" (at level 80).
Reserved Notation "d 'lshift_dt' n" (at level 80).
Reserved Notation "d 'lshift_dts' n" (at level 80).
Reserved Notation "e 'lshift_e' n" (at level 80).
Reserved Notation "d 'lshift_d' n" (at level 80).
Reserved Notation "d 'lshift_ds' n" (at level 80).
Reserved Notation "G 'lshift_e' n" (at level 80).

Fixpoint left_shift_type (n : nat) (t : ty) : ty :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => (t1 lshift_t n) arr (t2 lshift_t n)
  | sel p l => sel (p lshift_e n) l
  | str ds => str (ds lshift_dts n)
  end
where "t 'lshift_t' n" := (left_shift_type n t)

with
left_shift_decl_ty (n : nat) (d : decl_ty) : decl_ty :=
  match d with
  | type l sup t => type l sup (t lshift_t n)
  | type l ext t => type l ext (t lshift_t n)
  | type l eqt t => type l eqt (t lshift_t n)
  | val l oft t => val l oft (t lshift_t n)
  end
where "d 'lshift_dt' n" := (left_shift_decl_ty n d)

with
left_shift_decl_tys (n : nat) (ds : decl_tys) : decl_tys :=
  match ds with
  | dt_nil => dt_nil
  | dt_con d ds' => dt_con (d lshift_dt n) (ds' lshift_dts n)
  end
where "d 'lshift_dts' n" := (left_shift_decl_tys n d)

with
left_shift_exp (n : nat) (e : exp) : exp :=
  match e with
  | new ds => new (ds lshift_ds S n)
  | e_app e1 e2 => e_app (e1 lshift_e n) (e2 lshift_e n)
  | fn t1 in_exp e off t2 => fn (t1 lshift_t n) in_exp (e lshift_e S n) off (t2 lshift_t S n)
  | e_acc e m => e_acc (e lshift_e n) m
  | e cast t => (e lshift_e n) cast (t lshift_t n)
  | v_ x => v_ (x lshift_v n)
  | i_ i => i_ i
  end
where "e 'lshift_e' n" := (left_shift_exp n e)

with
left_shift_decl (n : nat) (d : decl) : decl :=
  match d with
  | type l eqe t => type l eqe (t lshift_t n)
  | val l assgn e oft t => val l assgn (e lshift_e n) oft (t lshift_t n)
  end
where "d 'lshift_d' n" := (left_shift_decl n d)

with
left_shift_decls (n : nat) (ds : decls) : decls :=
  match ds with
  | d_nil => d_nil
  | d_con d ds' => d_con (d lshift_d n) (ds' lshift_ds n)
  end
where "d 'lshift_ds' n" := (left_shift_decls n d).



(*Right Shift*)

Fixpoint right_shift_var (n : nat) (v : var) : var :=
  match v with
  | Var m => Var (m - n)
  | _ => v
  end.

Notation "v 'rshift_v' n" := (right_shift_var n v) (at level 80).
Reserved Notation "n 'rshift_n' m" (at level 80).
Reserved Notation "t 'rshift_t' n" (at level 80).
Reserved Notation "d 'rshift_d' n" (at level 80).
Reserved Notation "d 'rshift_ds' n" (at level 80).
Reserved Notation "d 'rshift_dt' n" (at level 80).
Reserved Notation "d 'rshift_dts' n" (at level 80).
Reserved Notation "p 'rshift_p' n" (at level 80).
Reserved Notation "G 'rshift_e' n" (at level 80).

Fixpoint right_shift_type (n : nat) (t : ty) : ty :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => (t1 rshift_t n) arr (t2 rshift_t n)
  | sel p l => sel (p rshift_e n) l
  | str ds => str (ds rshift_dts n)
  end
where "t 'rshift_t' n" := (right_shift_type n t)

with
right_shift_decl_ty (n : nat) (d : decl_ty) : decl_ty :=
  match d with
  | type l sup t => type l sup (t rshift_t n)
  | type l ext t => type l ext (t rshift_t n)
  | type l eqt t => type l eqt (t rshift_t n)
  | val l oft t => val l oft (t rshift_t n)
  end
where "d 'rshift_dt' n" := (right_shift_decl_ty n d)

with
right_shift_decl_tys (n : nat) (ds : decl_tys) : decl_tys :=
  match ds with
  | dt_nil => dt_nil
  | dt_con d ds' => dt_con (d rshift_dt n) (ds' rshift_dts n)
  end
where "d 'rshift_dts' n" := (right_shift_decl_tys n d)
                              
with
right_shift_exp (n : nat) (e : exp) : exp :=
  match e with
  | new ds => new (ds rshift_ds S n)
  | e_app e1 e2 => e_app (e1 rshift_e n) (e2 rshift_e n)
  | fn t1 in_exp e off t2 => fn (t1 rshift_t n) in_exp (e rshift_e S n) off (t2 rshift_t S n)
  | e_acc e m => e_acc (e rshift_e n) m
  | e cast t => (e rshift_e n) cast (t rshift_t n)
  | v_ x => v_ (x rshift_v n)
  | i_ i => i_ i
  end
where "e 'rshift_e' n" := (right_shift_exp n e)

with
right_shift_decl (n : nat) (d : decl) : decl :=
  match d with
  | type l eqe t => type l eqe (t rshift_t n)
  | val l assgn e oft t => val l assgn (e rshift_e n) oft (t rshift_t n)
  end
where "d 'rshift_d' n" := (right_shift_decl n d)

with
right_shift_decls (n : nat) (ds : decls) : decls :=
  match ds with
  | d_nil => d_nil
  | d_con d ds' => d_con (d rshift_d n) (ds' rshift_ds n)
  end
where "d 'rshift_ds' n" := (right_shift_decls n d).


(*with
  right_shift_path (n : nat) (p : path) : path :=
    match p with
    | v_ x => v_ (x rshift_v n)
    | p cast t => (p rshift_p n) cast (t rshift_t n)
    end
      where "p 'rshift_p' n" := (right_shift_path n p)*)

(*Environment shift*)

(*move all variables less than n, 1 space to the left, this means reducing the relative distance of all 
   references greater than or equal to n by 1*)

Definition inc (i : option nat) (n : nat) : option nat :=
  match i with
  | None => None
  | Some i' => Some (i' + n) 
  end.

Definition dec (i : option nat) (n : nat): option nat :=
  match i with
  | None => None
  | Some i' => if i' <? n
              then None
              else Some (i' - n)
  end.

Definition raise_nat (r i : nat) : nat :=
  if r <? i
  then r
  else r + 1.

Notation "r 'raise_n' i" := (raise_nat r i)(at level 80).

Definition raise_var (v : var)(i : nat) : var :=
  match v with
  | Var _ => v
  | Abs r => Abs (r raise_n i)
  end.

Notation "v 'raise_v' i" := (raise_var v i)(at level 80).

Reserved Notation "t 'raise_t' i" (at level 80).
Reserved Notation "s 'raise_s' i" (at level 80).
Reserved Notation "ss 'raise_ss' i" (at level 80).
Reserved Notation "e 'raise_e' i" (at level 80).
Reserved Notation "d 'raise_d' i" (at level 80).
Reserved Notation "ds 'raise_ds' i" (at level 80).

Fixpoint raise_ty (t : ty)(i : nat) : ty :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => (t1 raise_t i) arr (t2 raise_t (S i))
  | sel p L => sel (p raise_e i) L
  | str ss => str (ss raise_ss (S i))
  end
where "t 'raise_t' i" := (raise_ty t i)

with
raise_decl_ty (s : decl_ty)(i : nat) : decl_ty :=
  match s with
  | type L ext t => type L ext (t raise_t i)
  | type L sup t => type L sup (t raise_t i)
  | type L eqt t => type L eqt (t raise_t i)
  | val l oft t => val l oft (t raise_t i)
  end
where "s 'raise_s' i" := (raise_decl_ty s i)

with
raise_decl_tys (ss : decl_tys)(i : nat) : decl_tys :=
  match ss with
  | dt_nil => dt_nil
  | dt_con s ss' => dt_con (s raise_s i) (ss' raise_ss i)
  end
where "ss 'raise_ss' i" := (raise_decl_tys ss i)

with
raise_exp (e : exp)(i : nat) : exp :=
  match e with
  | v_ v => v_ (v raise_v i)
  | i_ _ => e
  | fn t1 in_exp e' off t2 => fn (t1 raise_t i) in_exp (e' raise_e (S i)) off (t2 raise_t (S i))
  | e_app e1 e2 => e_app (e1 raise_e i) (e2 raise_e i)
  | e_acc e' l => e_acc (e' raise_e i) l
  | new ds => new (ds raise_ds (S i))
  | e' cast t => (e' raise_e i) cast (t raise_t i)
  end
where "e 'raise_e' i" := (raise_exp e i)

with
raise_decl (d : decl)(i : nat) : decl :=
  match d with
  | type L eqe t => type L eqe (t raise_t i)
  | val l assgn e oft t => val l assgn (e raise_e i) oft (t raise_t i)
  end
where "d 'raise_d' i" := (raise_decl d i)

with
raise_decls (ds : decls)(i : nat) : decls :=
  match ds with
  | d_nil => d_nil
  | d_con d ds' => d_con (d raise_d i) (ds' raise_ds i)
  end
where "ds 'raise_ds' i" := (raise_decls ds i).

Fixpoint raise_n_t (n : nat)(t : ty)(i : nat) : ty :=
  match n with
  | 0 => t
  | S n' => raise_n_t n' (t raise_t i) (S i)
  end.

Fixpoint raise_n_s (n : nat)(s : decl_ty)(i : nat) : decl_ty :=
  match n with
  | 0 => s
  | S n' => raise_n_s n' (s raise_s i) (S i)
  end.

Fixpoint raise_n_ss (n : nat)(ss : decl_tys)(i : nat) : decl_tys :=
  match n with
  | 0 => ss
  | S n' => raise_n_ss n' (ss raise_ss i) (S i)
  end.

Fixpoint raise_n_e (n : nat)(e : exp)(i : nat) : exp :=
  match n with
  | 0 => e
  | S n' => raise_n_e n' (e raise_e i) (S i)
  end.

Fixpoint raise_n_d (n : nat)(d : decl)(i : nat) : decl :=
  match n with
  | 0 => d
  | S n' => raise_n_d n' (d raise_d i) (S i)
  end.

Fixpoint raise_n_ds (n : nat)(ds : decls)(i : nat) : decls :=
  match n with
  | 0 => ds
  | S n' => raise_n_ds n' (ds raise_ds i) (S i)
  end.


Reserved Notation "v '[' i ']' 'rjump_v' n" (at level 80).
Reserved Notation "t '[' i ']' 'rjump_t' n" (at level 80).
Reserved Notation "d '[' i ']' 'rjump_s' n" (at level 80).
Reserved Notation "d '[' i ']' 'rjump_ss' n" (at level 80).
Reserved Notation "d '[' i ']' 'rjump_d' n" (at level 80).
Reserved Notation "d '[' i ']' 'rjump_ds' n" (at level 80).
Reserved Notation "p '[' i ']' 'rjump_e' n" (at level 80).

(*left and right jumps for inserting new variables into the middle of contexts*)
(*
for a context G1++G2 that is a context G1 appended with G2, we would like to insert another 
context G between them (G1++G++G2) while maitaining the correct variable naming. Since refereces use de Bruijn indeces
Therefore every reference in G1 that refers to something in G2 must be increased by the length of G. References 
in G1 that refer to positions in G1 do not change, and similarly, all references in G2 must remain the same.

@params i is the relative distance to the first element of G2. If i = 0, then the current element is in G2
        n is the length of G, the distance to be shifted
        m is reference. If m = 0, then the next element in the context is the refered type.
 *)


Definition right_jump_n (r i n : nat) : nat :=
  if i <=? r
  then r + n
  else r.

Notation "r '[' i ']' 'rjump_n' n" := (right_jump_n r i n) (at level  80).

Fixpoint right_jump_v (x : var)(i n : nat) : var :=
  match x with
  | Var r => Var (r[i] rjump_n n)
  | _ => x
  end.

Notation "x '[' i ']' 'rjump_v' n" := (right_jump_v x i n) (at level  80).

Fixpoint right_jump_t (t : ty) (i n : nat) : ty  :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => (t1 [i] rjump_t n) arr (t2 [i] rjump_t n)
  | sel p l => sel (p [i] rjump_e n) l
  | str ss => str (ss [i] rjump_ss n)
  end
where "t '[' i ']' 'rjump_t' n" := (right_jump_t t i n)

with
right_jump_d_ty (s : decl_ty) (i n : nat) : decl_ty :=
  match s with
  | type l sup t => type l sup (t[i] rjump_t n)
  | type l ext t => type l ext (t[i] rjump_t n)
  | type l eqt t => type l eqt (t[i] rjump_t n)
  | val l oft t => val l oft (t[i] rjump_t n)
  end
where "d '[' i ']' 'rjump_s' n" := (right_jump_d_ty d i n)

with
right_jump_d_tys (ss : decl_tys) (i n : nat) : decl_tys :=
  match ss with 
  | dt_nil => dt_nil
  | dt_con s ss' => dt_con (s [i] rjump_s n) (ss' [i] rjump_ss n)
  end
where "d '[' i ']' 'rjump_ss' n" := (right_jump_d_tys d i n)

with
right_jump_e (e : exp) (i n : nat) : exp :=
  match e with
  | new ds => new (ds [i] rjump_ds n)
  | e_app e1 e2 => e_app (e1 [i] rjump_e n) (e2 [i] rjump_e n)
  | fn t1 in_exp e off t2 => fn (t1 [i] rjump_t n) in_exp (e [i] rjump_e n) off (t2 [i] rjump_t n)
  | e_acc e m => e_acc (e [i] rjump_e n) m
  | v_ x => v_ (x [i] rjump_v n)
  | i_ i => i_ i
  | e cast t => (e [i] rjump_e n) cast (t [i] rjump_t n)
  end
where "e '[' i ']' 'rjump_e' n" := (right_jump_e e i n)        
                                     
with
right_jump_d (d : decl) (i n : nat) : decl :=
  match d with
  | type l eqe t => type l eqe (t[i] rjump_t n)
  | val l assgn e oft t => val l assgn (e[i] rjump_e n) oft (t [i] rjump_t n)
  end
where "d '[' i ']' 'rjump_d' n" := (right_jump_d d i n)

with
right_jump_ds (ds : decls) (i n : nat) : decls :=
  match ds with
  | d_nil => d_nil
  | d_con d ds' => d_con (d [i] rjump_d n) (ds' [i] rjump_ds n)
  end
where "d '[' i ']' 'rjump_ds' n" := (right_jump_ds d i n).

Definition right_jump_env (G : env)(i n : nat) : env :=
  map (fun (t : ty) => t [i] rjump_t n) G.

Notation "G '[' i ']' 'rjump_env' n" :=(right_jump_env G i n)(at level 80).

Fixpoint rename (r n m : nat) : nat :=
  if r =? n
  then m
  else r.

Fixpoint rename_v (x : var)(n m : nat) : var :=
  match x with
  | Abs r => Abs (rename r n m)
  | _ => x
  end.

Notation "x '[' n 'maps_v' m ']'" := (rename_v x n m)(at level 80).

Reserved Notation "t '[' n 'maps_t' m ']'" (at level 80).
Reserved Notation "s '[' n 'maps_s' m ']'" (at level 80).
Reserved Notation "ss '[' n 'maps_ss' m ']'" (at level 80).
Reserved Notation "e '[' n 'maps_e' m ']'" (at level 80).
Reserved Notation "d '[' n 'maps_d' m ']'" (at level 80).
Reserved Notation "ds '[' n 'maps_ds' m ']'" (at level 80).

Fixpoint rename_t (t : ty)(n m : nat) : ty :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => (t1 [n maps_t m]) arr (t2 [S n maps_t S m])
  | sel p l => sel (p [n maps_e m]) l
  | str ss => str (ss [S n maps_ss S m])
  end
where "t '[' n 'maps_t' m ']'" := (rename_t t n m)

with
rename_s (s : decl_ty)(n m : nat) : decl_ty :=
  match s with
  | type l ext t => type l ext (t [n maps_t m])
  | type l sup t => type l sup (t [n maps_t m])
  | type l eqt t => type l eqt (t [n maps_t m])
  | val l oft t => val l oft (t [n maps_t m])
  end
where "s '[' n 'maps_s' m ']'" := (rename_s s n m)

with
rename_ss (ss : decl_tys)(n m : nat) : decl_tys :=
  match ss with
  | dt_nil => dt_nil
  | dt_con s ss' => dt_con (s [n maps_s m]) (ss' [n maps_ss m])
  end
where "ss '[' n 'maps_ss' m ']'" := (rename_ss ss n m)

with
rename_e (e : exp)(n m : nat) : exp :=
  match e with
  | v_ x => v_ (x [n maps_v m])
  | i_ i => i_ i
  | e' cast t => (e' [n maps_e m]) cast (t [n maps_t m])
  | fn t1 in_exp e0 off t2 => fn (t1 [n maps_t m]) in_exp (e0 [S n maps_e S m]) off (t2 [S n maps_t S m])
  | e_app e1 e2 => e_app (e1 [n maps_e m]) (e2 [n maps_e m])
  | e_acc e' l => e_acc (e' [n maps_e m]) l
  | new ds => new (ds [S n maps_ds S m])
  end
where "e '[' n 'maps_e' m ']'" := (rename_e e n m)

with
rename_d (d : decl)(n m : nat) : decl :=
  match d with
  | type l eqe t => type l eqe (t [n maps_t m])
  | val l assgn e oft t => val l assgn (e [n maps_e m]) oft (t [n maps_t m])
  end
where "d '[' n 'maps_d' m ']'" := (rename_d d n m)

with
rename_ds (ds : decls)(n m : nat) : decls :=
  match ds with
  | d_nil => d_nil
  | d_con d ds' => d_con (d [n maps_d m]) (ds' [n maps_ds m])
  end
where "ds '[' n 'maps_ds' m ']'" := (rename_ds ds n m).






Reserved Notation "'[' p '/t' n ']' ds" (at level 80).
Reserved Notation "'[' p '/s' n ']' ds" (at level 80).
Reserved Notation "'[' p '/ss' n ']' ds" (at level 80).
Reserved Notation "'[' p '/d' n ']' ds" (at level 80).
Reserved Notation "'[' p '/ds' n ']' ds" (at level 80).
Reserved Notation "'[' p '/e' n ']' ds" (at level 80).


Definition subst_v (n : nat) (x y : var) : var :=
  match y with
  | Abs m => if beq_nat n m
            then x
            else y
  | _ => y
  end.

Notation "'[' x '/v' n ']' y" := (subst_v n x y) (at level 80).

Fixpoint subst (n : nat) (e : exp) (t : ty) : ty :=
  match t with
  | top => top
  | bot => bot
  | t1 arr t2 => ([e /t n] t1) arr ([(e raise_e 0) /t S n] t2)
  | sel p l => sel ([ e /e n ] p) l
  | str ds => str ([ (e raise_e 0) /ss S n ] ds)
  end

where "'[' p '/t' n ']' t" := (subst n p t)

with
subst_d_ty (n : nat) (e : exp) (d : decl_ty) : decl_ty :=
  match d with
  | type l sup t => type l sup ([e /t n] t)
  | type l ext t => type l ext ([e /t n] t)
  | type l eqt t => type l eqt ([e /t n] t)
  | val l oft t => val l oft ([e /t n] t)                        
  end
    
where "'[' p '/s' n ']' d" := (subst_d_ty n p d)

with
subst_d_tys (n : nat) (e : exp) (d : decl_tys) : decl_tys :=
  match d with
  | dt_nil => dt_nil
  | dt_con d ds' => dt_con ([e /s n] d) ([e /ss n] ds')
  end
    
where "'[' p '/ss' n ']' d" := (subst_d_tys n p d)

with
subst_e (n : nat) (e1 e2 : exp) : exp :=
  match e2 with
  | new ds => new ([(e1 raise_e 0) /ds S n] ds)
  | e_app e e' => e_app ([e1 /e n] e) ([e1 /e n] e')
  | fn t1 in_exp e off t2 => fn ([e1 /t n] t1) in_exp ([(e1 raise_e 0) /e S n] e) off ([(e1 raise_e 0) /t S n] t2)
  | e_acc e m => e_acc ([e1 /e n] e) m
  | v_ x => match x with
           | Abs m => if beq_nat n m
                     then e1
                     else v_ x
           | _ => v_ x
           end
  | i_ i => i_ i
  | e cast t => ([e1 /e n] e) cast ([e1 /t n] t)
  end
    
where "'[' e1 '/e' n ']' e2" := (subst_e n e1 e2)

with
subst_d (n : nat) (e : exp) (d : decl) : decl :=
  match d with
  | type l eqe t => type l eqe ([e /t n] t)
  | val l assgn el oft t => val l assgn ([e /e n] el) oft ([e /t n] t)
  end
    
where "'[' p '/d' n ']' d" := (subst_d n p d)

with
subst_ds (n : nat) (e : exp) (d : decls) : decls :=
  match d with
  | d_nil => d_nil
  | d_con d ds' => d_con ([e /d n] d) ([e /ds n] ds')
  end
    
where "'[' p '/ds' n ']' d" := (subst_ds n p d).

(*  Definition subst_env (n : nat)(p : exp)(G : env) : env := map (fun (t : ty) => [p /t n] t) G.*)

Fixpoint subst_environment (n : nat)(p : exp)(G : env) : env :=
  match G with
  | nil => nil
  | t::G' => ([p /t n] t)::(subst_environment (S n) p G')
  end.

Definition subst_env (n : nat)(p : exp)(G : env) : env :=
  rev (subst_environment n p (rev G)).

Notation "'[' x '/env' n ']' G" := (subst_env n x G)(at level 80).

(*with
  subst_p (n : nat) (p1 p2 : path) : path :=
    match p2 with
    | v_ x => match x with
             | Abs m => if beq_nat n m
                       then p1
                       else p2
             | _ => p2
             end
    | p cast t => [p1 /p n] p cast [p1 /t n] t
    end
                              
      
  where "'[' p1 '/p' n ']' p2" := (subst_p n p1 p2)*)

Fixpoint get {A : Type} (n : nat) (l : list A) : option A :=
  match n with
  | O => match l with
        | nil => None
        | h::t => Some h
        end
  | S m => match l with
          | nil => None
          | h::t => get m t
          end
  end.

Definition mapping {A : Type}(n : nat)(l : list A) : option A :=
  get n (rev l).

Notation "n 'mapsto' t 'elem' G" := (mapping n G = Some t)(at level 80).

(*Definition get (n : nat) (l : list ty) : option ty :=
    nth n (rev l).*)

Reserved Notation "Sig 'en' G 'vdash' p 'pathType' t" (at level 80).

Inductive typing_p : env -> env -> exp -> ty -> Prop :=
| pt_var : forall Sig G n t, n mapsto t elem G ->
                      Sig en G vdash (c_ n) pathType t
| pt_loc : forall Sig G i t, i mapsto t elem Sig ->
                      Sig en G vdash (i_ i) pathType t
| pt_cast : forall Sig G p t, is_path p ->
                       Sig en G vdash (p cast t) pathType t

where "Sig 'en' G 'vdash' p 'pathType' t" := (typing_p Sig G p t).

Reserved Notation "Sig 'en' G 'vdash' p 'ni' d" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' d 'cont' t" (at level 80).

Hint Constructors typing_p.

Inductive in_dty : decl_ty -> decl_tys -> Prop :=
| in_head_dty : forall d ds, in_dty d (dt_con d ds)
| in_tail_dty : forall d d' ds, in_dty d ds ->
                           in_dty d (dt_con d' ds).

Inductive in_d : decl -> decls -> Prop :=
| in_head_d : forall d ds, in_d d (d_con d ds)
| in_tail_d : forall d d' ds, in_d d ds ->
                         in_d d (d_con d' ds).

Inductive has : env -> env -> exp -> decl_ty -> Prop :=
| has_path : forall Sig G p t d, Sig en G vdash p pathType t ->
                          Sig en G vdash d cont t ->
                          Sig en G vdash p ni ([p /s 0] d)

where "Sig 'en' G 'vdash' p 'ni' d" := (has Sig G p d)

with
contains : env -> env -> ty -> decl_ty -> Prop :=
| cont_struct : forall Sig G ds d, in_dty d ds ->
                            Sig en G vdash d cont str ds
| cont_upper : forall Sig G p L t d, Sig en G vdash p ni (type L ext t) ->
                              Sig en G vdash d cont t ->
                              Sig en G vdash ([a_ 0 cast t /s 0] d) cont (sel p L)
| cont_equal : forall Sig G p L t d, Sig en G vdash p ni (type L eqt t) ->
                              Sig en G vdash d cont t ->
                              Sig en G vdash ([a_ 0 cast t /s 0] d) cont (sel p L)
                                
where "Sig 'en' G 'vdash' d 'cont' t" := (contains Sig G t d).

Hint Constructors has contains.

Scheme has_mut_ind := Induction for has Sort Prop
  with contains_mut_ind := Induction for contains Sort Prop.             

Combined Scheme has_contains_mutind from has_mut_ind, contains_mut_ind.


Reserved Notation "Sig 'en' G1 'vdash' t1 '<;' t2 'dashv' G2" (at level 80).
Reserved Notation "Sig 'en' G1 'vdash' d1 '<;;' d2 'dashv' G2" (at level 80).
Reserved Notation "Sig 'en' G1 'vdash' ds1 '<;;;' ds2 'dashv' G2" (at level 80).

Inductive sub : env -> env -> ty -> ty -> env -> Prop :=
| s_top : forall Sig G1 t G2, Sig en G1 vdash t <; top dashv G2
| s_bot : forall Sig G1 t G2, Sig en G1 vdash bot <; t dashv G2
| s_refl : forall Sig G1 p L G2, Sig en G1 vdash (sel p L) <; (sel p L) dashv G2
| s_arr : forall Sig G1 t1 t1' t2 t2' G2 i, Sig en G1 vdash t1 <; t2 dashv G2 ->
                                     i = length G1 ->
                                     i = length G2 ->
                                     Sig en t1::G1 vdash ([c_ i /t 0] t1') <; ([c_ i /t 0] t2') dashv t2::G2 ->
                                     Sig en G1 vdash (t1 arr t1') <; (t2 arr t2') dashv G2
                                       
| s_upper : forall Sig G1 p L t1 t2 G2, Sig en G1 vdash p ni (type L ext t1) ->
                                 Sig en G1 vdash t1 <; t2 dashv G2 ->
                                 Sig en G1 vdash (sel p L) <; t2 dashv G2
                                   
| s_lower : forall Sig G1 t1 p L t2 G2, Sig en G2 vdash p ni (type L sup t2) ->
                                 Sig en G1 vdash t1 <; t2 dashv G2 ->
                                 Sig en G1 vdash t1 <; (sel p L) dashv G2
                                   
| s_equal1 : forall Sig G1 t1 p L t2 G2, Sig en G1 vdash p ni (type L eqt t1) ->
                                  Sig en G1 vdash t1 <; t2 dashv G2 ->
                                  Sig en G1 vdash (sel p L) <; t2 dashv G2
                                    
| s_equal2 : forall Sig G1 t1 p L t2 G2, Sig en G2 vdash p ni (type L eqt t2) ->
                                  Sig en G1 vdash t1 <; t2 dashv G2 ->
                                  Sig en G1 vdash t1 <; (sel p L) dashv G2

| s_struct : forall Sig G1 ds1 ds2 G2 i, i = length G1 ->
                                  i = length G2 ->
                                  Sig en (str ds1)::G1 vdash [c_ i /ss 0] ds1 <;;; [c_ i /ss 0] ds2 dashv (str ds2)::G2 ->
                                  Sig en G1 vdash str ds1 <; str ds2 dashv G2

where "Sig 'en' G1 'vdash' t1 '<;' t2 'dashv' G2" := (sub Sig G1 t1 t2 G2)

with
sub_d : env -> env -> decl_ty -> decl_ty -> env -> Prop :=
| sd_upper : forall Sig G1 L t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                                Sig en G1 vdash (type L ext t1) <;; (type L ext t2) dashv G2
| sd_lower : forall Sig G1 L t1 t2 G2, Sig en G2 vdash t2 <; t1 dashv G1 ->
                                Sig en G1 vdash (type L sup t1) <;; (type L sup t2) dashv G2
| sd_eq_up : forall Sig G1 L t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                                Sig en G1 vdash (type L eqt t1) <;; (type L ext t2) dashv G2
| sd_eq_lo : forall Sig G1 L t1 t2 G2, Sig en G2 vdash t2 <; t1 dashv G1 ->
                                Sig en G1 vdash (type L eqt t1) <;; (type L sup t2) dashv G2
| sd_equal : forall Sig G1 L t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                                Sig en G2 vdash t2 <; t1 dashv G1 ->
                                Sig en G1 vdash (type L eqt t1) <;; (type L eqt t2) dashv G2
| sd_value : forall Sig G1 l t1 t2 G2, Sig en G1 vdash t1 <; t2 dashv G2 ->
                                Sig en G2 vdash t2 <; t1 dashv G1 ->
                                Sig en G1 vdash (val l oft t1) <;; (val l oft t2) dashv G2

where "Sig 'en' G1 'vdash' d1 '<;;' d2 'dashv' G2" := (sub_d Sig G1 d1 d2 G2)

with
sub_ds : env -> env -> decl_tys -> decl_tys -> env -> Prop :=
| sd_nil : forall Sig G1 G2, Sig en G1 vdash dt_nil <;;; dt_nil dashv G2
| sd_cons : forall Sig G1 d1 ds1 d2 ds2 G2, Sig en G1 vdash d1 <;; d2 dashv G2 ->
                                     Sig en G1 vdash ds1 <;;; ds2 dashv G2 ->
                                     Sig en G1 vdash (dt_con d1 ds1) <;;; (dt_con d2 ds2) dashv G2

where "Sig 'en' G1 'vdash' ds1 '<;;;' ds2 'dashv' G2" := (sub_ds Sig G1 ds1 ds2 G2).

Hint Constructors sub sub_d sub_ds.

Scheme sub_mut_ind := Induction for sub Sort Prop
  with sub_s_mut_ind := Induction for sub_d Sort Prop
  with sub_ss_mut_ind := Induction for sub_ds Sort Prop.

Combined Scheme sub_mutind from sub_mut_ind, sub_s_mut_ind, sub_ss_mut_ind.


Inductive closed : nat -> var -> Prop :=
| cl_concrete : forall n x, closed n (Var x)
| cl_abstract : forall n x, n <> x ->
                       closed n (Abs x).

Hint Constructors closed.

Inductive closed_t : nat -> ty -> Prop :=
| cl_top : forall n, closed_t n top
| cl_bot : forall n, closed_t n bot
| cl_sel : forall n p L, closed_e n p ->
                    closed_t n (sel p L)
| cl_arr : forall n t1 t2, closed_t n t1 ->
                      closed_t (S n) t2 ->
                      closed_t n (t1 arr t2)
| cl_str : forall n ss, closed_ss (S n) ss ->
                   closed_t n (str ss)

with
closed_s : nat -> decl_ty -> Prop :=
| cls_upper : forall n L t, closed_t n t ->
                       closed_s n (type L ext t)
| cls_lower : forall n L t, closed_t n t ->
                       closed_s n (type L sup t)
| cls_equal : forall n L t, closed_t n t ->
                       closed_s n (type L eqt t)
| cls_value : forall n l t, closed_t n t ->
                       closed_s n (val l oft t)

with
closed_ss : nat -> decl_tys -> Prop :=
| cls_nil : forall n, closed_ss n dt_nil
| cls_cons : forall n s ss, closed_s n s ->
                       closed_ss n ss ->
                       closed_ss n (dt_con s ss)

with
closed_e : nat -> exp -> Prop :=
| cl_var : forall n x, closed n x ->
                  closed_e n (v_ x)
| cl_loc : forall n i, closed_e n (i_ i)
| cl_cast : forall n e t, closed_e n e ->
                     closed_t n t ->
                     closed_e n (e cast t)
| cl_new : forall n ds, closed_ds (S n) ds ->
                   closed_e n (new ds)
| cl_app : forall n e1 e2, closed_e n e1 ->
                      closed_e n e2 ->
                      closed_e n (e_app e1 e2)
| cl_acc : forall n e l, closed_e n e ->
                    closed_e n (e_acc e l)
| cl_fn : forall n t1 e t2, closed_t n t1 ->
                       closed_e (S n) e ->
                       closed_t (S n) t2 ->
                       closed_e n (fn t1 in_exp e off t2)

with
closed_d : nat -> decl -> Prop :=
| cld_equal : forall n l t, closed_t n t ->
                       closed_d n (type l eqe t)
| cld_value : forall n l e t, closed_e n e ->
                         closed_t n t ->
                         closed_d n (val l assgn e oft t)

with
closed_ds : nat -> decls -> Prop :=
| cld_nil : forall n, closed_ds n d_nil
| cld_con : forall n d ds, closed_d n d ->
                      closed_ds n ds ->
                      closed_ds n (d_con d ds).

Hint Constructors closed_t closed_s closed_ss closed_e closed_d closed_ds.

Scheme closed_t_mut_ind := Induction for closed_t Sort Prop
  with closed_s_mut_ind := Induction for closed_s Sort Prop
  with closed_ss_mut_ind := Induction for closed_ss Sort Prop
  with closed_e_mut_ind := Induction for closed_e Sort Prop
  with closed_d_mut_ind := Induction for closed_d Sort Prop
  with closed_ds_mut_ind := Induction for closed_ds Sort Prop.

Combined Scheme closed_mutind from closed_t_mut_ind, closed_s_mut_ind, closed_ss_mut_ind, closed_e_mut_ind,
closed_d_mut_ind, closed_ds_mut_ind.

Definition closed_ty (t : ty)(i : nat) := forall n, i <= n -> closed_t n t.
Definition closed_decl_ty (s : decl_ty)(i : nat) := forall n, i <= n -> closed_s n s.
Definition closed_decl_tys (ss : decl_tys)(i : nat) := forall n, i <= n -> closed_ss n ss.
Definition closed_exp (e : exp)(i : nat) := forall n, i <= n -> closed_e n e.
Definition closed_decl (d : decl)(i : nat) := forall n, i <= n -> closed_d n d.
Definition closed_decls (ds : decls)(i : nat) := forall n, i <= n -> closed_ds n ds.

Definition closed_env (G : env)(i : nat) := forall t, In t G -> closed_ty t i.

Reserved Notation "Sig 'en' G 'vdash' e 'hasType' t" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' d 'hasType_d' s" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' ds 'hasType_ds' ss" (at level 80).

Reserved Notation "n 'unbound_t' t" (at level 80).
Reserved Notation "n 'unbound_s' s" (at level 80).
Reserved Notation "n 'unbound_ss' ss" (at level 80).
Reserved Notation "n 'unbound_e' e" (at level 80).
Reserved Notation "n 'unbound_d' d" (at level 80).
Reserved Notation "n 'unbound_ds' ds" (at level 80).
Reserved Notation "n 'unbound_v' v" (at level 80).

Inductive unbound_var : nat -> var -> Prop :=
| ub_abs : forall n m, n unbound_v (Abs m)
| ub_con : forall n m, n <> m ->
                  n unbound_v (Var m)
where "n 'unbound_v' v" := (unbound_var n v).

Inductive unbound_ty : nat -> ty -> Prop :=
| ub_top : forall n, n unbound_t top
| ub_bot : forall n, n unbound_t bot
| ub_arr : forall n t1 t2, n unbound_t t1 ->
                      n unbound_t t2 ->
                      n unbound_t (t1 arr t2)
| ub_sel : forall n p l, n unbound_e p ->
                    n unbound_t (sel p l)
| ub_str : forall n ss, n unbound_ss ss ->
                   n unbound_t (str ss)
where "n 'unbound_t' t" := (unbound_ty n t)

with
unbound_decl_ty : nat -> decl_ty -> Prop :=
| ubs_lower : forall n l t, n unbound_t t ->
                       n unbound_s (type l sup t)
| ubs_upper : forall n l t, n unbound_t t ->
                       n unbound_s (type l ext t)
| ubs_equal : forall n l t, n unbound_t t ->
                       n unbound_s (type l eqt t)
| ubs_value : forall n l t, n unbound_t t ->
                       n unbound_s (val l oft t)
where "n 'unbound_s' s" := (unbound_decl_ty n s)

with
unbound_decl_tys : nat -> decl_tys -> Prop :=
| ubs_nil : forall n, n unbound_ss dt_nil
| ubs_con : forall n s ss, n unbound_s s ->
                      n unbound_ss ss ->
                      n unbound_ss (dt_con s ss)
where "n 'unbound_ss' d" := (unbound_decl_tys n d)
                              
with
unbound_exp : nat -> exp -> Prop :=
| ub_var : forall v n, n unbound_v v ->
                  n unbound_e (v_ v)
| ub_loc : forall i n, n unbound_e (i_ i)
| ub_cast : forall e t n, n unbound_e e ->
                     n unbound_t t ->
                     n unbound_e (e cast t)
| ub_fn : forall t1 e t2 n, n unbound_t t1 ->
                       n unbound_e e ->
                       n unbound_t t2 ->
                       n unbound_e (fn t1 in_exp e off t2)
| ub_app : forall e1 e2 n, n unbound_e e1 ->
                      n unbound_e e2 ->
                      n unbound_e (e_app e1 e2)
| ub_acc : forall e l n, n unbound_e e ->
                    n unbound_e (e_acc e l)
| ub_new : forall ds n, n unbound_ds ds ->
                   n unbound_e (new ds)
where "n 'unbound_e' e" := (unbound_exp n e)

with
unbound_decl : nat -> decl -> Prop :=
| ubd_equal : forall L t n, n unbound_t t ->
                       n unbound_d (type L eqe t)
| ubd_value : forall l e t n, n unbound_e e ->
                         n unbound_t t ->
                         n unbound_d (val l assgn e oft t)
where "n 'unbound_d' d" := (unbound_decl n d)

with
unbound_decls : nat -> decls -> Prop :=
| ubd_nil : forall n, n unbound_ds d_nil
| ubd_con : forall n d ds, n unbound_d d ->
                      n unbound_ds ds ->
                      n unbound_ds (d_con d ds)
where "n 'unbound_ds' ds" := (unbound_decls n ds).


Hint Constructors unbound_var unbound_ty unbound_decl_ty unbound_decl_tys unbound_exp unbound_decl unbound_decls.

Scheme unbound_ty_mutind := Induction for unbound_ty Sort Prop
  with unbound_decl_ty_mutind := Induction for unbound_decl_ty Sort Prop
  with unbound_decl_tys_mutind := Induction for unbound_decl_tys Sort Prop
  with unbound_exp_mutind := Induction for unbound_exp Sort Prop
  with unbound_decl_mutind := Induction for unbound_decl Sort Prop
  with unbound_decls_mutind := Induction for unbound_decls Sort Prop.

Combined Scheme unbound_mutind from unbound_ty_mutind, unbound_decl_ty_mutind, unbound_decl_tys_mutind,
unbound_exp_mutind, unbound_decl_mutind, unbound_decls_mutind.


Inductive typing : env -> env -> exp -> ty -> Prop :=
| t_var : forall  Sig G n t, n mapsto t elem G ->
                      Sig en G vdash (c_ n) hasType t
                        
| t_loc : forall  Sig G i t, i mapsto t elem Sig ->
                      Sig en G vdash (i_ i) hasType t

| t_cast : forall Sig G e t t', Sig en G vdash e hasType t'->
                         Sig en G vdash t' <; t dashv G ->
                         Sig en G vdash e cast t hasType t

| t_fn : forall Sig G t1 e t2, Sig en t1::G vdash ([c_ (length G) /e 0] e) hasType ([c_ (length G) /t 0] t2) ->
                        Sig en G vdash (fn t1 in_exp e off t2) hasType (t1 arr t2)

| t_app : forall Sig G e e' t1 t2 t', Sig en G vdash e hasType (t1 arr t2) ->
                               Sig en G vdash e' hasType t' ->
                               Sig en G vdash t' <; t1 dashv G ->
                               (forall n, closed_t n t1 -> closed_t n t2) ->
                               Sig en G vdash (e_app e e') hasType t2

| t_app_path : forall Sig G e p t1 t2 t', Sig en G vdash e hasType (t1 arr t2) ->
                                   Sig en G vdash p pathType t' ->
                                   Sig en G vdash t' <; t1 dashv G ->
                                   Sig en G vdash (e_app e p) hasType ([p cast t1 /t 0] t2)

| t_new : forall Sig G ds ss, Sig en (str ss)::G vdash ([c_ length G /ds 0] ds) hasType_ds ([c_ length G /ss 0] ss) ->
                       length G unbound_ss ss ->
                       Sig en G vdash new ds hasType str ss

| t_acc_path : forall Sig G p l t, Sig en G vdash p ni (val l oft t) ->
                            Sig en G vdash (e_acc p l) hasType t

| t_acc_closed : forall Sig G e l t t', Sig en G vdash e hasType t' ->
                                 Sig en G vdash (val l oft t) cont t' ->
                                 (forall n, closed_t n t' -> closed_t n t) ->
                                 Sig en G vdash (e_acc e l) hasType t

where "Sig 'en' G 'vdash' e 'hasType' t" := (typing Sig G e t)

with
typing_d : env -> env -> decl -> decl_ty -> Prop :=
| td_equal : forall Sig G L t, Sig en G vdash (type L eqe t) hasType_d (type L eqt t)
| td_val : forall Sig G l e t' t, Sig en G vdash e hasType t' ->
                           Sig en G vdash t' <; t dashv G ->
                           Sig en G vdash (val l assgn e oft t) hasType_d (val l oft t)

where "Sig 'en' G 'vdash' d 'hasType_d' s" := (typing_d Sig G d s)

with
typing_ds : env -> env -> decls -> decl_tys -> Prop :=
| td_nil : forall Sig G, Sig en G vdash d_nil hasType_ds dt_nil
| td_con : forall Sig G d ds s ss, Sig en G vdash d hasType_d s ->
                            Sig en G vdash ds hasType_ds ss ->
                            Sig en G vdash (d_con d ds) hasType_ds (dt_con s ss)

where "Sig 'en' G 'vdash' ds 'hasType_ds' ss" := (typing_ds Sig G ds ss).

Hint Constructors typing typing_d typing_ds.

Scheme typing_mut_ind := Induction for typing Sort Prop
  with typing_d_mut_ind := Induction for typing_d Sort Prop
  with typing_ds_mut_ind := Induction for typing_ds Sort Prop.

Combined Scheme typing_mutind from typing_mut_ind, typing_d_mut_ind, typing_ds_mut_ind.

Reserved Notation "u 'hasType_u' Sig" (at level 80).

Inductive store_typing : mu -> env -> Prop :=
| t_nil : nil hasType_u nil
| t_con : forall t Sig e u, Sig en nil vdash e hasType t ->
                     u hasType_u Sig ->
                     (e::u) hasType_u (t::Sig)

where "u 'hasType_u' Sig" := (store_typing u Sig).

Reserved Notation "Sig 'en' G 'vdash' e 'mem' d" (at level 80).

Inductive member : env -> env -> exp -> decl_ty -> Prop :=
| mem_path : forall Sig G p d, Sig en G vdash p ni d ->
                        Sig en G vdash p mem d
| mem_exp : forall Sig G e t d, Sig en G vdash e hasType t ->
                         Sig en G vdash d cont t ->
                         closed_s 0 d ->
                         Sig en G vdash e mem d
                           
where "Sig 'en' G 'vdash' e 'mem' d" := (member Sig G e d).


Inductive is_value : exp -> Prop :=
| v_loc : forall i, is_value (i_ i)
| v_fn : forall t1 e t2, is_value (fn t1 in_exp e off t2)
| v_cast : forall v t, is_value v ->
                  is_value (v cast t).

Inductive is_value_d : decl -> Prop :=
| v_upper : forall L t, is_value_d (type L eqe t)
| v_value : forall l v t, is_value v ->
                     is_value_d (val l assgn v oft t).

Inductive is_value_ds : decls -> Prop :=
| v_nil : is_value_ds d_nil
| v_con : forall d ds, is_value_d d ->
                  is_value_ds ds ->
                  is_value_ds (d_con d ds).

Notation "u 'bar' e" := (u, e)(at level 80).
Reserved Notation "p1 'reduce' p2" (at level 80).
Reserved Notation "p1 'reduce_d' p2" (at level 80).
Reserved Notation "p1 'reduce_ds' p2" (at level 80).

(*Inductive mapsto : mu -> exp -> decls -> Prop :=
  | map_loc : forall u i ds, get i u = Some (new ds) ->
                        mapsto u (i_ i) ds
  | map_cast : forall u v t ds, mapsto u v ds ->
                           mapsto u (v cast t) ds.*)

Inductive in_ds : decl -> decls -> Prop :=
| ind_head : forall d ds, in_ds d ds
| ind_tail : forall d ds d', in_ds d ds ->
                        in_ds d (d_con d' ds).

Inductive reduction : (mu * exp) -> (mu * exp) -> Prop :=
| r_new : forall u ds, is_value_ds ds ->
                  (u bar new ds) reduce (u ++ (new ds::nil) bar i_ 0)
                               
| r_app : forall u t1 e t2 v, is_value v ->
                         (u bar e_app (fn t1 in_exp e off t2) v) reduce (u bar [v cast t1 /e 0] (e cast t2))

| r_app_cast : forall u v t1 t2 v', is_value v ->
                               is_value v' ->
                               (u bar e_app (v cast (t1 arr t2)) v') reduce (u bar ((e_app v (v' cast t1)) cast ([v' /t 0] t2)))

| r_acc : forall u i l ds e t, i mapsto (new ds) elem u ->
                          in_ds (val l assgn e oft t) ds ->
                          (u bar e_acc (i_ i) l) reduce (u bar [i_ i /e 0] e)

| r_acc_cast : forall u Sig v t l t', is_value v ->
                               u hasType_u Sig ->
                               Sig en nil vdash v cast t ni (val l oft t') ->
                               (u bar e_acc (v cast t) l) reduce (u bar ((e_acc v l) cast t'))

| r_new_ctx : forall u ds u' ds', u bar ds reduce_ds (u' bar ds') ->
                             u bar new ds reduce (u' bar new ds')

| r_app_ctx_1 : forall u e1 e2 u' e', u bar e1 reduce (u' bar e') ->
                                 u bar e_app e1 e2 reduce (u' bar e_app e' e2)

| r_app_ctx_2 : forall u e1 e2 u' e', u bar e2 reduce (u' bar e') ->
                                 u bar e_app e1 e2 reduce (u' bar e_app e1 e')

| r_acc_ctx : forall u e l u' e', u bar e reduce (u' bar e') ->
                             (u bar e_acc e l) reduce (u' bar (e_acc e' l))

| r_cast_ctx : forall u e t u' e', (u bar e) reduce (u' bar e') -> 
                              (u bar (e cast t)) reduce (u' bar (e' cast t))
                                            

where "p1 'reduce' p2" := (reduction p1 p2)
                            
with
reduction_d : (mu * decl) -> (mu * decl) -> Prop :=
| r_val : forall u e u' e' l t, u bar e reduce (u' bar e') ->
                           u bar (val l assgn e oft t) reduce_d (u' bar (val l assgn e' oft t))

where "p1 'reduce_d' p2" := (reduction_d p1 p2)

with
reduction_ds : (mu * decls) -> (mu * decls) -> Prop :=
| r_head : forall u d ds u' d', u bar d reduce_d (u' bar d') ->
                           u bar (d_con d ds) reduce_ds (u' bar (d_con d' ds))

| r_tail : forall u d ds u' ds', u bar ds reduce_ds (u' bar ds') ->
                            u bar (d_con d ds) reduce_ds (u' bar (d_con d ds'))

where "p1 'reduce_ds' p2" := (reduction_ds p1 p2).


Inductive lt_t : ty -> nat -> Prop :=
| lt_top : forall n, lt_t top n
| lt_bot : forall n, lt_t bot n
| lt_sel : forall p L n, lt_e p n ->
                    lt_t (sel p L) n
| lt_arr : forall t1 t2 n, lt_t t1 n ->
                      lt_t t2 n ->
                      lt_t (t1 arr t2) n
| lt_str : forall ss n, lt_ss ss n ->
                   lt_t (str ss) n

with
lt_s : decl_ty -> nat -> Prop :=
| lts_upper : forall L t n, lt_t t n ->
                       lt_s (type L ext t) n
| lts_lower : forall L t n, lt_t t n ->
                       lt_s (type L sup t) n
| lts_equal : forall L t n, lt_t t n ->
                       lt_s (type L eqt t) n
| lts_value : forall l t n, lt_t t n ->
                       lt_s (val l oft t) n

with
lt_ss : decl_tys -> nat -> Prop :=
| lts_nil : forall n, lt_ss dt_nil n
| lts_con : forall n s ss, lt_s s n ->
                      lt_ss ss n ->
                      lt_ss (dt_con s ss) n

with
lt_e : exp -> nat -> Prop :=
| lt_concrete : forall r n, r < n ->
                       lt_e (c_ r) n
| lt_abstract : forall r n, lt_e (a_ r) n
| lt_loc : forall i n, lt_e (i_ i) n
| lt_cast : forall e t n, lt_e e n ->
                     lt_t t n ->
                     lt_e (e cast t) n
| lt_fn : forall t1 e t2 n, lt_t t1 n ->
                       lt_e e n ->
                       lt_t t2 n ->
                       lt_e (fn t1 in_exp e off t2) n
| lt_app : forall e1 e2 n, lt_e e1 n ->
                      lt_e e2 n ->
                      lt_e (e_app e1 e2) n
| lt_acc : forall e l n, lt_e e n ->
                    lt_e (e_acc e l) n
| lt_new : forall ds n, lt_ds ds n ->
                   lt_e (new ds) n

with
lt_d : decl -> nat -> Prop :=
| ltd_equal : forall L t n, lt_t t n ->
                       lt_d (type L eqe t) n
| ltd_value : forall l e t n, lt_e e n ->
                         lt_t t n ->
                         lt_d (val l assgn e oft t) n

with
lt_ds : decls -> nat -> Prop :=
| ltd_nil : forall n, lt_ds d_nil n
| ltd_con : forall d ds n, lt_d d n ->
                      lt_ds ds n ->
                      lt_ds (d_con d ds) n.


Hint Constructors lt_t lt_s lt_ss lt_e lt_d lt_ds.

Scheme lt_t_mutind := Induction for lt_t Sort Prop
  with lt_s_mutind := Induction for lt_s Sort Prop
  with lt_ss_mutind := Induction for lt_ss Sort Prop
  with lt_e_mutind := Induction for lt_e Sort Prop
  with lt_d_mutind := Induction for lt_d Sort Prop
  with lt_ds_mutind := Induction for lt_ds Sort Prop.

Combined Scheme lt_mutind from lt_t_mutind, lt_s_mutind, lt_ss_mutind, lt_e_mutind, lt_d_mutind, lt_ds_mutind.

Definition lt_env (G : env)(n : nat) := forall t, In t G -> lt_t t n.

(*Inductive ge_t : ty -> nat -> Prop :=
  | ge_top : forall n, ge_t top n
  | ge_bot : forall n, ge_t bot n
  | ge_arr : forall t1 t2 n, *)



Reserved Notation "e 'notin_t' t" (at level 80).
Reserved Notation "e 'notin_s' s" (at level 80).
Reserved Notation "e 'notin_ss' ss" (at level 80).
Reserved Notation "e1 'notin_e' e2" (at level 80).
Reserved Notation "e 'notin_d' d" (at level 80).
Reserved Notation "e 'notin_ds' ds" (at level 80).
Reserved Notation "e 'notin_v' v" (at level 80).

Inductive notin_ty : exp -> ty -> Prop :=
| ni_top : forall e, e notin_t top
| ni_bot : forall e, e notin_t bot
| ni_arr : forall e t1 t2, e notin_t t1 ->
                      (e raise_e 0) notin_t t2 ->
                      e notin_t (t1 arr t2)
| ni_sel : forall e p l, e notin_e p ->
                    e notin_t (sel p l)
| ni_str : forall e ss, (e raise_e 0) notin_ss ss ->
                   e notin_t (str ss)
where "e 'notin_t' t" := (notin_ty e t)

with
notin_decl_ty : exp -> decl_ty -> Prop :=
| nit_upper : forall e l t, e notin_t t ->
                       e notin_s (type l ext t)
| nit_lower : forall e l t, e notin_t t ->
                       e notin_s (type l sup t)
| nit_equal : forall e l t, e notin_t t ->
                       e notin_s (type l eqt t)
| nit_value : forall e l t, e notin_t t ->
                       e notin_s (val l oft t)
where "e 'notin_s' s" := (notin_decl_ty e s)

with
notin_decl_tys : exp -> decl_tys -> Prop :=
| nit_nil : forall e, e notin_ss dt_nil
| nit_con : forall e s ss, e notin_s s ->
                      e notin_ss ss ->
                      e notin_ss (dt_con s ss)
where "e 'notin_ss' ss" := (notin_decl_tys e ss)

with
notin_exp : exp -> exp -> Prop :=
| ni_var : forall e x, e <> (v_ x) ->
                  e notin_e (v_ x)
| ni_loc : forall e i, e <> (i_ i) ->
                  e notin_e (i_ i)
| ni_cast : forall e e' t, e notin_e e' ->
                      e notin_t t ->
                      e <> (e' cast t) ->
                      e notin_e (e' cast t)
| ni_fn : forall e t1 e' t2, e notin_t t1 ->
                        (e raise_e 0) notin_e e' ->
                        (e raise_e 0) notin_t t2 ->
                        e <> (fn t1 in_exp e' off t2) ->
                        e notin_e (fn t1 in_exp e' off t2)
| ni_app : forall e e1 e2, e notin_e e1 ->
                      e notin_e e2 ->
                      e <> (e_app e1 e2) ->
                      e notin_e (e_app e1 e2)
| ni_acc : forall e e' l, e notin_e e' ->
                     e <> (e_acc e' l) ->
                     e notin_e (e_acc e' l)
| ni_new : forall e ds, (e raise_e 0) notin_ds ds ->
                   e <> (new ds) ->
                   e notin_e (new ds)
where "e 'notin_e' e'" := (notin_exp e e')

with
notin_decl : exp -> decl -> Prop :=
| nie_equal : forall e t l, e notin_t t ->
                       e notin_d (type l eqe t)
| nie_value : forall e l e' t, e notin_e e' ->
                          e notin_t t ->
                          e notin_d (val l assgn e' oft t)
where "e 'notin_d' d" := (notin_decl e d)

with
notin_decls : exp -> decls -> Prop :=
| nie_nil : forall e, e notin_ds d_nil
| nie_con : forall e d ds, e notin_d d ->
                      e notin_ds ds ->
                      e notin_ds (d_con d ds)
where "e 'notin_ds' ds" := (notin_decls e ds).

Hint Constructors notin_ty notin_decl_ty notin_decl_tys notin_exp notin_decl notin_decls.

Scheme notin_ty_mutind := Induction for notin_ty Sort Prop
  with notin_decl_ty_mutind := Induction for notin_decl_ty Sort Prop
  with notin_decl_tys_mutind := Induction for notin_decl_tys Sort Prop
  with notin_exp_mutind := Induction for notin_exp Sort Prop
  with notin_decl_mutind := Induction for notin_decl Sort Prop
  with notin_decls_mutind := Induction for notin_decls Sort Prop.

Combined Scheme notin_mutind from notin_ty_mutind, notin_decl_ty_mutind, notin_decl_tys_mutind,
notin_exp_mutind, notin_decl_mutind, notin_decls_mutind.

Definition notin_environment (e : exp)(G : env) := forall t, In t G -> e notin_t t.

Notation "e 'notin_env' G" := (notin_environment e G)(at level 80).

Fixpoint synsize_t (t : ty) : nat :=
  match t with
  | top => 0
  | bot => 0
  | t1 arr t2 => 1 + synsize_t t1 + synsize_t t2
  | str ss => 1 + synsize_ss ss
  | sel p l => 1 + synsize_e p
  end

with
synsize_s (s : decl_ty) : nat :=
  match s with
  | type l ext t => 1 + synsize_t t
  | type l sup t => 1 + synsize_t t
  | type l eqt t => 1 + synsize_t t
  | val l oft t => 1 + synsize_t t
  end

with
synsize_ss (ss : decl_tys) : nat :=
  match ss with
  | dt_nil => 0
  | dt_con s ss => 1 + synsize_s s + synsize_ss ss
  end

with
synsize_e (e : exp) : nat :=
  match e with
  | fn t1 in_exp e off t2 => 1 + synsize_t t1 + synsize_e e + synsize_t t2
  | e_app e1 e2 => 1 + synsize_e e1 + synsize_e e2
  | e_acc e' _ => 1 + synsize_e e'
  | new ds => 1 + synsize_ds ds
  | e' cast t => 1 + synsize_e e' + synsize_t t
  | _ => 0
  end

with
synsize_d (d : decl) : nat :=
  match d with
  | type _ eqe t => 1 + synsize_t t
  | val _ assgn e oft t => 1 + synsize_e e + synsize_t t
  end

with
synsize_ds (ds : decls) : nat :=
  match ds with
  | d_nil => 0
  | d_con d ds => 1 + synsize_d d + synsize_ds ds
  end.


Inductive root : exp -> exp -> Prop :=
| root_var : forall r, root (c_ r) (c_ r)
| root_loc : forall i, root (i_ i) (i_ i)
| root_cast : forall r p t, root r p ->
                       root r (p cast t).

Hint Constructors root.

Reserved Notation "Sig 'en' G 'vdash' t 'wf_t'" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' d 'wf_s'" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' ds 'wf_ss'" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' e 'wf_e'" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' d 'wf_d'" (at level 80).
Reserved Notation "Sig 'en' G 'vdash' ds 'wf_ds'" (at level 80).

Definition distinct (ss : decl_tys) : Prop :=
  forall s1 s2, in_dty s1 ss ->
           in_dty s2 ss ->
           id_t s1 = id_t s2 ->
           s1 = s2.

Inductive wf_ty : env -> env -> ty -> Prop :=
| wf_top : forall Sig G, Sig en G vdash top wf_t
                    
| wf_bot : forall Sig G, Sig en G vdash bot wf_t
                    
| wf_arr : forall Sig G t1 t2, Sig en G vdash t1 wf_t ->
                        (length G) unbound_t t2 ->
                        Sig en t1::G vdash ([c_ length G /t 0] t2) wf_t ->
                        Sig en G vdash (t1 arr t2) wf_t

| wf_sel_upper : forall Sig G p L t, Sig en G vdash p wf_e ->
                              is_path p ->
                              Sig en G vdash p ni (type L ext t) ->
                              Sig en G vdash (sel p L) wf_t

| wf_sel_lower : forall Sig G p L t, Sig en G vdash p wf_e ->
                              is_path p ->
                              Sig en G vdash p ni (type L sup t) ->
                              Sig en G vdash (sel p L) wf_t

| wf_sel_equal : forall Sig G p L t, Sig en G vdash p wf_e ->
                              is_path p ->
                              Sig en G vdash p ni (type L eqt t) ->
                              Sig en G vdash (sel p L) wf_t

| wf_str : forall Sig G ss, (length G) unbound_ss ss ->
                     Sig en (str ss)::G vdash ([c_ length G /ss 0] ss) wf_ss ->
                     Sig en G vdash (str ss) wf_t

where "Sig 'en' G 'vdash' t 'wf_t'" := (wf_ty Sig G t)

with
wf_decl_ty : env -> env -> decl_ty -> Prop :=
| wft_upper : forall Sig G L t, Sig en G vdash t wf_t ->
                         Sig en G vdash (type L ext t) wf_s

| wft_lower : forall Sig G L t, Sig en G vdash t wf_t ->
                         Sig en G vdash (type L sup t) wf_s

| wft_equal : forall Sig G L t, Sig en G vdash t wf_t ->
                         Sig en G vdash (type L eqt t) wf_s

| wft_value : forall Sig G l t, Sig en G vdash t wf_t ->
                         Sig en G vdash (val l oft t) wf_s

where "Sig 'en' G 'vdash' s 'wf_s'" := (wf_decl_ty Sig G s)

with
wf_decl_tys : env -> env -> decl_tys -> Prop :=
| wft_nil : forall Sig G, Sig en G vdash dt_nil wf_ss
| wft_con : forall Sig G s ss, Sig en G vdash s wf_s ->
                        Sig en G vdash ss wf_ss ->
                        (forall s', in_dty s' ss ->
                               id_t s' <> id_t s) ->
                        Sig en G vdash (dt_con s ss) wf_ss

where "Sig 'en' G 'vdash' ss 'wf_ss'" := (wf_decl_tys Sig G ss)

with
wf_exp : env -> env -> exp -> Prop :=
| wf_var : forall Sig G n, n < length G ->
                    Sig en G vdash (c_ n) wf_e

| wf_loc : forall Sig G i, i < length Sig ->
                    Sig en G vdash (i_ i) wf_e

| wf_fn : forall Sig G t1 e t2, Sig en G vdash t1 wf_t ->
                         (length G) unbound_e e ->
                         Sig en t1::G vdash ([c_ length G /e 0] e) wf_e ->
                         (length G) unbound_t t2 ->
                         Sig en t1::G vdash ([c_ length G /t 0] t2) wf_t ->
                         Sig en t1::G vdash ([c_ length G /e 0] e) hasType ([c_ length G /t 0] t2) ->
                         Sig en G vdash fn t1 in_exp e off t2 wf_e

| wf_app : forall Sig G e e' t1 t2, Sig en G vdash e wf_e ->
                             Sig en G vdash e' wf_e ->
                             Sig en G vdash e hasType (t1 arr t2) ->
                             Sig en G vdash e' hasType t1 ->
                             Sig en G vdash (e_app e e') wf_e

| wf_acc : forall Sig G e l t', Sig en G vdash e wf_e ->
                         Sig en G vdash e mem (val l oft t') ->
                         Sig en G vdash e_acc e l wf_e

| wf_cast : forall Sig G e t t', Sig en G vdash e wf_e ->
                          Sig en G vdash t wf_t ->
                          Sig en G vdash e hasType t' ->
                          Sig en G vdash t' <; t dashv G ->
                          Sig en G vdash e cast t wf_e

| wf_new : forall Sig G ds ss, Sig en G vdash new ds hasType str ss ->
                        (length G) unbound_ds ds ->
                        Sig en (str ss)::G vdash ([c_ length G /ds 0] ds) wf_ds ->
                        Sig en G vdash new ds wf_e

where "Sig 'en' G 'vdash' e 'wf_e'" := (wf_exp Sig G e)

with
wf_decl : env -> env -> decl -> Prop :=
| wfe_equal : forall Sig G L t, Sig en G vdash t wf_t ->
                         Sig en G vdash (type L eqe t) wf_d

| wfe_value : forall Sig G l e t t', Sig en G vdash e wf_e ->
                              Sig en G vdash t wf_t ->
                              Sig en G vdash e hasType t' ->
                              Sig en G vdash t' <; t dashv G ->
                              Sig en G vdash (val l assgn e oft t) wf_d

where "Sig 'en' G 'vdash' d 'wf_d'" := (wf_decl Sig G d)

with
wf_decls : env -> env -> decls -> Prop :=
| wfe_nil : forall Sig G, Sig en G vdash d_nil wf_ds
                     
| wfe_con : forall Sig G d ds, Sig en G vdash d wf_d ->
                        Sig en G vdash ds wf_ds ->
                        (forall d', in_d d' ds ->
                               id_d d' <> id_d d) ->
                        Sig en G vdash (d_con d ds) wf_ds

where "Sig 'en' G 'vdash' ds 'wf_ds'" := (wf_decls Sig G ds).

Hint Constructors wf_ty wf_decl_ty wf_decl_tys wf_exp wf_decl wf_decls.

Scheme wf_ty_mut_ind := Induction for wf_ty Sort Prop
  with wf_decl_ty_mut_ind := Induction for wf_decl_ty Sort Prop
  with wf_decl_tys_mut_ind := Induction for wf_decl_tys Sort Prop
  with wf_exp_mut_ind := Induction for wf_exp Sort Prop
  with wf_decl_mut_ind := Induction for wf_decl Sort Prop
  with wf_decls_mut_ind := Induction for wf_decls Sort Prop.

Combined Scheme wf_mutind from wf_ty_mut_ind, wf_decl_ty_mut_ind, wf_decl_tys_mut_ind,
wf_exp_mut_ind, wf_decl_mut_ind, wf_decls_mut_ind.

Reserved Notation "Sig 'evdash' G 'wf_env'" (at level 80).

Inductive wf_environment : env -> env -> Prop :=
| wf_nil : forall Sig, Sig evdash nil wf_env
| wf_con : forall Sig t G, Sig en G vdash t wf_t ->
                    Sig evdash G wf_env ->
                    Sig evdash t::G wf_env

where "Sig 'evdash' G 'wf_env'" := (wf_environment Sig G).

Reserved Notation "Sig 'wf_st'" (at level 80).

Inductive wf_store_typing : env -> Prop :=
| wfst_nil : nil wf_st
| wfst_con : forall Sig ds, Sig en nil vdash str ds wf_t ->
                     Sig wf_st ->
                     str ds::Sig wf_st
where "Sig 'wf_st'" := (wf_store_typing Sig).
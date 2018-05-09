Require Export List.
Require Export Bool.
Require Export Arith.
Require Export Peano_dec.
Require Export Coq.Arith.PeanoNat.
Require Import CpdtTactics.
Require Export Coq.Program.Wf.
Require Export Coq.Program.Tactics.
Require Export Recdef.
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
| sel : var -> label -> ty
| fn_t  : ty -> ty -> ty
| top   : ty
| bot  : ty

(*with
path : Type := (*paths*)
| p_var : var -> path
| p_cast : path -> ty -> path*)
                           
with
decl_ty : Type := (*declaration types*)
| dt_upp : label -> ty -> decl_ty
| dt_low : label -> ty -> decl_ty
| dt_val : label -> ty -> decl_ty

with
decl_tys : Type :=
| dt_nil : decl_tys
| dt_con : decl_ty -> decl_tys -> decl_tys.


Inductive exp : Type := (*expressions*)
| new : decls -> exp
| app : exp -> exp -> exp
| e_fn : nat -> ty -> exp -> exp
| e_acc : exp -> label -> exp
| e_var : var -> exp

with
decl : Type := (*declarations*)
| d_upp : label -> ty -> decl
| d_low : label -> ty -> decl
| d_val : label -> exp -> decl

with
decls : Type :=
| d_nil : decls
| d_con : decl -> decls -> decls.



(*Notation "p 'cast' t" := (p_cast p t) (at level 80).
Notation "'v_' x" := (p_var x) (at level 80).*)

Notation "'c_' x" := (Var x) (at level 80).
Notation "'a_' x" := (Abs x) (at level 80).

Notation "'type' l 'sup' t" := (dt_low l t) (at level 80).
Notation "'type' l 'ext' t" := (dt_upp l t) (at level 80).
Notation "'fn' n 'off' t 'in_exp' e" := (e_fn n t e) (at level 80).
Notation "'val' l 'ofv' t" := (dt_val l t) (at level 80).
Notation "t1 'arr' t2" := (fn_t t1 t2) (at level 80).

Scheme type_mut_ind := Induction for ty Sort Prop
  with decl_ty_mut_ind := Induction for decl_ty Sort Prop
  with decl_tys_mut_ind := Induction for decl_tys Sort Prop
  (*with path_mut_ind := Induction for path Sort Prop*).

Combined Scheme type_mutind from type_mut_ind, decl_ty_mut_ind, decl_tys_mut_ind.

Inductive is_material : ty -> Prop :=
| m_top    : is_material top
| m_bot    : is_material bot
| m_struct : forall ds, is_material (str ds)
| m_select : forall p m, is_material (sel p (l_type (Material m))).

Definition id (d : decl_ty) : label :=
  match d with
  | type l sup _ => l
  | type l ext _ => l
  | val l ofv _ => l
  end.

(*Definition bind (x : var) : var :=
  match x with
  | Var _ => x
  | Self n => Var n
  end.*)


Section variables.
  
  Definition env := list ty.
  
  Reserved Notation "'[' p '/t' n ']' t" (at level 80).
  Reserved Notation "'[' p '/d' n ']' d" (at level 80).
  Reserved Notation "'[' p1 '/p' n ']' p2" (at level 80).

  Definition switch_n (n1 n2 m : nat) : nat :=
    if beq_nat n1 m
    then n2
    else if beq_nat n2 m
         then n1
         else m.

  Notation "'[' n1 'swap_n' n2 ']' m" := (switch_n n1 n2 m) (at level 80).

  Definition switch_v (n m : nat) (x : var) : var :=
    match x with
      | Var n' => Var ([n swap_n m] n')
      | _ => x
    end.
  
  Notation "'[' n 'swap_v' m ']'" := (switch_v n m) (at level 80).

  Fixpoint switch (n m : nat) (t : ty) : ty :=
    match t with
    | top => top
    | bot => bot
    | t1 arr t2 => (switch n m t1) arr (switch (S n) (S m) t2) 
    | sel x l => sel (switch_v n m x) l
    | str ds => str (switch_ds (S n) (S m) ds)
    end

  (*with
  switch_p (n m : nat) (p : path) : path :=
    match p with
    | v_ x => v_ [n swap_v m] x
    | p' cast t => (switch_p n m p') cast (switch n m t)
    end*)

  with
  switch_d (n m : nat) (d : decl_ty) : decl_ty :=
    match d with
    | type l sup t => type l sup (switch n m t)
    | type l ext t => type l ext (switch n m t)
    | val l ofv t => val l ofv (switch n m t)
    end

  with
  switch_ds (n m : nat) (ds : decl_tys) : decl_tys :=
    match ds with
      | dt_nil => dt_nil
      | dt_con d ds' => dt_con (switch_d n m d) (switch_ds n m ds')
    end.

  Notation "'[' n 'swap' m ']'" := (switch n m) (at level 80).
(*  Notation "'[' n 'swap_p' m ']'" := (switch_p n m) (at level 80).*)
  Notation "'[' n 'swap_d' m ']'" := (switch_d n m) (at level 80).
  

  Definition switch_env (n m : nat) (G : env) : env :=
    map ([n swap m]) G.
  
  Notation "'[' n 'swap_e' m ']'" := (switch_env n m) (at level 80).

  (*Left Shift*)
  
  Fixpoint left_shift_var (n : nat) (v : var) : var :=
    match v with
      | Var m => Var (n + m)
      | _ => v
    end.
      
  Notation "v 'lshift_v' n" := (left_shift_var n v) (at level 80).
  Reserved Notation "t 'lshift_t' n" (at level 80).
  Reserved Notation "d 'lshift_d' n" (at level 80).
  Reserved Notation "d 'lshift_ds' n" (at level 80).
  Reserved Notation "d 'lshift_dt' n" (at level 80).
  Reserved Notation "d 'lshift_dts' n" (at level 80).
  Reserved Notation "p 'lshift_p' n" (at level 80).
  Reserved Notation "G 'lshift_e' n" (at level 80).
  
  Fixpoint left_shift_type (n : nat) (t : ty) : ty :=
    match t with
      | top => top
      | bot => bot
      | t1 arr t2 => (t1 lshift_t n) arr (t2 lshift_t n)
      | sel x l => sel (x lshift_v n) l
      | str ds => str (ds lshift_dts n)
    end
      where "t 'lshift_t' n" := (left_shift_type n t)

  with
  left_shift_decl_ty (n : nat) (d : decl_ty) : decl_ty :=
    match d with
      | type l sup t => type l sup (t lshift_t n)
      | type l ext t => type l ext (t lshift_t n)
      | val l ofv t => val l ofv (t lshift_t n)
    end
      where "d 'lshift_dt' n" := (left_shift_decl_ty n d)

  with
  left_shift_decl_tys (n : nat) (ds : decl_tys) : decl_tys :=
    match ds with
      | dt_nil => dt_nil
      | dt_con d ds' => dt_con (d lshift_dt n) (ds' lshift_dts n)
    end
      where "d 'lshift_dts' n" := (left_shift_decl_tys n d)

  (*with
  left_shift_path (n : nat) (p : path) : path :=
    match p with
      | v_ x => v_ (x lshift_v n)
      | p cast t => (p lshift_p n) cast (t lshift_t n)
    end
      where "p 'lshift_p' n" := (left_shift_path n p)*).

  

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
    | sel x l => sel (x rshift_v n) l
    | str ds => str (ds rshift_dts n)
    end
  where "t 'rshift_t' n" := (right_shift_type n t)

  with
  right_shift_decl_ty (n : nat) (d : decl_ty) : decl_ty :=
    match d with
    | type l sup t => type l sup (t rshift_t n)
    | type l ext t => type l ext (t rshift_t n)
    | val l ofv t => val l ofv (t rshift_t n)
    end
  where "d 'rshift_dt' n" := (right_shift_decl_ty n d)

  with
  right_shift_decl_tys (n : nat) (ds : decl_tys) : decl_tys :=
    match ds with
      | dt_nil => dt_nil
      | dt_con d ds' => dt_con (d rshift_dt n) (ds' rshift_dts n)
    end
  where "d 'rshift_dts' n" := (right_shift_decl_tys n d)

  (*with
  right_shift_path (n : nat) (p : path) : path :=
    match p with
    | v_ x => v_ (x rshift_v n)
    | p cast t => (p rshift_p n) cast (t rshift_t n)
    end
      where "p 'rshift_p' n" := (right_shift_path n p)*).

  (*Environment shift*)
  
  (*move all variables less than n, 1 space to the left, this means reducing the relative distance of all 
   references greater than or equal to n by 1*)
  
  Reserved Notation "v '[' i ']' 'ljump_v' n" (at level 80).
  Reserved Notation "t '[' i ']' 'ljump_t' n" (at level 80).
  Reserved Notation "d '[' i ']' 'ljump_d' n" (at level 80).
  Reserved Notation "d '[' i ']' 'ljump_ds' n" (at level 80).
  Reserved Notation "d '[' i ']' 'ljump_dt' n" (at level 80).
  Reserved Notation "d '[' i ']' 'ljump_dts' n" (at level 80).
  Reserved Notation "p '[' i ']' 'ljump_p' n" (at level 80).
  Reserved Notation "p '[' i ']' 'ljump_e' n" (at level 80).

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

  Definition left_jump_n (r n: nat) (i : option nat) : nat :=
    match i with
      | None => r
      | Some i' => if r <? i'
                  then r
                  else r + n
    end.

  Notation "r '[' i ']' 'ljump_n' n" := (left_jump_n r n i) (at level  80).

  Fixpoint left_jump_v (x : var)(n : nat)(i : option nat) : var :=
    match x with
      | Var r => Var (r[i] ljump_n n)
      | _ => x
    end.

  Notation "x '[' i ']' 'ljump_v' n" := (left_jump_v x n i) (at level  80).

  Fixpoint left_jump_t (t : ty) (n : nat) (i : option nat): ty  :=
    match t with
      | top => top
      | bot => bot
      | t1 arr t2 => (t1 [i] ljump_t n) arr (t2 [inc i 1] ljump_t n)
      | sel x l => sel (x [i] ljump_v n) l
      | str ds => str (ds [inc i 1] ljump_dts n)
    end
      where "t '[' i ']' 'ljump_t' n" := (left_jump_t t n i)

  with
  left_jump_d_ty (d : decl_ty) (n : nat) (i : option nat) : decl_ty :=
    match d with
      | type l sup t => type l sup (t[i] ljump_t n)
      | type l ext t => type l ext (t[i] ljump_t n)
      | val l ofv t => val l ofv (t[i] ljump_t n)
    end
      where "d '[' i ']' 'ljump_dt' n" := (left_jump_d_ty d n i)

  with
  left_jump_d_tys (d : decl_tys) (n : nat) (i : option nat) : decl_tys :=
    match d with
      | dt_nil => dt_nil
      | dt_con d ds' => dt_con (d [i] ljump_dt n) (ds' [i] ljump_dts n)
    end
      where "d '[' i ']' 'ljump_dts' n" := (left_jump_d_tys d n i)

  (*with
  left_jump_p (p : path) (n : nat) (i : option nat) : path :=
    match p with
      | v_ x => v_ (x [i] ljump_v n)
      | p cast t => (p [i] ljump_p n) cast (t [i] ljump_t n)
    end
  where "p '[' i ']' 'ljump_p' n" := (left_jump_p p n i)*).

(*  Definition left_jump_option (i n : nat) (o : option ty) : option ty :=
    match o with
    | None => None
    | Some t => Some (t [i] ljump_t n)
    end.

  Notation "o '[' i ']' 'ljump_o' n" := (left_jump_option i n o)(at level 80).*)
  Reserved Notation "'[' p '/t' n ']' ds" (at level 80).
  Reserved Notation "'[' p '/dt' n ']' ds" (at level 80).
  Reserved Notation "'[' p '/dts' n ']' ds" (at level 80).
  Reserved Notation "'[' p '/d' n ']' ds" (at level 80).
  Reserved Notation "'[' p '/ds' n ']' ds" (at level 80).
  Reserved Notation "'[' p '/p' n ']' ds" (at level 80).


  Definition subst_v (n : nat) (x y : var) : var :=
    match y with
      | Abs m => if beq_nat n m
                then x
                else y
      | _ => y
    end.
  
  Notation "'[' x '/v' n ']' y" := (subst_v n x y) (at level 80).
    
  Fixpoint subst (n : nat) (x : var) (t : ty) : ty :=
    match t with
    | top => top
    | bot => bot
    | t1 arr t2 => ([x /t n] t1) arr ([x /t n] t2)
    | sel y l => sel ([ x /v n ] y) l
    | str ds => str ([ x lshift_v 1 /dts S n ] ds)
    end

  where "'[' p '/t' n ']' t" := (subst n p t)

  with
  subst_d_ty (n : nat) (x : var) (d : decl_ty) : decl_ty :=
    match d with
    | type l sup t => type l sup ([x /t n] t)
    | type l ext t => type l ext ([x /t n] t)
    | val l ofv t => val l ofv ([x /t n] t)                        
    end
      
  where "'[' p '/dt' n ']' d" := (subst_d_ty n p d)

  with
  subst_d_tys (n : nat) (x : var) (d : decl_tys) : decl_tys :=
    match d with
      | dt_nil => dt_nil
      | dt_con d ds' => dt_con ([x /dt n] d) ([x /dts n] ds')
    end
      
  where "'[' p '/dts' n ']' d" := (subst_d_tys n p d)

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
                              
      
  where "'[' p1 '/p' n ']' p2" := (subst_p n p1 p2)*).

  Fixpoint get (n : nat) (l : list ty) : option ty :=
    match l with 
    | nil  => None
    | h::t => match n with
              | O => Some h
              | S m => get m t
              end
    end.

  (*Definition get (n : nat) (l : list ty) : option ty :=
    nth n (rev l).*)
  
  Reserved Notation "G 'vdash' p 'hasType' t" (at level 80).
  
  Inductive typing : env -> var -> ty -> Prop :=
  | t_var : forall G n t, get n G = Some t ->
                     G vdash (c_ n) hasType (t lshift_t (S n))
  (*| t_cast : forall G p t, G vdash (p cast t) hasType t*)

  where "G 'vdash' p 'hasType' t" := (typing G p t).

  Reserved Notation "G 'vdash' p 'ni' d" (at level 80).
  Reserved Notation "G 'vdash' d 'cont' t" (at level 80).

  Hint Constructors typing.

  Inductive in_dty : decl_ty -> decl_tys -> Prop :=
  | in_head_dty : forall d ds, in_dty d (dt_con d ds)
  | in_tail_dty : forall d d' ds, in_dty d ds ->
                             in_dty d (dt_con d' ds).
  
  Inductive has : env -> var -> decl_ty -> Prop :=
  | h_path : forall G p d t, G vdash p hasType t ->
                        G vdash d cont t ->
                        G vdash p ni ([ p /dt O] d)
  where "G 'vdash' p 'ni' d" := (has G p d)
  

  with
  contains : env -> ty -> decl_ty -> Prop :=
  | c_struct1 : forall G d ds, in_dty d ds ->
                          G vdash (d rshift_dt 1) cont (str ds)
  | c_select : forall G p l l' t d, G vdash p ni (type l' ext t) ->
                               G vdash d cont t ->
                               G vdash d cont(sel p l)
                                 where "G 'vdash' d 'cont' t" := (contains G t d). 

  Hint Constructors has contains.
  
  Scheme has_mut_ind := Induction for has Sort Prop
                        with contains_mut_ind := Induction for contains Sort Prop.             

  Combined Scheme has_contains_mutind from has_mut_ind, contains_mut_ind. 
  
  Fixpoint left_jump_env (G : env) (n : nat) (i : option nat) : env :=
    match G with
      | nil => nil
      | t::G' => (t [i] ljump_t n) :: (G' [dec i 1] ljump_e n)
    end
      where "G '[' i ']' 'ljump_e' n" := (left_jump_env G n i).
  
  (*Fixpoint right_jump_env (G : env) (n : nat) (i : option nat) : env :=
    match G with
      | nil => nil
      | t::G' => (t [i] rjump_t n) :: (G' [dec i 1] rjump_e n)
    end
  where "G '[' i ']' 'rjump_e' n" := (right_jump_env G n i).*)

  (*t, d or p does not contain any variable less than n*)

  Inductive ge_var : var -> nat -> Prop :=
  | ge_concrete : forall r n, n <= r ->
                         ge_var (c_ r) n
  | ge_abstract : forall r n, ge_var (a_ r) n.

  Inductive ge_type : ty -> nat -> Prop :=
  | ge_top : forall n, ge_type top n
  | ge_bot : forall n, ge_type bot n
  | ge_arr : forall n t1 t2, ge_type t1 n ->
                        ge_type t2 (S n) ->
                        ge_type (t1 arr t2) n
  | ge_sel : forall p l n, ge_var p n ->
                      ge_type (sel p l) n
  | ge_str : forall ds n, ge_decl_tys ds (S n) ->
                     ge_type (str ds) n

  with
  ge_decl_ty : decl_ty -> nat -> Prop :=
  | ge_low_d : forall l t n, ge_type t n ->
                        ge_decl_ty (type l sup t) n
  | ge_upp_d : forall l t n, ge_type t n ->
                        ge_decl_ty (type l ext t) n
  | ge_val_d : forall l t n, ge_type t n ->
                        ge_decl_ty (val l ofv t) n

  with
  ge_decl_tys : decl_tys -> nat -> Prop :=
  | ge_nil_dt : forall n, ge_decl_tys dt_nil n 
  | ge_con_dt : forall n d ds, ge_decl_ty d n ->
                          ge_decl_tys ds n -> 
                          ge_decl_tys (dt_con d ds) n.

  Hint Constructors ge_type ge_decl_ty ge_decl_tys ge_var.

  Scheme ge_ty_mutind := Induction for ge_type Sort Prop
    with ge_decl_ty_mutind := Induction for ge_decl_ty Sort Prop
    with ge_decl_tys_mutind := Induction for ge_decl_tys Sort Prop.

  Combined Scheme ge_mutind from ge_ty_mutind, ge_decl_ty_mutind, ge_decl_tys_mutind.

  Inductive ge_env : env -> nat -> Prop :=
  | ge_nil : forall n, ge_env nil n
  | ge_cons : forall t G n, ge_type t n ->
                       ge_env G n ->
                       ge_env (t::G) n.

  (*there exists a variable in t, d or p that is less than n*)
                      
  

  Reserved Notation "n 'notin_t' t" (at level 80).
  Reserved Notation "n 'notin_dt' d" (at level 80).
  Reserved Notation "n 'notin_dts' p" (at level 80).
  Reserved Notation "n 'notin_v' v" (at level 80).

  Inductive notin_var : nat -> var -> Prop :=
  | ni_abs : forall n m, n notin_v (a_ m)
  | ni_con : forall n m, n <> m ->
                    n notin_v (c_ m)
                      where "n 'notin_v' p" := (notin_var n p).
  
  Inductive notin_ty : nat -> ty -> Prop :=
  | ni_top : forall n, n notin_t top
  | ni_bot : forall n, n notin_t bot
  | ni_arr : forall n t1 t2, n notin_t t1 ->
                          (S n) notin_t t2 ->
                          n notin_t (t1 arr t2)
  | ni_sel : forall n x l, n notin_v x ->
                      n notin_t (sel x l)
  | ni_str : forall n ds, (S n) notin_dts ds ->
                     n notin_t (str ds)
                       where "n 'notin_t' t" := (notin_ty n t)

  with
  notin_decl_ty : nat -> decl_ty -> Prop :=
  | ni_low_dt : forall n l t, n notin_t t ->
                         n notin_dt (type l sup t)
  | ni_upp_dt : forall n l t, n notin_t t ->
                         n notin_dt (type l ext t)
  | ni_val_dt : forall n l t, n notin_t t ->
                         n notin_dt (val l ofv t)
                           where "n 'notin_dt' d" := (notin_decl_ty n d)

  with
  notin_decl_tys : nat -> decl_tys -> Prop :=
  | ni_nil_dt : forall n, n notin_dts dt_nil
  | ni_con_dt : forall n d ds, n notin_dt d ->
                          n notin_dts ds ->
                          n notin_dts (dt_con d ds)
                          where "n 'notin_dts' d" := (notin_decl_tys n d)

  (*with
  notin_path : nat -> path -> Prop :=
  | ni_abs : forall n m, n notin_p (a_ m)
  | ni_con : forall n m, n <> m ->
                    n notin_p (c_ m)
  | ni_cast : forall n p t, n notin_p p ->
                       n notin_t t ->
                       n notin_p (p cast t)
                         where "n 'notin_p' p" := (notin_path n p)*).

  Hint Constructors notin_ty notin_decl_ty notin_decl_tys.

  Scheme notin_ty_mutind := Induction for notin_ty Sort Prop
    with notin_decl_ty_mutind := Induction for notin_decl_ty Sort Prop
    with notin_decl_tys_mutind := Induction for notin_decl_tys Sort Prop.

  Combined Scheme notin_mutind from notin_ty_mutind, notin_decl_ty_mutind, notin_decl_tys_mutind.

  Reserved Notation "n 'notin_e' G" (at level 80).

  Inductive notin_env : nat -> env -> Prop :=
  | ni_nil : forall n, n notin_e nil
  | ni_cons : forall n G t, n notin_t t ->
                       n notin_e G ->
                       n notin_e (t::G)
                         where "n 'notin_e' G" := (notin_env n G).

  Reserved Notation "G 'vdash' t 'wf_t'" (at level 80).
  Reserved Notation "G 'vdash' d 'wf_d'" (at level 80).
  Reserved Notation "G 'vdash' ds 'wf_ds'" (at level 80).
  Reserved Notation "G 'vdash' p 'wf_v'" (at level 80).

  Inductive wf_var : env -> var -> Prop :=
  | wf_variable : forall G r, r < length G ->
                         G vdash c_ r wf_v
                           
                           where "G 'vdash' v 'wf_v'" := (wf_var G v).
  
  Inductive wf_ty : env -> ty -> Prop := 
  | wf_top : forall G, G vdash top wf_t
  | wf_bot : forall G, G vdash bot wf_t
  | wf_arr : forall G t1 t2, G vdash t1 wf_t ->
                        (t1)::G vdash t2 wf_t ->
                        G vdash (t1 arr t2)  wf_t
  | wf_sel_lower : forall G x l t, G vdash x ni (type l sup t) ->
                              G vdash x wf_v ->
                              G vdash (sel x l) wf_t
  | wf_sel_upper : forall G x l t, G vdash x ni (type l ext t) ->
                              G vdash x wf_v ->
                              G vdash (sel x l) wf_t
  | wf_struct : forall G ds, (str ds)::G vdash ([ c_ O /dts O] ds) wf_ds ->
                        0 notin_dts ds ->
                        G vdash (str ds) wf_t

  where "G 'vdash' t 'wf_t'" := (wf_ty G t)

  with
  wf_decl_ty : env -> decl_ty -> Prop :=
  | wf_low : forall G l t, G vdash t wf_t ->
                      G vdash (type l sup t) wf_d
  | wf_upp : forall G l t, G vdash t wf_t ->
                      G vdash (type l ext t) wf_d
  | wf_val : forall G l t, G vdash t wf_t ->
                      G vdash (val l ofv t) wf_d

  where "G 'vdash' d 'wf_d'" := (wf_decl_ty G d)

  with
  wf_decl_tys : env -> decl_tys -> Prop :=
  | wf_nil : forall G, G vdash dt_nil wf_ds
  | wf_con : forall G d ds, G vdash d wf_d ->
                       G vdash ds wf_ds ->
                       (forall d', in_dty d' ds -> id d' <> id d) ->
                       G vdash (dt_con d ds) wf_ds

  where "G 'vdash' d 'wf_ds'" := (wf_decl_tys G d)

  (*with
  wf_var : env -> path -> Prop :=
  | wf_var : forall G r, r < length G ->
                    G vdash c_ r wf_p
  | wf_cast : forall G p t, G vdash p wf_p ->
                       G vdash t wf_t ->
                       G vdash p cast t wf_p

                         where "G 'vdash' p 'wf_p'" := (wf_path G p)*).

  Hint Constructors wf_ty wf_decl_ty wf_decl_tys.

  Reserved Notation "G 'wf_e'" (at level 80).
  
  Inductive wf_env : env -> Prop :=
  | wf_nil_env : nil wf_e
  | wf_con_env : forall G t, G vdash t wf_t ->
                     t::G wf_e

  where "G 'wf_e'" := (wf_env G).
  
  Scheme wf_ty_mutind := Induction for wf_ty Sort Prop
    with wf_decl_ty_mutind := Induction for wf_decl_ty Sort Prop
    with wf_decl_tys_mutind := Induction for wf_decl_tys Sort Prop.

  Combined Scheme wf_mutind from wf_ty_mutind, wf_decl_ty_mutind, wf_decl_tys_mutind.

 (* Lemma lt_not_ge_mutind :
    (forall t n, (lt_type t n -> ~ ge_type t n)) /\
    (forall d n, (lt_decl d n -> ~ ge_decl d n)) /\
    (forall p n, (lt_path p n -> ~ ge_path p n)).
  Proof.
    apply type_mutind; intros; intro Hcontra.
    
    inversion H0; subst; apply H in H2; inversion Hcontra; subst; auto.
    
    inversion H0; subst; apply H in H4; inversion Hcontra; subst; auto.

    inversion H.

    inversion H.
    
    inversion H0; subst; apply H in H4; inversion Hcontra; subst; auto.
    
    inversion H0; subst; apply H in H4; inversion Hcontra; subst; auto.

    destruct v as [x|x].
    inversion Hcontra; inversion H; crush.

    inversion H.
    
    inversion H1; inversion Hcontra; subst.
    apply H in H5; auto.
    apply H0 in H5; auto.
  Qed.

  Lemma not_lt_ge_mutind :
    (forall t n, (~ lt_type t n -> ge_type t n)) /\
    (forall d n, (~ lt_decl d n -> ge_decl d n)) /\
    (forall p n, (~ lt_path p n -> ge_path p n)).
  Proof.
    apply type_mutind; crush.

    destruct v as [r|r]; auto.

    destruct (ge_dec r n); auto.
    apply not_ge in n0; crush.
  Qed.

  Lemma lt_implies_in_mutind :
    (forall t n, lt_type t n -> exists m, in_type m t /\ m < n) /\
    (forall d n, lt_decl d n -> exists m, in_decl m d /\ m < n) /\
    (forall p n, lt_path p n -> exists m, in_path m p /\ m < n).
  Proof.
    apply type_mutind; intros.

    inversion H0; subst.
    destruct (H (S n)) as [m Hin]; auto;
      destruct Hin as [Hin1 Hin2].
  Qed.
  
  
  Lemma ge_subst :
    (forall t p' x n, ge_type ([p' /t x] t) n -> ge_type t n) /\
    (forall d p' x n, ge_decl ([p' /d x] d) n -> ge_decl d n) /\
    (forall p p' x n, ge_path ([p' /p x] p) n -> ge_path p n).
  Proof.
    apply type_mutind; crush.

    apply ge_str.
    inversion H0; subst.
    apply H in H2; auto.

    apply ge_sel.
    inversion H0; subst.
    apply H in H4; auto.

    apply ge_upper.
    inversion H0; subst.
    apply H in H4; auto.

    apply ge_lower.
    inversion H0; subst.
    apply H in H4; auto.

    destruct v as [r|r]; auto.

    apply ge_cast;
    inversion H1; subst.
    apply H in H4; auto.
    apply H0 in H6; auto.    
  Qed.
  


    

  Lemma wf_ge_O_mutind :
    (forall G t, G vdash t wf_t -> ge_type t O) /\
    (forall G d, G vdash d wf_d -> ge_decl d O) /\
    (forall G p, G vdash p wf_p -> ge_path p O).
  Proof.
    apply wf_mutind; crush.

    apply ge_subst in H;
      apply ge_str.
    apply not_lt_ge_mutind.
    intro Hcontra.
    
  Qed.*)

  Reserved Notation "p1 'equiv' p2" (at level 80).

  (*Inductive path_equiv : path -> path -> Prop :=
  | peq_refl : forall n, v_ n equiv v_ n
  | peq_cast_1 : forall p1 p2 t, p1 equiv p2 ->
                            p1 cast t equiv p2
  | peq_cast_2 : forall p1 p2 t, p1 equiv p2 ->
                            p1 equiv (p2 cast t)
                               where "p1 'equiv' p2" := (path_equiv p1 p2).

  Hint Constructors path_equiv.*)

  (*Lemma equiv_sym :
    forall p1 p2, p1 equiv p2 -> p2 equiv p1.
  Proof.
    intros p1 p2 Heq; induction Heq; auto.
  Qed.

  Hint Resolve equiv_sym.

  Lemma equiv_refl :
    forall p, p equiv p.
  Proof.
    intro p; induction p as [n | p' t]; auto.
  Qed.

  Hint Resolve equiv_refl.*)
    
  (*Lemma equiv_cast :
    forall p1 p2, p1 equiv p2 ->
             forall p1' p2' t1 t2, p1 = (p1' cast t1) ->
                              p2 = (p2' cast t2) ->
                              p1' equiv p2'.
  Proof.
    intro p1; induction p1; intros; subst; crush.

    inversion H; crush.

    
    
  Qed.
   *)

  (*Lemma equiv_uncast :
    forall p1 p2, p1 equiv p2 ->
             forall p t, p2 = (p cast t) ->
                    p1 equiv p.
  Proof.
    intros p1 p2 Heq; induction Heq; crush.
    assert (Hequiv : p1 equiv p); [apply IHHeq with (t:=t0); auto|]; crush.
  Qed.

  Hint Resolve equiv_uncast.

  Lemma equiv_trans :
    forall p1 p2, p1 equiv p2 ->
             forall p3, p2 equiv p3 ->
                   p1 equiv p3.
  Proof.
    intros p1 p2 Heq; induction Heq; intros; crush.
    apply IHHeq.
    apply equiv_sym in H.
    apply equiv_uncast with (p:=p2)(t:=t) in H; auto.
  Qed.

  Hint Resolve equiv_trans.
  Hint Rewrite equiv_trans.*)
  
  Inductive struct_equiv_var : var -> var -> Prop :=
  | seq_abs : forall r, struct_equiv_var (a_ r) (a_ r)
  | seq_con : forall r1 r2, struct_equiv_var (c_ r1) (c_ r2).

  Inductive struct_equiv_type : ty -> ty -> Prop :=
  | seq_top : struct_equiv_type top top
  | seq_bot : struct_equiv_type bot bot
  | seq_arr : forall t1 t2 t1' t2', struct_equiv_type t1 t1' ->
                               struct_equiv_type t2 t2' ->
                               struct_equiv_type (t1 arr t2) (t1' arr t2')
  | seq_sel : forall p1 p2 l, struct_equiv_var p1 p2 ->
                         struct_equiv_type (sel p1 l) (sel p2 l)
  | seq_str : forall ds ds', struct_equiv_decl_tys ds ds' ->
                        struct_equiv_type (str ds') (str ds')

  with
  struct_equiv_decl_ty : decl_ty -> decl_ty -> Prop :=
  | seq_low : forall t1 t2 l, struct_equiv_type t1 t2 ->
                         struct_equiv_decl_ty (type l sup t1) (type l sup t2)
  | seq_upp : forall t1 t2 l, struct_equiv_type t1 t2 ->
                         struct_equiv_decl_ty (type l ext t1) (type l ext t2)
  | seq_val : forall t1 t2 l, struct_equiv_type t1 t2 ->
                         struct_equiv_decl_ty (val l ofv t1) (val l ofv t2)

  with
  struct_equiv_decl_tys : decl_tys -> decl_tys -> Prop :=
  | seq_lower : struct_equiv_decl_tys dt_nil dt_nil
  | seq_upper : forall d1 d2 ds1 ds2, struct_equiv_decl_ty d1 d2 ->
                                 struct_equiv_decl_tys ds1 ds2 ->
                                 struct_equiv_decl_tys (dt_con d1 ds1) (dt_con d2 ds2)

  (*with
  struct_equiv_path : path -> path -> Prop :=
  | seq_abs : forall r, struct_equiv_path (a_ r) (a_ r)
  | seq_con : forall r1 r2, struct_equiv_path (c_ r1) (c_ r2)
  | seq_cast : forall p1 t1 p2 t2, struct_equiv_path p1 p2 ->
                              struct_equiv_type t1 t2 ->
                              struct_equiv_path (p1 cast t1) (p2 cast t2)*).

  Reserved Notation "G1 'vdash' t1 '<;' t2 'dashv' G2" (at level 80).
  Reserved Notation "G1 'vdash' d1 '<;;' d2 'dashv' G2" (at level 80).
  Reserved Notation "G1 'vdash' d1 '<;;;' d2 'dashv' G2" (at level 80).

  Hint Constructors struct_equiv_type struct_equiv_decl_ty struct_equiv_decl_tys struct_equiv_var.
                                             

  Inductive sub : env -> ty -> ty -> env -> Prop :=
  | s_top : forall G t G', G vdash t <; top dashv G'
  | s_bot : forall G t G', G vdash bot <; t dashv G'
  | s_arr : forall G t1 t2 t1' t2' G', G' vdash t1' <; t1 dashv G ->
                                  t1::G vdash t2 <; t2' dashv t1'::G' ->
                                  G vdash (t1 arr t2) <; (t1' arr t2') dashv G'
  | s_refl : forall G x l G', G vdash (sel x l) <; (sel x l) dashv G'
  | s_lower : forall G x l s t G', G' vdash x ni (type l sup s) ->
                              G vdash t <; s dashv G' ->
                              G vdash t <; (sel x l) dashv G'
  | s_upper : forall G x l u t G', G vdash x ni (type l ext u) ->
                              G vdash u <; t dashv G'->
                              G vdash (sel x l) <; t dashv G'
  | s_struct : forall G ds1 ds2 G', 
                 (str ds1)::G vdash ds1 <;;; ds2 dashv (str ds2)::G'  ->
                 G vdash (str ds1) <; (str ds2) dashv G'
                              
  where "G1 'vdash' t1 '<;' t2 'dashv' G2" := (sub G1 t1 t2 G2)

  with
  sub_d : env -> decl_ty -> decl_ty -> env -> Prop :=
  | sd_lower : forall G l t1 t2 G', G vdash t2 <; t1 dashv G' ->
                               G vdash (type l sup t1) <;; (type l sup t2) dashv G'
  | sd_upper : forall G l t1 t2 G', G vdash t1 <; t2 dashv G' ->
                               G vdash (type l ext t1) <;; (type l ext t2) dashv G'

                              where "G1 'vdash' d1 '<;;' d2 'dashv' G2" := (sub_d G1 d1 d2 G2)

  with
  sub_ds : env -> decl_tys -> decl_tys -> env -> Prop :=
  | sd_nil : forall G G', G vdash dt_nil <;;; dt_nil dashv G'
  | sd_con : forall G d1 ds1 d2 ds2 G', G vdash d1 <;; d2 dashv G' -> 
                                   G vdash ds1 <;;; ds2 dashv G' ->
                                   G vdash (dt_con d1 ds2) <;;; (dt_con d2 ds2) dashv G'

                                     where "G1 'vdash' d1 '<;;;' d2 'dashv' G2" := (sub_ds G1 d1 d2 G2).

  Scheme sub_ty_mutind := Induction for sub Sort Prop
    with sub_decl_ty_mutind := Induction for sub_d Sort Prop
    with sub_decl_tys_mutind := Induction for sub_ds Sort Prop.

  Combined Scheme sub_mutind from sub_ty_mutind, sub_decl_ty_mutind, sub_decl_tys_mutind.

  Hint Constructors sub sub_d sub_ds.

  (*Reserved Notation "G1 'vdash' t1 'equiv_t' t2 'dashv' G2" (at level 80).
  Reserved Notation "G1 'vdash' t1 'equiv_d' t2 'dashv' G2" (at level 80).
  Reserved Notation "G1 'vdash' t1 'equiv_p' t2 'dashv' G2" (at level 80). 

  Inductive ty_eq : env -> ty -> env -> ty -> Prop :=
  | eq_top : forall G1 G2, G1 vdash top equiv_t top dashv G2
  | eq_bot : forall G1 G2, G1 vdash bot equiv_t bot dashv G2
  | eq_sel : forall G1 p1 G2 p2 l, G1 vdash p1 equiv_p p2 dashv G2 ->
                              G2 vdash (sel p1 l) equiv_t (sel p2 l) dashv G2
  | eq_struct : forall G1 d1 d2 G2 d1' d2',
                  (struct d1 d2)::G1 vdash [c_ O /d O] d1 equiv_d [c_ O /d O] d1' dashv (struct d1' d2')::G2 ->
                  (struct d1 d2)::G1 vdash [c_ O /d O] d2 equiv_d [c_ O /d O] d2' dashv (struct d1' d2')::G2 ->
                  G1 vdash (struct d1 d2) equiv_t (struct d1' d2') dashv G2

  where "G1 'vdash' t1 'equiv_t' t2 'dashv' G2" := (ty_eq G1 t1 G2 t2)

  with
  path_eq : env -> path -> env -> var -> Prop :=
  | eq_var : forall G1 t1 G2 t2 n, get n G1 = Some t1 ->
                              get n G2 = Some t2 ->
                              G1 vdash t1 equiv_t t2 dashv G2 ->
                              G1 vdash c_ n equiv_p c_ n dashv G2
  | eq_cast : forall G1 p1 t1 G2 p2 t2, G1 vdash p1 equiv_p p2 dashv G2 ->
                                   G1 vdash t1 equiv_t t2 dashv G2 ->
                                   G1 vdash p1 cast t1 equiv_p p2 cast t2 dashv G2

  where "G1 'vdash' p1 'equiv_p' p2 'dashv' G2" := (path_eq G1 p1 G2 p2)

  with
  decl_eq : env -> decl -> env -> decl -> Prop :=
  | lower_eq : forall G1 t1 G2 t2 l, G1 vdash t1 equiv_t t2 dashv G2 ->
                                G1 vdash (type l sup t1) equiv_d (type l sup t2) dashv G2
  | upper_eq : forall G1 t1 G2 t2 l, G1 vdash t1 equiv_t t2 dashv G2 ->
                                G1 vdash (type l ext t1) equiv_d (type l ext t2) dashv G2

                                   where "G1 'vdash' d1 'equiv_d' d2 'dashv' G2" := (decl_eq G1 d1 G2 d2).

  Hint Constructors ty_eq path_eq decl_eq.

  Scheme ty_eq_mut_ind := Induction for ty_eq Sort Prop
    with decl_eq_mut_ind := Induction for decl_eq Sort Prop
    with path_eq_mut_ind := Induction for path_eq Sort Prop.             

  Combined Scheme ty_eq_mutind from ty_eq_mut_ind, decl_eq_mut_ind, path_eq_mut_ind.*)

  (*Reserved Notation "G1 'equiv_e' G2" (at level 80).
  
  Inductive env_eq : env -> env -> Prop :=
  | eq_nil : nil equiv_e nil
  | eq_cons : forall G1 t1 G2 t2, G1 equiv_e G2 ->
                             G1 vdash t1 equiv_t t2 dashv G2 ->
                             t1::G1 equiv_e t2::G2

                               where "G1 'equiv_e' G2" := (env_eq G1 G2).*)
  
  Lemma get_empty :
    forall n, get n nil = None.
  Proof.
    intro n; induction n as [| n'];
      crush.
  Qed.

  Hint Resolve get_empty.
  Hint Rewrite get_empty.

 (* Lemma get_empty :
    forall n, get n nil = None.
  Proof.
    intro n; induction n as [| n'];
      crush.
  Qed.

  Hint Resolve nth_empty.
  Hint Rewrite nth_empty.*)


  Lemma get_cons :
    forall n G t1 t2, get (S n) (t1::G) = Some t2 ->
                 get n G = Some t2.
  Proof.
    intro n; induction n as [|n']; intros; crush.
  Qed.

  Hint Resolve get_cons.
  Hint Rewrite get_cons.
  

  Lemma get_some_index :
    forall G n t, get n G = Some t ->
             n < length G.
  Proof.
    intro G ; induction G as [|t' G'] ; intros; crush.

    destruct n as [|n']; crush.
    apply gt_n_S.
    apply IHG' with (t:=t); auto.
  Qed.

  (*Lemma get_some_index :
    forall G n t, get n G = Some t ->
             n < length G.
  Proof.
    intros.
    rewrite <- rev_length.
    apply nth_some_index with (t:=t); auto.
  Qed.*)
  
  Lemma get_app :
    forall G G' n t, get n G = Some t ->
                get n (G++G') = Some t.
  Proof.
    intros G; induction G; intros; crush.
    destruct n as [|n']; auto.

    simpl; simpl in H; auto.
  Qed.

  (*Lemma get_app :
    forall G G' n t, get n G = Some t ->
                get n (G'++G) = Some t.
  Proof.
    intros.
    unfold get in H.
    unfold get.
    rewrite rev_app_distr.
    apply nth_app; auto.
  Qed.*)

  Hint Resolve get_app.

  Lemma get_shift :
    forall G' G n, get n G = get (n + (length G')) (G'++G).
  Proof.
    intro G'; induction G' as [|t'' G'']; intros; simpl.

    rewrite <- plus_n_O; auto.

    rewrite <- plus_n_Sm; simpl; auto.
  Qed.

  Hint Rewrite get_shift.
  Hint Resolve get_shift.

  Lemma get_length :
    forall G n t, n = length G -> get n (G++t::nil) = Some t.
  Proof.
    intro G; induction G as [|t' G'];
      intros; crush.
  Qed.

  Hint Resolve get_length.
    
  (*Lemma get_length :
    forall G n t, n = length G -> get n (t::G) = Some t.
  Proof.
    intros; subst.
    unfold get; simpl.
    rewrite <- rev_length; auto.
  Qed.*)

  Lemma get_app_l :
    forall G1 G2 n, n < length G1 ->
               get n (G1++G2) = get n G1.
  Proof.  
    intro G1; induction G1 as [|t' G1']; intros; auto.
    
    simpl in H.
    inversion H.

    simpl in H.
    destruct n as [|n']; crush.
  Qed.

  Hint Resolve get_app_l.

  Lemma get_app_r :
    forall G1 G2 n, n >= length G1 ->
               get n (G1++G2) = get (n - length G1) G2.
  Proof.  
    intro G1; induction G1 as [|t' G1']; intros; simpl; auto.

    rewrite <- minus_n_O; auto.

    destruct n as [|n']; auto.
    unfold ge in H; simpl in H.
    apply le_n_0_eq in H; inversion H.

    unfold ge in H.
    simpl in H; apply le_S_n in H.
    apply (IHG1' G2) in H; auto.
  Qed.

  Hint Resolve get_app_r.

  (*Lemma get_app_r :
    forall G1 G2 n, n < length G2 ->
               get n (G1++G2) = get n G2.
  Proof.
    intros.
    unfold get; rewrite rev_app_distr.
    apply nth_app_l.
    rewrite rev_length; auto.
  Qed.*)

  (*Lemma get_app_l :
    forall G1 G2 n, n >= length G2 ->
               get n (G1++G2) = get (n - length G2) G1.
  Proof.  
    intros; unfold get.
    rewrite rev_app_distr.
    rewrite <- rev_length.
    rewrite <- rev_length in H.
    apply nth_app_r; auto.
  Qed.*)
    
  (*Lemma get_cons :
    forall G t n, n < length G ->
             get n (t::G) = get n G.
  Proof.
    intros;
      assert (Happ : t::G = (t::nil)++G); auto;
        rewrite Happ; apply get_app_r; auto.    
  Qed.*)

  Lemma get_cons_dec :
    forall G n t1 t2, get n (G++(t1::nil)) = Some t2 ->
                 ((n < length G) /\ get n G = Some t2) \/ ((n = length G) /\ t1 = t2).
  Proof.
    intro G; induction G as [|t' G']; intros;
    destruct n as [|n']; simpl; simpl in H.

    inversion H; subst; auto.

    rewrite get_empty in H; inversion H.

    inversion H; subst; left; split; crush.
    
    apply IHG' in H.
    destruct H as [H|H]; destruct H as [Heq Hnth];  [left|right]; split; auto.
    crush.
  Qed.

  Hint Resolve get_cons_dec.

  Lemma get_in :
    forall G n t, get n G = Some t ->
             In t G.
  Proof.
    intro G; induction G as [|t' G']; intros.

    rewrite get_empty in H; inversion H.

    destruct n as [|n'].
    simpl in H; inversion H; subst; crush.
    simpl in H; apply IHG' in H; apply in_cons; auto.
  Qed.
    
(*  Lemma get_cons_dec :
    forall G n t1 t2, get n (t1::G) = Some t2 ->
                 (n < length G /\ get n G = Some t2) \/ (n = length G /\ t1 = t2).
  Proof.
    intros; unfold get; unfold get in H.
    rewrite <- rev_length.
    simpl in H; apply nth_cons_dec; auto.
  Qed.
 *)
  
  (*Lemma get_in :
    forall G n t, get n G = Some t ->
             In t G.
  Proof.
    intros; unfold get in H; apply nth_in in H.
    apply in_rev; auto.
  Qed.
   *)
  
  Lemma get_map :
    forall G n t, get n G = Some t ->
             forall f, get n (map f G) = Some (f t).
  Proof.
    intro G; induction G as [|t' G']; crush.

    destruct n as [|n']; crush.
  Qed.

  

  Lemma rshift_concrete :
    forall n m, ((Var n) rshift_v m) = Var (n - m).
  Proof.
    intros; destruct m as [|m']; simpl; crush.
  Qed.

  Lemma rshift_abstract :
    forall n m, ((Abs n) rshift_v m) = Abs n.
  Proof.
    intros; destruct m as [|m']; simpl; crush.
  Qed.

  Lemma lshift_concrete :
    forall n m, ((Var n) lshift_v m) = Var (n + m).
  Proof.
    intros; destruct m as [|m']; simpl; crush.
  Qed.

  Lemma lshift_abstract :
    forall n m, ((Abs n) lshift_v m) = Abs n.
  Proof.
    intros; destruct m as [|m']; simpl; crush.
  Qed.

  Hint Rewrite rshift_concrete rshift_abstract lshift_concrete lshift_abstract.
  Hint Resolve rshift_concrete rshift_abstract lshift_concrete lshift_abstract.

  Lemma ge_lt_n_var :
    forall x n, ge_var x n -> forall m, m < n -> ge_var x m.
  Proof.
    intros; destruct x as [r|r]; crush.
    inversion H;
    apply ge_concrete; crush.
  Qed.

  Hint Rewrite ge_lt_n_var.
  Hint Resolve ge_lt_n_var.

  Lemma ge_lt_n_mutind :
    (forall t n, ge_type t n -> forall m, m < n -> ge_type t m) /\
    (forall d n, ge_decl_ty d n -> forall m, m < n -> ge_decl_ty d m) /\
    (forall ds n, ge_decl_tys ds n -> forall m, m < n -> ge_decl_tys ds m).
  Proof.
    apply ge_mutind; crush.
    inversion g; crush.
  Qed.

  Lemma ge_lt_n_type :
    (forall t n, ge_type t n -> forall m, m < n -> ge_type t m).
  Proof.
    destruct ge_lt_n_mutind; crush.
  Qed.

  Lemma ge_lt_n_decl_ty :
    (forall d n, ge_decl_ty d n -> forall m, m < n -> ge_decl_ty d m).
  Proof.
    destruct ge_lt_n_mutind; crush.
  Qed.

  Lemma ge_lt_n_decl_tys :
    (forall ds n, ge_decl_tys ds n -> forall m, m < n -> ge_decl_tys ds m).
  Proof.
    destruct ge_lt_n_mutind; crush.
  Qed.

  Hint Resolve ge_lt_n_type ge_lt_n_decl_ty ge_lt_n_decl_tys.
  Hint Rewrite ge_lt_n_type ge_lt_n_decl_ty ge_lt_n_decl_tys.

  Lemma ge_notin_Sn_var :
    forall v n, ge_var v n ->
           n notin_v v ->
           ge_var v (S n).
  Proof.
    intros.
    inversion H; inversion H0; crush.
  Qed.

  Hint Rewrite ge_notin_Sn_var.
  Hint Resolve ge_notin_Sn_var.

  Lemma ge_notin_Sn_mutind :
    (forall t n, ge_type t n ->
            n notin_t t ->
            ge_type t (S n)) /\
    (forall d n, ge_decl_ty d n ->
            n notin_dt d ->
            ge_decl_ty d (S n)) /\
    (forall ds n, ge_decl_tys ds n ->
            n notin_dts ds ->
            ge_decl_tys ds (S n)).
  Proof.
    apply type_mutind; intros; auto.

    inversion H0; inversion H1; subst; crush.

    inversion H; inversion H0; subst; crush.

    inversion H1; inversion H2; subst; crush.

    inversion H0; inversion H1; subst; crush.

    inversion H0; inversion H1; crush.

    inversion H0; inversion H1; crush.

    inversion H1; inversion H2; crush.

  Qed.

  Lemma ge_notin_Sn_type :
    (forall t n, ge_type t n ->
            n notin_t t ->
            ge_type t (S n)).
  Proof.
    destruct ge_notin_Sn_mutind; crush.
  Qed.

  Lemma ge_notin_Sn_decl_ty :
    (forall d n, ge_decl_ty d n ->
            n notin_dt d ->
            ge_decl_ty d (S n)).
  Proof.
    destruct ge_notin_Sn_mutind; crush.
  Qed.

  Lemma ge_notin_Sn_decl_tys :
    (forall ds n, ge_decl_tys ds n ->
            n notin_dts ds ->
            ge_decl_tys ds (S n)).
  Proof.
    destruct ge_notin_Sn_mutind; crush.
  Qed.

  Hint Resolve ge_notin_Sn_type ge_notin_Sn_decl_ty ge_notin_Sn_decl_tys.
  Hint Rewrite ge_notin_Sn_type ge_notin_Sn_decl_ty ge_notin_Sn_decl_tys.

  Lemma ge_implies_notin_var :
    forall v n, ge_var v n ->
           forall m, m < n ->
                m notin_v v.
  Proof.
    intros.
    inversion H; crush.
    apply ni_con; crush.
    apply ni_abs.
  Qed.

  Hint Rewrite ge_implies_notin_var.
  Hint Resolve ge_implies_notin_var.

  Lemma ge_implies_notin_mutind :
    (forall t n, ge_type t n ->
            forall m, m < n ->
                 m notin_t t) /\
    (forall d n, ge_decl_ty d n ->
            forall m, m < n ->
                 m notin_dt d) /\
    (forall ds n, ge_decl_tys ds n ->
            forall m, m < n ->
                 m notin_dts ds).
  Proof.
    apply ge_mutind; crush.
    apply ni_sel.
    apply ge_implies_notin_var with (n := n); auto.
  Qed.

  Lemma ge_implies_notin_type :
    (forall t n, ge_type t n ->
            forall m, m < n ->
                 m notin_t t).
  Proof.
    destruct ge_implies_notin_mutind; crush.
  Qed.

  Lemma ge_implies_notin_decl_ty :
    (forall d n, ge_decl_ty d n ->
            forall m, m < n ->
                 m notin_dt d).
  Proof.
    destruct ge_implies_notin_mutind; crush.
  Qed.

  Lemma ge_implies_notin_decl_tys :
    (forall ds n, ge_decl_tys ds n ->
            forall m, m < n ->
                 m notin_dts ds).
  Proof.
    destruct ge_implies_notin_mutind; crush.
  Qed.

  Hint Resolve ge_implies_notin_type ge_implies_notin_decl_ty ge_implies_notin_decl_tys.
  Hint Rewrite ge_implies_notin_type ge_implies_notin_decl_ty ge_implies_notin_decl_tys.

  Lemma ge_shift_var :
    forall v n, ge_var v n -> forall m, ge_var (v lshift_v m) n.
  Proof.
    intros; inversion H; crush.
  Qed.
  
  Lemma ge_shift_mutind :
    (forall t n, ge_type t n -> forall m, ge_type (t lshift_t m) n) /\
    (forall d n, ge_decl_ty d n -> forall m, ge_decl_ty (d lshift_dt m) n) /\
    (forall ds n, ge_decl_tys ds n -> forall m, ge_decl_tys (ds lshift_dts m) n).
  Proof.
    apply ge_mutind; crush.
    apply ge_sel.
    apply ge_shift_var; auto.
  Qed.

  Lemma ge_shift_type :
    (forall t n, ge_type t n -> forall m, ge_type (t lshift_t m) n).
  Proof.
    destruct ge_shift_mutind; crush.
  Qed.

  Lemma ge_shift_decl_ty :
    (forall d n, ge_decl_ty d n -> forall m, ge_decl_ty (d lshift_dt m) n).
  Proof.
    destruct ge_shift_mutind; crush.
  Qed.

  Lemma ge_shift_decl_tys :
    (forall ds n, ge_decl_tys ds n -> forall m, ge_decl_tys (ds lshift_dts m) n).
  Proof.
    destruct ge_shift_mutind; crush.
  Qed.

  Hint Rewrite ge_shift_type ge_shift_decl_ty ge_shift_decl_tys.
  Hint Resolve ge_shift_type ge_shift_decl_ty ge_shift_decl_tys.
  
  Lemma shift_var_add :
    forall x n m, (x rshift_v n rshift_v m) = (x rshift_v (n + m)).
  Proof.
    intros; destruct x as [n'|n']; destruct n; destruct m; crush.    
  Qed.

  Hint Resolve shift_var_add.
    
  Lemma rshift_assoc_mutind :
    (forall t n m, (t rshift_t n rshift_t m) = (t rshift_t (n + m))) /\
    (forall d n m, (d rshift_dt n rshift_dt m) = (d rshift_dt (n + m))) /\
    (forall ds n m, (ds rshift_dts n rshift_dts m) = (ds rshift_dts (n + m))).
  Proof.
    apply type_mutind; intros; crush.
    rewrite shift_var_add; auto.
  Qed.

  Lemma rshift_assoc_type :
    (forall t n m, (t rshift_t n rshift_t m) = (t rshift_t (n + m))).
  Proof.
    destruct rshift_assoc_mutind; auto.
  Qed.
    
  Lemma rshift_assoc_decl_ty :
    (forall d n m, (d rshift_dt n rshift_dt m) = (d rshift_dt (n + m))).
  Proof.
    destruct rshift_assoc_mutind; crush.
  Qed.
    
  Lemma rshift_assoc_decl_tys :
    (forall p n m, (p rshift_dts n rshift_dts m) = (p rshift_dts (n + m))).
  Proof.
    destruct rshift_assoc_mutind; crush.
  Qed.
    
  Hint Resolve rshift_assoc_type rshift_assoc_decl_ty rshift_assoc_decl_tys.
  Hint Rewrite rshift_assoc_type rshift_assoc_decl_ty rshift_assoc_decl_tys.

  Lemma le_minus_plus :
    forall r n m, n <= r -> r - n + m = r + m - n.
  Proof.
    intro r; induction r as [|r']; crush.

    destruct n as [|n']; auto.

    rewrite IHr'; crush.
  Qed.

  Lemma lt_minus :
    forall m n p, m <= n ->
             n < p + m ->
             n - m < p.
  Proof.
    intro m; induction m as [|m']; intros; crush.
  Qed.

  Lemma rlshift_var :
    forall v n m, ge_var v n -> (v rshift_v n lshift_v m) = (v lshift_v m rshift_v n).
  Proof.
    intros.
    inversion H; crush.
  Qed.
            
  Lemma rlshift_mutind :
    (forall t n m, ge_type t n -> (t rshift_t n lshift_t m) = (t lshift_t m rshift_t n)) /\
    (forall d n m, ge_decl_ty d n -> (d rshift_dt n lshift_dt m) = (d lshift_dt m rshift_dt n)) /\
    (forall ds n m, ge_decl_tys ds n -> (ds rshift_dts n lshift_dts m) = (ds lshift_dts m rshift_dts n)).
  Proof.
    apply type_mutind; crush.

    rewrite H; auto;
    inversion H0; subst.
    apply ge_lt_n_decl_tys with (n:=S n); auto.

    inversion H; subst.
    rewrite rlshift_var; auto.

    inversion H1; subst.
    rewrite H, H0; crush.
    apply ge_lt_n_type with (n:= S n); auto. 

    inversion H0; subst.
    rewrite H; crush.

    inversion H0; subst.
    rewrite H; crush.

    inversion H0; subst.
    rewrite H; crush.
    
    inversion H1; subst.
    rewrite H; auto; rewrite H0; auto.
  Qed.

            
  Lemma rlshift_type :
    (forall t n m, ge_type t n -> (t rshift_t n lshift_t m) = (t lshift_t m rshift_t n)).
  Proof.
    destruct rlshift_mutind; crush.
  Qed.
            
  Lemma rlshift_decl_ty :
    (forall d n m, ge_decl_ty d n -> (d rshift_dt n lshift_dt m) = (d lshift_dt m rshift_dt n)).
  Proof.
    destruct rlshift_mutind; crush.
  Qed.
            
  Lemma rlshift_decl_tys :
    (forall ds n m, ge_decl_tys ds n -> (ds rshift_dts n lshift_dts m) = (ds lshift_dts m rshift_dts n)).
  Proof.
    destruct rlshift_mutind; crush.
  Qed.

  Hint Rewrite rlshift_type rlshift_decl_ty rlshift_decl_tys. 
  Hint Resolve rlshift_type rlshift_decl_ty rlshift_decl_tys.

  Lemma lrshift_n_mutind :
    (forall t n, (t lshift_t n rshift_t n) = t) /\
    (forall d n, (d lshift_dt n rshift_dt n) = d) /\
    (forall ds n, (ds lshift_dts n rshift_dts n) = ds).
  Proof.
    apply type_mutind; crush.
    destruct v as [r|r]; crush.
    rewrite <- Nat.add_sub_assoc; auto.
    assert (Htemp : n - n = 0); [crush|rewrite Htemp; rewrite <- plus_n_O; auto].
  Qed.

  Lemma lrshift_n_type :
    (forall t n, (t lshift_t n rshift_t n) = t).
  Proof.
    destruct lrshift_n_mutind; crush.
  Qed.

  Lemma lrshift_n_decl_tys :
    (forall d n, (d lshift_dt n rshift_dt n) = d).
  Proof.
    destruct lrshift_n_mutind; crush.
  Qed.

  Lemma lrshift_n_path :
    (forall ds n, (ds lshift_dts n rshift_dts n) = ds).
  Proof.
    destruct lrshift_n_mutind; crush.
  Qed.
  
  (*Lemma typing_weakening  :
    forall G p t, G vdash p hasType t ->
             forall G', G'++G vdash (p rshift_p (length G')) hasType (t rshift_t (length G')).
  Proof.
    intros G p t Htyp;
    induction Htyp; intros; crush.

    rewrite shift_add_type.
    apply t_var.

    rewrite <- get_shift; auto.
  Qed.
  
  Hint Resolve typing_weakening.*)
   

  Lemma shift_comm_mutind :
    (forall t n m, (t rshift_t n rshift_t m) = (t rshift_t m rshift_t n)) /\
    (forall d n m, (d rshift_dt n rshift_dt m) = (d rshift_dt m rshift_dt n)) /\
    (forall p n m, (p rshift_dts n rshift_dts m) = (p rshift_dts m rshift_dts n)).

  Proof.
    apply type_mutind; crush.

    rewrite shift_var_add, shift_var_add, plus_comm; auto.
  Qed.

  Lemma shift_comm_type :
    (forall t n m, (t rshift_t n rshift_t m) = (t rshift_t m rshift_t n)).
  Proof.
    destruct shift_comm_mutind; crush.
  Qed.

  Lemma shift_comm_decl_ty :
    (forall d n m, (d rshift_dt n rshift_dt m) = (d rshift_dt m rshift_dt n)).
  Proof.
    destruct shift_comm_mutind; crush.
  Qed.

  Lemma shift_comm_decl_tys :
    (forall ds n m, (ds rshift_dts n rshift_dts m) = (ds rshift_dts m rshift_dts n)).
  Proof.
    destruct shift_comm_mutind; crush.
  Qed.
      
  Hint Resolve shift_comm_decl_tys shift_comm_type shift_comm_decl_ty.

  Lemma rshift_subst_var :
    forall  y x n m, ge_var x m -> ([x /v n] y rshift_v m) = [x rshift_v m /v n] (y rshift_v m).
  Proof.
    intros; destruct y; crush.
    destruct (eq_nat_dec n n0); subst;
    [rewrite <- beq_nat_refl; auto|
     rewrite <- Nat.eqb_neq in n1;
       rewrite n1].
    crush.
  Qed.
    
  Lemma rshift_subst_mutind :
    (forall t x n m, ge_var x m -> ([x /t n] t rshift_t m) = [x rshift_v m /t n] (t rshift_t m)) /\
    (forall d x n m, ge_var x m -> ([x /dt n] d rshift_dt m) = [x rshift_v m /dt n] (d rshift_dt m)) /\
    (forall ds x n m, ge_var x m -> ([x /dts n] ds rshift_dts m) = [x rshift_v m /dts n] (ds rshift_dts m)).
  Proof.
    apply type_mutind; intros; crush.

    
    destruct x; [|crush]. 
    rewrite H.
    rewrite rshift_concrete.
    rewrite rshift_concrete.
    inversion H0; subst.
    rewrite minus_Sn_m; auto.
    inversion H0; crush.

    rewrite rshift_subst_var; auto.
  Qed.
    
  Lemma shift_subst_type :
    (forall t x n m, ge_var x m -> ([x /t n] t rshift_t m) = [x rshift_v m /t n] (t rshift_t m)).
  Proof.
    destruct rshift_subst_mutind; crush.
  Qed.
    
  Lemma shift_subst_decl_ty :
    (forall d x n m, ge_var x m -> ([x /dt n] d rshift_dt m) = [x rshift_v m /dt n] (d rshift_dt m)).
  Proof.
    destruct rshift_subst_mutind; crush.
  Qed.
    
  Lemma shift_subst_decl_tys :
    (forall ds x n m, ge_var x m -> ([x /dts n] ds rshift_dts m) = [x rshift_v m /dts n] (ds rshift_dts m)).
  Proof.
    destruct rshift_subst_mutind; crush.
  Qed.
  
(*  
  Lemma shift_typing :
    forall G p t, G vdash p hasType t ->
             forall G1 G2 t', G = G1++t'::G2 ->
                         (t' shift_t length G1)::(dec_env (length G2) G1)++G2 vdash 
   
*)
  
  (*Lemma has_contains_weakening_mutind :
    (forall G p d, G vdash p ni d ->
              (forall G', G'++G vdash (p rshift_p length G') ni (d rshift_d length G'))) /\
    (forall G t d, G vdash d cont t ->
              (forall G', G'++G vdash (d rshift_d length G') cont (t rshift_t length G'))).
  Proof.
    apply has_contains_mutind; crush.

    rewrite shift_subst_decl. apply h_path with (t:=t rshift_t length G'); auto.

    apply c_select with (l':=l')(t:=t rshift_t length G'); auto.
  Qed.


  Lemma has_weakening :
    (forall G p d, G vdash p ni d ->
              (forall G', G'++G vdash (p rshift_p length G') ni (d rshift_d length G'))).
  Proof.
    destruct has_contains_weakening_mutind; auto.
  Qed.

  Lemma contains_weakening :
    (forall G t d, G vdash d cont t ->
              (forall G', G'++G vdash (d rshift_d length G') cont (t rshift_t length G'))).
  Proof.
    destruct has_contains_weakening_mutind; auto.
  Qed.
    
  Hint Resolve has_weakening contains_weakening.*)

  Lemma ljump_concrete :
    forall m n i, ((Var m) [i] ljump_v n) = Var (m [i] ljump_n n).
  Proof.
    intros; unfold left_jump_v; destruct i; destruct n; crush.
  Qed.

  (*Lemma rjump_concrete :
    forall m n i, ((Var m) [i] rjump_dts n) = Var (m [i] rjump_n n).
  Proof.
    intros; unfold right_jump_v; destruct i; destruct n; crush.
  Qed.*)

  Lemma ljump_abstract :
    forall m n i, ((Abs m) [i] ljump_v n) = Abs m.
  Proof.
    intros; unfold left_jump_v; destruct i; destruct n; crush.
  Qed.

  (*Lemma rjump_abstract :
    forall m n i, ((Abs m) [i] rjump_v n) = Abs m.
  Proof.
    intros; unfold right_jump_v; destruct i; destruct n; crush.
  Qed.*)

  Hint Resolve ljump_concrete (*rjump_concrete*) ljump_abstract (*rjump_abstract*).
  Hint Rewrite ljump_concrete (*rjump_concrete*) ljump_abstract (*rjump_abstract*).  

  (*Lemma right_jump_left_jump_nat :
    forall r n i, ((r [i] ljump_n n) [i] rjump_n n) = r.
  Proof.
    intros; crush.
    unfold left_jump_n;
      unfold right_jump_n.

    destruct i as [i'|]; crush.
    destruct (lt_dec r i') as [Hlt1|Hlet1];
      [destruct (Nat.ltb_lt r i') as [Htemp Hltb1]; clear Htemp|
       destruct (Nat.ltb_nlt r i') as [Htemp Hltb1]; clear Htemp];
    rewrite Hltb1; auto.

    rewrite Hltb1; auto.
    destruct (Nat.ltb_nlt (r + n) i') as [Htemp Hltb2]; clear Htemp;
      rewrite Hltb2; crush.
  Qed.
  
  Hint Resolve right_jump_left_jump_nat.
  Hint Rewrite right_jump_left_jump_nat.*)

  (*Lemma right_jump_left_jump_var :
    forall x n i, ((x [i] ljump_v n) [i] rjump_v n) = x.
  Proof.
    intros;
    destruct x; crush.
  Qed.

  Hint Resolve right_jump_left_jump_var.
  Hint Rewrite right_jump_left_jump_var.*)

  Lemma l_jump_None :
    forall r n, (r [None] ljump_n n) = r.
  Proof.
    intros; crush.
  Qed.

  (*Lemma r_jump_None :
    forall r n, (r [None] rjump_n n) = r.
  Proof.
    intros; crush.
  Qed.*)

  Hint Rewrite l_jump_None (*r_jump_None*).
  Hint Resolve l_jump_None (*r_jump_None*).

  Lemma l_jump_None_var :
    forall x n, (x [None] ljump_v n) = x.
  Proof.
    intros; crush.
    destruct x as [m|m]; simpl; auto.
  Qed.

  Hint Rewrite l_jump_None_var.
  Hint Resolve l_jump_None_var.

  Lemma l_jump_None_mutind :
    (forall t n, (t [None] ljump_t n) = t) /\
    (forall d n, (d [None] ljump_dt n) = d) /\
    (forall ds n, (ds [None] ljump_dts n) = ds).
  Proof.
    apply type_mutind; intros; crush.
  Qed.

  Lemma l_jump_None_type :
    (forall t n, (t [None] ljump_t n) = t).
  Proof.
    destruct l_jump_None_mutind; crush.
  Qed.

  Lemma l_jump_None_decl_ty :
    (forall d n, (d [None] ljump_dt n) = d).
  Proof.
    destruct l_jump_None_mutind; crush.
  Qed.

  Lemma l_jump_None_decl_tys :
    (forall ds n, (ds [None] ljump_dts n) = ds).
  Proof.
    destruct l_jump_None_mutind; crush.
  Qed.

  Hint Rewrite l_jump_None_type l_jump_None_decl_ty l_jump_None_decl_tys.
  Hint Resolve l_jump_None_type l_jump_None_decl_ty l_jump_None_decl_tys.

  (*Lemma r_jump_None_var :
    forall x n, (x [None] rjump_v n) = x.
  Proof.
    intros; crush.
    destruct x as [m|m]; simpl; auto.
  Qed.

  Hint Rewrite r_jump_None_var.
  Hint Resolve r_jump_None_var.*)

  (*Lemma r_jump_None_mutind :
    (forall t n, (t [None] rjump_t n) = t) /\
    (forall d n, (d [None] rjump_d n) = d) /\
    (forall p n, (p [None] rjump_p n) = p).
  Proof.
    apply type_mutind; intros; crush.
  Qed.

  Lemma r_jump_None_type :
    (forall t n, (t [None] rjump_t n) = t).
  Proof.
    destruct r_jump_None_mutind; crush.
  Qed.

  Lemma r_jump_None_decl :
    (forall d n, (d [None] rjump_d n) = d).
  Proof.
    destruct r_jump_None_mutind; crush.
  Qed.

  Lemma r_jump_None_path :
    (forall p n, (p [None] rjump_p n) = p).
  Proof.
    destruct r_jump_None_mutind; crush.
  Qed.

  Hint Rewrite r_jump_None_type r_jump_None_decl r_jump_None_path.
  Hint Resolve r_jump_None_type r_jump_None_decl r_jump_None_path.*)

  Lemma l_jump_None_env :
    forall G n, (G [None] ljump_e n) = G.
  Proof.
    intro G; induction G as [|t' G']; intros; crush.
  Qed.

  (*Lemma r_jump_None_env :
    forall G n, (G [None] rjump_e n) = G.
  Proof.
    intro G; induction G as [|t' G']; intros; crush.
  Qed.*)

  Hint Rewrite l_jump_None_env (*r_jump_None_env*).
  Hint Resolve l_jump_None_env (*r_jump_None_env*).


  (*Lemma l_r_jump_inv_mutind :
    (forall t n i, ((t [i] ljump_t n) [i] rjump_t n) = t) /\
    (forall d n i, ((d [i] ljump_d n) [i] rjump_d n) = d) /\
    (forall p n i, ((p [i] ljump_p n) [i] rjump_p n) = p).
  Proof.
    apply type_mutind; intros; crush.
  Qed.

  Lemma l_r_jump_inv_type :
    (forall t n i, ((t [i] ljump_t n) [i] rjump_t n) = t).
  Proof.
    destruct l_r_jump_inv_mutind; crush.
  Qed.

  Lemma l_r_jump_inv_decl :
    (forall d n i, ((d [i] ljump_d n) [i] rjump_d n) = d).
  Proof.
    destruct l_r_jump_inv_mutind; crush.
  Qed.

  Lemma l_r_jump_inv_path :
    (forall p n i, ((p [i] ljump_p n) [i] rjump_p n) = p).
  Proof.
    destruct l_r_jump_inv_mutind; crush.
  Qed.

  Lemma l_r_jump_inv_env :
    forall G n i, ((G [i] ljump_e n) [i] rjump_e n) = G.
  Proof.
    intro G; induction G as [|t' G']; intros; auto.

    simpl;
      rewrite l_r_jump_inv_type;
      rewrite IHG'; auto.
  Qed.*)

  (*inc and dec of optional naturals*)

  Lemma inc_O :
    forall i, inc i 0 = i.
  Proof.
    destruct i; crush.
  Qed.

  Lemma dec_O :
    forall i, dec i 0 = i.
  Proof.
    destruct i; crush.    
  Qed.

  Hint Resolve inc_O dec_O.
  Hint Rewrite inc_O dec_O.

  Lemma dec_add :
    forall i n m, dec (dec i n) m = dec i (n + m).
  Proof.
    intros i n;
    destruct i as [i'|];
    [intros; simpl; destruct (lt_dec i' n) as [Hlt|Hlt]|crush].

    destruct (Nat.ltb_lt i' n) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; auto.
    destruct (Nat.ltb_lt i' (n + m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; crush.

    destruct (Nat.ltb_nlt i' n) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; auto; simpl.
    destruct (lt_dec (i' - n) m) as [Hlt2|Hlt2].
    destruct (Nat.ltb_lt i' (n + m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    destruct (Nat.ltb_lt (i' - n) m) as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; crush.
    
    destruct (Nat.ltb_nlt i' (n + m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    destruct (Nat.ltb_nlt (i' - n) m) as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; crush.    
  Qed.

  Lemma inc_add :
    forall i n m, inc (inc i n) m = inc i (n + m).
  Proof.
    intro i; destruct i as [i'|]; crush.
  Qed.

  Hint Resolve inc_add dec_add.
  Hint Rewrite inc_add dec_add.

  Lemma dec_inc_n :
    forall i n, dec (inc i n) n = i.
  Proof.
    intro i; destruct i as [i'|]; crush.

    destruct (Nat.ltb_nlt (i' + n) n) as [Htemp Hltb]; clear Htemp;
      rewrite Hltb; crush.
  Qed.

  Hint Rewrite dec_inc_n.
  Hint Resolve dec_inc_n.

    
  (*------------------------------------------------*)

  Lemma ljump_app :
    forall G1 G2 i m, ((G1 ++ G2) [i] ljump_e m) = (G1 [i] ljump_e m) ++ (G2 [dec i  (length G1)] ljump_e m).
  Proof.
    intro G1; induction G1 as [|t G1']; intros; [crush|].
    simpl.
    rewrite IHG1'; simpl.
    destruct i as [i'|]; crush.
    destruct (lt_dec i' 1) as [Hlt1|Hlt1];
      [destruct (Nat.ltb_lt i' 1) as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1|
       destruct (Nat.ltb_nlt i' 1) as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1]; crush.
    destruct (Nat.ltb_lt i' (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
      rewrite Hltb2; crush.
    destruct (lt_dec i' (S (length G1'))) as [Hlt2|Hlt2].
    destruct (Nat.ltb_lt i' (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
      rewrite Hltb2; auto.
    destruct (Nat.ltb_lt (i' - 1) (length G1')) as [Htemp Hltb3]; clear Htemp;
      rewrite Hltb3; crush.

    destruct (Nat.ltb_nlt i' (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
      rewrite Hltb2; auto.
    destruct (Nat.ltb_nlt (i' - 1) (length G1')) as [Htemp Hltb3]; clear Htemp;
      rewrite Hltb3; crush.
    rewrite <- Nat.sub_add_distr; crush.
  Qed.

  Lemma ljump_inc_n :
    forall i r n, ((S r) [inc i 1] ljump_n n) = S (r [i] ljump_n n).
  Proof.
    intro i; destruct i as [i'|]; crush.
    destruct (lt_dec r i') as [Hlt1|Hlt1];
      [destruct (Nat.ltb_lt r i') as [Htemp Hltb1]; clear Htemp;
       destruct (Nat.ltb_lt (S r) (i' + 1)) as [Htemp Hltb2]; clear Htemp;
       rewrite Hltb1; auto;
       rewrite Hltb2; crush|
      destruct (Nat.ltb_nlt r i') as [Htemp Hltb1]; clear Htemp;
       destruct (Nat.ltb_nlt (S r) (i' + 1)) as [Htemp Hltb2]; clear Htemp;
       rewrite Hltb1; auto;
       rewrite Hltb2; crush].
Qed.    
  
  Lemma get_ljump :
    forall G1 G2 G r, get r (G1 ++ G2) = get (r [Some (length G1)] ljump_n (length G)) (G1 ++ G ++ G2).
  Proof.
    intro G1; induction G1 as [|t' G1']; intros; simpl; auto.

    destruct r as [|r']; crush.
    rewrite IHG1' with (G:=G).
    destruct (lt_dec r' (length G1')) as [Hlt1|Hlt1];
      [destruct (Nat.ltb_lt r' (length G1')) as [Htemp Hltb1]; clear Htemp;
       destruct (Nat.ltb_lt (S r') (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
       rewrite Hltb1, Hltb2; crush|
       destruct (Nat.ltb_nlt r' (length G1')) as [Htemp Hltb1]; clear Htemp;
       destruct (Nat.ltb_nlt (S r') (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
       rewrite Hltb1, Hltb2; crush].
  Qed.
  
  Lemma get_dec :
    forall G n, {n < length G /\ exists t, get n G = Some t} + {n >= length G /\ get n G = None}.
  Proof.
    intro G; induction G as [|t' G']; intros; [crush|].

    destruct n as [|n'];
      [left; crush; exists t'; auto|simpl].

    destruct (IHG' n') as [Hdec|Hdec];
      [left|right]; crush.
  Qed.

  Lemma get_some_app :
    forall G1 G2 n, {(n < length G1) /\ get n (G1 ++ G2) = get n G1} +
               {n >= length G1 /\ get n (G1 ++ G2) = get (n - length G1) G2}.
  Proof.
    intro G1; induction G1 as [|t' G1']; intros; simpl;
    [right; split;
     [| rewrite <- minus_n_O]; crush|].

    destruct n as [|n'];
      [crush|destruct (IHG1' G2 n') as [Hdec|Hdec]; crush].
  Qed.

  Lemma dec_S_S :
    forall i n, dec (Some (S i)) (S n) = dec (Some i) n.
  Proof.
    intros; crush.
  Qed.

  Hint Rewrite dec_S_S.
  Hint Resolve dec_S_S.

  Lemma get_ljump_alt :
    forall G1 G2 n t, get n (G1 ++ G2) = Some t ->
                 forall G i m, m = length G ->
                          i = Some (length G1) ->
                          get (n [i] ljump_n m) ((G1 [dec i  1] ljump_e m) ++ G ++ G2) = Some (t [dec i (S n)] ljump_t m).
  Proof.
    intro G1; induction G1 as [|t' G1']; intros; subst.
    simpl; rewrite <- get_shift; crush.

    destruct n as [|n'].
    simpl; rewrite <- minus_n_O; auto.
    simpl in H; inversion H; subst; auto.

    assert (Hleng : length (t'::G1') = S (length G1'));
      [auto|rewrite Hleng; clear Hleng].
    rewrite dec_S_S, dec_S_S.
    rewrite <- (IHG1' G2) with (G:=G)(n:=n'); simpl; auto.
    rewrite <- minus_n_O.
    destruct (lt_dec n' (length G1')) as [Hlt1|Hlt1];
      [destruct (Nat.ltb_lt n' (length G1')) as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1; auto;
       destruct (Nat.ltb_lt (S n') (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
       rewrite Hltb2|
       destruct (Nat.ltb_nlt n' (length G1')) as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1; auto;
       destruct (Nat.ltb_nlt (S n') (S (length G1'))) as [Htemp Hltb2]; clear Htemp;
       rewrite Hltb2]; crush.
  Qed.

  Lemma ljump_lshift_var :
    forall v n i m, ((v lshift_v (S m)) [i] ljump_v n) = ((v [dec i (S m)] ljump_v n) lshift_v (S (m [i] ljump_n n))).
  Proof.
    intros; crush.
    destruct v as [r|r]; crush.

    destruct i as [i'|]; auto.

    simpl.
    destruct (lt_dec m i') as [Hlt1|Hlt1];
      [destruct (Nat.ltb_lt m i') as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1; [|auto]|
       destruct (Nat.ltb_nlt m i') as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1; [|auto]]; simpl.
    destruct (Nat.ltb_nlt i' (S m)) as [Htemp Hltb2]; clear Htemp;
      rewrite Hltb2; [|crush].
    simpl.
    destruct (lt_dec (S (m + r)) i') as [Hlt2|Hlt2].
    destruct (Nat.ltb_lt (S (m + r)) i') as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; [|auto].
    destruct (Nat.ltb_lt r (i' - S m)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; crush.

    destruct (Nat.ltb_nlt (S (m + r)) i') as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; [|auto].
    destruct (Nat.ltb_nlt r (i' - S m)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; crush.

    destruct (Nat.ltb_lt i' (S m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    simpl.

    destruct (Nat.ltb_nlt (S (m + r)) i') as [Htemp Hltb3]; clear Htemp;
      rewrite Hltb3; crush.    
  Qed.

  Hint Rewrite ljump_lshift_var.
  Hint Resolve ljump_lshift_var.


  Lemma ljump_rshift_var :
    forall v n i m, ge_var v m -> ((v rshift_v (m)) [i] ljump_v n) = ((v [inc i (m)] ljump_v n) rshift_v m).
  Proof.
    intros; crush.
    destruct v as [r|r]; crush.

    destruct i as [i'|]; auto.

    simpl.

    destruct (lt_dec (r - m) i') as [Hlt|Hlt].
    destruct (Nat.ltb_lt (r - m) i') as [Htemp Hltb1]; clear Htemp;
      rewrite Hltb1; auto.
    destruct (Nat.ltb_lt r (i' + m)) as [Htemp Hltb2]; clear Htemp;
      rewrite Hltb2; crush.

    destruct (Nat.ltb_nlt (r - m) i') as [Htemp Hltb1]; clear Htemp;
      rewrite Hltb1; auto.
    destruct (Nat.ltb_nlt r (i' + m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2.
    inversion H; subst; rewrite le_minus_plus; auto.

    inversion H; subst; intro Hcontra.
    apply lt_minus in Hcontra; auto.
  Qed.

  Lemma ljump_rshift_mutind :
    (forall t n i m, ge_type t m -> ((t rshift_t m) [i] ljump_t n) = ((t [inc i m] ljump_t n) rshift_t m)) /\
    (forall d n i m, ge_decl_ty d m -> ((d rshift_dt m) [i] ljump_dt n) = ((d [inc i m] ljump_dt n) rshift_dt m)) /\
    (forall ds n i m, ge_decl_tys ds m -> ((ds rshift_dts m) [i] ljump_dts n) = ((ds [inc i m] ljump_dts n) rshift_dts m)).
  Proof.
    apply type_mutind; intros; auto.

    simpl.
    rewrite H;
      [rewrite inc_add;
        rewrite inc_add;
        rewrite Nat.add_comm; auto|
       inversion H0; subst].
    apply ge_lt_n_decl_tys with (n:=S m); auto.

    simpl; rewrite ljump_rshift_var; auto.
    inversion H; auto.

    simpl; rewrite H, H0; 
    [rewrite inc_add, inc_add;
      rewrite plus_comm; auto| |];
    inversion H1; subst; crush.
    apply ge_lt_n_type with (n:=S m); auto.

    simpl; rewrite H;
    inversion H0; subst; crush.

    simpl; rewrite H;
    inversion H0; subst; crush.

    simpl; rewrite H;
    inversion H0; subst; crush.

    simpl; rewrite H, H0;
    inversion H1; subst; crush.
  Qed.

  Lemma ljump_rshift_type :
    (forall t n i m, ge_type t m -> ((t rshift_t m) [i] ljump_t n) = ((t [inc i m] ljump_t n) rshift_t m)).
  Proof.
    destruct ljump_rshift_mutind; crush.
  Qed.

  Lemma ljump_rshift_decl_ty :
    (forall d n i m, ge_decl_ty d m -> ((d rshift_dt m) [i] ljump_dt n) = ((d [inc i m] ljump_dt n) rshift_dt m)).
  Proof.
    destruct ljump_rshift_mutind; crush.
  Qed.

  Lemma ljump_rshift_decl_tys :
    (forall ds n i m, ge_decl_tys ds m -> ((ds rshift_dts m) [i] ljump_dts n) = ((ds [inc i m] ljump_dts n) rshift_dts m)).
  Proof.
    destruct ljump_rshift_mutind; crush.
  Qed.

  Lemma ge_n_implies_jump_shift_var :
    forall x i m, ge_var x i -> (x [Some i] ljump_v m) = (x lshift_v m).
  Proof.
    intros.
    inversion H; subst; [|crush].
    simpl.
    destruct (Nat.ltb_nlt r i) as [Htemp Hltb]; clear Htemp;
    rewrite Hltb; [|crush]; auto.
  Qed.
    
  
  Lemma ge_n_implies_jump_shift :
    (forall t i m, ge_type t i -> (t [Some i] ljump_t m) = (t lshift_t m)) /\
    (forall d i m, ge_decl_ty d i -> (d [Some i] ljump_dt m) = (d lshift_dt m)) /\
    (forall ds i m, ge_decl_tys ds i -> (ds [Some i] ljump_dts m) = (ds lshift_dts m)).
  Proof.
    apply type_mutind; crush.

    rewrite H; auto.
    inversion H0; subst.
    rewrite plus_comm; auto.

    rewrite ge_n_implies_jump_shift_var; auto.
    inversion H; subst; auto.

    rewrite H, H0; auto;
    inversion H1; subst; auto.
    rewrite plus_comm; auto.

    rewrite H; auto.
    inversion H0; subst; auto.
    
    inversion H0; subst.
    rewrite H; auto.

    inversion H0; subst;
    rewrite H; auto.

    inversion H1; subst;
    rewrite H, H0; auto.

  Qed.
  
  Lemma ge_n_implies_jump_shift_type :
    (forall t i m, ge_type t i -> (t [Some i] ljump_t m) = (t lshift_t m)).
  Proof.
    destruct ge_n_implies_jump_shift; crush.
  Qed.
  
  Lemma ge_n_implies_jump_shift_decl_ty :
    (forall d i m, ge_decl_ty d i -> (d [Some i] ljump_dt m) = (d lshift_dt m)).
  Proof.
    destruct ge_n_implies_jump_shift; crush.
  Qed.
  
  Lemma ge_n_implies_jump_shift_decl_tys :
    (forall ds i m, ge_decl_tys ds i -> (ds [Some i] ljump_dts m) = (ds lshift_dts m)).
  Proof.
    destruct ge_n_implies_jump_shift; crush.
  Qed.

  Lemma ge_type_in_env :
    forall G n, ge_env G n -> forall t, In t G -> ge_type t n.
  Proof.
    intro G; induction G as [|t' G']; intros.
    inversion H0.

    inversion H0; subst.
    inversion H; auto.

    apply IHG'; auto.
    inversion H; auto.
  Qed.
  
  Lemma lshift_add_mutind :
    (forall t n m, (t lshift_t n lshift_t m) = (t lshift_t (n + m))) /\
    (forall d n m, (d lshift_dt n lshift_dt m) = (d lshift_dt (n + m))) /\
    (forall ds n m, (ds lshift_dts n lshift_dts m) = (ds lshift_dts (n + m))). 
  Proof.
    apply type_mutind; crush.
    destruct v as [x|x]; crush.
    rewrite plus_assoc; auto.
  Qed.

  Lemma lshift_add_type :
    (forall t n m, (t lshift_t n lshift_t m) = (t lshift_t (n + m))). 
  Proof.
    destruct lshift_add_mutind; crush.
  Qed.

  Lemma lshift_add_decl_ty :
    (forall d n m, (d lshift_dt n lshift_dt m) = (d lshift_dt (n + m))). 
  Proof.
    destruct lshift_add_mutind; crush.
  Qed.

  Lemma lshift_add_decl_tys :
    (forall ds n m, (ds lshift_dts n lshift_dts m) = (ds lshift_dts (n + m))). 
  Proof.
    destruct lshift_add_mutind; crush.
  Qed.

  Hint Resolve lshift_add_decl_tys lshift_add_type lshift_add_decl_ty.
  Hint Rewrite lshift_add_decl_tys lshift_add_type lshift_add_decl_ty.

  Lemma lshift_subst_var :
    forall y v x n, (([v /v x] y) lshift_v n) = [v lshift_v n /v x] (y lshift_v n).
  Proof.
    intros.
    destruct y as [r|r]; crush.

    destruct (Nat.eq_dec x r); subst.
    rewrite <- beq_nat_refl; auto.
    destruct (Nat.eqb_neq x r) as [Htemp Hneqb]; clear Htemp;
    rewrite Hneqb; auto.
  Qed.
  
  Lemma lshift_subst_mutind :
    (forall t v x n, (([v /t x] t) lshift_t n) = [v lshift_v n /t x] (t lshift_t n)) /\
    (forall d v x n, (([v /dt x] d) lshift_dt n) = [v lshift_v n /dt x] (d lshift_dt n)) /\
    (forall ds v x n, (([v /dts x] ds) lshift_dts n) = [v lshift_v n /dts x] (ds lshift_dts n)).
  Proof.
    apply type_mutind; crush.
    assert (Htemp : S n = n + 1); crush.

    destruct v as [m|m]; crush.
    rewrite lshift_subst_var; auto.
  Qed.
  
  Lemma lshift_subst_type :
    (forall t v x n, (([v /t x] t) lshift_t n) = [v lshift_v n /t x] (t lshift_t n)).
  Proof.
    destruct lshift_subst_mutind; crush.
  Qed.
  
  Lemma lshift_subst_decl_ty :
    (forall d v x n, (([v /dt x] d) lshift_dt n) = [v lshift_v n /dt x] (d lshift_dt n)).
  Proof.
    destruct lshift_subst_mutind; crush.
  Qed.
  
  Lemma lshift_subst_decl_tys :
    (forall ds v x n, (([v /dts x] ds) lshift_dts n) = [v lshift_v n /dts x] (ds lshift_dts n)).
  Proof.
    destruct lshift_subst_mutind; crush.
  Qed.
  
  (*Lemma ljump_subst_mutind :
    (forall t p x i n, (([p /t x] t) [i] ljump_t n) = [p [i] ljump_p n /t x] (t [i] ljump_t n)) /\
    (forall d p x i n, (([p /d x] d) [i] ljump_d n) = [p [i] ljump_p n /d x] (d [i] ljump_d n)) /\
    (forall p p' x i n, (([p' /p x] p) [i] ljump_p n) = [p' [i] ljump_p n /p x] (p [i] ljump_p n)).
  Proof.
    apply type_mutind; crush.
    assert (Htemp : S n = n + 1); crush.

    destruct v as [m|m]; crush.
    destruct (Nat.eq_dec x m) as [|Heq]; subst.
    destruct (Nat.eqb_eq m m) as [Htemp Heqb]; rewrite Heqb; auto.
    destruct (Nat.eqb_neq x m) as [Htemp Hneqb]; rewrite Hneqb; crush.
  Qed.
  
  Lemma ljump_subst_type :
  Proof.
    destruct lshift_subst_mutind; crush.
  Qed.
  
  Lemma ljump_subst_decl :
  Proof.
    destruct lshift_subst_mutind; crush.
  Qed.
  
  Lemma ljump_subst_path :
  Proof.
    destruct lshift_subst_mutind; crush.
  Qed.*)

  (*Lemma struct_equiv_refl :
    (forall t, struct_equiv_type t t) /\
    (forall d, struct_equiv_decl d d) /\
    (forall p, struct_equiv_path p p).
  Proof.
    apply type_mutind; crush.

    
    
    destruct v; crush.
  Qed.*)

  (*
  Lemma subst_implies_equality :
    (forall t1 t2 p n, ([p /t n] t1) = ([p /t n] t2) ->
                  n notin_t t1 ->
                  n notin_t t2 ->
                  struct_equiv_type t1 t2 ->
                  t1 = t2) /\
    (forall d1 d2 p n, ([p /d n] d1) = ([p /d n] d2) -> 
                  n notin_d d1 ->
                  n notin_d d2 ->
                  struct_equiv_decl d1 d2 ->
                  d1 = d2) /\
    (forall p1 p2 p n, ([p /p n] p1) = ([p /p n] p2) -> 
                  n notin_p p1 ->
                  n notin_p p2 ->
                  struct_equiv_path p1 p2 ->
                  p1 = p2).
  Proof.
    apply type_mutind;
      try destruct t2;
      try destruct d2;
      try destruct p2; crush.

    inversion H2; inversion H3; inversion H4; subst; apply H in H1; crush.

    inversion H1; inversion H2; inversion H3; subst; apply H in H4; crush.

    inversion H1; inversion H2; inversion H3; subst; apply H in H0; crush.

    inversion H1; inversion H2; inversion H3; subst; apply H in H0; crush.

    destruct v as [x|x];
      destruct v0 as [y|y];
      [|inversion H2|
       inversion H2|]; auto.
    destruct (Nat.eq_dec n x) as [Heq1|Heq1];
      destruct (Nat.eq_dec n y) as [Heq2|Heq2]; subst; [crush| | |]; auto.
    inversion H2; crush.
    inversion H2; crush.
                    
    destruct (Nat.eqb_neq n x) as [Htemp Heqb1]; clear Htemp;
      rewrite Heqb1 in H; auto.
    destruct (Nat.eqb_neq n y) as [Htemp Heqb2]; clear Htemp;
      rewrite Heqb2 in H; auto.

    inversion H2.

    inversion H2.

    inversion H4.

    inversion H2; inversion H3; inversion H4; subst;
      apply H in H5; apply H0 in H1; crush.
  Qed.
*)  
  Lemma ljump_lshift_mutind :
    (forall t, ge_type t 0 ->
            (forall m i n, ((t lshift_t (S m)) [i] ljump_t n) = ((t [dec i (S m)] ljump_t n) lshift_t (S (m [i] ljump_n n))))) /\
    (forall d, ge_decl_ty d 0 ->
            (forall m i n, ((d lshift_dt (S m)) [i] ljump_dt n) = ((d [dec i (S m)] ljump_dt n) lshift_dt (S (m [i] ljump_n n))))) /\
    (forall ds, ge_decl_tys ds 0 ->
            (forall m i n, ((ds lshift_dts (S m)) [i] ljump_dts n) = ((ds [dec i (S m)] ljump_dts n) lshift_dts (S (m [i] ljump_n n))))).
  Proof.
    apply type_mutind; intros; auto.

    simpl; rewrite H.
    inversion H0; subst.

    destruct i as [i'|]; simpl; auto.
    destruct (lt_eq_lt_dec i' m) as [Hlt|Hlt];
      [destruct Hlt as [Hlt|Hlt]|]; subst.
    
    destruct (Nat.ltb_lt i' (S m)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; auto; simpl.
    destruct (Nat.ltb_lt (i' + 1) (S m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    destruct (Nat.ltb_nlt m i') as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; [|crush].
    destruct (Nat.ltb_nlt m (i' + 1)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; crush.

    destruct (Nat.ltb_nlt (m + 1) (S m)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; [|crush].
    destruct (Nat.ltb_nlt m m) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    destruct (Nat.ltb_lt m (S m)) as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; auto; simpl.
    destruct (Nat.ltb_lt m (m + 1)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; [|crush].
    assert (Htemp : m + 1 - S m = 0); [crush|rewrite Htemp; clear Htemp].

    rewrite l_jump_None_decl_tys.
    rewrite ge_n_implies_jump_shift_decl_tys.
    rewrite lshift_add_decl_tys;
    assert (n + S m = S (m + n)); crush.
    
    apply ge_lt_n_decl_tys with (n:=1); auto.

    destruct (Nat.ltb_nlt (i' + 1) (S m)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; [|crush].
    destruct (Nat.ltb_nlt i' (S m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [simpl|crush].
    destruct (Nat.ltb_lt m i') as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; auto.
    destruct (Nat.ltb_lt m (i' + 1)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; [|crush].
    assert (Htemp : i' + 1 - S m = i' - S m + 1); [crush|rewrite Htemp; auto].
    
    inversion H0; subst; apply ge_lt_n_decl_tys with (n:=1); auto.    

    assert (Htemp : ((sel v l lshift_t S m) [i] ljump_t n) = (sel ((v lshift_v S m) [i] ljump_v n) l));
      [auto| rewrite Htemp; rewrite ljump_lshift_var; auto].

    simpl; rewrite H, H0.

    destruct i as [i'|]; simpl; auto.
    destruct (lt_eq_lt_dec i' m) as [Hlt|Hlt];
      [destruct Hlt as [Hlt|Hlt]|]; subst.
    
    destruct (Nat.ltb_lt i' (S m)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; auto; simpl.
    destruct (Nat.ltb_lt (i' + 1) (S m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    destruct (Nat.ltb_nlt m i') as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; [|crush].
    destruct (Nat.ltb_nlt m (i' + 1)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; crush.

    destruct (Nat.ltb_nlt (m + 1) (S m)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; [|crush].
    destruct (Nat.ltb_nlt m m) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [|crush].
    destruct (Nat.ltb_lt m (S m)) as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; auto; simpl.
    destruct (Nat.ltb_lt m (m + 1)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; [|crush].
    assert (Htemp : m + 1 - S m = 0); [crush|rewrite Htemp; clear Htemp].
    
    rewrite ge_n_implies_jump_shift_type.
    rewrite lshift_add_type;
      assert (n + S m = S (m + n)); crush.
        
    apply ge_lt_n_type with (n:=1); auto.
    inversion H1; auto.

    destruct (Nat.ltb_nlt (i' + 1) (S m)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; [|crush].
    destruct (Nat.ltb_nlt i' (S m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; [simpl|crush].
    destruct (Nat.ltb_lt m i') as [Htemp Hltb3]; clear Htemp;
    rewrite Hltb3; auto.
    destruct (Nat.ltb_lt m (i' + 1)) as [Htemp Hltb4]; clear Htemp;
    rewrite Hltb4; [|crush].
    assert (Htemp : i' + 1 - S m = i' - S m + 1); [crush|rewrite Htemp; auto].
    
    inversion H1; subst; apply ge_lt_n_type with (n:=1); auto. 
    inversion H1; auto.

    inversion H0; subst; simpl; rewrite H; crush.

    inversion H0; subst; simpl; rewrite H; crush.

    inversion H0; subst; simpl; rewrite H; crush.
    
    inversion H1; subst; simpl; rewrite H, H0; crush.
    
    (*if i < m then dec (inc i 1) (S m) = None = inc (dec i (S m)) 1 
               and m [inc i 1] n = m + n = m [i] n    
      if i = m then dec (inc i 1) (S m) = Some 0
               and  inc (dec i (S m)) = None
               and m [inc i 1] n = m , m [i] n = m + n
               but if d is well-formed then all concrete references in d are greater than O
               which means that the jump of n is equivalent to a shift of n.
               which gives us the equality we need
      if i > m then we get equality immediately
     *)
  Qed.
  
  Lemma ljump_lshift_type :
    (forall t, ge_type t 0 ->
            (forall m i n, ((t lshift_t (S m)) [i] ljump_t n) = ((t [dec i (S m)] ljump_t n) lshift_t (S (m [i] ljump_n n))))).
  Proof.
    destruct ljump_lshift_mutind; crush.
  Qed.
  
  Lemma ljump_lshift_decl_ty :
    (forall d, ge_decl_ty d 0 ->
            (forall m i n, ((d lshift_dt (S m)) [i] ljump_dt n) = ((d [dec i (S m)] ljump_dt n) lshift_dt (S (m [i] ljump_n n))))).
  Proof.
    destruct ljump_lshift_mutind; crush.
  Qed.
  
  Lemma ljump_lshift_decl_tys :
    (forall ds, ge_decl_tys ds 0 ->
            (forall m i n, ((ds lshift_dts (S m)) [i] ljump_dts n) = ((ds [dec i (S m)] ljump_dts n) lshift_dts (S (m [i] ljump_n n))))).
  Proof.
    destruct ljump_lshift_mutind; crush.
  Qed.

  Lemma lshift_ljump :
    forall x n i m, ((x [i] ljump_n n) + m) = ((x + m) [inc i m] ljump_n n).
  Proof.

    crush.
    destruct i as [i'|]; crush.

    destruct (lt_dec x i') as [Hlt|Hnlt].
    destruct (Nat.ltb_lt x i') as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; auto.
    destruct (Nat.ltb_lt (x + m) (i' + m)) as [Htemp Hltb2]; clear Htemp;
    rewrite Hltb2; crush.

    destruct (Nat.ltb_nlt x i') as [Htemp Hnltb1]; clear Htemp;
    rewrite Hnltb1; auto.
    destruct (Nat.ltb_nlt (x + m) (i' + m)) as [Htemp Hnltb2]; clear Htemp;
    rewrite Hnltb2; crush.
  Qed.


  Lemma lshift_ljump_var :
    forall v n i m, ((v [i] ljump_v n) lshift_v m) = ((v lshift_v m) [inc i m] ljump_v n).
  Proof.
    intro v; destruct v as [x|x]; crush.
    rewrite lshift_ljump; auto.
  Qed.

  Hint Resolve lshift_ljump_var lshift_ljump.
  Hint Rewrite lshift_ljump_var lshift_ljump.

  Lemma lshift_ljump_mutind :
    (forall t n i m, ((t [i] ljump_t n) lshift_t m) = ((t lshift_t m) [inc i m] ljump_t n)) /\
    (forall d n i m, ((d [i] ljump_dt n) lshift_dt m) = ((d lshift_dt m) [inc i m] ljump_dt n)) /\
    (forall ds n i m, ((ds [i] ljump_dts n) lshift_dts m) = ((ds lshift_dts m) [inc i m] ljump_dts n)).
  Proof.
    apply type_mutind; crush.

    assert (m + 1 = S m); crush.
    assert (m + 1 = S m); crush.
  Qed.

  Lemma lshift_ljump_type :
    (forall t n i m, ((t [i] ljump_t n) lshift_t m) = ((t lshift_t m) [inc i m] ljump_t n)).
  Proof.
    destruct lshift_ljump_mutind; crush.
  Qed.

  Lemma lshift_ljump_decl_ty :
    (forall d n i m, ((d [i] ljump_dt n) lshift_dt m) = ((d lshift_dt m) [inc i m] ljump_dt n)).
  Proof.
    destruct lshift_ljump_mutind; crush.
  Qed.

  Lemma lshift_ljump_decl_tys :
    (forall ds n i m, ((ds [i] ljump_dts n) lshift_dts m) = ((ds lshift_dts m) [inc i m] ljump_dts n)).
  Proof.
    destruct lshift_ljump_mutind; crush.
  Qed.
    
  
  Lemma ljump_t_in_env :
    forall G n t, get n G = Some t ->
             forall i m, get n (G [i] ljump_e m) = Some (t [dec i n] ljump_t m).
  Proof.
    intro G; induction G as [|t' G']; crush.

    destruct n as [|n']; crush.
    rewrite IHG' with (t:=t); auto.

    rewrite dec_add; crush.
  Qed.

  Lemma jump_lt_n :
    forall r i n, r < i -> (r [Some i] ljump_n n) = r.
  Proof.
    intros; destruct (Nat.ltb_lt r i) as [Htemp Hltb];
    simpl; rewrite Hltb; crush.
  Qed.

  Lemma jump_nlt_n :
    forall r i n, ~ r < i -> (r [Some i] ljump_n n) = r + n.
  Proof.
    intros; destruct (Nat.ltb_nlt r i) as [Htemp Hltb];
    simpl; rewrite Hltb; crush.
  Qed.

  Hint Rewrite jump_lt_n jump_nlt_n.
  Hint Resolve jump_lt_n jump_nlt_n.

  Lemma jump_env_length :
    forall G i n, length (G [i] ljump_e n) = length G.
  Proof.
    intro G; induction G as [|t' G']; crush.
  Qed.

  Hint Rewrite jump_env_length.
  Hint Resolve jump_env_length.
  
  Lemma typing_weakening :
    forall G p t, G vdash p hasType t ->
             ge_env G 0 ->
             forall G1 G2, G = G1++G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (p [i] ljump_v n) hasType (t [i] ljump_t n).
  Proof.
    intros G p t Htyp; induction Htyp; intros; subst.

    rewrite ljump_lshift_type; auto.
    apply t_var.

    destruct (lt_dec n (length G1)) as [Hlt|Hlt];
      [rewrite jump_lt_n|
       rewrite jump_nlt_n]; auto.

    rewrite get_app_l.
    rewrite ljump_t_in_env with (t:=t); auto.
    assert (Htemp : dec (dec (Some (length G1)) 1) n =
                    dec (Some (length G1)) (S n)); [simpl|rewrite Htemp; auto].
    destruct G1 as [|t' G1'];
      [inversion Hlt|simpl].
    rewrite <- minus_n_O.
    destruct (lt_dec (length G1') n) as [Hlt2|Hlt2];
      [destruct (Nat.ltb_lt (length G1') n) as [Htemp Hltb2];
        clear Htemp; rewrite Hltb2; [|auto];
        destruct (Nat.ltb_lt (S (length G1')) (S n)) as [Htemp Hltb3];
        clear Htemp; rewrite Hltb3; [|crush]|]; auto.
    
    
    rewrite <- get_app_l with (G2:=G2); auto.
    
    rewrite jump_env_length; auto.
    
    rewrite get_app_r; [|crush].
    rewrite jump_env_length.
    simpl.
    destruct (Nat.ltb_lt (length G1) (S n)) as [Htemp Hltb1]; clear Htemp;
    rewrite Hltb1; [|crush].
    rewrite l_jump_None_type.
    rewrite get_app_r in  H; [|crush].
    rewrite get_shift with (G':=G') in H.
    assert (Htemp : n - length G1 + length G' = n + length G' - length G1);
      [crush|rewrite Htemp in H; auto].

    apply ge_type_in_env with (G:=G1++G2); auto.
    apply get_in with (n:=n); auto.
  Qed.

  Hint Resolve typing_weakening.
  Hint Rewrite typing_weakening.

  (*Inductive equiv_top : env -> ty -> Prop :=
  | eq_top : forall G, equiv_top G top
  | eq_low : forall G x l t, G vdash x ni (type l sup t) ->
                        equiv_top G t -> 
                        equiv_top G (sel x l).

  Hint Constructors equiv_top.

  Lemma sub_top_equiv :
    forall G1 t1 t2 G2, G1 vdash t1 <; t2 dashv G2 -> t1 = top -> equiv_top G2 t2.
  Proof.
    intros.  induction H.
    auto.
    inversion H0.
    inversion H0.
    inversion H0.
    apply eq_low with (t:=s); auto.
    inversion H0.
    inversion H0.
  Qed.

  Lemma sub_equiv_top_all :
    forall G t, equiv_top G t -> forall G' t', G' vdash t' <; t dashv G.
  Proof.
    intros G t Hequiv; induction Hequiv; intros; [crush|subst].
    apply s_lower with (s:=t); auto.
  Qed.

  Inductive equiv_bot : env -> ty -> Prop :=
  | eq_bot : forall G, equiv_bot G bot
  | eq_upp : forall G x l t, G vdash x ni (type l ext t) ->
                        equiv_bot G t -> 
                        equiv_bot G (sel x l).

  Hint Constructors equiv_bot.

  Lemma sub_bot_equiv :
    forall G1 t1 t2 G2, G1 vdash t1 <; t2 dashv G2 -> t2 = bot -> equiv_bot G1 t1.
  Proof.
    intros.  induction H.
    inversion H0.
    auto.
    inversion H0.
    inversion H0.
    inversion H0.
    apply eq_upp with (t:=u); auto.
    inversion H0.
  Qed.

  Lemma sub_equiv_bot_all :
    forall G t, equiv_bot G t -> forall G' t', G vdash t <; t' dashv G'.
  Proof.
    intros G t Hequiv; induction Hequiv; intros; [crush|subst].
    apply s_upper with (u:=t); auto.
  Qed.*)    

  Lemma ljump_subst_mutind :
    (forall t v x i n, ge_var v 0 -> (([v /t x] t) [i] ljump_t n) = [v [i] ljump_v n /t x] (t [i] ljump_t n)) /\
    (forall d v x i n, ge_var v 0 -> (([v /dt x] d) [i] ljump_dt n) = [v [i] ljump_v n /dt x] (d [i] ljump_dt n)) /\
    (forall ds v x i n, ge_var v 0 -> (([v /dts x] ds) [i] ljump_dts n) = [v [i] ljump_v n /dts x] (ds [i] ljump_dts n)).
  Proof.
    apply type_mutind; crush.

    (*rewrite H; auto.*)
    rewrite ljump_lshift_path; auto.
    rewrite dec_inc_n.

    destruct i as [i'|]; [|crush].
    simpl; destruct (Nat.ltb_lt 0 (i' + 1)) as [Htemp Hltb];
    rewrite Hltb; crush.

    destruct v as [r|r]; crush.
    destruct (Nat.eq_dec x r); subst.
    rewrite (Nat.eqb_refl); auto.
    rewrite <- Nat.eqb_neq in n0;
    rewrite n0; auto.
  Qed.

  Lemma ljump_subst_type :
    (forall t p x i n, ge_path p 0 -> (([p /t x] t) [i] ljump_t n) = [p [i] ljump_p n /t x] (t [i] ljump_t n)).
  Proof.
    destruct ljump_subst_mutind; crush.
  Qed.

  Lemma ljump_subst_decl :
    (forall d p x i n, ge_path p 0 -> (([p /d x] d) [i] ljump_d n) = [p [i] ljump_p n /d x] (d [i] ljump_d n)).
  Proof.
    destruct ljump_subst_mutind; crush.
  Qed.

  Lemma ljump_subst_path :
    (forall p p' x i n, ge_path p' 0 -> (([p' /p x] p) [i] ljump_p n) = [p' [i] ljump_p n /p x] (p [i] ljump_p n)).
  Proof.
    destruct ljump_subst_mutind; crush.
  Qed.

  Hint Rewrite ljump_subst_type ljump_subst_decl ljump_subst_path.
  Hint Resolve ljump_subst_type ljump_subst_decl ljump_subst_path.

  Lemma ge_lshift_mutind :
    (forall t n m, ge_type t n ->
              ge_type (t lshift_t m) (n + m)) /\
    (forall d n m, ge_decl d n ->
              ge_decl (d lshift_d m) (n + m)) /\
    (forall p n m, ge_path p n ->
              ge_path (p lshift_p m) (n + m)).
  Proof.
    apply type_mutind; intros; auto.

    inversion H1; subst; simpl; apply ge_str.
    apply H with (m := m) in H4; auto.
    apply H0 with (m := m) in H6; auto.

    inversion H0; subst; simpl; apply ge_sel;
    apply H; auto.

    inversion H0; subst; simpl; apply ge_upper;
    apply H; auto.

    inversion H0; subst; simpl; apply ge_lower;
    apply H; auto.

    destruct v as [r|r]; auto.
    inversion H; subst.
    simpl; rewrite lshift_concrete. apply ge_concrete; crush.

    inversion H1; subst; simpl; apply ge_cast;
    [apply H|apply H0]; auto.
  Qed.

  Lemma ge_lshift_type :
    (forall t n m, ge_type t n ->
              ge_type (t lshift_t m) (n + m)).
  Proof.
    destruct ge_lshift_mutind; crush.
  Qed.

  Lemma ge_lshift_decl : 
    (forall d n m, ge_decl d n ->
              ge_decl (d lshift_d m) (n + m)).
  Proof.
    destruct ge_lshift_mutind; crush.
  Qed.

  Lemma ge_lshift_path : 
    (forall p n m, ge_path p n ->
              ge_path (p lshift_p m) (n + m)).
  Proof.
    destruct ge_lshift_mutind; crush.
  Qed.

  Lemma ge_rshift_mutind :
    (forall t n m, ge_type t n ->
              n >= m ->
              ge_type (t rshift_t m) (n - m)) /\
    (forall d n m, ge_decl d n ->
              n >= m ->
              ge_decl (d rshift_d m) (n - m)) /\
    (forall p n m, ge_path p n ->
              n >= m ->
              ge_path (p rshift_p m) (n - m)).
  Proof.
    apply type_mutind; intros; auto.

    inversion H1; subst; simpl;
    apply ge_str.
    apply H with (m:=m) in H5; auto.
    apply H0 with (m:=m) in H7; auto.
    rewrite minus_Sn_m; auto.
    rewrite minus_Sn_m; auto.

    inversion H0; subst; crush.

    inversion H0; subst; crush.

    inversion H0; subst; crush.

    simpl; destruct v as [r|r]; [|crush].
    rewrite rshift_concrete.
    apply ge_concrete.
    inversion H; crush.

    inversion H1; crush.    
    
  Qed.

  Lemma ge_rshift_type :
    (forall t n m, ge_type t n ->
              n >= m ->
              ge_type (t rshift_t m) (n - m)).
  Proof.
    destruct ge_rshift_mutind; crush.
  Qed.

  Lemma ge_rshift_decl :
    (forall d n m, ge_decl d n ->
              n >= m ->
              ge_decl (d rshift_d m) (n - m)).
  Proof.
    destruct ge_rshift_mutind; crush.
  Qed.

  Lemma ge_rshift_path :
    (forall p n m, ge_path p n ->
              n >= m ->
              ge_path (p rshift_p m) (n - m)).
  Proof.
    destruct ge_rshift_mutind; crush.
  Qed.

  Hint Resolve ge_lshift_type ge_lshift_decl ge_lshift_path ge_rshift_type ge_rshift_decl ge_rshift_path.
  Hint Rewrite ge_lshift_type ge_lshift_decl ge_lshift_path ge_rshift_type ge_rshift_decl ge_rshift_path.

  Lemma ge_ljump_mutind :
    (forall t m i n, ge_type t m ->
                ge_type (t [i] ljump_t n) m) /\
    (forall d m i n, ge_decl d m ->
                ge_decl (d [i] ljump_d n) m) /\
    (forall p m i n, ge_path p m ->
                ge_path (p [i] ljump_p n) m).
  Proof.
    apply type_mutind; intros; auto.

    inversion H1; crush.

    inversion H0; crush.

    inversion H0; crush.

    inversion H0; crush.

    destruct v as [r|r]; crush.
    unfold left_jump_n.
    destruct i as [i'|]; auto.
    inversion H; subst.
    destruct (lt_dec r i') as [Hlt|Hlt];
      [destruct (Nat.ltb_lt r i') as [Htemp Hltb]; clear Htemp;
       rewrite Hltb; auto|
       destruct (Nat.ltb_nlt r i') as [Htemp Hltb]; clear Htemp;
       rewrite Hltb; crush].

    inversion H1; crush.
    
  Qed.

  Lemma ge_ljump_type :
    (forall t m i n, ge_type t m ->
                ge_type (t [i] ljump_t n) m).
  Proof.
    destruct ge_ljump_mutind; crush.
  Qed.

  Lemma ge_ljump_decl :
    (forall d m i n, ge_decl d m ->
                ge_decl (d [i] ljump_d n) m).
  Proof.
    destruct ge_ljump_mutind; crush.
  Qed.

  Lemma ge_ljump_path :
    (forall p m i n, ge_path p m ->
                ge_path (p [i] ljump_p n) m).
  Proof.
    destruct ge_ljump_mutind; crush.
  Qed.

  Hint Rewrite ge_ljump_type ge_ljump_decl ge_ljump_path.
  Hint Resolve ge_ljump_type ge_ljump_decl ge_ljump_path.
  
  Lemma ge_subst_mutind :
    (forall t p n, ge_type t n ->
              ge_path p n ->
              forall x, ge_type ([p /t x] t) n) /\
    (forall d p n, ge_decl d n ->
              ge_path p n ->
              forall x, ge_decl ([p /d x] d) n) /\
    (forall p p' n, ge_path p n ->
               ge_path p' n ->
               forall x, ge_path ([p' /p x] p) n).
  Proof.
    apply type_mutind; intros; auto.

    simpl; apply ge_str.
    inversion H1; subst.
    apply H; auto.
    assert (Htemp : S n = n + 1);
      [crush|rewrite Htemp;
         apply ge_lshift_path; auto].
    inversion H1; subst.
    apply H0; auto.
    assert (Htemp : S n = n + 1);
      [crush|rewrite Htemp;
         apply ge_lshift_path; auto].

    inversion H0; subst; simpl;
    apply ge_sel; crush.

    inversion H0; crush.

    inversion H0; crush.

    destruct v as [r|r]; crush.
    destruct (Nat.eq_dec x r); subst.    
    rewrite (Nat.eqb_refl); auto.
    rewrite <- (Nat.eqb_neq) in n0; rewrite n0; crush.

    inversion H1; crush.    
  Qed.
  
  Lemma ge_subst_type :
    (forall t p n, ge_type t n ->
              ge_path p n ->
              forall x, ge_type ([p /t x] t) n).
  Proof.
    destruct ge_subst_mutind; crush.
  Qed.
  
  Lemma ge_subst_decl :
    (forall d p n, ge_decl d n ->
              ge_path p n ->
              forall x, ge_decl ([p /d x] d) n).
  Proof.
    destruct ge_subst_mutind; crush.
  Qed.
  
  Lemma ge_subst_path :
    (forall p p' n, ge_path p n ->
               ge_path p' n ->
               forall x, ge_path ([p' /p x] p) n).
  Proof.
    destruct ge_subst_mutind; crush.
  Qed.

  Lemma subst_ge_mutind :
    (forall t p x n, ge_type ([p /t x] t) n ->
                ge_type t n) /\
    (forall d p x n, ge_decl ([p /d x] d) n ->
                ge_decl d n) /\
    (forall p p' x n, ge_path ([p' /p x] p) n ->
                 ge_path p n).
  Proof.
    apply type_mutind; intros; auto.

    inversion H1; subst.
    apply H in H4.
    apply H0 in H6.
    apply ge_str; auto.

    inversion H0; subst.
    apply H in H4; crush.

    inversion H0; subst.
    apply H in H4; crush.

    inversion H0; subst.
    apply H in H4; auto.

    destruct v as [r|r]; auto.

    inversion H1; subst.
    apply H in H4;
      apply H0 in H6; auto.
  Qed.

  Lemma subst_ge_type :
    (forall t p x n, ge_type ([p /t x] t) n ->
                ge_type t n).
  Proof.
    destruct subst_ge_mutind; crush.
  Qed.

  Lemma subst_ge_decl :
    (forall d p x n, ge_decl ([p /d x] d) n ->
                ge_decl d n).
  Proof.
    destruct subst_ge_mutind; crush.
  Qed.

  Lemma subst_ge_path :
    (forall p p' x n, ge_path ([p' /p x] p) n ->
                 ge_path p n).
  Proof.
    destruct subst_ge_mutind; crush.
  Qed.
  
  Lemma ge_typing :
    forall G p t, G vdash p hasType t ->
             forall n, ge_env G n ->
                  ge_path p n ->
                  ge_type t n.
  Proof.
    intros G p t Htyp; induction Htyp; intros.

    apply get_in in H.
    apply ge_type_in_env with (n:=n0) in H; auto.

    inversion H0; auto.
    
  Qed.

  Hint Rewrite ge_typing.
  Hint Resolve ge_typing.
  
  Lemma ge_has_contains_mutind :
    (forall G p d, G vdash p ni d ->
              forall n, ge_env G n ->
                   ge_path p n ->
                   ge_decl d n) /\
    (forall G t d, G vdash d cont t ->
              forall n, ge_env G n ->
                   ge_type t n ->
                   ge_decl d n).
  Proof.
    apply has_contains_mutind; intros; auto.

    apply ge_subst_decl; auto.
    apply H; auto.
    apply ge_typing with (G:=G)(p:=p); auto.

    inversion H0; subst.
    assert (Htemp : n = S n - 1); [crush|rewrite Htemp ; clear Htemp].
    apply ge_rshift_decl; crush.

    inversion H0; subst.
    assert (Htemp : n = S n - 1); [crush|rewrite Htemp ; clear Htemp].
    apply ge_rshift_decl; crush.

    apply H0; auto.
    inversion H2; subst.
    apply H in H6; auto.
    inversion H6; auto.
  Qed.

  Lemma ge_has :
    (forall G p d, G vdash p ni d ->
              forall n, ge_env G n ->
                   ge_path p n ->
                   ge_decl d n).
  Proof.
    destruct ge_has_contains_mutind; crush.
  Qed.

  Lemma ge_contains :
    (forall G t d, G vdash d cont t ->
              forall n, ge_env G n ->
                   ge_type t n ->
                   ge_decl d n).
  Proof.
    destruct ge_has_contains_mutind; crush.
  Qed.
  
  Lemma has_contains_weakening :
    (forall G p d, G vdash p ni d ->
              ge_env G 0 ->
              ge_path p 0 ->
              (forall G1 G2, G = G1 ++ G2 ->
                        forall G' i n, i = Some (length G1) ->
                                  n = length G' ->
                                  (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (p [i] ljump_p n) ni (d [i] ljump_d n))) /\
    (forall G t d, G vdash d cont t ->
              ge_env G 0 ->
              ge_type t 0 ->
              (forall G1 G2, G = G1 ++ G2 ->
                        forall G' i n, i = Some (length G1) ->
                                  n = length G' ->
                                  (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (d [i] ljump_d n) cont (t [i] ljump_t n))).
  Proof.
    apply has_contains_mutind; intros; subst.

    (*has weakening*)
    rewrite ljump_subst_decl; auto.
    apply h_path with (t:=(t [Some (length G1)] ljump_t (length G'))).

    apply typing_weakening with (G:=G1++G2); auto.
    apply H; auto.
    apply ge_typing with (G:=G1++G2)(p:=p); auto.

    (*struct contains weakening*)
    simpl.
    rewrite ljump_rshift_decl.
    apply c_struct1.
    inversion H0; subst; auto.
    
    simpl.
    rewrite ljump_rshift_decl.
    apply c_struct2.
    inversion H0; subst; auto.

    apply c_select with (l':=l')(t:=t [Some (length G1)] ljump_t (length G')).
    apply H; auto.
    inversion H2; auto.
    
    apply H0; auto.
    apply ge_has with (n:=0) in h; auto.
    inversion h; auto.
    inversion H2; auto.
  Qed.
  
  Lemma has_weakening :
    (forall G p d, G vdash p ni d ->
              ge_env G 0 ->
              ge_path p 0 ->
              (forall G1 G2, G = G1 ++ G2 ->
                        forall G' i n, i = Some (length G1) ->
                                  n = length G' ->
                                  (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (p [i] ljump_p n) ni (d [i] ljump_d n))).
  Proof.
    destruct has_contains_weakening; crush.
  Qed.
  
  Lemma contains_weakening :
    (forall G t d, G vdash d cont t ->
              ge_env G 0 ->
              ge_type t 0 ->
              (forall G1 G2, G = G1 ++ G2 ->
                        forall G' i n, i = Some (length G1) ->
                                  n = length G' ->
                                  (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (d [i] ljump_d n) cont (t [i] ljump_t n))).
  Proof.
    destruct has_contains_weakening; crush.
  Qed.

  Hint Resolve contains_weakening has_weakening.
  Hint Rewrite contains_weakening has_weakening.

  Lemma ge_wf_mutind :
    (forall G t, G vdash t wf_t ->
            ge_type t 0) /\
    (forall G d, G vdash d wf_d ->
            ge_decl d 0) /\
    (forall G p, G vdash p wf_p ->
            ge_path p 0).
  Proof.
    apply wf_mutind; crush.

    apply ge_str.
    apply subst_ge_decl in H.
    apply ge_notin_Sn_decl; auto.
    apply subst_ge_decl in H0.
    apply ge_notin_Sn_decl; auto.
  Qed.

  Lemma ge_wf_type :
    (forall G t, G vdash t wf_t ->
            ge_type t 0).
  Proof.
    destruct ge_wf_mutind; crush.
  Qed.

  Lemma ge_wf_decl :
    (forall G d, G vdash d wf_d ->
            ge_decl d 0).
  Proof.
    destruct ge_wf_mutind; crush.
  Qed.

  Lemma ge_wf_path :
    (forall G p, G vdash p wf_p ->
            ge_path p 0).
  Proof.
    destruct ge_wf_mutind; crush.
  Qed.

  Hint Resolve ge_wf_type ge_wf_decl ge_wf_path.
  Hint Rewrite ge_wf_type ge_wf_decl ge_wf_path.
  
  Lemma wf_weakening_mutind :
    (forall G t, G vdash t wf_t ->
            ge_env G 0 ->
            (forall G1 G2, G = G1 ++ G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (t [i] ljump_t n) wf_t)) /\
    (forall G d, G vdash d wf_d ->
            ge_env G 0 ->
            (forall G1 G2, G = G1 ++ G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (d [i] ljump_d n) wf_d)) /\
    (forall G p, G vdash p wf_p ->
            ge_env G 0 ->
            (forall G1 G2, G = G1 ++ G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (p [i] ljump_p n) wf_p)).
  Proof.
    apply wf_mutind; intros; subst; auto.

    simpl.
    apply wf_sel_lower with (t:=t [Some (length G1)] ljump_t length G').
    apply has_weakening with (G1:=G1)
                               (G2:=G2)
                               (G':=G')
                               (i:=Some (length G1))(n:=length G') in h; auto.
    apply ge_wf_path with (G:=G1++G2); auto.
    apply H with (G3:=G1)(G4:=G2)(G':=G')(i:=Some (length G1))(n:=length G') in H0; auto.

    simpl.
    apply wf_sel_upper with (t:=t [Some (length G1)] ljump_t length G').
    apply has_weakening with (G1:=G1)
                               (G2:=G2)
                               (G':=G')
                               (i:=Some (length G1))(n:=length G') in h; auto.
    apply ge_wf_path with (G:=G1++G2); auto.
    apply H with (G3:=G1)(G4:=G2)(G':=G')(i:=Some (length G1))(n:=length G') in H0; auto.

    simpl.
    apply wf_struct.
    assert (Hwf : ge_env (struct d1 d2 :: G1 ++ G2) 0);
      [apply ge_cons; auto;
       apply ge_wf_type with (G:=G1++G2); auto|].
    apply H with (G3:=(struct d1 d2)::G1)
                   (G4:=G2)
                   (G':=G')
                   (i:=Some (S (length G1)))(n:=length G') in Hwf; auto.
    simpl in Hwf.
    rewrite <- minus_n_O in Hwf.
    assert (Htemp : length G1 + 1 = S (length G1));
      [crush|
       rewrite Htemp;
         rewrite Htemp in Hwf; clear Htemp].
    rewrite ljump_subst_decl in Hwf; auto.
    assert (Hwf : ge_env (struct d1 d2 :: G1 ++ G2) 0);
      [apply ge_cons; auto;
       apply ge_wf_type with (G:=G1++G2); auto|].
    apply H0 with (G3:=(struct d1 d2)::G1)
                    (G4:=G2)
                    (G':=G')
                    (i:=Some (S (length G1)))(n:=length G') in Hwf; auto.
    simpl in Hwf.
    rewrite <- minus_n_O in Hwf.
    assert (Htemp : length G1 + 1 = S (length G1));
      [crush|
       rewrite Htemp;
         rewrite Htemp in Hwf; clear Htemp].
    rewrite ljump_subst_decl in Hwf; auto.
    
    apply ge_implies_notin_decl with (n:=1); auto.
    apply ge_ljump_decl; auto.
    assert (Htemp : ge_type (struct d1 d2) 0);
      [apply ge_wf_type with (G:=G1++G2); auto|
       inversion Htemp; subst; auto].
    
    apply ge_implies_notin_decl with (n:=1); auto.
    apply ge_ljump_decl; auto.
    assert (Htemp : ge_type (struct d1 d2) 0);
      [apply ge_wf_type with (G:=G1++G2); auto|
       inversion Htemp; subst; auto].

    simpl; apply wf_lower.
    apply H with (G3:=G1)
                   (G4:=G2)
                   (G':=G')
                   (i:=Some (length G1))(n:=length G') in H0; auto.

    simpl; apply wf_upper.
    apply H with (G3:=G1)
                   (G4:=G2)
                   (G':=G')
                   (i:=Some (length G1))(n:=length G') in H0; auto.

    simpl; apply wf_var.
    rewrite app_length.
    rewrite jump_env_length.
    destruct (lt_dec r (length G1)) as [Hlt|Hlt];
      [destruct (Nat.ltb_lt r (length G1)) as [Htemp Hltb]; clear Htemp;
       rewrite Hltb; crush|
       destruct (Nat.ltb_nlt r (length G1)) as [Htemp Hltb]; clear Htemp;
       rewrite Hltb; auto].
    rewrite app_length;
    rewrite app_length in l;
    crush.

    simpl; apply wf_cast.
    apply H with (G3:=G1)
                   (G4:=G2)
                   (G':=G')
                   (i:=Some (length G1))(n:=length G') in H1; auto.
    apply H0 with (G3:=G1)
                   (G4:=G2)
                   (G':=G')
                   (i:=Some (length G1))(n:=length G') in H1; auto.

  Qed.
  
  Lemma wf_insertion_weakening_type :
    (forall G t, G vdash t wf_t ->
            ge_env G 0 ->
            (forall G1 G2, G = G1 ++ G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (t [i] ljump_t n) wf_t)).
  Proof.
    destruct wf_weakening_mutind; crush.
  Qed.
  
  Lemma wf_insertion_weakening_decl :
    (forall G d, G vdash d wf_d ->
            ge_env G 0 ->
            (forall G1 G2, G = G1 ++ G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (d [i] ljump_d n) wf_d)).
  Proof.
    destruct wf_weakening_mutind; crush.
  Qed.
  
  Lemma wf_insertion_weakening_path :
    (forall G p, G vdash p wf_p ->
            ge_env G 0 ->
            (forall G1 G2, G = G1 ++ G2 ->
                      forall G' i n, i = Some (length G1) ->
                                n = length G' ->
                                (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (p [i] ljump_p n) wf_p)).
  Proof.
    destruct wf_weakening_mutind; crush.
  Qed.

  Hint Resolve wf_insertion_weakening_type wf_insertion_weakening_decl wf_insertion_weakening_path.
  Hint Rewrite wf_insertion_weakening_type wf_insertion_weakening_decl wf_insertion_weakening_path.

  Lemma wf_weakening_type :
    forall G t, G vdash t wf_t ->
           ge_env G 0 ->
           forall G', G'++G vdash (t lshift_t length G') wf_t.
  Proof.
    intros.
    apply wf_insertion_weakening_type with (t:=t)
                                             (G1:=nil)
                                             (G2:=G)
                                             (G':=G')
                                             (i:= Some 0)
                                             (n:=length G') in H0; auto; simpl in H0.
    rewrite ge_n_implies_jump_shift_type in H0; auto.
    apply ge_wf_type with (G:=G); auto.    
  Qed.

  Lemma wf_weakening_decl :
    forall G d, G vdash d wf_d ->
           ge_env G 0 ->
           forall G', G'++G vdash (d lshift_d length G') wf_d.
  Proof.
    intros.
    apply wf_insertion_weakening_decl with (d:=d)
                                             (G1:=nil)
                                             (G2:=G)
                                             (G':=G')
                                             (i:= Some 0)
                                             (n:=length G') in H0; auto; simpl in H0.
    rewrite ge_n_implies_jump_shift_decl in H0; auto.
    apply ge_wf_decl with (G:=G); auto.    
  Qed.

  Lemma wf_weakening_path :
    forall G p, G vdash p wf_p ->
           ge_env G 0 ->
           forall G', G'++G vdash (p lshift_p length G') wf_p.
  Proof.
    intros.
    apply wf_insertion_weakening_path with (p:=p)
                                             (G1:=nil)
                                             (G2:=G)
                                             (G':=G')
                                             (i:= Some 0)
                                             (n:=length G') in H0; auto; simpl in H0.
    rewrite ge_n_implies_jump_shift_path in H0; auto.
    apply ge_wf_path with (G:=G); auto.    
  Qed.

  Hint Resolve wf_weakening_type wf_weakening_decl wf_weakening_path.

  Lemma sub_weakening_mutind :
    (forall G t1 t2, G vdash t1 <; t2  ->
                ge_env G 0 ->
                ge_type t1 0 ->
                ge_type t2 0 ->
                (forall G1 G2, G = G1 ++ G2 ->
                          forall G' i n, i = Some (length G1) ->
                                    n = length G' ->
                                    (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (t1 [i] ljump_t n) <; (t2 [i] ljump_t n))) /\
    (forall G d1 d2, G vdash d1 <;; d2 ->
                ge_env G 0 ->
                ge_decl d1 0 ->
                ge_decl d2 0 ->
                (forall G1 G2, G = G1 ++ G2 ->
                          forall G' i n, i = Some (length G1) ->
                                    n = length G' ->
                                    (G1 [dec i 1] ljump_e n) ++ G' ++ G2 vdash (d1 [i] ljump_d n) <;; (d2 [i] ljump_d n))).
  Proof.
    apply sub_mutind; intros; auto.
    
    apply s_refl.
    fold left_jump_p.
    admit. (*obvious*)

    apply s_lower with (s:= s [i0] ljump_t n);
    fold left_jump_p.
    assert (Hsubst : (type l sup (s [i0]ljump_t n)) = ((type l sup s) [i0]ljump_d n)); auto.
    rewrite Hsubst; apply has_weakening with (G:=G); crush.
    inversion H2; auto.
    admit. (*obvious*)
    apply H; auto.
    apply ge_has with (n:=0) in h; auto.
    inversion h; subst; auto.
    inversion H2; auto.

    apply s_upper with (u:= u [i] ljump_t n);
    fold left_jump_p.
    assert (Hsubst : (type l ext (u [i]ljump_t n)) = ((type l ext u) [i]ljump_d n)); auto.
    rewrite Hsubst; apply has_weakening with (G:=G); crush.
    inversion H1; auto.
    apply H; auto.
    apply ge_has with (n:=0) in h; auto.
    inversion h; subst; auto.
    inversion H1; auto.

    apply s_struct;
      fold left_jump_d.
    assert (Hrewrite1 : (struct (d1' [inc i 1]ljump_d n) (d2' [inc i 1]ljump_d n)) = ((struct d1' d2') [i] ljump_t n));
      [auto|rewrite Hrewrite1].
    assert (Hrewrite2 : (struct (d1 [inc i 1]ljump_d n) (d2 [inc i 1]ljump_d n)) = ((struct d1 d2) [i] ljump_t n));
      [auto|rewrite Hrewrite2].
    rewrite lshift_ljump_type.
    assert (Hrewrite3 : (c_ 0) = (c_ 0 [inc i 1] ljump_p n));
      [crush; destruct (Nat.ltb_lt 0 (length G1 +1)) as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1; crush|rewrite Hrewrite3].
    assert (Hrewrite4 : (((c_ 0) [inc i 1]ljump_p n) cast ((struct d1' d2' lshift_t 1) [inc i 1]ljump_t n)) =
                        (((c_ 0) cast ((struct d1' d2' lshift_t 1))) [inc i 1] ljump_p n)); [auto|rewrite Hrewrite4].
    rewrite <- ljump_subst_decl.
    rewrite <- ljump_subst_decl.
    assert (Hrewrite5 :((struct d1 d2 [i]ljump_t n) :: (G1 [dec i 1]ljump_e n)) =
                       (((struct d1 d2) :: G1) [dec (inc i 1) 1] ljump_e n));
      [crush|rewrite app_comm_cons, Hrewrite5].
    apply H; auto.

    apply ge_cons; auto.
    apply ge_subst_decl; auto.
    inversion H2; subst.
    apply ge_lt_n_decl with (n:=1); auto.
    apply ge_subst_decl; auto.
    inversion H3; subst;
    apply ge_lt_n_decl with (n:=1); auto.
    crush.
    crush.
    apply ge_cast; [crush|].
    apply ge_shift_type; auto.
    crush.

    

    assert (Hrewrite1 : (struct (d1' [inc i 1]ljump_d n) (d2' [inc i 1]ljump_d n)) = ((struct d1' d2') [i] ljump_t n));
      [auto|rewrite Hrewrite1].
    assert (Hrewrite2 : (struct (d1 [inc i 1]ljump_d n) (d2 [inc i 1]ljump_d n)) = ((struct d1 d2) [i] ljump_t n));
      [auto|rewrite Hrewrite2].
    rewrite lshift_ljump_type.
    assert (Hrewrite3 : (c_ 0) = (c_ 0 [inc i 1] ljump_p n));
      [crush; destruct (Nat.ltb_lt 0 (length G1 +1)) as [Htemp Hltb1]; clear Htemp;
       rewrite Hltb1; crush|rewrite Hrewrite3].
    assert (Hrewrite4 : (((c_ 0) [inc i 1]ljump_p n) cast ((struct d1' d2' lshift_t 1) [inc i 1]ljump_t n)) =
                        (((c_ 0) cast ((struct d1' d2' lshift_t 1))) [inc i 1] ljump_p n)); [auto|rewrite Hrewrite4].
    rewrite <- ljump_subst_decl.
    rewrite <- ljump_subst_decl.
    assert (Hrewrite5 :((struct d1 d2 [i]ljump_t n) :: (G1 [dec i 1]ljump_e n)) =
                       (((struct d1 d2) :: G1) [dec (inc i 1) 1] ljump_e n));
      [crush|rewrite app_comm_cons, Hrewrite5].
    apply H0; auto.

    apply ge_cons; auto.
    apply ge_subst_decl; auto.
    inversion H2; subst.
    apply ge_lt_n_decl with (n:=1); auto.
    apply ge_subst_decl; auto.
    inversion H3; subst;
    apply ge_lt_n_decl with (n:=1); auto.
    crush.
    crush.
    apply ge_cast; [crush|].
    apply ge_shift_type; auto.
    crush.

    apply sd_lower; fold left_jump_t.
    apply H; auto.
    inversion H2; auto.
    inversion H1; auto.
    admit. (*obvious*)

    apply sd_upper; fold left_jump_t.
    apply H; auto.
    inversion H1; auto.
    inversion H2; auto.
    admit. (*obvious*)
  Admitted.

  

  Definition beq_ty_label (l1 l2 : ty_label) : bool :=
    match l1, l2 with
      | Material n, Material m => n =? m
      | Shape n, Shape m => n =? m
      | _, _ => false
    end.

  Lemma beq_ty_label_refl :
    forall l, beq_ty_label l l = true.
  Proof.
    intro l; destruct l as [n|n]; intros; crush; 
    rewrite <- beq_nat_refl; auto.
  Qed.
  
  Definition beq_label (l1 l2 : label) : bool :=
    match l1, l2 with
      | l_type l1', l_type l2' => beq_ty_label l1' l2'
      | l_def n, l_def m => n =? m
      | _, _ => false
    end.

  Lemma beq_label_refl :
    forall l, beq_label l l = true.
  Proof.
    intro l; destruct l as [n|l']; crush;
    [rewrite <- beq_nat_refl; auto|].
    
    apply beq_ty_label_refl.
  Qed.

  Lemma beq_ty_label_eq :
    forall l1 l2, beq_ty_label l1 l2 = true -> l1 = l2.
  Proof.
    intros; destruct l1, l2; crush.
    symmetry in H; apply beq_nat_eq in H; auto.
    symmetry in H; apply beq_nat_eq in H; auto.
  Qed.

  Lemma beq_label_eq :
    forall l1 l2, beq_label l1 l2 = true -> l1 = l2.
  Proof.
    intros; destruct l1; destruct l2; crush.
    symmetry in H; apply beq_nat_eq in H; auto.
    apply beq_ty_label_eq in H; subst; auto.
  Qed.

  Inductive eq_upper : env -> ty -> ty -> Prop :=
  | equ_top : forall G, eq_upper G top top
  | equ_bot : forall G, eq_upper G bot bot
  | equ_upp : forall G x l u t, G vdash x ni (type l ext u) ->
                          eq_upper G u t ->
                          eq_upper G (sel x l) t
  | equ_low : forall G x l t, G vdash x ni (type l sup t) ->
                         eq_upper G (sel x l) top
  | equ_str : forall G ds, eq_upper G (str ds) (str ds).

  Inductive eq_lower : env -> ty -> ty -> Prop :=
  | eql_top : forall G, eq_lower G top top
  | eql_bot : forall G, eq_lower G bot bot
  | eql_low : forall G x l s t, G vdash x ni (type l sup s) ->
                           eq_lower G s t ->
                           eq_lower G (sel x l) t
  | eql_upp : forall G x l t, G vdash x ni (type l ext t) ->
                         eq_lower G (sel x l) bot
  | eql_str : forall G ds, eq_lower G (str ds) (str ds).

  Hint Constructors eq_lower eq_upper.

  Lemma eq_upper_dec :
    forall G t t', eq_upper G t t' -> (t' = top) \/ (t' = bot) \/ (exists ds, t' = str ds).
  Proof.
    intros G t t' Heq; induction Heq; intros; auto.
    right; right; exists ds; auto.
  Qed.

  Lemma  sup_top_eq_lower :
    forall G1 t1 t2 G2, G1 vdash t1 <; t2 dashv G2 -> t1 = top -> eq_lower G2 t2 top.
  Proof.
    intros G1 t1 t2 G2 Hsub; induction Hsub; intros; subst; auto.

    inversion H.

    inversion H.

    inversion H.

    apply eql_low with (s:=s); auto.

    inversion H0.

    inversion H0.
  Qed.

  Lemma  sub_bot_eq_upper :
    forall G1 t1 t2 G2, G1 vdash t1 <; t2 dashv G2 -> t2 = bot -> eq_upper G1 t1 bot.
  Proof.
    intros G1 t1 t2 G2 Hsub; induction Hsub; intros; subst; auto.

    inversion H.

    inversion H.

    inversion H.

    inversion H0.

    apply equ_upp with (u:=u); auto.

    inversion H0.
  Qed.

  Lemma eq_lower_top_sub :
    forall G t t', eq_lower G t t' -> t' = top -> forall G2 t2, G2 vdash t2 <; t dashv G.
  Proof.
    intros G t t' Heq; induction Heq; intros; subst; auto.
    
    inversion H.

    apply s_lower with (s:= s); auto.

    inversion H0.

    inversion H.
    
  Qed.

  Lemma eq_upper_bot_sup :
    forall G t t', eq_upper G t t' -> t' = bot -> forall G2 t2, G vdash t <; t2 dashv G2.
  Proof.
    intros G t t' Heq; induction Heq; intros; subst; auto.
    
    inversion H.

    apply s_upper with (u:= u); auto.

    inversion H0.

    inversion H.
    
  Qed.
    
  Lemma sub_eq_upper_sub_ty :
    forall G1 t1 t,  eq_upper G1 t t1 -> forall t2 G2, G1 vdash t1 <; t2 dashv G2 -> G1 vdash t <; t2 dashv G2.
  Proof.
    intros G1 t1 t Heq; induction Heq; intros; auto.

    apply s_upper with (u:=u); auto.
    
    assert (eq_lower G2 t2 top); [apply (sup_top_eq_lower H0); auto|].
    apply (eq_lower_top_sub H1); auto.
  Qed.
    
  Lemma sub_eq_lower_sub_ty :
    forall G1 t1 t,  eq_lower G1 t t1 -> forall t2 G2, G2 vdash t2 <; t1 dashv G1 -> G2 vdash t2 <; t dashv G1.
  Proof.
    intros G1 t1 t Heq; induction Heq; intros; auto.

    apply s_lower with (s:=s); auto.
    
    assert (eq_upper G2 t2 bot); [apply (sub_bot_eq_upper H0); auto|].
    apply (eq_upper_bot_sup H1); auto.
  Qed.

  Lemma typing_unique :
    forall G x t, G vdash x hasType t -> forall t', G vdash x hasType t' -> t' = t.
  Proof.
    intros.
    inversion H; inversion H0; subst; auto.
    inversion H7; subst.
    
    rewrite H1 in H5; inversion H5; auto.
    
  Qed.

  Lemma has_contains_unique_mutind :
    (forall G x d, G vdash x ni d -> G vdash x wf_v -> G wf_e -> forall d', G vdash x ni d' -> id d' = id d -> d' = d) /\
    (forall G t d, G vdash d cont t -> G vdash t wf_t -> G wf_e -> forall d', G vdash d' cont t -> id d' = id d -> d' = d).
  Proof.
    apply has_contains_mutind; intros.

    inversion H2; subst.
    apply typing_unique with (t:=t) in H4; auto; subst.
    apply H in H5; subst; auto.
    
    
  Qed.
        

  Lemma subtype_transistivity_mutind :
    (forall t2 G1 t1 G2, G1 vdash t1 <; t2 dashv G2 -> (forall t3 G3, G2 vdash t2 <; t3 dashv G3 -> G1 vdash t1 <; t3 dashv G3)) /\
    (forall d2 G1 d1 G2, G1 vdash d1 <;; d2 dashv G2 -> (forall d3 G3, G2 vdash d2 <;; d3 dashv G3 -> G1 vdash d1 <;; d3 dashv G3)) /\
    (forall ds2 G1 ds1 G2, G1 vdash ds1 <;;; ds2 dashv G2 -> (forall ds3 G3, G2 vdash ds2 <;;; ds3 dashv G3 -> G1 vdash ds1 <;;; ds3 dashv G3)).
  Proof.
    apply type_mutind; intros; auto.

    admit.
    

    
    
    inversion H0; subst; auto.
    inversion H1; subst; auto.
    admit.
    admit.
    inversion H1; subst; auto.
    admit.
    apply s_struct.
    apply H with (G2:=(str d)::G2); auto.
    

    apply sub_top_equiv in H; auto.
    apply sub_equiv_top_all; auto.

    inversion H1; subst; auto.
    apply s_arr.
    admit.
    apply H0; auto.
    
  Qed.

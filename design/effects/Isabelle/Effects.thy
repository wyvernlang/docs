
theory Effects
imports String "~~/src/HOL/Library/FSet" List Partial_Function Option
begin

type_synonym resource = string
type_synonym operation = string

type_synonym R = "string list"
type_synonym \<Pi> = "string list"

type_synonym effect = "resource \<times> operation"

(* A variable is a string. *)
type_synonym vname = string

(* A method name is a string. *)
type_synonym mname = string

(* Method declarations and types.\
   Isabelle doesn't have (co-)recursive records, so we must use datatypes here. *)
datatype ty =
    Obj\<^sub>\<sigma> "meth_sig\<^sub>\<sigma> list"
    | ResT  "resource"
and meth_sig\<^sub>\<sigma> =
    Sig\<^sub>\<sigma> "mname \<times> vname \<times> ty \<times> ty \<times> (effect list)"
  
(* Expressions & values. *)
datatype expr =
    MethCall expr mname expr
    | OperCall expr operation expr
    | Var vname
    | Val val
and val =
    New\<^sub>\<sigma> "(meth_sig\<^sub>\<sigma> \<times> expr) list"
    | Res resource
  
(* Common usages. *)
type_synonym meth\<^sub>\<sigma> = "meth_sig\<^sub>\<sigma> \<times> expr"
abbreviation "unit_obj == New\<^sub>\<sigma> []"
abbreviation "unit_ty == Obj\<^sub>\<sigma> []"
abbreviation "this == ''this''"
   


(* Functions for extracting useful information out of a method signature.  *)
      
fun fst :: "('a \<times> 'b) \<Rightarrow> 'a" where "fst (x,y) = x"

(* Get the type of a sequence of \<sigma> = e declarations. *)
fun sigsFromObj :: "(meth_sig\<^sub>\<sigma> \<times> expr) list \<Rightarrow> meth_sig\<^sub>\<sigma> list"
where "sigsFromObj decls = List.map fst decls"

fun methName :: "meth_sig\<^sub>\<sigma> \<Rightarrow> mname"
where "methName (Sig\<^sub>\<sigma> (name,_,_,_,_)) = name"
  
fun argName :: "meth_sig\<^sub>\<sigma> \<Rightarrow> vname"
where "argName (Sig\<^sub>\<sigma> (_,name,_,_,_)) = name"

fun argType :: "meth_sig\<^sub>\<sigma> \<Rightarrow> ty"
where "argType (Sig\<^sub>\<sigma> (_,_,type,_,_)) = type"

fun retType :: "meth_sig\<^sub>\<sigma> \<Rightarrow> ty"
where "retType (Sig\<^sub>\<sigma> (_,_,_,type,_)) = type"

fun declFx :: "meth_sig\<^sub>\<sigma> \<Rightarrow> effect list"
where "declFx (Sig\<^sub>\<sigma> (_,_,_,_,fx)) = fx"

(* Select by name a particular method from a list of methods. *)
fun getMeth :: "(meth_sig\<^sub>\<sigma> \<times> expr) list \<Rightarrow> mname \<Rightarrow> (meth_sig\<^sub>\<sigma> \<times> expr)"
where
  "getMeth ((msig, e) # rest) goal =
        (if ((methName msig) = goal) then (msig, e) else (getMeth rest goal))"

        
        
(* The substitution function. *)
fun sub :: "vname \<Rightarrow> val \<Rightarrow> expr \<Rightarrow> expr"    
where
  "sub v newVal (Var x) =
      (if v = x then Val newVal else Var x)"
| "sub v newVal (MethCall e1 m e2) =
      (MethCall (sub v newVal e1) m (sub v newVal e2))"
| "sub v newVal (OperCall e1 \<pi> e2) =
      (OperCall (sub v newVal e1) \<pi> (sub v newVal e2))"
| "sub _ _ expr =
      expr"

fun subs :: "(vname \<times> val) list \<Rightarrow> expr \<Rightarrow> expr"
where
  "subs [] e = e"
| "subs ( (name, toSub) # rest ) e = subs rest (sub name toSub e)"

        
      
        
(* Typing context. *)
type_synonym ctx = "(vname \<times> ty) list"

fun lookup :: "ctx \<Rightarrow> vname \<Rightarrow> ty"
where "lookup ( (name,t) # rest ) goal = (if (name = goal) then t else (lookup rest goal))"

fun ctxHas :: "vname \<times> ty \<Rightarrow> ctx \<Rightarrow> bool"   (infixl "\<in>\<^sub>\<Gamma>" 60)
where
  "(_,_) \<in>\<^sub>\<Gamma> [] = False"
| "(nameGoal,tyGoal) \<in>\<^sub>\<Gamma> ((n,t) # rest) =
      (if n=nameGoal \<and> t=tyGoal then True else ( (nameGoal, tyGoal) \<in>\<^sub>\<Gamma> rest ))"

(* Small-step semantics. *)

inductive
  small_step :: "expr \<Rightarrow> (expr \<times> effect list) \<Rightarrow> bool" (infix "\<leadsto>" 55)
where
    E_MethCall:
        "\<lbrakk>e\<^sub>1 \<leadsto> (e\<^sub>1', \<epsilon>)\<rbrakk>
          \<Longrightarrow> (MethCall e\<^sub>1 m e\<^sub>2) \<leadsto> (MethCall e\<^sub>1' m e\<^sub>2, \<epsilon>)"
  
  | E_MethCall2:
        "\<lbrakk>e\<^sub>1 = Val (New\<^sub>\<sigma> _); e\<^sub>2 \<leadsto> (e\<^sub>2', \<epsilon>)\<rbrakk>
          \<Longrightarrow> (MethCall e\<^sub>1 m e\<^sub>2) \<leadsto> (MethCall e\<^sub>1 m e\<^sub>2', \<epsilon>)"
      
  | E_MethCall3:
        "\<lbrakk>e\<^sub>1 = Val (New\<^sub>\<sigma> meths); e\<^sub>2 = Val v; getMeth meths m = (sig, bdy)\<rbrakk>
          \<Longrightarrow> (MethCall e\<^sub>1 m e\<^sub>2) \<leadsto> (subs [ ((argName sig), v), (this, (New\<^sub>\<sigma> meths))] bdy
                                    , [])"
          
  | E_OperCall1:
        "\<lbrakk>e\<^sub>1 \<leadsto> (e\<^sub>1', \<epsilon>); \<pi> \<in> \<Pi>\<rbrakk>
          \<Longrightarrow> (OperCall e\<^sub>1 \<pi> e\<^sub>2) \<leadsto> (OperCall e\<^sub>1' \<pi> e\<^sub>2, \<epsilon>)"
          
  | E_OperCall2:
        "\<lbrakk>e\<^sub>1 = Val (Res r); r \<in> R; e\<^sub>2 \<leadsto> (e\<^sub>2', \<epsilon>)\<rbrakk>
          \<Longrightarrow> (OperCall e\<^sub>1 \<pi> e\<^sub>2) \<leadsto> (OperCall e\<^sub>1 \<pi> e\<^sub>2', \<epsilon>)"
          
  | E_OperCall3:
        "\<lbrakk>e\<^sub>1 = Val (Res r); r \<in> R; e\<^sub>2 = Val v\<^sub>2\<rbrakk>
          \<Longrightarrow> (OperCall e\<^sub>1 \<pi> e\<^sub>2) \<leadsto> (unit, [])"
          
          
          

 
(* Judgements for well-formedness of New\<^sub>\<sigma> declarations. *)         
inductive well_formed :: "ctx \<Rightarrow> meth_sig\<^sub>\<sigma> \<Rightarrow> expr \<Rightarrow> bool"
  ("(1_/ \<turnstile>(_ =/ _) OK)" [50,0,50] 50)
where
    \<epsilon>_ValidImpl\<^sub>\<sigma>:
      "\<lbrakk>effect_typing ((y, \<tau>\<^sub>2) # \<Gamma>) e \<tau>\<^sub>3 \<epsilon>\<^sub>3;
        \<sigma> = Sig\<^sub>\<sigma> (_, _, \<tau>\<^sub>2, \<tau>\<^sub>3, \<epsilon>\<^sub>3) \<rbrakk>
        \<Longrightarrow> \<Gamma> \<turnstile> \<sigma> = e OK"

inductive well_formed2 :: "ctx \<Rightarrow> (meth_sig\<^sub>\<sigma> \<times> expr) list \<Rightarrow> bool"
  ("(1_/ \<turnstile>/\<^sub>\<sigma>/ _ OK)" [50,0] 50)
where
    \<epsilon>_ValidImplsBase\<^sub>\<sigma>:
        "\<Gamma> \<turnstile>\<^sub>\<sigma> [] OK"
  | \<epsilon>_ValidImpls\<^sub>\<sigma>:
        "\<lbrakk>\<Gamma> \<turnstile> \<sigma>=e OK; \<Gamma> \<turnstile>\<^sub>\<sigma> rest OK \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>\<sigma> ((\<sigma>,e) # rest) OK"
     
          
          
(* Typing judgements w/ effects. *)
 
inductive effect_typing :: "ctx \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> effect list \<Rightarrow> bool"
  ("(1_/ \<turnstile>/\<^sub>\<epsilon>/ (_ :/ _ with/ _))" [50,0,50,50] 50)
where
    \<epsilon>_Resource:
        "\<lbrakk>r \<in> R\<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>\<epsilon> (Val (Res r)) : (ResT r) with []"
  | \<epsilon>_Var:
        "\<lbrakk> (var,varT) \<in>\<^sub>\<Gamma> ctx \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>\<epsilon> (Var var) : (varT) with []"
         
  | \<epsilon>_NewObj:
          "\<lbrakk>sigs = (sigsFromObj decls); ((this, (Obj\<^sub>\<sigma> sigs)) # \<Gamma>) \<turnstile>\<^sub>\<sigma> decls OK\<rbrakk>
            \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>\<epsilon> (Val (New\<^sub>\<sigma> decls)) : (Obj\<^sub>\<sigma> sigs) with []"  

  | \<epsilon>_OperCall:
        "\<lbrakk>\<Gamma> \<turnstile>\<^sub>\<epsilon> e\<^sub>1 : ResT r with \<epsilon>\<^sub>1; \<Gamma> \<turnstile>\<^sub>\<epsilon> e\<^sub>2 : \<tau>\<^sub>2 with \<epsilon>\<^sub>2; \<pi> \<in> \<Pi> \<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>\<epsilon> OperCall e\<^sub>1 \<pi> e\<^sub>2 : Unit with concat [\<epsilon>\<^sub>1, \<epsilon>\<^sub>2, [(r, \<pi>)]]"
          
  | \<epsilon>_MethCall\<^sub>\<sigma>:
        "\<lbrakk>\<Gamma> \<turnstile>\<^sub>\<epsilon> e\<^sub>1 : (Obj\<^sub>\<sigma> decls) with \<epsilon>\<^sub>1;
          \<Gamma> \<turnstile>\<^sub>\<epsilon> e\<^sub>2 : \<tau>\<^sub>2 with \<epsilon>\<^sub>2;
          msig = Sig\<^sub>\<sigma> (m, _, \<tau>\<^sub>2, \<tau>\<^sub>3, \<epsilon>\<^sub>3)\<rbrakk>
          \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>\<epsilon> MethCall e\<^sub>1 m e\<^sub>2 : \<tau>\<^sub>3 with concat [\<epsilon>\<^sub>1, \<epsilon>\<^sub>2, \<epsilon>\<^sub>3]"
          
          
end

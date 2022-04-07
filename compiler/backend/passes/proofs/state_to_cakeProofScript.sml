(*
  Correctness for compilation from stateLang to CakeML
*)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open stringTheory optionTheory sumTheory pairTheory listTheory alistTheory
     rich_listTheory arithmeticTheory intLib;
open semanticPrimitivesTheory itree_semanticsTheory itree_semanticsPropsTheory;
open pure_miscTheory pure_configTheory stateLangTheory;

val _ = intLib.deprecate_int();

val _ = new_theory "state_to_cakeProof";


(* TODO move *)
Theorem ALOOKUP_MAP_MAP:
  (∀x y. f x = f y ⇒ x = y) ⇒
  ALOOKUP (MAP (λ(a,b). (f a, g b)) l) (f x) =
  ALOOKUP (MAP (λ(a,b). (a, g b)) l) x
Proof
  Induct_on `l` >> rw[] >> PairCases_on `h` >> rw[] >> gvs[]
QED

Theorem OPTREL[simp]:
  (∀R x y. OPTREL R (SOME x) y ⇔ ∃z. y = SOME z ∧ R x z) ∧
  (∀R x y. OPTREL R x (SOME y) ⇔ ∃z. x = SOME z ∧ R z y) ∧
  (∀R y.   OPTREL R NONE y ⇔ y = NONE) ∧
  (∀R x.   OPTREL R x NONE ⇔ x = NONE)
Proof
  simp[OPTREL_SOME] >> rw[OPTREL_def]
QED

Theorem string_le_def[simp]:
  string_le [] s2 = T ∧
  string_le (c1::s1) [] = F ∧
  string_le (c1::s1) (c2::s2) =
    if c1 < c2 then T else
    if c1 = c2 then string_le s1 s2
    else F
Proof
  rw[] >> simp[string_le_def, string_lt_def, char_lt_def]
  >- (Cases_on `s2` >> rw[string_lt_def])
  >- (eq_tac >> rw[] >> simp[])
QED


(******************** Helper functions for itree semantics ********************)

Definition get_ffi_array_def[simp]:
  get_ffi_array (Estep (cenv, cst, ev, ck)) = (
    case store_lookup 0 cst of
    | SOME (W8array ws) => SOME ws
    | _ => NONE) ∧
  get_ffi_array (Effi s conf ws n cenv cst ck) = SOME ws ∧
  get_ffi_array _ = NONE
End

Definition cstep_n_def:
  cstep_n 0 e = e ∧
  cstep_n (SUC n) (Estep st) = cstep_n n (estep st) ∧
  cstep_n _ e = e
End

Theorem cstep_n_alt:
  cstep_n 0 e = e ∧
  cstep_n (SUC n) e = (
    case cstep_n n e of
    | Estep st => estep st
    | e => e)
Proof
  rw[cstep_n_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[cstep_n_def] >> simp[]
QED

Theorem cstep_n_0[simp] = cj 1 cstep_n_def;

Theorem cstep_n_add:
  ∀a b. cstep_n (a + b) e = cstep_n a (cstep_n b e)
Proof
  Induct >> rw[cstep_n_def] >>
  simp[ADD_CLAUSES, cstep_n_alt]
QED

Theorem same_type_refl[simp]:
  same_type stamp stamp
Proof
  Cases_on `stamp` >> rw[same_type_def]
QED


(******************** Compilation relation ********************)

Definition var_prefix_def:
  var_prefix v = "pure_" ++ v
End

Inductive opn_rel:
  opn_rel Add Plus ∧
  opn_rel Sub Minus ∧
  opn_rel Mul Times
End

Inductive opb_rel:
  opb_rel pure_config$Lt ast$Lt ∧
  opb_rel Leq Leq ∧
  opb_rel Gt Gt ∧
  opb_rel Geq Geq
End

Inductive atom_op_rel:
  (opn_rel sopn opn ⇒ atom_op_rel sopn (Opn opn)) ∧
  (opb_rel sopb opb ⇒ atom_op_rel sopb (Opb opb)) ∧
  atom_op_rel Eq Equality ∧
  atom_op_rel Len Strlen ∧
  atom_op_rel StrEq Equality
End

Inductive op_rel:
  op_rel AppOp Opapp ∧
  (atom_op_rel aop op ⇒ op_rel (AtomOp aop) op) ∧
  op_rel Ref AallocFixed ∧
  op_rel Length Alength ∧
  op_rel Sub Asub ∧
  op_rel UnsafeSub Asub_unsafe ∧
  op_rel Update Aupdate ∧
  op_rel UnsafeUpdate Aupdate_unsafe
End


Overload capp = ``λce1 ce2. ast$App Opapp [ce1; ce2]``;
Overload int  = ``λi. ast$Lit $ IntLit i``;
Overload clet = ``λs e1 e2. ast$Let (SOME s) e1 e2``;
Overload ifeq = ``λ(a,b) e1 e2. ast$If (App Equality [a;b]) e1 e2``;
Overload iflt = ``λ(a,b) e1 e2. ast$If (App (Opb Lt) [a;b]) e1 e2``
Overload var  = ``λs. ast$Var $ Short s``;
Overload tt = ``Con (SOME $ Short $ "True") []``;
Overload ff = ``Con (SOME $ Short $ "False") []``;

(*
  if v2 = 0 then 0 else Divide v1 v2
*)
Overload div =
  ``ifeq (var "v2", int 0) (int 0) (App (Opn Divide) [var "v1"; var "v2"])``;

(*
  if v2 = 0 then 0 else Modulo v1 v2
*)
Overload mod =
  ``ifeq (var "v2", int 0) (int 0) (App (Opn Modulo) [var "v1"; var "v2"])``;

(*
  if v2 < 0 then -1 else
  let strlen = LENGTH v1 in
    if v2 < strlen then Ord (Strsub v1 v2) else -1
*)
Overload elem_str =
  ``iflt (var "v2", int 0) (int (-1)) $
    clet "strlen" (App Strlen [var "v1"]) $
    iflt (var "v2", var "strlen")
      (App Ord [App Strsub [var "v1"; var "v2"]])
      (int (-1))``

(*
  let strlen = LENGTH v1 in
  let off = if v2 < 0 then 0 else v2 in
  if off < strlen then
    CopyStrStr v1 off (strlen - off)
    else ""
*)
Overload substring2 =
  ``clet "strlen" (App Strlen [var "v1"]) $
    clet "off" (iflt (var "v2", int 0) (int 0) (var "v2")) $
    iflt (var "off", var "strlen")
      (App CopyStrStr [var "v1"; var "off"; App (Opn Minus) [var "strlen"; var "off"]])
      (Lit $ StrLit "")``;

(*
  λs i l.
    if l < 0 then "" else
      let strlen = LENGTH s in
      let off = if i < 0 then 0 else i in
      if off < strlen then
        let off_l = off + l in
        let end = (if off_l < strlen then off_l else strlen) in
        CopyStrStr s off (end - off)
      else ""
*)
Overload substring3 =
  ``iflt (var "l", int 0) (Lit $ StrLit "") $
    clet "strlen" (App Strlen [var "s"]) $
    clet "off" (iflt (var "i", int 0) (int 0) (var "i")) $
    iflt (var "off", var "strlen") (
      clet "off_l" (App (Opn Plus) [var "off"; var "l"]) $
      clet "end" (iflt (var "off_l", var "strlen") (var "off_l") (var "strlen")) $
      App CopyStrStr [var "s"; var "off"; App (Opn Minus) [var "end"; var "off"]])
      (Lit $ StrLit "")``;

Definition strle_def:
  strle (n : num) s1 s2 =
    let len1 = LENGTH s1; len2 = LENGTH s2 in
    if len1 ≤ n then T else if len2 ≤ n then F else
    let o1 = ORD (EL n s1); o2 = ORD (EL n s2) in
    if o1 < o2 then T
    else if o1 = o2 then strle (n + 1) s1 s2
    else F
Termination
  WF_REL_TAC `measure (λ(n,s1,_). LENGTH s1 - n)`
End

Definition strle_v_def:
  strle_v env =
    Recclosure env ["strle", "n",
      Fun "s1" $ Fun "s2" $
      clet "len1" (App Strlen [var "s1"]) $
      clet "len2" (App Strlen [var "s2"]) $
      If (App (Opb Leq) [var "len1"; var "n"]) tt $
      If (App (Opb Leq) [var "len2"; var "n"]) ff $
      clet "o1" (App Ord [App Strsub [var "s1"; var "n"]]) $
      clet "o2" (ast$App Ord [App Strsub [var "s2"; var "n"]]) $
      iflt (var "o1", var "o2") tt $
      ifeq (var "o1", var "o2")
        (capp (capp (capp (var "strle") (App (Opn Plus) [var "n"; int 1]))
                            (var "s1")) (var "s2"))
        ff]
      "strle"
End

(*
  let len = (if v1 < 0 then 0 else v1) in Aalloc v1 v2
*)
Overload alloc =
  ``clet "len" (iflt (var "v1", int 0) (int 0) (var "v1")) $
    App Aalloc [var "len"; var "v2"]``;

(*
    let len0 = Int (ffi_array[0]) in
    let len1 = Int (ffi_array[1]) in
    let len = (len1 * 256) + len0 in
    let len = (if 4094 < len then 4094 else len) in
    CopyAw8Str ffi_array 2 len
*)
Overload ffi =
  ``clet "len0" (App (WordToInt W8) [(App Aw8sub_unsafe [var "ffi_array"; int 0])]) $
    clet "len1" (App (WordToInt W8) [(App Aw8sub_unsafe [var "ffi_array"; int 1])]) $
    clet "len" (App (Opn Plus) [App (Opn Times) [var "len1"; int 256]; var "len0"]) $
    clet "len" (iflt (int 4094, var "len") (int 4094) (var "len")) $
    App CopyAw8Str [var "ffi_array"; int 2; var "len"]``;

(* TODO list_to_v exists in CakeML - is there a list_to_exp already? *)
(* right to left evaluation should hold for this too *)
Definition list_to_exp_def:
  list_to_exp [] = Con (SOME $ Short "[]") [] ∧
  list_to_exp (e::es) = Con (SOME $ Short "::") [e; list_to_exp es]
End

Definition pat_row_def:
  pat_row sv cn vs =
    Pas ((if cn = "" then Pcon NONE else Pcon (SOME $ Short cn))
          (MAP (Pvar o var_prefix) vs)) (var_prefix sv)
End

Inductive compile_rel:
[~IntLit:]
  compile_rel cnenv (App (AtomOp (Lit $ Int i)) []) (Lit $ IntLit i) ∧

[~StrLit:]
  compile_rel cnenv (App (AtomOp (Lit $ Str s)) []) (Lit $ StrLit s) ∧

[~Tuple:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (Cons "") ses) (Con NONE ces)) ∧

[~Constructor:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH ses ∧ cn ≠ ""
    ⇒ compile_rel cnenv (App (Cons cn) ses) (Con (SOME $ Short cn) ces)) ∧

[~Var:]
  compile_rel cnenv (stateLang$Var v) (Var (Short (var_prefix v))) ∧

[~App:]
  (op_rel sop cop ∧ LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App sop ses) (App cop ces)) ∧

[~DivModElemSubstring2:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else aop = Substring ∧ rest = substring2)
    ⇒ compile_rel cnenv (App (AtomOp aop) [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 rest)) ∧

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces
    ⇒ compile_rel cnenv (App (AtomOp Concat) ses) (App Strcat [list_to_exp ces])) ∧

(*TODO
[~Implode:]
*)

[~Substring3:]
  (LIST_REL (compile_rel cnenv) [se1;se2;se3] [ce1;ce2;ce3]
    ⇒ compile_rel cnenv (App (AtomOp Substring) [se1; se2; se3])
                        (clet "l" ce3 $ clet "i" ce2 $ clet "s" ce1 substring3)) ∧

(* TODO
[~StrLt:]
[~StrLeq:]
[~StrGt:]
[~StrGeq:]
*)

[~Alloc:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (App Alloc [se1;se2])
                        (clet "v2" ce2 $ clet "v1" ce1 alloc)) ∧

[~FFI:]
  (compile_rel cnenv se ce ∧ ch ≠ ""
    ⇒ compile_rel cnenv (App (FFI ch) [se])
                        (clet "s" ce $
                          Let NONE (App (FFI ch) [var "s"; var "ffi_array"]) $ ffi)) ∧

[~Lam:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (stateLang$Lam (SOME x) se) (Fun (var_prefix x) ce)) ∧

[~Letrec:]
  (LIST_REL
      (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns ∧
   ALL_DISTINCT (MAP FST cfuns) ∧
   compile_rel cnenv se ce
    ⇒ compile_rel cnenv (stateLang$Letrec sfuns se) (ast$Letrec cfuns ce)) ∧

[~Let:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (Let (SOME x) se1 se2) (Let (SOME $ var_prefix x) ce1 ce2)) ∧

[~If:]
  (LIST_REL (compile_rel cnenv) [se;se1;se2] [ce;ce1;ce2]
    ⇒ compile_rel cnenv (If se se1 se2) (If ce ce1 ce2)) ∧

[~Case:]
  (compile_rel cnenv se ce ∧
   EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
   LIST_REL
    (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row sv cn vs)
    scss ccss
    ⇒ compile_rel cnenv (Case se sv scss) (Mat ce ccss)) ∧

[~TupleCase:]
  (compile_rel cnenv se ce ∧ compile_rel cnenv sce cce ∧ ALL_DISTINCT vs
    ⇒ compile_rel cnenv (Case se sv ["",vs,sce]) (Mat ce [(pat_row sv "" vs, cce)])) ∧

[~Raise:]
  (compile_rel cnenv se ce
    ⇒ compile_rel cnenv (Raise se) (Raise ce)) ∧

[~Handle:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2
    ⇒ compile_rel cnenv (Handle se1 x se2) (Handle ce1 [(Pvar $ var_prefix x, ce2)]))
End

Definition prim_types_ok_def:
  prim_types_ok senv ⇔
    (* booleans *)
      ALOOKUP senv "True" = SOME (TypeStamp "True" bool_type_num, 0n) ∧
      ALOOKUP senv "False" = SOME (TypeStamp "False" bool_type_num, 0n) ∧
    (* lists *)
      ALOOKUP senv "::" = SOME (TypeStamp "::" list_type_num, 2n) ∧
      ALOOKUP senv "[]" = SOME (TypeStamp "[]" list_type_num, 0n) ∧
    (* subscript exception *)
      ALOOKUP senv "Subscript" = SOME (subscript_stamp, 0n)
End

Definition cnenv_rel_def:
  cnenv_rel senv cenv ⇔
    prim_types_ok senv ∧
    (* unique stamp for each cn *)
    (∀stamp cn1 cn2 ar1 ar2.
      ALOOKUP senv cn1 = SOME (stamp, ar1) ∧ ALOOKUP senv cn2 = SOME (stamp, ar2)
     ⇒ cn1 = cn2) ∧
    ∀cn tyid ar. ALOOKUP senv cn = SOME (tyid,ar) ⇒
      cn ≠ "" ∧ (* no tuples *)
      nsLookup cenv (Short cn) = SOME (ar,tyid) ∧ (* matching type/arity *)
      (∀cn' id. tyid = TypeStamp cn' id ⇒ cn' = cn) (* type stamp matches cn *)
End

Definition env_ok_def:
  env_ok env ⇔
    nsLookup env.v (Short "ffi_array") = SOME (semanticPrimitives$Loc 0)
    (* TODO add in string operations and implode *)
End

Inductive v_rel:
[~Tuple:]
  (LIST_REL (v_rel cnenv) svs cvs
    ⇒ v_rel cnenv (Constructor "" svs) (Conv NONE cvs)) ∧

[~Constructor:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH svs ∧ cn ≠ ""
    ⇒ v_rel cnenv (Constructor cn svs) (Conv (SOME tyid) cvs)) ∧

[~Closure:]
  (compile_rel cnenv se ce ∧ env_rel cnenv senv cenv ∧ env_ok cenv
   ⇒ v_rel cnenv (Closure (SOME sx) senv se) (Closure cenv (var_prefix sx) ce)) ∧

[~Recclosure:]
  (compile_rel cnenv se ce ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   LIST_REL (λ(sv,se) (cv,cx,ce).
        var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧ compile_rel cnenv se' ce)
      sfuns cfuns ∧
   ALL_DISTINCT (MAP FST cfuns)
   ⇒ v_rel cnenv (stateLang$Recclosure sfuns senv sx)
                 (Recclosure cenv cfuns (var_prefix sx))) ∧

[~IntLit:]
  v_rel cnenv (Atom $ Int i) (Litv $ IntLit i) ∧

[~StrLit:]
  v_rel cnenv (Atom $ Str s) (Litv $ StrLit s) ∧

[~Loc:]
  v_rel cnenv (Atom $ Loc n) (Loc (n + 1)) ∧ (* leave space for FFI array *)

[~env_rel:]
  (cnenv_rel cnenv cenv.c ∧
   (∀sx sv.
      ALOOKUP senv sx = SOME sv ⇒
      ∃cv. nsLookup cenv.v (Short $ var_prefix sx) = SOME cv ∧ v_rel cnenv sv cv)
    ⇒ env_rel cnenv senv cenv)
End

Theorem env_rel_def = cj 2 v_rel_cases;
Theorem v_rel_cases = cj 1 v_rel_cases;

Theorem v_rel_def[simp] = [
  “v_rel cnenv (Constructor cn svs) cv”,
  “v_rel cnenv (Closure sx senv se) cv”,
  “v_rel cnenv (Recclosure sfuns senv sx) cv”,
  “v_rel cnenv (Atom a) cv”] |>
  map (GEN_ALL o SIMP_CONV (srw_ss()) [Once v_rel_cases, SF CONJ_ss]) |>
  LIST_CONJ;

Definition list_to_cont_def:
  list_to_cont env [] = [] ∧
  list_to_cont env (e::es) =
    (Ccon (SOME $ Short "::") [] [e], env) :: (list_to_cont env es)
End

Inductive cont_rel:
  cont_rel cnenv [] [] ∧

[~TupleK:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (Cons "") svs ses :: sk)
                     ((Ccon NONE cvs ces, cenv) :: ck)) ∧

[~ConsK:]
  (LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   ALOOKUP cnenv cn = SOME (tyid,ar) ∧
   ar = LENGTH ses + LENGTH svs + 1 ∧ cn ≠ "" ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (Cons cn) svs ses :: sk)
                     ((Ccon (SOME $ Short cn) cvs ces, cenv) :: ck)) ∧

[~AppK:]
  (op_rel sop cop ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   LIST_REL (compile_rel cnenv) ses ces ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv sop svs ses :: sk)
                     ((Capp cop cvs ces, cenv) :: ck)) ∧


[~TwoArgs1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else aop = Substring ∧ rest = substring2)
    ⇒ cont_rel cnenv (AppK senv (AtomOp aop) [] [se1] :: sk)
                     ((Clet (SOME "v2") (clet "v1" ce1 rest), cenv) :: ck)) ∧

[~TwoArgs2:]
  (nsLookup cenv.v (Short "v2") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   (if aop = Div then rest = div
    else if aop = Mod then rest = mod
    else if aop = Elem then rest = elem_str
    else aop = Substring ∧ rest = substring2)
    ⇒ cont_rel cnenv (AppK senv (AtomOp aop) [sv2] [] :: sk)
                     ((Clet (SOME "v1") rest, cenv) :: ck)) ∧

[~Alloc1:]
  (compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv Alloc [] [se1] :: sk)
                     ((Clet (SOME "v2") (clet "v1" ce1 alloc), cenv) :: ck)) ∧

[~Alloc2:]
  (nsLookup cenv.v (Short "v2") = SOME cv2 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv Alloc [sv2] [] :: sk)
                     ((Clet (SOME "v1") alloc, cenv) :: ck)) ∧

[~Concat:]
  (LIST_REL (compile_rel cnenv) ses ces ∧
   LIST_REL (v_rel cnenv) svs cvs ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
  ⇒ cont_rel cnenv
    (AppK senv (AtomOp Concat) svs ses :: sk)
    ((Ccon (SOME $ Short "::") [list_to_v cvs] [], cenv)
        :: list_to_cont cenv ces ++ [Capp Strcat [] [], cenv] ++ ck)) ∧

(*TODO
[~Implode:]
*)

[~Substring3_1:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [] [se2;se1] :: sk)
        ((Clet (SOME "l") (clet "i" ce2 $ clet "s" ce1 substring3), cenv) :: ck)) ∧

[~Substring3_2:]
  (nsLookup cenv.v (Short "l") = SOME cv3 ∧
   v_rel cnenv sv3 cv3 ∧ compile_rel cnenv se1 ce1 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv3] [se1] :: sk)
                     ((Clet (SOME "i") (clet "s" ce1 substring3), cenv) :: ck)) ∧

[~Substring3_3:]
  (nsLookup cenv.v (Short "l") = SOME cv3 ∧ nsLookup cenv.v (Short "i") = SOME cv2 ∧
   v_rel cnenv sv3 cv3 ∧ v_rel cnenv sv2 cv2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (AppK senv (AtomOp Substring) [sv2;sv3] [] :: sk)
                      ((Clet (SOME "s") substring3, cenv) :: ck)) ∧

(* TODO
[~StrLt:]
[~StrLeq:]
[~StrGt:]
[~StrGeq:]
*)

[~FFI:]
  (cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧ ch ≠ ""
    ⇒ cont_rel cnenv (AppK senv (FFI ch) [] [] :: sk)
                     ((Clet (SOME "s") $
                        Let NONE (App (FFI ch) [var "s"; var "ffi_array"]) $ ffi
                       , cenv) :: ck)) ∧

[~LetK:]
  (compile_rel cnenv se ce ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (LetK senv (SOME x) se :: sk)
                     ((Clet (SOME $ var_prefix x) ce, cenv) :: ck)) ∧

[~IfK:]
  (compile_rel cnenv se1 ce1 ∧ compile_rel cnenv se2 ce2 ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (IfK senv se1 se2 :: sk)
                     ((Cif ce1 ce2, cenv) :: ck)) ∧

[~CaseK:]
  (EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
    ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
   LIST_REL
    (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row sv cn vs)
    scss ccss ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   (ccont ≠ Cmat ⇒ ccont = Cmat_check)
    ⇒ cont_rel cnenv (CaseK senv sv scss :: sk)
                     ((ccont ccss bind_exn_v, cenv) :: ck)) ∧

[~TupleCaseK:]
  (compile_rel cnenv se ce ∧ compile_rel cnenv sce cce ∧ ALL_DISTINCT vs ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv ∧
   (ccont ≠ Cmat ⇒ ccont = Cmat_check)
    ⇒ cont_rel cnenv (CaseK senv sv ["",vs,sce] :: sk)
                     ((ccont [(pat_row sv "" vs, cce)] bind_exn_v, cenv) :: ck)) ∧

[~RaiseK:]
  (cont_rel cnenv sk ck
    ⇒ cont_rel cnenv (RaiseK :: sk) ((Craise, cenv) :: ck)) ∧

[~HandleK:]
  (compile_rel cnenv se ce ∧
   cont_rel cnenv sk ck ∧ env_rel cnenv senv cenv ∧ env_ok cenv
    ⇒ cont_rel cnenv (HandleK senv x se :: sk)
                     ((Chandle [(Pvar $ var_prefix x, ce)], cenv) :: ck))
End

Definition state_rel_def:
  state_rel cnenv sst (W8array ws :: cst) = (
    (LENGTH ws = max_FFI_return_size) ∧
    LIST_REL (λs c.  ∃cs. c = Varray cs ∧ LIST_REL (v_rel cnenv) s cs) sst cst) ∧
  state_rel cnenv sst _ = F
End

Theorem state_rel:
  state_rel cnenv sst cst ⇔
    ∃ws cst'. cst = W8array ws :: cst' ∧ LENGTH ws = max_FFI_return_size ∧
      LIST_REL (λs c. ∃cs. c = Varray cs ∧ LIST_REL (v_rel cnenv) s cs) sst cst'
Proof
  rw[DefnBase.one_line_ify NONE state_rel_def] >>
  TOP_CASE_TAC >> simp[] >> TOP_CASE_TAC >> simp[]
QED

Inductive step_rel:
  (compile_rel cnenv se ce ∧ cont_rel cnenv sk ck ∧
   env_rel cnenv senv cenv ∧ state_rel cnenv sst cst ∧ env_ok cenv
    ⇒ step_rel (Exp senv se, SOME sst, sk) (Estep (cenv, cst, Exp ce, ck))) ∧

  (v_rel cnenv sv cv ∧ cont_rel cnenv sk ck ∧ state_rel cnenv sst cst
    ⇒ step_rel (Val sv, SOME sst, sk) (Estep (cenv, cst, Val cv, ck))) ∧

  (v_rel cnenv sv cv ∧ cont_rel cnenv sk ck ∧ state_rel cnenv sst cst
    ⇒ step_rel (Exn sv, SOME sst, sk) (Estep (cenv, cst, Exn cv, ck))) ∧

  (cont_rel cnenv sk ck ∧ state_rel cnenv sst cst ∧
   ws1 = MAP (λc. n2w $ ORD c) (EXPLODE conf) ∧
   store_lookup 0 cst = SOME $ W8array ws2 ∧ s ≠ ""
    ⇒ step_rel (Action s conf, SOME sst, sk)
               (Effi s ws1 ws2 0 cenv' cst ((Clet NONE ffi, cenv) :: ck)))
End


(******************** Results ********************)

(********** Useful shorthands **********)

Definition get_ffi_ch_def[simp]:
  get_ffi_ch (ast$FFI ch) = SOME ch ∧
  get_ffi_ch _ = NONE
End

Definition get_ffi_args_def[simp]:
  get_ffi_args [Litv (StrLit conf); Loc lnum] = SOME (conf, lnum) ∧
  get_ffi_args _ = NONE
End

Theorem capplication_thm:
  ∀op env s vs c.
    application op env s vs c =
    if op = Opapp then
      case do_opapp vs of
      | NONE => Etype_error
      | SOME (env,e) => Estep (env,s,Exp e,c)
    else case get_ffi_ch op of
    | SOME n => (
      case get_ffi_args vs of
      | SOME (conf, lnum) => (
          case store_lookup lnum s of
            SOME (W8array ws) =>
              if n = "" then Estep (env, s, Val $ Conv NONE [], c)
              else Effi n (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env s c
          | _ => Etype_error)
      | NONE => Etype_error)
    | NONE => (
      case do_app s op vs of
      | NONE => Etype_error
      | SOME (v1,Rval v') => return env v1 v' c
      | SOME (v1,Rraise v) => Estep (env,v1,Exn v,c))
Proof
  rw[application_thm] >> simp[]
  >- rpt (TOP_CASE_TAC >> gvs[]) >>
  Cases_on `op` >> gvs[]
QED

val creturn_def       = itree_semanticsTheory.return_def;
val cpush_def         = itree_semanticsTheory.push_def;
val ccontinue_def     = itree_semanticsTheory.continue_def;
val cexn_continue_def = itree_semanticsTheory.exn_continue_def;
val cstep_ss          = simpLib.named_rewrites "cstep_ss" [
                         creturn_def, cpush_def, ccontinue_def, cexn_continue_def,
                         capplication_thm, estep_def, cstep_n_def];
val cstep             = SF cstep_ss;

val scontinue_def     = stateLangTheory.continue_def;
val spush_def         = stateLangTheory.push_def;
val svalue_def        = stateLangTheory.value_def;
val serror_def        = stateLangTheory.error_def;
val sapplication_def  = stateLangTheory.application_def;
val sreturn_def       = stateLangTheory.return_def;
val sstep_ss          = simpLib.named_rewrites "sstep_ss" [
                         scontinue_def, spush_def, svalue_def, serror_def,
                         sapplication_def, sreturn_def, step_def,
                         stateLangTheory.get_atoms_def];
val sstep             = SF sstep_ss;

val qrefine = Q.REFINE_EXISTS_TAC;

val qexists0 = qexists_tac `0`;


(********** Lemmmas **********)

Theorem get_atoms_SOME[simp]:
  ∀l as. get_atoms l = SOME as ⇔ l = MAP Atom as
Proof
  Induct >> rw[get_atoms_def] >> Cases_on `as` >> gvs[] >>
  Cases_on `h` >> gvs[get_atoms_def] >> eq_tac >> rw[]
QED

Theorem num_args_ok_0:
  num_args_ok op 0 ⇔
    (∃s. op = Cons s) ∨ (∃aop. op = AtomOp aop) ∨ (op = Ref)
Proof
  Cases_on `op` >> gvs[num_args_ok_def]
QED

Theorem v_to_list_list_to_v[simp]:
  v_to_list (list_to_v l) = SOME l
Proof
  Induct_on `l` >> rw[list_to_v_def, v_to_list_def]
QED

Theorem nsLookup_nsBind_var_prefix[simp]:
  nsLookup (nsBind (var_prefix n) v e) (Short (var_prefix n')) =
    if n = n' then SOME v else nsLookup e (Short (var_prefix n'))
Proof
  IF_CASES_TAC >> gvs[] >> simp[var_prefix_def]
QED

Theorem nsOptBind_SOME[simp]:
  nsOptBind (SOME x) = nsBind x
Proof
  rw[FUN_EQ_THM, namespaceTheory.nsOptBind_def]
QED

Triviality cstep_Exn_over_list_to_cont:
  ∀es cenv cst cv cenv' env ck'.
  cstep_n (LENGTH es) (Estep (cenv,cst,Exn cv, (list_to_cont env es ++ ck'))) =
        (Estep (cenv,cst,Exn cv,ck'))
Proof
  Induct >> rw[list_to_cont_def] >> simp[cstep] >> CASE_TAC >> gvs[]
QED

Theorem list_to_cont_APPEND:
  list_to_cont env (a ++ b) = list_to_cont env a ++ list_to_cont env b
Proof
  Induct_on `a` >> rw[list_to_cont_def]
QED

Theorem cstep_list_to_exp:
  ∀ces cnenv cenv cst ck. cnenv_rel cnenv cenv.c ⇒
    ∃n. cstep_n n (Estep (cenv,cst,Exp (list_to_exp ces), ck)) =
          Estep (cenv,cst,Val (Conv (SOME (TypeStamp "[]" 1)) []),
                 list_to_cont cenv (REVERSE ces) ++ ck)
Proof
  Induct >> rw[] >> gvs[env_ok_def] >> simp[list_to_exp_def, list_to_cont_def]
  >- (
    qrefine `SUC n` >> simp[cstep, do_con_check_def, build_conv_def] >>
    `nsLookup cenv.c (Short "[]") = SOME (0, TypeStamp "[]" 1)` by
      gvs[cnenv_rel_def, prim_types_ok_def, list_type_num_def] >>
    simp[] >> qexists0 >> simp[]
    ) >>
  qrefine `SUC n` >> simp[cstep, do_con_check_def, build_conv_def] >>
  `nsLookup cenv.c (Short "::") = SOME (2, TypeStamp "::" 1)` by
    gvs[cnenv_rel_def, prim_types_ok_def, list_type_num_def] >>
  simp[] >>
  last_x_assum $ drule_all_then assume_tac >>
  pop_assum $ qspecl_then
    [`cst`,`(Ccon (SOME (Short "::")) [] [h],cenv)::ck`] assume_tac >> gvs[] >>
  qrefine `m + n` >> simp[cstep_n_add] >>
  qexists0 >> simp[list_to_cont_APPEND, list_to_cont_def]
QED

Theorem step_Case_no_error:
  (∀n st k. step_n n (Val sv,sst,CaseK senv v scss::sk) ≠ (Error,st,k))
  ⇒ ∃cn vs pvs se.
      sv = Constructor cn vs ∧
      ALOOKUP scss cn = SOME (pvs, se) ∧
      LENGTH pvs = LENGTH vs
Proof
  Induct_on `scss` >> rw[] >- (qexists_tac `1` >> simp[sstep]) >>
  pop_assum $ qspec_then `SUC n` $ mp_tac o GEN_ALL >> rw[step_n_SUC, sstep] >>
  `∃cn vs. sv = Constructor cn vs` by (
    CCONTR_TAC >> gvs[] >> PairCases_on `h` >> Cases_on `sv` >> gvs[sstep] >>
    pop_assum mp_tac >> simp[] >> qexists0 >> simp[]) >>
  rw[] >> last_x_assum mp_tac >> PairCases_on `h` >> simp[sstep] >>
  TOP_CASE_TAC >> gvs[]
  >- (disch_then $ qspec_then `0` mp_tac >> simp[])
  >- (disch_then $ qspec_then `0` mp_tac >> simp[]) >>
  TOP_CASE_TAC >> simp[] >>  TOP_CASE_TAC >> gvs[] >> qexists0 >> simp[]
QED

Theorem pats_bindings_MAP_Pvar[simp]:
  ∀vs f l. pats_bindings (MAP (Pvar o f) vs) l = REVERSE (MAP f vs) ++ l
Proof
  Induct >> rw[astTheory.pat_bindings_def]
QED

Theorem pat_bindings_pat_row[simp]:
  ∀vs cn v l.
    pat_bindings (pat_row v cn vs) l = REVERSE (MAP var_prefix (v::vs)) ++ l
Proof
  Induct >> rw[pat_row_def, astTheory.pat_bindings_def] >> simp[MAP_REVERSE]
QED

Theorem var_prefix_11[simp]:
  var_prefix a = var_prefix b ⇔ a = b
Proof
  rw[var_prefix_def]
QED

Triviality ALL_DISTINCT_pat_bindings[simp]:
  ALL_DISTINCT (REVERSE (MAP var_prefix vs) ++ [var_prefix v]) ⇔
  ¬MEM v vs ∧ ALL_DISTINCT vs
Proof
  rw[ALL_DISTINCT_APPEND, MEM_MAP] >> eq_tac >> rw[]
  >- (drule ALL_DISTINCT_MAP >> simp[])
  >- (irule ALL_DISTINCT_MAP_INJ >> simp[])
QED

Theorem state_rel_store_lookup:
  state_rel cnenv sst cst ⇒
  OPTREL (λs c. ∃cs. c = Varray cs ∧ LIST_REL (v_rel cnenv) s cs)
    (oEL n sst) (store_lookup (n + 1) cst)
Proof
  rw[state_rel] >> rw[oEL_THM, store_lookup_def] >> gvs[LIST_REL_EL_EQN] >>
  gvs[ADD1] >> first_x_assum drule >> strip_tac >> simp[GSYM ADD1]
QED

Theorem store_lookup_assign_Varray:
  store_lookup n st = SOME (Varray vs) ⇒
  store_assign n (Varray (LUPDATE e i vs)) st =
  SOME $ LUPDATE (Varray (LUPDATE e i vs)) n st
Proof
  rw[store_lookup_def, store_assign_def, store_v_same_type_def]
QED


(***** cnenv_rel / env_rel / env_ok *****)

Theorem env_rel_lookup:
  ∀v sx cnenv senv cenv.
    env_rel cnenv senv cenv ∧
    ALOOKUP senv v = SOME sx
  ⇒ ∃cx. nsLookup cenv.v (Short (var_prefix v)) = SOME cx ∧ v_rel cnenv sx cx
Proof
  rw[env_rel_def]
QED

Theorem env_rel_check:
  ∀cn tyid ar cnenv senv cenv.
    env_rel cnenv senv cenv ∧
    ALOOKUP cnenv cn = SOME (tyid, ar) ∧ cn ≠ ""
  ⇒ do_con_check cenv.c (SOME (Short cn)) ar
Proof
  rw[env_rel_def, cnenv_rel_def, do_con_check_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem cnenv_rel_list_type:
  cnenv_rel cnenv cenv.c ⇒
    nsLookup cenv.c (Short "[]") = SOME (0,TypeStamp "[]" 1) ∧
    nsLookup cenv.c (Short "::") = SOME (2,TypeStamp "::" 1) ∧
    do_con_check cenv.c (SOME (Short "[]")) 0 ∧
    do_con_check cenv.c (SOME (Short "::")) 2 ∧
    build_conv cenv.c (SOME (Short "[]")) [] =
      SOME (Conv (SOME (TypeStamp "[]" 1)) []) ∧
    ∀a b. build_conv cenv.c (SOME (Short "::")) [a;b] =
            SOME (Conv (SOME (TypeStamp "::" 1)) [a;b])
Proof
  rw[cnenv_rel_def, prim_types_ok_def] >>
  rw[do_con_check_def, build_conv_def] >> gvs[list_type_num_def] >>
  res_tac >> simp[]
QED

Theorem env_rel_build:
  ∀vs cn tyid cnenv senv cenv.
    env_rel cnenv senv cenv ∧
    ALOOKUP cnenv cn = SOME (tyid, LENGTH vs) ∧ cn ≠ ""
  ⇒ build_conv cenv.c (SOME (Short cn)) vs = SOME (Conv (SOME tyid) vs)
Proof
  rw[env_rel_def, cnenv_rel_def, build_conv_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem env_ok_nsBind[simp]:
  env_ok (cenv with v := nsBind (var_prefix x) v cenv.v) ⇔ env_ok cenv
Proof
  rw[env_ok_def] >> simp[Once var_prefix_def]
QED

Theorem env_ok_nsBind_alt:
  env_ok cenv ∧ x ≠ "ffi_array" ⇒
  env_ok (cenv with v := nsBind x v cenv.v)
Proof
  rw[env_ok_def]
QED

Theorem env_rel_nsBind:
  env_rel cnenv senv cenv ∧
  v_rel cnenv sv cv
  ⇒ env_rel cnenv ((s,sv)::senv) (cenv with v := nsBind (var_prefix s) cv cenv.v)
Proof
  rw[env_rel_def] >> IF_CASES_TAC >> gvs[]
QED

Theorem env_rel_nsBind_alt:
  env_rel cnenv senv cenv ∧ (∀x. cx ≠ var_prefix x)
  ⇒ env_rel cnenv senv (cenv with v := nsBind cx cv cenv.v)
Proof
  rw[env_rel_def]
QED

Theorem env_ok_nsAppend_var_prefix:
  (∀n v. nsLookup ns' n = SOME v ⇒ ∃n'. n = Short $ var_prefix n') ∧
  env_ok (cenv with v := ns) ⇒
  env_ok (cenv with v := nsAppend ns' ns)
Proof
  rw[env_ok_def] >> simp[namespacePropsTheory.nsLookup_nsAppend_some] >>
  rw[DISJ_EQ_IMP] >> gvs[namespaceTheory.id_to_mods_def] >>
  Cases_on `nsLookup ns' (Short "ffi_array")` >> gvs[] >>
  first_x_assum drule >> simp[var_prefix_def]
QED

Theorem env_rel_nsAppend:
  env_rel cnenv senv cenv ∧
  (∀sx. ALOOKUP senv' sx = NONE ⇒ nsLookup cenv' (Short (var_prefix sx)) = NONE) ∧
  (∀sx sv. ALOOKUP senv' sx = SOME sv ⇒
    ∃cv. nsLookup cenv' (Short (var_prefix sx)) = SOME cv ∧ v_rel cnenv sv cv)
  ⇒ env_rel cnenv (senv' ++ senv) (cenv with v := nsAppend cenv' cenv.v)
Proof
  rw[env_rel_def] >> simp[namespacePropsTheory.nsLookup_nsAppend_some] >>
  simp[namespaceTheory.id_to_mods_def, SF DNF_ss] >>
  gvs[ALOOKUP_APPEND] >> every_case_tac >> gvs[]
QED

Theorem env_ok_Recclosure:
  env_ok cenv ∧
  EVERY (λ(cv,cx,ce). ∃sv. cv = var_prefix sv) cfuns ⇒
  env_ok (cenv with v := build_rec_env cfuns cenv cenv.v)
Proof
  rw[build_rec_env_def] >>
  qsuff_tac `∀fs.
    env_ok (cenv with v :=
      FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cenv fs f) env') cenv.v cfuns)` >>
  rw[] >>
  Induct_on `cfuns` >> rw[] >> pairarg_tac >> gvs[] >>
  gvs[env_ok_def] >> simp[Once var_prefix_def]
QED

Theorem env_rel_Recclosure:
  env_rel cnenv senv cenv ∧ env_ok cenv ∧
  LIST_REL
    (λ(sv,se) (cv,cx,ce). var_prefix sv = cv ∧
      ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧
               compile_rel cnenv se' ce) sfuns cfuns ∧
  ALL_DISTINCT (MAP FST cfuns)
  ⇒ env_rel cnenv
      (MAP (λ(fn,_). (fn,Recclosure sfuns senv fn)) sfuns ++ senv)
      (cenv with v := build_rec_env cfuns cenv cenv.v)
Proof
  rw[build_rec_env_def] >>
  qsuff_tac `∀sfs cfs.
    LIST_REL
      (λ(sv,se) (cv,cx,ce). var_prefix sv = cv ∧
        ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧
                 compile_rel cnenv se' ce) sfs cfs ∧
    ALL_DISTINCT (MAP FST cfs) ⇒
    env_rel cnenv
      (MAP (λ(fn,_). (fn,Recclosure sfs senv fn)) sfuns ++ senv)
      (cenv with v :=
        FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cenv cfs f) env') cenv.v cfuns)` >>
  rw[] >> pop_assum mp_tac >> qpat_x_assum `LIST_REL _ sfuns _` mp_tac >>
  map_every qid_spec_tac [`cfuns`,`sfuns`] >> ho_match_mp_tac LIST_REL_ind >> rw[] >>
  ntac 2 (pairarg_tac >> gvs[]) >> gvs[env_rel_def] >>
  rw[] >> simp[env_rel_def, SF SFY_ss]
QED

Theorem env_ok_nsBind_Recclosure:
  env_ok cenv ∧ EVERY (λ(cv,cx,ce). ∃sv. cv = var_prefix sv) cfuns ⇒
  env_ok (cenv with v := nsBind (var_prefix x) v (build_rec_env cfuns cenv cenv.v))
Proof
  rw[] >> drule_all env_ok_Recclosure >> strip_tac >>
  gvs[env_ok_def] >> simp[Once var_prefix_def]
QED

Theorem env_rel_nsBind_Recclosure:
  env_rel cnenv senv cenv ∧ env_ok cenv ∧ v_rel cnenv sv cv ∧
  LIST_REL
    (λ(sv,se) (cv,cx,ce). var_prefix sv = cv ∧
      ∃sx se'. se = Lam (SOME sx) se' ∧ var_prefix sx = cx ∧
               compile_rel cnenv se' ce) sfuns cfuns ∧
  ALL_DISTINCT (MAP FST cfuns)
  ⇒ env_rel cnenv
      ((s,sv)::(MAP (λ(fn,_). (fn,Recclosure sfuns senv fn)) sfuns ++ senv))
      (cenv with v := nsBind (var_prefix s) cv (build_rec_env cfuns cenv cenv.v))
Proof
  rw[] >> drule_all env_rel_Recclosure >> strip_tac >>
  gvs[env_ok_def, env_rel_def] >> rw[] >> simp[]
QED

Theorem env_rel_pmatch:
  env_rel cnenv senv cenv ∧
  v_rel cnenv sv cv ∧ LIST_REL (v_rel cnenv) svs cvs ∧
  LENGTH pvs = LENGTH cvs
  ⇒ env_rel cnenv
      (REVERSE (ZIP (pvs,svs)) ++ [(x,sv)] ++ senv)
      (cenv with v :=
        nsAppend (alist_to_ns (REVERSE (ZIP (MAP var_prefix pvs,cvs))
          ++ [(var_prefix x,cv)])) cenv.v)
Proof
  rw[] >> irule_at Any env_rel_nsAppend >> simp[] >>
  simp[namespacePropsTheory.nsLookup_alist_to_ns_some,
       namespacePropsTheory.nsLookup_alist_to_ns_none, PULL_EXISTS] >>
  imp_res_tac LIST_REL_LENGTH >> gvs[] >> rw[ZIP_MAP, ALOOKUP_APPEND]
  >- (
    simp[GSYM MAP_REVERSE, LAMBDA_PROD] >>
    DEP_REWRITE_TAC[ALOOKUP_MAP_MAP] >> simp[] >>
    DEP_REWRITE_TAC[MAP_ID_ON] >> simp[FORALL_PROD] >>
    gvs[REVERSE_ZIP] >> every_case_tac >> gvs[]
    >- (gvs[ALOOKUP_NONE] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP])
    >- (gvs[ALOOKUP_NONE] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP]) >>
    drule $ INST_TYPE [beta |-> ``:semanticPrimitives$v``] ALOOKUP_SOME_EL_2 >>
    disch_then $ qspec_then `ZIP (REVERSE pvs,REVERSE cvs)` mp_tac >>
    simp[MAP_ZIP] >> strip_tac >> gvs[EL_ZIP, LIST_REL_EL_EQN, EL_REVERSE]
    )
  >- (
    simp[GSYM MAP_REVERSE, LAMBDA_PROD] >>
    DEP_REWRITE_TAC[ALOOKUP_MAP_MAP] >> simp[] >>
    DEP_REWRITE_TAC[MAP_ID_ON] >> simp[FORALL_PROD] >>
    gvs[REVERSE_ZIP] >> every_case_tac >> gvs[]
    >- (gvs[ALOOKUP_NONE] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP]) >>
    drule $ INST_TYPE [beta |-> ``:semanticPrimitives$v``] ALOOKUP_SOME_EL_2 >>
    disch_then $ qspec_then `ZIP (REVERSE pvs,REVERSE cvs)` mp_tac >>
    simp[MAP_ZIP] >> strip_tac >> gvs[EL_ZIP, LIST_REL_EL_EQN, EL_REVERSE]
    )
  >- (every_case_tac >> gvs[])
  >- (
    every_case_tac >> gvs[] >> imp_res_tac ALOOKUP_MEM >>
    gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
    imp_res_tac ALOOKUP_MEM >> gvs[ALOOKUP_NONE, MEM_MAP, MEM_ZIP]
    )
QED

Theorem env_ok_pmatch:
  env_ok cenv ∧
  LENGTH pvs = LENGTH cvs
  ⇒ env_ok (cenv with v :=
      nsAppend (alist_to_ns (REVERSE (ZIP (MAP var_prefix pvs,cvs))
        ++ [(var_prefix v,cv)])) cenv.v)
Proof
  rw[] >> irule env_ok_nsAppend_var_prefix >>
  rw[namespacePropsTheory.nsLookup_alist_to_ns_some] >>
  imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
QED


(***** pmatch *****)

Theorem can_pmatch_all_tuple:
  LENGTH pvs = LENGTH cvs ⇒
  can_pmatch_all cenv.c st [pat_row c "" pvs] (Conv NONE cvs)
Proof
  rw[can_pmatch_all_def, pat_row_def, pmatch_def] >>
  rename1 `_ binding ≠ _` >> pop_assum mp_tac >>
  map_every qid_spec_tac [`binding`,`pvs`,`cvs`] >> Induct >> rw[pmatch_def] >>
  Cases_on `pvs` >> gvs[pmatch_def]
QED

Theorem pmatch_no_match:
  cnenv_rel cnenv cenv.c ∧
  ALOOKUP cnenv cn = SOME (tyid,LENGTH cvs) ∧
  ALOOKUP cnenv cn' = SOME (tyid',LENGTH vs) ∧
  same_type tyid' tyid ∧ cn' ≠ cn ⇒
  pmatch cenv.c cst (pat_row v cn' vs) (Conv (SOME tyid) cvs) [] = No_match
Proof
  rw[pat_row_def, pmatch_def] >> gvs[cnenv_rel_def] >- metis_tac[] >>
  qpat_x_assum `∀cn. _` imp_res_tac >> simp[] >>
  IF_CASES_TAC >> gvs[same_ctor_def]
QED

Theorem pmatch_match:
  cnenv_rel cnenv cenv.c ∧
  ALOOKUP cnenv cn = SOME (tyid, LENGTH cvs) ∧
  LENGTH pvs = LENGTH cvs ⇒
  pmatch cenv.c cst (pat_row v cn pvs) (Conv (SOME tyid) cvs) [] =
    Match $ REVERSE (ZIP (MAP var_prefix pvs,cvs)) ++
      [(var_prefix v, Conv (SOME tyid) cvs)]
Proof
  rw[pat_row_def, pmatch_def] >> gvs[cnenv_rel_def] >- metis_tac[] >>
  first_x_assum drule >> strip_tac >> simp[same_ctor_def] >>
  rename1 `pmatch_list _ _ _ _ foo` >> qpat_x_assum `LENGTH _ = _` mp_tac >>
  map_every qid_spec_tac [`foo`,`pvs`,`cvs`] >> Induct >> rw[pmatch_def] >>
  Cases_on `pvs` >> gvs[] >> simp[pmatch_def]
QED

Theorem pmatch_tuple:
  LENGTH pvs = LENGTH cvs ⇒
  pmatch cenv cst (pat_row v "" pvs) (Conv NONE cvs) [] =
    Match $ REVERSE (ZIP (MAP var_prefix pvs,cvs)) ++ [(var_prefix v, Conv NONE cvs)]
Proof
  rw[pat_row_def, pmatch_def] >>
  rename1 `pmatch_list _ _ _ _ foo` >> qpat_x_assum `LENGTH _ = _` mp_tac >>
  map_every qid_spec_tac [`foo`,`pvs`,`cvs`] >> Induct >> rw[pmatch_def] >>
  Cases_on `pvs` >> gvs[] >> simp[pmatch_def]
QED


(***** compile_rel *****)

(* `ALL_DISTINCT vs` not necessary here, but useful for matching against *)
Theorem compile_rel_can_pmatch_all:
  ∀scss ccss c cn stamp id vs cnenv (cenv:semanticPrimitives$v sem_env) st.
    LIST_REL
      (λ(cn,vs,se) (pat,ce). compile_rel cnenv se ce ∧ pat = pat_row c cn vs)
      scss ccss ⇒
    EVERY (λ(cn,vs,_). ALL_DISTINCT vs ∧ ∃stamp'.
      ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧ same_type stamp' stamp) scss ∧
    cnenv_rel cnenv cenv.c ∧
    v_rel cnenv (Constructor cn svs) (Conv (SOME stamp) cvs)
  ⇒ can_pmatch_all cenv.c st (MAP FST ccss) (Conv (SOME stamp) cvs)
Proof
  Induct >> rw[] >> simp[can_pmatch_all_def] >>
  ntac 2 (pairarg_tac >> gvs[]) >> rename1 `compile_rel _ se _` >> gvs[SF DNF_ss] >>
  last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
  simp[pat_row_def] >> gvs[cnenv_rel_def] >>
  qpat_x_assum `∀cn. _` imp_res_tac >> simp[pmatch_def] >>
  IF_CASES_TAC >> gvs[same_ctor_def] >>
  `cn = cn'` by metis_tac[] >> imp_res_tac LIST_REL_LENGTH >> gvs[] >>
  rename1 `pmatch_list _ _ _ _ bindings` >>
  qpat_x_assum `LENGTH vs = _` mp_tac >>
  map_every qid_spec_tac [`bindings`,`vs`,`cvs`] >>
  Induct >> rw[pmatch_def] >> Cases_on `vs'` >> gvs[] >> simp[pmatch_def]
QED

Theorem concat_vs_to_string:
  ∀strs cvs cnenv str.
    LIST_REL (v_rel cnenv) (MAP Atom strs) cvs ∧
    concat strs = SOME str
    ⇒ vs_to_string cvs = SOME str
Proof
  Induct >> rw[] >> gvs[vs_to_string_def, concat_def] >>
  first_x_assum drule >> rw[]
QED


(***** primitive operations *****)

Theorem strle_lemma:
  ∀n s1 s2 env env' st c.
    nsLookup env.v (Short "strle") = SOME $ strle_v env' ∧
    nsLookup env'.c (Short $ "True") = SOME (0n, TypeStamp "True" bool_type_num) ∧
    nsLookup env'.c (Short $ "False") = SOME (0n, TypeStamp "False" bool_type_num)
  ⇒ ∃k env'. cstep_n k (Estep (env,st, Exp (var "strle"),
        (Capp Opapp [Litv (IntLit &n)] [], env)::
        (Capp Opapp [Litv (StrLit s1)] [], env)::
        (Capp Opapp [Litv (StrLit s2)] [], env)::c)) =
      Estep (env',st,Val (Boolv (DROP n s1 ≤ DROP n s2)),c)
Proof
  recInduct strle_ind >> rw[] >>
  ntac 2 (qrefine `SUC k` >> simp[cstep]) >>
  simp[do_opapp_def, strle_v_def] >> simp[find_recfun_def, build_rec_env_def] >>
  qmatch_goalsub_abbrev_tac `If _ _ rest` >>
  ntac 20 (qrefine `SUC k` >> simp[cstep, do_opapp_def, do_app_def]) >>
  simp[opb_lookup_def] >> Cases_on `STRLEN s1 ≤ n` >>
  ntac 2 (qrefine `SUC k` >> simp[cstep, do_if_def])
  >- (
    simp[do_con_check_def, build_conv_def] >>
    qexists_tac `0` >> simp[Boolv_def] >> IF_CASES_TAC >> simp[] >>
    pop_assum mp_tac >> simp[] >> `DROP n s1 = ""` by rw[DROP_EQ_NIL] >> simp[]
    ) >>
  unabbrev_all_tac >>
  ntac 5 (qrefine `SUC k` >> simp[cstep, do_app_def]) >>
  simp[do_app_def, opb_lookup_def] >> Cases_on `STRLEN s2 ≤ n` >>
  ntac 2 (qrefine `SUC k` >> simp[cstep, do_if_def])
  >- (
    simp[do_con_check_def, build_conv_def] >> qexists_tac `0` >> simp[Boolv_def] >>
    `DROP n s2 = ""` by rw[DROP_EQ_NIL] >> simp[] >> Cases_on `DROP n s1` >> gvs[]
    ) >>
  ntac 24 (qrefine `SUC k` >> simp[cstep, do_app_def, IMPLODE_EXPLODE_I]) >>
  gvs[NOT_LESS_EQUAL] >> imp_res_tac DROP_CONS_EL >> gvs[] >>
  simp[opb_lookup_def, do_if_def] >> IF_CASES_TAC >> gvs[]
  >- (
    ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
    simp[do_con_check_def, build_conv_def] >>
    qexists_tac `0` >> simp[Boolv_def, char_lt_def]
    ) >>
  ntac 7 (qrefine `SUC k` >> simp[cstep, do_app_def, do_eq_def, lit_same_type_def]) >>
  simp[do_if_def] >> reverse $ IF_CASES_TAC >> gvs[ORD_11]
  >- (
    ntac 1 (qrefine `SUC k` >> simp[cstep]) >>
    simp[do_con_check_def, build_conv_def] >>
    qexists_tac `0` >> simp[Boolv_def, char_lt_def]
    ) >>
  ntac 13 (qrefine `SUC k` >> simp[cstep, do_app_def, opn_lookup_def]) >>
  gvs[integerTheory.INT_ADD_CALCULATE, char_lt_def, ADD1] >>
  last_x_assum $ irule_at Any >>
  goal_assum drule >> simp[strle_v_def]
QED

Theorem strle:
  ∀s1 s2 env env' st c.
    nsLookup env.v (Short "strle") = SOME $ strle_v env' ∧
    nsLookup env'.c (Short $ "True") = SOME (0n, TypeStamp "True" bool_type_num) ∧
    nsLookup env'.c (Short $ "False") = SOME (0n, TypeStamp "False" bool_type_num)
  ⇒ ∃k env'. cstep_n k (Estep (env,st, Exp (var "strle"),
        (Capp Opapp [Litv (IntLit 0)] [], env)::
        (Capp Opapp [Litv (StrLit s1)] [], env)::
        (Capp Opapp [Litv (StrLit s2)] [], env)::c)) =
      Estep (env',st,Val (Boolv (s1 ≤ s2)),c)
Proof
  rw[] >> drule_all strle_lemma >> disch_then $ qspec_then `0` mp_tac >> simp[]
QED



(********** Main results **********)

Theorem step1_rel:
  step_rel s c ∧ ¬is_halt s ∧ (∀n st k. step_n n s ≠ error st k)
  ⇒ ∃n. step_rel (step_n 1 s) (cstep_n (SUC n) c) ∧
        ∀ws. get_ffi_array (cstep_n (SUC n) c) = SOME ws ⇒
             get_ffi_array c = SOME ws
Proof
  rw[Once step_rel_cases] >> gvs[]
  >- ( (* Exp *)
    pop_assum $ qspec_then `1` assume_tac >> gvs[] >>
    gvs[Once compile_rel_cases, sstep, cstep] >~ [`Concat`]
    >- ( (* Concat *)
      `cnenv_rel cnenv cenv.c` by gvs[env_rel_def] >>
      drule cnenv_rel_list_type >> strip_tac >>
      TOP_CASE_TAC >> gvs[]
      >- (
        gvs[eval_op_def, concat_def, list_to_exp_def] >>
        ntac 2 (qrefine `SUC n` >> simp[cstep]) >>
        simp[do_app_def, v_to_list_def, v_to_char_list_def,
             list_type_num_def, vs_to_string_def] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
      qspecl_then [`ys1 ++ [y]`,`cnenv`,`cenv`,`cst`,`(Capp Strcat [] [],cenv)::ck`]
        assume_tac cstep_list_to_exp >> gvs[] >>
      qrefine `m + n` >> simp[cstep_n_add, REVERSE_APPEND] >>
      qrefine `SUC m` >> simp[cstep, list_to_cont_def] >>
      gvs[env_ok_def, do_con_check_def] >> qexists0 >> simp[] >>
      simp[step_rel_cases, env_ok_def] >> goal_assum drule >>
      simp[Once cont_rel_cases, list_to_v_def, list_type_num_def, env_ok_def] >>
      irule_at Any EQ_REFL >> simp[EVERY2_REVERSE1]
      ) >>
    qexists0 >> simp[]
    >- simp[step_rel_cases, SF SFY_ss] (* IntLit *)
    >- simp[step_rel_cases, SF SFY_ss] (* StrLit *)
    >- ( (* Tuple *)
      simp[do_con_check_def] >> TOP_CASE_TAC >> gvs[]
      >- (simp[build_conv_def] >> simp[step_rel_cases, SF SFY_ss]) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases, EVERY2_REVERSE1]
      )
    >- ( (* Constructor *)
      drule_all env_rel_check >> strip_tac >> simp[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      TOP_CASE_TAC >> gvs[]
      >- (
        qspec_then `[]` mp_tac env_rel_build >> simp[] >>
        disch_then drule_all >> strip_tac >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases, EVERY2_REVERSE1]
      )
    >- ( (* Var *)
      CASE_TAC >> gvs[] >> drule_all env_rel_lookup >> strip_tac >> gvs[] >>
      simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* App *)
      IF_CASES_TAC >> gvs[] >> reverse $ TOP_CASE_TAC >> gvs[]
      >- (
        gvs[SWAP_REVERSE_SYM, LIST_REL_SPLIT1, REVERSE_APPEND] >>
        simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[Once cont_rel_cases, EVERY2_REVERSE1]
        ) >>
      gvs[num_args_ok_0, op_rel_cases]
      >- (
        Cases_on `aop` >> gvs[sstep, eval_op_def] >>
        gvs[atom_op_rel_cases, opn_rel_cases, opb_rel_cases]
        ) >>
      (* Ref *)
      gvs[sstep, do_app_def, store_alloc_def, SNOC_APPEND] >>
      simp[step_rel_cases, SF DNF_ss, GSYM CONJ_ASSOC] >>
      gvs[state_rel, ADD1] >> rpt $ goal_assum $ drule_at Any >>
      imp_res_tac LIST_REL_LENGTH >> simp[store_lookup_def]
      )
    >- ( (* Div/Mod/Elem/Substring2 *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Substring3 *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Alloc *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* FFI *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- simp[step_rel_cases, SF SFY_ss] (* Lam *)
    >- ( (* Letrec *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_Recclosure >> irule_at Any env_ok_Recclosure >> simp[] >>
      rw[EVERY_EL] >> gvs[LIST_REL_EL_EQN] >>
      first_x_assum drule >> ntac 2 (pairarg_tac >> simp[]) >>
      rw[] >> irule_at Any EQ_REFL
      )
    >- ( (* Let *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* If *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Case *)
      IF_CASES_TAC >> gvs[] >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases] >> disj1_tac >>
      irule_at Any EQ_REFL >> simp[SF SFY_ss]
      )
    >- ( (* TupleCase *)
      IF_CASES_TAC >> gvs[] >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases] >> disj2_tac >> irule_at Any EQ_REFL >> simp[SF SFY_ss]
      )
    >- ( (* Raise *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    >- ( (* Handle *)
      simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      )
    )
  >~ [`Exn`]
  >- ( (* Raise *)
    pop_assum $ qspec_then `1` assume_tac >> gvs[] >>
    Cases_on `sk` >> gvs[sstep] >>
    Cases_on `h` >> gvs[Once cont_rel_cases] >> simp[cstep]
    >~ [`list_to_cont`]
    >- ( (* AppK (Cons _) *)
      qrefine `n + LENGTH ces` >>
      simp[cstep_n_add] >> once_rewrite_tac[GSYM APPEND_ASSOC] >>
      simp[cstep_Exn_over_list_to_cont] >>
      qrefine `SUC n` >> simp[cstep] >> qexists0 >> simp[] >>
      simp[step_rel_cases, SF SFY_ss]
      )
    >>~ [`Cmat_check`]
    >- ( (* CaseK *)
      Cases_on `ccont = Cmat_check` >> gvs[cstep] >>
      qexists0 >> simp[] >> simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* TupleCaseK *)
      Cases_on `ccont = Cmat_check` >> gvs[cstep] >>
      qexists0 >> simp[] >> simp[step_rel_cases, SF SFY_ss]
      )
    >~ [`Exp`,`Pvar`]
    >- ( (* HandleK *)
      qrefine `SUC n` >> simp[cstep] >>
      simp[can_pmatch_all_def, pmatch_def] >>
      qrefine `SUC n` >> simp[cstep] >>
      simp[astTheory.pat_bindings_def, pmatch_def] >>
      qexists0 >> simp[step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >> simp[] >>
      irule env_rel_nsBind >> simp[]
      ) >>
    qexists0 >> simp[] >> simp[step_rel_cases, SF SFY_ss]
    ) >>
  (* Val *)
  Cases_on `sk` >> gvs[sstep] >>
  gvs[DefnBase.one_line_ify NONE return_def] >>
  reverse TOP_CASE_TAC >> gvs[Once cont_rel_cases, sstep, cstep]
  >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* HandleK *)
  >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* RaiseK *)
  >- ( (* CaseK *)
    rename1 `CaseK senv v scss :: sk` >>
    drule step_Case_no_error >> strip_tac >> gvs[]
    >- (
      irule FALSITY >> imp_res_tac ALOOKUP_MEM >> gvs[EVERY_MEM] >>
      first_x_assum drule >> strip_tac >> gvs[] >>
      gvs[env_rel_def, cnenv_rel_def] >> metis_tac[]
      ) >>
    rename1 `_ = LENGTH svs` >> rename1 `ALOOKUP _ _ = SOME (_,sce)` >>
    `same_type tyid stamp` by (
      gvs[EVERY_MEM] >> drule ALOOKUP_MEM >> strip_tac >>
      first_x_assum drule >> simp[]) >>
    `EVERY (λ(cn,vs,se). ALL_DISTINCT vs ∧
       ∃stamp'. ALOOKUP cnenv cn = SOME (stamp',LENGTH vs) ∧
          same_type stamp' tyid) scss` by (
        gvs[EVERY_MEM] >> rw[] >> pairarg_tac >> gvs[] >>
        first_x_assum drule >> rw[] >> simp[] >>
        metis_tac[evaluatePropsTheory.same_type_trans,
                  evaluatePropsTheory.same_type_sym]) >>
    pop_assum mp_tac >> pop_assum kall_tac >>
    qpat_x_assum `EVERY _ _` kall_tac >> strip_tac >>
    drule compile_rel_can_pmatch_all >> disch_then drule >> simp[] >>
    rpt $ disch_then $ drule_at Any >>
    disch_then $ qspecl_then [`cenv'`,`cst`] mp_tac >>
    impl_keep_tac >- gvs[env_rel_def] >> strip_tac >>
    last_x_assum $ qspec_then `SUC n` $ assume_tac o GEN_ALL >>
    TOP_CASE_TAC >> gvs[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    IF_CASES_TAC >> gvs[step_n_SUC, sstep]
    >- (first_x_assum $ qspec_then `0` assume_tac >> gvs[])
    >- (first_x_assum $ qspec_then `0` assume_tac >> gvs[]) >>
    reverse $ IF_CASES_TAC
    >- ( (* No match *)
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      drule_all pmatch_no_match >> strip_tac >>
      Cases_on `ccont = Cmat_check` >> gvs[] >> simp[cstep]
      >- (
        qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
        simp[] >> qexists0 >> simp[Once step_rel_cases] >>
        rpt $ goal_assum $ drule_at Any >> simp[Once cont_rel_cases] >>
        disj1_tac >> irule_at Any EQ_REFL >> simp[SF SFY_ss]
        )
      >- (
        simp[] >> qexists0 >> simp[Once step_rel_cases] >>
        rpt $ goal_assum $ drule_at Any >> simp[Once cont_rel_cases] >>
        disj1_tac >> irule_at Any EQ_REFL >> simp[SF SFY_ss]
        )
      ) >>
    pop_assum SUBST_ALL_TAC >> gvs[] >>
    drule pmatch_match >>
    disch_then $ qspecl_then [`v`,`stamp'`,`pvs`,`cvs`,`cst`,`cn`] mp_tac >>
    simp[] >> imp_res_tac LIST_REL_LENGTH >> simp[] >> strip_tac >>
    Cases_on `ccont = Cmat_check` >> gvs[] >> simp[cstep]
    >- (
      qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
      simp[] >> qexists0 >> simp[Once step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
      )
    >- (
      simp[] >> qexists0 >> simp[Once step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
      )
    )
  >- ( (* TupleCaseK *)
    IF_CASES_TAC >> gvs[]
    >- (last_x_assum $ qspec_then `1` assume_tac >> gvs[sstep]) >>
    drule step_Case_no_error >> strip_tac >> gvs[] >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    Cases_on `ccont = Cmat_check` >> gvs[cstep]
    >- (
      simp[can_pmatch_all_tuple] >>
      qrefine `SUC n` >> simp[cstep_n_def, cstep, pmatch_tuple] >>
      qexists0 >> simp[Once step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
      )
    >- (
      qexists0 >> simp[pmatch_tuple] >> simp[Once step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_rel_pmatch >> irule_at Any env_ok_pmatch >> simp[]
      )
    )
  >- ( (* IfK *)
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep, AllCaseEqs()]
    >- (
      `Conv (SOME tyid) [] = Boolv T` by
        gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def] >>
      simp[do_if_def] >>
      qexists0 >> simp[step_rel_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rpt $ goal_assum $ drule_at Any >> simp[AllCaseEqs()]
      )
    >- (
      `Conv (SOME tyid) [] = Boolv F` by
        gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def, Boolv_def] >>
      simp[do_if_def] >>
      qexists0 >> simp[step_rel_cases, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      rpt $ goal_assum $ drule_at Any >> simp[AllCaseEqs()]
      )
    )
  >- ( (* LetK *)
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    irule env_rel_nsBind >> simp[]
    )
  >- ( (* TupleK *)
    TOP_CASE_TAC >> gvs[cstep, do_con_check_def, build_conv_def] >>
    qexists0 >> simp[step_rel_cases, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> simp[Once cont_rel_cases]
    )
  >- ( (* AppK (Cons cn) *)
    drule_all env_rel_check >> strip_tac >>
    imp_res_tac LIST_REL_LENGTH >> gvs[] >>
    reverse TOP_CASE_TAC >> gvs[cstep, ADD1]
    >- ( (* more arguments to evaluate *)
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      ) >>
    qspec_then `cv::cvs` mp_tac env_rel_build >> simp[ADD1] >>
    disch_then drule_all >> strip_tac >> simp[] >>
    qexists0 >> simp[step_rel_cases, ADD1, SF SFY_ss]
    )
  >- ( (* AppK *)
    reverse TOP_CASE_TAC >> gvs[cstep]
    >- ( (* more arguments to evaluate *)
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases]
      ) >>
    Cases_on `s = AppOp` >> gvs[]
    >- (
      gvs[op_rel_cases] >>
      pop_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
      TOP_CASE_TAC >> gvs[dest_anyClosure_def, LENGTH_EQ_NUM_compute] >>
      TOP_CASE_TAC >> gvs[] >> PairCases_on `x` >> gvs[] >>
      reverse $ Cases_on `dest_Closure sv` >> gvs[]
      >- ( (* Closure *)
        Cases_on `sv` >> gvs[opt_bind_def, do_opapp_def] >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        irule env_rel_nsBind >> simp[]
        ) >>
      (* Recclosure *)
      Cases_on `dest_Recclosure sv` >> gvs[] >>
      PairCases_on `x` >> rename1 `SOME (f,env,n)` >> gvs[] >>
      Cases_on `ALOOKUP f n` >> gvs[] >> Cases_on `x` >> gvs[] >>
      Cases_on `sv` >> gvs[] >>
      simp[do_opapp_def, semanticPrimitivesPropsTheory.find_recfun_ALOOKUP] >>
      qpat_x_assum `ALL_DISTINCT _` mp_tac >> rw[FST_THM, Once LAMBDA_PROD] >>
      imp_res_tac ALOOKUP_SOME_EL >>
      drule $ iffLR LIST_REL_EL_EQN >> strip_tac >>
      pop_assum drule >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      simp[opt_bind_def] >>
      drule ALOOKUP_ALL_DISTINCT_EL >> rw[FST_THM, Once LAMBDA_PROD] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      irule_at Any env_ok_nsBind_Recclosure >>
      irule_at Any env_rel_nsBind_Recclosure >> simp[FST_THM, LAMBDA_PROD] >>
      rw[EVERY_EL] >> gvs[LIST_REL_EL_EQN] >>
      last_x_assum drule >> simp[] >> ntac 2 (pairarg_tac >> gvs[]) >>
      strip_tac >> simp[] >> qexists_tac `sv` >> simp[]
      ) >>
    `cop ≠ Opapp` by (CCONTR_TAC >> gvs[op_rel_cases, atom_op_rel_cases]) >>
    `get_ffi_ch cop = NONE` by (
      CCONTR_TAC >> Cases_on `cop` >> gvs[op_rel_cases, atom_op_rel_cases]) >>
    simp[] >> first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    IF_CASES_TAC >> gvs[] >> reverse $ gvs[op_rel_cases, ADD1]
    >- ( (* Unsafe update *)
      `LENGTH l0 = 2` by gvs[] >> gvs[LENGTH_EQ_NUM_compute] >>
      rename1 `[lnum;idx;elem]` >> gvs[application_def, sstep] >>
      Cases_on `lnum` >> gvs[] >> Cases_on `idx` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      `¬(i < 0)` by ARITH_TAC >> simp[] >>
      `¬(Num (ABS i) ≥ LENGTH cs)` by ARITH_TAC >> simp[] >>
      drule store_lookup_assign_Varray >> rw[] >>
      `ABS i = i` by ARITH_TAC >> simp[] >>
      qexists0 >> reverse $ rw[step_rel_cases]
      >- gvs[state_rel, LUPDATE_DEF, store_lookup_def] >>
      goal_assum drule >> gvs[state_rel] >> simp[LUPDATE_DEF, GSYM ADD1] >>
      ntac 2 (irule EVERY2_LUPDATE_same >> simp[])
      )
    >- ( (* Update *)
      `LENGTH l0 = 2` by gvs[] >> gvs[LENGTH_EQ_NUM_compute] >>
      rename1 `[lnum;idx;elem]` >> gvs[application_def, sstep] >>
      Cases_on `lnum` >> gvs[] >> Cases_on `idx` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[]
      >- ( (* in bounds *)
        `¬(i < 0)` by ARITH_TAC >> simp[] >>
        `¬(Num (ABS i) ≥ LENGTH cs)` by ARITH_TAC >> simp[] >>
        drule store_lookup_assign_Varray >> rw[] >>
        `ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> reverse $ rw[step_rel_cases]
        >- gvs[state_rel, LUPDATE_DEF, store_lookup_def] >>
        goal_assum drule >> gvs[state_rel] >> simp[LUPDATE_DEF, GSYM ADD1] >>
        ntac 2 (irule EVERY2_LUPDATE_same >> simp[])
        )
      >- ( (* out of bounds *)
        qmatch_goalsub_abbrev_tac `cstep_n _ foo` >>
        `foo = Estep (cenv',cst,Exn sub_exn_v,ck')` by (
          unabbrev_all_tac >> simp[AllCaseEqs()] >> ARITH_TAC) >>
        simp[] >> ntac 2 $ pop_assum kall_tac >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[sub_exn_v_def] >> gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
        )
      )
    >- ( (* Unsafe sub *)
      `LENGTH l0 = 1` by gvs[] >> gvs[LENGTH_EQ_NUM_compute] >>
      rename1 `[lnum;idx]` >> gvs[application_def, sstep] >>
      Cases_on `lnum` >> gvs[] >> Cases_on `idx` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      `¬(i < 0)` by ARITH_TAC >> simp[] >>
      `¬(Num (ABS i) ≥ LENGTH cs)` by ARITH_TAC >> simp[] >>
      `ABS i = i` by ARITH_TAC >> simp[] >>
      qexists0 >> rw[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      gvs[LIST_REL_EL_EQN]
      )
    >- ( (* Sub *)
      `LENGTH l0 = 1` by gvs[] >> gvs[LENGTH_EQ_NUM_compute] >>
      rename1 `[lnum;idx]` >> gvs[application_def, sstep] >>
      Cases_on `lnum` >> gvs[] >> Cases_on `idx` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> IF_CASES_TAC >> gvs[DISJ_EQ_IMP] >>
      simp[do_app_def] >> drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[]
      >- ( (* in bounds *)
        `¬(i < 0)` by ARITH_TAC >> simp[] >>
        `¬(Num (ABS i) ≥ LENGTH cs)` by ARITH_TAC >> simp[] >>
        `ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> rw[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        gvs[LIST_REL_EL_EQN]
        )
      >- ( (* out of bounds *)
        qmatch_goalsub_abbrev_tac `cstep_n _ foo` >>
        `foo = Estep (cenv',cst,Exn sub_exn_v,ck')` by (
          unabbrev_all_tac >> simp[AllCaseEqs()] >> ARITH_TAC) >>
        simp[] >> ntac 2 $ pop_assum kall_tac >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[sub_exn_v_def] >> gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
        )
      )
    >- ( (* Length *)
      gvs[application_def, sstep] >> Cases_on `sv` >> gvs[] >>
      TOP_CASE_TAC >> gvs[] >> simp[do_app_def] >>
      drule state_rel_store_lookup >>
      disch_then $ qspec_then `n` assume_tac >> gvs[] >>
      imp_res_tac LIST_REL_LENGTH >> gvs[] >>
      qexists0 >> rw[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Ref *)
      gvs[application_def, sstep] >> simp[do_app_def, store_alloc_def] >>
      qexists0 >> reverse $ rw[step_rel_cases]
      >- (gvs[store_lookup_def] >> Cases_on `cst` >> gvs[]) >>
      gvs[state_rel, ADD1] >> rpt $ goal_assum $ drule_at Any >>
      imp_res_tac LIST_REL_LENGTH >> simp[]
      ) >>
    (* AtomOp *)
    gvs[application_def, sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    reverse $ gvs[atom_op_rel_cases]
    >- ( (* StrEq *)
      gvs[eval_op_SOME] >> simp[do_app_def, do_eq_def, lit_same_type_def] >>
      qexists0 >> rw[step_rel_cases, Boolv_def] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
      )
    >- ( (* Len str *)
      gvs[eval_op_SOME] >> simp[do_app_def] >>
      qexists0 >> rw[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Eq int *)
      gvs[eval_op_SOME] >> simp[do_app_def, do_eq_def, lit_same_type_def] >>
      qexists0 >> rw[step_rel_cases, Boolv_def] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
      )
    >- ( (* opb *)
      gvs[opb_rel_cases] >> gvs[eval_op_SOME] >> simp[do_app_def, opb_lookup_def] >>
      qexists0 >> rw[step_rel_cases, Boolv_def] >> rpt $ goal_assum $ drule_at Any >>
      gvs[env_rel_def, cnenv_rel_def, prim_types_ok_def]
      )
    >- ( (* opn *)
      gvs[opn_rel_cases] >> gvs[eval_op_SOME] >> simp[do_app_def, opn_lookup_def] >>
      qexists0 >> rw[step_rel_cases, SF SFY_ss]
      )
    )
  >- ( (* Div/Mod/Elem/Substring2 - second argument to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Div/Mod/Elem/Substring2 - ready to evaluate *)
    last_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    `aop = Div ∨ aop = Mod ∨ aop = Elem ∨ aop = Substring` by (CCONTR_TAC >> gvs[]) >>
    gvs[]
    >- ( (* Div *)
      gvs[eval_op_SOME] >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, do_eq_def, lit_same_type_def] >>
      IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* div by 0 *) >>
      ntac 4 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      qexists0 >> simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Mod *)
      gvs[eval_op_SOME] >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, do_eq_def, lit_same_type_def] >>
      IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) (* mod by 0 *) >>
      ntac 4 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      qexists0 >> simp[step_rel_cases, SF SFY_ss]
      )
    >- ( (* Elem str *)
      gvs[eval_op_SOME] >>
      ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def, str_el_def] >>
      rename1 `_ ≤ idx` >> reverse $ Cases_on `0 ≤ idx` >> gvs[]
      >- (
        `idx < 0` by ARITH_TAC >> simp[] >>
        ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      `¬ (idx < 0)` by ARITH_TAC >> simp[] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def] >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, opb_lookup_def] >> reverse $ IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def] >>
      `¬ (Num (ABS idx) ≥ STRLEN s')` by ARITH_TAC >> simp[] >>
      qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
      simp[do_app_def] >>
      qexists0 >> simp[step_rel_cases] >>
      rpt $ goal_assum $ drule_at Any >> simp[IMPLODE_EXPLODE_I] >>
      `ABS idx = idx` by ARITH_TAC >> simp[]
      )
    >- ( (* Substring2 *)
      gvs[eval_op_SOME] >> rename1 `idx < _` >>
      ntac 4 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def] >>
      ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >> IF_CASES_TAC >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (
        ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
        simp[do_app_def, opb_lookup_def] >>
        reverse $ Cases_on `0 < STRLEN s''` >> gvs[] >>
        ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
        >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
        ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
        simp[do_app_def, opn_lookup_def] >>
        ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
        simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      reverse $ Cases_on `idx < &STRLEN s''` >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (
        `DROP (Num idx) s'' = []` by (simp[] >> ARITH_TAC) >> simp[] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        ) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I] >>
      `¬ (&STRLEN s'' − idx < 0)` by ARITH_TAC >> simp[] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      `ABS idx = idx` by ARITH_TAC >> simp[] >> ARITH_TAC
      )
    )
  >- ( (* Alloc - second argument to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Alloc - ready to evaluate *)
    last_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >>
    ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def, opb_lookup_def] >>
    IF_CASES_TAC >> gvs[] >>
    ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
    simp[do_app_def, store_alloc_def] >>
    qexists0 >> simp[step_rel_cases] >> gvs[state_rel, ADD1, store_lookup_def] >>
    rpt $ goal_assum $ drule_at Any >> imp_res_tac LIST_REL_LENGTH >> simp[] >>
    `ABS i = i` by ARITH_TAC >> simp[LIST_REL_REPLICATE_same]
    )
  >- ( (* Concat *)
    `cnenv_rel cnenv cenv'.c` by gvs[env_rel_def] >>
    drule cnenv_rel_list_type >> strip_tac >> simp[] >>
    reverse TOP_CASE_TAC >> gvs[]
    >- ( (* arguments left to evaluate *)
      qrefine `SUC n` >> simp[cstep_n_def, cstep, list_to_cont_def] >>
      qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
      simp[Once cont_rel_cases] >> irule_at Any EQ_REFL >> simp[] >>
      rpt $ goal_assum $ drule_at Any >> simp[list_to_v_def, list_type_num_def]
      ) >>
    pop_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    qrefine `SUC n` >> simp[cstep_n_def, cstep, list_to_cont_def] >>
    simp[do_app_def, v_to_list_def, list_type_num_def] >>
    Cases_on `x` >> gvs[concat_def] >>
    drule_all concat_vs_to_string >> rw[] >> simp[vs_to_string_def] >>
    qexists0 >> simp[step_rel_cases, SF SFY_ss]
    )
  >- ( (* Substring3 - two args left to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Substring3 - one arg left to evaluate *)
    qrefine `SUC n` >> simp[cstep_n_def, cstep] >>
    qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
    simp[Once cont_rel_cases] >>
    irule_at Any env_rel_nsBind_alt >> simp[var_prefix_def] >>
    irule_at Any env_ok_nsBind_alt >> simp[]
    )
  >- ( (* Substring3 - ready to evaluate *)
    qmatch_goalsub_abbrev_tac `clet "off" rest1 rest2` >>
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >> TOP_CASE_TAC >> gvs[] >>
    `∃s i len. sv = Atom $ Str s ∧ sv2 = Atom $ Int i ∧ sv3 = Atom $ Int len` by
      gvs[eval_op_SOME] >>
    gvs[MAP_EQ_CONS] >> reverse $ TOP_CASE_TAC >> gvs[] >- gvs[AllCaseEqs()] >>
    ntac 6 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def, opb_lookup_def] >>
    Cases_on `len < 0` >> gvs[] >>
    ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
    >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
    simp[Abbr `rest1`] >>
    ntac 3 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def] >>
    ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    simp[do_app_def, opb_lookup_def] >>
    IF_CASES_TAC >> gvs[] >>
    ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
    >- (
      unabbrev_all_tac >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      reverse $ Cases_on `0 < STRLEN s` >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (qexists0 >> simp[step_rel_cases, SF SFY_ss]) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      Cases_on `len < &STRLEN s` >> gvs[] >>
      ntac 9 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I]
      >- (
        `¬ (STRLEN s < Num (ABS len))` by ARITH_TAC >> simp[] >>
        `ABS len = len` by ARITH_TAC >> simp[] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        )
      >- (
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        ARITH_TAC
        )
      )
    >- (
      unabbrev_all_tac >>
      ntac 7 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      reverse $ Cases_on `i < &STRLEN s` >> gvs[] >>
      ntac 2 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def])
      >- (
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        ARITH_TAC
        ) >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opn_lookup_def] >>
      ntac 8 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
      simp[do_app_def, opb_lookup_def] >>
      Cases_on `i + len < &STRLEN s` >> gvs[] >>
      ntac 9 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>

      simp[do_app_def, opn_lookup_def] >>
      ntac 5 (qrefine `SUC n` >> simp[cstep_n_def, cstep, do_if_def]) >>
      simp[do_app_def, copy_array_def, IMPLODE_EXPLODE_I]
      >- (
        `¬ (STRLEN s < Num (ABS (i + len)))` by ARITH_TAC >> simp[] >>
        `ABS len = len ∧ ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> simp[step_rel_cases, SF SFY_ss]
        )
      >- (
        `¬ (&STRLEN s − i < 0)` by ARITH_TAC >> simp[] >>
        `ABS (&STRLEN s - i) = (&STRLEN s - i) ∧ ABS i = i` by ARITH_TAC >> simp[] >>
        qexists0 >> simp[step_rel_cases] >> rpt $ goal_assum $ drule_at Any >>
        simp[TAKE_DROP_SWAP] >>
        `Num i + (Num (&STRLEN s - i)) = STRLEN s` by ARITH_TAC >> simp[] >>
        DEP_REWRITE_TAC[TAKE_LENGTH_TOO_LONG] >> ARITH_TAC
        )
      )
    )
  >- ( (* FFI *)
    qmatch_goalsub_abbrev_tac `Let _ _ ffi_rest` >>
    first_x_assum $ qspec_then `1` assume_tac >> gvs[sstep] >>
    TOP_CASE_TAC >> gvs[] >>
    ntac 3 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    `nsLookup cenv'.v (Short "ffi_array") = SOME (Loc 0)` by gvs[env_ok_def] >>
    simp[] >>
    ntac 3 (qrefine `SUC n` >> simp[cstep_n_def, cstep]) >>
    `∃ws. store_lookup 0 cst = SOME $ W8array ws ∧
          LENGTH ws = max_FFI_return_size` by gvs[state_rel, store_lookup_def] >>
    simp[] >> qexists0 >> simp[step_rel_cases, SF SFY_ss]
    )
QED


(**********)

val _ = export_theory ();

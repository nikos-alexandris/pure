
open HolKernel Parse boolLib bossLib term_tactic;
open stringTheory optionTheory configTheory pairTheory listTheory
     finite_mapTheory pred_setTheory;

val _ = new_theory "exp";

(* AST for a small functional language *)

Type vname = “:string”  (* variable name *)

Datatype:
  op = If                 (* if-expression                            *)
     | Cons string        (* datatype constructor                     *)
     | IsEq string num    (* compare cons tag and num of args         *)
     | Proj string num    (* reading a field of a constructor         *)
     | AtomOp atom_op     (* primitive parametric operator over Atoms *)
     | Lit lit            (* parametric literal Atom                  *)
End

Datatype:
  exp = Var vname                         (* variable                 *)
      | Prim op (exp list)                (* primitive operations     *)
      | App exp exp                       (* function application     *)
      | Lam vname exp                     (* lambda                   *)
      | Letrec ((vname # exp) list) exp   (* mutually recursive exps  *)
End

(* some abbreviations *)
Overload Let  = “λs x y. App (Lam s y) x”      (* let-expression    *)
Overload If   = “λx y z. Prim If [x; y; z]”    (* If   at exp level *)
Overload Lit  = “λa. Prim (Lit a) []”          (* Lit  at exp level *)
Overload Cons = “λs. Prim (Cons s)”            (* Cons at exp level *)
Overload IsEq = “λs n x. Prim (IsEq s n) [x]”  (* IsEq at exp level *)
Overload Proj = “λs i x. Prim (Proj s i) [x]”  (* Proj at exp level *)
Overload Fail = “Prim (Lit ARB) [Prim (Lit ARB)[]]” (* causes Error *)

Definition freevars_def[simp]:
  freevars (Var n)     = [n]                               ∧
  freevars (Prim _ es) = (FLAT (MAP freevars es))          ∧
  freevars (App e1 e2) = (freevars e1 ⧺ freevars e2)       ∧
  freevars (Lam n e)   = (FILTER ($≠ n) (freevars e))      ∧
  freevars (Letrec lcs e) =
    FILTER (\n. ¬ MEM n (MAP FST lcs))
           (freevars e ⧺ FLAT (MAP (λ(fn,e). freevars e) lcs))
Termination
  WF_REL_TAC ‘measure exp_size’ \\ fs[]
  \\ conj_tac \\ TRY conj_tac
  \\ TRY (Induct_on ‘lcs’)
  \\ TRY (Induct_on ‘css’)
  \\ TRY (Induct_on ‘es’)
  \\ rw [] \\ fs [fetch "-" "exp_size_def"] \\ res_tac \\ fs[]
  \\ pop_assum (assume_tac o SPEC_ALL) \\ fs[]
End

Overload freevars = “λe. set (freevars e)”

Theorem freevars_set_def[simp]:
  (∀n.     freevars (Var n)        = {n}) ∧
  (∀op es. freevars (Prim op es)   = BIGUNION (set (MAP freevars es))) ∧
  (∀e1 e2. freevars (App e1 e2)    = freevars e1 ∪ freevars e2) ∧
  (∀n e.   freevars (Lam n e)      = freevars e DELETE n) ∧
  (∀lcs e. freevars (Letrec lcs e) =
    freevars e ∪ BIGUNION (set (MAP (λ(fn,e). freevars e) lcs))
      DIFF set (MAP FST lcs))
Proof
  rw[freevars_def, LIST_TO_SET_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  rw[LIST_TO_SET_FILTER, DELETE_DEF, EXTENSION] >>
  fs[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  eq_tac >> rw[] >> fs[] >>
  DISJ2_TAC >> qexists_tac `y` >> fs[] >>
  PairCases_on `y` >> fs[]
QED

Definition closed_def:
  closed e = (freevars e = {})
End

Theorem exp_size_lemma:
  (∀xs     a. MEM      a  xs ⇒ exp_size a < exp3_size xs) ∧
  (∀xs x   a. MEM   (x,a) xs ⇒ exp_size a < exp1_size xs)
Proof
  conj_tac \\ TRY conj_tac \\ Induct \\ rw []
  \\ res_tac \\ fs [fetch "-" "exp_size_def"]
QED

Definition subst_def:
  subst m (Var s) =
    (case FLOOKUP m s of
     | NONE => Var s
     | SOME x => x) ∧
  subst m (Prim op xs) = Prim op (MAP (subst m) xs) ∧
  subst m (App x y) = App (subst m x) (subst m y) ∧
  subst m (Lam s x) = Lam s (subst (m \\ s) x) ∧
  subst m (Letrec f x) =
    let m1 = FDIFF m (set (MAP FST f)) in
      Letrec (MAP (λ(f,e). (f,subst m1 e)) f) (subst m1 x)
Termination
  WF_REL_TAC `measure (exp_size o SND)` \\ rw []
  \\ imp_res_tac exp_size_lemma \\ fs []
End

Definition bind_def:
  bind m e =
    if (∀n v. FLOOKUP m n = SOME v ⇒ closed v) then subst m e else Fail
End

Theorem subst_ignore:
  ∀m e. DISJOINT (freevars e) (FDOM m) ⇒ subst m e = e
Proof
  ho_match_mp_tac subst_ind \\ rw [] \\ fs [subst_def] \\ rw[]
  >- fs[FLOOKUP_DEF]
  >- (Induct_on `xs` >> fs[])
  >- (
    first_x_assum irule >>
    fs[DISJOINT_DEF, EXTENSION] >>
    metis_tac[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> fs[MEM_EL, PULL_EXISTS, EL_MAP] >>
    Cases_on `EL x f` >> fs[] >> rename1 `(fn_name, fn_body)` >>
    first_x_assum drule >> fs[] >> disch_then irule >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `var ∉ _` >>
    first_assum (qspec_then `var` assume_tac) >> fs[] >>
    first_x_assum (qspec_then `freevars fn_body` assume_tac) >> gvs[] >>
    pop_assum mp_tac >> simp[MEM_MAP] >> strip_tac >>
    pop_assum (qspec_then `(fn_name,fn_body)` assume_tac) >> gvs[MEM_EL] >>
    pop_assum mp_tac >> simp[MEM_EL] >> strip_tac >>
    pop_assum (qspec_then `x` assume_tac) >> gvs[]
    )
  >- (
    first_x_assum irule >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >>
    first_x_assum (qspec_then `x` assume_tac) >> fs[]
    )
QED

Theorem closed_subst[simp]:
  ∀m e. closed e ⇒ subst m e = e
Proof
  rw [] \\ match_mp_tac subst_ignore \\ fs [closed_def]
QED

Theorem subst_subst:
  ∀m1 e m2.
    DISJOINT (FDOM m1) (FDOM m2) ∧
    (∀v1. v1 ∈ FRANGE m1 ⇒ closed v1) ∧
    (∀v2. v2 ∈ FRANGE m2 ⇒ closed v2)
  ⇒ subst m1 (subst m2 e) = subst m2 (subst m1 e)
Proof
  ho_match_mp_tac subst_ind >> rw[subst_def] >> gvs[]
  >- (
    fs[DISJOINT_DEF, EXTENSION, FLOOKUP_DEF] >>
    last_assum (qspec_then `s` assume_tac) >> fs[]
    >- (
      IF_CASES_TAC >> gvs[subst_def, FLOOKUP_DEF, IN_FRANGE] >>
      irule closed_subst >> first_x_assum irule >>
      goal_assum drule >> fs[]
      )
    >- (
      IF_CASES_TAC >> gvs[subst_def, FLOOKUP_DEF, IN_FRANGE] >>
      irule (GSYM closed_subst) >> last_x_assum irule >>
      goal_assum drule >> fs[]
      )
    )
  >- (
    fs[MAP_MAP_o, combinTheory.o_DEF] >>
    rw[MAP_EQ_f] >> first_x_assum irule >> fs[]
    )
  >- (first_x_assum irule >> fs[])
  >- (first_x_assum irule >> fs[])
  >- (
    first_x_assum irule >> fs[] >>
    gvs[IN_FRANGE, PULL_EXISTS, DOMSUB_FAPPLY_THM, DISJOINT_DEF, EXTENSION] >>
    rw[] >> Cases_on `x = s` >> fs[]
    )
  >- (
    rw[LIST_EQ_REWRITE] >> gvs[MEM_EL, PULL_EXISTS, EL_MAP] >>
    Cases_on `EL x f` >> rename1 `(fn_name, fn_body)` >> gvs[] >>
    ntac 2 (
      qpat_abbrev_tac `l = MAP FST (MAP _ _)` >>
      `l = MAP FST f` by (
        unabbrev_all_tac >>
        rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
        rename1 `FST _ = FST foo` >>
        PairCases_on `foo` >> fs[]) >>
      gvs[]) >>
    first_x_assum irule >>
    gvs[IN_FRANGE, PULL_EXISTS] >>
    simp[FDIFF_def, DRESTRICT_DEF, GSYM CONJ_ASSOC] >>
    goal_assum drule >> fs[] >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `foo ∉ _` >>
    Cases_on `MEM foo (MAP FST f)` >> fs[]
    )
  >- (
    ntac 2 (
      qpat_abbrev_tac `l = MAP FST (MAP _ _)` >>
      `l = MAP FST f` by (
        unabbrev_all_tac >>
        rw[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
        rename1 `FST _ = FST foo` >>
        PairCases_on `foo` >> fs[]) >>
      gvs[]) >>
    first_x_assum irule >>
    gvs[IN_FRANGE, PULL_EXISTS] >>
    simp[FDIFF_def, DRESTRICT_DEF] >>
    fs[DISJOINT_DEF, EXTENSION] >> rw[] >> rename1 `foo ∉ _` >>
    Cases_on `MEM foo (MAP FST f)` >> fs[]
    )
QED

Theorem subst_FEMPTY:
  ∀e. subst FEMPTY e = e
Proof
  rw[] >> irule subst_ignore >> fs[]
QED

Definition subst_funs_def:
  subst_funs f = bind (FEMPTY |++ (MAP (λ(g,x). (g,Letrec f x)) f))
End

Definition expandLets_def:
   expandLets i cn nm ([]) cs = cs ∧
   expandLets i cn nm (v::vs) cs = Let v (Proj cn i (Var nm))
                                         (expandLets (i+1) cn nm vs cs)
End

Definition expandRows_def:
   expandRows nm [] = Fail ∧
   expandRows nm ((cn,vs,cs)::css) = If (IsEq cn (LENGTH vs) (Var nm))
                                        (expandLets 0 cn nm vs cs)
                                        (expandRows nm css)
End

Definition expandCases_def:
   expandCases x nm css = (Let nm x (expandRows nm css))
End

Overload Case = “λx nm css. expandCases x nm css”

val _ = export_theory ();

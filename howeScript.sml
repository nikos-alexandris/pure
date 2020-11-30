(*
   This file formalises Howe's method following the description of
   Pitts 2011 chapter "Howe's method for higher-order languages".
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory
     expTheory valueTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     pure_langTheory pred_setTheory relationTheory
     BasicProvers pure_langPropsTheory rich_listTheory finite_mapTheory;

val _ = new_theory "howe";


(* -- basics -- *)

(* the set of all expressions with at most free variables vars *)
Definition Exps_def:
  Exps vars = { e | freevars e ⊆ vars }
End

Theorem Exps_EMPTY_closed[simp]:
  e IN Exps EMPTY ⇔ closed e
Proof
  fs [Exps_def,closed_def]
QED


(* -- applicative (bi)similarity -- *)

Definition unfold_rel_def:
  unfold_rel rel (e1, e2) ⇔
    closed e1 ∧ closed e2 ∧
    (* this follows the paper directly *)
    (∀x e1'. eval e1 = Closure x e1' ⇒
             ∃y e2'. eval e2 = Closure y e2' ∧
                     ∀e. closed e ⇒ rel (subst x e e1', subst y e e2'))
    (* but I think we need one such conjunct for each result alternative, e.g.
    ∧
    (∀x xs.
       eval e1 = Constructor x xs ⇒
       ∃es1 es2. eval e1 = eval (Cons x es1) ∧ EVERY closed es1 ∧
                 eval e2 = eval (Cons x es2) ∧ EVERY closed es2 ∧
                 LIST_REL (CURRY rel) es1 es2)
    ∧
    (∀a. eval e1 = Atom a ⇒ eval e2 = Atom a)
    ∧
    (eval e1 = Diverge ⇒ eval e2 = Diverge)
    ∧
    (eval e1 = Error ⇒ eval e2 = Error) *)
End

Definition app_simulation_def:
  app_simulation S ⇔
    ∀e1 e2. S (e1, e2) ⇒ unfold_rel S (e1, e2)
End

Definition opp_def:
  opp s (x,y) ⇔ (y,x) IN s
End

Definition app_bisimulation_def:
  app_bisimulation S ⇔ app_simulation S ∧ app_simulation (opp S)
End

Definition FF_def:
  FF s = { (e1, e2) | unfold_rel s (e1, e2) }
End

Triviality monotone_similarity:
  monotone FF
Proof
  fs [monotone_def,FF_def,unfold_rel_def]
  \\ fs [SUBSET_DEF,FORALL_PROD,IN_DEF]
  \\ metis_tac []
QED

Definition app_similarity_def:
  app_similarity = gfp FF
End

val _ = set_fixity "≲" (Infixl 480);
Overload "≲" = “λx y. app_similarity (x,y)”;

Theorem app_similarity_thm =
  MATCH_MP gfp_greatest_fixedpoint monotone_similarity
  |> SIMP_RULE std_ss [GSYM app_similarity_def]

Theorem app_similarity_iff = (* result (5.4) *)
  app_similarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE std_ss [IN_DEF];

Theorem app_simulation_SUBSET_app_similarity:
  app_simulation R ⇒ R ⊆ app_similarity
Proof
  rw [app_similarity_def,app_simulation_def]
  \\ fs [gfp_def,SUBSET_DEF,FORALL_PROD]
  \\ fs [IN_DEF,FF_def,EXISTS_PROD] \\ metis_tac []
QED

Theorem app_simulation_app_similarity:
  app_simulation app_similarity
Proof
  fs [app_simulation_def]
  \\ assume_tac app_similarity_iff
  \\ metis_tac []
QED

Triviality monotone_bisimilarity:
  monotone (λs. { (e1,e2) | (e1,e2) IN FF s ∧ (e2,e1) IN FF (opp s) })
Proof
  fs [monotone_def,FF_def,unfold_rel_def,opp_def]
  \\ fs [SUBSET_DEF,FORALL_PROD,IN_DEF,opp_def]
  \\ metis_tac []
QED

Definition app_bisimilarity_def:
  app_bisimilarity = gfp (λs. { (e1,e2) | (e1,e2) IN FF s ∧ (e2,e1) IN FF (opp s) })
End

val _ = set_fixity "≃" (Infixl 480);
Overload "≃" = “λx y. app_bisimilarity (x,y)”;

Theorem app_bisimilarity_thm =
  MATCH_MP gfp_greatest_fixedpoint monotone_bisimilarity
  |> SIMP_RULE std_ss [GSYM app_bisimilarity_def]

Theorem app_bisimilarity_iff = (* result (5.5) *)
  app_bisimilarity_thm |> CONJUNCT1 |> GSYM
    |> SIMP_RULE std_ss [FF_def,EXTENSION,FORALL_PROD,GSPECIFICATION,EXISTS_PROD]
    |> SIMP_RULE (std_ss++boolSimps.CONJ_ss) [IN_DEF,unfold_rel_def,opp_def]
    |> REWRITE_RULE [GSYM CONJ_ASSOC];

Theorem app_bisimulation_SUBSET_app_bisimilarity:
  app_bisimulation R ⇒ R ⊆ app_bisimilarity
Proof
  rw [app_bisimilarity_def,app_bisimulation_def,app_simulation_def]
  \\ fs [gfp_def,SUBSET_DEF,FORALL_PROD,opp_def,IN_DEF]
  \\ fs [IN_DEF,FF_def,EXISTS_PROD,unfold_rel_def,opp_def]
  \\ rw [] \\ qexists_tac ‘R’ \\ rw []
  \\ res_tac \\ fs []
QED

Theorem app_bisimulation_app_bisimilarity:
  app_bisimulation app_bisimilarity
Proof
  fs [app_bisimulation_def,app_simulation_def,opp_def,IN_DEF,unfold_rel_def]
  \\ assume_tac app_bisimilarity_iff
  \\ metis_tac [unfold_rel_def]
QED

Theorem app_similarity_coinduct:
  ∀P.
    (∀x y. P x y ⇒ FF (UNCURRY P) (x,y))
  ⇒
  ∀x y. P x y ⇒ x ≲ y
Proof
  rpt GEN_TAC >> strip_tac >> simp[app_similarity_def] >>
  qspec_then ‘UNCURRY P’ mp_tac (MATCH_MP gfp_coinduction monotone_similarity) >>
  rw[SUBSET_DEF,IN_DEF] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  Cases >> rw[]
QED

Theorem app_bisimilarity_coinduct:
  ∀P.
    (∀x y. P x y ⇒ FF (UNCURRY P) (x,y) ∧
                   FF (opp(UNCURRY P)) (y,x))
  ⇒
  ∀x y. P x y ⇒ x ≃ y
Proof
  rpt GEN_TAC >> strip_tac >> simp[app_bisimilarity_def] >>
  qspec_then ‘UNCURRY P’ mp_tac (MATCH_MP gfp_coinduction monotone_bisimilarity) >>
  rw[SUBSET_DEF,IN_DEF] >>
  first_x_assum(match_mp_tac o MP_CANON) >>
  simp[] >>
  pop_assum kall_tac >>
  Cases >> gvs[ELIM_UNCURRY]
QED

Theorem app_similarity_closed:
  x ≲ y ⇒ closed x ∧ closed y
Proof
  rw[app_similarity_iff,Once unfold_rel_def]
QED

(* Premise not necessary, but convenient for drule:ing.
   TODO: surely this can be derived automatically somehow? *)
Theorem eval_op_cases:
  ∀op xs t.
    eval_op op xs = t ⇒
    (∃s. op = Cons s) ∨
    (∃x1 x2 x3. op = If ∧ xs = [x1;x2;x3]) ∨
    (∃s i x. op = Proj s i ∧ xs = [x]) ∨
    (∃a. op = AtomOp a) ∨
    (∃b. op = Lit b ∧ xs = []) ∨
    (op = If ∧ xs = []) ∨
    (∃x. op = If ∧ xs = [x]) ∨
    (∃x1 x2. op = If ∧ xs = [x1;x2]) ∨
    (∃x1 x2 x3 x4 xs'. op = If ∧ xs = x1::x2::x3::x4::xs') ∨
    (∃s n. op = IsEq s n ∧ xs = []) ∨
    (∃s n x. op = IsEq s n ∧ xs = [x]) ∨
    (∃s n x1 x2 xs'. op = IsEq s n ∧ xs = x1::x2::xs') ∨
    (∃s i. op = Proj s i ∧ xs = []) ∨
    (∃s i x1 x2 xs'. op = Proj s i ∧ xs = x1::x2::xs') ∨
    (∃b x xs'. op = Lit b ∧ xs = x::xs')
Proof
  ho_match_mp_tac eval_op_ind >> rw[]
QED

Theorem eval_eq_Cons_IMP:
  eval x = Constructor s xs ⇒
  ∃ts. eval x = eval (Cons s ts) ∧ MAP eval ts = xs ∧
       (closed x ⇒ closed (Cons s ts))
Proof
  strip_tac >>
  qexists_tac ‘GENLIST (λk. Proj s k x) (LENGTH xs)’ >>
  rw[eval_Cons,MAP_GENLIST,eval_thm,combinTheory.o_DEF,el_def] >>
  rw[LIST_EQ_REWRITE] >>
  gvs[closed_def,freevars_def,FLAT_EQ_NIL,EVERY_MEM,MEM_MAP,MEM_GENLIST,PULL_EXISTS]
QED

Theorem v_lookup_Error:
  v_lookup path Error = if path = [] then (Error',0) else (Diverge',0)
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem v_lookup_Atom:
  v_lookup path (Atom a) = if path = [] then (Atom' a,0) else (Diverge',0)
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem v_lookup_Closure:
  v_lookup path (Closure x e) = if path = [] then (Closure' x e,0) else (Diverge',0)
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem v_lookup_Constructor:
  v_lookup path (Constructor x xs) =
  if path = [] then (Constructor' x,LENGTH xs)
  else
    case oEL (HD path) xs of
      NONE => (Diverge',0)
    | SOME x => v_lookup (TL path) x
Proof
  Cases_on ‘path’ >> rw[v_lookup]
QED

Theorem freevars_v_simps[simp]:
  (v ∈ freevars_v Error) = F ∧
  (v ∈ freevars_v Diverge) = F ∧
  (v ∈ freevars_v (Atom a)) = F ∧
  (v ∈ freevars_v (Closure x e)) = MEM v (FILTER ($<> x) (freevars e)) ∧
  (v ∈ freevars_v (Constructor x xs)) = (v ∈ BIGUNION(IMAGE freevars_v (set xs)))
Proof
  gvs[freevars_v_MEM,MEM_FILTER] >>
  gvs[v_lookup_Error,v_lookup_Diverge,v_lookup_Atom,v_lookup_Closure,v_lookup_Constructor,AllCaseEqs(),
      oEL_THM] >>
  rw[EQ_IMP_THM,MEM_EL,PULL_EXISTS]
  >- (goal_assum (drule_at (Pat ‘_ < _’)) >>
      simp[freevars_v_MEM] >>
      goal_assum drule >>
      rw[rich_listTheory.EL_MEM,MEM_FILTER])
  >- (gvs[freevars_v_MEM,LIST_TO_SET_FILTER] >>
      qexists_tac ‘n::path’ >>
      rw[] >>
      metis_tac[MEM_EL])
QED

Theorem eval_to_freevars_SUBSET:
  ∀k e1 v e2 x y.
    eval_to k e1 = v ∧ y ∈ freevars_v v ⇒
    MEM y (freevars e1)
Proof
  ho_match_mp_tac eval_to_ind >> rpt strip_tac
  >- (rename1 ‘Var’ >> gvs[eval_to_def])
  >- (rename1 ‘Prim’ >> gs[eval_to_def] >>
      drule eval_op_cases >> rw[] >>
      gvs[eval_op_def,AllCaseEqs(),MAP_EQ_CONS,DISJ_IMP_THM,FORALL_AND_THM,MEM_MAP,MEM_FLAT,PULL_EXISTS]
      >- metis_tac[]
      >- (rpt(PURE_FULL_CASE_TAC >> gvs[]) >> metis_tac[])
      >- (gvs[el_def,AllCaseEqs()] >>
          rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
          gvs[PULL_EXISTS,MEM_EL] >>
          metis_tac[])
      >- (PURE_FULL_CASE_TAC >> gvs[] >>
          rename1 ‘if XX then _ else _’ >>
          PURE_FULL_CASE_TAC >> gvs[])
      >- (gvs[is_eq_def] >>
          rpt(PURE_FULL_CASE_TAC >> gvs[])))
  >- (rename1 ‘Lam’ >> gvs[freevars_def,MEM_FILTER,eval_to_def])
  >- (rename1 ‘App’ >>
      gvs[freevars_def,MEM_FILTER,eval_to_def] >>
      rpt(PURE_FULL_CASE_TAC >> gvs[]) >>
      res_tac >> fs[bind_def] >>
      PURE_FULL_CASE_TAC >> fs[freevars_subst] >>
      gvs[dest_Closure_def,AllCaseEqs(),MEM_FILTER,PULL_EXISTS])
  >- (rename1 ‘Letrec’ >>
      gvs[freevars_def,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS,eval_to_def] >>
      PURE_FULL_CASE_TAC >> gvs[] >>
      first_x_assum drule >> strip_tac >> fs[subst_funs_def,freevars_bind] >>
      reverse FULL_CASE_TAC >- fs[] >>
      gvs[MEM_FILTER] >>
      gvs[MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
      metis_tac[MEM_MAP,FST])
  >- (rename1 ‘Case’ >>
      gvs[freevars_def,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS,eval_to_def] >>
      PURE_FULL_CASE_TAC >> gvs[] >>
      res_tac >>
      drule freevars_expandCases >> strip_tac >>
      gvs[MEM_FILTER] >>
      disj2_tac >>
      goal_assum drule >>
      rw[MEM_FILTER])
QED

Theorem eval_to_Closure_freevars_SUBSET:
  ∀k e1 e2 x y.
    eval_to k e1 = Closure x e2 ∧ MEM y (freevars e2) ⇒
    x = y ∨ MEM y (freevars e1)
Proof
  rpt strip_tac >> drule eval_to_freevars_SUBSET >>
  simp[MEM_FILTER] >>
  metis_tac[]
QED

Theorem eval_Closure_closed:
  eval e1 = Closure x e2 ∧ closed e1 ⇒
  set(freevars e2) ⊆ {x}
Proof
  rw[eval_def,Once gen_v] >>
  gvs[AllCaseEqs()] >>
  gvs[v_limit_def,limit_def,AllCaseEqs()] >>
  gvs[some_def] >>
  qpat_x_assum ‘_ = _’ mp_tac >>
  SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rw[] >>
  last_x_assum kall_tac >>
  first_x_assum(resolve_then (Pos hd) assume_tac LESS_EQ_REFL) >>
  gvs[v_lookup,AllCaseEqs()] >>
  drule eval_to_Closure_freevars_SUBSET >>
  rw[SUBSET_DEF] >>
  gvs[closed_def]
QED

Theorem reflexive_app_similarity: (* exercise (5.3.3) *)
  reflexive (UNCURRY $≲) closed
Proof
  rw[set_relationTheory.reflexive_def,ELIM_UNCURRY,IN_DEF] >>
  ‘∀x y. x = y ∧ closed x ⇒ x ≲ y’ suffices_by metis_tac[] >>
  pop_assum kall_tac >>
  ho_match_mp_tac app_similarity_coinduct >>
  rw[FF_def,ELIM_UNCURRY,unfold_rel_def] >>
  simp[] >>
  drule_all eval_Closure_closed >>
  simp[closed_def,freevars_subst] >>
  strip_tac >>
  rename [‘freevars (subst x e1 e2)’] >>
  ‘∀v. MEM v (freevars (subst x e1 e2)) ⇒ F’
    by(rpt strip_tac >>
       gvs[freevars_subst] >>
       drule_all SUBSET_THM >> simp[]) >>
  Cases_on ‘freevars (subst x e1 e2)’ >> gvs[FORALL_AND_THM]
QED

Theorem reflexive_app_similarity':
  closed x ⇒ x ≲ x
Proof
  mp_tac reflexive_app_similarity >>
  rw[set_relationTheory.reflexive_def,IN_DEF]
QED

Theorem transitive_app_similarity: (* exercise (5.3.3) *)
  transitive $≲
Proof
  rw[transitive_def,ELIM_UNCURRY,IN_DEF] >>
  rpt(first_x_assum mp_tac) >>
  simp[AND_IMP_INTRO] >>
  rename [‘x ≲ y ∧ y ≲ z’] >>
  MAP_EVERY qid_spec_tac [‘y’,‘z’,‘x’] >>
  simp[GSYM PULL_EXISTS] >>
  ho_match_mp_tac app_similarity_coinduct >>
  rw[ELIM_UNCURRY,FF_def,unfold_rel_def] >>
  imp_res_tac app_similarity_closed >>
  rpt(qpat_x_assum ‘_ ≲ _’ (strip_assume_tac o PURE_ONCE_REWRITE_RULE[app_similarity_iff])) >>
  gvs[unfold_rel_def] >>
  metis_tac[]
QED

Theorem app_bisimilarity_similarity: (* prop (5.3.4) *)
  e1 ≃ e2 ⇔ e1 ≲ e2 ∧ e2 ≲ e1
Proof
  eq_tac \\ rw []
  THEN1
   (assume_tac app_bisimulation_app_bisimilarity
    \\ fs [app_bisimulation_def]
    \\ imp_res_tac app_simulation_SUBSET_app_similarity
    \\ fs [SUBSET_DEF,IN_DEF])
  THEN1
   (assume_tac app_bisimulation_app_bisimilarity
    \\ fs [app_bisimulation_def]
    \\ imp_res_tac app_simulation_SUBSET_app_similarity
    \\ fs [SUBSET_DEF,IN_DEF,opp_def])
  \\ rpt(pop_assum mp_tac)
  \\ simp[AND_IMP_INTRO]
  \\ MAP_EVERY qid_spec_tac [‘e2’,‘e1’]
  \\ ho_match_mp_tac app_bisimilarity_coinduct
  \\ rpt GEN_TAC
  \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘FF R’
  \\ ‘opp R = R’ by(simp[FUN_EQ_THM] >> Cases >> rw[opp_def,Abbr‘R’,ELIM_UNCURRY,EQ_IMP_THM])
  \\ pop_assum SUBST_ALL_TAC
  \\ rw[Abbr ‘R’,FF_def,unfold_rel_def,ELIM_UNCURRY]
  \\ imp_res_tac app_similarity_closed
  \\ rpt(qpat_x_assum ‘_ ≲ _’ (strip_assume_tac o PURE_ONCE_REWRITE_RULE[app_similarity_iff]))
  \\ gvs[unfold_rel_def]
QED

Theorem reflexive_app_bisimilarity: (* exercise (5.3.3) *)
  reflexive (UNCURRY $≃) closed
Proof
  rw[set_relationTheory.reflexive_def,app_bisimilarity_similarity,ELIM_UNCURRY] >>
  imp_res_tac(reflexive_app_similarity |> SIMP_RULE std_ss [set_relationTheory.reflexive_def,ELIM_UNCURRY]) >>
  gvs[]
QED

Theorem symmetric_app_bisimilarity: (* exercise (5.3.3) *)
  symmetric $≃
Proof
  rw[app_bisimilarity_similarity,symmetric_def,EQ_IMP_THM]
QED

Theorem transitive_app_bisimilarity: (* exercise (5.3.3) *)
  transitive $≃
Proof
  rw[app_bisimilarity_similarity,transitive_def] >>
  imp_res_tac(transitive_app_similarity |> SIMP_RULE std_ss [transitive_def])
QED

(* -- Applicative simulation up-to à la Damien Pous (LICS 2016) -- *)
Definition compatible_def:
  compatible f ⇔ (∀B. f(FF B) ⊆ FF(f B))
End

Definition companion_def:
  companion R xy ⇔ ∃f. monotone f ∧ compatible f ∧ xy ∈ f(UNCURRY R)
End

Theorem companion_compatible:
  compatible ((companion o CURRY))
Proof
  mp_tac monotone_similarity >>
  rw[compatible_def,companion_def,pred_setTheory.SUBSET_DEF,IN_DEF,monotone_def] >>
  res_tac >>
  last_x_assum(match_mp_tac o MP_CANON) >>
  goal_assum(drule_at (Pos last)) >>
  rw[companion_def] >>
  qexists_tac ‘f’ >>
  rw[compatible_def,companion_def,pred_setTheory.SUBSET_DEF,IN_DEF,monotone_def] >>
  metis_tac[]
QED

Theorem companion_monotone:
  monotone(companion o CURRY)
Proof
  rw[monotone_def,pred_setTheory.SUBSET_DEF,companion_def,IN_DEF] >>
  rpt(goal_assum drule) >>
  metis_tac[]
QED

Theorem compatible_app_similarity:
  compatible (λR. app_similarity)
Proof
  rw[compatible_def,app_similarity_def] >>
  metis_tac[gfp_greatest_fixedpoint,monotone_similarity]
QED

Theorem opp_IN:
  (x,y) ∈ opp s ⇔ (y,x) ∈ s
Proof
  rw[opp_def,IN_DEF]
QED

Theorem companion_SUBSET:
  X ⊆ companion(CURRY X)
Proof
  rw[companion_def,pred_setTheory.SUBSET_DEF,IN_DEF] >>
  qexists_tac ‘I’ >>
  rw[monotone_def,compatible_def]
QED

Theorem monotone_compose:
  monotone f ∧ monotone g ⇒ monotone(f o g)
Proof
  rw[monotone_def,pred_setTheory.SUBSET_DEF,IN_DEF] >> res_tac >> metis_tac[]
QED

Theorem compatible_compose:
  monotone f ∧ compatible f ∧ compatible g ⇒ compatible(f o g)
Proof
  rw[compatible_def,pred_setTheory.SUBSET_DEF,IN_DEF,monotone_def] >>
  first_x_assum match_mp_tac >>
  last_x_assum(match_mp_tac o MP_CANON) >>
  goal_assum(drule_at (Pos last)) >>
  metis_tac[]
QED

Theorem companion_idem:
  companion (CURRY (companion (CURRY B))) = companion(CURRY B)
Proof
  rw[companion_def,FUN_EQ_THM,EQ_IMP_THM]
  >- (qexists_tac ‘f o companion o CURRY’ >>
      simp[compatible_compose,companion_compatible,monotone_compose,companion_monotone]) >>
  qexists_tac ‘I’ >>
  simp[monotone_def,compatible_def] >>
  gvs[IN_DEF,companion_def] >> metis_tac[]
QED

Theorem gfp_companion_SUBSET:
  gfp(FF o companion o CURRY) ⊆ gfp FF
Proof
  match_mp_tac (MP_CANON gfp_coinduction) >>
  conj_tac >- ACCEPT_TAC monotone_similarity >>
  rw[pred_setTheory.SUBSET_DEF,IN_DEF] >>
  ‘monotone(FF ∘ companion ∘ CURRY)’ by simp[monotone_compose,monotone_similarity,companion_monotone] >>
  first_assum(mp_tac o GSYM o MATCH_MP (cj 1 gfp_greatest_fixedpoint)) >>
  disch_then(gs o single o Once) >>
  mp_tac monotone_similarity >>
  simp[monotone_def,pred_setTheory.SUBSET_DEF,IN_DEF] >>
  disch_then(match_mp_tac o MP_CANON) >>
  goal_assum(dxrule_at (Pos last)) >>
  rpt strip_tac >>
  first_assum(mp_tac o GSYM o MATCH_MP (cj 1 gfp_greatest_fixedpoint)) >>
  disch_then(gs o single o Once) >>
  mp_tac companion_compatible >>
  simp[compatible_def,pred_setTheory.SUBSET_DEF,IN_DEF] >>
  disch_then dxrule >>
  strip_tac >>
  gvs[companion_idem] >>
  first_assum(mp_tac o GSYM o MATCH_MP (cj 1 gfp_greatest_fixedpoint)) >>
  disch_then(simp o single o Once)
QED

Theorem app_similarity_companion_coind:
  ∀R. (∀v1 v2. R v1 v2 ⇒ FF (companion R) (v1,v2)) ⇒
      ∀v1 v2. R v1 v2 ⇒ v1 ≲ v2
Proof
  ntac 2 strip_tac >>
  rw[app_similarity_def] >>
  match_mp_tac(MP_CANON pred_setTheory.SUBSET_THM |> SIMP_RULE std_ss [IN_DEF]) >>
  irule_at (Pos hd) gfp_companion_SUBSET >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [‘v2’,‘v1’] >>
  simp[PFORALL_THM,ELIM_UNCURRY] >>
  simp[GSYM(pred_setTheory.SUBSET_DEF |> SIMP_RULE std_ss [IN_DEF])] >>
  CONV_TAC(DEPTH_CONV ETA_CONV) >>
  match_mp_tac (MP_CANON gfp_coinduction) >>
  simp[monotone_compose,monotone_similarity,companion_monotone] >>
  rw[pred_setTheory.SUBSET_DEF,IN_DEF,ELIM_UNCURRY] >>
  first_x_assum drule >> gs[CURRY_UNCURRY_THM |> SIMP_RULE bool_ss [ELIM_UNCURRY]]
QED

Theorem companion_refl[simp]:
  closed x ⇒ companion R (x,x)
Proof
  rw[companion_def] >>
  irule_at Any compatible_app_similarity >>
  simp[IN_DEF,monotone_def,reflexive_app_similarity']
QED

Theorem companion_v_rel:
  x ≲ y ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  irule_at Any compatible_app_similarity >>
  simp[IN_DEF,v_rel_refl,monotone_def]
QED

Theorem FF_trans:
  ∀R S x y z.
    (x,z) ∈ FF R ∧ (z,y) ∈ FF S ⇒ (x,y) ∈ FF {(x,y) | ∃z. (x,z) ∈ R ∧ (z,y) ∈ S}
Proof
  rw[FF_def,IN_DEF,ELIM_UNCURRY,unfold_rel_def] >>
  metis_tac[]
QED

Theorem companion_duplicate:
  ∀x y z. companion R (x,z) ∧ companion R (z,y) ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  qexists_tac ‘λR. {(x,y) | ∃z. (x,z) ∈ f R ∧ (z,y) ∈ f' R}’ >>
  gvs[monotone_def,compatible_def,pred_setTheory.SUBSET_DEF] >>
  conj_tac >- (rw[] >> metis_tac[]) >>
  reverse conj_tac >- metis_tac[] >>
  rw[] >>
  res_tac >>
  metis_tac[FF_trans]
QED

Theorem companion_duplicate_SET:
  ∀x y z. (x,z) ∈ companion R ∧ (z,y) ∈ companion R ⇒ (x,y) ∈ companion R
Proof
  metis_tac[IN_DEF,companion_duplicate]
QED

Theorem companion_rel:
  ∀R x y. R x y ⇒ companion R (x,y)
Proof
  rw[companion_def] >>
  qexists_tac ‘I’ >> rw[monotone_def,compatible_def,IN_DEF]
QED

(* -- more lemmas -- *)

Theorem res_eq_IMP_app_bisimilarity: (* exercise (5.3.5) *)
  ∀e1 e2 x t. eval e1 = Closure x t ∧ closed e1 ∧ closed e2 ∧ eval e2 = Closure x t ⇒ e1 ≲ e2
Proof
  simp[GSYM PULL_EXISTS] >>
  ho_match_mp_tac app_similarity_companion_coind >>
  rw[FF_def,unfold_rel_def,ELIM_UNCURRY] >> gvs[] >>
  rpt strip_tac >>
  match_mp_tac companion_refl >>
  drule eval_Closure_closed >>
  simp[] >>
  rw[closed_def] >>
  rename [‘freevars (subst x e1 e2)’] >>
  ‘∀v. MEM v (freevars (subst x e1 e2)) ⇒ F’
    by(rpt strip_tac >> gvs[freevars_subst] >>
       drule_all SUBSET_THM >> rw[]) >>
  Cases_on ‘freevars (subst x e1 e2)’ >> fs[FORALL_AND_THM]
QED

(* -- congruence -- *)

(* TODO: not sure why this is parameterised on a set of names.
   Can't we just always choose the support of the two procs involved?
   I'm sure Andy knows what he's doing though so I'll roll with it...
 *)
(* TODO: cute mixfix syntax with ⊢ and all would be cute *)
(* Substitution closure of applicative bisimilarity. *)
Definition open_similarity_def:
  open_similarity names e1 e2 ⇔
    set(freevars e1) ∪ set(freevars e2) ⊆ names ∧
    ∀f. names = FDOM f ⇒ bind f e1 ≲ bind f e2
End

Definition open_bisimilarity_def:
  open_bisimilarity names e1 e2 ⇔
    set(freevars e1) ∪ set(freevars e2) ⊆ names ∧
    ∀f. names = FDOM f ⇒ bind f e1 ≃ bind f e2
End

Definition Ref_def:
  Ref R ⇔
    ∀vars e. e IN Exps vars ⇒ R vars e e
End

Definition Sym_def:
  Sym R ⇔
    ∀vars e1 e2.
      {e1; e2} SUBSET Exps vars ⇒
      R vars e1 e2 ⇒ R vars e2 e1
End

Definition Tra_def:
  Tra R ⇔
    ∀vars e1 e2 e3.
      {e1; e2; e3} SUBSET Exps vars ⇒
      R vars e1 e2 ∧ R vars e2 e3 ⇒ R vars e1 e3
End

Definition Com1_def:
  Com1 R ⇔
    ∀vars x.
      x IN vars ⇒
      R vars (Var x) (Var x)
End

Definition Com2_def:
  Com2 R ⇔
    ∀vars x e e'.
      ~(x IN vars) ∧ {e; e'} SUBSET Exps (x INSERT vars) ⇒
      R (x INSERT vars) e e' ⇒ R vars (Lam x e) (Lam x e')
End

Definition Com3_def:
  Com3 R ⇔
    ∀vars e1 e1' e2 e2'.
      {e1; e1'; e2; e2'} SUBSET Exps vars ⇒
      R vars e1 e1' ∧ R vars e2 e2' ⇒ R vars (App e1 e2) (App e1' e2')
End

Definition Compatible_def:
  Compatible R ⇔ Com1 R ∧ Com2 R ∧ Com3 R
End

Definition Precongruence_def:
  Precongruence R ⇔ Tra R ∧ Compatible R
End

Definition Congruence_def:
  Congruence R ⇔ Sym R ∧ Precongruence R
End

Theorem Ref_open_similarity:
  Ref open_similarity
Proof
  fs[Ref_def, Exps_def]
  \\ rw[open_similarity_def]
  \\ irule reflexive_app_similarity'
  \\ cheat
QED

Theorem Sym_open_similarity:
  Sym open_bisimilarity
Proof
  rw[Sym_def, open_bisimilarity_def]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs[symmetric_def]
QED

(* (Tra) in the paper has an amusing typo that renders the corresponding
   proposition a tautology *)
Theorem open_similarity_transitive:
  open_similarity names e1 e2 ∧ open_similarity names e2 e3 ⇒ open_similarity names e1 e3
Proof
  rw[open_similarity_def] >>
  metis_tac[transitive_app_similarity |> SIMP_RULE std_ss[transitive_def]]
QED

Theorem Tra_open_similarity:
  Tra open_similarity
Proof
  rw[Tra_def]
  \\ irule open_similarity_transitive
  \\ goal_assum drule \\ fs[]
QED

Theorem Tra_open_bisimilarity:
  Tra open_bisimilarity
Proof
  cheat
QED

(* (Com1) in Pitts *)
Theorem open_similarity_var_refl:
  x IN names ⇒ open_similarity names (Var x) (Var x)
Proof
  rw[open_similarity_def]
  \\ rw [bind_all_def,subst_all_def,FLOOKUP_DEF]
  \\ res_tac
  \\ match_mp_tac reflexive_app_similarity' \\ fs []
  \\ fs [closed_def]
QED

(* (Com2) in Pitts *)
Theorem open_similarity_Lam_pres:
  open_similarity (x INSERT names) e1 e2 ⇒
  open_similarity names (Lam x e1) (Lam x e2)
Proof
  cheat (*
  rw[open_similarity_def,SUBSET_DEF,MEM_FILTER] >>
  TRY(res_tac >> gvs[] >> NO_TAC) >>
  simp[bind_Lam,MAP_ZIP] >>
  simp[app_similarity_iff] >>
  simp[unfold_rel_def] >>
  conj_tac
  >- (
    fs[closed_def, app_similarity_iff, Once unfold_rel_def] >>
    first_x_assum (qspec_then `(Cons s [])::exps` assume_tac) >>
    gvs[closed_def, bind_def] >>
    pop_assum mp_tac >>
    once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    `closed (Cons s [])` by fs[closed_def] >>
    drule freevars_subst >> disch_then (once_rewrite_tac o single) >>
    fs[SUBSET_DIFF_EMPTY, SUBSET_DEF, FILTER_EQ_NIL, EVERY_MEM]
    ) >>
  conj_tac
  >- (
    fs[closed_def, app_similarity_iff, Once unfold_rel_def] >>
    first_x_assum (qspec_then `(Cons s [])::exps` assume_tac) >>
    gvs[closed_def, bind_def] >>
    pop_assum kall_tac >> pop_assum mp_tac >>
    once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    `closed (Cons s [])` by fs[closed_def] >>
    drule freevars_subst >> disch_then (once_rewrite_tac o single) >>
    fs[SUBSET_DIFF_EMPTY, SUBSET_DEF, FILTER_EQ_NIL, EVERY_MEM]
    ) >>
  rw[eval_thm] >>
  first_x_assum(qspec_then ‘e::exps’ mp_tac) >>
  simp[bind_def] *)
QED

(* (Com3L) in Pitts *)
Theorem open_similarity_App_pres1:
  open_similarity names e1 e2 ∧ freevars e3 ⊆ names ⇒
  open_similarity names (App e1 e3) (App e2 e3)
Proof
  cheat (*
  rw[open_similarity_def,SUBSET_DEF,MEM_FILTER] >> gvs[bind_App,MAP_ZIP] >>
  simp[app_similarity_iff] >>
  simp[unfold_rel_def] >>
  conj_tac
  >- (
    fs[closed_def, app_similarity_iff, Once unfold_rel_def] >>
    once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    once_rewrite_tac[freevars_bind] >>
    fs[MAP_ZIP, FILTER_EQ_NIL, EVERY_MEM]
    ) >>
  conj_tac
  >- (
    fs[closed_def, app_similarity_iff, Once unfold_rel_def] >>
    once_rewrite_tac[GSYM LIST_TO_SET_EQ_EMPTY] >>
    once_rewrite_tac[freevars_bind] >>
    fs[MAP_ZIP, FILTER_EQ_NIL, EVERY_MEM]
    ) >>
  rpt strip_tac >>
  gvs[eval_App,AllCaseEqs(),PULL_FORALL,dest_Closure_def] >>
  last_x_assum drule_all >>
  simp[Once app_similarity_iff] >>
  rw[unfold_rel_def] >>
  simp[GSYM PULL_FORALL] >>
  gvs[bind_def] >>
  reverse IF_CASES_TAC >- fs[eval_thm] >>
  gvs[] >>
  first_assum drule >>
  SIMP_TAC std_ss [Once app_similarity_iff] >>
  rw[unfold_rel_def] *)
QED

(*
(* (Com3R) in Pitts *)
Theorem open_similarity_App_pres2:
  set(freevars e1) ⊆ set names ∧ open_similarity names e2 e3 ⇒
  open_similarity names (App e1 e2) (App e1 e3)
Proof
  (* This one seems more complicated than the preceding thms. Probably requires Howe's construction ;) *)
QED
*)

(* -- Permutations and alpha-equivalence -- *)

Definition perm1_def:
  perm1 v1 v2 v = if v = v1 then v2 else if v = v2 then v1 else v
End

Definition perm_exp_def:
  (perm_exp v1 v2 (Var v) = Var (perm1 v1 v2 v))
  ∧ (perm_exp v1 v2 (Prim op l) = Prim op (MAP (perm_exp v1 v2) l))
  ∧ (perm_exp v1 v2 (App e1 e2) = App (perm_exp v1 v2 e1) (perm_exp v1 v2 e2))
  ∧ (perm_exp v1 v2 (Lam v e) = Lam (perm1 v1 v2 v) (perm_exp v1 v2 e))
  ∧ (perm_exp v1 v2 (Letrec l e) =
     Letrec
        (MAP (λ(x,z). (perm1 v1 v2 x, perm_exp v1 v2 z)) l)
        (perm_exp v1 v2 e)
     )
  ∧ (perm_exp v1 v2 (Case e s l) =
       Case (perm_exp v1 v2 e)
            (perm1 v1 v2 s)
            (MAP (λ(x,y,z). (x, MAP (perm1 v1 v2) y, perm_exp v1 v2 z)) l)
     )
Termination
  WF_REL_TAC ‘measure(exp_size o SND o SND)’ >>
  rw[] >> imp_res_tac exp_size_lemma >> rw[]
End

Theorem perm1_cancel[simp]:
  perm1 v1 v2 (perm1 v1 v2 x) = x
Proof
  rw[perm1_def] >> fs[CaseEq "bool"] >> fs[]
QED

Theorem perm_exp_cancel[simp]:
  ∀v1 v2 e. perm_exp v1 v2 (perm_exp v1 v2 e) = e
Proof
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def,MAP_MAP_o,combinTheory.o_DEF,ELIM_UNCURRY] >>
  rw[LIST_EQ_REWRITE] >>
  gvs[MEM_EL,PULL_EXISTS,EL_MAP] >>
  metis_tac[PAIR,FST,SND]
QED

Theorem perm1_eq_cancel[simp]:
  perm1 v1 v2 v3 = perm1 v1 v2 v4 ⇔ v3 = v4
Proof
  rw[perm1_def] >> simp[]
QED

Theorem perm_exp_eqvt:
  ∀fv2 fv3 e.
    MAP (perm1 fv2 fv3) (freevars e) = freevars(perm_exp fv2 fv3 e)
Proof
  ho_match_mp_tac perm_exp_ind >>
  rw[perm_exp_def,freevars_def,FILTER_MAP,combinTheory.o_DEF,MAP_MAP_o,MAP_FLAT]
  >- (AP_TERM_TAC >> rw[MAP_EQ_f])
  >- (pop_assum (assume_tac o GSYM) >>
      rw[FILTER_MAP,combinTheory.o_DEF])
  >- (rw[ELIM_UNCURRY] >>
      pop_assum (assume_tac o GSYM) >>
      simp[FILTER_APPEND] >>
      simp[FILTER_MAP,combinTheory.o_DEF] >>
      qmatch_goalsub_abbrev_tac ‘a1 ++ a2 = a3 ++ a4’ >>
      ‘a1 = a3 ∧ a2 = a4’ suffices_by simp[] >>
      unabbrev_all_tac >>
      conj_tac >- (AP_TERM_TAC >> rw[FILTER_EQ,MEM_MAP]) >>
      rw[FILTER_FLAT,MAP_FLAT,MAP_MAP_o,combinTheory.o_DEF,FILTER_FILTER] >>
      AP_TERM_TAC >>
      rw[MAP_EQ_f] >>
      PairCases_on ‘x’ >>
      first_assum (drule_then (assume_tac o GSYM o SIMP_RULE std_ss [])) >>
      simp[FILTER_MAP,combinTheory.o_DEF,MEM_MAP])
  >- (AP_TERM_TAC >>
      rw[MAP_EQ_f,ELIM_UNCURRY] >>
      PairCases_on ‘x’ >>
      first_assum(drule_then (assume_tac o GSYM)) >>
      gvs[FILTER_MAP,combinTheory.o_DEF,MEM_MAP])
QED

Theorem closed_perm:
  closed(perm_exp v1 v2 e) = closed e
Proof
  rw[closed_def,GSYM perm_exp_eqvt]
QED

Definition perm_v_def:
  perm_v x y v =
  gen_v (λpath.
          case v_lookup path v of
            (Closure' z e, len) => (Closure' (perm1 x y z) (perm_exp x y e), len)
          | x => x)
End

Theorem perm_v_thm:
  perm_v x y v =
  case v of
    Constructor s xs => Constructor s (MAP (perm_v x y) xs)
  | Closure z e => Closure (perm1 x y z) (perm_exp x y e)
  | v => v
Proof
  ‘∀v1 v2. ((∃v. v1 = perm_v x y v ∧
               v2 = (case v of
                       Constructor s xs => Constructor s (MAP (perm_v x y) xs)
                     | Closure z e => Closure (perm1 x y z) (perm_exp x y e)
                     | v => v)) ∨ v1 = v2)
           ⇒ v1 = v2’ suffices_by metis_tac[] >>
  ho_match_mp_tac v_coinduct >>
  reverse(rw[])
  >- (Cases_on ‘v1’ >> gvs[] >> match_mp_tac EVERY2_refl >> rw[]) >>
  TOP_CASE_TAC
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Atom])
  >- (rw[Once perm_v_def] >> rw[Once gen_v,v_lookup_Constructor] >>
      ‘MAP (perm_v x y) t =
       MAP (perm_v x y) (GENLIST (λx. EL x t) (LENGTH t))
      ’
       by(AP_TERM_TAC >> CONV_TAC SYM_CONV >>
          match_mp_tac GENLIST_EL >> rw[]) >>
      pop_assum SUBST_ALL_TAC >>
      simp[MAP_GENLIST] >>
      rw[LIST_REL_GENLIST,oEL_THM] >>
      simp[perm_v_def])
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Closure])
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Diverge] >> rw[gen_v_Diverge])
  >- (rw[perm_v_def] >> rw[Once gen_v,v_lookup_Error])
QED

Theorem perm_v_clauses:
  perm_v x y (Constructor s xs) = Constructor s (MAP (perm_v x y) xs) ∧
  perm_v x y Diverge = Diverge ∧
  perm_v x y (Atom b) = Atom b
  (* TODO: add more *)
Proof
  cheat
QED

Theorem perm_v_cancel[simp]:
  perm_v x y (perm_v x y v) = v
Proof
  ‘∀v1 v2. v2 = perm_v x y (perm_v x y v1) ⇒ v1 = v2’ suffices_by metis_tac[] >>
  ho_match_mp_tac v_coinduct >>
  Cases >> TRY(rw[perm_v_thm] >> NO_TAC) >>
  ntac 2 (rw[Once perm_v_thm]) >>
  rw[LIST_REL_MAP2] >>
  match_mp_tac EVERY2_refl >> rw[]
QED

Definition perm_v_prefix_def:
  perm_v_prefix x y v =
  case v of
  | Closure' z e => Closure' (perm1 x y z) (perm_exp x y e)
  | v => v
End

Theorem gen_v_eqvt:
  perm_v v1 v2 (gen_v f) = gen_v(λx. (perm_v_prefix v1 v2 ## I) (f x))
Proof
  ‘∀v v' v1 v2 f. v = perm_v v1 v2 (gen_v f) ∧
                  v' = gen_v(λx. (perm_v_prefix v1 v2 ## I) (f x)) (*∨ v = v'*) ⇒ v = v'’
    suffices_by metis_tac[] >>
  Ho_Rewrite.PURE_REWRITE_TAC [GSYM PULL_EXISTS] >>
  ho_match_mp_tac v_coinduct >>
  reverse(rw[]) >> (*(Cases_on ‘v’ >> rw[] >> match_mp_tac EVERY2_refl >> simp[]) >>*)
  simp[Once gen_v] >> rpt(TOP_CASE_TAC)
  >- (rename1 ‘Atom’ >>
      disj1_tac >> simp[perm_v_def,v_lookup_Atom] >>
      simp[Once gen_v] >>
      simp[Once gen_v] >>
      simp[perm_v_prefix_def])
  >- (rename1 ‘Constructor’ >>
      disj2_tac >> disj1_tac >>
      simp[Once gen_v] >>
      simp[Once perm_v_thm] >>
      simp[Once gen_v,v_lookup_Constructor] >>
      simp[Once perm_v_prefix_def] >>
      rw[MAP_GENLIST,LIST_REL_GENLIST] >>
      qexists_tac ‘v1’ >>
      qexists_tac ‘v2’ >>
      qexists_tac ‘f o CONS n’ >>
      simp[combinTheory.o_DEF])
  >- (rename1 ‘Closure’ >>
      ntac 2 disj2_tac >> disj1_tac >>
      simp[Once gen_v] >>
      simp[Once perm_v_thm] >>
      simp[Once gen_v,v_lookup_Constructor] >>
      simp[Once perm_v_prefix_def])
  >- (rename1 ‘Diverge’ >>
      ntac 3 disj2_tac >> disj1_tac >>
      PURE_ONCE_REWRITE_TAC[gen_v] >>
      simp[] >>
      PURE_ONCE_REWRITE_TAC[perm_v_thm] >>
      simp[] >>
      PURE_ONCE_REWRITE_TAC[perm_v_prefix_def] >>
      simp[])
  >- (rename1 ‘Error’ >>
      ntac 4 disj2_tac >>
      simp[Once gen_v] >>
      simp[Once perm_v_thm] >>
      simp[Once gen_v,v_lookup_Constructor] >>
      simp[Once perm_v_prefix_def])
QED

Theorem perm_v_inj:
 (perm_v v1 v2 v = perm_v v1 v2 v') ⇔ v = v'
Proof
  cheat
QED

Theorem eval_to_eqvt:
  ∀v1 v2 k e. perm_v v1 v2 (eval_to k e) =
              eval_to k (perm_exp v1 v2 e)
Proof
  ntac 2 strip_tac >>
  ho_match_mp_tac eval_to_ind >>
  rw[] >>
  rw[perm_v_thm,eval_to_def,perm_exp_def]
  >- (‘eval_op op (MAP (λa. eval_to k a) xs) = eval_op op (MAP (λa. eval_to k a) xs)’ by metis_tac[] >>
      dxrule eval_op_cases >> rw[] >>
      gvs[eval_op_def,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,MAP_EQ_CONS,MEM_MAP,PULL_EXISTS,DISJ_IMP_THM,
          FORALL_AND_THM]
      >- (‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
            by metis_tac[perm_v_inj] >>
          simp[perm_v_thm] >>
          pop_assum kall_tac >>
          rw[] >>
          TOP_CASE_TAC >> gvs[perm_v_thm])
      >- (rw[el_def] >> gvs[perm_v_thm] >>
          Cases_on ‘eval_to k a’ >> gvs[]
          >- (gvs[AllCaseEqs()] >> metis_tac[])
          >- cheat
          >- (gvs[AllCaseEqs()] >> metis_tac[]))
      >- (IF_CASES_TAC
          >- (simp[] >> gvs[] >>
              IF_CASES_TAC >> rw[] >>
              gvs[] >>
              rename1 ‘eval_to k e’ >>
              first_x_assum(qspec_then ‘e’ mp_tac) >>
              rw[] >>
              ‘∀x. eval_to k e = x ⇔ (perm_v v1 v2 (eval_to k e) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_thm]) >>
          cheat)
      >- (rw[is_eq_def]
          >- (‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_thm])
          >- (TOP_CASE_TAC >> fs[MAP_MAP_o,combinTheory.o_DEF] >>
              gvs[AllCaseEqs()] >>
              ‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_thm])
          >- (TOP_CASE_TAC >> fs[MAP_MAP_o,combinTheory.o_DEF] >>
              gvs[AllCaseEqs()] >>
              ‘∀x. eval_to k a = x ⇔ (perm_v v1 v2 (eval_to k a) = perm_v v1 v2 x)’
                by metis_tac[perm_v_inj] >>
              pop_assum(gvs o single) >>
              gvs[perm_v_clauses] >> gvs[perm_v_thm] >> metis_tac[LENGTH_MAP])))
  >- (gvs[perm_v_clauses])
  >- (gvs[perm_v_clauses] >>
      ‘∀x. eval_to k e = x ⇔ (perm_v v1 v2 (eval_to k e) = perm_v v1 v2 x)’
        by metis_tac[perm_v_inj] >>
      pop_assum(gvs o single) >>
      gvs[perm_v_clauses])
  >- (cheat)
  >- (cheat)
  >- (cheat)
QED

Theorem v_lookup_eqvt:
  ∀v1 v2 path v. (perm_v_prefix v1 v2 ## I) (v_lookup path v) =
                 v_lookup path (perm_v v1 v2 v)
Proof
  ntac 2 strip_tac >>
  Induct >>
  rw[v_lookup] >> TOP_CASE_TAC >> rw[perm_v_prefix_def,perm_v_thm] >>
  simp[oEL_THM] >> rw[EL_MAP,perm_v_prefix_def]
QED

Theorem eval_eqvt:
  perm_v v1 v2 (eval e) = eval (perm_exp v1 v2 e)
Proof
  simp[eval_def,gen_v_eqvt] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,v_limit_def] >>
  simp[limit_def] >>
  TOP_CASE_TAC
  >- (gvs[some_def] >>
      simp[Once perm_v_prefix_def] >>
      TOP_CASE_TAC >>
      gvs[AllCaseEqs()] >>
      SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
      pop_assum kall_tac >>
      rpt strip_tac >>
      last_x_assum(qspecl_then [‘(perm_v_prefix v1 v2 ## I) x’,‘k’] strip_assume_tac) >>
      first_x_assum drule >> strip_tac >>
      rename1 ‘eval_to k'’ >>
      ‘(perm_v_prefix v1 v2 ## I) (v_lookup path (eval_to k' (perm_exp v1 v2 e))) = (perm_v_prefix v1 v2 ## I) x’
        by metis_tac[] >>
      qpat_x_assum ‘_ = x’ kall_tac >>
      gvs[v_lookup_eqvt,eval_to_eqvt])
  >- (gvs[some_def] >>
      SELECT_ELIM_TAC >> conj_tac >- metis_tac[] >>
      last_x_assum kall_tac >> rpt strip_tac >>
      IF_CASES_TAC
      >- (SELECT_ELIM_TAC >>
          conj_tac >- metis_tac[] >>
          pop_assum kall_tac >> rw[] >>
          first_x_assum(qspec_then ‘MAX k k'’ mp_tac) >> simp[] >>
          first_x_assum(qspec_then ‘MAX k k'’ mp_tac) >> simp[] >>
          rpt(disch_then(assume_tac o GSYM)) >>
          rw[v_lookup_eqvt,eval_to_eqvt]) >>
      gvs[] >>
      last_x_assum(qspecl_then [‘(perm_v_prefix v1 v2 ## I) x’,‘k’] strip_assume_tac) >>
      first_x_assum drule >> strip_tac >>
      rename1 ‘eval_to k'’ >>
      ‘(perm_v_prefix v1 v2 ## I) (v_lookup path (eval_to k' e)) = (perm_v_prefix v1 v2 ## I) x’
        by metis_tac[] >>
      qpat_x_assum ‘_ = x’ kall_tac >>
      gvs[v_lookup_eqvt,eval_to_eqvt])
QED

Theorem eval_perm_closure:
  eval (perm_exp v1 v2 e) = Closure x e' ⇔ eval e = Closure (perm1 v1 v2 x) (perm_exp v1 v2 e')
Proof
  simp[GSYM eval_eqvt,perm_v_thm,AllCaseEqs()] >>
  metis_tac[perm1_cancel,perm_exp_cancel]
QED

Theorem subst_eqvt:
  ∀v1 v2 x y e.
    perm_exp v1 v2 (subst x y e) =
    subst (perm1 v1 v2 x) (perm_exp v1 v2 y) (perm_exp v1 v2 e)
Proof
  ntac 2 strip_tac >> ho_match_mp_tac subst_ind >>
  rw[subst_def,perm_exp_def,MAP_MAP_o,combinTheory.o_DEF,MAP_EQ_f,ELIM_UNCURRY,MEM_MAP,PULL_EXISTS] >>
  rw[] >> metis_tac[PAIR,FST,SND]
QED

Theorem compatible_perm:
  compatible (λR. {(e1,e2) | ∃v1 v2 e3 e4. e1 = perm_exp v1 v2 e3  ∧ e2 = perm_exp v1 v2 e4 ∧ R(e3,e4)})
Proof
  rw[compatible_def] >> simp[SUBSET_DEF] >> Cases >> rw[FF_def,unfold_rel_def,ELIM_UNCURRY,eval_perm_closure] >>
  simp[closed_perm] >> gvs[eval_perm_closure] >>
  irule_at (Pos hd) (GSYM perm1_cancel) >>
  irule_at (Pos hd) (GSYM perm_exp_cancel) >>
  rw[] >>
  irule_at (Pos hd) (GSYM perm_exp_cancel) >>
  simp[subst_eqvt] >>
  PRED_ASSUM is_forall (irule_at (Pos last)) >>
  simp[subst_eqvt,closed_perm]
QED

Triviality CURRY_thm:
  CURRY f = λ x y. f(x,y)
Proof
  rw[FUN_EQ_THM]
QED

Theorem companion_app_similarity:
  ∀e1 e2. companion ($≲) (e1,e2) ⇒ e1 ≲ e2
Proof
  ho_match_mp_tac app_similarity_companion_coind >>
  rw[companion_idem |> SIMP_RULE std_ss [CURRY_thm]] >>
  mp_tac companion_compatible >>
  rw[compatible_def,CURRY_thm,SUBSET_DEF,IN_DEF] >>
  first_x_assum match_mp_tac >>
  gvs[] >>
  gvs[FF_def,ELIM_UNCURRY,GSYM app_similarity_iff]
QED

Theorem app_similarity_eqvt:
  e1 ≲ e2 ⇒ perm_exp x y e1 ≲ perm_exp x y e2
Proof
  strip_tac >>
  match_mp_tac companion_app_similarity >>
  simp[companion_def] >>
  irule_at Any compatible_perm >>
  rw[monotone_def,SUBSET_DEF] >>
  metis_tac[IN_DEF]
QED

Inductive exp_alpha:
[~Refl:]
  (∀avoid e. closed e ⇒ exp_alpha avoid e e) ∧
(*[~Sym:]
  (∀avoid e e'. exp_alpha avoid e' e ⇒ exp_alpha avoid e e') ∧*)
[~Trans:]
  (∀avoid e e' e''. exp_alpha avoid e e' ∧ exp_alpha avoid e' e'' ⇒ exp_alpha avoid e e'') ∧
[~Lam:]
  (∀avoid e x e'. (∀t. closed t ⇒ exp_alpha (x INSERT avoid) (subst x t e) (subst x t e')) ⇒ exp_alpha avoid (Lam x e) (Lam x e')) ∧
[~Alpha:]
  (∀avoid e x y. x ≠ y ∧ y ∉ avoid ∧ y ∉ set(freevars e)
                    ⇒ exp_alpha avoid (Lam x e) (Lam y (perm_exp x y e)))
  (* TODO: needs more congruence clauses to be useful *)
End

Theorem exp_alpha_mono_vars:
  ∀avoid e e' avoid'.
    exp_alpha avoid e e' ∧ avoid' ⊆ avoid ⇒
    exp_alpha avoid' e e'
Proof
  Induct_on ‘exp_alpha’ >>
  rw[]
  >- metis_tac[exp_alpha_rules]
  >- metis_tac[exp_alpha_rules]
  >- (match_mp_tac exp_alpha_Lam >>
      rw[] >>
      first_x_assum drule >>
      rw[] >>
      first_x_assum match_mp_tac >>
      gvs[SUBSET_DEF])
  >- (match_mp_tac exp_alpha_Alpha >>
      rw[] >>
      metis_tac[SUBSET_DEF])
QED

Theorem compatible_exp_alpha:
  compatible(λR (x,y). exp_alpha avoid x y)
Proof
  simp[compatible_def,SUBSET_DEF] >>
  PairCases >>
  rw[ELIM_UNCURRY] >>
  pop_assum mp_tac >>
  Induct_on ‘exp_alpha’ >>
  rw[]
  >- (gvs[FF_def,unfold_rel_def] >>
      rw[] >>
      match_mp_tac exp_alpha_Refl >>
      cheat)
  >- (dxrule_all FF_trans >>
      match_mp_tac(monotone_similarity |> SIMP_RULE std_ss [monotone_def,SUBSET_DEF]) >>
      rw[] >> rw[] >> metis_tac[exp_alpha_Trans])
  >- (gvs[FF_def,unfold_rel_def] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw[eval_thm] >>
      first_x_assum drule >> rw[] >>
      match_mp_tac exp_alpha_mono_vars >>
      goal_assum drule >>
      rw[SUBSET_DEF])
  >- (gvs[FF_def,unfold_rel_def] >>
      conj_tac >- cheat >>
      conj_tac >- cheat >>
      rw[eval_thm] >>
      cheat (* I expect there should be some (possibly convoluted) induction that proves this *)
      )
QED

Theorem companion_exp_alpha:
  exp_alpha avoid x y ⇒ (x,y) ∈ companion R
Proof
  rw[IN_DEF,companion_def] >>
  irule_at Any compatible_exp_alpha >>
  simp[monotone_def] >>
  goal_assum drule
QED

Theorem app_similarity_eqvt:
  x ≠ y ∧ closed(Lam x e1) ∧ y ∉ freevars e1 ⇒
  Lam x e1 ≲ Lam y (perm_exp x y e1)
Proof
  strip_tac >>
  match_mp_tac companion_app_similarity  >>
  match_mp_tac(companion_exp_alpha |> SIMP_RULE std_ss [IN_DEF] |> GEN_ALL) >>
  qexists_tac ‘{}’ >>
  match_mp_tac(GEN_ALL exp_alpha_Alpha) >>
  simp[]
QED

(* -- Howe's construction -- *)

Inductive Howe:
[Howe1:]
  (∀R vars x e2.
     R vars (Var x) e2 ⇒
     Howe R vars (Var x) e2)
  ∧
[Howe2:]
  (∀R x e1 e1' e2 vars.
     Howe R (x INSERT vars) e1 e1' ∧
     R vars (Lam x e1') e2 ∧
     ~(x IN vars) ⇒
     Howe R vars (Lam x e1) e2)
  ∧
[Howe3:]
  (∀R e1 e1' e3 vars.
     Howe R vars e1 e1' ∧
     Howe R vars e2 e2' ∧
     R vars (App e1' e2') e3 ⇒
     Howe R vars (App e1 e2) e3)
End

Theorem Howe_Ref: (* 5.5.1(i) *)
  Ref R ⇒ Compatible (Howe R)
Proof
  rw[Ref_def, Compatible_def]
  >- (
    rw[Com1_def] >>
    irule Howe1 >>
    first_x_assum irule >> fs[Exps_def]
    )
  >- (
    rw[Com2_def] >>
    irule Howe2 >> fs[] >>
    goal_assum (drule_at Any) >>
    first_x_assum irule >>
    fs[Exps_def, LIST_TO_SET_FILTER, SUBSET_DEF] >>
    metis_tac[]
    )
  >- (
    rw[Com3_def] >>
    irule Howe3 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[Exps_def]
    )
QED

Definition term_rel_def:
  term_rel R ⇔
    ∀vars e1 e2. R vars e1 e2 ⇒ e1 ∈ Exps vars ∧ e2 ∈ Exps vars
End

Theorem term_rel_Howe:
  term_rel R ⇒ term_rel (Howe R)
Proof
  fs[term_rel_def] >>
  Induct_on `Howe` >> rw[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    last_x_assum drule >>
    rw[Exps_def] >>
    fs[LIST_TO_SET_FILTER, SUBSET_DEF] >>
    metis_tac[]
    )
  >- metis_tac[]
  >- (
    last_x_assum drule >>
    last_x_assum drule >>
    rw[Exps_def]
    )
  >- metis_tac[]
QED

Theorem Howe_Tra: (* 5.5.1(ii) *)
  Tra R ∧ term_rel R ⇒
  ∀vars e1 e2 e3.
    e1 ∈ Exps vars ∧ e2 ∈ Exps vars ∧ e3 ∈ Exps vars ∧
    Howe R vars e1 e2 ∧ R vars e2 e3 ⇒ Howe R vars e1 e3
Proof
  rw[Tra_def] >>
  qpat_x_assum `Howe _ _ _ _` mp_tac >>
  simp[Once Howe_cases] >> rw[]
  >- (
    irule Howe1 >>
    first_x_assum irule >> fs[Exps_def] >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe2 >> fs[] >>
    goal_assum (drule_at Any) >>
    first_x_assum irule >>
    fs[term_rel_def] >> res_tac >> fs[] >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe3 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[] >> rw[]
    >- (
      drule term_rel_Howe >> simp[term_rel_def] >>
      disch_then imp_res_tac >>
      fs[Exps_def]
      ) >>
    qexists_tac `e2` >> fs[]
    )
QED

Theorem Howe_Ref_Tra: (* 5.5.1(iii) *)
  Ref R ⇒
  ∀vars e1 e2. R vars e1 e2 ⇒ Howe R vars e1 e2
Proof
  cheat
QED

Definition Sub_def: (* Sub = substitutive *)
  Sub R ⇔
    ∀vars x e1 e1' e2 e2'.
      x ∉ vars ∧
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ {e2; e2'} SUBSET Exps vars ⇒
      R (x INSERT vars) e1 e1' ∧ R vars e2 e2' ⇒
      R vars (subst x e2 e1) (subst x e2' e1')
  (* TODO: we should use a capture avoiding subst here! *)
End

Definition Cus_def: (* closed under value-substitution *)
  Cus R ⇔
    ∀vars x e1 e1' e2.
      x ∉ vars ∧
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ e2 IN Exps vars ⇒
      R (x INSERT vars) e1 e1' ⇒
      R vars (subst x e2 e1) (subst x e2 e1')
  (* TODO: we should use a capture avoiding subst here! *)
End

Theorem Sub_Ref_IMP_Cus:
  Sub R ∧ Ref R ⇒ Cus R
Proof
  rw[Sub_def, Ref_def, Cus_def]
QED

Theorem Cus_open_similarity:
  Cus open_similarity
Proof
  cheat
QED

Theorem Cus_open_bisimilarity:
  Cus open_bisimilarity
Proof
  cheat
QED

Theorem IMP_Howe_Sub: (* 5.5.3 *)
  Ref R ∧ Tra R ∧ Cus R ⇒ Sub (Howe R)
Proof
  cheat (* errata: says use 5.5.1(ii), i.e. Howe_Tra *)
QED

Theorem Ref_Howe:
  Ref R ⇒ Ref (Howe R)
Proof
(*  Unprovable for now, need moar clauses
  strip_tac >>
  gvs[Ref_def,Exps_def,PULL_FORALL] >>
  CONV_TAC SWAP_FORALL_CONV >>
  qsuff_tac ‘∀e vars vars'. ALL_DISTINCT(vars ++ vars') ∧ set (freevars e) ⊆ set vars ⇒ Howe R vars e e’
  >- (rpt strip_tac >> first_x_assum match_mp_tac >>
      rw[] >> qexists_tac ‘[]’ >> rw[]) >>
  Induct_on ‘e’
  >- (rename1 ‘Var’ >>
      rw[Once Howe_cases,ALL_DISTINCT_APPEND])
  >- (rename1 ‘Prim’ >>
      cheat)
  >- (rename1 ‘App’ >>
      rw[Once Howe_cases] >>
      first_x_assum drule_all >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      rpt(goal_assum drule) >>
      first_x_assum match_mp_tac >>
      rw[freevars_def] >> gvs[ALL_DISTINCT_APPEND])
  >- (rename1 ‘Lam’ >>
      cheat)
 *)
  cheat
QED

Theorem Cus_Howe_open_similarity:
  Cus (Howe open_similarity)
Proof
  match_mp_tac Sub_Ref_IMP_Cus \\ rw []
  \\ metis_tac [Ref_Howe,Ref_open_similarity,IMP_Howe_Sub,
       Cus_open_similarity,Tra_open_similarity,Ref_open_similarity]
QED

Theorem KeyLemma: (* key lemma 5.5.4 *)
  eval e1 = Closure x e ∧ Howe open_similarity {} e1 e2 ⇒
  ∃e'. eval e2 = Closure x e' ∧ Howe open_similarity {x} e e'
Proof
  cheat
QED

Theorem Howe_vars:
  Howe open_similarity vars e1 e2 ⇒
  freevars e1 ⊆ vars ∧ freevars e2 ⊆ vars
Proof
  qsuff_tac ‘∀R vars e1 e2.
     Howe R vars e1 e2 ⇒ R = open_similarity ⇒
     freevars e1 ⊆ vars ∧ freevars e2 ⊆ vars’ THEN1 metis_tac []
  \\ ho_match_mp_tac Howe_ind \\ rw []
  \\ fs [open_similarity_def]
  \\ fs [SUBSET_DEF,MEM_FILTER]
  \\ metis_tac []
QED

Theorem app_simulation_Howe_open_similarity:
  app_simulation (UNCURRY (Howe open_similarity {}))
Proof
  fs [app_simulation_def,unfold_rel_def]
  \\ cheat (* KeyLemma? *)
QED

(*
Theorem subst_bind:
  ∀vars t h v e1.
    h ∉ vars ∧ LENGTH t = LENGTH vars ∧ EVERY closed t ∧ closed v ⇒
    subst h v (bind (ZIP (vars,t)) e1) =
    bind (ZIP (vars,t)) (subst h v e1)
Proof
  Induct_on ‘vars’ \\ fs [bind_def] \\ rw []
  \\ Cases_on ‘t’ \\ fs [bind_def]
  \\ first_x_assum drule
  \\ rename [‘LENGTH tt = LENGTH _’]
  \\ disch_then drule \\ fs []
  \\ disch_then (drule o GSYM) \\ fs [] \\ rw []
  \\ match_mp_tac subst_subst \\ fs []
QED
*)

Theorem IMP_open_similarity_INSERT:
  (∀e. e IN Exps vars ⇒ open_similarity vars (subst h e e1) (subst h e e2)) ∧
  h ∉ vars ∧ e1 IN Exps (h INSERT vars) ∧ e2 IN Exps (h INSERT vars) ⇒
  open_similarity (h INSERT vars) e1 e2
Proof
  cheat (*
  fs [open_similarity_def] \\ rw [] \\ fs [Exps_def]
  \\ Cases_on ‘exps’ \\ fs [] \\ fs []
  \\ fs [subst_bind,bind_def]
  \\ ‘set (freevars h') ⊆ set vars’ by fs [closed_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] *)
QED

Theorem open_similarity_inter:
  open_similarity vars e1 e2 =
  open_similarity (vars INTER freevars (App e1 e2)) e1 e2
Proof
  cheat
QED

Theorem Howe_inter:
  ∀R vars e1 e2.
    Howe R vars e1 e2 ⇒
    ∀t. (∀vars e1 e2. R vars e1 e2 ⇒ R (vars INTER t e1 e2) e1 e2) ⇒
        Howe R (vars INTER t e1 e2) e1 e2
Proof
  cheat
QED

Theorem bind_FEMPTY[simp]:
  bind FEMPTY e1 = e1
Proof
  cheat
QED

Theorem bind_FDIFF:
  freevars x ⊆ vars ⇒
  bind f x = bind (FDIFF f (COMPL vars)) x
Proof
  cheat
QED

Theorem Howe_open_similarity: (* key property *)
  Howe open_similarity = open_similarity
Proof
  simp [FUN_EQ_THM] \\ rw []
  \\ rename [‘Howe open_similarity vars e1 e2’]
  \\ reverse eq_tac \\ rw []
  THEN1 (metis_tac [Howe_Ref_Tra,Ref_open_similarity,Tra_open_similarity])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def]
  \\ first_x_assum (qspec_then ‘{}’ mp_tac) \\ fs [] \\ rw []
  \\ assume_tac app_simulation_Howe_open_similarity
  \\ drule app_simulation_SUBSET_app_similarity
  \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ rw [SUBSET_DEF,IN_DEF,FORALL_PROD]
  \\ last_x_assum mp_tac
  \\ once_rewrite_tac [open_similarity_inter]
  \\ strip_tac \\ drule Howe_inter
  \\ disch_then (qspec_then ‘λe1 e2. freevars (App e1 e2)’ mp_tac)
  \\ fs [] \\ impl_tac THEN1 simp [Once open_similarity_inter]
  \\ ‘FINITE (vars ∩ (freevars (App e1 e2)))’ by
        (match_mp_tac FINITE_INTER \\ fs [])
  \\ fs [] \\ rename [‘FINITE t’]
  \\ qid_spec_tac ‘e2’
  \\ qid_spec_tac ‘e1’
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ qid_spec_tac ‘t’
  \\ Induct_on ‘FINITE’ \\ rw []
  THEN1
   (fs [open_similarity_def,FDOM_EQ_EMPTY] \\ res_tac
    \\ imp_res_tac Howe_vars \\ fs [])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def,AND_IMP_INTRO]
  \\ pop_assum (first_assum o mp_then Any mp_tac)
  \\ rw [] \\ simp []
  \\ match_mp_tac IMP_open_similarity_INSERT
  \\ imp_res_tac Howe_vars \\ fs [] \\ rw []
  \\ fs [Exps_def]
  \\ first_x_assum match_mp_tac
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem Precongruence_open_similarity: (* part 1 of 5.5.5 *)
  Precongruence open_similarity
Proof
  fs [Precongruence_def] \\ rw [Tra_open_similarity]
  \\ once_rewrite_tac [GSYM Howe_open_similarity]
  \\ match_mp_tac Howe_Ref
  \\ fs [open_similarity_def,Ref_open_similarity]
QED

Theorem Congruence_open_bisimilarity: (* part 2 of 5.5.5 *)
  Congruence open_bisimilarity
Proof
  fs [Congruence_def,Sym_open_similarity]
  \\ assume_tac Precongruence_open_similarity
  \\ fs [Precongruence_def,Tra_open_bisimilarity]
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com1_def,Com2_def,Com3_def,open_bisimilarity_def,open_similarity_def]
  \\ fs [app_bisimilarity_similarity]
  \\ metis_tac []
QED

(* -- contextual equivalence -- *)

Definition exp_eq_def:
  exp_eq x y ⇔
    ∀f. freevars x ∪ freevars y ⊆ FDOM f ⇒ bind f x ≃ bind f y
End

val _ = set_fixity "≅" (Infixl 480);
Overload "≅" = “exp_eq”;

Theorem subst_all_FDIFF:
  subst_all f x = subst_all (DRESTRICT f (freevars x)) x
Proof
  cheat
QED

Theorem exp_eq_open_bisimilarity:
  exp_eq x y ⇔ ∃vars. open_bisimilarity vars x y ∧
                      FINITE vars ∧ freevars x ∪ freevars y ⊆ vars
Proof
  eq_tac \\ rw []
  THEN1
   (fs [open_bisimilarity_def,SUBSET_DEF]
    \\ rw [] \\ fs [exp_eq_def]
    \\ qexists_tac ‘freevars (App x y)’ \\ fs []
    \\ rw [] \\ first_x_assum match_mp_tac
    \\ first_x_assum (assume_tac o GSYM) \\ fs [])
  \\ fs [exp_eq_def,open_bisimilarity_def] \\ rw []
  \\ fs [bind_all_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1
   (simp [Once app_bisimilarity_iff] \\ fs [eval_thm,closed_def])
  \\ first_x_assum (qspec_then ‘FUN_FMAP
        (λn. if n IN FDOM f then f ' n else Fail) vars’ mp_tac)
  \\ once_rewrite_tac [subst_all_FDIFF]
  \\ fs [FLOOKUP_FUN_FMAP]
  \\ reverse IF_CASES_TAC
  THEN1
   (fs [] \\ gvs [FLOOKUP_DEF] \\ Cases_on ‘n IN FDOM f’ \\ gvs []
    \\ res_tac \\ fs [closed_def]) \\ fs []
  \\ match_mp_tac (METIS_PROVE []
       “x1 = y1 ∧ x2 = y2 ⇒ f x1 x ≃ f x2 y ⇒ f y1 x ≃ f y2 y”)
  \\ fs [fmap_EXT,EXTENSION,DRESTRICT_DEF,FUN_FMAP_DEF,SUBSET_DEF]
  \\ metis_tac []
QED

Theorem Congruence_exp_eq:
  Congruence (K $≅)
Proof
  mp_tac Congruence_open_bisimilarity
  \\ rw [Congruence_def,Precongruence_def]
  \\ fs [Sym_def,exp_eq_def]
  THEN1 cheat
  THEN1 cheat
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com1_def,Com2_def,Com3_def] \\ rw []
  \\ fs [exp_eq_open_bisimilarity]
  THEN1 (qexists_tac ‘{x}’ \\ fs [])
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ cheat
QED

Theorem exp_eq_Lam:
  Lam x1 e1 ≅ Lam x2 e2 ⇔
  ∀y1 y2.
    y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
    subst x1 y1 e1 ≅ subst x2 y2 e2
Proof
  assume_tac Ref_open_similarity
  \\ drule IMP_Howe_Sub
  \\ fs [Cus_open_similarity,Tra_open_similarity,Howe_open_similarity]
  \\ fs [Sub_def] \\ rw []
  \\ eq_tac \\ rw []
  \\ fs [exp_eq_open_bisimilarity]
  \\ fs [bind_def,PULL_EXISTS]
  \\ cheat
QED

Theorem exp_eq_Lam_cong:
  e ≅ e' ⇒ Lam x e ≅ Lam x e'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com2_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Lam x e) (Lam x e'))’
  \\ fs [Exps_def,SUBSET_DEF] \\ fs [MEM_FILTER]
QED

Theorem exp_eq_App_cong:
  f ≅ f' ∧ e ≅ e' ⇒ App f e ≅ App f' e'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com3_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App f (App f' (App e e')))’
  \\ fs [Exps_def,SUBSET_DEF]
QED

val _ = export_theory();

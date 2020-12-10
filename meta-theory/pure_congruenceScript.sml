(*
   This file formalises Howe's method following the description of
   Pitts 2011 chapter "Howe's method for higher-order languages".
*)
open HolKernel Parse boolLib bossLib term_tactic;
open fixedPointTheory arithmeticTheory listTheory stringTheory alistTheory
     optionTheory pairTheory ltreeTheory llistTheory bagTheory
     BasicProvers pred_setTheory relationTheory rich_listTheory finite_mapTheory
     dep_rewrite;
open pure_expTheory pure_valueTheory pure_evalTheory pure_eval_lemmasTheory
     pure_exp_lemmasTheory pure_eval_altTheory pure_limitTheory
     pure_exp_relTheory pure_alpha_equivTheory;

val _ = new_theory "pure_congruence";


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
     (* ~(x IN vars) ∧ *) {e; e'} SUBSET Exps (x INSERT vars) ⇒
      R (x INSERT vars) e e' ⇒ R vars (Lam x e) (Lam x e')
End

Definition Com3_def:
  Com3 R ⇔
    ∀vars e1 e1' e2 e2'.
      {e1; e1'; e2; e2'} SUBSET Exps vars ⇒
      R vars e1 e1' ∧ R vars e2 e2' ⇒ R vars (App e1 e2) (App e1' e2')
End

Definition Com4_def:
  Com4 R ⇔
    ∀ vars es es' op.
      set es ∪ set es' ⊆ Exps vars ⇒
      LIST_REL (R vars) es es' ⇒ R vars (Prim op es) (Prim op es')
End

Definition Com5_def:
  Com5 R ⇔
    ∀ vars ves ves' e e'.
      {e; e'} ∪ set (MAP SND ves) ∪ set (MAP SND ves') ⊆
        Exps (vars ∪ set (MAP FST ves)) ⇒
   (* DISJOINT (set (MAP FST ves)) vars ⇒ *)
      MAP FST ves = MAP FST ves' ∧
      LIST_REL
        (R (vars ∪ set (MAP FST ves))) (MAP SND ves) (MAP SND ves') ∧
      R (vars ∪ set (MAP FST ves)) e e'
      ⇒ R vars (Letrec ves e) (Letrec ves' e')
End

Theorem Com_defs =
  LIST_CONJ [Com1_def,Com2_def,Com3_def,Com4_def,Com5_def];

Definition Compatible_def:
  Compatible R ⇔ Com1 R ∧ Com2 R ∧ Com3 R ∧ Com4 R ∧ Com5 R
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
  \\ reverse (rw [bind_def])
  THEN1 fs [closed_def]
  \\ match_mp_tac IMP_closed_subst
  \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS]
QED

Theorem Ref_open_bisimilarity:
  Ref open_bisimilarity
Proof
  assume_tac Ref_open_similarity
  \\ fs [Ref_def,open_bisimilarity_eq]
QED

Theorem Sym_open_bisimilarity:
  Sym open_bisimilarity
Proof
  rw[Sym_def, open_bisimilarity_def]
  \\ assume_tac symmetric_app_bisimilarity
  \\ fs[symmetric_def]
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
  fs [Tra_def] \\ metis_tac [open_similarity_transitive,open_bisimilarity_eq]
QED


(* -- Howe's construction -- *)

Inductive Howe: (* TODO: add Cons clause *)
[Howe1:]
  (∀R vars x e2.
     R vars (Var x) e2 ⇒
     Howe R vars (Var x) e2)
  ∧
[Howe2:]
  (∀R x e1 e1' e2 vars.
     Howe R (x INSERT vars) e1 e1' ∧
     R vars (Lam x e1') e2 ⇒
     (* ~(x IN vars) ⇒ *)
     Howe R vars (Lam x e1) e2)
  ∧
[Howe3:]
  (∀R e1 e1' e3 vars.
     Howe R vars e1 e1' ∧
     Howe R vars e2 e2' ∧
     R vars (App e1' e2') e3 ⇒
     Howe R vars (App e1 e2) e3)
  ∧
[Howe4:]
  (∀R es es' e op vars.
    LIST_REL (Howe R vars) es es' ∧
    R vars (Prim op es') e ⇒
    Howe R vars (Prim op es) e)
  ∧
[Howe5:]
  (∀R ves ves' e e' e2.
    MAP FST ves = MAP FST ves' ∧
    (* DISJOINT vars (set (MAP FST ves)) ∧ *)
    Howe R (vars ∪ set (MAP FST ves)) e e' ∧
    LIST_REL (Howe R (vars ∪ set (MAP FST ves))) (MAP SND ves) (MAP SND ves') ∧
    R vars (Letrec ves' e') e2
  ⇒ Howe R vars (Letrec ves e) e2)
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
  >- (
    rw[Com4_def] >>
    irule Howe4 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[Exps_def] >>
    gvs[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rw[] >>
    first_x_assum irule >>
    goal_assum drule >> fs[]
    )
  >- (
    rw[Com5_def] >>
    irule Howe5 >>
    gvs[DISJOINT_SYM] >>
    rpt (goal_assum (drule_at Any)) >> fs[] >>
    first_x_assum irule >> fs[Exps_def] >>
    fs[LIST_TO_SET_FILTER, SUBSET_DEF] >> rw[]
    >- (last_x_assum drule >> fs[]) >>
    gvs[MEM_FLAT] >>
    qpat_x_assum `¬ MEM _ _` mp_tac >>
    simp[IMP_DISJ_THM, Once DISJ_SYM] >>
    first_x_assum irule >> gvs[MEM_MAP] >>
    PairCases_on `y` >> gvs[] >>
    rpt (goal_assum (drule_at Any)) >> fs[]
    )
QED

Definition term_rel_def:
  term_rel R ⇔
    ∀vars e1 e2. R vars e1 e2 ⇒ e1 ∈ Exps vars ∧ e2 ∈ Exps vars
End

Theorem term_rel_open_similarity:
  term_rel open_similarity
Proof
  fs [term_rel_def,open_similarity_def,Exps_def]
QED

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
  >- (
    fs[LIST_REL_EL_EQN] >>
    first_assum drule >> rw[Exps_def] >>
    gvs[SUBSET_DEF, MEM_FLAT, MEM_MAP] >> rw[] >>
    qpat_x_assum `MEM _ es` mp_tac >> simp[MEM_EL] >> strip_tac >> gvs[] >>
    last_x_assum drule >> strip_tac >> first_x_assum drule >>
    simp[Exps_def, SUBSET_DEF]
    )
  >- metis_tac[]
  >- (
    fs[LIST_REL_EL_EQN] >>
    first_assum drule >> rw[Exps_def] >>
    fs[LIST_TO_SET_FILTER, SUBSET_DEF] >> rw[]
    >- (
      last_x_assum drule >> fs[Exps_def, SUBSET_DEF] >> strip_tac >>
      first_x_assum drule >> fs[]
      ) >>
    gvs[] >>
    qpat_x_assum `MEM s _` mp_tac >> simp[MEM_MAP, MEM_EL] >>
    strip_tac >> gvs[] >>
    first_x_assum (qspec_then `n` mp_tac) >>
    disch_then drule >> strip_tac >>
    pop_assum drule >> simp[EL_MAP, Exps_def] >> strip_tac >>
    Cases_on `EL n ves` >> gvs[SUBSET_DEF] >>
    first_x_assum drule >> fs[]
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
    >- (imp_res_tac term_rel_def >> fs[Exps_def]) >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe4 >>
    rpt (goal_assum (drule_at Any)) >>
    first_x_assum irule >> fs[] >> rw[]
    >- (imp_res_tac term_rel_def >> fs[Exps_def]) >>
    qexists_tac `e2` >> fs[]
    )
  >- (
    irule Howe5 >> gvs[] >>
    rpt (goal_assum (drule_at Any)) >> gvs[] >>
    first_x_assum irule >> gvs[] >> rw[]
    >- (imp_res_tac term_rel_def >> fs[Exps_def]) >>
    qexists_tac `e2` >> fs[]
    )
QED

Theorem Howe_Ref_Tra: (* 5.5.1(iii) *)
  Ref R ∧ term_rel R ⇒
  ∀vars e1 e2. R vars e1 e2 ⇒ Howe R vars e1 e2
Proof
  strip_tac
  \\ imp_res_tac Howe_Ref
  \\ simp [Once SWAP_FORALL_THM]
  \\ ho_match_mp_tac freevars_ind \\ rw []
  THEN1 (simp [Once Howe_cases])
  THEN1
   (simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [term_rel_def] \\ last_x_assum drule
    \\ pop_assum kall_tac
    \\ strip_tac
    \\ ‘∀e. MEM e es ⇒ e IN Exps vars’ by
      (fs [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS]
       \\ rw [] \\ res_tac \\ fs [])
    \\ qpat_x_assum ‘∀e. _’ mp_tac
    \\ qpat_x_assum ‘∀e. _’ mp_tac
    \\ qid_spec_tac ‘es’ \\ Induct \\ fs [] \\ rw []
    \\ first_x_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs [])
  THEN1
   (simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [term_rel_def] \\ last_x_assum drule
    \\ strip_tac \\ fs [] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Exps_def,SUBSET_DEF])
  THEN1
   (simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [term_rel_def] \\ last_x_assum drule
    \\ strip_tac \\ fs [] \\ rw []
    \\ first_x_assum match_mp_tac
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Exps_def,SUBSET_DEF] \\ metis_tac [])
  \\ simp [Once Howe_cases]
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [term_rel_def] \\ last_x_assum drule
  \\ strip_tac \\ fs [] \\ rw []
  THEN1
   (first_x_assum match_mp_tac
    \\ fs [Ref_def] \\ first_assum (match_mp_tac o MP_CANON) \\ fs []
    \\ fs [Exps_def,SUBSET_DEF] \\ metis_tac [])
  \\ ‘∀fn e1. MEM (fn,e1) lcs ⇒ e1 IN Exps (vars UNION set (MAP FST lcs))’ by
   (fs [Exps_def,SUBSET_DEF,FORALL_PROD,EXISTS_PROD,MEM_MAP,PULL_EXISTS]
    \\ rw [] \\ Cases_on ‘∃p_2. MEM (x,p_2) lcs’
    THEN1 metis_tac [] \\ disj1_tac
    \\ last_x_assum match_mp_tac \\ fs [] \\ metis_tac [])
  \\ qmatch_goalsub_abbrev_tac ‘Howe _ (vars UNION v2)’
  \\ ‘set (MAP FST lcs) SUBSET v2’ by fs [SUBSET_DEF,EXTENSION]
  \\ pop_assum mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qpat_x_assum ‘∀x y. MEM _ _ ⇒ _’ mp_tac
  \\ qid_spec_tac ‘v2’
  \\ qid_spec_tac ‘lcs’
  \\ Induct \\ fs [FORALL_PROD] \\ rw []
  THEN1
   (fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD,AND_IMP_INTRO,PULL_FORALL]
    \\ first_x_assum match_mp_tac
    \\ qexists_tac ‘p_1’ \\ fs []
    \\ fs [Ref_def])
  \\ first_x_assum (match_mp_tac o MP_CANON) \\ fs []
  \\ fs [SUBSET_DEF,EXISTS_PROD,FORALL_PROD]
  \\ metis_tac []
QED

Definition Sub_def: (* Sub = substitutive *)
  Sub R ⇔
    ∀vars x e1 e1' e2 e2'.
      (* x ∉ vars ∧ *)
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ {e2; e2'} SUBSET Exps {} ⇒
      R (x INSERT vars) e1 e1' ∧ R vars e2 e2' ⇒
      R vars (subst x e2 e1) (subst x e2' e1')
  (* This definition has been tweaked to only insert closed expressions e2, e2' *)
End

Definition Cus_def: (* closed under value-substitution *)
  Cus R ⇔
    ∀vars x e1 e1' e2.
      (* x ∉ vars ∧ *)
      {e1; e1'} SUBSET Exps (x INSERT vars) ∧ e2 IN Exps {} ⇒
      R (x INSERT vars) e1 e1' ⇒
      R vars (subst x e2 e1) (subst x e2 e1')
  (* This definition has been tweaked to only insert closed expressions e2 *)
End

Theorem Sub_Ref_IMP_Cus:
  Sub R ∧ Ref R ⇒ Cus R
Proof
  rw[Sub_def, Ref_def, Cus_def]
  \\ fs [AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac \\ fs []
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def,closed_def]
QED

Theorem Cus_open_similarity:
  Cus open_similarity
Proof
  fs [Cus_def] \\ rw []
  \\ fs [open_similarity_def]
  \\ fs [SUBSET_DEF,freevars_subst]
  \\ conj_tac THEN1 (metis_tac [])
  \\ rw [bind_def]
  \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (x,e2)) ⇒ closed v)’ by fs [FRANGE_DEF]
  \\ drule subst_subst_FUNION \\ fs []
  \\ disch_then kall_tac
  \\ first_x_assum (qspec_then ‘FEMPTY |+ (x,e2) ⊌ f’ mp_tac)
  \\ impl_tac THEN1 (fs [FUNION_DEF] \\ metis_tac [])
  \\ simp [bind_def] \\ IF_CASES_TAC \\ fs []
  \\ gvs [FLOOKUP_DEF,FUNION_DEF] \\ metis_tac []
QED

Theorem Cus_open_bisimilarity:
  Cus open_bisimilarity
Proof
  assume_tac Cus_open_similarity
  \\ fs [Cus_def,open_bisimilarity_eq]
QED

Theorem IMP_Howe_Sub: (* 5.5.3 *)
  Ref R ∧ Tra R ∧ Cus R ⇒ Sub (Howe R)
Proof
  fs [Sub_def,PULL_FORALL]
  \\ qsuff_tac ‘
       ∀R x_vars e1 e1'.
         Howe R x_vars e1 e1' ⇒
         ∀vars x e2 e2'. x_vars = x INSERT vars ∧ Ref R ∧ Tra R ∧ Cus R ∧
            (e1 ∈ Exps (x INSERT vars) ∧ e1' ∈ Exps (x INSERT vars)) ∧
            closed e2 ∧ closed e2' ∧ Howe R vars e2 e2' ⇒
            Howe R vars (subst x e2 e1) (subst x e2' e1')’
  THEN1 fs [PULL_FORALL]
  \\ Induct_on ‘Howe’ \\ rw [] \\ fs []
  THEN1
   (match_mp_tac (Howe_Tra |> MP_CANON |> GEN_ALL)
    \\ qexists_tac ‘(subst x' e2' (Var x))’
    \\ rw [] THEN1 cheat THEN1 cheat THEN1 cheat THEN1 cheat
    THEN1 (fs [subst_single_def] \\ rw [] \\ cheat)
    \\ fs [Cus_def])
  (*
    fs [Cus_def,AND_IMP_INTRO]
    \\ first_assum (first_assum o mp_then (Pos last) mp_tac)
    \\ disch_then (qspec_then ‘e2'’ mp_tac)
    \\ impl_tac THEN1 cheat
    \\ simp [subst_single_def] \\ strip_tac
    \\ simp [Once Howe_cases]
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ rw [] THEN1 (fs [INSERT_INSERT])
    \\ first_x_assum match_mp_tac
  *)
  \\ cheat
QED

Theorem Ref_Howe:
  Ref R ⇒ Ref (Howe R)
Proof
  strip_tac
  \\ gvs[Ref_def,Exps_def,PULL_FORALL]
  \\ CONV_TAC SWAP_FORALL_CONV
  \\ ho_match_mp_tac freevars_ind \\ rw []
  THEN1 (rename [‘Var’] \\ rw[Once Howe_cases])
  THEN1 (rename [‘Prim’] \\ rw[Once Howe_cases]
         \\ qexists_tac ‘es’ \\ fs []
         \\ Induct_on ‘es’ \\ fs [])
  THEN1 (rename [‘App’] \\ rw[Once Howe_cases]
         \\ ‘freevars (App e e') SUBSET vars’ by (fs [SUBSET_DEF] \\ metis_tac [])
         \\ metis_tac [])
  THEN1 (rename [‘Lam’] \\ rw[Once Howe_cases]
         \\ ‘freevars (Lam n e) SUBSET vars’ by (fs [SUBSET_DEF] \\ metis_tac [])
         \\ qexists_tac ‘e’ \\ fs []
         \\ first_x_assum match_mp_tac \\ fs [SUBSET_DEF] \\ metis_tac [])
  \\ rename [‘Letrec’] \\ rw[Once Howe_cases]
  \\ qexists_tac ‘lcs’
  \\ qexists_tac ‘e’ \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  THEN1 (first_x_assum match_mp_tac \\ fs [SUBSET_DEF] \\ metis_tac [])
  \\ qmatch_goalsub_abbrev_tac ‘Howe _ (vars UNION v2)’
  \\ ‘set (MAP FST lcs) SUBSET v2’ by fs [SUBSET_DEF,EXTENSION]
  \\ pop_assum mp_tac
  \\ qpat_x_assum ‘∀x y. _’ mp_tac
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘v2’
  \\ qid_spec_tac ‘lcs’
  \\ Induct \\ fs [FORALL_PROD] \\ rw []
  THEN1
   (fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
    \\ first_x_assum match_mp_tac
    \\ qexists_tac ‘p_1’ \\ fs [] \\ metis_tac [])
  \\ first_x_assum (match_mp_tac o MP_CANON) \\ fs []
  \\ fs [SUBSET_DEF,EXISTS_PROD,FORALL_PROD]
  \\ metis_tac []
QED

Theorem Sub_Howe_open_similarity:
  Sub (Howe open_similarity)
Proof
  metis_tac [Ref_Howe,Ref_open_similarity,IMP_Howe_Sub,
       Cus_open_similarity,Tra_open_similarity,Ref_open_similarity]
QED

Theorem Cus_Howe_open_similarity:
  Cus (Howe open_similarity)
Proof
  match_mp_tac Sub_Ref_IMP_Cus \\ rw []
  \\ metis_tac [Ref_Howe,Ref_open_similarity,IMP_Howe_Sub,
       Cus_open_similarity,Tra_open_similarity,Ref_open_similarity]
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
  \\ fs [SUBSET_DEF,MEM_FILTER,MEM_FLAT,MEM_MAP,PULL_EXISTS]
  THEN1 metis_tac []
  THEN1 (rw [] \\ drule_all listTheory.LIST_REL_MEM_IMP \\ fs []
         \\ metis_tac [])
  \\ rw [] \\ fs [GSYM IMP_DISJ_THM]
  \\ fs [FORALL_PROD,EXISTS_PROD]
  \\ imp_res_tac (METIS_PROVE []
                  “MAP f xs = MAP f xs' ⇒ ∀y. MEM y (MAP f xs) = MEM y (MAP f xs')”)
  \\ fs [MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]
  THEN1 metis_tac []
  \\ Cases_on ‘y’ \\ fs [IN_DISJOINT]
  \\ fs [MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]
  \\ ‘MEM r (MAP SND ves)’ by (fs [MEM_MAP,EXISTS_PROD] \\ metis_tac [])
  \\ drule_all listTheory.LIST_REL_MEM_IMP \\ fs []
  \\ metis_tac []
QED

Theorem Howe_open_similarity_IMP_freevars:
  Howe open_similarity s x y ⇒ freevars x ⊆ s ∧ freevars y ⊆ s
Proof
  rw [] \\ assume_tac term_rel_open_similarity
  \\ imp_res_tac term_rel_Howe
  \\ fs [term_rel_def]
  \\ res_tac \\ fs [] \\ rw []
  \\ fs [Exps_def]
QED

Theorem Howe_open_similarity_IMP_closed:
  Howe open_similarity ∅ x y ⇒ closed x ∧ closed y
Proof
  rw [] \\ imp_res_tac Howe_open_similarity_IMP_freevars
  \\ fs [closed_def]
QED

Triviality perm_exp_IN_Exps:
  freevars ce2 ⊆ {y} ⇒ perm_exp x y ce2 ∈ Exps {x}
Proof
  fs [Exps_def]
  \\ rewrite_tac [GSYM perm_exp_eqvt]
  \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def,closed_def,
         FILTER_EQ_NIL,EVERY_MEM]
  \\ rw [] \\ res_tac \\ fs []
QED

Theorem exp_alpha_subst_lemma[local]:
  closed (Lam y e5) ∧ closed e4 ⇒
  exp_alpha (subst x e4 (perm_exp x y e5)) (subst y e4 e5)
Proof
  rw [] \\ match_mp_tac exp_alpha_Trans
  \\ qexists_tac ‘perm_exp x y (subst x e4 (perm_exp x y e5))’
  \\ rw [] THEN1
   (match_mp_tac exp_alpha_perm_irrel
    \\ fs [freevars_subst,GSYM perm_exp_eqvt,MEM_MAP,closed_def,FILTER_EQ_NIL,
           EVERY_MEM,perm1_def] \\ metis_tac [])
  \\ fs [subst_single_eqvt,perm1_def]
  \\ match_mp_tac exp_alpha_subst_closed_single'
  \\ fs [closed_perm]
  \\ match_mp_tac exp_alpha_sym
  \\ match_mp_tac exp_alpha_perm_irrel
  \\ fs [closed_def]
QED

Theorem Howe_open_similarity_IMP:
  Howe open_similarity ∅ e1 e2 ∧ closed e1 ∧ closed e2 ⇒
  (∀x ce1.
       eval e1 = Closure x ce1 ⇒
       ∃y ce2.
           eval e2 = Closure y ce2 ∧
           Howe open_similarity {x} ce1 (perm_exp x y ce2)) ∧
  (∀x v1s.
       eval e1 = Constructor x v1s ⇒
       ∃es1 es2.
           Constructor x v1s = eval (Cons x es1) ∧ EVERY closed es1 ∧
           eval e2 = eval (Cons x es2) ∧ EVERY closed es2 ∧
           LIST_REL (Howe open_similarity ∅) es1 es2) ∧
  (∀a. eval e1 = Atom a ⇒ eval e2 = Atom a) ∧
  (eval e1 = Error ⇒ eval e2 = Error)
Proof
  Cases_on ‘eval e1 = Diverge’ \\ fs []
  \\ fs [eval_eq_Diverge] \\ pop_assum mp_tac
  \\ qid_spec_tac ‘e2’
  \\ qid_spec_tac ‘e1’
  \\ qid_spec_tac ‘n’
  \\ ho_match_mp_tac eval_to_ind \\ rpt conj_tac
  THEN1 (fs [eval_Var,closed_def])
  THEN1
   (rename [‘Prim’] \\ cheat)
  THEN1
   (rename [‘Lam’]
    \\ simp [Once Howe_cases]
    \\ fs [eval_Lam]
    \\ rpt gen_tac \\ rpt (disch_then assume_tac) \\ gvs []
    \\ fs [open_similarity_EMPTY]
    \\ qpat_x_assum ‘_ ≲ _’ mp_tac
    \\ simp [Once app_similarity_iff]
    \\ fs [unfold_rel_def,eval_Lam]
    \\ strip_tac \\ fs []
    \\ match_mp_tac (MP_CANON Howe_Tra |> GEN_ALL)
    \\ fs [open_similarity_EMPTY]
    \\ fs [Tra_open_similarity,term_rel_open_similarity]
    \\ rename [‘Howe open_similarity {s} x t’]
    \\ qexists_tac ‘t’ \\ fs []
    \\ rewrite_tac [CONJ_ASSOC]
    \\ conj_tac THEN1
     (imp_res_tac Howe_open_similarity_IMP_closed
      \\ fs [Exps_def] \\ rewrite_tac [GSYM perm_exp_eqvt]
      \\ drule_all eval_Closure_closed \\ strip_tac
      \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def,closed_def,
             FILTER_EQ_NIL,EVERY_MEM]
      \\ rw [] \\ res_tac \\ fs [])
    \\ fs [open_similarity_def]
    \\ drule_all eval_Closure_closed \\ strip_tac
    \\ conj_asm1_tac THEN1
     (rewrite_tac [GSYM perm_exp_eqvt]
      \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def,closed_def,
             FILTER_EQ_NIL,EVERY_MEM])
    \\ rw [] \\ rw [bind_def]
    \\ reverse (Cases_on ‘s IN FDOM f’)
    THEN1
     (‘closed t’ by
        (fs [freevars_def,SUBSET_DEF,closed_def] \\ Cases_on ‘freevars t’ \\ fs [])
      \\ ‘closed ce2’ by
        (fs [freevars_def,SUBSET_DEF,closed_def,GSYM perm_exp_eqvt,MEM_MAP,PULL_EXISTS]
         \\ Cases_on ‘freevars ce2’ \\ fs [] \\ metis_tac [])
      \\ fs [closed_subst,closed_perm]
      \\ match_mp_tac (SIMP_RULE std_ss [transitive_def] transitive_app_similarity)
      \\ qexists_tac ‘ce2’ \\ fs []
      \\ conj_tac
      THEN1 (first_x_assum match_mp_tac \\ qexists_tac ‘Fail’ \\ fs [closed_def])
      \\ match_mp_tac exp_alpha_app_similarity \\ fs [closed_perm]
      \\ match_mp_tac exp_alpha_perm_irrel \\ fs [closed_def])
    \\ qabbrev_tac ‘vv = f ' s’
    \\ ‘closed vv’ by fs [FLOOKUP_DEF,Abbr‘vv’]
    \\ first_x_assum drule
    \\ ‘subst f t = subst s vv t’ by
       (once_rewrite_tac [subst_FDIFF] \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ fs [fmap_EXT,DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
        \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
    \\ strip_tac
    \\ match_mp_tac (SIMP_RULE std_ss [transitive_def] transitive_app_similarity)
    \\ fs []
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ ‘subst f (perm_exp s y ce2) = subst s vv (perm_exp s y ce2)’ by
       (once_rewrite_tac [subst_FDIFF] \\ AP_THM_TAC \\ AP_TERM_TAC
        \\ fs [fmap_EXT,DRESTRICT_DEF,FAPPLY_FUPDATE_THM]
        \\ fs [EXTENSION,SUBSET_DEF] \\ metis_tac [])
    \\ fs []
    \\ match_mp_tac exp_alpha_app_similarity
    \\ conj_tac THEN1
     (match_mp_tac exp_alpha_sym
      \\ match_mp_tac exp_alpha_subst_lemma
      \\ fs [closed_def,FILTER_EQ_NIL,EVERY_MEM,SUBSET_DEF])
    \\ rw [] \\ match_mp_tac IMP_closed_subst \\ fs [FRANGE_DEF])
  THEN1
   (rename [‘App’]
    \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
    \\ rename [‘Howe open_similarity ∅ (App e_1 e_1') e’]
    \\ simp_tac (srw_ss()) [Once Howe_cases,eval_to_def,LET_THM,AllCaseEqs()]
    \\ Cases_on ‘eval_to n e_1 ≠ Diverge’ \\ fs []
    \\ ‘∃v body. eval_to n e_1 = Closure v body ∧
                 eval e_1 = Closure v body’
           by cheat (* just to get to the interesting case *)
    \\ fs [] \\ Cases_on ‘n = 0’ \\ fs [] \\ ntac 2 strip_tac
    \\ qpat_x_assum ‘Howe open_similarity ∅ e_1' _’ mp_tac
    \\ qpat_x_assum ‘Howe open_similarity ∅ e_1 _’ mp_tac
    \\ rename [‘Howe open_similarity ∅ _ e_4 ⇒
                Howe open_similarity ∅ _ e_4' ⇒ _’]
    \\ rpt (disch_then strip_assume_tac)
    \\ rename [‘eval e_1 = Closure x e_2’]
    \\ first_x_assum drule
    \\ impl_tac THEN1 (imp_res_tac Howe_open_similarity_IMP_closed \\ fs [])
    \\ strip_tac
    \\ rename [‘eval _ = Closure y e_5’]
    \\ ‘Howe open_similarity {} (Lam x e_2) (Lam y e_5)’ by
      (simp [Once Howe_cases] \\ qexists_tac ‘perm_exp x y e_5’ \\ fs []
       \\ fs [open_similarity_EMPTY]
       \\ match_mp_tac app_similarity_Lam_Alpha_alt
       \\ imp_res_tac Howe_open_similarity_IMP_closed
       \\ drule_all eval_Closure_closed
       \\ gvs [SUBSET_DEF,closed_def,FILTER_EQ_NIL,EVERY_MEM])
    \\ assume_tac Sub_Howe_open_similarity
    \\ fs [Sub_def,AND_IMP_INTRO]
    \\ pop_assum (qspecl_then [‘{}’,‘x’,‘e_2’,‘perm_exp x y e_5’,‘e_1'’,‘e_4'’] mp_tac)
    \\ impl_keep_tac
    THEN1 (imp_res_tac Howe_open_similarity_IMP_freevars
           \\ fs [Exps_def] \\ fs [closed_def])
    \\ strip_tac
    \\ simp [eval_App]
    \\ first_x_assum match_mp_tac
    \\ ‘closed e_1'’ by fs [closed_def]
    \\ fs [bind_single_def]
    \\ reverse conj_tac
    THEN1 (imp_res_tac Howe_open_similarity_IMP_closed \\ fs [])
    \\ match_mp_tac (MP_CANON Howe_Tra |> GEN_ALL)
    \\ fs [open_similarity_EMPTY]
    \\ fs [Tra_open_similarity,term_rel_open_similarity]
    \\ qexists_tac ‘subst x e_4' (perm_exp x y e_5)’ \\ fs []
    \\ rewrite_tac [CONJ_ASSOC]
    \\ conj_asm1_tac
    THEN1 (imp_res_tac Howe_open_similarity_IMP_closed \\ fs [])
    \\ match_mp_tac (SIMP_RULE std_ss [transitive_def] transitive_app_similarity)
    \\ qexists_tac ‘subst y e_4' e_5’
    \\ imp_res_tac Howe_open_similarity_IMP_closed
    \\ conj_tac
    THEN1
     (match_mp_tac exp_alpha_app_similarity
      \\ fs [exp_alpha_subst_lemma]
      \\ match_mp_tac IMP_closed_subst
      \\ fs [closed_def,SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM])
    \\ qpat_x_assum ‘_ ≲ _’ mp_tac
    \\ rewrite_tac [app_similarity_iff]
    \\ once_rewrite_tac [unfold_rel_def]
    \\ fs [eval_App,eval_Cons]
    \\ fs [bind_single_def]
    \\ rw [] \\ match_mp_tac IMP_closed_subst
    \\ fs [FRANGE_DEF,closed_def,FILTER_EQ_NIL,EVERY_MEM,SUBSET_DEF])
  \\ rename [‘Letrec’]
  \\ rpt gen_tac \\ strip_tac \\ rpt gen_tac
  \\ fs [eval_to_def,AllCaseEqs()]
  \\ Cases_on ‘n=0’ \\ fs []
  \\ rpt (disch_then strip_assume_tac) \\ fs []
  \\ cheat
QED

Theorem app_simulation_Howe_open_similarity:
  app_simulation (UNCURRY (Howe open_similarity {}))
Proof
  fs [app_simulation_def,unfold_rel_def] \\ rpt gen_tac \\ strip_tac
  \\ drule Howe_open_similarity_IMP_closed \\ strip_tac \\ fs []
  \\ drule Howe_open_similarity_IMP \\ fs [] \\ rw [] \\ fs []
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def,AND_IMP_INTRO]
  \\ pop_assum (first_x_assum o mp_then (Pos last) mp_tac) \\ rw []
  \\ first_x_assum (first_assum o mp_then (Pos last) mp_tac)
  \\ impl_keep_tac
  THEN1 (imp_res_tac eval_Closure_closed
         \\ imp_res_tac perm_exp_IN_Exps \\ fs [Exps_def])
  \\ rw [] \\ match_mp_tac (MP_CANON Howe_Tra |> GEN_ALL)
  \\ fs [open_similarity_EMPTY]
  \\ fs [Tra_open_similarity,term_rel_open_similarity]
  \\ fs [AC CONJ_ASSOC CONJ_SYM]
  \\ goal_assum (first_assum o mp_then (Pos last) mp_tac)
  \\ rewrite_tac [CONJ_ASSOC]
  \\ reverse conj_asm1_tac
  THEN1 (match_mp_tac exp_alpha_app_similarity \\ rw []
         \\ match_mp_tac exp_alpha_subst_lemma \\ fs []
         \\ imp_res_tac eval_Closure_closed \\ simp [closed_def]
         \\ fs [closed_def,SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM])
  \\ rw [] \\ match_mp_tac IMP_closed_subst
  \\ fs [FRANGE_DEF]
  \\ imp_res_tac eval_Closure_closed
  \\ fs [closed_def,SUBSET_DEF,FILTER_EQ_NIL,EVERY_MEM]
  \\ rewrite_tac [GSYM perm_exp_eqvt]
  \\ fs [SUBSET_DEF,MEM_MAP,PULL_EXISTS,perm1_def,closed_def,
           FILTER_EQ_NIL,EVERY_MEM]
QED

Theorem IMP_open_similarity_INSERT:
  (* This has been modified to only subst in closed expressions *)
  (∀e. closed e ⇒ open_similarity vars (subst h e e1) (subst h e e2)) ∧
  h ∉ vars ∧ e1 IN Exps (h INSERT vars) ∧ e2 IN Exps (h INSERT vars) ⇒
  open_similarity (h INSERT vars) e1 e2
Proof
  fs [open_similarity_def] \\ rw [] \\ fs [Exps_def]
  \\ rw [bind_def]
  \\ reverse (Cases_on ‘h IN FDOM f’)
  THEN1
   (‘~(h IN freevars e1) ∧ ~(h IN freevars e2)’ by (fs [SUBSET_DEF] \\ metis_tac [])
    \\ fs [subst_ignore_single]
    \\ ‘closed Fail’ by fs[closed_def]
    \\ first_x_assum drule
    \\ disch_then drule_all
    \\ fs [] \\ fs [bind_def]
    \\ metis_tac [])
  \\ ‘∃e. FLOOKUP f h = SOME e ∧ closed e’ by
        (fs [FLOOKUP_DEF,EXTENSION] \\ metis_tac [])
  \\ last_x_assum drule \\ rw []
  \\ first_x_assum (qspec_then ‘f’ mp_tac)
  \\ impl_tac THEN1 (fs [SUBSET_DEF,freevars_subst])
  \\ fs [bind_def,FLOOKUP_DRESTRICT]
  \\ reverse IF_CASES_TAC THEN1 metis_tac [] \\ fs []
  \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (h,e)) ⇒ closed v)’ by fs [FRANGE_DEF,FLOOKUP_DEF]
  \\ drule subst_subst_FUNION \\ fs []
  \\ qsuff_tac ‘FEMPTY |+ (h,e) ⊌ f = f’ THEN1 fs []
  \\ fs [fmap_EXT,FUNION_DEF,EXTENSION,DRESTRICT_DEF,FLOOKUP_DEF]
  \\ metis_tac []
QED

Theorem open_similarity_larger:
  ∀vars e1 e2 vars1.
    open_similarity vars e1 e2 ∧ vars SUBSET vars1 ⇒ open_similarity vars1 e1 e2
Proof
  fs [open_similarity_def]
  \\ rw [] \\ imp_res_tac SUBSET_TRANS \\ fs []
QED

Theorem Howe_larger:
  Howe R vars e1 e2 ⇒ R = open_similarity ⇒
  ∀vars1. vars SUBSET vars1 ⇒ Howe R vars1 e1 e2
Proof
  Induct_on ‘Howe’ \\ rw []
  THEN1
   (simp [Once Howe_cases] \\ imp_res_tac open_similarity_larger)
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ qexists_tac ‘e2’ \\ fs [] \\ rw []
    THEN1 (pop_assum match_mp_tac \\ fs [SUBSET_DEF])
    \\ imp_res_tac open_similarity_larger)
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS] \\ res_tac
    \\ rpt (goal_assum (first_assum o mp_then Any mp_tac))
    \\ imp_res_tac open_similarity_larger)
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ qexists_tac ‘es'’ \\ fs [] \\ rw []
    THEN1
     (last_x_assum kall_tac \\ pop_assum mp_tac
      \\ qid_spec_tac ‘es'’ \\ qid_spec_tac ‘es’
      \\ Induct \\ Cases_on ‘es'’ \\ fs [])
    \\ imp_res_tac open_similarity_larger)
  \\ simp [Once Howe_cases,PULL_EXISTS]
  \\ qexists_tac ‘ves'’ \\ fs [] \\ rw []
  \\ qexists_tac ‘e2’ \\ fs []
  \\ imp_res_tac open_similarity_larger \\ fs [] \\ rw []
  THEN1 (first_x_assum match_mp_tac \\ fs [SUBSET_DEF])
  \\ pop_assum kall_tac
  \\ pop_assum mp_tac
  \\ last_x_assum mp_tac
  \\ pop_assum kall_tac
  \\ qid_spec_tac ‘ves’ \\ qid_spec_tac ‘ves'’
  \\ Induct \\ Cases_on ‘ves’ \\ fs [FORALL_PROD] \\ rw []
  THEN1 (first_x_assum match_mp_tac \\ fs [SUBSET_DEF])
  \\ pop_assum mp_tac
  \\ rename [‘_ (MAP SND xs) (MAP SND ys)’]
  \\ match_mp_tac LIST_REL_mono
  \\ fs [FORALL_PROD] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs [SUBSET_DEF]
QED

Theorem Howe_larger = GEN_ALL Howe_larger |> SIMP_RULE std_ss [] |> MP_CANON;

Theorem LIST_REL_Howe_larger:
  ∀vs ws es ys.
    LIST_REL (Howe open_similarity vs) es ys ∧ vs SUBSET ws ⇒
    LIST_REL (Howe open_similarity ws) es ys
Proof
  rw [] \\ last_x_assum mp_tac
  \\ match_mp_tac LIST_REL_mono \\ rw []
  \\ match_mp_tac Howe_larger
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ fs [SUBSET_DEF]
QED

Theorem open_similarity_finite:
  ∀vars e1 e2.
    open_similarity vars e1 e2 ⇒ ∃vs. open_similarity vs e1 e2 ∧ FINITE vs
Proof
  fs [open_similarity_def] \\ rw []
  \\ qexists_tac ‘freevars e1 UNION freevars e2’ \\ fs []
QED

Theorem Howe_finite:
  Howe R vars e1 e2 ⇒ R = open_similarity ⇒
  ∃ws. Howe R ws e1 e2 ∧ FINITE ws
Proof
  Induct_on ‘Howe’ \\ rw []
  THEN1
   (simp [Once Howe_cases]
    \\ imp_res_tac open_similarity_finite
    \\ qexists_tac ‘vs’ \\ fs [])
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ imp_res_tac open_similarity_finite
    \\ qexists_tac ‘x INSERT (ws UNION vs)’ \\ fs []
    \\ qexists_tac ‘e2’ \\ fs [] \\ rw []
    THEN1
     (match_mp_tac Howe_larger
      \\ goal_assum (first_assum o mp_then Any mp_tac)
      \\ fs [SUBSET_DEF])
    \\ match_mp_tac open_similarity_larger
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ imp_res_tac open_similarity_finite
    \\ qexists_tac ‘vs UNION ws UNION ws'’ \\ fs []
    \\ qexists_tac ‘e2’ \\ fs [] \\ rw []
    \\ qexists_tac ‘e2'’ \\ fs [] \\ rw []
    \\ TRY (match_mp_tac Howe_larger)
    \\ TRY (match_mp_tac open_similarity_larger)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (simp [Once Howe_cases,PULL_EXISTS]
    \\ imp_res_tac open_similarity_finite
    \\ ‘∃ws1. LIST_REL (Howe open_similarity ws1) es es' ∧ FINITE ws1 ∧ vs SUBSET ws1’ by
     (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
      \\ qid_spec_tac ‘es'’ \\ qid_spec_tac ‘es’
      \\ Induct \\ fs []
      THEN1 (goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs [])
      \\ fs [PULL_EXISTS] \\ rw []
      \\ first_x_assum drule \\ rw []
      \\ qexists_tac ‘ws UNION ws1’ \\ fs [] \\ rw []
      \\ TRY (match_mp_tac Howe_larger)
      \\ TRY (match_mp_tac LIST_REL_Howe_larger)
      \\ TRY (goal_assum (first_assum o mp_then Any mp_tac))
      \\ fs [SUBSET_DEF])
    \\ goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs []
    \\ TRY (match_mp_tac open_similarity_larger)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  \\ simp [Once Howe_cases,PULL_EXISTS]
  \\ imp_res_tac open_similarity_finite
  \\ ‘∃ws1. LIST_REL (Howe open_similarity ws1) (MAP SND ves) (MAP SND ves') ∧
            FINITE ws1 ∧ vs SUBSET ws1’ by
    (‘LIST_REL (λe1 e2. ∃ws. Howe open_similarity ws e1 e2 ∧ FINITE ws) (MAP SND ves)
        (MAP SND ves')’ by
      (qpat_x_assum ‘LIST_REL _ _ _’ mp_tac
       \\ match_mp_tac LIST_REL_mono \\ rw []
       \\ match_mp_tac Howe_larger)
     \\ pop_assum mp_tac
     \\ qid_spec_tac ‘ves'’ \\ qid_spec_tac ‘ves’
     \\ Induct \\ fs []
     THEN1 (goal_assum (first_assum o mp_then (Pos hd) mp_tac) \\ fs [])
     \\ Cases \\ fs [] \\ Cases \\ fs [] \\ PairCases_on ‘h’ \\ fs []
     \\ fs [PULL_EXISTS] \\ rw []
     \\ first_x_assum drule \\ rw []
     \\ qexists_tac ‘ws' UNION ws1’ \\ fs [] \\ rw []
     \\ TRY (match_mp_tac Howe_larger)
     \\ TRY (match_mp_tac LIST_REL_Howe_larger)
     \\ TRY (goal_assum (first_assum o mp_then Any mp_tac))
     \\ fs [SUBSET_DEF])
  \\ qexists_tac ‘ws1 UNION ws’ \\ fs []
  \\ qexists_tac ‘ves'’ \\ fs []
  \\ qexists_tac ‘e2’ \\ fs [] \\ rw []
  \\ TRY (match_mp_tac open_similarity_larger)
  \\ TRY (match_mp_tac Howe_larger)
  \\ TRY (match_mp_tac LIST_REL_Howe_larger)
  \\ TRY (goal_assum (first_assum o mp_then Any mp_tac))
  \\ fs [SUBSET_DEF]
QED

Theorem Howe_finite = GEN_ALL Howe_finite |> SIMP_RULE std_ss [] |> MP_CANON;

Theorem Howe_open_similarity: (* key property *)
  Howe open_similarity = open_similarity
Proof
  simp [FUN_EQ_THM] \\ rw []
  \\ rename [‘Howe open_similarity vars e1 e2’]
  \\ reverse eq_tac \\ rw []
  THEN1 (metis_tac [Howe_Ref_Tra,Ref_open_similarity,Tra_open_similarity,
                    term_rel_open_similarity])
  \\ assume_tac Cus_Howe_open_similarity \\ fs [Cus_def]
  \\ first_x_assum (qspec_then ‘{}’ mp_tac) \\ fs [] \\ rw []
  \\ assume_tac app_simulation_Howe_open_similarity
  \\ drule app_simulation_SUBSET_app_similarity
  \\ pop_assum kall_tac \\ pop_assum kall_tac
  \\ rw [SUBSET_DEF,IN_DEF,FORALL_PROD]
  \\ imp_res_tac Howe_finite
  \\ qsuff_tac ‘open_similarity ws e1 e2’
  THEN1
   (rw [] \\ assume_tac term_rel_open_similarity
    \\ imp_res_tac term_rel_Howe
    \\ fs [term_rel_def] \\ res_tac \\ fs [Exps_def]
    \\ fs [open_similarity_def])
  \\ last_x_assum kall_tac
  \\ qpat_x_assum ‘Howe open_similarity ws e1 e2’ mp_tac
  \\ qid_spec_tac ‘e2’
  \\ qid_spec_tac ‘e1’
  \\ pop_assum mp_tac
  \\ qid_spec_tac ‘ws’
  \\ Induct_on ‘FINITE’ \\ rw []
  THEN1
   (fs [open_similarity_def,FDOM_EQ_EMPTY] \\ res_tac
    \\ imp_res_tac Howe_vars \\ fs []
    \\ rw [bind_def]
    \\ ‘∀m. DISJOINT (freevars e2) (FDOM m) ∧
            DISJOINT (freevars e1) (FDOM m)’ by fs []
    \\ fs [subst_ignore])
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

Theorem LIST_REL_open_bisimilarity:
  ∀es es'.
    LIST_REL (open_bisimilarity vars) es es' ⇔
    LIST_REL (open_similarity vars) es es' ∧
    LIST_REL (open_similarity vars) es' es
Proof
  Induct \\ Cases_on ‘es'’ \\ fs [PULL_EXISTS]
  \\ fs [open_bisimilarity_eq] \\ metis_tac []
QED

Theorem Congruence_open_bisimilarity: (* part 2 of 5.5.5 *)
  Congruence open_bisimilarity
Proof
  fs [Congruence_def,Sym_open_bisimilarity]
  \\ assume_tac Precongruence_open_similarity
  \\ fs [Precongruence_def,Tra_open_bisimilarity]
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com_defs,open_bisimilarity_def,open_similarity_def]
  \\ fs [app_bisimilarity_similarity]
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1 metis_tac []
  THEN1
   (fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
    \\ qpat_x_assum ‘∀x. _’ kall_tac
    \\ qpat_x_assum ‘∀x. _’ mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ fs [LIST_REL_open_bisimilarity]
    \\ metis_tac [])
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ fs [LIST_REL_open_bisimilarity]
  \\ fs [GSYM PULL_FORALL]
  THEN1 (metis_tac [])
  THEN1 (metis_tac [])
  \\ fs [GSYM CONJ_ASSOC]
  THEN1
   (first_x_assum (qspecl_then [‘vars’,‘ves’,‘ves'’,‘e’,‘e'’] mp_tac)
    \\ impl_tac THEN1 gvs [] \\ rw [])
  THEN1
   (first_x_assum (qspecl_then [‘vars’,‘ves'’,‘ves’,‘e'’,‘e’] mp_tac)
    \\ impl_tac THEN1 gvs [] \\ rw [])
QED

(* -- contextual equivalence -- *)

Theorem exp_eq_refl:
  ∀x. x ≅ x
Proof
  fs [exp_eq_open_bisimilarity] \\ rw []
  \\ qexists_tac ‘freevars x’ \\ fs []
  \\ assume_tac Ref_open_bisimilarity
  \\ fs [Ref_def]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem exp_eq_sym:
  ∀x y. x ≅ y ⇔ y ≅ x
Proof
  qsuff_tac ‘∀x y. x ≅ y ⇒ y ≅ x’ THEN1 metis_tac []
  \\ fs [exp_eq_open_bisimilarity] \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac) \\ fs []
  \\ assume_tac Sym_open_bisimilarity
  \\ fs [Sym_def,PULL_FORALL,AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def]
QED

Theorem exp_eq_trans:
  ∀x y z. x ≅ y ∧ y ≅ z ⇒ x ≅ z
Proof
  fs [exp_eq_open_bisimilarity] \\ rw []
  \\ qexists_tac ‘vars UNION vars'’ \\ fs [SUBSET_DEF]
  \\ assume_tac Tra_open_bisimilarity
  \\ fs [Tra_def,PULL_FORALL,AND_IMP_INTRO]
  \\ first_x_assum match_mp_tac
  \\ fs [Exps_def,SUBSET_DEF]
  \\ qexists_tac ‘y’ \\ fs [] \\ rw []
  \\ match_mp_tac open_bisimilarity_SUBSET
  \\ goal_assum (first_x_assum o mp_then Any mp_tac) \\ fs [SUBSET_DEF]
QED

Theorem Congruence_exp_eq:
  Congruence (K $≅)
Proof
  mp_tac Congruence_open_bisimilarity
  \\ rw [Congruence_def,Precongruence_def]
  \\ fs [Sym_def,Tra_def]
  THEN1 metis_tac [exp_eq_sym]
  THEN1 metis_tac [exp_eq_trans]
  \\ fs [exp_eq_def]
  \\ fs [Compatible_def] \\ rw []
  \\ fs [Com1_def,Com2_def,Com3_def,Com4_def,Com5_def] \\ rw []
  THEN1 (fs [exp_eq_open_bisimilarity] \\ qexists_tac ‘{x}’ \\ fs [])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ simp [Exps_def,SUBSET_DEF]
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ simp [Exps_def,SUBSET_DEF] \\ rw []
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then Any mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ simp [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS] \\ rw []
    THEN1 metis_tac []
    THEN1 metis_tac []
    \\ qmatch_goalsub_abbrev_tac ‘open_bisimilarity vars1’
    \\ ‘BIGUNION (set (MAP (λe. freevars e) es)) SUBSET vars1 ∧
        BIGUNION (set (MAP (λe. freevars e) es')) SUBSET vars1’ by
           fs [Abbr‘vars1’]
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘es'’
    \\ qid_spec_tac ‘es’
    \\ Induct \\ fs [PULL_EXISTS] \\ rw []
    \\ fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
    \\ fs [SUBSET_DEF])
  THEN1
   (fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ first_x_assum match_mp_tac
    \\ rpt (qpat_x_assum ‘∀x. _’ kall_tac)
    \\ conj_tac
    THEN1
     (fs [Exps_def,SUBSET_DEF,MEM_MAP,PULL_EXISTS,FORALL_PROD,EXISTS_PROD]
      \\ rw [] \\ fs [IN_DISJOINT,MEM_MAP,FORALL_PROD,EXISTS_PROD]
      \\ imp_res_tac (METIS_PROVE []
            “MAP f xs = MAP f xs' ⇒ ∀y. MEM y (MAP f xs) = MEM y (MAP f xs')”)
      \\ fs [MEM_MAP,FORALL_PROD,EXISTS_PROD,PULL_EXISTS]
      \\ metis_tac [])
    \\ fs [] \\ reverse conj_tac
    THEN1
     (match_mp_tac open_bisimilarity_SUBSET
      \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
      \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ qmatch_goalsub_abbrev_tac ‘open_bisimilarity vars1’
    \\ ‘BIGUNION (set (MAP (λ(_,e). freevars e) ves)) SUBSET vars1 ∧
        BIGUNION (set (MAP (λ(_,e). freevars e) ves')) SUBSET vars1’ by
           (fs [Abbr‘vars1’] \\ fs [SUBSET_DEF] \\ metis_tac [])
    \\ pop_assum mp_tac
    \\ pop_assum mp_tac
    \\ pop_assum kall_tac
    \\ pop_assum kall_tac
    \\ pop_assum mp_tac
    \\ qid_spec_tac ‘ves'’
    \\ qid_spec_tac ‘ves’
    \\ Induct \\ fs [PULL_EXISTS,MAP_EQ_CONS,FORALL_PROD]
    \\ rw []
    \\ fs [exp_eq_open_bisimilarity_freevars,AND_IMP_INTRO]
    \\ match_mp_tac open_bisimilarity_SUBSET
    \\ goal_assum (first_x_assum o mp_then (Pos hd) mp_tac)
    \\ fs [SUBSET_DEF])
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

Theorem exp_eq_Prim_cong:
  LIST_REL $≅ xs xs' ⇒
  Prim p xs ≅ Prim p xs'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com4_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Prim p xs) (Prim p xs'))’
  \\ fs [Exps_def,SUBSET_DEF]
  \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem exp_eq_Letrec_cong:
  LIST_REL $≅ (MAP SND xs) (MAP SND xs') ∧ e ≅ e' ∧ MAP FST xs = MAP FST xs' ⇒
  Letrec xs e ≅ Letrec xs' e'
Proof
  assume_tac Congruence_exp_eq
  \\ fs [Congruence_def,Precongruence_def,Compatible_def,Com5_def]
  \\ fs [PULL_FORALL,AND_IMP_INTRO] \\ rw []
  \\ first_x_assum match_mp_tac \\ fs []
  \\ qexists_tac ‘freevars (App (Letrec xs e) (Letrec xs' e'))’
  \\ fs [Exps_def,SUBSET_DEF]
  \\ rw [] \\ fs [MEM_MAP,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac []
QED

Theorem exp_eq_subst:
  y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
  subst x y1 e1 ≅ subst x y2 e1
Proof
  rw [] \\ qid_spec_tac ‘e1’
  \\ ho_match_mp_tac freevars_ind \\ rw []
  THEN1 (fs [subst_def,FLOOKUP_UPDATE] \\ rw [exp_eq_refl])
  THEN1 (fs [subst_def] \\ match_mp_tac exp_eq_Prim_cong \\ fs []
         \\ Induct_on ‘es’ \\ fs [])
  THEN1 (fs [subst_def] \\ match_mp_tac exp_eq_App_cong \\ fs [])
  THEN1 (fs [subst_def,DOMSUB_FUPDATE_THM] \\ rw [exp_eq_refl]
         \\ match_mp_tac exp_eq_Lam_cong \\ fs [])
  \\ fs [subst_def]
  \\ match_mp_tac exp_eq_Letrec_cong
  \\ fs [MAP_MAP_o,combinTheory.o_DEF,UNCURRY]
  \\ ‘∀y s. FDIFF (FEMPTY |+ (x,y:exp)) s =
            if x IN s then FEMPTY else FEMPTY |+ (x,y)’ by
   (fs [fmap_EXT] \\ rw [FDOM_FDIFF,EXTENSION]
    THEN1 (rw [] \\ eq_tac \\ rw [])
    \\ fs [FDIFF_def])
  \\ fs [] \\ IF_CASES_TAC \\ fs [exp_eq_refl]
  THEN1 (qid_spec_tac ‘lcs’ \\ Induct \\ fs [exp_eq_refl,FORALL_PROD])
  \\ Induct_on ‘lcs’ \\ fs [FORALL_PROD] \\ rw []
  \\ fs [PULL_FORALL]
  \\ first_x_assum match_mp_tac
  \\ metis_tac []
QED

Theorem exp_eq_Lam_basic_lemma[local]:
  Lam x e1 ≅ Lam x e2 ⇔
  ∀y. closed y ⇒ subst x y e1 ≅ subst x y e2
Proof
  fs [exp_eq_def] \\ eq_tac \\ rw []
  THEN1
   (rw [bind_def]
    \\ first_x_assum (qspec_then ‘f’ mp_tac)
    \\ fs [bind_def]
    \\ reverse IF_CASES_TAC THEN1 (rfs [] \\ res_tac \\ fs [])
    \\ fs [] \\ impl_tac THEN1 (gvs [freevars_subst,SUBSET_DEF])
    \\ fs [subst_def]
    \\ simp [Once app_bisimilarity_iff] \\ fs [eval_thm]
    \\ rw []
    \\ last_x_assum assume_tac \\ first_x_assum drule
    \\ ‘(∀v. v ∈ FRANGE (f \\ x) ⇒ closed v)’ by
         fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
    \\ drule subst_subst_FUNION
    \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (x,y)) ⇒ closed v)’ by
         fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
    \\ drule subst_subst_FUNION \\ fs []
    \\ ntac 2 strip_tac
    \\ qmatch_goalsub_abbrev_tac ‘subst m1’ \\ strip_tac
    \\ qmatch_goalsub_abbrev_tac ‘subst m2’
    \\ qsuff_tac ‘m1 = m2’ \\ rw [] \\ fs []
    \\ unabbrev_all_tac
    \\ fs [fmap_EXT,FUNION_DEF,FAPPLY_FUPDATE_THM,EXTENSION,DOMSUB_FAPPLY_THM]
    \\ metis_tac [])
  \\ rw [bind_def]
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ simp [Once app_bisimilarity_iff] \\ fs [eval_thm]
  \\ fs [GSYM subst_def,CONJ_ASSOC]
  \\ conj_tac
  THEN1
   (rw [] \\ match_mp_tac IMP_closed_subst
    \\ fs [FLOOKUP_DEF,FRANGE_DEF,PULL_EXISTS])
  \\ rw []
  \\ first_x_assum (qspecl_then [‘e’,‘f \\ x’] mp_tac)
  \\ impl_tac THEN1
   (res_tac \\ fs [] \\ fs [SUBSET_DEF]
    \\ simp [freevars_subst,SUBSET_DEF])
  \\ fs [bind_def]
  \\ reverse IF_CASES_TAC \\ fs []
  THEN1 (fs [DOMSUB_FAPPLY_THM,FLOOKUP_DEF] \\ res_tac \\ gvs [])
  \\ ‘(∀v. v ∈ FRANGE (f \\ x) ⇒ closed v)’ by
    fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
  \\ drule subst_subst_FUNION
  \\ ‘(∀v. v ∈ FRANGE (FEMPTY |+ (x,e)) ⇒ closed v)’ by
    fs [FRANGE_DEF,FLOOKUP_DEF,PULL_EXISTS,DOMSUB_FAPPLY_THM]
  \\ drule subst_subst_FUNION \\ fs []
  \\ ntac 2 strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘subst m1’ \\ strip_tac
  \\ qmatch_goalsub_abbrev_tac ‘subst m2’
  \\ qsuff_tac ‘m1 = m2’ \\ rw [] \\ fs []
  \\ unabbrev_all_tac
  \\ fs [fmap_EXT,FUNION_DEF,FAPPLY_FUPDATE_THM,EXTENSION,DOMSUB_FAPPLY_THM]
  \\ metis_tac []
QED

Theorem exp_eq_Lam_lemma[local]:
  Lam x e1 ≅ Lam x e2 ⇔
  ∀y1 y2.
    y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
    subst x y1 e1 ≅ subst x y2 e2
Proof
  fs [exp_eq_Lam_basic_lemma] \\ reverse eq_tac \\ rw []
  THEN1 (first_x_assum match_mp_tac \\ fs [exp_eq_refl])
  \\ match_mp_tac exp_eq_trans
  \\ first_x_assum drule \\ rw []
  \\ goal_assum (first_assum o mp_then Any mp_tac)
  \\ match_mp_tac exp_eq_subst \\ fs []
QED

Theorem exp_eq_forall_subst:
  ∀v. x ≅ y ⇔ ∀z. closed z ⇒ subst v z x ≅ subst v z y
Proof
  fs [exp_eq_def] \\ rw [] \\ eq_tac \\ rw []
  THEN1
   (rw [bind_def] \\ fs []
    \\ ‘(∀x. x ∈ FRANGE (FEMPTY |+ (v,z)) ⇒ closed x)’ by fs [FRANGE_DEF]
    \\ drule subst_subst_FUNION \\ fs [] \\ rw []
    \\ last_x_assum (qspec_then ‘FEMPTY |+ (v,z) ⊌ f’ mp_tac)
    \\ impl_tac THEN1 (fs [SUBSET_DEF,freevars_subst] \\ metis_tac [])
    \\ rw [bind_def]
    \\ gvs [FLOOKUP_FUNION,FLOOKUP_UPDATE,AllCaseEqs()] \\ res_tac)
  \\ reverse (Cases_on ‘v IN FDOM f’)
  THEN1
   (‘~(MEM v (freevars x)) ∧ ~(MEM v (freevars y))’ by (fs [SUBSET_DEF] \\ metis_tac [])
    \\ gvs [subst_ignore_single]
    \\ fs [PULL_FORALL,AND_IMP_INTRO]
    \\ first_x_assum irule \\ fs [] \\ qexists_tac ‘Fail’ \\ fs [closed_def])
  \\ rw [bind_def] \\ fs []
  \\ first_x_assum (qspec_then ‘f ' v’ mp_tac)
  \\ impl_keep_tac
  THEN1 (first_x_assum match_mp_tac \\ qexists_tac ‘v’ \\ fs [FLOOKUP_DEF])
  \\ disch_then (qspec_then ‘f’ mp_tac)
  \\ impl_tac THEN1 fs [SUBSET_DEF,freevars_subst]
  \\ fs [bind_def]
  \\ IF_CASES_TAC \\ fs []
  \\ res_tac \\ fs []
  \\ ‘(∀x. x ∈ FRANGE (FEMPTY |+ (v,f ' v)) ⇒ closed x)’ by fs [FRANGE_DEF]
  \\ drule subst_subst_FUNION \\ fs [] \\ rw [] \\ gvs []
  \\ qsuff_tac ‘FEMPTY |+ (v,f ' v) ⊌ f = f’ \\ rw [] \\ fs []
  \\ fs [fmap_EXT,FUNION_DEF] \\ rw []
  \\ fs [EXTENSION] \\ rw [] \\ eq_tac \\ rw [] \\ fs []
QED

Theorem exp_eq_free:
  ~MEM v (freevars y) ⇒
  (x ≅ y ⇔ ∀z. closed z ⇒ subst v z x ≅ y)
Proof
  metis_tac [exp_eq_forall_subst,subst_ignore_single]
QED

Theorem exp_eq_perm_IMP:
  ∀x y e e'.
    ~(MEM x (freevars e')) ∧ ~(MEM y (freevars e')) ∧ e ≅ perm_exp x y e' ⇒ e ≅ e'
Proof
  metis_tac [exp_eq_perm,exp_eq_sym,exp_eq_trans]
QED

Theorem exp_eq_subst_perm_exp:
  closed e' ⇒ subst y e' e ≅ subst y (perm_exp x y e') e
Proof
  rw [] \\ match_mp_tac exp_eq_subst \\ fs [closed_perm]
  \\ match_mp_tac exp_eq_perm \\ fs [closed_def]
QED

Triviality Lam_Lam:
  Lam x e1 ≅ Lam y e2 ⇔
  ∀xv yv. closed xv ∧ closed yv ⇒ subst y yv (Lam x e1) ≅ subst x xv (Lam y e2)
Proof
  Cases_on ‘x=y’ \\ fs [subst_def]
  \\ ‘closed Fail’ by fs [closed_def]
  THEN1 metis_tac []
  \\ ‘~MEM y (freevars (Lam y e2))’ by fs [MEM_FILTER]
  \\ drule exp_eq_free
  \\ disch_then (once_rewrite_tac o single)
  \\ simp [subst_def]
  \\ ‘∀e1. ~MEM x (freevars (Lam x e1))’ by fs [MEM_FILTER]
  \\ ‘(∀e1 x'. Lam x e1 ≅ x' ⇔ ∀z. closed z ⇒ Lam x e1 ≅ subst x z x')’
         by metis_tac [exp_eq_sym,exp_eq_free]
  \\ pop_assum (simp o single o Once)
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ metis_tac []
QED

Triviality subst_subst_lemma:
  closed y1 ∧ closed y2 ⇒
  (subst x y1 e1 ≅ subst y y2 e2 ⇔
   ∀xv yv. closed xv ∧ closed yv ⇒
           subst y yv (subst x y1 e1) ≅ subst x xv (subst y y2 e2))
Proof
  strip_tac
  \\ Cases_on ‘x=y’ \\ fs [subst_def,subst_subst_eq]
  THEN1 metis_tac []
  \\ ‘closed Fail’ by fs [closed_def]
  \\ simp [subst_def]
  \\ ‘~MEM y (freevars (subst y y2 e2))’ by fs [freevars_subst]
  \\ drule exp_eq_free
  \\ disch_then (once_rewrite_tac o single)
  \\ drule_at (Pos last) subst_subst_single
  \\ disch_then (simp o single)
  \\ ‘∀e1. ~MEM x (freevars (subst x y1 e1))’ by fs [freevars_subst]
  \\ ‘(∀e1 x'. subst x y1 e1 ≅ x' ⇔ ∀z. closed z ⇒ subst x y1 e1 ≅ subst x z x')’
         by metis_tac [exp_eq_sym,exp_eq_free]
  \\ pop_assum (simp o single o Once)
  \\ fs [subst_def,PULL_FORALL,AND_IMP_INTRO]
  \\ metis_tac []
QED

Theorem exp_eq_Lam:
  Lam x e1 ≅ Lam y e2 ⇔
  ∀y1 y2.
    y1 ≅ y2 ∧ closed y1 ∧ closed y2 ⇒
    subst x y1 e1 ≅ subst y y2 e2
Proof
  Cases_on ‘x = y’ THEN1 metis_tac [exp_eq_Lam_lemma]
  \\ fs [Lam_Lam]
  \\ CONV_TAC (RATOR_CONV (SIMP_CONV std_ss [subst_def])) \\ fs []
  \\ CONV_TAC (RAND_CONV (SIMP_CONV std_ss [Once subst_subst_lemma])) \\ fs []
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ ‘∀t xv. closed xv ⇒ (t ≅ Lam y (subst x xv e2) ⇔
                          t ≅ Lam x (subst y (perm_exp x y xv) (perm_exp x y e2)))’ by
   (rw [] \\ eq_tac \\ rw []
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’
    \\ fs [MEM_FILTER,freevars_subst,closed_perm]
    \\ fs [perm_exp_def,perm1_def,subst_single_eqvt])
  \\ fs [exp_eq_Lam_lemma,DOMSUB_FUPDATE_THM]
  \\ fs [PULL_FORALL,AND_IMP_INTRO]
  \\ drule_at Any subst_subst_single
  \\ disch_then (simp o single o GSYM)
  \\ pop_assum kall_tac
  \\ eq_tac \\ rw [] \\ fs [AC CONJ_ASSOC CONJ_COMM]
  \\ first_x_assum (first_x_assum o mp_then (Pos last) mp_tac)
  THEN1
   (disch_then (qspecl_then [‘xv’,‘yv’] assume_tac) \\ gvs []
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [] \\ disch_then kall_tac
    \\ match_mp_tac exp_eq_trans
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ fs []
    \\ fs [freevars_subst,subst_single_eqvt,perm1_def]
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [closed_perm] \\ disch_then kall_tac
    \\ rename [‘subst _ _ e ≅ _’]
    \\ once_rewrite_tac [perm_exp_sym]
    \\ fs [exp_eq_subst_perm_exp])
  THEN1
   (disch_then (qspecl_then [‘xv’,‘yv’] assume_tac) \\ gvs []
    \\ match_mp_tac exp_eq_trans
    \\ ‘y ≠ x’ by fs []
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [closed_perm]
    \\ disch_then (qspecl_then [‘e1’,‘y1’,‘yv’] assume_tac) \\ rfs []
    \\ pop_assum (rewrite_tac o single)
    \\ goal_assum (first_assum o mp_then Any mp_tac)
    \\ drule_at (Pos last) subst_subst_single
    \\ fs [closed_perm]
    \\ disch_then (qspecl_then [‘e2’,‘xv’,‘y2’] assume_tac) \\ rfs []
    \\ pop_assum (rewrite_tac o single)
    \\ match_mp_tac exp_eq_perm_IMP
    \\ qexists_tac ‘x’ \\ qexists_tac ‘y’ \\ fs []
    \\ fs [freevars_subst,subst_single_eqvt,perm1_def, closed_perm]
    \\ fs [exp_eq_subst_perm_exp])
QED

val _ = export_theory();

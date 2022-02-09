open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory arithmeticTheory stringTheory optionTheory pred_setTheory
     listTheory rich_listTheory alistTheory finite_mapTheory sptreeTheory;
open mlmapTheory;
open pure_miscTheory pure_typingTheory pure_typingPropsTheory pure_typingProofTheory
     pure_tcexpTheory pure_inference_commonTheory pure_unificationTheory
     pure_inferenceTheory pure_inferencePropsTheory pure_inference_modelTheory;

val _ = new_theory "pure_inferenceProof";

Overload csubst = ``pure_apply_subst``;

(******************** Lemmas ********************)

Theorem minfer_itype_ok:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ itype_ok (SND ns) 0 it
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[itype_ok_iFunctions, itype_ok] >>
  gvs[LIST_REL_EL_EQN, EVERY_MAP, EVERY_MEM, itype_ok]
  >- (rw[MEM_EL] >> first_x_assum drule >> simp[EL_ZIP])
  >- gvs[oEL_THM]
  >- (
    Cases_on `tys` >> gvs[] >> Cases_on `final_cs` >> gvs[] >>
    gvs[EL_ZIP] >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    rpt (pairarg_tac >> simp[])
    )
  >- (
    Cases_on `tys` >> gvs[]
    >- (
      PairCases_on `ns` >> gvs[namespace_ok_def, oEL_THM, EVERY_EL] >>
      last_x_assum drule >> simp[]
      ) >>
    Cases_on `final_cs` >> gvs[] >>
    gvs[EL_ZIP] >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    rpt (pairarg_tac >> simp[])
    )
QED

Theorem minfer_msets:
  ∀ns mset cexp as cs it tsub vars tsup.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    mImplicit tsub vars tsup ∈ cs
  ⇒ mset ⊆ vars
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (imp_res_tac infer_atom_op_LENGTH >> gvs[MAP2_MAP, EL_MAP, EL_ZIP])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    first_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
    pop_assum drule >> simp[]
    )
  >- (first_x_assum drule >> pairarg_tac >> gvs[])
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (
    ntac 2 $ first_x_assum drule >> pairarg_tac >> gvs[] >>
    ntac 2 strip_tac >> reverse $ gvs[] >- metis_tac[] >>
    qpat_x_assum `MEM _ _` mp_tac >>
    DEP_REWRITE_TAC[MAP2_MAP] >> simp[MEM_MAP, MEM_ZIP, EXISTS_PROD] >>
    reverse conj_tac >- (strip_tac >> gvs[]) >>
    PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    qsuff_tac `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)`
    >- (
      rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
      rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
      ) >>
    drule $ iffRL sortingTheory.PERM_MEM_EQ >>
    simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
    simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then drule >> simp[DISJ_IMP_THM] >> strip_tac >> gvs[] >>
    last_x_assum $ qspec_then `"Subscript"` mp_tac >>
    simp[pure_configTheory.reserved_cns_def] >>
    imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> goal_assum drule
    )
  >- metis_tac[]
  >- (
    last_x_assum drule >> pairarg_tac >> gvs[] >> strip_tac >>
    first_x_assum drule >> simp[] >>
    strip_tac >> reverse $ gvs[] >- metis_tac[] >>
    qpat_x_assum `MEM _ _` mp_tac >>
    DEP_REWRITE_TAC[MAP2_MAP] >> simp[MEM_MAP, MEM_ZIP, EXISTS_PROD] >>
    reverse conj_tac >- (strip_tac >> gvs[]) >>
    PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
    `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
      drule $ iffRL sortingTheory.PERM_MEM_EQ >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
    gvs[MEM_MAP, EXISTS_PROD] >>
    drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
    gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
    irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
    simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
    gvs[oEL_THM] >> goal_assum drule >> simp[]
    )
QED

Theorem minfer_msets_disjoint:
  ∀ns mset cexp as cs it.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ DISJOINT mset (new_vars as cs it)
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[new_vars_def, pure_vars, pure_vars_iFunctions, PULL_EXISTS, MEM_MAP,
      LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP, EVERY_EL] >>
  gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, FLOOKUP_FDIFF,
      DOMSUB_FLOOKUP_THM, MEM_EL, PULL_EXISTS, PULL_FORALL] >>
  gvs[FORALL_AND_THM, IMP_CONJ_THM]
  >- (rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac)
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac)
  >- (
    rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac >>
    irule SUBSET_DISJOINT >> irule_at Any pure_vars_isubst_SUBSET >>
    simp[MAP_MAP_o, combinTheory.o_DEF, pure_vars, MEM_MAP, PULL_EXISTS] >>
    irule_at Any SUBSET_REFL >> rw[MEM_EL] >> gvs[]
    )
  >- (
    rw[] >> gvs[DISJOINT_BIGUNION, PULL_EXISTS] >> rw[] >> res_tac >>
    imp_res_tac infer_atom_op_LENGTH >> simp[MAP2_MAP, EL_MAP, EL_ZIP, pure_vars]
    )
  >- (rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[])
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[PULL_EXISTS] >> rw[MEM_EL] >> res_tac
    )
  >- (
    rw[] >> gvs[EL_ZIP, pure_vars] >- (res_tac >> simp[]) >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> rw[]
    >- res_tac
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (last_x_assum drule >> pairarg_tac >> rw[] >> res_tac)
    >- (
      gvs[EL_ZIP] >> pairarg_tac >> gvs[pure_vars] >>
      gvs[get_massumptions_def, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      every_case_tac >> gvs[]
      >- (last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT])
      >- (
        reverse $ rw[] >- (last_x_assum drule >> simp[]) >>
        gvs[MEM_EL] >> last_x_assum drule >> pairarg_tac >> rw[] >>
        metis_tac[DISJOINT_ALT]
        )
      >- (last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT])
      >- (
        reverse $ rw[] >- (last_x_assum drule >> simp[]) >>
        gvs[MEM_EL] >> last_x_assum drule >> pairarg_tac >> rw[] >>
        metis_tac[DISJOINT_ALT]
        )
      )
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> res_tac >> simp[] >>
    gvs[EL_ZIP, EL_MAP, pure_vars] >>
    gvs[get_massumptions_def] >> every_case_tac >> gvs[] >> metis_tac[DISJOINT_ALT]
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> rw[]
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `0` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[]
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `SUC n` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[] >>
      Cases_on `tys` >> gvs[]
      )
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >> gvs[pure_vars]
      >- (
        gvs[get_massumptions_def] >> every_case_tac >> gvs[] >>
        last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT]
        )
      >- (
        qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
        DEP_REWRITE_TAC[MAP2_MAP] >> simp[] >>
        reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, MEM_ZIP] >> rw[] >> gvs[pure_vars, EL_MAP] >>
          qpat_x_assum `_ ∈ get_massumptions _ _` mp_tac >>
          gvs[get_massumptions_def] >> CASE_TAC >> rw[] >>
          last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        `cn ≠ "Subscript"` by (
          imp_res_tac ALOOKUP_MEM >> gvs[pure_configTheory.reserved_cns_def] >>
          gvs[MEM_MAP, FORALL_PROD] >> metis_tac[]) >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        simp[Once MEM_EL, PULL_EXISTS] >>
        disch_then drule >> rw[] >> gvs[] >>
        drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> simp[]
        )
      >- (last_x_assum drule >> simp[])
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `0` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[]
      )
    )
  >- (
    rw[] >> every_case_tac >> gvs[] >> rw[]
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- res_tac
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >>
      gvs[FLOOKUP_FDIFF] >> last_x_assum drule >> rw[] >> res_tac
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `0` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[]
      )
    >- (
      last_x_assum assume_tac >>
      last_x_assum $ qspec_then `SUC n` mp_tac >>
      Cases_on `final_cs` >> gvs[] >> pairarg_tac >> simp[] >>
      Cases_on `tys` >> gvs[]
      )
    >- (
      first_x_assum drule >> pairarg_tac >> rw[] >> gvs[pure_vars]
      >- (
        gvs[get_massumptions_def] >> every_case_tac >> gvs[] >>
        last_x_assum drule >> rw[] >> metis_tac[DISJOINT_ALT]
        )
      >- (
        qpat_x_assum `MEM _ (MAP2 _ _ _)` mp_tac >>
        DEP_REWRITE_TAC[MAP2_MAP] >> simp[] >>
        reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, MEM_ZIP] >> rw[] >> gvs[pure_vars, EL_MAP] >>
          qpat_x_assum `_ ∈ get_massumptions _ _` mp_tac >>
          gvs[get_massumptions_def] >> CASE_TAC >> simp[] >> strip_tac >>
          last_x_assum drule >> simp[] >> strip_tac >>
          conj_tac >- metis_tac[DISJOINT_ALT] >>
          irule SUBSET_DISJOINT >> irule_at Any pure_vars_isubst_SUBSET >>
          simp[MAP_MAP_o, combinTheory.o_DEF, pure_vars, MEM_MAP, PULL_EXISTS] >>
          irule_at Any SUBSET_REFL >> rw[MEM_EL] >> gvs[]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        `MEM (cn, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
          drule $ iffRL sortingTheory.PERM_MEM_EQ >>
          simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
          disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
        gvs[MEM_MAP, EXISTS_PROD] >>
        drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
        gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
        simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
        gvs[oEL_THM] >> goal_assum drule >> simp[]
        )
      >- (last_x_assum drule >> simp[])
      )
    >- (
      last_x_assum assume_tac >> last_x_assum $ qspec_then `0` mp_tac >>
      reverse $ Cases_on `final_cs` >> gvs[]
      >- (pairarg_tac >> simp[]) >>
      PairCases_on `ns` >> gvs[namespace_ok_def] >>
      gvs[EVERY_EL, oEL_THM] >> last_x_assum drule >> simp[]
      )
    )
QED

Theorem minfer_pure_vars[local]:
  ∀ns mset cexp as cs it v.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns ∧
    v ∈ pure_vars it
  ⇒ v ∈ new_vars as cs Exception
Proof
  ntac 6 gen_tac >> Induct_on `minfer` >> rw[] >>
  gvs[pure_vars, new_vars_def, pure_vars_iFunctions] >>
  gvs[LIST_REL_EL_EQN, EL_ZIP, MEM_EL, MAP2_MAP, EL_MAP,
      PULL_EXISTS, SF CONJ_ss, pure_vars]
  >- (
    first_x_assum drule >> strip_tac >> pop_assum drule >> reverse $ rw[]
    >- (disj2_tac >> rpt $ goal_assum drule) >>
    disj1_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FOLDR_maunion, FLOOKUP_DEF,
        PULL_EXISTS, GSYM CONJ_ASSOC] >>
    rpt $ goal_assum $ drule_at Any >> simp[EL_MEM]
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum drule) >>
    rpt disj1_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, PULL_EXISTS] >>
    Cases_on `FLOOKUP as k` >> gvs[]
    >- (qexistsl_tac [`s`,`k`] >> simp[])
    >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
    )
  >- (disj2_tac >> rpt disj1_tac >> irule_at Any EQ_REFL >> simp[])
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum drule) >>
    rpt disj1_tac >>
    gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, PULL_EXISTS] >>
    Cases_on `FLOOKUP as k` >> gvs[]
    >- (qexistsl_tac [`s`,`k`] >> simp[])
    >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
    )
  >- (disj2_tac >> disj1_tac >> disj2_tac >> irule_at Any EQ_REFL >> simp[])
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (disj2_tac >> rpt disj1_tac >> rpt $ goal_assum drule) >>
    Cases_on `s ∈ FRANGE (FDIFF as (set xs))`
    >- (rpt disj1_tac >> goal_assum drule >> simp[]) >>
    rpt disj2_tac >> gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >>
    first_x_assum drule >> rw[MEM_EL] >>
    qexists_tac `n` >> simp[get_massumptions_def] >>
    goal_assum $ drule_at Any >> simp[]
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum drule) >>
    Cases_on `s ∈ FRANGE (as' \\ x)`
    >- (
      rpt disj1_tac >> qpat_x_assum `_ ∈ FRANGE as'` kall_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, PULL_EXISTS] >>
      Cases_on `FLOOKUP as k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x' ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >> rw[] >>
      disj2_tac >> rpt disj1_tac >> simp[get_massumptions_def] >>
      goal_assum $ drule_at Any >> simp[]
      )
    )

  >- (
    first_x_assum drule >> strip_tac >> gvs[SF SFY_ss] >>
    simp[FDIFF_maunion] >>
    Cases_on `s ∈ FRANGE (FDIFF as' (set (MAP FST fns)))`
    >- (
      rpt disj1_tac >> qpat_x_assum `_ ∈ FRANGE as'` kall_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FDIFF, PULL_EXISTS] >>
      Cases_on `FLOOKUP as k` >> gvs[] >>
      Cases_on `FLOOKUP (FOLDR maunion FEMPTY ass) k` >> gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x`,`k`] >> simp[])
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`s ∪ x'`,`k`] >> simp[])
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >> first_x_assum drule >> rw[] >>
      rpt disj2_tac >> gvs[MEM_EL, EL_MAP] >> goal_assum $ drule_at Any >>
      pairarg_tac >> gvs[PULL_EXISTS, pure_vars] >>
      simp[get_massumptions_def, FLOOKUP_maunion] >>
      qexists_tac `v` >> simp[] >> CASE_TAC >> simp[]
      )
    )
  >- (
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> goal_assum drule >> simp[]) >>
    Cases_on `s ∈ FRANGE (FDIFF as (v INSERT set pvars))`
    >- (
      rpt disj1_tac >> qpat_x_assum `_ ∈ FRANGE as` kall_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FDIFF, PULL_EXISTS] >>
      Cases_on `FLOOKUP as' k` >>  gvs[]
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x ∪ s`,`k`] >> simp[])
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF] >> first_x_assum drule >> rw[] >>
      simp[get_massumptions_def, GSYM DISJ_ASSOC]
      >- (ntac 5 disj2_tac >> disj1_tac >> goal_assum $ drule_at Any >> simp[]) >>
      ntac 6 disj2_tac >> disj1_tac >> gvs[MEM_EL] >>
      ntac 2 (goal_assum $ drule_at Any >> simp[])
      )
    )
  >- (
    first_x_assum $ qspec_then `0` mp_tac >>
    impl_keep_tac >- (Cases_on `cases` >> gvs[]) >>
    last_x_assum assume_tac >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    pairarg_tac >> gvs[] >> ntac 2 strip_tac >>
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]) >>
    Cases_on `s ∈ FRANGE (FDIFF (HD ass) (v INSERT set pvars))`
    >- (
      qpat_x_assum `_ ∈ FRANGE (HD _)` kall_tac >> rpt disj1_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      simp[PULL_EXISTS] >>
      qexists_tac `(case FLOOKUP as k of NONE => {} | SOME s => s) ∪
        BIGUNION ({ s | ∃m. MEM m final_as ∧ FLOOKUP m k = SOME s})` >>
      simp[PULL_EXISTS] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      qexists_tac `k` >> simp[GSYM CONJ_ASSOC] >>
      goal_assum drule >> qexists_tac `FDIFF (HD ass) (v INSERT set pvars)` >>
      simp[FLOOKUP_FDIFF] >> conj_asm1_tac >- (Cases_on `final_as` >> gvs[]) >>
      TOP_CASE_TAC >> gvs[]
      >- (goal_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]) >>
      IF_CASES_TAC >> gvs[] >> irule FALSITY >>
      first_x_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      rpt disj2_tac >> simp[Once SWAP_EXISTS_THM] >>
      qexists_tac `0` >> simp[]
      >- (
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS] >>
        simp[get_massumptions_def, pure_vars] >> goal_assum drule >> simp[]
        )
      >- (
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS] >> DEP_REWRITE_TAC[MAP2_MAP] >> reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, PULL_EXISTS, MEM_ZIP, pure_vars] >> gvs[MEM_EL] >>
          qexists_tac `n` >> simp[get_massumptions_def] >>
          goal_assum drule >> simp[]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        qsuff_tac `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)`
        >- (
          rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
          rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
          ) >>
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        simp[Once MEM_EL, PULL_EXISTS] >>
        disch_then drule >> simp[DISJ_IMP_THM] >> strip_tac >> gvs[] >>
        first_x_assum $ qspec_then `"Subscript"` mp_tac >>
        simp[pure_configTheory.reserved_cns_def] >>
        imp_res_tac ALOOKUP_MEM >> simp[MEM_MAP, EXISTS_PROD] >> goal_assum drule
        )
      )
    )
  >- (
    first_x_assum $ qspec_then `0` mp_tac >> impl_keep_tac
    >- (
      PairCases_on `ns` >> gvs[namespace_ok_def] >>
      gvs[EVERY_EL, oEL_THM] >> last_x_assum drule >> simp[] >> strip_tac >>
      imp_res_tac sortingTheory.PERM_LENGTH >> gvs[] >> Cases_on `cdefs` >> gvs[]
      ) >>
    last_x_assum assume_tac >> last_x_assum $ qspec_then `0` mp_tac >> simp[] >>
    pairarg_tac >> gvs[] >> ntac 2 strip_tac >>
    first_x_assum drule >> reverse strip_tac >> gvs[]
    >- (rpt disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[]) >>
    Cases_on `s ∈ FRANGE (FDIFF (HD ass) (v INSERT set pvars))`
    >- (
      qpat_x_assum `_ ∈ FRANGE (HD _)` kall_tac >> rpt disj1_tac >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      simp[PULL_EXISTS] >>
      qexists_tac `(case FLOOKUP as k of NONE => {} | SOME s => s) ∪
        BIGUNION ({ s | ∃m. MEM m final_as ∧ FLOOKUP m k = SOME s})` >>
      simp[PULL_EXISTS] >> irule_at Any OR_INTRO_THM2 >> simp[PULL_EXISTS] >>
      qexists_tac `k` >> simp[GSYM CONJ_ASSOC] >>
      goal_assum drule >> qexists_tac `FDIFF (HD ass) (v INSERT set pvars)` >>
      simp[FLOOKUP_FDIFF] >> conj_asm1_tac >- (Cases_on `final_as` >> gvs[]) >>
      TOP_CASE_TAC >> gvs[]
      >- (goal_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]) >>
      IF_CASES_TAC >> gvs[] >> irule FALSITY >>
      first_x_assum drule >> gvs[FDOM_FDIFF, FLOOKUP_DEF]
      )
    >- (
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_FDIFF, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      rpt disj2_tac >> simp[Once SWAP_EXISTS_THM] >>
      qexists_tac `0` >> simp[]
      >- (
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS] >>
        simp[get_massumptions_def, pure_vars] >> goal_assum drule >> simp[]
        )
      >- (
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS] >> DEP_REWRITE_TAC[MAP2_MAP] >> reverse conj_asm1_tac
        >- (
          simp[MEM_MAP, PULL_EXISTS, MEM_ZIP, pure_vars] >> gvs[MEM_EL] >>
          qexists_tac `n` >> simp[get_massumptions_def] >>
          goal_assum drule >> simp[]
          ) >>
        simp[] >> PairCases_on `ns` >> gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
        `MEM (cname, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
          drule $ iffRL sortingTheory.PERM_MEM_EQ >>
          simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
          disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
        gvs[MEM_MAP, EXISTS_PROD] >>
        drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
        gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
        irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
        simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
        gvs[oEL_THM] >> goal_assum drule >> simp[]
        )
      )
    )
QED

Theorem minfer_pure_vars:
  ∀ns mset cexp as cs it v.
    minfer ns mset cexp as cs it ∧
    namespace_ok ns
  ⇒ pure_vars it ⊆ new_vars as cs Exception
Proof
  rw[SUBSET_DEF] >> imp_res_tac minfer_pure_vars
QED


(******************** Simple lemmas ********************)

Theorem CARD_has_fmap_linv:
  ∀f. (∃g. fmap_linv f g) ⇔ CARD (FDOM f) = CARD (FRANGE f)
Proof
  rw[miscTheory.has_fmap_linv_inj, CARD_fmap_injection] >>
  simp[INJ_DEF, FLOOKUP_DEF, FRANGE_DEF] >> eq_tac >> rw[] >>
  goal_assum drule >> gvs[]
QED

Theorem fmap_linv_sym:
  ∀f g. fmap_linv f g ⇔ fmap_linv g f
Proof
  rw[miscTheory.fmap_linv_def] >> eq_tac >> rw[] >>
  gvs[FLOOKUP_DEF, FRANGE_DEF, EXTENSION] >> metis_tac[]
QED

Theorem fmap_linv_alt_def:
  fmap_linv f g ⇔
    FDOM f = FRANGE g ∧
    FDOM g = FRANGE f ∧
    (∀x. x ∈ FDOM f ⇒ g ' (f ' x) = x) ∧
    (∀x. x ∈ FDOM g ⇒ f ' (g ' x) = x)
Proof
  eq_tac >> strip_tac
  >- (imp_res_tac fmap_linv_sym >> gvs[miscTheory.fmap_linv_def, FLOOKUP_DEF])
  >- (
    rw[miscTheory.fmap_linv_def, FLOOKUP_DEF] >>
    last_x_assum $ assume_tac o GSYM >> gvs[] >>
    simp[FRANGE_DEF] >> goal_assum drule >> simp[]
    )
QED

Theorem pure_apply_subst_split_isubst:
  ∀fm (sub : num |-> itype) it.
    CARD (FDOM fm) = CARD (FRANGE fm) ∧
    count (CARD (FDOM fm)) = FRANGE fm ∧
    FDOM sub ⊆ FDOM fm ∧
    freedbvars it = {}
  ⇒ ∃gm.
      fmap_linv fm gm ∧
      isubst
        (GENLIST (λn. csubst sub (CVar $ gm ' n))
          (CARD (FDOM fm)))
        (csubst (DBVar o_f fm) it) = csubst sub it
Proof
  rw[pure_apply_subst, FLOOKUP_DEF] >> drule $ iffRL CARD_has_fmap_linv >> rw[] >>
  goal_assum drule >> qpat_x_assum `_ = {}` mp_tac >>
  qid_spec_tac `it` >> recInduct itype_ind >>
  rw[pure_apply_subst, isubst_def] >> gvs[freedbvars_def] >>
  gvs[LIST_TO_SET_EQ_SING, EVERY_MAP, EVERY_MEM] >>
  simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f, FLOOKUP_o_f] >>
  gvs[miscTheory.fmap_linv_def, FLOOKUP_DEF] >>
  Cases_on `n ∈ FDOM sub` >> Cases_on `n ∈ FDOM fm` >> gvs[SUBSET_DEF, isubst_def] >>
  qsuff_tac `fm ' n < CARD (FRANGE fm)` >> rw[] >>
  gvs[FRANGE_DEF, EXTENSION]
QED

Theorem pure_walkstar_pure_apply_subst_pure_walkstar[local]:
  ∀s. pure_wfs s ⇒
  ∀it sub. (∀v. v ∈ FRANGE sub ⇒ pure_vars v = {}) ⇒
  pure_walkstar s (pure_apply_subst sub (pure_walkstar s it)) =
  pure_apply_subst sub (pure_walkstar s it)
Proof
  gen_tac >> strip_tac >>
  qspec_then `s` mp_tac pure_walkstar_alt_ind >> simp[] >>
  disch_then ho_match_mp_tac >> rw[pure_walkstar_alt, pure_apply_subst]
  >- simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f]
  >- simp[MAP_MAP_o, combinTheory.o_DEF, MAP_EQ_f] >>
  CASE_TAC >> gvs[] >>
  simp[pure_apply_subst] >> CASE_TAC >> gvs[pure_walkstar_alt] >>
  irule pure_walkstar_unchanged >> simp[] >>
  gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >>
  first_x_assum drule >> simp[]
QED

Triviality new_vars_SUBSET:
  BIGUNION (FRANGE as) ⊆ BIGUNION (FRANGE as') ∧ cs ⊆ cs' ∧
  pure_vars it ⊆ pure_vars it' ∧
  v ∈ new_vars as cs it ⇒
  v ∈ new_vars as' cs' it'
Proof
  rw[new_vars_def] >> gvs[SUBSET_DEF] >> metis_tac[]
QED

Triviality new_vars_SUBSET_minfer:
  BIGUNION (FRANGE as) ⊆ BIGUNION (FRANGE as') ∧ cs ⊆ cs' ∧
  pure_vars it ⊆ new_vars as cs Exception ⇒
  ∀n. n ∈ new_vars as cs it ⇒ n ∈ new_vars as' cs' it'
Proof
  rw[new_vars_def] >> gvs[SUBSET_DEF, pure_vars] >> metis_tac[]
QED


Triviality pure_vars_csubst_EMPTY_suff:
  (∀it. it ∈ FRANGE s ⇒ pure_vars it = {}) ∧
  pure_vars t ⊆ FDOM s ⇒
  pure_vars (csubst s t) = {}
Proof
  rw[] >> once_rewrite_tac[GSYM SUBSET_EMPTY] >> irule SUBSET_TRANS >>
  irule_at Any pure_vars_pure_apply_subst_SUBSET >>
  simp[IMAGE_EQ_SING, SUBSET_DIFF_EMPTY]
QED

Triviality freedbvars_isubst_EMPTY_suff:
  ∀it its.
    freedbvars it ⊆ count (LENGTH its) ∧
    EVERY ( λit. freedbvars it = {}) its
  ⇒ freedbvars (isubst its it) = {}
Proof
  Induct using itype_ind >> rw[isubst_def, freedbvars_def] >>
  gvs[LIST_TO_SET_MAP, IMAGE_EQ_SING, PULL_EXISTS, DISJ_EQ_IMP, BIGUNION_SUBSET] >>
  gvs[EVERY_EL]
QED

Triviality shift_shift_let_lemma:
  ∀it t sub vs1 vs2.
    type_of (csubst (ishift vs1 o_f sub) it) = SOME t ∧
    freedbvars it ⊆ count vs1 ⇒
    type_of (csubst ((ishift vs1 ∘ ishift vs2) o_f sub) it) =
    SOME (shift_db vs1 vs2 t)
Proof
  Induct using itype_ind >> rw[] >>
  gvs[pure_apply_subst, freedbvars_def, type_of_def, shift_db_def]
  >- (
    ntac 2 $ pop_assum mp_tac >> qid_spec_tac `z` >>
    Induct_on `ts` >> rw[] >> gvs[]
    )
  >- (
    ntac 2 $ pop_assum mp_tac >> qid_spec_tac `z` >>
    Induct_on `ts` >> rw[] >> gvs[]
    ) >>
  gvs[FLOOKUP_o_f] >> CASE_TAC >> gvs[type_of_def] >>
  drule_then (assume_tac o GSYM) type_of_SOME >> simp[] >>
  simp[ishift_itype_of, type_of_itype_of] >> gvs[type_of_ishift] >>
  simp[tshift_tshift] >> simp[GSYM tshift_tshift] >> simp[GSYM shift_db_shift_db]
QED



(******************** Definitions/apparatus ********************)

Definition msubst_vars_def:
  msubst_vars s vars = BIGUNION (IMAGE (pure_vars o pure_walkstar s o CVar) vars)
End

Theorem subst_vars_msubst_vars:
  ∀s vs. pure_wfs s ⇒
    domain (subst_vars s vs) = msubst_vars s (domain vs)
Proof
  rw[subst_vars_def, msubst_vars_def] >>
  qsuff_tac
    `∀m b.
      domain (
        foldi (λn u acc. union acc (freecvars (pure_walkstar s (CVar n)))) m b vs) =
      BIGUNION (IMAGE
        (pure_vars o pure_walkstar s o CVar o (λi. m + sptree$lrnext m * i))
        (domain vs))
        ∪ domain b`
  >- rw[Once lrnext_def, combinTheory.o_DEF] >>
  qid_spec_tac `vs` >> Induct >> rw[foldi_def] >>
  simp[pure_walkstar_alt, freecvars_def, domain_union]
  >- (CASE_TAC >> simp[freecvars_pure_vars, domain_union, Once UNION_COMM]) >>
  simp[IMAGE_IMAGE, combinTheory.o_DEF] >>
  simp[lrnext_lrnext, lrnext_lrnext_2, LEFT_ADD_DISTRIB]
  >- simp[AC UNION_ASSOC UNION_COMM] >>
  qmatch_goalsub_abbrev_tac `BIGUNION A ∪ (BIGUNION B ∪ _ ∪ C) = C' ∪ _ ∪ _ ∪ _` >>
  qsuff_tac `C = C'` >> rw[] >- simp[AC UNION_ASSOC UNION_COMM] >>
  unabbrev_all_tac >> CASE_TAC >> simp[freecvars_pure_vars]
QED

Theorem msubst_vars_UNION:
  msubst_vars s (a ∪ b) = msubst_vars s a ∪ msubst_vars s b
Proof
  simp[msubst_vars_def]
QED

Definition ctxt_vars_def:
  ctxt_vars ctxt = BIGUNION (set (MAP (λ(x,vs,t). pure_vars t) ctxt))
End

Theorem ctxt_vars:
  ctxt_vars [] = {} ∧
  ctxt_vars ((x,vs,t)::ctxt) = pure_vars t ∪ ctxt_vars ctxt ∧
  ctxt_vars (ctxt ++ ctxt') = ctxt_vars ctxt ∪ ctxt_vars ctxt'
Proof
  simp[ctxt_vars_def]
QED

Definition subst_ctxt_def:
  subst_ctxt s ctxt = MAP (λ(x,vs,t). (x,vs,pure_walkstar s t)) ctxt
End

Theorem subst_ctxt:
  subst_ctxt s [] = [] ∧
  subst_ctxt s ((x,vs,t)::ctxt) =
    (x,vs,pure_walkstar s t)::(subst_ctxt s ctxt) ∧
  subst_ctxt s (ctxt ++ ctxt') = subst_ctxt s ctxt ++ subst_ctxt s ctxt'
Proof
  simp[subst_ctxt_def]
QED

Theorem ctxt_vars_subst_ctxt:
  pure_wfs s ⇒
  ctxt_vars (subst_ctxt s ctxt) = msubst_vars s (ctxt_vars ctxt)
Proof
  Induct_on `ctxt` >> simp[ctxt_vars, subst_ctxt, msubst_vars_def] >>
  rw[] >> PairCases_on `h` >> simp[ctxt_vars, subst_ctxt, msubst_vars_def] >>
  simp[pure_vars_pure_walkstar_alt]
QED

Definition satisfies_def:
  satisfies tdefs s (mUnify t1 t2) = (pure_walkstar s t1 = pure_walkstar s t2) ∧

  satisfies tdefs s (mInstantiate t (vars, scheme)) = (
    ∃subs.
      LENGTH subs = vars ∧ EVERY (itype_ok tdefs 0) subs ∧
      EVERY (λit. pure_vars it ⊆ pure_vars (pure_walkstar s t)) subs ∧
      pure_walkstar s t = isubst subs (pure_walkstar s scheme)) ∧

  satisfies tdefs s (mImplicit tsub vars tsup) = (
    ∃sub.
      FDOM sub ⊆ pure_vars (pure_walkstar s tsup) DIFF (msubst_vars s vars) ∧
      (∀it. it ∈ FRANGE sub ⇒ itype_ok tdefs 0 it ∧
        pure_vars it ⊆ pure_vars (pure_walkstar s tsub)) ∧
      pure_walkstar s tsub = pure_apply_subst sub (pure_walkstar s tsup))
End

Theorem satisfies_lemmas:
    satisfies tdefs s (mUnify t1 t2) = satisfies tdefs s (mInstantiate t1 (0, t2)) ∧
    (pure_wfs s ⇒
      satisfies tdefs s (mUnify t1 t2) =
      satisfies tdefs s (mImplicit t1 (pure_vars t2) t2)) ∧
    (pure_wfs s ∧ freedbvars (pure_walkstar s t2) = {} ⇒
      satisfies tdefs s (mImplicit t1 vs t2) =
        ∀gen.
          let new = pure_vars (pure_walkstar s t2) DIFF msubst_vars s vs in
          FDOM gen = new ∧
          FRANGE gen = count (CARD new)
        ⇒ satisfies tdefs s $ mInstantiate t1 $
            (CARD new, csubst (DBVar o_f gen) (pure_walkstar s t2)))
Proof
  rpt conj_tac >> rw[satisfies_def]
  >- (
    eq_tac >> rw[] >- (qexists_tac `FEMPTY` >> simp[]) >>
    gvs[msubst_vars_def, PULL_EXISTS] >>
    irule pure_apply_subst_unchanged >>
    simp[pure_vars_pure_walkstar_alt] >> simp[PULL_EXISTS, pure_vars] >>
    simp[Once DISJOINT_SYM] >> rw[DISJOINT_ALT] >>
    gvs[SUBSET_DEF] >> metis_tac[]
    ) >>
  eq_tac >> rw[] >> gvs[]
  >- (
    simp[Once pure_apply_subst_min] >>
    qmatch_goalsub_abbrev_tac `csubst sub'` >>
    qspecl_then [`gen`,`sub'`,`pure_walkstar s t2`]
      mp_tac pure_apply_subst_split_isubst >>
    simp[] >> impl_tac >> rw[]
    >- (
      unabbrev_all_tac >> gvs[FDOM_DRESTRICT] >>
      gvs[DISJOINT_DEF, EXTENSION, SUBSET_DEF] >> metis_tac[]
      ) >>
    qmatch_asmsub_abbrev_tac `isubst its` >>
    qexists_tac `its` >> simp[] >>
    DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
    unabbrev_all_tac >> simp[] >>
    simp[EVERY_GENLIST] >> rw[]
    >- (
      simp[pure_apply_subst, FLOOKUP_DRESTRICT] >>
      every_case_tac >> gvs[itype_ok] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> metis_tac[]
      )
    >- (
      rw[SUBSET_DEF] >>
      simp[pure_vars_pure_apply_subst] >> simp[PULL_EXISTS, pure_vars] >>
      goal_assum drule >>
      qsuff_tac `gm ' n ∈ FDOM gen` >- rw[] >>
      gvs[fmap_linv_alt_def] >> simp[IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
      goal_assum drule >> simp[]
      )
    >- simp[Once pure_apply_subst_min]
    )
  >- (
    qmatch_asmsub_abbrev_tac `FDOM _ = diff` >>
    `FINITE diff` by (unabbrev_all_tac >> irule FINITE_DIFF >> simp[]) >>
    drule $ INST_TYPE [beta |-> ``:num``] cardinalTheory.CARD_CARDEQ_I >>
    disch_then $ qspec_then `count (CARD diff)` mp_tac >> simp[] >>
    rw[cardinalTheory.cardeq_def] >>
    first_x_assum $ qspec_then `FUN_FMAP f diff` mp_tac >> simp[] >>
    imp_res_tac BIJ_IMAGE >> rw[] >> simp[] >>
    pop_assum mp_tac >>
    DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >> strip_tac >>
    simp[isubst_pure_apply_subst_alt] >>
    irule_at Any EQ_REFL >> unabbrev_all_tac >> simp[DISJOINT_DIFF] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[]
    >- (
      rw[isubst_def] >- gvs[EVERY_EL, pure_vars] >>
      irule FALSITY >> pop_assum mp_tac >> simp[] >> gvs[BIJ_IFF_INV]
      ) >>
    reverse $ rw[isubst_def]
    >- (irule FALSITY >> pop_assum mp_tac >> simp[] >> gvs[BIJ_IFF_INV]) >>
    simp[pure_vars_pure_apply_subst] >>
    simp[combinTheory.o_DEF, SUBSET_DEF, PULL_EXISTS] >> rw[] >>
    simp[pure_apply_subst, FLOOKUP_o_f, FLOOKUP_FUN_FMAP] >>
    qexists_tac `x'` >> simp[isubst_def]
    )
QED


(******************** Main results ********************)

Definition ctxt_rel_def:
  ctxt_rel tdefs sub as ctxt ⇔
    ∀k v. FLOOKUP as k = SOME v ⇒
      ∃vars scheme.
        ALOOKUP ctxt k = SOME (vars,scheme) ∧
        ∀n. n ∈ v ⇒
          ∃inst. LENGTH inst = vars ∧
            EVERY (λit. itype_ok tdefs 0 it ∧
                        pure_vars it ⊆ pure_vars (pure_walkstar sub (CVar n))) inst ∧
            isubst inst (pure_walkstar sub scheme) = pure_walkstar sub (CVar n)
End

Theorem ctxt_rel_mInstantiate:
  pure_wfs sub ∧
  ctxt_rel tdefs sub as ctxt ⇒
    ∀k v. FLOOKUP as k = SOME v ⇒
      ∃vars scheme. ALOOKUP ctxt k = SOME (vars,scheme) ∧
        ∀n. n ∈ v ⇒
          satisfies tdefs sub $ mInstantiate (CVar n) (vars, scheme)
Proof
  rw[ctxt_rel_def] >> first_x_assum drule >> rw[] >> simp[] >>
  rw[] >> first_x_assum drule >> rw[satisfies_def] >>
  irule_at Any EQ_REFL >> simp[] >> gvs[EVERY_MEM]
QED

Theorem ctxt_rel_sub:
  ∀tdefs sub as ctxt as'.
    ctxt_rel tdefs sub as ctxt ∧
    (∀k v. FLOOKUP as' k = SOME v ⇒ ∃v'. FLOOKUP as k = SOME v' ∧ v ⊆ v')
  ⇒ ctxt_rel tdefs sub as' ctxt
Proof
  rw[ctxt_rel_def] >> first_x_assum drule >> rw[] >>
  first_x_assum drule >> rw[] >> simp[] >> rw[] >> gvs[SUBSET_DEF]
QED

Theorem inference_constraints_sound_lemma:
  ∀ns sub.
    namespace_ok ns ∧
    pure_wfs sub ∧
    (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ⇒
  ∀mset cexp as cs it ictxt ctxt db closing t.
    minfer ns mset cexp as cs it ∧
    FINITE mset ∧
    (∀c. c ∈ cs ⇒ satisfies (SND ns) sub c) ∧
    ctxt_rel (SND ns) sub as ictxt ∧
    EVERY (λ(x,vs,it). freedbvars it ⊆ count vs) ictxt ∧
    msubst_vars sub (ctxt_vars ictxt) = msubst_vars sub mset ∧
    (∀n. n ∈ new_vars as cs it ⇒
      pure_vars (pure_walkstar sub (CVar n)) ⊆ FDOM closing) ∧
    (∀it. it ∈ FRANGE closing ⇒ pure_vars it = {} ∧ itype_ok (SND ns) db it) ∧
    LIST_REL (λ(xs,vs,t) (ixs,ivs,it). xs = ixs ∧ vs = ivs ∧
      type_of $ csubst (ishift vs o_f closing) (pure_walkstar sub it) = SOME t)
      ctxt ictxt ∧
    type_of $ csubst closing (pure_walkstar sub it) = SOME t
    ⇒ type_tcexp ns db [] ctxt (tcexp_of cexp) t
Proof
  rpt gen_tac >> strip_tac >>
  ntac 5 gen_tac >> Induct_on `minfer` >> rw[tcexp_of_def] >> gvs[]
  >- ( (* Var *)
    simp[Once type_tcexp_cases] >> gvs[ctxt_rel_def, FLOOKUP_UPDATE] >>
    qspecl_then [`ictxt`,`ctxt`] mp_tac ALOOKUP_SOME_EL_2 >>
    disch_then drule >> gvs[LIST_REL_EL_EQN] >> impl_tac
    >- (
      rw[Once LIST_EQ_REWRITE, EL_MAP] >>
      first_x_assum drule >> rpt (pairarg_tac >> simp[])
      ) >>
    strip_tac >> gvs[] >> rename1 `_ = (v,s)` >> PairCases_on `s` >>
    first_x_assum drule >> rw[specialises_def] >>
    `EVERY (λit. pure_vars it = {}) (MAP (csubst closing) inst)` by (
      gvs[EVERY_MAP, EVERY_MEM] >> rw[] >>
      first_x_assum drule >> rw[] >>
      simp[pure_vars_pure_apply_subst] >> rw[IMAGE_EQ_SING, DISJ_EQ_IMP] >>
      simp[pure_apply_subst] >> reverse CASE_TAC >> gvs[pure_vars]
      >- (gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS] >> first_x_assum drule >> simp[]) >>
      gvs[new_vars_def, pure_vars] >> gvs[FLOOKUP_DEF, SUBSET_DEF]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >>
    qexists_tac `ts` >> rw[] >> gvs[]
    >- (
      gvs[MAP_EQ_EVERY2, EVERY_EL, LIST_REL_EL_EQN] >> rw[] >>
      simp[GSYM itype_ok_type_ok] >> first_x_assum drule >> rw[EL_MAP] >>
      drule type_of_SOME >> rw[] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      last_x_assum drule >> rw[] >> gvs[itype_ok_def]
      )
    >- gvs[MAP_EQ_EVERY2] >>
    simp[GSYM itype_of_11, GSYM isubst_itype_of] >>
    drule type_of_SOME_MAP >> rw[] >>
    imp_res_tac type_of_SOME >> rw[] >>
    simp[GSYM pure_apply_subst_isubst_strong]
    )
  >- ( (* Tuple *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[pure_walkstar_alt, pure_apply_subst] >>
    imp_res_tac $ cj 1 type_of_SOME_lemma >> gvs[] >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MAP_EQ_EVERY2] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- (rw[] >> first_x_assum irule >> goal_assum drule >> simp[EL_MEM]) >>
    rpt $ goal_assum $ drule_at Any >> simp[] >> rw[]
    >- (
      gvs[GSYM pure_walkstar_alt] >> first_x_assum irule >>
      irule new_vars_SUBSET >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      simp[pure_vars, SUBSET_DEF, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS, GSYM CONJ_ASSOC] >>
      goal_assum drule >> gvs[FLOOKUP_DEF] >>
      simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Ret *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    last_x_assum irule >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[] >>
    first_x_assum irule >> irule new_vars_SUBSET >>
    goal_assum drule >> simp[pure_vars]
    )
  >- ( (* Bind *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >>
    `pure_vars (csubst closing (pure_walkstar sub (CVar f1))) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Raise *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[GSYM pure_walkstar_alt] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      imp_res_tac type_of_SOME >> simp[GSYM itype_ok_type_ok] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      irule itype_ok_pure_walkstar >> rw[itype_ok] >> gvs[itype_ok_def]
      )
    )
  >- ( (* Handle *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Act *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    last_x_assum irule >> rpt $ goal_assum $ drule_at Any >> rw[] >>
    gvs[GSYM pure_walkstar_alt] >>
    first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
    imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
    )
  >- ( (* Alloc *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Length *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >>
    `pure_vars (csubst closing (pure_walkstar sub (CVar fresh))) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[] >>
    first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
    imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
    )
  >- ( (* Deref *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* Update *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    ntac 3 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    gvs[GSYM pure_walkstar_alt] >>
    `pure_vars (csubst closing (pure_walkstar sub (CVar f))) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> rpt CASE_TAC >> simp[SUBSET_DEF]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> rpt CASE_TAC >> simp[SUBSET_DEF]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> rpt CASE_TAC >> simp[SUBSET_DEF]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* True *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]
    )
  >- ( (* False *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]
    )
  >- ( (* Subscript *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]
    )
  >- ( (* Exception *)
    simp[Once type_tcexp_cases] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    `s ≠ "Subscript"` by gvs[pure_configTheory.reserved_cns_def] >> simp[] >>
    PairCases_on `ns` >> gvs[] >> simp[type_exception_def] >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[] >>
    gvs[MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS, satisfies_def, type_of_itype_of] >>
    gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Cons *)
    simp[Once type_tcexp_cases] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >>
    drule $ cj 2 type_of_SOME_lemma >> rw[] >>
    PairCases_on `ns` >> gvs[] >> simp[type_cons_def, PULL_EXISTS, oEL_THM] >>
    gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP] >> reverse $ rw[]
    >- (
      gvs[EVERY_EL] >> rw[] >> first_x_assum drule >> strip_tac >>
      imp_res_tac type_of_SOME >> simp[GSYM itype_ok_type_ok] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      irule itype_ok_pure_walkstar >> simp[itype_ok] >> gvs[itype_ok_def]
      ) >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[GSYM pure_walkstar_alt] >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
      )
    >- (
      gvs[MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS, satisfies_def] >>
      DEP_REWRITE_TAC[pure_walkstar_isubst] >> conj_tac >- gvs[itype_ok_def] >>
      simp[pure_walkstar_itype_of, pure_apply_subst_isubst_itype_of] >>
      drule $ cj 2 type_of_SOME_lemma >> rw[] >>
      imp_res_tac type_of_SOME_MAP >> pop_assum $ assume_tac o GSYM >>
      simp[isubst_itype_of, type_of_itype_of]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* AtomOp *)
    simp[Once type_tcexp_cases] >> disj2_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[GSYM pure_walkstar_alt] >>
    imp_res_tac infer_atom_op_LENGTH >> pop_assum $ assume_tac o GSYM >> gvs[] >>
    simp[GSYM infer_atom_op] >> goal_assum $ drule_at Any >> simp[get_PrimTys_SOME] >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MAP2_MAP, MEM_MAP, MEM_ZIP, PULL_EXISTS] >>
    rw[] >> last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> gvs[satisfies_def] >>
    simp[pure_walkstar_alt, pure_apply_subst, type_of_def] >> rw[GSYM pure_walkstar_alt]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF, MEM_EL, SF SFY_ss, PULL_EXISTS]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      goal_assum drule >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Seq *)
    simp[Once type_tcexp_cases] >>
    ntac 2 $ last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    `pure_vars (csubst closing (pure_walkstar sub it)) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      first_x_assum irule >> imp_res_tac minfer_pure_vars >>
      gvs[SUBSET_DEF, BIGUNION_FRANGE_maunion, new_vars_def, pure_vars] >>
      metis_tac[]) >>
    gvs[pure_vars_empty_eq_type_of] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    )
  >- ( (* App *)
    simp[Once type_tcexp_cases] >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_iFunctions, pure_apply_subst_iFunctions] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    irule_at Any $ cj 3 type_of_lemma >> simp[] >>
    `EVERY (λit. pure_vars it = {})
      (MAP (csubst closing) (MAP (pure_walkstar sub) tys))` by (
      rw[EVERY_MAP, EVERY_MEM] >> irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      rw[] >> first_x_assum irule >> simp[new_vars_def, pure_vars_iFunctions] >>
      simp[MEM_MAP, PULL_EXISTS, SF SFY_ss]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >> irule_at Any EQ_REFL >>
    `ts ≠ []` by (CCONTR_TAC >> gvs[]) >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      rw[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >>
      goal_assum drule >> simp[BIGUNION_FRANGE_maunion] >>
      imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      ) >>
    gvs[LIST_REL_EL_EQN, EL_ZIP, EL_MAP, MAP_EQ_EVERY2] >> rw[] >>
    last_x_assum drule >> strip_tac >> pop_assum irule >> conj_tac
    >- gvs[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
    rpt $ goal_assum $ drule_at Any >> rw[]
    >- (
      first_x_assum irule >> irule new_vars_SUBSET >>
      qexistsl_tac [`FOLDR maunion FEMPTY ass`,`BIGUNION (set css)`,`CVar f`] >>
      reverse $ conj_tac >- (simp[BIGUNION_FRANGE_maunion] >> simp[SUBSET_DEF]) >>
      irule new_vars_SUBSET_minfer >> goal_assum drule >>
      irule_at Any BIGUNION_FRANGE_FOLDR_maunion >> simp[EL_MEM] >>
      imp_res_tac minfer_pure_vars >>
      simp[SUBSET_DEF, MEM_EL, PULL_EXISTS, SF SFY_ss]
      )
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      rpt CASE_TAC >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    )
  >- ( (* Lam *)
    simp[Once type_tcexp_cases] >>
    gvs[pure_walkstar_iFunctions, pure_apply_subst_iFunctions] >>
    drule $ cj 3 type_of_SOME_lemma >> rw[] >>
    irule_at Any EQ_REFL >> simp[] >> rw[] >>
    imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >>
    `ts ≠ []` by (CCONTR_TAC >> gvs[]) >> rw[]
    >- (
      gvs[EVERY_EL, MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_MAP] >> rw[] >>
      first_x_assum drule >> strip_tac >>
      imp_res_tac type_of_SOME >> simp[GSYM itype_ok_type_ok] >>
      irule itype_ok_pure_apply_subst >> simp[] >>
      irule itype_ok_pure_walkstar >> simp[itype_ok] >> gvs[itype_ok_def]
      ) >>
    last_x_assum irule >> goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (xs, MAP ($, 0) (MAP CVar freshes))) ++ ictxt` >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP,
           FLOOKUP_FDIFF, MEM_MAP, GSYM DISJ_ASSOC, get_massumptions_def,
           MAP2_MAP, MEM_ZIP, pure_vars_iFunctions] >>
      reverse $ rw[] >> simp[SF SFY_ss] >>
      reverse $ Cases_on `MEM k xs` >> gvs[] >> simp[SF SFY_ss] >>
      pop_assum mp_tac >> simp[Once MEM_EL] >> strip_tac >> gvs[] >>
      ntac 3 disj2_tac >> disj1_tac >>
      rpt (goal_assum $ drule_at Any >> simp[])
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >>
      AP_THM_TAC >> AP_TERM_TAC >> simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt_def, ctxt_vars_def, msubst_vars_def] >>
      simp[MAP_REVERSE, ZIP_MAP] >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, MAP_ZIP_ALT] >>
      AP_TERM_TAC >> rw[Once EXTENSION] >>
      simp[MEM_MAP, MEM_ZIP, PULL_EXISTS, MEM_EL]
      )
    >- gvs[ZIP_MAP, EVERY_MAP, freedbvars_def]
    >- (
      gvs[MAP_EQ_EVERY2, LIST_REL_EL_EQN, EL_APPEND_EQN] >> rw[] >>
      simp[ZIP_MAP, GSYM MAP_REVERSE, EL_MAP, EL_REVERSE, EL_ZIP] >> gvs[EL_MAP]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> simp[ALOOKUP_APPEND] >> CASE_TAC
      >- (
        first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
        impl_tac >> rw[] >> gvs[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP]
        ) >>
      PairCases_on `x` >> simp[] >> rw[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
      gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP] >>
      first_x_assum $ drule_at Any >> simp[get_massumptions_def] >>
      disch_then drule >> simp[satisfies_def]
      )
    )
  >- ( (* Let *)
    rename [`Let _ (_ e1) (_ e2)`,
            `minfer _ _ e2 as2 cs2 it2`,`minfer _ _ e1 as1 cs1 it1`] >>
    simp[Once type_tcexp_cases] >>
    last_x_assum $ irule_at Any >> goal_assum $ drule_at Any >>
    `∃smonos : num_set. domain smonos = msubst_vars sub mset ∧ wf smonos` by (
      qexists_tac `list_to_num_set (SET_TO_LIST (msubst_vars sub mset))` >>
      simp[EXTENSION, domain_list_to_num_set, wf_list_to_num_set] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[msubst_vars_def, PULL_EXISTS]) >>
    qabbrev_tac `gen = generalise 0 smonos FEMPTY (pure_walkstar sub it1)` >>
    PairCases_on `gen` >> gvs[] >> rename1 `(new_dbvars,gen_sub,let_ity)` >>
    drule_all generalise_0_FEMPTY >> simp[] >> strip_tac >>
    `FDIFF gen_sub (msubst_vars sub mset) = gen_sub` by (
      rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
    gvs[] >>
    pop_assum kall_tac >>
    qmatch_asmsub_abbrev_tac `gen_vars,_,let_ity` >>
    `pure_vars (csubst (ishift gen_vars o_f closing) let_ity) = {}` by (
      irule pure_vars_csubst_EMPTY_suff >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
      unabbrev_all_tac >> irule SUBSET_TRANS >>
      irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, pure_vars] >>
      rw[IMAGE_K_EMPTY, DIFF_SUBSET] >>
      qsuff_tac `pure_vars (pure_walkstar sub it1) ⊆ FDOM closing` >- rw[SUBSET_DEF] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      first_x_assum irule >> irule new_vars_SUBSET_minfer >>
      qexistsl_tac [`as1`,`cs1`,`it1`] >> imp_res_tac minfer_pure_vars >>
      simp[BIGUNION_FRANGE_maunion] >> simp[SUBSET_DEF, new_vars_def]) >>
    pop_assum mp_tac >> simp[Once pure_vars_empty_eq_type_of] >> strip_tac >>
    rename1 `SOME let_ty` >>
    qexistsl_tac [`let_ty`,`gen_vars`,
      `FUNION (DBVar o_f gen_sub) (ishift gen_vars o_f closing)`] >>
    DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
    simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >>
      simp[FLOOKUP_maunion] >> rw[] >> CASE_TAC >> simp[]
      )
    >- (
      qsuff_tac `pure_vars (pure_walkstar sub (CVar n)) ⊆ FDOM closing`
      >- rw[SUBSET_DEF] >>
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      pop_assum mp_tac >> qid_spec_tac `it` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      pop_assum mp_tac >> qid_spec_tac `it` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, itype_ok, type_of_def] >>
      rw[] >> last_x_assum drule >> rw[] >>
      irule itype_ok_ishift >> simp[]
      )
    >- (
      gvs[LIST_REL_EL_EQN] >> rw[EL_MAP] >> ntac 3 (pairarg_tac >> gvs[]) >>
      first_x_assum drule >> simp[] >> PairCases_on `scheme` >> gvs[] >> rw[] >>
      simp[o_f_FUNION] >> DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      qabbrev_tac `wlkit = pure_walkstar sub it` >>
      `csubst ((ishift ivs o DBVar) o_f gen_sub) wlkit = wlkit` by (
        irule pure_apply_subst_unchanged >> rw[DISJOINT_ALT, DISJ_EQ_IMP] >>
        qpat_x_assum `msubst_vars _ _ = msubst_vars _ _` $ assume_tac o GSYM >>
        simp[GSYM ctxt_vars_subst_ctxt] >>
        simp[ctxt_vars_def, MEM_MAP, PULL_EXISTS, MEM_EL, EXISTS_PROD,
             subst_ctxt_def, EL_MAP] >>
        qpat_x_assum `_ ∈ pure_vars _` kall_tac >> unabbrev_all_tac >>
        rpt $ goal_assum drule >> simp[]) >>
      simp[] >> pop_assum kall_tac >>
      irule shift_shift_let_lemma >> simp[] >>
      unabbrev_all_tac >> irule SUBSET_TRANS >>
      irule_at Any freedbvars_pure_walkstar_SUBSET >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >>
      gvs[EVERY_EL, itype_ok_def] >> first_x_assum drule >> simp[]
      ) >>
    last_x_assum irule >> rpt $ goal_assum drule >> simp[] >>
    qexists_tac `(x,gen_vars,let_ity)::ictxt` >> simp[] >>
    `pure_walkstar sub let_ity = let_ity` by (
      unabbrev_all_tac >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]) >>
    simp[] >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP,
           FLOOKUP_maunion, DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC, get_massumptions_def] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `k = x` >> gvs[] >- metis_tac[] >>
      disj1_tac >> Cases_on `FLOOKUP as1 k`
      >- (qexistsl_tac [`s`,`k`] >> simp[])
      >- (qexistsl_tac [`x' ∪ s`,`k`] >> simp[])
      )
    >- (
      simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt, ctxt_vars] >> simp[ctxt_vars_subst_ctxt] >>
      irule SUBSET_ANTISYM >> simp[]
      )
    >- (
      unabbrev_all_tac >> irule SUBSET_TRANS >>
      irule_at Any freedbvars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      ) >>
    gvs[ctxt_rel_def] >> reverse $ rw[]
    >- (
      first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> gvs[] >> rw[] >> simp[]
      ) >>
    unabbrev_all_tac >>
    gvs[DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, PULL_EXISTS] >>
    gvs[get_massumptions_def, satisfies_def] >>
    last_x_assum drule >> strip_tac >> simp[] >>
    qabbrev_tac `wlkit1 = pure_walkstar sub it1` >>
    qspecl_then [`gen_sub`,`sub'`,`wlkit1`] mp_tac pure_apply_subst_split_isubst >>
    simp[] >> impl_tac >> rw[]
    >- (
      unabbrev_all_tac >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
      simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      ) >>
    goal_assum $ drule_at Any >> simp[EVERY_GENLIST] >> rw[]
    >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
    simp[pure_vars_pure_apply_subst] >>
    simp[SUBSET_DEF, pure_vars, PULL_EXISTS] >> rw[] >>
    goal_assum drule >> qsuff_tac `gm ' n' ∈ FDOM gen_sub` >- simp[] >>
    gvs[fmap_linv_alt_def, IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
    goal_assum drule >> simp[]
    )
  >- ( (* Letrec *)
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP] >>
    simp[Once type_tcexp_cases] >> `fns ≠ []` by (CCONTR_TAC >> gvs[]) >> simp[] >>
    last_x_assum $ irule_at Any >> goal_assum $ drule_at Any >> simp[] >>
    `∃smonos : num_set. domain smonos = msubst_vars sub mset ∧ wf smonos` by (
      qexists_tac `list_to_num_set (SET_TO_LIST (msubst_vars sub mset))` >>
      simp[EXTENSION, domain_list_to_num_set, wf_list_to_num_set] >>
      DEP_REWRITE_TAC[MEM_SET_TO_LIST] >> simp[msubst_vars_def, PULL_EXISTS]) >>
    qabbrev_tac `gens =
      MAP (generalise 0 smonos FEMPTY) (MAP (pure_walkstar sub) tys)` >>
    `LIST_REL (λ(new,sub,ty) t.
      CARD (FDOM sub) = new ∧ FDOM sub = pure_vars t DIFF domain smonos ∧
      FRANGE sub = count new ∧ pure_vars ty ⊆ domain smonos ∧
      csubst (DBVar o_f sub) t = ty)
      gens (MAP (pure_walkstar sub) tys)` by (
      unabbrev_all_tac >> rw[LIST_REL_EL_EQN, EL_MAP] >>
      pairarg_tac >> simp[] >> drule generalise_0_FEMPTY >> simp[] >> rw[] >>
      qsuff_tac `FDIFF sub' (msubst_vars sub mset) = sub'` >> rw[] >>
      rw[fmap_eq_flookup, FLOOKUP_FDIFF] >> rw[FLOOKUP_DEF] >> gvs[]) >>
    `EVERY (λit. pure_vars it = {}) $
      MAP (λ(new,gen_sub,ty). csubst (ishift new o_f closing) ty) gens` by (
      gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >> rw[] >> pairarg_tac >> gvs[] >>
      irule pure_vars_csubst_EMPTY_suff >> simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >>
      first_x_assum drule >> rw[] >>
      irule SUBSET_TRANS >> irule_at Any pure_vars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, pure_vars] >>
      rw[IMAGE_K_EMPTY, DIFF_SUBSET] >>
      qsuff_tac `pure_vars (pure_walkstar sub (EL n tys)) ⊆ FDOM closing`
      >- rw[SUBSET_DEF] >>
      simp[pure_vars_pure_walkstar_alt] >> rw[BIGUNION_SUBSET, PULL_EXISTS] >>
      first_x_assum irule >>
      simp[new_vars_def, MEM_MAP, MEM_EL, PULL_EXISTS, SF SFY_ss]) >>
    pop_assum mp_tac >> simp[Once pure_vars_empty_eq_type_of_MAP] >> strip_tac >>
    rename1 `MAP SOME fn_tys` >>
    qexists_tac `ZIP (MAP FST gens, fn_tys)` >>
    qexists_tac
      `REVERSE (ZIP (MAP FST fns, MAP (λ(vs,s,t). (vs,t)) gens)) ++ ictxt` >> simp[] >>
    imp_res_tac LIST_REL_LENGTH >> imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >>
    simp[AC (GSYM CONJ_ASSOC) CONJ_COMM] >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, MEM_MAP, MEM_ZIP] >> rw[] >> gvs[SF SFY_ss] >>
      gvs[IN_FRANGE_FLOOKUP, PULL_EXISTS, FLOOKUP_FDIFF, FLOOKUP_maunion] >>
      Cases_on `¬MEM k (MAP FST fns)` >> gvs[GSYM DISJ_ASSOC]
      >- (
        disj1_tac >> simp[Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> simp[] >> CASE_TAC >> simp[]
        ) >>
      ntac 4 disj2_tac >> disj1_tac >>
      pop_assum mp_tac >> simp[MEM_MAP, MEM_EL, EXISTS_PROD] >> rw[] >>
      pop_assum $ assume_tac o GSYM >> goal_assum $ drule_at Any >> simp[] >>
      simp[PULL_EXISTS, pure_vars, get_massumptions_def, FLOOKUP_maunion] >>
      qexists_tac `n` >> simp[] >> CASE_TAC >> simp[]
      )
    >- (
      drule type_of_SOME_MAP >> rw[] >>
      gvs[EVERY_EL, EL_ZIP, EL_MAP, LIST_REL_EL_EQN, MAP_EQ_EVERY2] >> rw[] >>
      simp[GSYM itype_ok_type_ok] >>
      ntac 3 (first_x_assum drule >> simp[] >> strip_tac) >>
      pairarg_tac >> gvs[] >>
      irule itype_ok_pure_apply_subst >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[]
      >- (irule itype_ok_ishift >> simp[]) >>
      irule itype_ok_pure_apply_subst >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS] >> rw[itype_ok] >>
      irule itype_ok_pure_walkstar >> rw[] >- gvs[itype_ok_def] >>
      last_x_assum drule >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[]
      >- (
        `¬MEM k (MAP FST fns)` by (
          pop_assum mp_tac >>
          simp[ALOOKUP_NONE, MEM_MAP, MEM_ZIP, PULL_EXISTS, EXISTS_PROD] >>
          simp[Once MONO_NOT_EQ] >> rw[MEM_EL] >> csimp[EL_MAP] >>
          goal_assum $ drule_at Any >> pop_assum $ assume_tac o GSYM >>
          simp[] >> pairarg_tac >> simp[]) >>
        first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
        qsuff_tac
         `∃v'. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) k = SOME v' ∧ v ⊆ v'`
        >- (strip_tac >> simp[] >> rw[] >> gvs[SUBSET_DEF]) >>
        simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
        ) >>
      PairCases_on `x` >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
      pairarg_tac >> gvs[] >> rw[] >>
      first_x_assum $ drule_at Any >>
      pairarg_tac >> simp[PULL_EXISTS] >>
      simp[get_massumptions_def, FLOOKUP_maunion] >> gvs[] >>
      disch_then $ qspec_then `n'` mp_tac >> impl_tac >- (CASE_TAC >> simp[]) >>
      simp[satisfies_def] >> rw[] >> simp[] >>
      gvs[LIST_REL_EL_EQN] >> first_x_assum drule >> simp[EL_MAP] >> rw[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      qabbrev_tac `wlk = pure_walkstar sub (EL n tys)` >>
      qspecl_then [`s`,`sub'`,`wlk`] mp_tac pure_apply_subst_split_isubst >>
      simp[] >> impl_tac >> rw[]
      >- (
        unabbrev_all_tac >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >>
        last_x_assum drule >> simp[EL_ZIP] >> strip_tac >>
        imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
        ) >>
      goal_assum $ drule_at Any >> simp[EVERY_GENLIST] >> rw[]
      >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
      simp[pure_vars_pure_apply_subst] >>
      simp[SUBSET_DEF, pure_vars, PULL_EXISTS] >> rw[] >>
      goal_assum drule >> qsuff_tac `gm ' n'' ∈ FDOM s` >- simp[] >>
      gvs[fmap_linv_alt_def, IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
      goal_assum drule >> simp[]
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >> irule SUBSET_ANTISYM >> simp[] >>
      simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt_def, ctxt_vars_def,
           ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS, MEM_MAP, MEM_ZIP] >> rw[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[] >> rw[] >>
      pairarg_tac >> gvs[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      gvs[EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[] >> strip_tac >>
      pop_assum $ assume_tac o GSYM >> simp[] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
      reverse conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >> reverse conj_tac >- gvs[itype_ok_def] >>
      last_x_assum drule >> simp[EL_ZIP] >> pairarg_tac >> simp[] >> strip_tac >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      )
    >- (
      gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP] >> rw[] >>
      simp[EL_APPEND_EQN] >> CASE_TAC >> gvs[] >>
      simp[EL_REVERSE, EL_ZIP, EL_MAP, LAMBDA_PROD] >>
      qmatch_goalsub_abbrev_tac `EL m` >>
      `m < LENGTH fn_tys` by (unabbrev_all_tac >> gvs[]) >>
      rpt (pairarg_tac >> gvs[]) >>
      first_x_assum drule >> simp[] >>
      qsuff_tac `pure_walkstar sub it' = it'` >> rw[] >>
      first_x_assum drule >> simp[] >>
      rw[] >> DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      ) >>
    gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    last_assum drule >> asm_rewrite_tac[] >> simp[] >>
    strip_tac >> pop_assum irule >> conj_tac
    >- (
      rw[] >> qpat_x_assum `∀c s. _ ∧ MEM _ __ ⇒ _` irule >>
      goal_assum $ drule_at Any >> simp[EL_MEM]
      ) >>
    first_assum drule >> pairarg_tac >> asm_rewrite_tac[] >> rw[] >>
    qpat_assum `∀n. n < _ ⇒ _ (pure_walkstar _ _)` drule >>
    asm_rewrite_tac[] >> simp[] >> strip_tac >> gvs[] >>
    qmatch_asmsub_abbrev_tac `EL n gens = (new,gen_sub,ty)` >>
    qexists_tac `FUNION (DBVar o_f gen_sub) (ishift new o_f closing)` >>
    qexists_tac `REVERSE (ZIP (MAP FST fns, MAP (λ(vs,s,t). (vs,t)) gens)) ++ ictxt` >>
    simp[] >> rw[]
    >- (
      pop_assum mp_tac >> qid_spec_tac `it'` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      pop_assum mp_tac >> qid_spec_tac `it'` >>
      ho_match_mp_tac IN_FRANGE_FUNION_suff >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, itype_ok] >> rw[] >>
      irule itype_ok_ishift >> gvs[itype_ok_def]
      )
    >- (
      simp[EL_APPEND_EQN] >> reverse $ rw[] >> simp[EL_MAP, EL_REVERSE, EL_ZIP]
      >- (
        qmatch_goalsub_abbrev_tac `EL m`  >>
        `m < LENGTH ictxt` by (unabbrev_all_tac >> gvs[]) >>
        rpt (pairarg_tac >> gvs[]) >>
        qpat_x_assum `∀n. _ < LENGTH ictxt ⇒ _` $ qspec_then `m` mp_tac >> rw[] >>
        simp[o_f_FUNION] >> DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, ishift_def, pure_vars] >>
        `csubst ((ishift ivs o DBVar) o_f gen_sub) (pure_walkstar sub it') =
          pure_walkstar sub it'` by (
          irule pure_apply_subst_unchanged >> simp[] >> rw[DISJOINT_ALT] >>
          disj2_tac >> qpat_x_assum `msubst_vars _ _ = _` $ assume_tac o GSYM >>
          simp[GSYM ctxt_vars_subst_ctxt, subst_ctxt_def, ctxt_vars_def] >>
          simp[MEM_MAP, PULL_EXISTS, EXISTS_PROD, MEM_EL] >>
          goal_assum drule >> goal_assum $ drule_at Any o GSYM >> simp[]) >>
        pop_assum SUBST_ALL_TAC >> irule shift_shift_let_lemma >> simp[] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[BIGUNION_SUBSET, PULL_EXISTS] >> gvs[EVERY_EL, itype_ok_def] >>
        qpat_x_assum `∀n. n < LENGTH ictxt ⇒ _` $ qspec_then `m` mp_tac >> simp[]
        )
      >- (
        qmatch_goalsub_abbrev_tac `EL m`  >>
        `m < LENGTH fn_tys` by (unabbrev_all_tac >> gvs[]) >>
        rpt (pairarg_tac >> gvs[]) >>
        first_x_assum drule >> rw[] >> first_x_assum drule >> rw[] >>
        DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
        qmatch_goalsub_abbrev_tac `ishift new'` >>
        simp[o_f_FUNION] >> DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
        simp[GSYM IMAGE_FRANGE, PULL_EXISTS, ishift_def, pure_vars] >>
        `csubst ((ishift new' ∘ DBVar) o_f gen_sub) $
          csubst (DBVar o_f s) (pure_walkstar sub (EL m tys)) =
          csubst (DBVar o_f s) (pure_walkstar sub (EL m tys))` by (
          irule pure_apply_subst_unchanged >> rw[DISJOINT_ALT] >>
          disj2_tac >> pop_assum mp_tac >>
          simp[pure_vars_pure_apply_subst] >>
          csimp[PULL_EXISTS, pure_vars, pure_apply_subst, FLOOKUP_DEF] >>
          gen_tac >> CASE_TAC >> simp[pure_vars] >> rw[]) >>
        pop_assum $ SUBST_ALL_TAC >> irule shift_shift_let_lemma >> gvs[] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_apply_subst_SUBSET >>
        simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
        reverse conj_tac >- (rw[SUBSET_DEF] >> gvs[]) >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[] >> reverse conj_tac >- gvs[BIGUNION_SUBSET, PULL_EXISTS, itype_ok_def] >>
        last_x_assum drule >> simp[] >> strip_tac >>
        imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
        )
      )
    >- (
      qsuff_tac `pure_vars (pure_walkstar sub (CVar n')) ⊆ FDOM closing`
      >- rw[SUBSET_DEF] >>
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, MEM_MAP, MEM_ZIP, PULL_EXISTS, IN_FRANGE_FLOOKUP,
           FLOOKUP_FDIFF, FLOOKUP_maunion, GSYM DISJ_ASSOC, FORALL_PROD] >>
      reverse $ rw[]
      >- simp[MEM_EL, PULL_EXISTS, SF SFY_ss]
      >- simp[MEM_EL, PULL_EXISTS, SF SFY_ss] >>
      Cases_on `¬MEM k (MAP FST fns)` >> gvs[]
      >- (
        gvs[MEM_MAP, FORALL_PROD] >> disj1_tac >>
        simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
        qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY ass) k = SOME v ∧ s ⊆ v`
        >- (rw[] >> simp[] >> CASE_TAC >> gvs[SUBSET_DEF]) >>
        simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >>
        gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
        ) >>
      ntac 4 disj2_tac >> disj1_tac >>
      pop_assum mp_tac >> simp[MEM_MAP, EXISTS_PROD, MEM_EL] >> rw[] >>
      goal_assum $ drule_at Any >> pop_assum $ assume_tac o GSYM >>
      simp[get_massumptions_def, FLOOKUP_maunion, PULL_EXISTS, pure_vars] >>
      qexists_tac `n'` >> simp[] >>
      qsuff_tac `∃v. FLOOKUP (FOLDR maunion FEMPTY ass) k = SOME v ∧ s ⊆ v`
      >- (rw[] >> simp[] >> CASE_TAC >> gvs[SUBSET_DEF]) >>
      simp[FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
      qexists_tac `n` >> gvs[FLOOKUP_DEF, SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >> irule SUBSET_ANTISYM >> simp[] >>
      simp[GSYM ctxt_vars_subst_ctxt] >>
      simp[subst_ctxt_def, ctxt_vars_def,
           ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS, MEM_MAP, MEM_ZIP] >> rw[] >>
      pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
      gvs[LIST_REL_EL_EQN, EL_MAP] >> first_x_assum drule >> simp[] >> rw[] >>
      pairarg_tac >> gvs[] >>
      first_x_assum drule >> simp[] >> rw[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      DEP_REWRITE_TAC[GSYM pure_apply_subst_FUNION] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars]
      )
    >- (
      gvs[EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
      pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      first_x_assum drule >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[] >> rw[] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_apply_subst_SUBSET >>
      simp[GSYM IMAGE_FRANGE, IMAGE_IMAGE, combinTheory.o_DEF, freedbvars_def] >>
      reverse conj_tac >- simp[SUBSET_DEF, PULL_EXISTS] >>
      irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >> simp[] >>
      simp[BIGUNION_SUBSET, PULL_EXISTS] >> reverse conj_tac >- gvs[itype_ok_def] >>
      last_x_assum drule >> simp[EL_ZIP] >> pairarg_tac >> simp[] >> strip_tac >>
      imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> simp[ALOOKUP_APPEND] >> CASE_TAC >> gvs[]
      >- (
        `¬MEM k (MAP FST fns)` by (
          pop_assum mp_tac >>
          simp[ALOOKUP_NONE, MEM_MAP, MEM_ZIP, PULL_EXISTS, EXISTS_PROD] >>
          simp[Once MONO_NOT_EQ] >> rw[MEM_EL] >> csimp[EL_MAP] >>
          goal_assum $ drule_at Any >> pop_assum $ assume_tac o GSYM >>
          simp[] >> pairarg_tac >> simp[]) >>
        first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_FDIFF] >>
        qsuff_tac
         `∃v'. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) k = SOME v' ∧ v ⊆ v'`
        >- (strip_tac >> simp[] >> rw[] >> gvs[SUBSET_DEF]) >>
        simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
        IF_CASES_TAC >> gvs[]
        >- (first_x_assum $ qspec_then `n` assume_tac >> gvs[FLOOKUP_DEF])
        >- (CASE_TAC >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss])
        ) >>
      PairCases_on `x` >> gvs[] >>
      imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP] >>
      pairarg_tac >> gvs[] >> rw[] >>
      qabbrev_tac `n'_fns = EL n' fns` >> PairCases_on `n'_fns` >> gvs[] >>
      qpat_x_assum `∀c n. _ ⇒ satisifes _ _ _` $ drule_at Any >>
      simp[PULL_EXISTS, get_massumptions_def] >>
      `∃v'. FLOOKUP (maunion as' (FOLDR maunion FEMPTY ass)) n'_fns0 =
              SOME v' ∧ v ⊆ v'` by (
        simp[FLOOKUP_maunion, FLOOKUP_FOLDR_maunion, MEM_EL, PULL_EXISTS] >>
        IF_CASES_TAC >> gvs[]
        >- (first_x_assum $ qspec_then `n` assume_tac >> gvs[FLOOKUP_DEF]) >>
        CASE_TAC >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss]) >>
      simp[satisfies_def] >> disch_then $ qspec_then `n''` mp_tac >>
      impl_tac >- gvs[SUBSET_DEF] >> rw[] >>
      qpat_x_assum `∀n. _ ⇒ _ (pure_walkstar _ _)` drule >> rw[] >>
      DEP_REWRITE_TAC[pure_walkstar_pure_apply_subst_pure_walkstar] >>
      simp[GSYM IMAGE_FRANGE, PULL_EXISTS, pure_vars] >>
      qabbrev_tac `wlk = pure_walkstar sub (EL n' tys)` >>
      qspecl_then [`s`,`sub'`,`wlk`] mp_tac pure_apply_subst_split_isubst >>
      simp[] >> impl_tac >> rw[]
      >- (
        unabbrev_all_tac >> once_rewrite_tac[GSYM SUBSET_EMPTY] >>
        irule SUBSET_TRANS >> irule_at Any freedbvars_pure_walkstar_SUBSET >>
        simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >>
        last_x_assum drule >> simp[EL_ZIP] >> strip_tac >>
        imp_res_tac minfer_itype_ok >> gvs[itype_ok_def]
        ) >>
      goal_assum $ drule_at Any >> simp[EVERY_GENLIST] >> rw[]
      >- (irule itype_ok_pure_apply_subst >> simp[itype_ok]) >>
      rename1 `gm ' foo` >>
      simp[pure_vars_pure_apply_subst] >>
      simp[SUBSET_DEF, pure_vars, PULL_EXISTS] >> rw[] >>
      goal_assum drule >> qsuff_tac `gm ' foo ∈ FDOM s` >- simp[] >>
      gvs[fmap_linv_alt_def, IN_FRANGE_FLOOKUP, FLOOKUP_DEF] >>
      goal_assum drule >> simp[]
      )
    )
  >- ( (* BoolCase *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    gvs[GSYM pure_walkstar_alt] >>
    ntac 3 $ last_x_assum $ irule_at Any >>
    ntac 5 $ goal_assum $ drule_at Any >> simp[] >>
    qexistsl_tac [`(v,0,BoolTy)::ictxt`,`(v,0,BoolTy)::ictxt`] >> simp[] >>
    simp[freedbvars_def, pure_walkstar_alt, pure_apply_subst, type_of_def] >>
    simp[GSYM pure_walkstar_alt] >> simp[ctxt_vars, pure_vars] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      gvs[ctxt_rel_def, get_massumptions_def] >> rw[] >- simp[pure_walkstar_alt] >>
      first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP, FLOOKUP_maunion,
           DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC, get_massumptions_def] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `n = f` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `v = k` >> gvs[] >> simp[SF SFY_ss] >> disj1_tac >>
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      every_case_tac >> simp[]
      )
    >- (
      gvs[ctxt_rel_def, get_massumptions_def] >> rw[] >- simp[pure_walkstar_alt] >>
      first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, DOMSUB_FLOOKUP_THM] >>
      every_case_tac >> rw[] >> gvs[]
      )
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP, FLOOKUP_maunion,
           DOMSUB_FLOOKUP_THM, GSYM DISJ_ASSOC, get_massumptions_def] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `n = f` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `v = k` >> gvs[] >> simp[SF SFY_ss] >> disj1_tac >>
      simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      every_case_tac >> simp[]
      )
    )
  >- ( (* TupleCase *)
    simp[Once type_tcexp_cases] >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, LEFT_AND_OVER_OR, MAP2_MAP,
        MEM_MAP, MEM_ZIP, EL_MAP, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >> gvs[GSYM $ cj 9 pure_walkstar_alt] >>
    last_x_assum $ irule_at $ Pos hd >> rpt $ goal_assum $ drule_at Any >> simp[] >>
    irule_at Any $ cj 1 type_of_lemma >>
    `EVERY (λit. pure_vars it = {}) $
      MAP (csubst closing) $ MAP (pure_walkstar sub) $ MAP CVar freshes` by (
        rw[EVERY_MAP, EVERY_MEM] >> irule pure_vars_csubst_EMPTY_suff >> simp[] >>
        first_x_assum irule >> simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >> irule_at Any EQ_REFL >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- gvs[MAP_EQ_EVERY2] >>
    last_x_assum irule >> goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (pvars,MAP ($, 0) (MAP CVar freshes))) ++
                  (v,0,CVar f)::ictxt` >>
    simp[freedbvars_def, LIST_TO_SET_MAP, IMAGE_EQ_SING, PULL_EXISTS] >> rw[]
    >- (
      first_x_assum irule >> pop_assum mp_tac >>
      simp[new_vars_def, PULL_EXISTS, pure_vars, IN_FRANGE_FLOOKUP,
           FLOOKUP_maunion, FLOOKUP_FDIFF, GSYM DISJ_ASSOC, get_massumptions_def,
           MEM_MAP, MEM_ZIP, EL_MAP] >>
      rw[] >> simp[SF SFY_ss] >>
      Cases_on `n = f` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `v = k` >> gvs[] >> simp[SF SFY_ss] >>
      Cases_on `MEM k pvars`
      >- (
        gvs[MEM_EL] >> ntac 5 disj2_tac >> disj1_tac >>
        qexistsl_tac [`n'`,`n`] >> simp[]
        ) >>
      disj1_tac >> simp[Once SWAP_EXISTS_THM] >> qexists_tac `k` >> simp[] >>
      CASE_TAC >> simp[]
      )
    >- (
      simp[ctxt_vars, pure_vars, msubst_vars_UNION] >>
      simp[GSYM msubst_vars_UNION] >> AP_TERM_TAC >>
      once_rewrite_tac[INSERT_SING_UNION] >> rewrite_tac[UNION_ASSOC] >>
      AP_THM_TAC >> AP_TERM_TAC >> simp[Once UNION_COMM] >> AP_TERM_TAC >>
      simp[ctxt_vars_def, Once EXTENSION, MEM_MAP, MEM_ZIP,
           MEM_EL, PULL_EXISTS, EL_MAP, SF CONJ_ss, pure_vars] >>
      rw[] >> eq_tac >> rw[] >> goal_assum $ drule_at Any >> simp[]
      )
    >- (rw[EVERY_MEM, MEM_ZIP, MEM_MAP] >> simp[EL_MAP, freedbvars_def])
    >- (
      irule EVERY2_APPEND_suff >> simp[] >>
      simp[pure_apply_subst] >> irule_at Any $ cj 1 type_of_lemma >> simp[] >>
      gvs[LIST_REL_EL_EQN, MAP_EQ_EVERY2, EL_ZIP, EL_MAP]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_APPEND, get_massumptions_def] >>
      reverse $ TOP_CASE_TAC >> simp[]
      >- (
        PairCases_on `x` >> rw[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
        ) >>
      IF_CASES_TAC >> gvs[] >> first_x_assum $ qspec_then `k` mp_tac >>
      simp[FLOOKUP_maunion, FLOOKUP_FDIFF] >>
      gvs[ALOOKUP_NONE, MEM_MAP, MEM_ZIP, EL_MAP, PULL_EXISTS] >>
      IF_CASES_TAC >- gvs[MEM_EL] >> simp[] >>
      TOP_CASE_TAC >> gvs[] >> rw[] >> simp[]
      )
    )
  >- ( (* ExceptionCase *)
    simp[Once type_tcexp_cases] >> ntac 2 disj2_tac >> disj1_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MEM_MAP, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >> gvs[GSYM pure_walkstar_alt] >>
    PairCases_on `ns` >> gvs[] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    rw[type_of_def]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      imp_res_tac sortingTheory.PERM_LIST_TO_SET >> gvs[] >>
      qspec_then `FST` drule sortingTheory.PERM_MAP >> rw[] >>
      drule sortingTheory.PERM_LIST_TO_SET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
      )
    >- (imp_res_tac sortingTheory.PERM_LENGTH >> gvs[]) >>
    gvs[LIST_REL_EL_EQN, EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> simp[] >> strip_tac >> simp[] >>
    `c ≠ "Subscript"` by (
      qpat_x_assum `namespace_ok _` assume_tac >>
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      last_x_assum $ qspec_then `"Subscript"` mp_tac >>
      impl_tac >- simp[pure_configTheory.reserved_cns_def] >> strip_tac >>
      CCONTR_TAC >> gvs[] >> imp_res_tac ALOOKUP_MEM >> gvs[MEM_MAP]) >>
    simp[] >> rpt conj_asm1_tac
    >- (
      gvs[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, PULL_EXISTS, EXISTS_PROD, MEM_EL] >>
      metis_tac[]
      )
    >- (
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      qsuff_tac `MEM (c, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) ns0)`
      >- (
        rw[] >> gvs[MEM_MAP, EXISTS_PROD] >>
        rev_drule ALOOKUP_ALL_DISTINCT_MEM >> disch_then drule >> simp[]
        ) >>
      drule $ iffRL sortingTheory.PERM_MEM_EQ >>
      simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
      simp[Once MEM_EL, PULL_EXISTS] >> disch_then drule >> simp[]
      ) >>
    last_x_assum drule >> simp[] >> strip_tac >> pop_assum irule >> conj_tac
    >- (
      gvs[MEM_EL, PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[]
      ) >>
    goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (pvars,MAP ($, 0) (MAP itype_of schemes))) ++
                  (v,0,CVar f)::ictxt` >>
    qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >> simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then $ drule_at Any >>
    simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP,
         DISJ_IMP_THM, FORALL_AND_THM, satisfies_def, EL_MAP] >>
    strip_tac >> gvs[] >> rw[]
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >>
      reverse $ rw[] >- (Cases_on `n' - LENGTH pvars` >> gvs[freedbvars_def]) >>
      gvs[namespace_ok_def, EVERY_EL, freetyvars_ok_freedbvars] >>
      drule ALOOKUP_MEM >> simp[MEM_EL] >> strip_tac >> pop_assum $ assume_tac o GSYM >>
      last_x_assum drule >> simp[] >>
      disch_then $ qspec_then `PRE (LENGTH pvars − n')` mp_tac >>
      simp[GSYM itype_ok_type_ok, itype_ok_def]
      )
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >> rw[type_of_itype_of] >>
      Cases_on `n' - LENGTH pvars` >> gvs[pure_apply_subst, type_of_def]
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      simp[pure_vars, PULL_EXISTS, MEM_MAP, GSYM DISJ_ASSOC]
      >- (
        Cases_on `n` >> gvs[] >>
        ntac 4 disj2_tac >> disj1_tac >> irule_at Any OR_INTRO_THM2 >>
        goal_assum drule >> simp[EL] >> DEP_REWRITE_TAC[EL_MEM] >>
        gvs[namespace_ok_def] >> Cases_on `tys` >> gvs[]
        )
      >- (
        ntac 6 disj2_tac >> disj1_tac >>
        simp[MEM_EL, PULL_EXISTS] >> rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      Cases_on `k ∈ v INSERT set pvars` >> gvs[]
      >- (
        ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS, pure_vars] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        ntac 6 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP, EL_MAP, pure_vars] >>
        gvs[MEM_EL] >> qexists_tac `n''` >> simp[] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        rpt disj1_tac >> simp[PULL_EXISTS, Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> CASE_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum drule >> gvs[FLOOKUP_DEF]
          ) >>
        CASE_TAC >> simp[PULL_EXISTS, MEM_EL] >> gvs[]
        >- (rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        >- (disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        )
      )
    >- (
      simp[ctxt_vars, msubst_vars_UNION] >> simp[GSYM msubst_vars_UNION] >>
      AP_TERM_TAC >> simp[pure_vars, UNION_ASSOC] >>
      once_rewrite_tac[INSERT_SING_UNION] >> AP_THM_TAC >> AP_TERM_TAC >>
      simp[ctxt_vars_def, MAP_REVERSE, ZIP_MAP, MAP_MAP_o, combinTheory.o_DEF,
           LAMBDA_PROD, LIST_TO_SET_MAP] >>
      rw[Once EXTENSION, PULL_EXISTS, EXISTS_PROD]
      )
    >- (
      Cases_on `n` >> gvs[] >> simp[EL] >>
      qpat_x_assum `∀t. MEM _ _ ⇒ _` $ qspec_then `EL n' (TL tys)` mp_tac >>
      impl_tac >> rw[] >> gvs[] >> irule EL_MEM >> Cases_on `tys` >> gvs[]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_APPEND, get_massumptions_def] >>
      reverse $ TOP_CASE_TAC >> simp[]
      >- (
        PairCases_on `x` >> rw[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
        ) >>
      IF_CASES_TAC >> gvs[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_maunion] >>
      qsuff_tac
        `∃s. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME s ∧ v' ⊆ s`
      >- (strip_tac >> simp[] >> CASE_TAC >> rw[] >> gvs[SUBSET_DEF]) >>
      `¬ MEM k pvars` by (
        qpat_x_assum `ALOOKUP _ _ = _` mp_tac >>
        simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD, MEM_ZIP, EXISTS_PROD] >>
        rw[Once MONO_NOT_EQ, MEM_EL] >> irule_at Any EQ_REFL >> simp[EL_MAP]) >>
      simp[FLOOKUP_FOLDR_maunion] >> rw[MEM_EL, PULL_EXISTS]
      >- (goal_assum drule >> gvs[FLOOKUP_DEF]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
      rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]
      )
    )
  >- ( (* Case *)
    simp[Once type_tcexp_cases] >> rpt disj2_tac >>
    gvs[DISJ_IMP_THM, FORALL_AND_THM, PULL_EXISTS, MEM_MAP, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst] >> gvs[GSYM $ cj 9 pure_walkstar_alt] >>
    PairCases_on `ns` >> gvs[] >>
    last_x_assum $ irule_at Any >> rpt $ goal_assum $ drule_at Any >>
    qexists_tac `id` >> simp[] >>
    irule_at Any $ cj 2 type_of_lemma >>
    `EVERY (λit. pure_vars it = {}) $ MAP (csubst closing) $
      MAP (pure_walkstar sub) $ MAP CVar freshes` by (
      rw[EVERY_MEM, MEM_MAP] >> irule pure_vars_csubst_EMPTY_suff >> simp[] >>
      first_x_assum irule >> simp[new_vars_def, pure_vars, MEM_MAP, PULL_EXISTS]) >>
    gvs[pure_vars_empty_eq_type_of_MAP] >> irule_at Any EQ_REFL >>
    imp_res_tac $ cj 1 $ iffLR MAP_EQ_EVERY2 >> gvs[] >> rw[]
    >- (
      irule ctxt_rel_sub >> goal_assum $ drule_at Any >> rw[] >>
      simp[FLOOKUP_maunion] >> CASE_TAC >> simp[]
      )
    >- (
      first_x_assum irule >> irule new_vars_SUBSET_minfer >> goal_assum drule >>
      simp[BIGUNION_FRANGE_maunion] >> imp_res_tac minfer_pure_vars >> simp[SUBSET_DEF]
      )
    >- (
      imp_res_tac sortingTheory.PERM_LIST_TO_SET >> gvs[] >>
      qspec_then `FST` drule sortingTheory.PERM_MAP >> rw[] >>
      drule sortingTheory.PERM_LIST_TO_SET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD, FST_THM]
      )
    >- (imp_res_tac sortingTheory.PERM_LENGTH >> gvs[]) >>
    gvs[LIST_REL_EL_EQN, EVERY_EL, EL_ZIP, EL_MAP] >> rw[] >>
    pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
    first_x_assum drule >> simp[] >> strip_tac >> simp[] >> rpt conj_asm1_tac
    >- (
      gvs[namespace_ok_def, ALL_DISTINCT_APPEND] >>
      `MEM (c, LENGTH pvars) (MAP (λ(cn,ts). (cn, LENGTH ts)) cdefs)` by (
        drule $ iffRL sortingTheory.PERM_MEM_EQ >>
        simp[MEM_MAP, EXISTS_PROD, PULL_EXISTS, FORALL_PROD] >>
        disch_then irule >> simp[MEM_EL] >> goal_assum drule >> simp[]) >>
      gvs[MEM_MAP, EXISTS_PROD] >>
      drule_at (Pos last) ALOOKUP_ALL_DISTINCT_MEM >> impl_tac >> simp[] >>
      gvs[MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD] >>
      irule ALL_DISTINCT_FLAT_IMP >> goal_assum drule >>
      simp[MEM_MAP, EXISTS_PROD] >> irule_at Any EQ_REFL >> simp[MEM_EL] >>
      gvs[oEL_THM] >> goal_assum drule >> simp[]
      )
    >- (
      gvs[MEM_FLAT, MEM_MAP, DISJ_EQ_IMP, PULL_EXISTS, EXISTS_PROD, MEM_EL] >>
      metis_tac[]
      ) >>
    last_x_assum drule >> simp[] >> strip_tac >> pop_assum irule >> conj_tac
    >- (
      gvs[MEM_EL, PULL_EXISTS] >> rw[] >>
      first_x_assum irule >> goal_assum drule >> simp[]
      ) >>
    goal_assum $ drule_at Any >> simp[] >>
    qexists_tac `REVERSE (ZIP (pvars,MAP ($, 0)
      (MAP (isubst (MAP CVar freshes) o itype_of) schemes))) ++ (v,0,CVar f)::ictxt` >>
    qpat_x_assum `∀c s. _ ∧ _ ⇒ _` mp_tac >> simp[Once MEM_EL, PULL_EXISTS] >>
    disch_then $ drule_at Any >>
    simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP,
         DISJ_IMP_THM, FORALL_AND_THM, satisfies_def, EL_MAP] >>
    strip_tac >> gvs[] >> rw[]
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >>
      reverse $ rw[] >- (Cases_on `n' - LENGTH schemes` >> gvs[freedbvars_def]) >>
      gvs[namespace_ok_def, EVERY_EL, freetyvars_ok_freedbvars, oEL_THM] >>
      drule ALOOKUP_MEM >> simp[MEM_EL] >> strip_tac >> pop_assum $ assume_tac o GSYM >>
      last_x_assum kall_tac >> last_x_assum drule >> simp[] >>
      disch_then drule >> simp[] >>
      disch_then $ qspec_then `PRE (LENGTH schemes − n')` mp_tac >>
      rw[GSYM itype_ok_type_ok, itype_ok_def] >>
      irule freedbvars_isubst_EMPTY_suff >> simp[EVERY_MAP, freedbvars_def]
      )
    >- (
      simp[EL_APPEND_EQN, EL_REVERSE, EL_ZIP, EL_MAP] >> rw[type_of_itype_of]
      >- (
        DEP_REWRITE_TAC[pure_walkstar_isubst] >> conj_tac >- gvs[itype_ok_def] >>
        simp[pure_apply_subst_isubst_itype_of] >>
        drule_then (assume_tac o GSYM) type_of_SOME_MAP >>
        simp[isubst_itype_of, type_of_itype_of]
        )
      >- (
        Cases_on `n' - LENGTH schemes` >> gvs[pure_apply_subst] >>
        irule $ cj 2 type_of_lemma >> simp[]
        )
      )
    >- (
      first_x_assum irule >> reverse $ gvs[new_vars_def] >>
      simp[pure_vars, PULL_EXISTS, MEM_MAP, GSYM DISJ_ASSOC]
      >- (
        Cases_on `n` >> gvs[] >>
        ntac 5 disj2_tac >> disj1_tac >> irule_at Any OR_INTRO_THM2 >>
        goal_assum drule >> simp[EL] >> DEP_REWRITE_TAC[EL_MEM] >>
        gvs[namespace_ok_def] >> Cases_on `tys` >> gvs[]
        )
      >- (
        ntac 7 disj2_tac >> disj1_tac >>
        simp[MEM_EL, PULL_EXISTS] >> rpt $ goal_assum $ drule_at Any >> simp[]
        ) >>
      gvs[IN_FRANGE_FLOOKUP, FLOOKUP_maunion, FLOOKUP_FOLDR_maunion] >>
      Cases_on `k ∈ v INSERT set pvars` >> gvs[]
      >- (
        ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        rpt $ irule_at Any OR_INTRO_THM1 >> simp[PULL_EXISTS, pure_vars] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        ntac 7 disj2_tac >> disj1_tac >> simp[MEM_EL, PULL_EXISTS] >>
        goal_assum $ drule_at Any >> simp[PULL_EXISTS] >>
        irule_at Any OR_INTRO_THM1 >> irule_at Any OR_INTRO_THM2 >>
        simp[PULL_EXISTS, MAP2_MAP, MEM_MAP, MEM_ZIP, EL_MAP, pure_vars] >>
        gvs[MEM_EL] >> qexists_tac `n''` >> simp[] >>
        simp[get_massumptions_def] >> goal_assum drule >> simp[]
        )
      >- (
        rpt disj1_tac >> simp[PULL_EXISTS, Once SWAP_EXISTS_THM] >>
        qexists_tac `k` >> CASE_TAC >> gvs[]
        >- (
          irule FALSITY >> pop_assum mp_tac >> simp[MEM_EL, PULL_EXISTS] >>
          goal_assum drule >> gvs[FLOOKUP_DEF]
          ) >>
        CASE_TAC >> simp[PULL_EXISTS, MEM_EL] >> gvs[]
        >- (rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        >- (disj2_tac >> rpt $ goal_assum $ drule_at Any >> simp[FLOOKUP_FDIFF])
        )
      )
    >- (
      once_rewrite_tac[INSERT_SING_UNION] >> rewrite_tac[msubst_vars_UNION] >>
      simp[ctxt_vars, msubst_vars_UNION, pure_vars, UNION_ASSOC] >>
      AP_THM_TAC >> AP_TERM_TAC >>
      simp[msubst_vars_def, ctxt_vars_def, MAP_REVERSE, ZIP_MAP, MAP_MAP_o,
           combinTheory.o_DEF, LAMBDA_PROD, LIST_TO_SET_MAP, IMAGE_IMAGE,
           pure_vars] >>
      irule SUBSET_ANTISYM >> simp[] >>
      simp[SUBSET_DEF, PULL_EXISTS, MEM_ZIP] >> rw[] >>
      qspecl_then [`MAP CVar freshes`,`itype_of (EL n' schemes)`]
        mp_tac pure_vars_isubst_SUBSET >>
      simp[MAP_MAP_o, combinTheory.o_DEF, pure_vars, LIST_TO_SET_MAP,
           SUBSET_DEF, PULL_EXISTS] >>
      disch_then drule >> simp[SF SFY_ss]
      )
    >- (
      Cases_on `n` >> gvs[] >> simp[EL] >>
      qpat_x_assum `∀t. MEM _ _ ⇒ _` $ qspec_then `EL n' (TL tys)` mp_tac >>
      impl_tac >> rw[] >> gvs[] >> irule EL_MEM >> Cases_on `tys` >> gvs[]
      )
    >- (
      gvs[ctxt_rel_def] >> rw[] >> gvs[ALOOKUP_APPEND, get_massumptions_def] >>
      reverse $ TOP_CASE_TAC >> simp[]
      >- (
        PairCases_on `x` >> rw[] >>
        imp_res_tac ALOOKUP_MEM >> gvs[MEM_ZIP, MEM_MAP, EL_MAP]
        ) >>
      IF_CASES_TAC >> gvs[] >>
      first_x_assum $ qspec_then `k` mp_tac >> simp[FLOOKUP_maunion] >>
      qsuff_tac
        `∃s. FLOOKUP (FOLDR maunion FEMPTY final_as) k = SOME s ∧ v' ⊆ s`
      >- (strip_tac >> simp[] >> CASE_TAC >> rw[] >> gvs[SUBSET_DEF]) >>
      `¬ MEM k pvars` by (
        qpat_x_assum `ALOOKUP _ _ = _` mp_tac >>
        simp[ALOOKUP_NONE, MEM_MAP, FORALL_PROD, MEM_ZIP, EXISTS_PROD] >>
        rw[Once MONO_NOT_EQ, MEM_EL] >> irule_at Any EQ_REFL >> simp[EL_MAP]) >>
      simp[FLOOKUP_FOLDR_maunion] >> rw[MEM_EL, PULL_EXISTS]
      >- (goal_assum drule >> gvs[FLOOKUP_DEF]) >>
      simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
      rpt $ goal_assum drule >> simp[FLOOKUP_FDIFF]
      )
    )
QED

Theorem inference_constraints_sound:
  namespace_ok ns ∧ infer ns LN e 0 = SOME ((ty,as,cs), n) ∧
  null as ∧
  pure_wfs sub ∧
  (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ∧
  (∀c. c ∈ set (MAP to_mconstraint cs) ⇒ satisfies (SND ns) sub c)
  ⇒ ∃t. type_tcexp ns 0 [] [] (tcexp_of e) t
Proof
  rw[] >> irule_at Any inference_constraints_sound_lemma >> simp[] >>
  goal_assum drule >> simp[] >>
  drule infer_minfer >> rw[] >> goal_assum drule >> simp[] >>
  `mas = FEMPTY` by (
    gvs[assumptions_rel_def] >>
    Cases_on `as` >> gvs[null_def] >>
    Cases_on `b` >> gvs[balanced_mapTheory.null_def] >>
    gvs[lookup_def, balanced_mapTheory.lookup_def] >> rw[fmap_eq_flookup]) >>
  gvs[] >> simp[ctxt_rel_def, ctxt_vars_def, msubst_vars_def] >>
  qabbrev_tac `vs = BIGUNION $ IMAGE (pure_vars o pure_walkstar sub o CVar) $
    pure_vars ty ∪
      BIGUNION (IMAGE new_vars_constraint (set (MAP to_mconstraint cs)))` >>
  qabbrev_tac `close = FUN_FMAP (K Unit) vs` >>
  `FINITE vs` by (
    unabbrev_all_tac >> simp[PULL_EXISTS, MEM_MAP] >>
    irule IMAGE_FINITE >> simp[PULL_EXISTS, MEM_MAP] >>
    Cases >> simp[] >> Cases_on `p` >> simp[]) >>
  `pure_vars (csubst close (pure_walkstar sub ty)) = {}` by (
    simp[pure_vars_pure_apply_subst] >> simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >> rw[] >>
    unabbrev_all_tac >> simp[pure_apply_subst, FLOOKUP_FUN_FMAP] >>
    simp[MEM_MAP, PULL_EXISTS] >> CASE_TAC >> simp[pure_vars] >>
    ntac 2 $ pop_assum mp_tac >> simp[] >>
    simp[Once pure_vars_pure_walkstar_alt] >> rw[] >> goal_assum drule >> simp[]) >>
  gvs[pure_vars_empty_eq_type_of] >> goal_assum $ drule_at Any >> reverse conj_tac
  >- (
    unabbrev_all_tac >> simp[PULL_EXISTS, MEM_MAP] >>
    rw[] >> simp[type_of_def, itype_ok]
    ) >>
  rw[new_vars_def] >> unabbrev_all_tac >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
QED

Theorem inference_constraints_safe_itree:
  namespace_ok ns ∧ infer ns LN e 0 = SOME ((ty,as,cs), n) ∧
  null as ∧
  pure_wfs sub ∧
  (∀it. it ∈ FRANGE sub ⇒ itype_ok (SND ns) 0 it) ∧
  (∀c. c ∈ set (MAP to_mconstraint cs) ∨ c = mUnify ty (M any)
    ⇒ satisfies (SND ns) sub c)
  ⇒ safe_itree (itree_of (exp_of e))
Proof
  rw[] >> irule type_soundness_cexp >> goal_assum drule >> qexists_tac `0` >>
  irule_at Any inference_constraints_sound_lemma >> simp[] >>
  goal_assum drule >> simp[] >>
  drule infer_minfer >> rw[] >> goal_assum drule >> simp[] >>
  `mas = FEMPTY` by (
    gvs[assumptions_rel_def] >>
    Cases_on `as` >> gvs[null_def] >>
    Cases_on `b` >> gvs[balanced_mapTheory.null_def] >>
    gvs[lookup_def, balanced_mapTheory.lookup_def] >> rw[fmap_eq_flookup]) >>
  gvs[] >> simp[ctxt_rel_def, ctxt_vars_def, msubst_vars_def] >>
  qabbrev_tac `vs = BIGUNION $ IMAGE (pure_vars o pure_walkstar sub o CVar) $
    pure_vars ty ∪
      BIGUNION (IMAGE new_vars_constraint (set (MAP to_mconstraint cs)))` >>
  qabbrev_tac `close = FUN_FMAP (K Unit) vs` >>
  `FINITE vs` by (
    unabbrev_all_tac >> simp[PULL_EXISTS, MEM_MAP] >>
    irule IMAGE_FINITE >> simp[PULL_EXISTS, MEM_MAP] >>
    Cases >> simp[] >> Cases_on `p` >> simp[]) >>
  `pure_vars (csubst close (pure_walkstar sub ty)) = {}` by (
    simp[pure_vars_pure_apply_subst] >> simp[DISJ_EQ_IMP, IMAGE_EQ_SING] >> rw[] >>
    unabbrev_all_tac >> simp[pure_apply_subst, FLOOKUP_FUN_FMAP] >>
    simp[MEM_MAP, PULL_EXISTS] >> CASE_TAC >> simp[pure_vars] >>
    ntac 2 $ pop_assum mp_tac >> simp[] >>
    simp[Once pure_vars_pure_walkstar_alt] >> rw[] >> goal_assum drule >> simp[]) >>
  gvs[pure_vars_empty_eq_type_of] >>
  `∃t'. t = M t'` by (
    gvs[DISJ_IMP_THM, FORALL_AND_THM, satisfies_def] >>
    gvs[pure_walkstar_alt, pure_apply_subst, type_of_def]) >> gvs[] >>
  goal_assum $ drule_at Any >> reverse conj_tac
  >- (
    unabbrev_all_tac >> simp[PULL_EXISTS, MEM_MAP] >>
    rw[] >> simp[type_of_def, itype_ok]
    ) >>
  rw[new_vars_def] >> unabbrev_all_tac >> simp[SUBSET_DEF, PULL_EXISTS, SF SFY_ss]
QED


(****************************************)

val _ = export_theory();

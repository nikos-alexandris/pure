(* Relating the itree- and FFI state-based CakeML semantics *)
open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open optionTheory relationTheory pairTheory listTheory arithmeticTheory;
open lem_pervasives_extraTheory libTheory namespaceTheory astTheory
     ffiTheory semanticPrimitivesTheory smallStepTheory;
open io_treeTheory cakeml_semanticsTheory pure_miscTheory;

val _ = new_theory "cakeml_semanticsProof";

(* TODO use evaluatePropsTheory and semanticPrimitivesPropsTheory *)

(* Deliberately no `application_def` here *)
val smallstep_ss = simpLib.named_rewrites "smallstep_ss" [
    smallStepTheory.continue_def,
    smallStepTheory.return_def,
    smallStepTheory.push_def,
    smallStepTheory.e_step_def
    ];

val itree_ss = simpLib.named_rewrites "itree_ss" [
    cakeml_semanticsTheory.continue_def,
    cakeml_semanticsTheory.return_def,
    cakeml_semanticsTheory.push_def,
    cakeml_semanticsTheory.estep_def
    ];


(****************************************)
(* Copied from CakeML *)


Theorem cml_application_thm:
  ∀op env s vs c.
    application op env s vs c =
    if op = Opapp then
      case do_opapp vs of
      | NONE => Eabort Rtype_error
      | SOME (env,e) => Estep (env,s,Exp e,c)
    else
      case do_app s op vs of
      | NONE => Eabort Rtype_error
      | SOME (v1,Rval v') => return env v1 v' c
      | SOME (v1,Rerr (Rraise v)) => Estep (env,v1,Val v,(Craise (),env)::c)
      | SOME (v1,Rerr (Rabort a)) => Eabort a
Proof
  rw[smallStepTheory.application_def] >> every_case_tac >> gvs[]
QED


(****************************************)
(* Adapt CakeML's RTC definitions to our more functional definitions *)


Definition step_n_cml_def:
  step_n_cml 0 e = e ∧
  step_n_cml (SUC n) (Estep st) = step_n_cml n (e_step st) ∧
  step_n_cml _ e = e
End

Theorem step_n_same[simp]:
  ∀n.
    step_n n Edone = Edone ∧
    step_n n Etype_error = Etype_error ∧
    step_n n (Effi s ws1 ws2 n env st cs) = (Effi s ws1 ws2 n env st cs) ∧
    step_n_cml n Estuck = Estuck ∧
    step_n_cml n (Eabort a) = Eabort a
Proof
  Cases >> rw[step_n_def, step_n_cml_def]
QED

Theorem step_n_cml_alt_def:
  step_n_cml 0 e = e ∧
  step_n_cml (SUC n) e = (
    case step_n_cml n e of
    | Estep st => e_step st
    | e => e)
Proof
  rw[step_n_cml_def] >>
  qid_spec_tac `e` >> qid_spec_tac `n` >>
  Induct >> Cases >> rewrite_tac[step_n_cml_def] >> simp[]
QED

Theorem step_n_cml_add:
  ∀a b. step_n_cml (a + b) e = step_n_cml a (step_n_cml b e)
Proof
  Induct >> rw[step_n_cml_def] >>
  simp[ADD_CLAUSES, step_n_cml_alt_def]
QED

Theorem e_step_reln_eq_step_n_cml:
  e_step_reln^* st1 st2 ⇔
  ∃n. step_n_cml n (Estep st1) = Estep st2
Proof
  reverse $ eq_tac >> rw[] >> pop_assum mp_tac
  >- (
    map_every qid_spec_tac [`st2`,`st1`,`n`] >>
    Induct >> rw[step_n_cml_alt_def] >>
    every_case_tac >> gvs[] >>
    rw[Once relationTheory.RTC_CASES2] >> disj2_tac >>
    last_x_assum $ irule_at Any >> gvs[e_step_reln_def]
    )
  >- (
    Induct_on `RTC e_step_reln` >> rw[]
    >- (qexists_tac `0` >> gvs[step_n_cml_def])
    >- (qexists_tac `SUC n` >> gvs[step_n_cml_def, e_step_reln_def])
    )
QED

Definition is_halt_cml_def:
  is_halt_cml (Estep (env, st_ffi, Val v, [])) = T ∧
  is_halt_cml (Estep (env, st_ffi, Val v, [Craise (), env'])) = T ∧
  is_halt_cml (Eabort a) = T ∧
  is_halt_cml _ = F
End

Definition step_to_halt_cml_def:
  step_to_halt_cml e =
    case some n. is_halt_cml (step_n_cml n e) of
    | NONE => NONE
    | SOME n => SOME $ step_n_cml n e
End

Theorem small_eval_eq_step_n_cml:
  (small_eval env st_ffi e cs (st_ffi', Rval v) ⇔
  ∃n env'.
    step_n_cml n (Estep (env, st_ffi, Exp e, cs)) =
      (Estep (env', st_ffi', Val v, []))) ∧
  (small_eval env st_ffi e cs (st_ffi', Rerr (Rraise v)) ⇔
  ∃n env' env''.
    step_n_cml n (Estep (env, st_ffi, Exp e, cs)) =
      (Estep (env', st_ffi', Val v, [(Craise (), env'')]))) ∧
  ((∃st_ffi'. small_eval env st_ffi e cs (st_ffi', Rerr (Rabort a))) ⇔
  ∃n env' env''.
    step_n_cml n (Estep (env, st_ffi, Exp e, cs)) = Eabort a)
Proof
  reverse $ rw[small_eval_def, e_step_reln_eq_step_n_cml]
  >- (
    eq_tac >> rw[]
    >- (qexists_tac `SUC n` >> gvs[step_n_cml_alt_def]) >>
    Induct_on `n` >> gvs[step_n_cml_alt_def] >>
    every_case_tac >> gvs[] >> rw[PULL_EXISTS] >>
    PairCases_on `p` >> goal_assum drule >> simp[]
    ) >>
  eq_tac >> rw[] >> ntac 2 $ goal_assum drule
QED

Triviality Estep_is_halt_imp_e_step_neq_Estep:
  is_halt_cml (Estep st) ⇒ ∀st'. e_step st ≠ Estep st'
Proof
  PairCases_on `st` >> rw[] >>
  Cases_on `st3` >> Cases_on `st4` >> gvs[is_halt_cml_def]
  >- simp[e_step_def, SF smallstep_ss] >>
  PairCases_on `h` >>
  Cases_on `h0` >> Cases_on `t` >> gvs[is_halt_cml_def] >>
  simp[e_step_def, SF smallstep_ss]
QED

Triviality Estep_is_halt_imp_step_n_neq_Estep:
  is_halt_cml st ⇒ ∀st'. step_n_cml (SUC n) st ≠ Estep st'
Proof
  Cases_on `st` >> gvs[is_halt_cml_def] >>
  PairCases_on `p` >>
  Cases_on `p3` >> gvs[is_halt_cml_def] >>
  Cases_on `p4` >> gvs[is_halt_cml_def]
  >- (gvs[step_n_cml_def, e_step_def, SF smallstep_ss, is_halt_cml_def]) >>
  PairCases_on `h` >> Cases_on `h0` >> gvs[is_halt_cml_def] >>
  Cases_on `t` >> gvs[is_halt_cml_def] >>
  gvs[step_n_cml_def, e_step_def, SF smallstep_ss, is_halt_cml_def]
QED

Theorem small_eval_eq_step_to_halt_cml:
  (small_eval env st_ffi e cs (st_ffi', Rval v) ⇔
  ∃env'.
    step_to_halt_cml (Estep (env, st_ffi, Exp e, cs)) =
      SOME (Estep (env', st_ffi', Val v, []))) ∧
  (small_eval env st_ffi e cs (st_ffi', Rerr (Rraise v)) ⇔
  ∃env' env''.
    step_to_halt_cml (Estep (env, st_ffi, Exp e, cs)) =
      SOME (Estep (env', st_ffi', Val v, [(Craise (), env'')]))) ∧
  ((∃st_ffi'. small_eval env st_ffi e cs (st_ffi', Rerr (Rabort a))) ⇔
  ∃env' env''.
    step_to_halt_cml (Estep (env, st_ffi, Exp e, cs)) = SOME (Eabort a))
Proof
  rw[small_eval_eq_step_n_cml, step_to_halt_cml_def] >> eq_tac >>
  DEEP_INTRO_TAC some_intro >> rw[] >> gvs[]
  >- (
    Cases_on `n < x` >> gvs[]
    >- (
      `step_n_cml (SUC n) (Estep (env,st_ffi,Exp e, cs)) = Estuck` by (
        simp[step_n_cml_alt_def, e_step_def, SF smallstep_ss]) >>
      `∃p. x = p + SUC n` by (
        imp_res_tac arithmeticTheory.LESS_STRONG_ADD >> gvs[ADD_CLAUSES]) >>
      gvs[step_n_cml_add, is_halt_cml_def]
      )
    >- (
      Cases_on `n = x` >> gvs[] >> `x < n` by gvs[] >>
      imp_res_tac arithmeticTheory.LESS_STRONG_ADD >>
      gvs[step_n_cml_add |> ONCE_REWRITE_RULE [Once ADD_COMM]] >>
      gvs[Estep_is_halt_imp_step_n_neq_Estep]
      )
    )
  >- (
    pop_assum $ qspec_then `n` assume_tac >>
    CCONTR_TAC >> gvs[is_halt_cml_def]
    )
  >- goal_assum drule
  >- (
    Cases_on `n < x` >> gvs[]
    >- (
      `step_n_cml (SUC n) (Estep (env,st_ffi,Exp e, cs)) = Estuck` by (
        simp[step_n_cml_alt_def, e_step_def, SF smallstep_ss]) >>
      `∃p. x = p + SUC n` by (
        imp_res_tac arithmeticTheory.LESS_STRONG_ADD >> gvs[ADD_CLAUSES]) >>
      gvs[step_n_cml_add, is_halt_cml_def]
      )
    >- (
      Cases_on `n = x` >> gvs[] >> `x < n` by gvs[] >>
      imp_res_tac arithmeticTheory.LESS_STRONG_ADD >>
      gvs[step_n_cml_add |> ONCE_REWRITE_RULE [Once ADD_COMM]] >>
      gvs[Estep_is_halt_imp_step_n_neq_Estep]
      )
    )
  >- (
    pop_assum $ qspec_then `n` assume_tac >>
    CCONTR_TAC >> gvs[is_halt_cml_def]
    )
  >- goal_assum drule
  >- (
    Cases_on `n < x` >> gvs[]
    >- (
      `step_n_cml (SUC n) (Estep (env,st_ffi,Exp e, cs)) = Eabort a` by (
        simp[step_n_cml_alt_def, e_step_def, SF smallstep_ss]) >>
      `∃p. x = p + SUC n` by (
        imp_res_tac arithmeticTheory.LESS_STRONG_ADD >> gvs[ADD_CLAUSES]) >>
      gvs[step_n_cml_add, is_halt_cml_def]
      )
    >- (
      Cases_on `n = x` >> gvs[] >> `x < n` by gvs[] >>
      imp_res_tac arithmeticTheory.LESS_STRONG_ADD >>
      gvs[step_n_cml_add |> ONCE_REWRITE_RULE [Once ADD_COMM]] >>
      Cases_on `step_n_cml x (Estep (env,st_ffi,Exp e,cs))` >> gvs[is_halt_cml_def] >>
      rename1 `_ $ Estep st` >> PairCases_on `st` >> gvs[step_n_cml_def] >>
      Cases_on `st3` >> gvs[is_halt_cml_def] >>
      Cases_on `st4` >> gvs[is_halt_cml_def, e_step_def, SF smallstep_ss] >>
      PairCases_on `h` >> Cases_on `h0` >> gvs[is_halt_cml_def] >>
      Cases_on `t` >> gvs[is_halt_cml_def]
      )
    )
  >- (
    pop_assum $ qspec_then `n` assume_tac >>
    CCONTR_TAC >> gvs[is_halt_cml_def]
    )
  >- goal_assum drule
QED

Theorem application_not_Estuck:
  application op env st_ffi vs cs ≠ Estuck
Proof
  rw[cml_application_thm] >>
  EVERY_CASE_TAC >> gvs[SF smallstep_ss]
QED

Theorem e_step_to_Estuck:
  e_step (env, st_ffi, ev, cs) = Estuck ⇔
  (∃v. ev = Val v ∧ cs = []) ∨
  (∃v env'. ev = Val v ∧ cs = [Craise (), env'])
Proof
  reverse $ eq_tac
  >- (rw[] >> gvs[SF smallstep_ss]) >>
  gvs[e_step_def] >> CASE_TAC >> gvs[]
  >- (every_case_tac >> gvs[SF smallstep_ss, application_not_Estuck]) >>
  Cases_on `cs` >> gvs[SF smallstep_ss] >>
  every_case_tac >> gvs[application_not_Estuck]
QED

Theorem e_diverges_eq_step_to_halt_cml:
  e_diverges env st_ffi e ⇔ step_to_halt_cml (Estep (env, st_ffi, Exp e, [])) = NONE
Proof
  rw[step_to_halt_cml_def, e_diverges_def, e_step_reln_eq_step_n_cml] >>
  simp[PULL_EXISTS] >>
  eq_tac >> rw[] >> gvs[e_step_reln_def]
  >- (
    DEEP_INTRO_TAC some_intro >> rw[] >>
    Induct_on `x` >> rw[] >> gvs[step_n_cml_alt_def, is_halt_cml_def] >>
    CASE_TAC >> gvs[is_halt_def] >>
    PairCases_on `p` >> rename1 `Estep (a, b, c, d)` >>
    last_assum drule >> strip_tac >> gvs[] >> rename1 `Estep (f, g, h, i)` >>
    last_x_assum $ qspecl_then [`f`,`g`,`h`,`i`,`SUC x`] assume_tac >>
    gvs[step_n_cml_alt_def] >>
    metis_tac[Estep_is_halt_imp_e_step_neq_Estep]
    )
  >- (
    last_x_assum mp_tac >>
    DEEP_INTRO_TAC some_intro >> rw[] >>
    first_assum $ qspec_then `n` assume_tac >>
    first_x_assum $ qspec_then `SUC n` assume_tac >> gvs[step_n_cml_alt_def] >>
    Cases_on `e_step (env', s', e', c')` >> gvs[is_halt_cml_def]
    >- (PairCases_on `p` >> simp[]) >>
    gvs[e_step_to_Estuck, is_halt_cml_def]
    )
QED


(****************************************)


Inductive result_rel:
  result_rel (Rval v) (Rval v) ∧
  result_rel (Rraise v) (Rerr $ Rraise v)
End

(* Takes 30s *)
Theorem do_app_rel:
  (∀s. op ≠ FFI s) ⇒
  OPTREL (λ(a,b) (c,d). a = c ∧ result_rel b d)
    (do_app st op vs)
    (OPTION_MAP (λ(a,b). (FST a, b)) (do_app (st, ffi) op vs))
Proof
  rw[semanticPrimitivesTheory.do_app_def] >>
  rpt (
    TOP_CASE_TAC >>
    gvs[do_app_def, result_rel_cases, store_alloc_def]
    )
QED

Inductive ctxt_frame_rel:
  ctxt_frame_rel Craise (Craise ()) ∧
  ctxt_frame_rel (Chandle pes) (Chandle () pes) ∧
  ctxt_frame_rel (Capp op vs es) (Capp op vs () es) ∧
  ctxt_frame_rel (Clog lop e) (Clog lop () e) ∧
  ctxt_frame_rel (Cif e1 e2) (Cif () e1 e2) ∧
  ctxt_frame_rel (Cmat_check pes v) (Cmat_check () pes v) ∧
  ctxt_frame_rel (Cmat pes v) (Cmat () pes v) ∧
  ctxt_frame_rel (Clet vopt e) (Clet vopt () e) ∧
  ctxt_frame_rel (Ccon idopt vs es) (Ccon idopt vs () es) ∧
  ctxt_frame_rel (Ctannot ty) (Ctannot () ty) ∧
  ctxt_frame_rel (Clannot ls) (Clannot () ls)
End

Definition ctxt_rel_def:
  ctxt_rel cs1 cs2 =
    LIST_REL (λ(c1,env1) (c2,env2). ctxt_frame_rel c1 c2 ∧ env1 = env2) cs1 cs2
End

Inductive step_result_rel:
  (ctxt_rel cs1 cs2 ⇒
    step_result_rel (Estep (env, st, ev, cs1)) (Estep (env, (st, ffi), ev, cs2))) ∧
  step_result_rel Edone Estuck ∧
  step_result_rel Etype_error (Eabort $ Rtype_error)
End

(* Takes 20s *)
Theorem application_rel:
  (∀s. op ≠ FFI s) ∧
  ctxt_rel cs1 cs2 ⇒
  step_result_rel
    (application op env st vs cs1)
    (application op env (st,ffi) vs cs2)
Proof
  rw[] >>
  drule do_app_rel >> disch_then $ qspecl_then [`vs`,`st`,`ffi`] assume_tac >>
  rw[application_def, cml_application_thm]
  >- (CASE_TAC >> gvs[step_result_rel_cases] >> CASE_TAC >> gvs[]) >>
  Cases_on `do_app (st,ffi) op vs` >> gvs[] >>
  Cases_on `do_app st op vs` >> gvs[]
  >- (rpt (TOP_CASE_TAC >> gvs[step_result_rel_cases])) >>
  gvs[FST_THM] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[result_rel_cases] >>
  rpt (
    TOP_CASE_TAC >>
    gvs[step_result_rel_cases, SF smallstep_ss, SF itree_ss,
        ctxt_rel_def, ctxt_frame_rel_cases]
    )
QED

Triviality application_FFI_results:
  (application (FFI s) env st vs cs = Etype_error) ∨
  (application (FFI s) env st vs cs = Estep (env, st, Val $ Conv NONE [], cs)) ∨
  ∃conf ws lnum.
    (application (FFI s) env st vs cs) = Effi s conf ws lnum env st cs
Proof
  rw[application_def] >> every_case_tac >> gvs[]
QED

Theorem application_rel_FFI_type_error:
  application (FFI s) env st vs cs1 = Etype_error ⇔
  application (FFI s) env (st, ffi) vs cs2 = Eabort Rtype_error
Proof
  rw[application_def, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[store_lookup_def, store_assign_def, store_v_same_type_def]
QED

Theorem application_rel_FFI_step:
  application (FFI s) env st vs cs1 = Estep (env, st, Val v, cs1) ⇔
  application (FFI s) env (st, ffi) vs cs2 = Estep (env, (st,ffi), Val v, cs2)
Proof
  rw[application_def, cml_application_thm] >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[SF smallstep_ss] >>
  gvs[call_FFI_def, store_lookup_def, store_assign_def, store_v_same_type_def]
  >- (eq_tac >> rw[] >> metis_tac[LUPDATE_SAME]) >>
  every_case_tac >> gvs[] >> rw[] >> gvs[ffi_state_component_equality]
QED

Triviality application_eq_Effi_fields:
  application op env st vs cs = Effi s conf ws lnum env' st' cs' ⇒
  op = FFI s ∧ env = env' ∧ st = st' ∧ cs' = cs ∧
  ∃conf'.
    vs = [Litv $ StrLit conf'; Loc lnum] ∧
    conf = MAP (λc. n2w $ ORD c) (EXPLODE conf')
Proof
  Cases_on `op` >> simp[application_def, SF itree_ss] >>
  every_case_tac >> gvs[] >> rw[]
QED

Theorem application_rel_FFI:
  application (FFI s) env st vs cs1 = Effi s conf ws lnum env st cs1 ⇒
    store_lookup lnum st = SOME $ W8array ws ∧
    application (FFI s) env (st, ffi) vs cs2 =
      case ffi.oracle s ffi.ffi_state conf ws of
      | Oracle_return ffi' ws' =>
          if LENGTH ws' ≠ LENGTH ws then
            Eabort $ Rffi_error $ Final_event s conf ws FFI_failed
          else
            Estep (env,
              (LUPDATE (W8array ws') lnum st,
               ffi with <|
                  ffi_state := ffi';
                  io_events := ffi.io_events ++ [IO_event s conf (ZIP (ws,ws'))]
                  |>),
              Val $ Conv NONE [], cs2)
      | Oracle_final outcome =>
          Eabort $ Rffi_error $ Final_event s conf ws outcome
Proof
  simp[application_def] >>
  ntac 6 (TOP_CASE_TAC >> gvs[]) >>
  gvs[store_lookup_def] >>
  ntac 2 (TOP_CASE_TAC >> gvs[]) >> rw[] >> gvs[] >>
  simp[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def] >>
  simp[store_lookup_def, call_FFI_def] >>
  qmatch_goalsub_abbrev_tac `foo l` >>
  reverse $ Cases_on `foo l` >> gvs[] >>
  IF_CASES_TAC >> gvs[store_assign_def, store_v_same_type_def, SF smallstep_ss]
QED

Theorem application_rel_FFI':
  application (FFI s) env (st, ffi) vs cs2 ≠ Eabort Rtype_error ⇒
  (∃conf lnum ws.
    vs = [Litv $ StrLit conf; Loc lnum] ∧
    store_lookup lnum st = SOME $ W8array ws ∧
    application (FFI s) env st vs cs1 =
      Effi s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws lnum env st cs1) ∨
  (s = "" ∧
  application (FFI s) env st vs cs1 = Estep (env, st, Val $ Conv NONE [], cs1))
Proof
  rw[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[application_def] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem do_app_ffi_changed:
  do_app (st, ffi) op vs = SOME ((st', ffi'), res) ∧
  ffi ≠ ffi' ⇒
  ∃s conf lnum ws ffi_st ws'.
    op = FFI s ∧
    vs = [Litv (StrLit conf); Loc lnum] ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ "" ∧
    ffi.oracle s ffi.ffi_state (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws =
      Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws' ∧
    st' = LUPDATE (W8array ws') lnum st ∧
    ffi'.oracle = ffi.oracle ∧
    ffi'.ffi_state = ffi_st ∧
    ffi'.io_events =
      ffi.io_events ++
        [IO_event s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) (ZIP (ws,ws'))]
Proof
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[store_alloc_def, store_assign_def] >>
  strip_tac >> gvs[call_FFI_def] >>
  every_case_tac >> gvs[]
QED

Theorem do_app_ffi_unchanged:
  ∀st ffi op vs st' ffi' res.
    (∀s. op ≠ FFI s) ∧
    do_app (st, ffi) op vs = SOME ((st', ffi'), res)
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >>
  simp[semanticPrimitivesTheory.do_app_def] >>
  every_case_tac >> gvs[store_alloc_def]
QED

Theorem application_ffi_unchanged:
  ∀op env st ffi vs cs env' st' ffi' ev cs'.
    (∀s. op ≠ FFI s) ∧
    application op env (st, ffi) vs cs = Estep (env', (st', ffi'), ev, cs')
  ⇒ ffi = ffi'
Proof
  rpt gen_tac >>
  rw[cml_application_thm, SF smallstep_ss]
  >- (every_case_tac >> gvs[]) >>
  qspecl_then [`st`,`ffi`,`op`,`vs`] assume_tac do_app_ffi_unchanged >>
  every_case_tac >> gvs[]
QED

Theorem e_step_ffi_changed:
  e_step (env, (st, ffi), ev, cs) = Estep (env', (st', ffi'), ev', cs') ∧
  ffi ≠ ffi' ⇒
  ∃ s conf lnum ccs ws ffi_st ws'.
    ev = Val (Litv (StrLit conf)) ∧
    cs = (Capp (FFI s) [Loc lnum] () [], env') :: ccs ∧
    store_lookup lnum st = SOME (W8array ws) ∧
    s ≠ "" ∧
    ffi.oracle s ffi.ffi_state (MAP (λc. n2w $ ORD c) (EXPLODE conf)) ws =
      Oracle_return ffi_st ws' ∧
    LENGTH ws = LENGTH ws' ∧
    ev' = Val (Conv NONE []) ∧
    cs' = ccs ∧
    st' = LUPDATE (W8array ws') lnum st ∧
    ffi'.oracle = ffi.oracle ∧
    ffi'.ffi_state = ffi_st ∧
    ffi'.io_events =
      ffi.io_events ++
        [IO_event s (MAP (λc. n2w $ ORD c) (EXPLODE conf)) (ZIP (ws,ws'))]
Proof
  simp[e_step_def] >>
  every_case_tac >> gvs[SF smallstep_ss]
  >- (
    strip_tac >> rename1 `application op _ _ _ _` >>
    Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (irule application_ffi_unchanged >> rpt $ goal_assum drule) >>
    gvs[smallStepTheory.application_def, semanticPrimitivesTheory.do_app_def]
    ) >>
  every_case_tac >> gvs[] >>
  rename1 `application op _ _ _ _` >>
  (
    strip_tac >> Cases_on `∀s. op ≠ FFI s` >> gvs[]
    >- (drule_all application_ffi_unchanged >> gvs[]) >>
    gvs[smallStepTheory.application_def,
        semanticPrimitivesTheory.do_app_def, call_FFI_def] >>
    every_case_tac >> gvs[SF smallstep_ss, store_lookup_def, store_assign_def]
  )
QED


(****************************************)


(* Play out a particular trace prefix from a given itree, modelling the
   environment as an FFI oracle with associated FFI state (as in CakeML) *)
Definition trace_prefix_def:
  trace_prefix 0 (oracle, st) itree = ([], NONE) ∧
  trace_prefix (SUC n) (oracle, st) (Ret r) = ([], SOME r) ∧
  trace_prefix (SUC n) (oracle, st) (Vis (s, conf, ws) f) =
    case oracle s st conf ws of
    | Oracle_return st' ws' =>
        let (io, res) = trace_prefix n (oracle, st) (f $ INR ws') in
        (IO_event s conf (ZIP (ws,ws'))::io, res)
    | Oracle_final outcome => trace_prefix n (oracle, st) (f $ INL outcome)
End

Definition is_Effi_def:
  is_Effi (Effi _ _ _ _ _ _ _) = T ∧
  is_Effi _ = F
End

Theorem is_Effi_def:
  is_Effi e ⇔ ∃ s ws1 ws2 n env st cs. e = Effi s ws1 ws2 n env st cs
Proof
  Cases_on `e` >> simp[is_Effi_def]
QED

Definition get_ffi_def:
  get_ffi (Estep (env, (st, ffi), ev, cs)) = SOME ffi ∧
  get_ffi _ = NONE
End

Theorem step_result_rel_single:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    ¬ is_Effi (estep ea)
  ⇒ step_result_rel (estep ea) (e_step eb) ∧
    ∀ffi. get_ffi (e_step eb) = SOME ffi ⇒ get_ffi (Estep eb) = SOME ffi
Proof
  rpt PairCases >> rename1 `_ (_ (env,st,ev,cs1)) (_ (env',(st',ffi),ev',cs2))` >>
  gvs[e_step_def] >>
  every_case_tac >> gvs[estep_def, step_result_rel_cases] >> strip_tac >>
  gvs[SF smallstep_ss, SF itree_ss, ctxt_rel_def, ctxt_frame_rel_cases, get_ffi_def] >>
  gvs[GSYM ctxt_frame_rel_cases, GSYM step_result_rel_cases]
  >- (
    rename1 `application op _ _ _ _` >>
    reverse $ Cases_on `∃s. op = FFI s` >> gvs[]
    >- (
      reverse $ rw[]
      >- (
        drule application_ffi_unchanged >>
        Cases_on `application op env (st,ffi) [] cs2` >> gvs[get_ffi_def] >>
        PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
        )
      >- (
        drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
        disch_then $ qspecl_then [`[]`,`st`,`ffi`,`env`] assume_tac >>
        gvs[step_result_rel_cases, ctxt_rel_def]
        )
      ) >>
    qspecl_then [`[]`,`st`,`s`,`env`,`cs1`]
      assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
    csimp[] >> gvs[is_Effi_def, get_ffi_def]
    >- metis_tac[application_rel_FFI_type_error] >>
    imp_res_tac application_rel_FFI_step >> simp[get_ffi_def]
    )
  >- gvs[FST_THM, LAMBDA_PROD]
  >- gvs[FST_THM, LAMBDA_PROD] >>
  CASE_TAC >- gvs[continue_def, get_ffi_def] >>
  PairCases_on `h` >> gvs[] >> PairCases_on `x` >> gvs[] >>
  rename1 `ctxt_frame_rel c1 c2` >> rename1 `(c1,env)` >>
  rename1 `LIST_REL _ rest1 rest2` >>
  Cases_on `c1` >> gvs[SF itree_ss, ctxt_frame_rel_cases] >>
  gvs[GSYM ctxt_frame_rel_cases, get_ffi_def]
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (
    reverse CASE_TAC >>
    gvs[PULL_EXISTS, EXISTS_PROD, get_ffi_def, SF itree_ss]
    >- simp[ctxt_frame_rel_cases] >>
    rename1 `application op _ _ vs _` >>
    reverse $ Cases_on `∃s. op = FFI s` >> gvs[]
    >- (
      reverse $ rw[]
      >- (
        drule application_ffi_unchanged >>
        Cases_on `application op env (st,ffi) vs rest2` >> gvs[get_ffi_def] >>
        PairCases_on `p` >> disch_then drule >> gvs[get_ffi_def]
        )
      >- (
        drule application_rel >> gvs[ctxt_rel_def] >> disch_then drule >>
        disch_then $ qspecl_then [`vs`,`st`,`ffi`,`env`] assume_tac >>
        gvs[step_result_rel_cases, ctxt_rel_def]
        )
      ) >>
    qspecl_then [`vs`,`st`,`s`,`env`,`rest1`]
      assume_tac $ GEN_ALL application_FFI_results >> gvs[] >>
    csimp[] >> gvs[is_Effi_def, get_ffi_def]
    >- metis_tac[application_rel_FFI_type_error] >>
    imp_res_tac application_rel_FFI_step >> gvs[get_ffi_def]
    )
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases])
  >- (
    CASE_TAC >> gvs[PULL_EXISTS, EXISTS_PROD, get_ffi_def, SF itree_ss]
    >- simp[ctxt_frame_rel_cases] >>
    CASE_TAC >>  gvs[SF itree_ss] >>
    EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases]
    )
  >- (
    TOP_CASE_TAC >> gvs[SF itree_ss] >>
    EVERY_CASE_TAC >> gvs[get_ffi_def, ctxt_frame_rel_cases]
    )
QED

Theorem step_result_rel_n:
  ∀n ea eb.
    step_result_rel ea eb ∧
    ¬ is_Effi (step_n n ea)
  ⇒ step_result_rel (step_n n ea) (step_n_cml n eb) ∧
    ∀ffi. get_ffi (step_n_cml n eb) = SOME ffi ⇒ get_ffi eb = SOME ffi
Proof
  Induct >- simp[step_n_def, step_n_cml_def] >>
  simp[step_n_alt_def, step_n_cml_alt_def] >>
  rpt gen_tac >> strip_tac >>
  last_x_assum drule >> impl_keep_tac
  >- (CCONTR_TAC >> gvs[is_Effi_def]) >>
  strip_tac >>
  Cases_on `step_n n ea` >> imp_res_tac step_result_rel_cases >> gvs[get_ffi_def] >>
  simp[GSYM step_result_rel_cases] >>
  qmatch_goalsub_abbrev_tac `step_result_rel (estep ea) (e_step eb)` >>
  qspecl_then [`ea`,`eb`] assume_tac step_result_rel_single >> gvs[] >>
  unabbrev_all_tac >> gvs[get_ffi_def]
QED

Theorem step_result_rel_single_FFI:
  ∀ea eb.
    step_result_rel (Estep ea) (Estep eb) ∧
    estep ea = Effi s ws1 ws2 lnum env' st' cs1'
  ⇒ ∃ffi.
      get_ffi (Estep eb) = SOME ffi ∧
      ((∃ffi'. get_ffi (e_step eb) = SOME ffi' ∧ ffi' ≠ ffi)  ∨
       (∃outcome. e_step eb = Eabort (Rffi_error (Final_event s ws1 ws2 outcome))))
Proof
  rpt PairCases >> gvs[step_result_rel_cases, e_step_def] >> rw[] >>
  rename1 `estep (env,st,ev,cs1)` >> rename1 `Estep ((env,(st,ffi),ev,cs2))` >>
  gvs[get_ffi_def] >>
  every_case_tac >> gvs[estep_def, step_result_rel_cases, FST_THM, LAMBDA_PROD] >>
  gvs[SF smallstep_ss, SF itree_ss, ctxt_rel_def, ctxt_frame_rel_cases, get_ffi_def]
  >- (imp_res_tac application_eq_Effi_fields >> gvs[application_def, SF itree_ss]) >>
  TOP_CASE_TAC >> gvs[SF itree_ss] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[get_ffi_def, SF itree_ss]
  >- (EVERY_CASE_TAC >> gvs[])
  >- (
    CASE_TAC >> gvs[SF itree_ss, GSYM ctxt_frame_rel_cases] >>
    imp_res_tac application_eq_Effi_fields >> gvs[] >>
    rename [`LIST_REL _ cs1 cs2`, `application _ env`] >>
    drule application_rel_FFI >>
    disch_then $ qspecl_then [`ffi`,`cs2`] assume_tac >> gvs[] >>
    every_case_tac >> gvs[get_ffi_def] >>
    gvs[ffi_state_component_equality]
    )
  >- (EVERY_CASE_TAC >> gvs[])
  >- (EVERY_CASE_TAC >> gvs[])
  >- (EVERY_CASE_TAC >> gvs[])
  >- (rpt (CASE_TAC >> gvs[SF itree_ss]))
  >- (rpt (CASE_TAC >> gvs[SF itree_ss]))
QED


(****************************************)


val _ = export_theory();


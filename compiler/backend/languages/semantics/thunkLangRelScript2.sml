open HolKernel Parse BasicProvers boolLib bossLib listTheory;
open thunkLangTheory thunkLang_primitivesTheory thunkLangRel_primitivesTheory;

val _ = new_theory "thunkLangRel";
val _ = numLib.prefer_num ();

Definition fix_state_def:
  fix_state s1 (res, s2) =
    if s1.c < s2.c then (res, s1) else (res, s2)
End

Theorem fix_state_non_incr_thm:
  ∀s1 s2 x res.
   fix_state s1 x = (res, s2) ⇒ s2.c ≤ s1.c
Proof
  Cases_on `x` >> rw [fix_state_def] >> rw []
QED

Definition check_state_def:
  check_state s e f =
    if (s.c < fuel e) ∨ (s.t < trace e) then
      (OOT, s)
    else
      f $ s - (state (fuel e) (trace e))
End

Theorem check_state_CONG[defncong]:
  ∀s1 e1 s2 e2 f1 f2.
   s1 = s2 ∧ e1 = e2
   ∧ (∀s'. s'.c < s1.c ⇒ f1 s' = f2 s')
   ⇒ check_state s1 e1 f1 = check_state s2 e2 f2
Proof
  rw [check_state_def, fuel_def]
QED

Definition dest_Closure'_def[simp]:
  (dest_Closure' (Closure s x) = SOME (s, x)) ∧
  (dest_Closure' _ = NONE)
End

Definition dest_Recclosure'_def[simp]:
  (dest_Recclosure' (Recclosure f n) = SOME (f, n)) ∧
  (dest_Recclosure' _ = NONE)
End

Definition dest_anyClosure'_def:
  dest_anyClosure' v =
    case dest_Closure' v of
    | SOME (s, x) => SOME (s, x, [])
    | NONE =>
        (case dest_Recclosure' v of
         | SOME (f, n) =>
            (case ALOOKUP (REVERSE f) n of
             | SOME (Lam s x) => SOME (s, x, MAP (λ(g, x). (g, Recclosure f g)) f)
             | _ => NONE)
         | NONE => NONE)
End

Definition dest_Tick'_def[simp]:
  (dest_Tick' (DoTick v) = SOME v) ∧
  (dest_Tick' _ = NONE)
End

Definition dest_Thunk'_def[simp]:
  (dest_Thunk' (Thunk x) = SOME x) ∧
  (dest_Thunk' _ = NONE)
End

Definition dest_anyThunk'_def:
  dest_anyThunk' v =
    case dest_Thunk' v of
    | SOME w => SOME (w, [])
    | _ =>
        (case dest_Recclosure' v of
         | SOME (f, n) =>
            (case ALOOKUP (REVERSE f) n of
             | SOME (Delay x) => SOME (x, f)
             | _ => NONE)
         | NONE => NONE)
End

Definition dest_Constructor'_def[simp]:
  (dest_Constructor' (Constructor s vs) = SOME (s, vs)) ∧
  (dest_Constructor' _ = NONE)
End

Definition mapok_def:
  mapok st rs =
    case FIND (isfail ∘ FST) rs of
    | SOME (Fail, st) => (Fail, st)
    | NONE =>
        (case FIND (isoot ∘ FST) rs of
         | SOME (OOT, st) => (OOT, st)
         | NONE => (Ok (MAP (outok ∘ FST) rs), st))
End

Theorem mapok_non_incr_lemma:
  ∀st rs rs' st'.
    mapok st rs = (rs', st')
    ∧ (∀s. MEM s (MAP SND rs) ⇒ s.c ≤ st.c)
    ⇒ st'.c ≤ st.c
Proof
  rw [mapok_def]
  >> gvs [AllCaseEqs()]
  >> imp_res_tac FIND_pred_thm >> gvs []
  >> imp_res_tac FIND_MEM_thm >> gvs []
  >> imp_res_tac MEM_MAP_SND_thm >> gvs []
QED

Theorem mapok_every_thm:
  ∀s rs r s'.
    mapok s rs = (Ok r, s') ⇒ EVERY (isok ∘ FST) rs
Proof
  rw [mapok_def]
  >> gvs [AllCaseEqs(), EVERY_MEM] >> rpt strip_tac
  >> Cases_on `FST e` >> gvs []
  >> imp_res_tac FIND_pred_thm >> gvs []
QED

Theorem mapok_ok_thm:
  ∀s rs r s'.
    mapok s rs = (Ok r, s') ⇒ r = MAP (outok ∘ FST) rs
Proof
  rw [mapok_def]
  >> gvs [AllCaseEqs()]
  >> imp_res_tac FIND_pred_thm >> gvs []
QED

Theorem mapok_add_thm:
  ∀(s : state) q r s' sp.
    mapok s q = (Ok r, s')
    ⇒ mapok (s + sp) (MAP (with_snd (λs. s + sp)) q)
        = (Ok r, s' + sp)
Proof
  rw [mapok_def]
  >> gvs [AllCaseEqs(), FIND_FST_WITH_SND_thm, MAP_FST_WITH_SND_thm]
  >> imp_res_tac FIND_pred_thm >> gvs []
QED

Definition atom_lit_def:
  atom_lit r =
    case r of
    | (Ok (Atom l), s) => (Ok l, s)
    | (Ok _, s) => (Fail, s)
    | (Fail, s) => (Fail, s)
    | (OOT, s) => (OOT, s)
End

(*Theorem atom_lit_isok_thm:
  ∀x. (isok ∘ atom_lit) x ⇒ isok x
Proof
  Cases_on `x` >> gvs [atom_lit_def]
QED

Theorem EVERY_atom_lit_thm:
  ∀l.
    EVERY (isok ∘ atom_lit ∘ FST) l
    ⇒ EVERY (isok ∘ FST) l
Proof
  Induct_on `l` >> gvs []
  >> rpt strip_tac
  >> qspec_then `FST h` assume_tac atom_lit_isok_thm
  >> gvs []
QED*)

Definition result_map'_fix_def:
  (result_map'_fix s f [] = ([], s)) ∧
  (result_map'_fix s f (x::xs) =
    let (r, s') = fix_state s (f s x) in
    let (rs, s'') = result_map'_fix s' f xs in
    ((r, s') :: rs, s''))
End

Theorem result_map'_fix_CONG[defncong]:
  ∀s s' f f' xs xs'.
    s = s'
    ∧ xs = xs'
    ∧ (∀st x. st.c ≤ s.c ∧ MEM x xs ⇒ f st x = f' st x)
    ⇒ result_map'_fix s f xs = result_map'_fix s' f' xs'
Proof
  Induct_on `xs` >> gvs [result_map'_fix_def]
  >> rpt strip_tac
  >> Cases_on `fix_state s' (f' s' h)` >> rw []
  >> Cases_on `result_map'_fix r f xs` >> rw []
  >> Cases_on `result_map'_fix r f' xs` >> rw []
  >> first_x_assum $ qspecl_then [`r`, `f`, `f'`] assume_tac
  >> imp_res_tac fix_state_non_incr_thm
  >> gvs []
QED

Definition eval_to'_def:
  (eval_to' st (Value v) =
    check_state st (Value v) (λst.
      (Ok v, st))) ∧
  (eval_to' st (Var n) =
    check_state st (Var n) (λst.
      (Fail, st))) ∧
  (eval_to' st (App f x) =
    check_state st (App f x) (λst.
      case fix_state st (eval_to' st x) of
      | (Ok xv, st') =>
          (case fix_state st' (eval_to' st' f) of
           | (Ok fv, st'') =>
               (case dest_anyClosure' fv of
                | SOME (n, body, binds) =>
                    let y = subst (binds ++ [(n, xv)]) body in
                    eval_to' st'' y
                | NONE => (Fail, st''))
           | res => res)
      | res => res)) ∧
  (eval_to' st (Lam n x) =
    check_state st (Lam n x) (λst.
      (Ok (Closure n x), st))) ∧
  (eval_to' st (Let NONE x y) =
    check_state st (Let NONE x y) (λst.
      case fix_state st (eval_to' st x) of
      | (Ok xv, st') => eval_to' st' y
      | res => res)) ∧
  (eval_to' st (Let (SOME n) x y) =
    check_state st (Let (SOME n) x y) (λst.
      case fix_state st (eval_to' st x) of
      | (Ok xv, st') => eval_to' st' (subst1 n xv y)
      | res => res)) ∧
  (eval_to' st (If x y z) =
    check_state st (If x y z) (λst.
      case fix_state st (eval_to' st x) of
      | (Ok (Constructor "True" []), st') => eval_to' st' y
      | (Ok (Constructor "False" []), st') => eval_to' st' z
      | (Ok _, st') => (Fail, st')
      | res => res)) ∧
  (eval_to' st (Letrec funs x) =
    check_state st (Letrec funs x) (λst.
      eval_to' st (subst_funs funs x))) ∧
  (eval_to' st (Delay x) =
    check_state st (Delay x) (λst.
      (Ok (Thunk x), st))) ∧
  (eval_to' st (Force x) =
    check_state st (Force x) (λst.
      case fix_state st (eval_to' st x) of
      | (Ok xv, st') =>
          (case dest_anyThunk' xv of
           | SOME (y, binds) =>
               eval_to' st' (subst_funs binds y)
           | NONE => (Fail, st'))
      | res => res)) ∧
  (eval_to' st (MkTick x) =
    check_state st (MkTick x) (λst.
      case fix_state st (eval_to' st x) of
      | (Ok xv, st') => (Ok (DoTick xv), st')
      | res => res)) ∧
  (eval_to' st (Prim op xs) =
    check_state st (Prim op xs) (λst.
      (case op of
       | If => (Fail, st)
       | Seq => (Fail, st)
       | Proj s i =>
           if LENGTH xs ≠ 1 then
             (Fail, st)
           else
             (case fix_state st (eval_to' st (HD xs)) of
              | (Ok v, st') =>
                  (case dest_Constructor' v of
                   | SOME (t, ys) =>
                       if (t ≠ s) ∨ (i ≥ LENGTH ys) then
                         (Fail, st')
                       else
                         (Ok (EL i ys), st')
                   | NONE => (Fail, st'))
              | res => res)
       | IsEq s i a =>
           if LENGTH xs ≠ 1 then
             (Fail, st)
           else
             (case fix_state st (eval_to' st (HD xs)) of
              | (Ok v, st') =>
                  (case dest_Constructor' v of
                   | SOME (t, ys) =>
                       if (¬(t = s ⇒ i = LENGTH ys)) ∨ (t ∈ monad_cns) then
                         (Fail, st')
                       else if t = s then
                         (Ok (Constructor "True" []), st')
                       else
                         (Ok (Constructor "False" []), st')
                   | NONE => (Fail, st'))
              | res => res)
       | AtomOp aop =>
           let (rs, st') = result_map'_fix st (λs x. atom_lit (eval_to' s x)) xs in
           (case mapok st rs of
            | (Fail, st') => (Fail, st')
            | (OOT, st') => (OOT, st')
            | (Ok vs, st') =>
                (case eval_op aop vs of
                 | SOME (INL v) =>
                     (Ok (Atom v), st')
                  | SOME (INR b) =>
                      (Ok (Constructor (if b then "True" else "False") []), st')
                  | NONE => (Fail, st')))
       | Cons s =>
           let (rs, st') = result_map'_fix st (λs x. eval_to' s x) xs in
           (case mapok st rs of
            | (Fail, st') => (Fail, st')
            | (OOT, st') => (OOT, st')
            | (Ok vs, st') => (Ok (Constructor s vs), st'))))) ∧
  (eval_to' s (Monad mop xs) =
    check_state s (Monad mop xs) (λs.
      (Ok (Monadic mop xs), s)))
Termination
  WF_REL_TAC `inv_image ($< LEX $<) (λ(s, e). (s.c, exp_size e))`
  >> rw []
  >> gvs []
  >> imp_res_tac fix_state_non_incr_thm
  >> gvs []
End

Theorem result_map'_fix_non_incr_thm:
  ∀s f xs rs r.
    result_map'_fix s f xs = (rs, r)
    ⇒ r.c ≤ s.c 
      ∧ (∀st. MEM st (MAP SND rs) ⇒ st.c ≤ s.c)
Proof
  Induct_on `xs` >> gvs [result_map'_fix_def]
  >> rpt strip_tac
  >> Cases_on `fix_state s (f s h)` >> gvs []
  >> Cases_on `result_map'_fix r' f xs` >> gvs []
  >> imp_res_tac fix_state_non_incr_thm
  >> res_tac
  >> gvs []
QED

Theorem eval_to'_non_incr_thm:
  ∀s e res s'. eval_to' s e = (res, s') ⇒ s'.c ≤ s.c
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw [eval_to'_def, check_state_def, fuel_def, trace_def]
  >> gvs [AllCaseEqs()]
  >> imp_res_tac fix_state_non_incr_thm >> gvs []
  >>~- ([`mapok _ _`],
        qmatch_asmsub_abbrev_tac `result_map' st f xs`
        >> Cases_on `result_map'_fix st f xs` >> gvs []
        >> gvs [AllCaseEqs()]
        >> unabbrev_all_tac
        >> imp_res_tac mapok_non_incr_lemma
        >> imp_res_tac result_map'_fix_non_incr_thm
        >> gvs [])
  >> qmatch_asmsub_abbrev_tac `state a b`
  >> rpt (last_x_assum $ qspec_then `state a b` assume_tac
          >> gvs [])
  >> unabbrev_all_tac >> gvs []
QED

Definition result_map'_def:
  (result_map' s f [] = ([], s)) ∧
  (result_map' s f (x::xs) =
    let (r, s') = f s x in
    let (rs, s'') = result_map' s' f xs in
    ((r, s') :: rs, s''))
End

Theorem fix_state_thm:
  (∀s e. fix_state s (eval_to' s e) = eval_to' s e) ∧
  (∀s xs. result_map'_fix s (λs x. eval_to' s x) xs
          = result_map' s (λs x. eval_to' s x) xs) ∧
  (∀s xs. result_map'_fix s (λs x. atom_lit (eval_to' s x)) xs
          = result_map' s (λs x. atom_lit (eval_to' s x)) xs)
Proof
  rpt conj_tac
  >- (rpt strip_tac
      >> Cases_on `eval_to' s e` >> rw [fix_state_def]
      >> imp_res_tac eval_to'_non_incr_thm >> gvs [])
  >- (Induct_on `xs` >> gvs [result_map'_def, result_map'_fix_def]
      >> rpt strip_tac
      >> Cases_on `eval_to' s h` >> rw [fix_state_def]
      >> imp_res_tac eval_to'_non_incr_thm >> gvs [])
  >- (Induct_on `xs` >> gvs [result_map'_def, result_map'_fix_def]
      >> rpt strip_tac
      >> Cases_on `atom_lit (eval_to' s h)` >> rw [fix_state_def]
      >> Cases_on `eval_to' s h`
      >> gvs [AllCaseEqs(), atom_lit_def]
      >> imp_res_tac eval_to'_non_incr_thm >> gvs [])
QED

Theorem eval_to'_def[compute,allow_rebind] =
  REWRITE_RULE [fix_state_thm] eval_to'_def;

Theorem eval_to'_ind[allow_rebind] =
  REWRITE_RULE [fix_state_thm] eval_to'_ind;

Theorem eval_to'_add_thm:
  ∀s e res s' sp.
    eval_to' s e = (Ok res, s')
    ⇒ eval_to' (s + sp) e = (Ok res, s' + sp)
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw [eval_to'_def, check_state_def, fuel_def, trace_def]
  >> gvs [AllCaseEqs()]
  >>~- ([`mapok _ _`],
        Cases_on `result_map' (state (s.c - 1) s.t) xs`
        >> first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
        >> gvs [AllCaseEqs()]
        >> imp_res_tac mapok_every_thm >> gvs []
        >> imp_res_tac mapok_add_thm
        >> gvs [EVERY_MAP_WITH_FST_thm, EVERY_atom_lit_thm,
                MAP_WITH_FST_WITH_SND_thm])
  >>~- ([`result_map' _ _`],
        Cases_on `eval_to' s e` >> gvs []
        >> Cases_on `result_map' r xs` >> gvs []
        >> Cases_on `q` >> gvs [with_snd_def])

  >- (
      Cases_on `result_map' (state (s.c - 1) s.t) (λs x. eval_to' s x) xs`
      >> gvs []
      >> Cases_on `result_map' (state (s.c + sp.c − 1) (s.t + sp.t))
             (λs x. eval_to' s x) xs`
      >> rw []
      >> gvs [AllCaseEqs()]
      >> imp_res_tac mapok_add_thm
      >> first_x_assum $ qspec_then `sp` assume_tac
      >> gvs []

      `result_map' (state (s.c - 1) s.t) (λs x. eval_to' s x) xs = (q, r)
       ⇒ result_map' (state (s.c + sp.c - 1) (s.t + sp.t)) (λs x. eval_to' s x) xs
         = (MAP (with_snd (λs''. state (s''.c + sp.c) (s''.t + sp.t))) q, r + sp)` by
        (
          Induct_on `xs` >> gvs [result_map'_def]
          rw []
          >- (
              Cases_on `eval_to' (state (s.c - 1) s.t) h` >> gvs []
              >> Cases_on `result_map' r'' (λs x. eval_to' s x) xs` >> gvs []
              >> Cases_on `eval_to' (state (s.c + sp.c - 1) (s.t + sp.t)) h` >> gvs []
              >> Cases_on `result_map' r'3' (λs x. eval_to' s x) xs` >> gvs []
             )
          >- ()
        )
      >> gvs []
     )




  >> qmatch_asmsub_abbrev_tac `state a b`
  >> rpt (first_x_assum $ qspec_then `state a b` assume_tac
          >> gvs [])
  >> unabbrev_all_tac >> gvs []
QED

Theorem eval_to_add_thm:
  ∀c c' e v.
    eval_to c e = INR v
    ⇒ eval_to (c + c') e = INR v
Proof
  rpt strip_tac
  >> qspecl_then [`c`, `e`, `c + c'`] assume_tac eval_to_mono
  >> rw []
QED

Theorem eval_requiv_lemma:
  (∀s e v s'.
    eval_to' s e = (Ok v, s')
    ⇒ ∃c. eval_to c e = INR v) ∧
  (∀s xs rs s'.
    result_map' s xs = (rs, s')
    ∧ EVERY (isok ∘ FST) rs
    ⇒ ∃c. result_map (λx. eval_to c x) xs = INR (MAP (outok ∘ FST) rs))
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw []
  >> gvs [AllCaseEqs(), Once eval_to_def, eval_to'_def, check_state_def, fuel_def, trace_def]
  >- (rpt (first_x_assum $ qspec_then `state (s.c - 1) (s.t + 1)` assume_tac
           >> gvs [])
      >> qexists `c + c' + c'' + 1`
      >> qspecl_then [`c`, `c' + c'' + 1`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c + c'' + 1`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> Cases_on `fv` >> gvs [AllCaseEqs(), dest_anyClosure_def, dest_anyClosure'_def]
      >> qspecl_then [`c''`, `c + c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1`
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1`
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (gvs [Once eval_to_def]
      >> rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
              >> gvs [])
      >> qexists `c + c' + 1`
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (gvs [Once eval_to_def]
      >> rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
              >> gvs [])
      >> qexists `c + c' + 1`
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
           >> gvs [])
      >> qexists `c + 1` >> gvs []) 
  >- (rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1` >> gvs []
      >> qspecl_then [`c`, `c' + 1`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> Cases_on `xv` >> gvs [AllCaseEqs(), dest_Tick_def, dest_anyThunk_def,
                               dest_anyThunk'_def]
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
           >> gvs [])
      >> qexists `c` >> gvs [])
  >- (gvs [Once eval_to_def]
      >> rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
              >> gvs [])
      >> Cases_on `result_map' (state (s.c - 1) s.t) xs` >> gvs []
      >> ntac 2 (FULL_CASE_TAC >> gvs [])
      >> imp_res_tac mapok_every_thm >> gvs []
      >> qexists_tac `c` >> gvs []
      >> imp_res_tac mapok_ok_thm >> gvs [])
  >- (gvs [Once eval_to_def]
      >> rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
              >> gvs [])
      >> qexists_tac `c + 1` >> gvs []
      >> Cases_on `v'` >> gvs [AllCaseEqs(), dest_Constructor_def,
                               dest_Constructor'_def])
  >- (gvs [Once eval_to_def]
      >> rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
              >> gvs [])
      >> qexists_tac `c + 1` >> gvs []
      >> Cases_on `v'` >> gvs [AllCaseEqs(), dest_Constructor_def,
                               dest_Constructor'_def])
  >- (gvs [Once eval_to_def]
      >> rpt (first_x_assum $ qspec_then `state (s.c - 1) s.t` assume_tac
              >> gvs [])
      >> qexists_tac `c + 1` >> gvs []
      >> Cases_on `v'` >> gvs [AllCaseEqs(), dest_Constructor_def,
                               dest_Constructor'_def])
  >- cheat
  >- gvs [result_map_def]
  >- (Cases_on `eval_to' s e` >> gvs []
      >> Cases_on `result_map' r xs` >> gvs []
      >> Cases_on `q` >> gvs []
      >> qexists_tac `c + c'`
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> imp_res_tac result_map_add_thm
      >> first_x_assum $ qspec_then `c'` assume_tac
      >> imp_res_tac result_map_INR
      >> rw [result_map_INR, map_def])
QED

Type inv = ``:state -> state -> bool``;

Definition rel_def:
  (val_rel (s : state) (q : inv) (Constructor n vs) (Constructor n' vs') ⇔
    n = n' ∧ LIST_REL (val_rel s q) vs vs') ∧
  (val_rel s q (Monadic op es) (Monadic op' es') ⇔
    op = op' ∧ LIST_REL (exp_rel s (q, q)) es es') ∧
  (val_rel s q (Closure x e) (Closure x' e') ⇔
    ∀s' v1 v2.
      if s'.c < s.c then
        val_rel s' q v1 v2
        ⇒ exp_rel s' (q, q) (subst1 x v1 e) (subst1 x' v2 e')
      else
        T) ∧
  (val_rel s q (Recclosure fs n) (Recclosure fs' n') ⇔
    ∀s' e e'.
      s'.c < s.c
      ∧ ALOOKUP fs n = SOME e
      ∧ ALOOKUP fs' n' = SOME e'
      ⇒
      exp_rel s (q, q) (subst_funs fs e) (subst_funs fs' e')) ∧
  (val_rel s q (Thunk e) (Thunk e') ⇔
    exp_rel s (q, q) e e') ∧
  (val_rel s q (Atom l) (Atom l') ⇔
    l = l') ∧
  (val_rel s q (DoTick v) (DoTick v') ⇔
    val_rel s q v v') ∧
  (val_rel s q v1 v2 ⇔ F) ∧

  (res_rel (s : state) (q : inv) OOT OOT ⇔ T) ∧
  (res_rel s q Fail Fail ⇔ T) ∧
  (res_rel s q (Ok v) (Ok v') ⇔
    val_rel s q v v') ∧
  (res_rel s q r1 r2 ⇔ F) ∧

  (exp_rel (s : state) ((ql, qg) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀r1 s'.
      s'.c ≤ s.c
      ⇒ FST (eval_to' s' e1) = r1
      ⇒ (∃r2 s''.
          FST (eval_to' s'' e2) = r2 ∧
          ql s' s'' ∧
          res_rel <|c := s.c - s'.c; t := s.t|> qg r1 r2))
Termination
  cheat
  (*WF_REL_TAC `inv_image ($< LEX ($< LEX $<))
              (λx. case x of
                   | INL (s, q, v1, v2) => (s.c, (v_size v1, 0))
                   | INR (INL (s, q, r1, r2)) => (s.c, (res_size v_size r1, 1))
                   | INR (INR (s, (ql,qg), e1, e2)) => (s.c, (exp_size e1, 2)))`*)
End

Definition subst_rel_def:
  (subst_rel (s : state) (q : inv) (S : string set) (sub1 : (string # v) list) (sub2 : (string # v) list) ⇔  
    ∀x v1.
      if x ∈ S then
        ALOOKUP sub1 x = SOME v1
        ⇒ (∃v2. 
            ALOOKUP sub2 x = SOME v2
            ∧ val_rel s q v1 v2)
      else
        T)
End

Definition top_rel_def:
  top_rel ((ql, qg) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀(s : state) (sub1 : (string # v) list) (sub2 : (string # v) list).
      subst_rel s qg (freevars e1) sub1 sub2
      ⇒ (freevars e1) ⊆ (set (MAP FST sub1))
      ⇒ exp_rel s (ql, qg) e1 e2
End

Definition constr_compat_thm:
    ∀st ql qg x1 x2 n1 n2 es1 es2.
      ql (state 0 0) (state 0 0)
      ∧ (∀s1 s2. ql s1 s2 ⇒ ql (s1 + (state 1 0)) (s2 + (state 1 0)))
      ∧ ((∀vs1 vs2. LIST_REL (val_rel st qg) vs1 vs2
          ⇒ exp_rel st (ql, qg) (subst1 x1 (Constructor n1 vs1) e1)
                                (subst1 x2 (Constructor n2 vs2) e2)))
      ⇒ exp_rel st (ql, qg) (Let (SOME x1) (Value $ Constructor n1 es1) e1)
                            (Let (SOME x2) (Value $ Constructor n2 es2) e2)
Proof
  gvs [rel_def]
  >> gvs [AllCaseEqs(), eval_to'_def, check_state_def, fuel_def, trace_def]
  >> rpt strip_tac
  >> qexists `s'`
  >> rw []
  >- ()
  >- rw [rel_def]
  >- rw [rel_def]
  >- rw [rel_def]
  >- (
      first_x_assum $ qspecl_then [`es1`, `es2`] assume_tac >> gvs []
     )
QED

val _ = export_theory()

open HolKernel boolLib bossLib Parse;
open integerTheory stringTheory alistTheory listTheory pred_setTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;
open BasicProvers;
open term_tactic monadsyntax sumTheory;
open thunkLangTheory;

val _ = new_theory "thunkLangRel";
val _ = numLib.prefer_num ();

Datatype:
  res = Ok 'a
      | Fail
      | OOT
End

Definition OUTOK[simp,compute]:
  OUTOK (Ok x) = x
End

Type fuel = ``:num``;
Type trace = ``:num``;
Datatype:
  state = <| c : fuel; t : trace |>
End

val state_component_equality = fetch "-" "state_component_equality";

Definition fuel_def:
  (fuel (e : exp) : fuel = 1)
End

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

Theorem fix_state_add_lemma:
  ∀s1 x s2 res s3 c t.
    fix_state s1 (x, s2) = (res, s3)
    ⇒ fix_state
        <|c := s1.c + c; t := s1.t + t|>
        (x, <|c := s2.c + c; t := s2.t + t|>)
      = (res, <|c := s3.c + c; t := s3.t + t|>)
Proof
  rw [fix_state_def]
QED

Theorem fix_state_add_thm:
  ∀c t. ∀s1 x s2 res s3.
    fix_state s1 (x, s2) = (res, s3)
    ⇒ fix_state
        <|c := s1.c + c; t := s1.t + t|>
        (x, <|c := s2.c + c; t := s2.t + t|>)
      = (res, <|c := s3.c + c; t := s3.t + t|>)
Proof
  rw [fix_state_add_lemma]
QED

Definition trace_def:
  (trace (App f x) : trace = 1) ∧
  (trace e = 0)
End

Definition check_state_def:
  check_state s e f =
    if (s.c < fuel e) ∨ (s.t < trace e) then
      (OOT, s)
    else
      f <| c := s.c - fuel e; t := s.t - trace e |>
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

Definition thread_state_def:
  (thread_state st f [] = ([], st)) ∧
  (thread_state st f (x::xs) =
    let (r, st') = fix_state st (f st x) in
    let (rs, st'') = thread_state st' f xs in
    ((r, st') :: rs, st''))
End

Theorem thread_state_CONG[defncong]:
  ∀st1 st2 f1 f2 xs1 xs2.
    st1 = st2
    ∧ xs1 = xs2
    ∧ (∀st x. st.c ≤ st1.c ∧ MEM x xs1 ⇒ f1 st x = f2 st x)
    ⇒ thread_state st1 f1 xs1 = thread_state st2 f2 xs2
Proof
  Induct_on `xs1`
  >> rpt strip_tac
  >> rw [thread_state_def]
  >> Cases_on `fix_state st1 (f2 st1 h)` >> rw []
  >> first_x_assum $ qspecl_then [`r`, `r`, `f1`, `f2`, `xs1`] assume_tac
  >> gvs []
  >> imp_res_tac fix_state_non_incr_thm
  >> gvs []
QED

Theorem thread_state_non_incr_thm:
  ∀st f xs rs st'.
    thread_state st f xs = (rs, st')
    ⇒ (st'.c ≤ st.c
      ∧ (∀x. MEM x rs ⇒ (SND x).c ≤ st.c))
Proof
  Induct_on `xs`
  >> rpt strip_tac
  >> gvs [thread_state_def]
  >> Cases_on `fix_state st (f st h)` >> gvs []
  >> Cases_on `thread_state r f xs` >> gvs []
  >> res_tac
  >> imp_res_tac fix_state_non_incr_thm
  >> gvs []
QED

Theorem thread_state_add_lemma:
  ∀st f xs rs st' c t.
    thread_state st f xs = (rs, st')
    ∧ (∀st x r st' c t.
         f st x = (r, st')
         ⇒ f <|c := st.c + c; t := st.t + t|> x 
           = (r, <|c := st'.c + c; t := st'.t + t|>))
    ⇒ thread_state <|c := st.c + c; t := st.t + t|> f xs
      = (MAP (λ(r,s). (r, <|c := s.c + c; t := s.t + t|>)) rs, 
         <|c := st'.c + c; t := st'.t + t|>)
Proof
  Induct_on `xs`
  >> rw [thread_state_def]
  >> Cases_on `f st h` >> gvs []
  >> Cases_on `f <|c := c + st.c; t := t + st.t|> h` >> gvs []
  >> first_assum $ qspecl_then [`st`, `h`, `q`, `r`, `c`, `t`] assume_tac
  >> gvs []
  >> Cases_on `fix_state st (q,r)`
  >> gvs []
  >> Cases_on `fix_state <|c := c + st.c; t := t + st.t|> 
                         (q,<|c := c + r.c; t := t + r.t|>)`
  >> gvs []
  >> qspecl_then
       [`st`, `q`, `r`, `q'`, `r'`, `c`, `t`]
       assume_tac
       fix_state_add_lemma
  >> gvs []
  >> Cases_on `thread_state r' f xs` >> gvs []
  >> Cases_on `thread_state <|c := c + r'.c; t := t + r'.t|> f xs` >> gvs []
  >> first_x_assum $ qspecl_then [`r'`, `f`, `q''`, `r''`, `c`, `t`] assume_tac
  >> gvs []
QED

Theorem thread_state_add_thm:
  ∀c t. ∀st f xs rs st'.
    thread_state st f xs = (rs, st')
    ∧ (∀st x r st' c t.
         f st x = (r, st')
         ⇒ f <|c := st.c + c; t := st.t + t|> x 
           = (r, <|c := st'.c + c; t := st'.t + t|>))
    ⇒ thread_state <|c := st.c + c; t := st.t + t|> f xs
      = (MAP (λ(r,s). (r, <|c := s.c + c; t := s.t + t|>)) rs, 
         <|c := st'.c + c; t := st'.t + t|>)
Proof
  rw [thread_state_add_lemma]
QED

Theorem INDEX_FIND_pred_thm:
  ∀i P xs x. INDEX_FIND i P xs = SOME x ⇒ P (SND x)
Proof
  Induct_on `xs`
  >> rw [INDEX_FIND_def]
  >- gvs []
  >- res_tac
QED

Theorem FIND_pred_thm:
  ∀P xs x. FIND P xs = SOME x ⇒ P x
Proof
  rw [FIND_def]
  >> imp_res_tac INDEX_FIND_pred_thm
QED

Theorem INDEX_FIND_MEM_thm:
  ∀i P xs x. INDEX_FIND i P xs = SOME x ⇒ MEM (SND x) xs
Proof
  Induct_on `xs`
  >> rw [INDEX_FIND_def]
  >> res_tac
  >> gvs []
QED

Theorem FIND_MEM_thm:
  ∀P xs x. FIND P xs = SOME x ⇒ MEM x xs
Proof
  rw [FIND_def]
  >> imp_res_tac INDEX_FIND_MEM_thm
QED

Theorem find_fail_thm:
  ∀q c t.
    FIND (λ(x,_). x = Fail)
      (MAP (λ(r,s). (r, <|c := c + s.c; t := t + s.t|>)) q) = NONE
    ⇒ FIND (λ(x,_). x = Fail) q = NONE
Proof
  Induct_on `q` >> rw []
  >> first_x_assum $ qspecl_then [`c`, `t`] assume_tac >> gvs []
  >> gvs [FIND_thm]
  >> Cases_on `(λ(x,_). x = Fail) ((λ(r,s). (r,<|c := c + s.c; t := t + s.t|>)) h)`
  >> gvs []
  >> Cases_on `h` >> gvs []
QED

Theorem find_oot_thm:
  ∀q c t.
    FIND (λ(x,_). x = OOT)
      (MAP (λ(r,s). (r, <|c := c + s.c; t := t + s.t|>)) q) = NONE
    ⇒ FIND (λ(x,_). x = OOT) q = NONE
Proof
  Induct_on `q` >> rw []
  >> first_x_assum $ qspecl_then [`c`, `t`] assume_tac >> gvs []
  >> gvs [FIND_thm]
  >> Cases_on `(λ(x,_). x = OOT) ((λ(r,s). (r,<|c := c + s.c; t := t + s.t|>)) h)`
  >> gvs []
  >> Cases_on `h` >> gvs []
QED

Theorem find_oot_some_thm:
  ∀q c t s.
    FIND (λ(x,_). x = OOT)
      (MAP (λ(r,s). (r, <|c := c + s.c; t := t + s.t|>)) q)
    = SOME (OOT, s)
    ⇒ FIND (λ(x,_). x = OOT) q
      = SOME (OOT, <|c := s.c - c; t := s.t - t|>)
      ∧ s.c ≥ c
      ∧ s.t ≥ t
Proof
  Induct_on `q`
  >> rw []
  >> gvs [FIND_thm]
  >> Cases_on `h` >> gvs []
  >> Cases_on `q'`
  >> gvs [state_component_equality]
  >> res_tac
QED

Theorem find_fail_some_thm:
  ∀q c t s.
    FIND (λ(x,_). x = Fail)
      (MAP (λ(r,s). (r, <|c := c + s.c; t := t + s.t|>)) q)
    = SOME (Fail, s)
    ⇒ FIND (λ(x,_). x = Fail) q
      = SOME (Fail, <|c := s.c - c; t := s.t - t|>)
      ∧ s.c ≥ c
      ∧ s.t ≥ t
Proof
  Induct_on `q`
  >> rw []
  >> gvs [FIND_thm]
  >> Cases_on `h` >> gvs []
  >> Cases_on `q'`
  >> gvs [state_component_equality]
  >> res_tac
QED

Theorem MAP_FST_o:
  ∀g f l.
    MAP (g ∘ FST ∘ (λ(x,y). (x, f y))) l = MAP (g ∘ FST) l
Proof
  Induct_on `l` >> rw []
  >> Cases_on `h` >> rw []
QED

Definition result_map'_def:
  result_map' st f xs =
    let (rs, st') = thread_state st f xs in
    let rs' = REVERSE rs in
    case FIND (λ(x, _). x = Fail) rs' of
    | SOME (Fail, st') => (Fail, st')
    | NONE =>
        (case FIND (λ(x, _). x = OOT) rs' of
         | SOME (OOT, st') => (OOT, st')
         | NONE => (Ok (MAP (OUTOK ∘ FST) rs'), st'))
End

Theorem result_map'_CONG[defncong]:
  ∀st1 st2 f1 f2 xs1 xs2.
    st1 = st2
    ∧ xs1 = xs2
    ∧ (∀st x. st.c ≤ st1.c ∧ MEM x xs1 ⇒ f1 st x = f2 st x)
    ⇒ result_map' st1 f1 xs1 = result_map' st2 f2 xs2
Proof
  rw [result_map'_def]
  >> imp_res_tac thread_state_CONG
  >> gvs []
QED

Theorem result_map'_non_incr_thm:
  ∀st f xs res st'.
    result_map' st f xs = (res, st')
    ⇒ st'.c ≤ st.c
Proof
  rw [result_map'_def]
  >> Cases_on `thread_state st f xs` >> gvs []
  >> imp_res_tac thread_state_non_incr_thm
  >> gvs [AllCaseEqs()]
  >> imp_res_tac FIND_pred_thm >> gvs []
  >> qmatch_asmsub_abbrev_tac `FIND _ _ = SOME el`
  >> first_x_assum $ qspec_then `el` assume_tac
  >> unabbrev_all_tac
  >> imp_res_tac FIND_MEM_thm
  >> gvs [MEM_REVERSE]
QED

Theorem result_map'_add_lemma:
  ∀st f xs res st' c t.
    result_map' st f xs = (res, st')
    ∧ (∀st x r st' c t.
         f st x = (r, st')
         ⇒ f <|c := st.c + c; t := st.t + t|> x 
           = (r, <|c := st'.c + c; t := st'.t + t|>))
    ⇒ result_map' <|c := st.c + c; t := st.t + t|> f xs
      = (res, <|c := st'.c + c; t := st'.t + t|>)
Proof
  rpt strip_tac
  >> rw [result_map'_def]
  >> Cases_on `thread_state <|c := c + st.c; t := t + st.t|> f xs` >> gvs []
  >> TOP_CASE_TAC
  >- (TOP_CASE_TAC
      >- (gvs [result_map'_def]
          >> Cases_on `thread_state st f xs` >> gvs []
          >> qspecl_then [`st`, `f`, `xs`, `q'`, `r'`, `c`, `t`] assume_tac thread_state_add_lemma
          >> gvs [GSYM rich_listTheory.MAP_REVERSE]
          >> qspecl_then [`REVERSE q'`, `c`, `t`] assume_tac find_fail_thm
          >> gvs []
          >> qspecl_then [`REVERSE q'`, `c`, `t`] assume_tac find_oot_thm
          >> gvs []
          >> rw [MAP_MAP_o, MAP_FST_o])
      >- (ntac 2 TOP_CASE_TAC
          >> imp_res_tac FIND_pred_thm >> gvs []
          >> gvs [result_map'_def]
          >> Cases_on `thread_state st f xs` >> gvs []
          >> qspecl_then [`st`, `f`, `xs`, `q'`, `r''`, `c`, `t`] assume_tac thread_state_add_lemma
          >> gvs []
          >> gvs [GSYM rich_listTheory.MAP_REVERSE]
          >> qspecl_then [`REVERSE q'`, `c`, `t`] assume_tac find_fail_thm
          >> gvs []
          >> qspecl_then [`REVERSE q'`, `c`, `t`, `r'`] assume_tac find_oot_some_thm
          >> gvs []
          >> rw [state_component_equality]))
  >- (TOP_CASE_TAC
      >> gvs [result_map'_def]
      >> Cases_on `thread_state st f xs` >> gvs []
      >> qspecl_then [`st`, `f`, `xs`, `q''`, `r''`, `c`, `t`] assume_tac thread_state_add_lemma
      >> gvs [GSYM rich_listTheory.MAP_REVERSE]
      >> imp_res_tac FIND_pred_thm >> gvs []
      >> qspecl_then [`REVERSE q''`, `c`, `t`, `r'`] assume_tac find_fail_some_thm
      >> gvs [state_component_equality])
QED

Theorem result_map'_add_thm:
  ∀c t. ∀st f xs res st'.
    result_map' st f xs = (res, st')
    ∧ (∀st x r st' c t.
         f st x = (r, st')
         ⇒ f <|c := st.c + c; t := st.t + t|> x 
           = (r, <|c := st'.c + c; t := st'.t + t|>))
    ⇒ result_map' <|c := st.c + c; t := st.t + t|> f xs
      = (res, <|c := st'.c + c; t := st'.t + t|>)
Proof
  rw [result_map'_add_lemma]
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
       | Cons s =>
           (case result_map' st (λst x. eval_to' st x) xs of
            | (Fail, st') => (Fail, st')
            | (OOT, st') => (OOT, st')
            | (Ok vs, st') => (Ok (Constructor s vs), st'))
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
           (case result_map' st (λst x. case eval_to' st x of
                                        | (Ok (Atom l), st') => (Ok l, st')
                                        | (Ok _, st') => (Fail, st')
                                        | (Fail, st') => (Fail, st')
                                        | (OOT, st') => (OOT, st')) xs of
            | (Fail, st') => (Fail, st')
            | (OOT, st') => (OOT, st')
            | (Ok vs, st') =>
                (case eval_op aop vs of
                 | SOME (INL v) =>
                     (Ok (Atom v), st')
                 | SOME (INR b) =>
                     (Ok (Constructor (if b then "True" else "False") []), st')
                 | NONE => (Fail, st')))))) ∧
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

Theorem state_non_incr_thm:
  ∀s1 e res s2.
    eval_to' s1 e = (res, s2) ⇒ s2.c ≤ s1.c
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw [eval_to'_def, check_state_def, fuel_def, trace_def]
  >> gvs [AllCaseEqs()]
  >> imp_res_tac fix_state_non_incr_thm >> gvs []
  >> imp_res_tac result_map'_non_incr_thm >> gvs []
  >> qmatch_asmsub_abbrev_tac `<|c := a; t := b|>`
  >> rpt (last_x_assum $ qspec_then `<|c := a; t := b|>` assume_tac
          >> gvs [])
  >> unabbrev_all_tac
  >> gvs []
QED

Theorem fix_state_thm:
  ∀s e. fix_state s (eval_to' s e) = eval_to' s e
Proof
  rpt strip_tac
  >> Cases_on `eval_to' s e`
  >> rw [fix_state_def]
  >> imp_res_tac state_non_incr_thm
  >> gvs []
QED

Definition thread_state_eval_def:
  (thread_state_eval st f [] = ([], st)) ∧
  (thread_state_eval st f (x::xs) =
    let (r, st') = f st x in
    let (rs, st'') = thread_state_eval st' f xs in
    ((r, st') :: rs, st''))
End

Definition result_map'_eval_def:
  result_map'_eval st f xs =
    let (rs, st') = thread_state_eval st f xs in
    let rs' = REVERSE rs in
    case FIND (λ(x, _). x = Fail) rs' of
    | SOME (Fail, st') => (Fail, st')
    | NONE =>
        (case FIND (λ(x, _). x = OOT) rs' of
         | SOME (OOT, st') => (OOT, st')
         | NONE => (Ok (MAP (OUTOK ∘ FST) rs'), st'))
End

Theorem thread_state_fix_one:
  ∀st xs.
    thread_state st (λst x. eval_to' st x) xs
    = thread_state_eval st (λst x. eval_to' st x) xs
Proof
  Induct_on `xs`
  >> rw [thread_state_def, thread_state_eval_def]
  >> rw [fix_state_thm]
QED

Theorem result_map'_fix_one:
  ∀st xs.
    result_map' st (λst x. eval_to' st x) xs
    = result_map'_eval st (λst x. eval_to' st x) xs
Proof
  rw [result_map'_def, result_map'_eval_def, thread_state_fix_one]
QED

Theorem fix_state_two_thm:
  ∀st x. fix_state st (case eval_to' st x of
                       | (Ok (Atom l), st') => (Ok l, st')
                       | (Ok _, st') => (Fail, st')
                       | (Fail, st') => (Fail, st')
                       | (OOT, st') => (OOT, st'))
        = case eval_to' st x of
          | (Ok (Atom l), st') => (Ok l, st')
          | (Ok _, st') => (Fail, st')
          | (Fail, st') => (Fail, st')
          | (OOT, st') => (OOT, st')
Proof
  rpt strip_tac
  >> Cases_on `eval_to' st x`
  >> rw [fix_state_def]
  >> imp_res_tac state_non_incr_thm
  >> gvs []
  >> rpt TOP_CASE_TAC
  >> gvs [fix_state_def]
QED

Theorem thread_state_fix_two:
  ∀st xs.
    thread_state st (λst x. case eval_to' st x of
                            | (Ok (Atom l), st') => (Ok l, st')
                            | (Ok _, st') => (Fail, st')
                            | (Fail, st') => (Fail, st')
                            | (OOT, st') => (OOT, st')) xs
    = thread_state_eval st (λst x. case eval_to' st x of
                                   | (Ok (Atom l), st') => (Ok l, st')
                                   | (Ok _, st') => (Fail, st')
                                   | (Fail, st') => (Fail, st')
                                   | (OOT, st') => (OOT, st')) xs
Proof
  Induct_on `xs`
  >> rw [thread_state_def, thread_state_eval_def]
  >> rw [fix_state_two_thm]
QED

Theorem result_map'_fix_two:
  ∀st xs.
    result_map' st (λst x. case eval_to' st x of
                           | (Ok (Atom l), st') => (Ok l, st')
                           | (Ok _, st') => (Fail, st')
                           | (Fail, st') => (Fail, st')
                           | (OOT, st') => (OOT, st')) xs
    = result_map'_eval st (λst x. case eval_to' st x of
                                  | (Ok (Atom l), st') => (Ok l, st')
                                  | (Ok _, st') => (Fail, st')
                                  | (Fail, st') => (Fail, st')
                                  | (OOT, st') => (OOT, st')) xs
Proof
  rw [result_map'_def, result_map'_eval_def, thread_state_fix_two]
QED

Theorem eval_to'_def[compute,allow_rebind] =
  REWRITE_RULE [fix_state_thm] eval_to'_def;

Theorem eval_to'_ind[allow_rebind] =
  REWRITE_RULE [fix_state_thm] eval_to'_ind;

Theorem eval_to'_def[compute,allow_rebind] =
  REWRITE_RULE [result_map'_fix_one] eval_to'_def;

Theorem eval_to'_ind[allow_rebind] =
  REWRITE_RULE [result_map'_fix_one] eval_to'_ind;

Theorem eval_to'_def[compute,allow_rebind] =
  REWRITE_RULE [result_map'_fix_two] eval_to'_def;

Theorem eval_to'_ind[allow_rebind] =
  REWRITE_RULE [result_map'_fix_two] eval_to'_ind;

Definition eval'_def:
  eval' x =
    case some (c, t). FST (eval_to' <|c := c; t := t|> x) ≠ OOT of
      NONE => Fail
    | SOME (c, t) => FST (eval_to' <|c := c; t := t|> x)
End

Theorem eval_to'_add_lemma:
  ∀s e v s' c t.
    eval_to' s e = (Ok v, s')
    ⇒ eval_to' <|c := s.c + c; t := s.t + t|> e
        = (Ok v, <|c := s'.c + c; t := s'.t + t|>)
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw []
  >> gvs [AllCaseEqs(), eval_to'_def, check_state_def, fuel_def, trace_def]
  >>~- ([`result_map' _ _ _ = _`],
        imp_res_tac result_map'_add_thm
        >> gvs []
        >> first_x_assum $ qspec_then `<|c := c; t := t|>` assume_tac
        >> gvs [])
  >> qmatch_asmsub_abbrev_tac `<|c := a; t := b|>`
  >> rpt (first_x_assum $ qspec_then `<|c := a; t := b|>` assume_tac
          >> gvs [])
  >> unabbrev_all_tac >> gvs []
QED

Theorem eval_to'_add_thm:
  ∀s c t.
    ∀e v s'.
      eval_to' s e = (Ok v, s')
      ⇒ eval_to' <|c := s.c + c; t := s.t + t|> e
          = (Ok v, <|c := s'.c + c; t := s'.t + t|>)
Proof
  rw [eval_to'_add_lemma]
QED

Theorem eval_requiv_lemma:
  ∀s e v s'. eval_to' s e = (Ok v, s')
    ⇒ ∃c. eval_to c e = INR v
Proof
  cheat
  (*ho_match_mp_tac eval_to'_ind
  >> rw []
  >> gvs [AllCaseEqs(), eval_to'_def, eval_to_def, check_state_def, fuel_def, trace_def]
  >- (rpt (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t - 1|>` assume_tac
           >> gvs [])
      >> qexists `c + c' + c'' + 1`
      >> qspecl_then [`c`, `c' + c'' + 1`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c + c'' + 1`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> Cases_on `fv` >> gvs [AllCaseEqs(), dest_anyClosure_def, dest_anyClosure'_def]
      >> qspecl_then [`c''`, `c + c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
      >> gvs []
      >> qexists `c + 1` >> rw [])
  >- (rpt (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1` >> rw []
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1` >> rw []
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1` >> rw []
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1` >> rw []
      >> qspecl_then [`c`, `c'`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])
  >- (rpt (first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
           >> gvs [])
      >> qexists `c + c' + 1` >> rw []
      >> qspecl_then [`c`, `c' + 1`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw []
      >> Cases_on `xv` >> gvs [AllCaseEqs(), dest_anyThunk_def, dest_anyThunk'_def]
      >> qspecl_then [`c'`, `c`] assume_tac eval_to_add_thm
      >> pop_assum drule >> rw [])*)
QED

Theorem really[simp]:
  ∀s. <|c := s.c; t := s.t|> = s
Proof
  rw [fetch "-" "state_component_equality"]
QED

Theorem eval_lequiv_lemma:
  ∀c e v.
    eval_to c e = INR v
    ⇒ ∃s s'. eval_to' s e = (Ok v, s')
Proof
  cheat
  (*ho_match_mp_tac eval_to_ind
  >> rw []
  >> gvs [AllCaseEqs(), eval_to_def]
  >> rw [AllCaseEqs(), eval_to'_def, check_state_def, fuel_def, trace_def]

  >- (Cases_on `eval_to c e'` >> gvs []
      >> Cases_on `eval_to c e` >> gvs []
      >> Cases_on `y'` >> gvs [AllCaseEqs(), dest_anyClosure_def]
      >- (first_x_assum $ qspecl_then [`[]`, `s'4'`, `y`, `e''`] assume_tac
          >> gvs []
          >> qexistsl [`<|c := s.c + s''.c + s'5'.c + 1; t := s.t + s''.t +
                        s'5'.t + 1|>`, `<|c := s'.c + s'3'.c + s'6'.c; t :=
                        s'.t + s'3'.t + s'6'.t|>`] >> gvs []
          >> qspecl_then [`s''`, `s.c + s'5'.c`, `s.t + s'5'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []
          >> rw [dest_anyClosure'_def]
          >> qspecl_then [`s`, `s'3'.c + s'5'.c`, `s'3'.t + s'5'.t`] assume_tac
               eval_to'_add_thm
          >> pop_assum drule >> rw []
          >> qspecl_then [`s'5'`, `s'.c + s'3'.c`, `s'.t + s'3'.t`] assume_tac
               eval_to'_add_thm
          >> pop_assum drule >> rw [])
      >- (Cases_on `ALOOKUP (REVERSE l) s'4'` >> gvs []
          >> Cases_on `x` >> gvs []
          >> first_x_assum $ qspecl_then [`MAP (λ(g,x). (g,Recclosure l g)) l`,
            `s'5'`, `y`, `e''`] assume_tac
          >> gvs []
          >> Cases_on `c = 0` >> gvs []
          >> qexistsl [`<|c := s.c + s''.c + s'6'.c + 1; t := s.t + s''.t + s'6'.t + 1|>`,
                       `<|c := s'.c + s'3'.c + s'7'.c; t := s'.t + s'3'.t + s'7'.t|>`]
          >> gvs []
          >> qspecl_then [`s''`, `s.c + s'6'.c`, `s.t + s'6'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []
          >> rw [dest_anyClosure'_def]
          >> qspecl_then [`s`, `s'3'.c + s'6'.c`, `s'3'.t + s'6'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []
          >> qspecl_then [`s'6'`, `s'.c + s'3'.c`, `s'.t + s'3'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []))

  >- (qexists `<|c := 1; t := 1|>` >> rw [])

  >- (qexists `<|c := s.c + 1; t := s.t|>` >> rw [])

  >- (Cases_on `eval_to (c - 1) e` >> gvs []
      >> qexists `<|c := s.c + s''.c + 1; t := s.t + s''.t|>`
      >> rw []
      >> qspecl_then [`s`, `s''.c`, `s''.t`] assume_tac eval_to'_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`s''`, `s'.c`, `s'.t`] assume_tac eval_to'_add_thm
      >> pop_assum drule >> rw [])
  
  >- (Cases_on `eval_to (c - 1) e` >> gvs []
      >> first_x_assum $ drule_then assume_tac
      >> gvs []
      >> qexists `<|c := s.c + s''.c + 1; t := s.t + s''.t|>`
      >> rw []
      >> qspecl_then [`s`, `s''.c`, `s''.t`] assume_tac eval_to'_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`s''`, `s'.c`, `s'.t`] assume_tac eval_to'_add_thm
      >> pop_assum drule >> rw [])

  >- (Cases_on `eval_to (c - 1) e` >> gvs []
      >> Cases_on `y` >> gvs []
      >> Cases_on `b` >> gvs []
      >> qexists `<|c := s.c + s''.c + 1; t := s.t + s''.t|>`
      >> rw []
      >> qspecl_then [`s`, `s''.c`, `s''.t`] assume_tac eval_to'_add_thm
      >> pop_assum drule >> rw []
      >> qspecl_then [`s''`, `s'.c`, `s'.t`] assume_tac eval_to'_add_thm
      >> pop_assum drule >> rw [])

  >- (qexists `<|c := 1; t := 1|>` >> rw [])

  >- (Cases_on `eval_to c e` >> gvs [dest_anyThunk_def]
      >> Cases_on `y` >> gvs []
      >- (first_x_assum $ qspecl_then [`[]`, `e'`, `v`] assume_tac
          >> gvs []
          >> qexists `<|c := s.c + s''.c + 1; t := s.t + s''.t|>`
          >> rw []
          >> qspecl_then [`s`, `s''.c`, `s''.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []
          >> rw [dest_anyThunk'_def]
          >> qspecl_then [`s''`, `s'.c`, `s'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw [])
      >- (Cases_on `ALOOKUP (REVERSE l) s''` >> gvs []
          >> Cases_on `x` >> gvs []
          >> first_x_assum $ qspecl_then [`l`, `e'`, `v`] assume_tac
          >> gvs []
          >> qexists `<|c := s.c + s'3'.c + 1; t := s.t + s'3'.t|>`
          >> rw []
          >> qspecl_then [`s`, `s'3'.c`, `s'3'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []
          >> rw [dest_anyThunk'_def]
          >> qspecl_then [`s'3'`, `s'.c`, `s'.t`] assume_tac eval_to'_add_thm
          >> pop_assum drule >> rw []))

  >- (qexists `<|c := 1; t := 1|>` >> rw [])*)
QED

Theorem eval_equiv_thm:
  ∀e v.
    (∀c. eval_to c e = INR v ⇒ ∃s s'. eval_to' s e = (Ok v, s')) ∧
    (∀s s'. eval_to' s e = (Ok v, s') ⇒ ∃c. eval_to c e = INR v)
Proof
  rw []
  >- (imp_res_tac eval_lequiv_lemma
      >> metis_tac [])
  >- (imp_res_tac eval_requiv_lemma
      >> metis_tac [])
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
                   | INR (INR (s, (ql,qg), e1, e2)) => (s.c, (exp_size e1, 2)))`
  >- cheat*)
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
    ql <|c := 0; t := 0|> <|c := 0; t := 0|>
    ∧ (∀c1 t1 c2 t2. ql <|c := c1; t := t1|> <|c := c2; t := t2|>
                     ⇒ ql <|c := c1 + 1; t := t1|> <|c := c2 + 1; t := t2|>)
    ⇒ ((∀vs1 vs2. LIST_REL (val_rel st qg) vs1 vs2
        ⇒ exp_rel st (ql, qg) (subst1 x1 (Constructor n1 vs1) e1)
                              (subst1 x2 (Constructor n2 vs2) e2))
       ⇒ exp_rel st (ql, qg) (Let (SOME x1) (Value $ Constructor n1 es1) e1)
                             (Let (SOME x2) (Value $ Constructor n2 es2) e2))
Proof
  cheat
QED


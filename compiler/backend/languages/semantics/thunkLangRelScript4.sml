open HolKernel boolLib bossLib Parse;
open integerTheory stringTheory alistTheory listTheory rich_listTheory pred_setTheory;
open pairTheory optionTheory finite_mapTheory arithmeticTheory;
open BasicProvers;
open term_tactic monadsyntax sumTheory;
open thunkLangTheory;

val _ = numLib.prefer_num ();

Datatype:
  res = Ok 'a
      | Fail
      | OOT
End

Definition isok_def[simp]:
  (isok (Ok x) = T) ∧
  (isok _ = F)
End

Definition isfail_def[simp]:
  (isfail Fail = T) ∧
  (isfail _ = F)
End

Definition isoot_def[simp]:
  (isoot OOT = T) ∧
  (isoot _ = F)
End

Definition OUTOK[simp,compute]:
  OUTOK (Ok x) = x
End

Type fuel = ``:num``;
Type trace = ``:num``;
Datatype:
  state = <| c : fuel; t : trace |>
End

Definition fuel_def:
  (fuel (e : exp) : fuel = 1)
End

Definition trace_def:
  (trace (App f x) : trace = 1) ∧
  (trace e = 0)
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

Definition mapok_def:
  mapok st rs =
    case FIND (isfail ∘ FST) rs of
    | SOME (Fail, st) => (Fail, st)
    | NONE =>
        (case FIND (isoot ∘ FST) rs of
         | SOME (OOT, st) => (OOT, st)
         | NONE => (Ok (MAP (OUTOK ∘ FST) rs), st))
End

Theorem FIND_pred_thm:
  (∀P xs x. FIND P xs = SOME x ⇒ P x) ∧
  (∀P xs. FIND P xs = NONE ⇒ (∀x. MEM x xs ⇒ ¬(P x)))
Proof
  rw []
  >> Induct_on `xs` >> gvs [FIND_thm]
  >> ntac 2 (rw [])
QED

Theorem FIND_MEM_thm:
  ∀P xs x. FIND P xs = SOME x ⇒ MEM x xs
Proof
  Induct_on `xs` >> gvs [FIND_thm]
  >> rw []
  >> res_tac
  >> rw []
QED

Theorem MEM_MAP_SND_thm:
  ∀x x' xs.
    MEM (x, x') xs ⇒ MEM x' (MAP SND xs)
Proof
  Induct_on `xs` >> gvs []
  >> rpt strip_tac
  >> rw []
  >> first_x_assum $ drule_then assume_tac
  >> rw []
QED

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

Definition with_fst_def:
  with_fst f (x, y) = (f x, y)
End

Definition with_snd_def:
  with_snd f (x, y) = (x, f y)
End

Theorem FIND_FST_WITH_SND_thm:
  ∀l f g.
    FIND (f ∘ FST) l = NONE
    ⇒ FIND (f ∘ FST) (MAP (with_snd g) l) = NONE
Proof
  Induct_on `l` >> gvs [FIND_thm]
  >> rw []
  >> Cases_on `h` >> gvs [with_snd_def]
QED

Theorem FIND_FST_WITH_SND_SOME_thm:
  ∀l f g x.
    FIND (f ∘ FST) l = SOME x
    ⇒ FIND (f ∘ FST) (MAP (with_snd g) l)
        = SOME (with_snd g x)
Proof
  Induct_on `l` >> gvs [FIND_thm]
  >> rw []
  >> Cases_on `h` >> gvs [with_snd_def]
QED

Theorem MAP_FST_WITH_SND_thm:
  ∀l f g.
    MAP (f ∘ FST) (MAP (with_snd g) l)
    = MAP (f ∘ FST) l
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Cases_on `h` >> gvs [with_snd_def]
QED

Theorem MAP_SND_MAP_WITH_FST_thm:
  ∀f l.
    MAP SND (MAP (with_fst f) l) = MAP SND l
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Cases_on `h` >> gvs [with_fst_def]
QED

Theorem EVERY_MAP_WITH_FST_thm:
  ∀P f l.
    EVERY (P ∘ FST) (MAP (with_fst f) l)
    ⇔ EVERY (P ∘ f ∘ FST) l
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Cases_on `h` >> gvs [with_fst_def]
QED

Theorem MAP_WITH_FST_WITH_SND_thm:
  ∀f g l.
    MAP (with_fst f) (MAP (with_snd g) l)
    = MAP (with_snd g) (MAP (with_fst f) l)
Proof
  Induct_on `l` >> gvs []
  >> rw []
  >> Induct_on `h` >> gvs [with_fst_def, with_snd_def]
QED

Theorem mapok_add_thm:
  ∀s q r s' c t.
    mapok s q = (Ok r, s')
    ⇒ mapok
        <|c := s.c + c; t := s.t + t|>
        (MAP (with_snd (λs. <|c := s.c + c; t := s.t + t|>)) q)
      = (Ok r, <|c := s'.c + c; t := s'.t + t|>)
Proof
  rw [mapok_def]
  >> gvs [AllCaseEqs(), FIND_FST_WITH_SND_thm, MAP_FST_WITH_SND_thm]
  >> imp_res_tac FIND_pred_thm >> gvs []
QED

Definition atom_lit_def:
  atom_lit r =
    case r of
    | Ok (Atom l) => Ok l
    | Ok _ => Fail
    | Fail => Fail
    | OOT => OOT
End

Theorem atom_lit_isok_thm:
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
           let (rs, st') = result_map' st xs in
           let rs = MAP (with_fst atom_lit) rs in
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
           let (rs, st') = result_map' st xs in
           (case mapok st rs of
            | (Fail, st') => (Fail, st')
            | (OOT, st') => (OOT, st')
            | (Ok vs, st') => (Ok (Constructor s vs), st'))))) ∧
  (eval_to' s (Monad mop xs) =
    check_state s (Monad mop xs) (λs.
      (Ok (Monadic mop xs), s))) ∧
  (result_map' st [] = ([], st)) ∧
  (result_map' st (x::xs) =
    let (r, st') = fix_state st (eval_to' st x) in
    let (rs, st'') = result_map' st' xs in
    (rs ++ [(r, st')], st''))
Termination
  cheat
  (*WF_REL_TAC `inv_image ($< LEX $<)
                (λx. case x of
                     | INL (s, e) => (s.c, exp_size e)
                     | INR (s, es) => (s.c, _))`
  >> rw []
  >> gvs []
  >> imp_res_tac fix_state_non_incr_thm
  >> gvs []*)
End

Theorem eval_to'_non_incr_thm:
  (∀s e res s'.
    eval_to' s e = (res, s') ⇒ s'.c ≤ s.c) ∧
  (∀s xs rs s'.
    result_map' s xs = (rs, s')
    ⇒ (s'.c ≤ s.c
       ∧ (∀st. MEM st (MAP SND rs) ⇒ st.c ≤ s.c)))
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw [eval_to'_def, check_state_def, fuel_def, trace_def]
  >> gvs [AllCaseEqs()]
  >> imp_res_tac fix_state_non_incr_thm >> gvs []
  >>~- ([`mapok _ _`],
        Cases_on `result_map' <|c := s.c - 1; t := s.t|> xs`
        >> gvs [AllCaseEqs()]
        >> imp_res_tac mapok_non_incr_lemma
        >> gvs [MAP_SND_MAP_WITH_FST_thm])
  >>~- ([`result_map' _ _`],
        Cases_on `fix_state s (eval_to' s e)` >> gvs []
        >> Cases_on `result_map' r xs` >> gvs []
        >> imp_res_tac fix_state_non_incr_thm >> gvs []
        >> res_tac >> simp [])
  >> qmatch_asmsub_abbrev_tac `<|c := a; t := b|>`
  >> rpt (last_x_assum $ qspec_then `<|c := a; t := b|>` assume_tac
          >> gvs [])
  >> unabbrev_all_tac >> gvs []
QED

Theorem fix_state_thm:
  ∀s e. fix_state s (eval_to' s e) = eval_to' s e
Proof
  rpt strip_tac
  >> Cases_on `eval_to' s e` >> rw [fix_state_def]
  >> imp_res_tac eval_to'_non_incr_thm >> gvs []
QED

Theorem eval_to'_def[compute,allow_rebind] =
  REWRITE_RULE [fix_state_thm] eval_to'_def;

Theorem eval_to'_ind[allow_rebind] =
  REWRITE_RULE [fix_state_thm] eval_to'_ind;

Theorem eval_to'_add_thm:
  (∀s e res s' c t.
    eval_to' s e = (Ok res, s')
    ⇒ eval_to' <|c := s.c + c; t := s.t + t|> e
      = (Ok res, <|c := s'.c + c; t := s'.t + t|>)) ∧
  (∀s xs rs s' c t.
    result_map' s xs = (rs, s')
    ∧ EVERY (isok ∘ FST) rs
    ⇒ result_map' <|c := s.c + c; t := s.t + t|> xs
      = (MAP (with_snd (λs. <|c := s.c + c; t := s.t + t|>)) rs,
         <|c := s'.c + c; t := s'.t + t|>))
Proof
  ho_match_mp_tac eval_to'_ind
  >> rw [eval_to'_def, check_state_def, fuel_def, trace_def]
  >> gvs [AllCaseEqs()]
  >>~- ([`mapok _ _`],
        Cases_on `result_map' <|c := s.c - 1; t := s.t|> xs`
        >> first_x_assum $ qspec_then `<|c := s.c - 1; t := s.t|>` assume_tac
        >> gvs [AllCaseEqs()]
        >> imp_res_tac mapok_every_thm >> gvs []
        >> imp_res_tac mapok_add_thm
        >> gvs [EVERY_MAP_WITH_FST_thm, EVERY_atom_lit_thm,
                MAP_WITH_FST_WITH_SND_thm])
  >>~- ([`result_map' _ _`],
        Cases_on `eval_to' s e` >> gvs []
        >> Cases_on `result_map' r xs` >> gvs []
        >> Cases_on `q` >> gvs [with_snd_def])
  >> qmatch_asmsub_abbrev_tac `<|c := a; t := b|>`
  >> rpt (first_x_assum $ qspec_then `<|c := a; t := b|>` assume_tac
          >> gvs [])
  >> unabbrev_all_tac >> gvs []
QED

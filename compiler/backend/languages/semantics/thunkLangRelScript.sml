open HolKernel Parse BasicProvers boolLib bossLib listTheory;
open thunkLangTheory thunkLang_primitivesTheory 
     thunkLangRel_primitivesTheory thunkLangRel_semanticsTheory;

val _ = new_theory "thunkLangRel";
val _ = numLib.prefer_num ();

Type inv = ``:state -> state -> bool``;
Type sigma = ``:(string # v) list``;

Definition rel_def:
  (val_rel (k : fuel) (Q : inv) (Constructor n vs) (Constructor n' vs') ⇔
    n = n'
    ∧ LIST_REL (val_rel k Q) vs vs') ∧
  (val_rel k Q (Monadic op es) (Monadic op' es') ⇔
    op = op'
    ∧ ∀i. i < k
      ⇒ LIST_REL (exp_rel i (Q, Q)) es es') ∧
  (val_rel k Q (Closure x e) (Closure x' e') ⇔
    ∀i v1 v2.
      i < k
      ⇒ val_rel i Q v1 v2
      ⇒ exp_rel i (Q, Q) (subst1 x v1 e) (subst1 x' v2 e')) ∧
  (val_rel k Q (Recclosure fs n) (Recclosure fs' n') ⇔
    ∀i e e'.
      i < k
      ∧ ALOOKUP fs n = SOME e
      ∧ ALOOKUP fs' n' = SOME e'
      ⇒ exp_rel i (Q, Q) (subst_funs fs e) (subst_funs fs' e')) ∧
  (val_rel k Q (Thunk e) (Thunk e') ⇔
    ∀i. i < k ⇒ exp_rel i (Q, Q) e e') ∧
  (val_rel k Q (Atom l) (Atom l') ⇔ l = l') ∧
  (val_rel k Q (DoTick v) (DoTick v') ⇔ val_rel k Q v v') ∧
  (val_rel k Q v1 v2 ⇔ F) ∧

  (res_rel (k : fuel) (Q : inv) OOT OOT ⇔ T) ∧
  (res_rel k Q Fail Fail ⇔ T) ∧
  (res_rel k Q (Ok v) (Ok v') ⇔ val_rel k Q v v') ∧
  (res_rel k Q r1 r2 ⇔ F) ∧

  (exp_rel (k : fuel) ((QL, QG) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀c1 t1 r1.
      c1 ≤ k
      ⇒ FST (eval_to' (state c1 t1) e1) = r1
      ⇒ (∃c2 t2 r2.
          FST (eval_to' (state c2 t2) e2) = r2
          ∧ QL (state c1 t1) (state c2 t2)
          ∧ res_rel (k - c1) QG r1 r2))
Termination
  WF_REL_TAC `inv_image ($< LEX $< LEX $<) (λx.
                case x of
                | INL (k, q, v1, v2) => (k, 0, v_size v1)
                | INR (INL (k, q, r1, r2)) => (k, 1, res_size v_size r1)
                | INR (INR (k, (ql, qg), e1, e2)) => (k, 2, exp_size e1))`
End

Definition var_rel_def:
  var_rel (k : fuel) (Q : inv) (sub1 : sigma) (sub2 : sigma)
          (x : string) (y : string) ⇔
    ∀v1. ALOOKUP sub1 x = SOME v1
         ⇒ ∃v2. ALOOKUP sub2 y = SOME v2
                ∧ val_rel k Q v1 v2
End

Definition subst_rel_def:
  subst_rel (k : fuel) (Q : inv) (S : string set)
            (sub1 : sigma) (sub2 : sigma) ⇔
    ∀x. x ∈ S ⇒ var_rel k Q sub1 sub2 x x
End

Definition top_rel_def:
  top_rel ((QL, QG) : inv # inv) (e1 : exp) (e2 : exp) ⇔
    ∀k sub1 sub2.
      subst_rel k QG (freevars e1) sub1 sub2
      ⇒ (freevars e1) ⊆ (set (MAP FST sub1))
      ⇒ exp_rel k (QL, QG) (subst sub1 e1) (subst sub2 e2)
End

Theorem eval_to'_oot_thm:
  ∀t e. eval_to' (state 0 t) e = (OOT, (state 0 t))
Proof
  rw []
  >> Cases_on `e`
  >~ [`Let x _ _`]
  >- (Cases_on `x`
      >> gvs [eval_to'_def, check_state_def, fuel_def, trace_def])
  >> gvs [eval_to'_def, check_state_def, fuel_def, trace_def]
QED

Theorem eval_to'_zero_thm:
  ∀t e r s'.
    eval_to' (state 0 t) e = (r, s')
    ⇒ r = OOT
Proof
  cheat
QED

Theorem rel_add_thm:
  (∀k c Q x x'.
    val_rel (k + c) Q x x'
    ⇒ val_rel k Q x x') ∧
  (∀k c Q r r'.
    res_rel (k + c) Q r r'
    ⇒ res_rel k Q r r') ∧
  (∀k c Qs e1 e2.
    exp_rel (k + c) Qs e1 e2
    ⇒ exp_rel k Qs e1 e2)
Proof
  cheat
QED

Theorem constr_compat_thm:
  ∀(k : fuel) (QL : inv) (QG : inv)
   (ys1 : string list) (ys2 : string list)
   (x1 : string) (x2 : string) (sub1 : sigma)
   (sub2 : sigma) (C : string)
   (e1 : exp) (e2 : exp).
    QL (state 0 0) (state 0 0)
    ∧ (∀c1 t1 c2 t2.
        QL (state c1 t1) (state c2 t2) 
        ⇒ QL (state (c1 + 1) t1) (state (c2 + 1) t2))
    ∧ (LIST_REL (var_rel k QG sub1 sub2) ys1 ys2)
    ∧ (∀vs1 vs2.
        LIST_REL (val_rel k QG) vs1 vs2
        ⇒ exp_rel k (QL, QG) (subst1 x1 (Constructor C vs1) e1)
                             (subst1 x2 (Constructor C vs2) e2))
    ⇒ exp_rel k (QL, QG)
        (Let (SOME x1) (Value $ Constructor C []) e1)
        (Let (SOME x2) (Value $ Constructor C []) e2)
    (*⇒ exp_rel k (QL, QG)
        ((Let (SOME x1) (Value $ Constructor C (MAP Var ys1)) e1))
        ((Let (SOME x2) (Value $ Constructor C (MAP Var ys2)) e2))*)
Proof
  cheat
  (*rw [rel_def]
  >> first_x_assum $ qspecl_then [`[]`, `[]`] assume_tac >> gvs []
  >> first_x_assum $ qspecl_then [`c1 - 2`, `t1`] assume_tac >> rfs []
  >> qexistsl [`c2 + 2`, `t2`] >> gvs []
  >> rw []
  >- (
      first_assum $ drule_then assume_tac
      >> simp []
      >> `c1 - 2 + 1 + 1 = c1` by
          (
          )
     ) 
  >- (ntac 2 (qmatch_asmsub_abbrev_tac `FST rt`
              >> Cases_on `rt`
              >> gvs [])
      >> ntac 2 (qmatch_goalsub_abbrev_tac `FST rt`
                 >> Cases_on `rt`
                 >> gvs [])
      >> gvs [AllCaseEqs(), eval_to'_def, check_state_def, fuel_def, trace_def,
              rel_def]
      >- (imp_res_tac eval_to'_zero_thm
          >> gvs [rel_def])
      >- (Cases_on `c1 = 1` >> gvs []   
          >> imp_res_tac eval_to'_zero_thm
          >> gvs [rel_def]
          >> Cases_on `q'` >> gvs [rel_def])
      >- (Cases_on `q` >> Cases_on `q'` >> gvs [rel_def]
          >> qspecl_then [`k - c1`, `2`] assume_tac (cj 1 rel_add_thm)
          >> gvs []))*)
QED

val _ = export_theory()

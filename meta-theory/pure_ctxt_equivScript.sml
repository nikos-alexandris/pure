
open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory stringTheory alistTheory optionTheory
     ltreeTheory llistTheory bagTheory pairTheory pred_setTheory;
open pure_evalTheory pure_exp_lemmasTheory pure_expTheory pure_congruenceTheory


val _ = new_theory "pure_ctxt_equiv";

Datatype:
  ctxt = Hole
       | Prim op (exp list) ctxt (exp list)
       | AppL ctxt exp
       | AppR exp ctxt
       | Lam vname ctxt
       | LetrecL ((vname # exp) list)
                  (vname # ctxt)
                 ((vname # exp) list) exp
       | LetrecR ((vname # exp) list) ctxt
End

Definition plug_def:
  plug Hole n = n ∧
  plug (Prim op xs1 h xs2) n = Prim op (xs1 ++ [plug h n] ++ xs2) ∧
  plug (AppL h y) n = App (plug h n) y ∧
  plug (AppR x h) n = App x (plug h n) ∧
  plug (Lam v h) n = Lam v (plug h n) ∧
  plug (LetrecL xs1 (f,h) xs2 x) n = Letrec (xs1 ++ [(f,plug h n)] ++ xs2) x ∧
  plug (LetrecR xs h) n = Letrec xs (plug h n)
End

Theorem exp_equiv_plug:
  ∀h x y. x ≅ y ⇒ plug h x ≅ plug h y
Proof
  recInduct plug_ind >> rw[plug_def]
  >- ( (* Prim *)
    irule exp_eq_Prim_cong >>
    irule LIST_REL_APPEND_suff >> simp[] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
  >- ( (* AppL *)
    irule exp_eq_App_cong >> simp[exp_eq_refl]
    )
  >- ( (* AppR *)
    irule exp_eq_App_cong >> simp[exp_eq_refl]
    )
  >- ( (* Lam *)
    irule exp_eq_Lam_cong >> simp[exp_eq_refl]
    )
  >- ( (* LetrecL *)
    irule exp_eq_Letrec_cong >> simp[exp_eq_refl] >>
    irule LIST_REL_APPEND_suff >> simp[] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
  >- ( (* LetrecR *)
    irule exp_eq_Letrec_cong >> simp[exp_eq_refl] >>
    rw[LIST_REL_EL_EQN, exp_eq_refl]
    )
QED

(****************************************)

Definition plug_ctxt_def:
  plug_ctxt Hole n = n ∧
  plug_ctxt (Prim op xs1 h xs2) n = Prim op xs1 (plug_ctxt h n) xs2 ∧
  plug_ctxt (AppL h y) n = AppL (plug_ctxt h n) y ∧
  plug_ctxt (AppR x h) n = AppR x (plug_ctxt h n) ∧
  plug_ctxt (Lam v h) n = Lam v (plug_ctxt h n) ∧
  plug_ctxt (LetrecL xs1 (f,h) xs2 x) n = LetrecL xs1 (f, plug_ctxt h n) xs2 x ∧
  plug_ctxt (LetrecR xs h) n = LetrecR xs (plug_ctxt h n)
End

Theorem plug_plug_ctxt:
  ∀c1 c2 e. plug (plug_ctxt c1 c2) e = plug c1 (plug c2 e)
Proof
  recInduct plug_ctxt_ind >> rw[plug_def, plug_ctxt_def]
QED

(****************************************)

val _ = export_theory();


open HolKernel Parse boolLib bossLib term_tactic;
open arithmeticTheory listTheory rich_listTheory stringTheory alistTheory
     optionTheory llistTheory;
open pure_evalTheory pure_valueTheory pure_expTheory pure_exp_lemmasTheory pure_miscTheory;

val _ = new_theory "pure_list_fusion";

(*********** Some PureCake programs *************)

Definition nil_def:
  nil = Prim (Cons "nil") []
End

Definition cons_def:
  cons xs = Prim (Cons "cons") xs
End

Definition LAMREC_def:
  LAMREC f v b = Lam v (Letrec [ (f,Lam v b) ] b)
End

(* map f [] = []
   map f (x::xs) = f x::map f xs *)
Definition map_def:
   map =
   LAMREC "MAP" "f"
             (Lam "l"
               (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [App (Var "f"  ) (Var "x" )
                                               ;App (App (Var "MAP") (Var "f")) (Var "xs")]
                    )
                   ])
             )
End

Definition map_f_def:
   map_f f =
   LAMREC "MAP_F" "l"
               (Case (Var "l") "v" [
                    ("nil" ,         [],  nil );
                    ("cons", ["x";"xs"],  cons [App f (Var "x")
                                               ;App (Var "MAP_F") (Var "xs")]
                    )
                   ])
End

Definition Apps_rev_def:
  Apps_rev [] = Fail                     ∧
  Apps_rev [x] = x                       ∧
  Apps_rev (x::xs) = App (Apps_rev xs) x
End

Definition Apps_def:
  Apps xs = Apps_rev (REVERSE xs)
End

(*
(*used to control recursive steps during the proofs*)
Theorem eval_LAMREC3:
  v≠f (*∧ closed (LAMREC f v b)*) ⇒
  eval (App (LAMREC f v b) y) =
       eval (App (Lam v ( subst f (LAMREC f v b) b) ) y)
Proof
  rpt strip_tac
  \\ fs[Once LAMREC_def]
  \\ fs[eval_thm]
  \\ fs[bind_def]
  \\ rw[]
  \\ fs[subst_def]
  \\ fs[eval_thm]
  \\ fs[subst_funs_def]
  \\ fs[bind_def,closed_def]
  \\ fs[eval_thm]
  \\ fs[subst_def]
  \\ fs[eval_Let]
  \\ fs[bind_def]
  \\ fs[LAMREC_def]
  \\ metis_tac [subst_swap]
QED

Theorem eval_LAMREC2:
  (*b has no other free variables except v and f*)
  (∀ k. MEM k (freevars b) ⇒ k = v ∨ k = f) ⇒
  eval (LAMREC f v b) = if closed (Lam v (Letrec [(f,v,b)] b))
                        then eval (Lam v ( Letrec [(f,v,b)] b ))
                        else Error
Proof
  rpt strip_tac
  \\ fs[Once LAMREC_def]
  \\ fs[eval_thm] \\ fs[closed_def,no_var_no_subst,freevars_subst_lemma_gen]
  \\ fs[FILTER_APPEND]
  \\ fs[FILTER_FILTER]
  \\ fs[AC CONJ_ASSOC CONJ_COMM]
  \\ rw[] \\ fs[FILTER_NEQ_NIL]
  \\ res_tac \\ fs[]
QED
*)

Triviality not_diverge_is_eq:
  x ≠ Diverge ⇒ is_eq s n x ≠ Diverge
Proof
  rw[] \\ Cases_on ‘x’ \\ fs[is_eq_def]
  \\ IF_CASES_TAC \\ fs[]
  \\ IF_CASES_TAC \\ fs[]
QED

Definition compose_def:
 compose f g = Lam "x" (App f (App g (Var "x")))
End

Definition next_list_def:
  next_list f input =
              if (¬closed input) then (INL Fail)
              else ( if eval input = Diverge then (INL bottom)
                     else (case eval input of
                           | Constructor n vs =>
                               (if n = "nil" ∧ LENGTH vs = 0
                                then (INL nil)
                                else (if n = "cons" ∧ LENGTH vs = 2
                                then (INR (n
                                           ,App f (Proj n 0 input)
                                           ,Proj n 1 input       ))
                                else (INL Fail))
                               )
                           | _ => (INL Fail)))
End


(* progress map f *)
Theorem progress_map_f:
  ∀ f. closed f ⇒ progress (App map f) (next_list f)
Proof
  cheat (* TODO
  rw[]
  \\ simp[progress_def] \\ rw[]
  \\ fs[exp_rel_def,eval_thm]
  \\ simp[map_def,LAMREC_def,cons_def,nil_def]
  \\ simp[bind_def,subst_def,subst_funs_def,eval_thm,closed_def]
  \\ reverse IF_CASES_TAC THEN1 (fs[next_list_def,closed_def,v_rel_refl])
  \\ simp[expandCases_def,expandRows_def,expandLets_def,eval_thm]
  \\ simp[bind_def,subst_def,subst_funs_def,eval_thm,closed_def,
          no_var_no_subst,is_eq_def,el_def,LNTH_2]
  \\ fs[next_list_def,closed_def]
  \\ Cases_on ‘eval input = Diverge’ THEN1 (fs[eval_thm,v_rel_refl,eval_bottom])
  \\ fs[]
  \\ Cases_on ‘eval input’ \\ fs[eval_thm,v_rel_refl]
  \\ Cases_on ‘s = "nil" ∧ t = []’ THEN1 (fs[eval_thm,nil_def,v_rel_refl])
  \\ Cases_on ‘s = "cons" ∧ LENGTH t = 2’ THEN1 (
    fs[eval_thm]
    \\ IF_CASES_TAC \\ fs[]
    \\ simp[bind_def,subst_def,subst_funs_def,eval_thm,closed_def,
            no_var_no_subst,is_eq_def,el_def,LNTH_2]
    \\ simp[expandCases_def,expandRows_def,expandLets_def,eval_thm]
    \\ simp[bind_def,subst_def,subst_funs_def,eval_thm,closed_def,
            no_var_no_subst,is_eq_def,el_def,LNTH_2]
    \\ IF_CASES_TAC \\ fs[v_rel_refl]
  )
  \\ fs[eval_thm,v_rel_refl]
  \\ Cases_on ‘s = "nil"’ \\ fs[]
  \\ Cases_on ‘s = "cons"’ \\ fs[]
  \\ fs[eval_thm,v_rel_refl]
  *)
QED

(* progress map f (cheap version)*)
Theorem progress_map_f_f:
  ∀ f. closed f ⇒ progress (map_f f) (next_list f)
Proof
  cheat (* TODO
  rw[]
  \\ fs[progress_def,exp_rel_def] \\ rw[]
  \\ fs[eval_thm]
  \\ fs[map_f_def,LAMREC_def,cons_def,nil_def]
  \\ fs[bind_def,subst_def,subst_funs_def,eval_thm,closed_def]
  \\ reverse IF_CASES_TAC THEN1 (fs[next_list_def,closed_def,v_rel_refl])
  \\ fs[next_list_def,closed_def]
  \\ fs[eval_thm,no_var_no_subst,bind_def,subst_def,subst_funs_def,closed_def]
  \\ fs[expandCases_def,expandRows_def,expandLets_def,eval_thm]
  \\ fs[eval_thm,no_var_no_subst,bind_def,subst_def,subst_funs_def,closed_def]
  \\ Cases_on ‘eval input = Diverge’ THEN1(fs[is_eq_def,eval_bottom,v_rel_refl])
  \\ fs [not_diverge_is_eq]
  \\ Cases_on ‘eval input’ \\ fs[eval_thm,v_rel_refl,is_eq_def]
  \\ Cases_on ‘s = "nil" ∧ t = []’ THEN1 (fs[eval_thm,nil_def,v_rel_refl])
  \\ Cases_on ‘s = "cons" ∧ LENGTH t = 2’ THEN1 (
    fs[eval_thm]
    \\ IF_CASES_TAC \\ fs[]
    \\ simp[bind_def,subst_def,subst_funs_def,eval_thm,closed_def,
            no_var_no_subst,is_eq_def,el_def,LNTH_2]
    \\ simp[expandCases_def,expandRows_def,expandLets_def,eval_thm]
    \\ simp[bind_def,subst_def,subst_funs_def,eval_thm,closed_def,
            no_var_no_subst,is_eq_def,el_def,LNTH_2]
    \\ IF_CASES_TAC \\ fs[v_rel_refl]
  )
  \\ fs[eval_thm,v_rel_refl]
  \\ Cases_on ‘s = "nil"’ \\ fs[]
  \\ Cases_on ‘s = "cons"’ \\ fs[]
  \\ fs[eval_thm,v_rel_refl]
  *)
QED

(*valid only within an exp_rel context*)
Triviality equational_reasoning:
  exp_rel e1 e2 ⇒ e1 = e2
Proof
  cheat
QED

Theorem progress_compose_fg:
  ∀ f g. closed f ∧ closed g
  ⇒ progress (compose (App map f) (App map g)) (next_list (compose f g))
Proof
  cheat (* TODO
  rw[]
  \\ ‘∀ h. closed h ⇒ exp_rel (App map h) (map_f h)’ by (
    rpt strip_tac
    \\ qspecl_then [‘next_list h’,‘map_f h’,‘App map h’]
             assume_tac (GEN_ALL progress_lemma)
    \\ assume_tac progress_map_f
    \\ assume_tac progress_map_f_f
    \\ res_tac
    \\ ‘isClos (eval (App map h))’ by (
       simp[map_def,LAMREC_def,cons_def,nil_def]
       \\ simp[eval_thm,bind_def,subst_def,subst_funs_def,closed_def]
       \\ simp[isClos_def]
    )
    \\ ‘isClos (eval (map_f h))’ by (
       simp[map_f_def,LAMREC_def,cons_def,nil_def]
       \\ simp[eval_thm,bind_def,subst_def,subst_funs_def,closed_def]
       \\ simp[isClos_def]
    )
    \\ res_tac
  )
  \\ first_assum (qspec_then ‘f’ assume_tac)
  \\ first_assum (qspec_then ‘g’ assume_tac)
  \\ res_tac
  \\ imp_res_tac equational_reasoning \\ fs[] (*morally correct*)
  \\ fs[compose_def,progress_def]
  \\ strip_tac
  \\ fs[exp_rel_def,eval_thm]
  \\ fs[bind_def,closed_def,subst_def]
  \\ Cases_on ‘¬closed input’ THEN1 (fs[next_list_def,closed_def,v_rel_refl])
  \\ fs[closed_def]
  \\ fs[map_f_def,LAMREC_def,cons_def]
  *)
QED

(*   (map f) o (map g) l = map (f o g) l   *)
Theorem map_fusion:
 ∀ f g. closed f ∧ closed g ⇒
      exp_rel (compose (App map f) (App map g)) (App map (compose f g))
Proof
  cheat (* TODO
  rw[]
  \\ ‘closed (compose f g)’ by (fs[compose_def,closed_def])
  \\ qspecl_then [‘next_list (compose f g)’,
                  ‘App map (compose f g)’,
                  ‘compose (App map f) (App map g)’]
          assume_tac (GEN_ALL progress_lemma)
  \\ qspec_then ‘compose f g’ assume_tac progress_map_f
  \\ qspecl_then [‘f’,‘g’] assume_tac progress_compose_fg
  \\ ‘isClos (eval (compose (App map f) (App map g)))’ by (
     simp[map_def,LAMREC_def,cons_def,nil_def,compose_def]
     \\ simp[eval_thm,bind_def,subst_def,subst_funs_def,closed_def]
     \\ simp[isClos_def]
  )
  \\ ‘isClos (eval (App map (compose f g)))’ by (
     simp[map_def,LAMREC_def,cons_def,nil_def,compose_def]
     \\ ‘freevars f = []’ by (fs[closed_def])
     \\ ‘freevars g = []’ by (fs[closed_def])
     \\ simp[eval_thm,bind_def,subst_def,subst_funs_def,closed_def]
     \\ simp[isClos_def]
  )
  \\ res_tac
  *)
QED


(*
Theorem deforestation:
  ∀ c l f g.
  closed f ∧ closed g ∧ closed l ∧
  f = Lam fn fb ∧ g = Lam gn ge
   ⇒
   exp_rel
     (*(map f) (map g l)*)
     (*Apps map [f;Apps map [g;l]]*)
     (App (App map f) (App (App map g) l))
     (*map (f.g) l*)
     (App (App map (App (App dot f) g)) l)
Proof
  rw[]
  \\ fs[exp_rel_def,v_rel_def,v_rel'_def] \\ strip_tac
  \\ fs [eval_thm]
  \\ ‘eval map ≠ Diverge’ by (cheat)
  \\ fs [map_def,eval_thm]
  \\ fs [bind_def]
  \\ fs [subst_def]
  \\ fs [eval_thm]
  \\ fs [closed_def]
  \\ fs [subst_def]
  \\ cheat
QED
*)


val _ = export_theory();
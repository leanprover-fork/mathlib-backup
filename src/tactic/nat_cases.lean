import tactic.interactive

open tactic
meta def get_nat_ineq : expr → tactic (expr × expr × ℕ)
| `(%%val < %%ebound) := prod.mk val <$> (prod.mk ebound <$> eval_expr ℕ ebound)
| `(%%val ≤ %%ebound) := prod.mk val <$> (prod.mk ebound <$> nat.succ <$> eval_expr ℕ ebound)
| _ := failed

namespace tactic.interactive
open lean.parser interactive
meta def nat_cases (h : parse ident) : tactic unit :=
focus1 $ do
  e ← get_local h,
  ⟨val, ⟨ebound, bound⟩⟩ ← infer_type e >>= get_nat_ineq,
  expr.local_const _ nval _ _ ← return val,
  iterate_at_most bound $ do {
      val ← get_local nval,
      cases_core val,
      clear_lst [h],
      swap },
  e ← get_local h,
  val ← get_local nval,
  proof ← to_expr ```(absurd %%e (not_lt_of_ge $ nat.le_add_left %%ebound %%val)),
  tactic.exact proof,
  goals ← get_goals,
  set_goals goals.reverse

end tactic.interactive

example (n : ℕ) (h : n ≤ 4) : n ≤ 10 :=
begin
  nat_cases h,
  do { goals ← get_goals, guard (goals.length = 5) },
  all_goals { exact dec_trivial},
end

example (n : ℕ) (h : n < 4) : n ≤ 10 :=
begin
  nat_cases h,
  do { goals ← get_goals, guard (goals.length = 4) },
  all_goals { exact dec_trivial},
end

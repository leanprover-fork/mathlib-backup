import data.fin order.basic
import category_theory.category
import tactic.split_ifs
import tactic.tidy tactic.linarith tactic.monotonicity

namespace fin
variables {n : ℕ}

@[extensionality] lemma le_ext {a b : fin n} (h : a.val ≤ b.val) : a ≤ b := h

attribute [extensionality] fin.eq_of_veq

end fin

inductive simplex_category
| from_nat : ℕ → simplex_category

namespace simplex_category

local notation ` [`n`] ` := from_nat n

instance : has_coe_to_sort simplex_category :=
{ S := Type,
  coe := λ n, simplex_category.cases_on n (λ n, fin $ n+1) }

instance {Δ : simplex_category} : linear_order Δ := by cases Δ; unfold_coes; apply_instance

instance : category_theory.category simplex_category :=
{ hom := λ Δ Δ', {f : Δ → Δ' // monotone f},
  id := λ _, ⟨_, monotone_id⟩,
  comp := λ _ _ _ f g, ⟨_, monotone_comp f.2 g.2⟩ }

@[extensionality] lemma hom_ext {Δ Δ' : simplex_category} {f g : Δ ⟶ Δ'} (h : f.1 = g.1) : f = g := by tidy

@[simp] lemma comp_val {Δ Δ' Δ'' : simplex_category} {f : Δ ⟶ Δ'} {g : Δ' ⟶ Δ''} : (f ≫ g).val = g.val ∘ f.val := rfl

def δ {n} (i : [n+1]) : [n] ⟶ [n+1] :=
{ val := fin.succ_above i,
  property := λ a b (H : a.val ≤ b.val),
    by dsimp [fin.succ_above]; split_ifs with ha hb; { ext1, simp [nat.succ_eq_add_one], linarith } }

/-- The i-th degeneracy map from [n+1] to [n] -/
def σ {n} (i : [n]) (a : [n+1]) : [n] :=
if h : a.val ≤ i.val
then a.cast_lt (lt_of_le_of_lt h i.is_lt)
else ⟨a.val.pred,
  (nat.sub_lt_right_iff_lt_add (lt_of_le_of_lt i.val.zero_le (not_le.mp h))).mpr a.is_lt⟩
  --a.pred sorry

lemma σ_monotone {n} (i : [n]) : monotone (σ i) :=
λ a b (H : a.val ≤ b.val),
begin
  unfold σ,
  split_ifs with ha hb;
  try { ext1, simp, linarith },
  { simp at hb,
    have hb' : i.val ≤ nat.pred b.val :=
    begin
      rw ←nat.pred_succ i.val,
      exact nat.pred_le_pred hb
    end,
    exact nat.le_trans ha hb' },
  { exact nat.pred_le_pred H }
end

lemma simplicial_identity₁ {n} {i j : [n+1]} (H : i ≤ j) : δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
begin
  change i.val ≤ j.val at H,
  ext,
  dsimp [δ, fin.succ_above],
  split_ifs; { try {ext1}, try {simp [nat.succ_eq_add_one] at *}, try {linarith} },
end

end simplex_category
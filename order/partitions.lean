import data.set.lattice

open function

variable {α : Type*}

namespace setoid

def top : setoid α :=
{ r := λ s₁ s₂, true,
  iseqv := by { unfold equivalence reflexive symmetric transitive,
    exact ⟨by { intro, trivial }, by { intros, trivial }, by { intros, trivial }⟩ }}

def bot : setoid α :=
{ r := (=),
  iseqv := by { unfold equivalence reflexive symmetric transitive,
    exact ⟨by { intro, refl }, by { intros, exact a.symm }, by { intros, exact eq.trans a a_1 }⟩ }}

theorem eq_iff_r_eq : ∀ {r₁ r₂ : setoid α}, r₁ = r₂ ↔ r₁.r = r₂.r
| ⟨r1, e1⟩ ⟨r2, e2⟩
:= begin
  intros,
  split,
  { intro h, injection h },
  { intro h, dsimp at h, subst h }
end

theorem eq_iff_eqv_class_eq {r₁ r₂ : setoid α} :
  r₁ = r₂ ↔ (∀ a, let r1 := r₁.r in let r2 := r₂.r in {b | r1 a b} = {b | r2 a b}) :=
begin
  rw eq_iff_r_eq,
  split,
  { intros h a r1 r2,
    have : r1 = r2 := h,
    rw this },
  { intro h,
    apply funext,
    exact h }
end

/- Should we do this without sets? The two definitions below are equivalent,
so maybe it doesn't matter -/
instance : has_subset (setoid α) :=
--⟨λ r₁ r₂, ∀ (a : α), let r1 := r₁.r in let r2 := r₂.r in ∀ b, r1 a b → r2 a b⟩
⟨λ r₁ r₂, ∀ (a : α), let r1 := r₁.r in let r2 := r₂.r in {b | r1 a b} ⊆ {b | r2 a b}⟩

theorem finer_def (r₁ r₂ : setoid α) : r₁ ⊆ r₂ ↔ ∀ (a : α), let r1 := r₁.r in
  let r2 := r₂.r in {b | r1 a b} ⊆ {b | r2 a b} :=
iff.rfl

@[simp] theorem subset.refl (r : setoid α) : r ⊆ r :=
by rw [finer_def]; exact assume _, set.subset.refl _

theorem subset.trans {r₁ r₂ r₃ : setoid α} : r₁ ⊆ r₂ → r₂ ⊆ r₃ → r₁ ⊆ r₃ :=
by iterate { rw [finer_def] }; exact assume h₁ h₂ a, set.subset.trans (h₁ a) (h₂ a)

theorem subset.antisymm {r₁ r₂ : setoid α} (H₁ : r₁ ⊆ r₂) (H₂ : r₂ ⊆ r₁) :
r₁ = r₂ :=
begin
  rw finer_def at H₁ H₂,
  rw eq_iff_eqv_class_eq,
  intro a,
  exact set.subset.antisymm (H₁ a) (H₂ a)
end

instance : has_ssubset (setoid α) := ⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

set_option pp.implicit true
protected def union (r₁ r₂ : setoid α) : setoid α :=
{ r := λ s₁ s₂, let r1 := r₁.r in let r2 := r₂.r in sorry, --need transitive closure
  iseqv := by { unfold equivalence reflexive symmetric transitive,
    sorry
  }}

instance : has_union (setoid α) :=
⟨setoid.union⟩

--theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl

@[simp] theorem subset_union_left (s t : setoid α) : s ⊆ s ∪ t := λ x, or.inl

@[simp] theorem subset_union_right (s t : setoid α) : t ⊆ s ∪ t := λ x, or.inr

theorem union_subset {s t r : setoid α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
by finish [finer_def, union_def]

protected def inter (r₁ r₂ : setoid α) : setoid α :=
{ r := λ s₁ s₂, let r1 := r₁.r in let r2 := r₂.r in r1 s₁ s₂ ∧ r2 s₁ s₂,
  iseqv := by { unfold equivalence reflexive symmetric transitive,
    exact ⟨(by { intros, exact ⟨r₁.2.1 x, r₂.2.1 x⟩ }),
      (by { intros, exact ⟨r₁.2.2.1 a.1, r₂.2.2.1 a.2⟩ }),
      (by { intros, exact ⟨r₁.2.2.2 a.1 a_1.1, r₂.2.2.2 a.2 a_1.2⟩ })⟩ }}

instance : has_inter (setoid α) :=
⟨setoid.inter⟩

theorem inter_def {r₁ r₂ : setoid α} : r₁ ∩ r₂ =
  { r := λ s₁ s₂, let r1 := r₁.r in let r2 := r₂.r in r1 s₁ s₂ ∧ r2 s₁ s₂,
  iseqv := by { unfold equivalence reflexive symmetric transitive,
    exact ⟨(by { intros, exact ⟨r₁.2.1 x, r₂.2.1 x⟩ }),
      (by { intros, exact ⟨r₁.2.2.1 a.1, r₂.2.2.1 a.2⟩ }),
      (by { intros, exact ⟨r₁.2.2.2 a.1 a_1.1, r₂.2.2.2 a.2 a_1.2⟩ })⟩ }} := rfl

@[simp] theorem inter_subset_left (r₁ r₂ : setoid α) : r₁ ∩ r₂ ⊆ r₁ :=
begin
  rw [finer_def, inter_def],
  intros,
  sorry
end

@[simp] theorem inter_subset_right (r₁ r₂ : setoid α) : r₁ ∩ r₂ ⊆ r₂ := λ x H, and.right H

theorem subset_inter {s t r : setoid α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by finish [finer_def, inter_def]

instance lattice_set : lattice.complete_lattice (setoid α) :=
{ lattice.complete_lattice .
  le           := (⊆),
  le_refl      := subset.refl,
  le_trans     := assume a b c, subset.trans,
  le_antisymm  := assume a b, subset.antisymm,

  lt           := (⊂),
  lt_iff_le_not_le := λ x y, iff.refl _,

  sup          := (∪),
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  sup_le       := assume a b c, union_subset,

  inf          := (∩),
  inf_le_left  := inter_subset_left,
  inf_le_right := inter_subset_right,
  le_inf       := assume a b c, subset_inter,

  top          := top,
  le_top       := assume s a h, trivial,

  bot          := bot,
  bot_le       := assume s a, false.elim,

  Sup          := λs, {a | ∃ t ∈ s, a ∈ t },
  le_Sup       := assume s t t_in a a_in, ⟨t, ⟨t_in, a_in⟩⟩,
  Sup_le       := assume s t h a ⟨t', ⟨t'_in, a_in⟩⟩, h t' t'_in a_in,

  Inf          := λs, {a | ∀ t ∈ s, a ∈ t },
  le_Inf       := assume s t h a a_in t' t'_in, h t' t'_in a_in,
  Inf_le       := assume s t t_in a h, h _ t_in }

/- We define a partition as a family of nonempty sets such that any element of α is contained in
exactly one set -/

variables (α) (r : setoid α)

/- Is there a way to set this up so that we talk about the equivalence classes via quot? -/
structure partition :=
(blocks : set (set α))
(empty_not_mem_blocks : ∅ ∉ blocks)
(blocks_partition : ∀ a, ∃ b, b ∈ blocks ∧ a ∈ b ∧ ∀ b' ∈ blocks, b ≠ b' → a ∉ b')

/- There is a partition associated to an equivalence relation on a set -/
def coe_of_setoid [setoid α] : partition α :=
{ blocks := {t | ∃ a, {b | a ≈ b} = t},
  empty_not_mem_blocks := by { rw [set.nmem_set_of_eq], intro h,
    exact exists.elim h (by { intros a ha, simp [set.eq_empty_iff_forall_not_mem] at ha,
      exact ha a (setoid.refl a) }) },
  blocks_partition := assume a, by {
    exact exists.intro ({b | a ≈ b}) (by {
      split,
      { exact exists.intro a (by { refl }) },
      { split,
        { simp },
        { intros x h₁ h₂,
          rw [ne, set.ext_iff] at h₂,
          intro H,
          rw [set.mem_set_of_eq] at h₁,
          exact exists.elim h₁ (by {
            intros a' ha',
            rw [set.ext_iff] at ha',
            have := (ha' a).mpr H,
            rw [set.mem_set_of_eq] at this,
            exact h₂ (by {
              intro a''',
              replace ha' := ha' a''',
              refine iff.trans _ ha',
              rw [set.mem_set_of_eq, set.mem_set_of_eq],
              rw [set.mem_set_of_eq] at ha',
              split, { intro h, exact setoid.trans this h },
              { intro h, exact setoid.trans (setoid.symm this) h } }) }) } } }) } }

end setoid
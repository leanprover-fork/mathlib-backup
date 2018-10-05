/- Given a finite set A (with decidable equality), construct the poset of partitions of A, as an
instance of some well-structured theory of finite posets. Prove that if |A|=3 then |Part(A)|=5.
Key points: the basic framework for dealing with finiteness and decidability.
-/
import data.fintype

variables {α : Type*} [decidable_eq α]

namespace finset

lemma inter_of_subset {A B : finset α} (h : A ⊆ B) : A ∩ B = A :=
by simp [ext]; exact λ a, iff.intro (λ H, H.1) (λ H, ⟨H, mem_of_subset h H⟩)

end finset

open finset
variable [fintype α]

variable (α)
-- should this be done with a fintype instead?
structure partition :=
(blocks : finset (finset α))
(blocks_nonempty : ∅ ∉ blocks)
(blocks_partition : ∀ a, ∃ b, b ∈ blocks ∧ a ∈ b ∧ ∀ b' ∈ blocks, b ≠ b' → a ∉ b')

variable {α}
-- should we define a finset.join (and add it to mathlib)?
def partition_of_disjoint_union {P : finset (finset α)} (h₁ : ∅ ∉ P)
(h₂ : (multiset.join (P.val.map (λ S, S.val))).to_finset = univ)
(h₃ : ∀ (b₁ b₂), b₁ ∈ P → b₂ ∈ P → b₁ ≠ b₂ → disjoint b₁ b₂) : partition α :=
by simp [ext] at h₂;
exact { blocks := P,
  blocks_nonempty := h₁,
  blocks_partition := assume (a : α),
    by replace h₂ : ∃ s, (∃ (a : finset α), a ∈ P.val ∧ a.val = s) ∧ a ∈ s := h₂ a;
    exact exists.elim h₂ (assume (b'' : multiset α)
      (hb'' : (∃ a : finset α, a ∈ P.val ∧ a.val = b'') ∧ a ∈ b''),
      exists.elim hb''.1 $ assume (b : finset α) (hb : b ∈ P.val ∧ b.val = b''),
        have hab : a ∈ b := hb.2.substr hb''.2,
        exists.intro b ⟨hb.1, hab, assume (b' : finset α) (hb' : b' ∈ P) (hbb' : b ≠ b'),
          by replace h₃ : disjoint b b' := h₃ b b' hb.1 hb' hbb';
          exact disjoint_left.mp h₃ hab⟩) }

theorem disjoint_union_of_partition (P : partition α) :
(multiset.join (P.1.val.map (λ S, S.val))).to_finset = univ ∧
∀ (b₁ b₂), b₁ ∈ P.1 → b₂ ∈ P.1 → b₁ ≠ b₂ → disjoint b₁ b₂ :=
begin
  simp [ext],
  split,
  { intro a,
      have hP := P.blocks_partition a,
      exact exists.elim hP (by { intros b hb,
        exact exists.intro b.1 ⟨exists.intro b ⟨hb.1, rfl⟩, hb.2.1⟩ }) },
  { intros b₁ b₂ hb₁ hb₂ h,
    rw ←ext at h,
    have HP : ∅ ∉ P.blocks := P.blocks_nonempty,
    have hP' := P.blocks_partition,
    have Hb₁ : b₁ ≠ ∅ := by { intro h', exact (h'.symm ▸ HP) hb₁ },
    refine disjoint_left.mpr _,
    intros a ha,
    replace hP' := hP' a,
    exact exists.elim hP' (by { intros b' hb',
      have Hb' : b' = b₁ := by { have := mt (hb'.2.2 b₁ hb₁), simp at this, exact this ha },
      exact hb'.2.2 b₂ hb₂ (Hb'.symm ▸ h) }) }
end

instance decidable_disjoint (A B : finset α) : decidable (disjoint A B) :=
by unfold disjoint; apply_instance

namespace partition

@[simp] theorem eq_of_blocks_eq : ∀ {P₁ P₂ : partition α}, P₁ = P₂ ↔ P₁.1 = P₂.1
| ⟨_, _, _⟩ ⟨_, _, _⟩ :=
by simp

/- extensionality -/
theorem ext {P₁ P₂ : partition α} : P₁ = P₂ ↔ ∀ b, b ∈ P₁.1 ↔ b ∈ P₂.1 :=
by simp only [eq_of_blocks_eq, ext]

@[extensionality]
theorem ext' {P₁ P₂ : partition α} : (∀ b, b ∈ P₁.1 ↔ b ∈ P₂.1) → P₁ = P₂ :=
ext.2

def is_partition (P : finset (finset α)) : Prop :=
∅ ∉ P ∧ (multiset.join (P.val.map (λ S, S.val))).to_finset = univ ∧ ∀ b₁∈ P, ∀ b₂ ∈ P,
b₁ ≠ b₂ → disjoint b₁ b₂

instance decidable_partition (P : finset (finset α)) :
decidable (is_partition P) :=
by unfold is_partition; apply_instance

variable (α)
def partitions : finset (finset (finset α)) :=
(powerset (powerset univ)).filter (λ S, is_partition S)

theorem card_partitions_eq_card_partitions_fin {n : ℕ} (h : fintype.card α = n) :
card (partitions α) = card (partitions (fin n)) :=
begin
  rw ←h,
  have hcard := (fintype.equiv_fin α),
  sorry
end

variable {α}
theorem card_partitions_3 : card (partitions (fin 3)) = 5 :=
dec_trivial

theorem card_partitions_eq_5_of_card_3 (h : fintype.card α = 3) : card (partitions α) = 5 :=
(card_partitions_eq_card_partitions_fin α h).symm ▸ card_partitions_3

instance : has_subset (partition α) :=
⟨λ P₁ P₂, ∀ p ∈ P₁.1, ∃ q, q ∈ P₂.1 ∧ p ⊆ q⟩

theorem finer_def (P₁ P₂ : partition α) : P₁ ⊆ P₂ ↔ ∀ p ∈ P₁.1,
∃ q, q ∈ P₂.1 ∧ p ⊆ q :=
iff.rfl

instance decidable_finer (P₁ P₂ : partition α) : decidable (P₁ ⊆ P₂) :=
by rw [finer_def]; exact decidable_of_iff (∀ p ∈ P₁.1, ∃ q ∈ P₂.1, p ⊆ q) (by simp)

@[simp] theorem subset.refl (P : partition α) : P ⊆ P :=
by rw [finer_def]; exact assume (p : finset α) (H : p ∈ P.1), exists.intro p ⟨H, subset.refl p⟩

theorem subset.trans {s₁ s₂ s₃ : partition α} : s₁ ⊆ s₂ → s₂ ⊆ s₃ → s₁ ⊆ s₃ :=
by iterate { rw finer_def };
exact assume (h₁ : ∀ p ∈ s₁.1, ∃ q, q ∈ s₂.1 ∧ p ⊆ q)
  (h₂ : ∀ p ∈ s₂.1, ∃ q, q ∈ s₃.1 ∧ p ⊆ q) (p : finset α) (hp : p ∈ s₁.1),
  exists.elim (h₁ p hp : ∃ q, q ∈ s₂.1 ∧ p ⊆ q)
    (assume (p' : finset α) (hp' : p' ∈ s₂.blocks ∧ p ⊆ p'),
    exists.elim (h₂ p' hp'.1 : ∃ q, q ∈ s₃.1 ∧ p' ⊆ q) $
      assume (p'' : finset α) (hp'' : p'' ∈ s₃.blocks ∧ p' ⊆ p''),
      exists.intro p'' ⟨hp''.1, subset.trans hp'.2 hp''.2⟩)

theorem subset.antisymm {s₁ s₂ : partition α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) :
s₁ = s₂ :=
begin
  rw finer_def at H₁ H₂,
  have hs₁ := disjoint_union_of_partition s₁, have hs₂ := disjoint_union_of_partition s₂,
  ext,
  exact iff.intro (assume (h : b ∈ s₁.blocks),
    exists.elim (H₁ b h) $
      assume (b' : finset α) (hb' : b' ∈ s₂.blocks ∧ b ⊆ b'),
      have ∃ q, q ∈ s₁.blocks ∧ b' ⊆ q := H₂ b' hb'.1,
      exists.elim this $ by { assume (b'' : finset α) (hb'' : b'' ∈ s₁.blocks ∧ b' ⊆ b''),
        replace hs₁ := mt (hs₁.2 b b'' h hb''.1), simp at hs₁,
        have : b = b'' := by { refine hs₁ _,
          have : b ⊆ b'' := finset.subset.trans hb'.2 hb''.2,
          have hinter : b ∩ b'' = b := inter_of_subset this,
          have hbne : b ≠ ∅ := by { by_contra H, simp at H,
            exact s₁.blocks_nonempty (H ▸ h) },
          replace hinter := hinter.substr hbne,
          exact (mt disjoint_iff_inter_eq_empty.mp) hinter },
        have b'b : b' = b := subset.antisymm (this.symm ▸ hb''.2) (hb'.2),
        exact b'b ▸ hb'.1 })
    (assume (h : b ∈ s₂.blocks), exists.elim (H₂ b h) $
      assume (b' : finset α) (hb' : b' ∈ s₁.blocks ∧ b ⊆ b'),
      have ∃ q, q ∈ s₂.blocks ∧ b' ⊆ q := H₁ b' hb'.1,
      exists.elim this $ by { assume (b'' : finset α) (hb'' : b'' ∈ s₂.blocks ∧ b' ⊆ b''),
        replace hs₂ := mt (hs₂.2 b b'' h hb''.1), simp at hs₂,
        have : b = b'' := by { refine hs₂ _,
          have : b ⊆ b'' := finset.subset.trans hb'.2 hb''.2,
          have hinter : b ∩ b'' = b := inter_of_subset this,
          have hbne : b ≠ ∅ := by { by_contra H, simp at H,
            exact s₂.blocks_nonempty (H ▸ h) },
          replace hinter := hinter.substr hbne,
          exact (mt disjoint_iff_inter_eq_empty.mp) hinter },
        have b'b : b' = b := subset.antisymm (this.symm ▸ hb''.2) (hb'.2),
        exact b'b ▸ hb'.1 })
end

instance : has_ssubset (partition α) := ⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

instance partial_order_of_partitions : partial_order (partition α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _ _ _,
  le_antisymm := @subset.antisymm _ _ _ }

instance lattice_of_partitions : lattice.lattice (partition α) := sorry

end partition

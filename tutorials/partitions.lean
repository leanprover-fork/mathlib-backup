/- Given a finite set A (with decidable equality), construct the poset of partitions of A, as an
instance of some well-structured theory of finite posets. Prove that if |A|=3 then |Part(A)|=5.
Key points: the basic framework for dealing with finiteness and decidability. -/
import data.fintype

variables {α : Type*} [decidable_eq α]

namespace finset
/- In lean + mathlib, `finset α` is the type of finite sets consisting of elements of type α. They
are implemented as structures with two records, `val : multiset α` and `nodup` which is a proof that
`val` contains no duplicates. Multisets are implemented as a quotient type of lists modulo
permutations. The main file for finsets is data.finset, which is a dependency of data.fintype. We
will discuss fintypes soon. -/

lemma inter_of_subset {A B : finset α} (h : A ⊆ B) : A ∩ B = A :=
by simp [ext]; exact λ a, iff.intro (λ H, H.1) (λ H, ⟨H, mem_of_subset h H⟩)
/- A preliminary and rather obvious lemma, which nonetheless needs a proof; note the use of
`simp [ext]`, where `ext` stands for "extensionality":

finset.ext : ∀ {α : Type ?} {s₁ s₂ : finset α}, s₁ = s₂ ↔ ∀ (a : α), a ∈ s₁ ↔ a ∈ s₂

This is a very useful theorem as it turns equality of finsets into membership questions, which are
often easier to handle. -/

/- The following #eval statements show how we can use lean to do basic manipulations on explicit
finsets of natural numbers -/
#eval ({1, 3, 4} ∩ {1} = ({1} : finset ℕ) : bool) -- tt
#eval ({1, 3, 4} ∩ {1} : finset ℕ) -- {1}
#eval ({3, 4} ∩ {1} : finset ℕ) -- {}
#eval ({1, 3, 4} ∪ {1} : finset ℕ) -- {1, 3, 4}
#eval card ({1, 3, 4, 9, 0} : finset ℕ) -- 5

/- The following instance is needed so that mathlib is able to computably decide whether two
finsets are disjoint or not. -/
instance decidable_disjoint {β : Type*} [decidable_eq β] {A B : finset β} :
decidable (disjoint A B) :=
by unfold disjoint; apply_instance

/- The following computed examples rely on the above instance to work properly -/
#eval (disjoint {1, 2, 3} ({1} : finset ℕ) : bool) -- ff
#eval (disjoint {0, 2, 3} ({1} : finset ℕ) : bool) -- tt

end finset

open finset fintype
variable [fintype α]
/- A fintype is a type with only finitely many distinct terms. We will see that this is a convenient
stand-in for the underlying finite set of our partition. -/

variable (α)

/- The following definition of a partition is based on the one in wikipedia:
https://en.wikipedia.org/wiki/Partition_of_a_set#Definition,
which is taken from Halmos's Naïve Set Theory,
"A partition of a set X is -/
structure partition :=
/- a set of nonempty subsets of X  -/
(blocks : finset (finset α))
(empty_not_mem_blocks : ∅ ∉ blocks)
/- such that every element x in X is in exactly one of these subsets." -/
(blocks_partition : ∀ a, ∃ b, b ∈ blocks ∧ a ∈ b ∧ ∀ b' ∈ blocks, b ≠ b' → a ∉ b')
/- We could have taken the above definition more literally and defined a partition as a
type dependent on X : finset α. If we had done so, we would have needed an extra record in the
above definition to ensure that the elements of `blocks` are actually all subsets of X and don't
contain anything from "outside", e.g.:

structure partition (X : finset α) :=
(blocks : ... ) (blocks_nonempty : ...) (blocks_partition : ...)
(blocks_contained : ∀ S ∈ blocks, S ⊆ X)

or the different-looking but ultimately equivalent

structure partition (X : finset α) :=
(blocks : ... ) (blocks_nonempty : ...) (blocks_partition : ...)
(blocks_subset_powerset : blocks ⊆ powerset X)

The declaration `fintype α` above allowed us to be more economical; since
blocks : finset (finset α), there cannot be anything from "outside" by definition. -/

/- The following instance tells lean how to "print" a partition, if its underlying fintype α has
a way of being printed, since finsets of types with `has_repr` can be printed. -/
instance partition_repr [has_repr α] : has_repr (partition α) :=
⟨λ P, has_repr.repr P.blocks⟩

variable {α}

/- The following two theorems formalize the equivalence of the second definition from wikipedia,
for which they cite Lucas, "Introduction to Abstract Mathematics":
"Equivalently, a family of sets P is a partition of X if and only if all of the following
conditions hold:

- The family P does not contain the empty set (that is ∅ ∉ P).
- The union of the sets in P is equal to X (that is ⋃ A ∈ P A = X). The sets in P are said to cover
  X.
- The intersection of any two distinct sets in P is empty
  (that is ( ∀ A , B ∈ P ) A ≠ B ⟹ A ∩ B = ∅). The elements of P are said to be pairwise
  disjoint.
-/

-- should we define a finset.join (and add it to mathlib)?

/- The following is the nontrivial-part of the only-if direction of the above alternate
characterization of a finite set partition. To formalize the second condition above, we apply the
`multiset.join` operation, which is the (multiplicity-preserving) union of multisets. `data.finset`
does contain a pairwise union operation but not a union over a finset of finsets. Note that `univ`
is the finset consisting of all elements of type α.

The proof has been written out in a relatively relaxed tactic style so that you can see how the
tactic state changes in your favorite editor with lean-integration. -/
theorem disjoint_union_of_partition (P : partition α) :
P.1.sup id = univ ∧
∀ (b₁ b₂), b₁ ∈ P.1 → b₂ ∈ P.1 → b₁ ≠ b₂ → disjoint b₁ b₂ :=
begin
  simp [ext],
  split,
  { intro a,
      have hP := P.blocks_partition a,
      exact exists.elim hP (by { intros b hb,
        exact exists.intro b ⟨hb.1, hb.2.1⟩ }) },
  { intros b₁ b₂ hb₁ hb₂ h,
    rw ←ext at h,
    have HP : ∅ ∉ P.blocks := P.empty_not_mem_blocks,
    have hP' := P.blocks_partition,
    have Hb₁ : b₁ ≠ ∅ := by { intro h', exact (h'.symm ▸ HP) hb₁ },
    refine disjoint_left.mpr _,
    intros a ha,
    replace hP' := hP' a,
    exact exists.elim hP' (by { intros b' hb',
      have Hb' : b' = b₁ := by { have := mt (hb'.2.2 b₁ hb₁), simp at this, exact this ha },
      exact hb'.2.2 b₂ hb₂ (Hb'.symm ▸ h) }) }
end

/- The following definition provides the "if" direction of the equivalence. Given the hypotheses
h₁, h₂, h₃ (which correspond to the three conditions above), this produces (computably!) a term of
type `partition α`.

Almost all of the proof is devoted to showing that blocks_partition is satisfied. The proof of that
proceeds fairly mechanically. First we simplify h₂ a bit and then eliminate the two nested "exists"
that appear. (The type of the simplified h₂ is written out explicitly after the replace statement.)
Then the desired existence statement is not hard to prove after using `disjoint_left`. This proof
has been slightly condensed ("golfed") into term mode, though more explicit type ascriptions are
provided to help with readability. -/
def partition_of_disjoint_union {P : finset (finset α)} (h₁ : ∅ ∉ P)
(h₂ : P.sup id = univ)
(h₃ : ∀ (b₁ b₂), b₁ ∈ P → b₂ ∈ P → b₁ ≠ b₂ → disjoint b₁ b₂) : partition α :=
by simp [ext] at h₂;
exact { blocks := P,
  empty_not_mem_blocks := h₁,
  blocks_partition := assume (a : α),
    by replace h₂ : ∃ b, b ∈ P ∧ a ∈ b := h₂ a;
    exact exists.elim h₂ (assume (b : finset α)
      (hb : b ∈ P ∧ a ∈ b),
      and.elim hb $ assume (hb : b ∈ P) (hab : a ∈ b),
        exists.intro b ⟨hb,hab,assume (b' : finset α) (hb' : b' ∈ P) (hbb' : b ≠ b'),
          by replace h₃ : disjoint b b' := h₃ b b' hb hb' hbb';
          exact disjoint_left.mp h₃ hab⟩) }

namespace partition

/- The next three theorems lay some basic groundwork for showing the equality of two partitions.
They are based on the corresponding theorems in `data.finset`. -/

/- This theorem proves that two partitions are equal if and only if their "blocks" are equal. This
follows in Lean because of "proof irrelevance" for terms of type Prop. -/
@[simp] theorem eq_of_blocks_eq : ∀ {P₁ P₂ : partition α}, P₁ = P₂ ↔ P₁.1 = P₂.1
| ⟨_, _, _⟩ ⟨_, _, _⟩ :=
by simp

/- This is a version of extensionality for partitions; two partitions P₁ P₂ are equal if and only if
(a finset b is a block of P₁ iff it is a block of P₂.) -/
theorem ext {P₁ P₂ : partition α} : P₁ = P₂ ↔ ∀ b, b ∈ P₁.1 ↔ b ∈ P₂.1 :=
by simp only [eq_of_blocks_eq, ext]

/- This version of ext is the form suitable for use by the `ext` tactic. -/
@[extensionality]
theorem ext' {P₁ P₂ : partition α} : (∀ b, b ∈ P₁.1 ↔ b ∈ P₂.1) → P₁ = P₂ :=
ext.2

/- This definition tells us when a finset of finsets is actually a partition. It uses the second
(disjoint union) definition of partitions. -/
def is_partition (P : finset (finset α)) : Prop :=
∅ ∉ P ∧ P.sup id = univ ∧ ∀ b₁ b₂, b₁∈ P → b₂ ∈ P → b₁ ≠ b₂ → disjoint b₁ b₂

/- This instance now allows us to use #eval to figure out whether a finset is a partition of the
underlying fintype or not. -/
instance decidable_partition (P : finset (finset α)) :
decidable (is_partition P) :=
by unfold is_partition; apply_instance

/- For our explicit examples below, our underlying fintype will be `fin n` where n : ℕ. This is
the fintype corresponding to the set {0, 1, …, n-1}. -/
#eval (is_partition ({{0}, {1}, {2, 3}} : finset (finset (fin 4))) : bool) -- tt
#eval (is_partition ({{0}, {1}, {2, 3}} : finset (finset (fin 5))) : bool) -- ff
#eval (is_partition ({{0}, {1}, {3}} : finset (finset (fin 4))) : bool) -- ff
#eval (is_partition ({{0}, {1}, {1,3}} : finset (finset (fin 4))) : bool) -- ff

/- This convenience function lets us create a partition from `is_partition`. -/
def of_is_partition {P : finset (finset α)} (h : is_partition P) : (partition α) :=
partition_of_disjoint_union h.1 h.2.1 h.2.2

/- We have been using #eval to determine the truth values of decidable propositions. The term
`dec_trivial` allows us to use computation (in the kernel) as a proof; it is useful, but limited
to computations that can be completed before the short timeout. We use it to define a few explicit
partitions of `fin 4` that we will use as running examples. -/
def P0 : partition (fin 4) :=
of_is_partition (dec_trivial : is_partition ({{0}, {1}, {2, 3}} : finset (finset (fin 4))))

def P1 : partition (fin 4) :=
of_is_partition (dec_trivial : is_partition ({{0}, {1}, {2}, {3}} : finset (finset (fin 4))))

def P2 : partition (fin 4) :=
of_is_partition (dec_trivial : is_partition ({{0, 1}, {2}, {3}} : finset (finset (fin 4))))

#eval P0 -- {{0}, {1}, {2, 3}}
#eval P1 -- {{0}, {1}, {2}, {3}}
#eval P2 -- {{0, 1}, {2}, {3}}

variable (α)

/- This creates the finset of all partitions of α by filtering on the elements of the powerset of
the powerset of `univ`. -/
def partitions : finset (finset (finset α)) :=
(powerset (powerset univ)).filter (λ S, is_partition S)

#eval partitions (fin 3)
-- {{{0, 1, 2}}, {{0, 1}, {2}}, {{0, 2}, {1}}, {{0}, {1, 2}}, {{0}, {1}, {2}}}
/- Unfortunately, computing the partitions of fin 4 causes a timeout with this naive definition. -/

lemma mem_partitions (x : finset (finset α)) : x ∈ partitions α ↔ is_partition x :=
by simp [partitions]

/- The goal of the next few theorems is to prove the following inocuous looking statement:

The number of partitions of a set of size `n` is equal to the number of partitions of the set
{0, 1, …, n-1}.

Of the results in this file, this is in some sense the "hardest" one to deal with in lean. This may
be surprising, since it seems so trivial. The reason for the mismatch is that the essence of this
statement is a "transport of structure" operation -- given a bijection betwen two fintypes, we need
to show that the partitions are also in bijection. As human mathematicians, this is completely
obvious; however, this is something which is not (yet) completely trivial in lean. It is hoped that
automation will be able to dispose of such results in the future.

An additional wrinkle is the fact that we will not have an explicit bijection, but rather only the
existence of one. We will apply a trick using one of lean's quotient axioms (akin to the use of the
axiom of choice). -/

variables {α} {β : Type*} [decidable_eq β] [fintype β]

open equiv

def partitions_congr (h : α ≃ β) :
  to_set (partitions α) ≃ to_set (partitions β) :=
begin
  simp [partitions,set.mem_powerset_iff],
  let f : finset (finset α) ≃ finset (finset β) := finset_equiv_of_equiv
    (finset_equiv_of_equiv h),
  apply set.coe_equiv_of_iff f,
  intros, dsimp [(∈)], simp only [set.mem,is_partition],
  apply and_congr,
  { dsimp [f,finset_equiv_of_equiv],
    simp only [coe_fn_mk,exists_prop,exists_eq_right,mem_map,
               to_embedding_coe_fn,map_eq_empty] },
  apply and_congr,
  { dsimp [f,finset_equiv_of_equiv],
    simp only [sup_map,to_embedding_coe_fn,
               coe_fn_mk,function.comp.left_id],
    rw [sup_hom' (map _),map_eq_iff_of_equiv],
    simp only [map_univ], apply_instance },
  { dsimp [f,finset_equiv_of_equiv,mem_map], simp [disjoint_iff],
    split; introv h₀ h₁ h₂ h₃,
    { intros h₄ h₅,
      subst b₁, subst b₂,
      specialize h₀ _ _ h₁ h₃ _,
      { rw [← map_inter,h₀], exact map_empty _ },
      intro h, subst h, contradiction, },
    { specialize h₀ _ _ _ h₁ rfl _ h₂ rfl _,
      { rw [← map_inter,map_eq_iff_of_equiv] at h₀, rw h₀,
        exact map_empty _ },
      intro h, apply h₃ (map_inj_of_embedding _ h) } }
end

theorem card_partitions_eq_card_partitions_fin {n : ℕ} (h : fintype.card α = n) :
card (partitions α) = card (partitions (fin n)) :=
begin
  rw ←h,
  refine trunc.induction_on (fintype.equiv_fin α) _, intro this,
  apply card_eq_of_equiv,
  apply partitions_congr,
  apply this,
end

theorem card_partitions_3 : card (partitions (fin 3)) = 5 :=
dec_trivial

theorem card_partitions_eq_5_of_card_3 (h : fintype.card α = 3) : card (partitions α) = 5 :=
(card_partitions_eq_card_partitions_fin h).symm ▸ card_partitions_3

/- We now begin to define a partial order structure on the type `partition α`.
For two partitions P₁ and P₂, we say that P₁ is finer than P₂ (written here as P₁ ⊆ P₂) if
every element of P₁.blocks is a subset of some element of P₂.blocks.

The following theorems and proofs imitate those in `data.finset` which define the partial order
structure on finset given by the subset relation. -/
instance : has_subset (partition α) :=
⟨λ P₁ P₂, ∀ p ∈ P₁.1, ∃ q, q ∈ P₂.1 ∧ p ⊆ q⟩

theorem finer_def (P₁ P₂ : partition α) : P₁ ⊆ P₂ ↔ ∀ p ∈ P₁.1,
∃ q, q ∈ P₂.1 ∧ p ⊆ q :=
iff.rfl

instance decidable_finer (P₁ P₂ : partition α) : decidable (P₁ ⊆ P₂) :=
by rw [finer_def]; exact decidable_of_iff (∀ p ∈ P₁.1, ∃ q ∈ P₂.1, p ⊆ q) (by simp)

#eval (P0 ⊆ P1 : bool) -- ff
#eval (P1 ⊆ P0 : bool) -- tt
#eval (P1 ⊆ P2 : bool) -- tt
#eval (P0 ⊆ P2 : bool) -- ff
#eval (P2 ⊆ P0 : bool) -- ff

/- The next three theorems prove the reflexivity, transitivity, and antisymmetry properties of the
partition (⊆) relation. -/

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
            exact s₁.empty_not_mem_blocks (H ▸ h) },
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
            exact s₂.empty_not_mem_blocks (H ▸ h) },
          replace hinter := hinter.substr hbne,
          exact (mt disjoint_iff_inter_eq_empty.mp) hinter },
        have b'b : b' = b := subset.antisymm (this.symm ▸ hb''.2) (hb'.2),
        exact b'b ▸ hb'.1 })
end

instance : has_ssubset (partition α) := ⟨λa b, a ⊆ b ∧ ¬ b ⊆ a⟩

/- This instance sets up the poset structure on `partitions α` -/
instance partial_order_of_partitions : partial_order (partition α) :=
{ le := (⊆),
  lt := (⊂),
  le_refl := subset.refl,
  le_trans := @subset.trans _ _ _,
  le_antisymm := @subset.antisymm _ _ _ }

/- As a bonus, we show that there is a lattice structure on partitions... -/
instance lattice_of_partitions : lattice.lattice (partition α) := sorry

end partition
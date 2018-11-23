import order.basic algebraic_topology.simplex_category data.finset data.finsupp algebra.group
import algebra.group_power tactic.abel
import category_theory.opposites category_theory.functor_category
import linear_algebra.basic

universes u v w

namespace finset
local attribute [instance] classical.prop_decidable

variables {X : Type u} {M : Type v}
variables {R : Type w} [ring R] [add_comm_group M] [module R M]
include R

def sum_smul' (s : finset X) (f : X → M) (r : R) : s.sum (λ x, r • f x) = r • s.sum f :=
finset.induction_on s (by simp) $ λ x s hx H,
begin
  repeat {erw sum_insert hx},
  simp [H, smul_add]
end

end finset

namespace finsupp
noncomputable theory
local attribute [instance] classical.prop_decidable

variables {X Y : Type u} {M : Type v}

local attribute [instance] finsupp.to_module

@[simp] lemma single_neg [add_comm_group M] {x : X} {m : M} : single x (-m) = -single x m :=
ext $ λ x', by simp [single_apply]; split_ifs; simp

def linear_extension [add_comm_monoid M] (f : X → M → Y →₀ M) (s : X →₀ M) : Y →₀ M :=
s.sum $ f

namespace linear_extension

instance [add_comm_monoid M] {f : X → M → Y →₀ M} (h₁ : ∀ (x : X), f x 0 = 0) (h₂ : ∀ (x : X) (m₁ m₂ : M), f x (m₁ + m₂) = f x m₁ + f x m₂) :
is_add_monoid_hom $ linear_extension f :=
{ map_zero := rfl,
  map_add  := λ s₁ s₂, finsupp.sum_add_index h₁ h₂ }

instance [add_comm_group M] {f : X → M → Y →₀ M} (h : ∀ (x : X), is_add_group_hom $ f x) :
is_add_group_hom $ linear_extension f :=
{ add := (linear_extension.is_add_monoid_hom (λ x, is_add_group_hom.zero (f x)) (λ x, (h x).add)).map_add }

variables {R : Type w} [ring R] [add_comm_group M] [module R M]
include R

instance is_linear_map {f : X → M → Y →₀ M} (h : ∀ (x : X), is_linear_map $ f x) :
is_linear_map $ linear_extension f :=
{ add  := (linear_extension.is_add_group_hom (λ x, ⟨(h x).add⟩)).add,
  smul := λ r s,
  begin
    dsimp [linear_extension],
    erw [finsupp.sum_map_range_index _],
    { rw show sum s (λ (a : X) (b : M), f a (r • b)) = sum s (λ (a : X) (b : M), r • (f a b)),
      begin
        congr, funext, exact is_linear_map.smul _ _ _
      end,
      dsimp [sum],
      erw ←finset.sum_smul' (s.support) (λ (a : X), f a (s a)) r },
    { intro x,
      rw [← zero_smul (0 : M), is_linear_map.smul (f x) _],
      exact zero_smul _ }
  end }

end linear_extension

end finsupp

open category_theory

local notation ` [`n`] ` := simplex_category.from_nat n

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

def simplicial_object := simplex_categoryᵒᵖ ⥤ C

variable {C}

namespace simplicial_object

instance : category (simplicial_object C) := functor.category _ _

/-- The i-th face map of a simplicial set -/
def δ (X : simplicial_object C) {n : ℕ} (i : [n+1]) := X.map (simplex_category.δ i)

lemma simplicial_identity₁ {X : simplicial_object C} {n : ℕ} {i j : [n + 1]} (H : i ≤ j) :
(X.δ j.succ) ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j :=
by {dsimp [δ], erw [←X.map_comp, simplex_category.simplicial_identity₁, X.map_comp], assumption}

end simplicial_object

omit 𝒞

/-- Simplicial set -/
def simplicial_set := simplicial_object (Type u)

namespace simplicial_set
noncomputable theory
local attribute [instance] classical.prop_decidable

open finset finsupp

variables (X : simplicial_set) {n : ℕ}
variables {M : Type u} [add_comm_group M]

def boundary (x : X.obj [n+1]) (m : M) : X.obj [n] →₀ M :=
sum univ $ λ i : [n+1], single (X.δ i x) $ gsmul ((-1 : ℤ)^i.val) m

instance boundary.is_add_group_hom (x : X.obj [n+1]) : is_add_group_hom (boundary X x : M → X.obj [n] →₀ M) :=
{ add := λ m₁ m₂, by finish [simplicial_set.boundary, finset.sum_add_distrib, finset.sum_congr rfl, single_add, gsmul_add] }

end simplicial_set

section simplicial_complex

variables (R : Type u) [ring R]
variables (M : Type u) [add_comm_group M] [module R M]
variables (X : simplicial_set) (n : ℕ)

/-- The simplicial complex associated with a simplicial set -/
def simplicial_complex := X.obj [n] →₀ M

end simplicial_complex

namespace simplicial_complex
noncomputable theory
local attribute [instance] classical.prop_decidable
open finset finsupp simplicial_object group

local attribute [instance] finsupp.to_module

variables (R : Type u) [comm_ring R]
variables (M : Type u) [add_comm_group M] [module R M]
variables (X : simplicial_set) (n : ℕ)

instance : add_comm_group (simplicial_complex M X n) := finsupp.add_comm_group
instance : module R (simplicial_complex M X n) := finsupp.to_module _ _

/-- The boundary morphism of the simplicial complex -/
definition boundary : simplicial_complex M X (n+1) → simplicial_complex M X n :=
linear_extension X.boundary

namespace boundary
variables {R} {M} {X} {n}

instance : is_add_group_hom (boundary M X n) :=
linear_extension.is_add_group_hom $ λ x, simplicial_set.boundary.is_add_group_hom X x

include R

@[simp] lemma add_monoid.smul_eq_smul {n : ℕ} {m : M} : add_monoid.smul n m = (n : R) • m :=
begin
  induction n, simp,
  calc gsmul (int.of_nat (nat.succ n_n)) m = gsmul (int.of_nat n_n + 1) m : rfl
    ... = gsmul (int.of_nat n_n) m + gsmul 1 m : add_gsmul _ _ _
    ... = _ : by simp [*,add_smul],
end

@[simp] lemma gsmul_eq_smul {n : ℤ} {m : M} : gsmul n m = (n : R) • m :=
begin
  induction n, exact add_monoid.smul_eq_smul,
  simp, rw [add_monoid.smul_eq_smul, add_smul],
  simp [nat.succ_eq_add_one, add_smul, neg_smul, one_smul]
end

instance : is_linear_map (boundary M X n) := linear_extension.is_linear_map $ λ x,
{ smul := λ r m,
  begin
    dsimp [simplicial_set.boundary],
    erw ← sum_smul' _ (λ (i : ↥ [n + 1] ), single (δ X i x) (gsmul ((-1) ^ i.val) m)) r,
    congr,
    tidy,
    repeat {erw single_apply},
    split_ifs,
    tidy,
    repeat {erw [gsmul_eq_smul, ←mul_smul]},
    erw mul_comm
  end,
  .. (simplicial_set.boundary.is_add_group_hom X x) }

end boundary

lemma boundary_boundary (γ : simplicial_complex M X (n+2)) : (boundary M X n) ((boundary M X (n+1)) γ) = 0 :=
-- Step 1. It suffices to the condition on generators,
-- i.e., on γ of the form (single x m).
finsupp.induction γ (is_add_group_hom.zero _) $ λ x m f xni mne h,
begin
  rw [is_add_group_hom.add (boundary M X (n + 1)), is_add_group_hom.add (boundary M X n), h, add_zero],
  dsimp [boundary, linear_extension],
  -- Step 2a. Simplify the expression for the generators.
  -- Somehow these rewrites generate annoying trivial sidegoals.
  rw finsupp.sum_single_index,
  swap, { exact is_add_group_hom.zero _ },
  -- Step 2b. Gather the sums together.
  erw ←finsupp.sum_finset_sum_index,
  swap, { exact λ _, is_add_group_hom.zero _ },
  swap, { exact λ _, is_add_group_hom.add _ },
  -- Step 2c. Another simplification step.
  have : ∀ {n} {x : X.obj [n+1]}, X.boundary x (0 : M) = 0 := λ _ x, (is_add_group_hom.zero $ simplicial_set.boundary X x),
  simp [this, sum_single_index],
  -- Step 3. Fold the boundary operators into a composed function.assumption
  -- I wouldn't mind making this step shorter and more readable.
  erw show sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
        single (X.δ i (X.δ j x)) (gsmul ((-1) ^ i.val) (gsmul ((-1) ^ j.val) m)))) =
      sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
        single ((X.δ i ∘ X.δ j) x) (gsmul ((-1) ^ i.val) (gsmul ((-1) ^ j.val) m)))),
    by unfold function.comp,
  -- Step 4. Gather the sums into a sum over the product of the indexing sets.
  rw [←@finset.sum_product _ _ _ _ _ _ (λ (p : [n+1+1] × [n+1]),
        single ((X.δ p.snd ∘ X.δ p.fst) x) (gsmul ((-1)^p.snd.val) (gsmul ((-1)^p.fst.val) m)))],
  -- Step 5. Split the sum into two parts that will cancel.
  -- Afterwards, move one sum to the other side of the equation,
  -- and move the minus sign into the sum.
  rw [←@finset.sum_sdiff ([n+1+1] × [n+1]) _ (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val))],
  swap, { apply filter_subset },
  rw [←eq_neg_iff_add_eq_zero, ←finset.sum_neg_distrib],
  -- Step 6. The sums are equal because we can give a bijection
  -- between the indexing sets, such that corresponding terms are equal.
  -- We get 4 goals. All the substance is in the second goal.
  symmetry,
  refine (finset.sum_bij (λ (p : [n+1+1] × [n+1]) hp,
    (p.snd.succ, p.fst.cast_lt (lt_of_le_of_lt (mem_filter.mp hp).right p.snd.is_lt)))
    _ _ _ _),
  -- Step 7a. Show that our function is well-defined
  { tidy, exact nat.succ_le_succ (by assumption) }, swap,
  -- Step 7b. Show that our function is injective
  { tidy, exact fin.veq_of_eq (fin.succ.inj (by assumption)) }, swap,
  -- Step 7c. Show that our function is surjective
  { intros p hp,
    simp at *,
    exact ⟨p.snd.cast_succ, p.fst.pred
    begin
      intro H,
      rw H at hp,
      cases p.fst,
      exact nat.not_lt_zero _ hp
    end, by simpa [nat.pred_succ p.snd.val] using nat.pred_le_pred hp, by ext; simp⟩ },
  -- Step 8. Now we drilled down to the core of the proof.
  -- After all, we have to use the simplicial identity somewhere.
  rintros ⟨i,j⟩ hij,
  erw ← single_neg,
  erw show (X.δ $ i.cast_lt $ lt_of_le_of_lt (mem_filter.mp hij).2 j.is_lt) ∘ (X.δ (j.succ)) = (X.δ j) ∘ (X.δ i),
  begin
    show (X.δ j.succ ≫ (X.δ $ i.cast_lt _)) = (X.δ i ≫ X.δ j),
    erw simplicial_identity₁, -- this is where it happens!!
    { congr },
    { exact (mem_filter.mp hij).2 },
  end,
  -- Step 9. What is left is trivial manipulation of scalar multiplications
  simp [pow_succ, gsmul_neg],
  repeat {rw ← gsmul_mul},
  rw mul_comm
end

section lboundary
open linear_map
include R

def lboundary := is_linear_map.mk' (boundary M X n) boundary.is_linear_map

lemma lboundary_lboundary : (lboundary R M X n).comp (lboundary R M X (n+1)) = 0 :=
ext $ λ x, boundary_boundary _ _ _ _

def homology := (lboundary R M X (n+1)).ker

end lboundary

end simplicial_complex
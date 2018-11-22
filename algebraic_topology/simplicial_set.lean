import order.basic algebraic_topology.simplex_category data.finset data.finsupp algebra.group
import algebra.group_power tactic.abel
import category_theory.opposites category_theory.functor_category

universes u v w

open category_theory

local notation ` [`n`] ` := simplex_category.from_nat n

variables (C : Type u) [𝒞 : category.{u v} C]
include 𝒞

def simplicial_object := simplex_categoryᵒᵖ ⥤ C

variable {C}

instance : category (simplicial_object C) := functor.category _ _

omit 𝒞

/-- Simplicial set -/
def simplicial_set := simplicial_object (Type u)

namespace simplicial_object
include 𝒞

/-- The i-th face map of a simplicial set -/
def δ {X : simplicial_object C} {n : ℕ} (i : [n+1]) := X.map (simplex_category.δ i)

lemma simplicial_identity₁ {X : simplicial_object C} {n : ℕ} {i j : [n + 1]} (H : i ≤ j) :
(@δ _ _ X _ j.succ) ≫ δ i = δ i.cast_succ ≫ δ j :=
by {dsimp [δ], erw [←X.map_comp, simplex_category.simplicial_identity₁, X.map_comp], assumption}

end simplicial_object

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

variables (R : Type u) [ring R]
variables (M : Type u) [add_comm_group M] [module R M]
variables (X : simplicial_set) (n : ℕ)

instance : add_comm_group (simplicial_complex M X n) := finsupp.add_comm_group
instance : module R (simplicial_complex M X n) := finsupp.to_module _ _

definition boundary_component (i : [n+1]) : simplicial_complex M X (n+1) → simplicial_complex M X n :=
map_domain (@δ _ _ X _ i)

namespace boundary_component
variables {R} {M} {X} {n}

instance {i : [n+1]} : is_add_group_hom (boundary_component M X n i) :=
{ add := λ _ _, map_domain_add }

include R

instance {i : [n+1]} : is_linear_map (boundary_component M X n i) :=
{ smul := λ _ _, map_domain_smul _ _,
  .. boundary_component.is_add_group_hom }

end boundary_component

/-- The boundary morphism of the simplicial complex -/
definition boundary : simplicial_complex M X (n+1) → simplicial_complex M X n :=
λ s, s.sum $ λ x m, sum univ $ λ i : [n+1], finsupp.single (@δ _ _ X _ i x) $ gsmul ((-1 : ℤ)^i.val) m

namespace boundary
variables {R} {M} {X} {n}

instance : is_add_group_hom (boundary M X n) :=
⟨λ s₁ s₂, by apply finsupp.sum_add_index;
  finish [finset.sum_add_distrib, finset.sum_congr rfl, single_add, gsmul_add] ⟩

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

instance : is_linear_map (boundary M X n) :=
{ smul := λ r s, by {
  ext1,
  erw [map_range_apply],
  dsimp [boundary],
  erw [sum_map_range_index _], },
  .. boundary.is_add_group_hom }

end boundary

lemma C_is_a_complex (γ : C A X (n+2)) : (boundary A X n) ((boundary A X (n+1)) γ) = 0 :=
begin
  apply finsupp.induction γ,
  { apply is_add_group_hom.zero },
  { intros x a f xni ane h,
    rw [is_add_group_hom.add (boundary A X (n + 1)), is_add_group_hom.add (boundary A X n), h, add_zero],
    unfold boundary,
    rw finsupp.sum_single_index,
    { rw ←finsupp.sum_finset_sum_index,
      { rw show sum univ (λ (i : [n+1+1]),
                  sum (single (δ i x) ((-1 : ℤ) ^ i.val • a))
                    (λ (y : objs (n + 1)) (b : A),
                      sum univ (λ (i : [n+1]), single (δ i y) ((-1 : ℤ)^i.val • b)))) =
                sum univ (λ (i : [n+1+1]),
                  (λ (y : objs (n + 1)) (b : A),
                    sum univ (λ (i : [n+1]),
                      single (δ i y) ((-1 : ℤ)^i.val • b))) (δ i x) ((-1 : ℤ)^i.val • a)),
        by finish [finset.sum_congr rfl, finsupp.sum_single_index],
        rw show sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
                  single (δ i (δ j x)) ((-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ j.val • a)))) =
                sum univ (λ (j : [n+1+1]), sum univ (λ (i : [n+1]),
                  single (((δ i) ∘ (δ j)) x) ((-1 : ℤ) ^ i.val • ((-1 : ℤ) ^ j.val • a)))),
        by unfold function.comp,
        rw [←@finset.sum_product _ _ _ _ _ _
                (λ (p : [n+1+1] × [n+1]),
                  single ((δ p.snd ∘ δ p.fst) x) ((-1 : ℤ)^p.snd.val • ((-1 : ℤ)^p.fst.val • a))),
            ←@finset.sum_sdiff ([n+1+1] × [n+1]) _ (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val))],
        { rw [←eq_neg_iff_add_eq_zero, ←finset.sum_neg_distrib],
          apply eq.symm,
          apply @finset.sum_bij ([n+1+1] × [n+1]) _ ([n+1+1] × [n+1]) _
                                (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val)) _ _ _
                                (λ (p : [n+1+1] × [n+1]) hp,
                                (p.snd.succ, ⟨p.fst.val,lt_of_le_of_lt (mem_filter.mp hp).2 p.snd.is_lt⟩)),
          { intros p hp,
            simp,
            apply nat.succ_le_succ,
            exact (mem_filter.mp hp).2 },
          { intros p hp,
            simp [fin.succ],
            let j := p.fst,
            let i := p.snd,
            show -single (δ i (δ j x)) ((-1:ℤ)^i.val • ((-1:ℤ)^j.val • a)) =
                  single (δ ⟨j.val, _⟩ (δ i.succ x))((-1:ℤ)^j.val • ((-1:ℤ)^nat.succ (i.val) • a)),
            rw show -single (δ i (δ j x)) ((-1:ℤ)^i.val • (-1:ℤ)^j.val • a) =
                      single (δ i (δ j x)) (-((-1:ℤ)^i.val • (-1:ℤ)^j.val • a)),
            begin
            apply finsupp.ext,
            intro γ,
            simp [single_apply],
            split_ifs; simp
            end,
            apply finsupp.ext,
            intro γ,
            rw show (δ ⟨j.val, _⟩ (δ (fin.succ i) x)) = (δ i (δ j x)),
            begin
              show ((δ ⟨j.val, _⟩) ∘ (δ (fin.succ i))) x = ((δ i) ∘ (δ j)) x,
              rw simplicial_identity₁, -- this is where it happens!!
              { suffices foo : (fin.raise ⟨j.val, lt_of_le_of_lt (mem_filter.mp hp).2 i.is_lt⟩) = j,
                { rw foo },
                { apply fin.eq_of_veq,
                  finish }},
              { exact (mem_filter.mp hp).2 }
            end,
            simp [single_apply],
            split_ifs;
            simp [pow_succ, eq.symm mul_smul, eq_neg_iff_add_eq_zero, add_smul, mul_comm] },
          { intros p q hp hq,
            simp,
            intros h2 h1,
            apply prod.ext.mpr,
            split,
            { apply fin.eq_of_veq,
              apply fin.veq_of_eq h1 },
            { exact fin.succ.inj h2 }},
          { intros p hp,
            simp at *,
            existsi p.snd.raise,
            existsi (⟨p.fst.val.pred, begin
              induction H : p.fst.val with i,
              { simp [nat.zero_lt_succ] },
              { change i.succ ≤ n+2,
                simp [eq.symm H, nat.le_of_succ_le_succ p.fst.is_lt] }
            end⟩ : [n+1]),
            existsi _,
            { apply prod.ext.mpr,
              split; simp [fin.succ,fin.raise];
                apply fin.eq_of_veq;
                simp [nat.succ_pred_eq_of_pos (lt_of_le_of_lt (nat.zero_le p.snd.val) hp)] },
            { simp,
              exact (nat.pred_succ (p.fst).val ▸ nat.pred_le_pred hp) } } },
        { apply filter_subset }},
      { finish },
      { finish [finset.sum_add_distrib, finset.sum_congr rfl, single_add, smul_add] } },
    { finish }}
end

end simplicial_complex
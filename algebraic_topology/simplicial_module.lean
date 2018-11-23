import category_theory.examples.modules
import algebraic_topology.simplicial_set
import linear_algebra.tensor_product

open category_theory category_theory.examples finset

universe u

namespace linear_map
variables (R M N P : Type u) [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]
variables (f : M →ₗ N) (g : N →ₗ P)

lemma lcomp_comp : lcomp P f g = g.comp f := rfl

set_option class.instance_max_depth 100
include R
lemma llcomp_lcomp : llcomp M N P g f = lcomp P f g := rfl

end linear_map

variables (R : Type u) [comm_ring R]

def simplicial_module := simplicial_object (RMod R)

namespace simplicial_module
open linear_map simplicial_object

variables {R} (X : simplicial_module R)

local notation `[`n`]` := simplex_category.from_nat n

def boundary (n : ℕ) : X.obj [n+1] ⟶ X.obj [n] :=
sum univ $ λ i : [n+1], ((-1 : R)^i.val) • (X.δ i)

-- set_option pp.notation false

lemma boundary_boundary (n : ℕ) : boundary X (n+1) ≫ boundary X n = 0 :=
begin
  -- Massage the sums towards the outside
  dsimp [(≫)],
  erw [← lcomp_comp, ← llcomp_lcomp, map_sum],
  simp only [llcomp_lcomp],
  simp [boundary, map_sum],
  simp [(llcomp_lcomp R _ _ _ _ _).symm],
  simp [llcomp_lcomp, lcomp_comp, smul_smul],
  -- Gather the sums into a sum over the product of the indexing sets.
  erw ← @finset.sum_product _ _ _ _ _ _
    (λ (p : [n+1+1] × [n+1]), ((-1:R)^p.snd.val * (-1)^p.fst.val) • comp (X.δ p.snd) (X.δ p.fst)),
  -- Split the sum into two parts that will cancel.
  -- Afterwards, move one sum to the other side of the equation,
  -- and move the minus sign into the sum.
  erw ← @finset.sum_sdiff ([n+1+1] × [n+1]) _
    (univ.filter (λ p : [n+1+1] × [n+1], p.fst.val ≤ p.snd.val)),
  swap, { apply filter_subset },
  erw [←eq_neg_iff_add_eq_zero, ←finset.sum_neg_distrib],
  -- The sums are equal because we can give a bijection
  -- between the indexing sets, such that corresponding terms are equal.
  -- We get 4 goals. All the substance is in the second goal.
  symmetry,
  refine (finset.sum_bij (λ (p : [n+1+1] × [n+1]) hp,
    (p.snd.succ, p.fst.cast_lt (lt_of_le_of_lt (mem_filter.mp hp).right p.snd.is_lt)))
    _ _ _ _),
  -- Show that our function is well-defined
  { tidy, exact nat.succ_le_succ (by assumption) }, swap,
  -- Show that our function is injective
  { tidy, exact fin.veq_of_eq (fin.succ.inj (by assumption)) }, swap,
  -- Show that our function is surjective
  { intros p hp,
    simp at *,
    exact ⟨p.snd.cast_succ, p.fst.pred
    begin
      intro H,
      rw H at hp,
      cases p.fst,
      exact nat.not_lt_zero _ hp
    end, by simpa [nat.pred_succ p.snd.val] using nat.pred_le_pred hp, by ext; simp⟩ },
  -- Now we drilled down to the core of the proof.
  -- After all, we have to use the simplicial identity somewhere.
  rintros ⟨i,j⟩ hij,
  change _ = _ • (_ ≫ _),
  erw simplicial_identity₁,
  swap, { exact (mem_filter.mp hij).2 },
  erw [← neg_one_smul, smul_smul _ _ (comp (δ X j) (δ X i))],
  congr' 1,
  simp [nat.succ_eq_add_one, pow_add, mul_comm],
end

end simplicial_module

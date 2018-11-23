import category_theory.examples.modules
import algebraic_topology.simplicial_set

open category_theory category_theory.examples finset

universe u

section

variables (R : Type u) [ring R]

def simplicial_module := simplicial_object (RMod R)

section

variables {R} (X : simplicial_module R)

local notation ` [`n`] ` := simplex_category.from_nat n

def boundary (n : ℕ) : X.obj [n+1] ⟶ X.obj [n] :=
sum univ $ λ i : [n+1], gsmul ((-1 : ℤ)^i.val) (X.δ i)

lemma boundary_boundary (n : ℕ) : boundary X (n+1) ≫ boundary X n = 0 :=
sorry

end

end

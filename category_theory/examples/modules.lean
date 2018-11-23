import linear_algebra.tensor_product
import category_theory.functor

open category_theory

universe u

namespace category_theory.examples

variables (R : Type u) [ring R]

/-- The category of (left) R-modules and R-linear maps. -/
structure RMod : Type (u+1) :=
(α : Type u)
[add_comm_group : add_comm_group α]
[module : module R α]

instance : has_coe_to_sort (RMod R) :=
{ S := Type u, coe := RMod.α }

instance RMod_obj.add_comm_group (M : RMod R) : add_comm_group M := M.add_comm_group
instance RMod_obj.module (M : RMod R) : module R M := M.module

instance RMod_category : category (RMod R) :=
{ hom := λ M N, M →ₗ N,
  id := λ M, linear_map.id,
  comp := λ _ _ _ f g, g.comp f }

instance RMod_hom.has_coe_to_fun {M N : RMod R} : has_coe_to_fun (M ⟶ N) :=
by dunfold RMod_category; apply_instance

instance RMod_hom.add_comm_group {M N : RMod R} : add_comm_group (M ⟶ N) :=
by dunfold RMod_category; apply_instance

end category_theory.examples

import algebra.module
import category_theory.examples.rings

universes u v

namespace category_theory.examples
open category_theory category_theory.examples

namespace Ring

def int : Ring := { α := ℤ }

end Ring

structure left_module (R : Ring.{v}) : Type (max (u+1) v) :=
(carrier : Type u)
(grp : add_comm_group carrier)
(mod : module R carrier)

namespace left_module

variables {R : Ring}

local notation R`-Mod` : max := left_module.{u} R

instance : has_coe_to_sort (R-Mod) :=
{ S := Type u, coe := λ M, M.carrier }

instance (M : R-Mod) : add_comm_group M := M.grp
instance (M : R-Mod) : module R M := M.mod

instance : category (R-Mod) :=
{ hom  := λ M N, linear_map M N,
  id   := λ M, @linear_map.id _ M _ _ _,
  comp := λ M N P f g, g.comp f }

end left_module

section

def add_comm_group_to_int_module (G : Type u) [add_comm_group G] : left_module Ring.int :=
{ carrier := G,
  grp := by apply_instance,
  mod := module.of_core
  { smul := gsmul,
    smul_add := λ n a b, gsmul_add a b n,
    add_smul := λ m n a, add_gsmul a m n,
    mul_smul := λ m n a, gsmul_mul a m n,
    one_smul := λ a, one_gsmul a } }

end

end category_theory.examples

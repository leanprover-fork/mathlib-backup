import algebra.module tactic.ring

class has_bracket (α : Type*) := (bracket : α → α → α)

local notation `[` a `,` b `]` := has_bracket.bracket a b

class lie_algebra (R : out_param $ Type*) (𝔤 : Type*) [out_param $ comm_ring R]
extends module R 𝔤, has_bracket 𝔤 :=
(left_linear  : ∀ y : 𝔤, is_linear_map (λ x : 𝔤, [x,y]))
(right_linear : ∀ x : 𝔤, is_linear_map (λ y : 𝔤, [x,y]))
(alternating  : ∀ x : 𝔤, [x,x] = 0)
(Jacobi_identity : ∀ x y z : 𝔤, [x,[y,z]] + [z,[x,y]] + [y,[z,x]] = 0)
(anti_comm    : ∀ x y : 𝔤, [x,y] = -([y,x]))

variables {R : Type*} [ri : comm_ring R]
variables {𝔤 : Type*} [la : lie_algebra R 𝔤]
include ri la

section from_ring

variables {S : Type*} [ring S]
variables {f : R → S}  [is_ring_hom f]
variable  {central : ∀ (r : R) (s : S), f(r) * s = s * f(r)}

instance commutator_bracket : has_bracket S := ⟨λ x y, x*y - y*x⟩

include central
definition ring.to_lie_algebra : lie_algebra R S :=
{ left_linear  := begin
    intro y,
    dsimp [commutator_bracket],
    constructor,
    { intros x₁ x₂,
      simp [left_distrib,right_distrib,mul_assoc] },
    { intros r x,
      show f r * x * y + -(y * (f r * x)) = f r * (x * y + -(y * x)),
      simp [left_distrib,right_distrib,mul_assoc,central] }
  end,
  right_linear := begin
    intro x,
    dsimp [commutator_bracket],
    constructor,
    { intros x₁ x₂,
      simp [left_distrib,right_distrib,mul_assoc] },
    { intros r y,
      show x * (f r * y) + -(f r * y * x) = f r * (x * y + -(y * x)),
      simp [left_distrib,right_distrib,mul_assoc,central] }
  end,
  alternating  := begin
    intro x,
    dsimp [commutator_bracket],
    simp
  end,
  Jacobi_identity := begin
    intros x y z,
    dsimp [commutator_bracket],
    simp [left_distrib,right_distrib,mul_assoc],
  end,
  anti_comm := begin
    intros x y,
    dsimp [commutator_bracket],
    simp
  end,
  ..restriction_of_scalars.restriction_of_scalars f S
}

end from_ring

/-- `𝔥` is a Lie subalgebra: a set closed under the Lie bracket. -/
class is_lie_subalgebra (𝔥 : set 𝔤) extends is_submodule 𝔥 :=
(closed {x y} : x ∈ 𝔥 → y ∈ 𝔥 → [x,y] ∈ 𝔥)

-- We are not ready for this instance...
-- Lean does not yet know that a submodule is a module.
-- instance subset.lie_algebra {𝔥 : set 𝔤} [is_lie_subalgebra 𝔥] : lie_algebra R 𝔥 := {}

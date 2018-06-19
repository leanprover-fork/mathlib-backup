import algebra.module tactic.ring data.complex.basic linear_algebra.basic linear_algebra.dimension data.set.finite
import linear_algebra.linear_map_module

universes u v w

class has_bracket (α : Type u) := (bracket : α → α → α)

local notation `[` a `,` b `]` := has_bracket.bracket a b

class lie_algebra (R : out_param $ Type u) (𝔤 : Type v) [out_param $ comm_ring R]
extends module R 𝔤, has_bracket 𝔤 :=
(left_linear  : ∀ y : 𝔤, is_linear_map (λ x : 𝔤, [x,y]))
(right_linear : ∀ x : 𝔤, is_linear_map (λ y : 𝔤, [x,y]))
(alternating  : ∀ x : 𝔤, [x,x] = 0)
(Jacobi_identity : ∀ x y z : 𝔤, [x,[y,z]] + [z,[x,y]] + [y,[z,x]] = 0)
(anti_comm    : ∀ x y : 𝔤, [x,y] = -([y,x]))

section generalities

variables {R : Type u} [ri : comm_ring R]
variables {𝔤 : Type v} [la : lie_algebra R 𝔤]

section from_ring

variables {S : Type w} [ring S]
variables {f : R → S}  [is_ring_hom f]
variable  {central : ∀ (r : R) (s : S), f(r) * s = s * f(r)}

instance commutator_bracket : has_bracket S := ⟨λ x y, x*y - y*x⟩

include ri la
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
  ..module.restriction_of_scalars f S
}

end from_ring

include ri la

/-- `𝔥` is a Lie subalgebra: a set closed under the Lie bracket. -/
class is_lie_subalgebra (𝔥 : set 𝔤) extends is_submodule 𝔥 : Prop :=
(closed {x y} : x ∈ 𝔥 → y ∈ 𝔥 → [x,y] ∈ 𝔥)

/-- `I` is an ideal: for all x ∈ 𝔤 and y in I: [x,y] ∈ I. -/
class lie.is_ideal (I : set 𝔤) extends is_submodule I : Prop :=
(closed {x y} : y ∈ I → [x,y] ∈ I)

instance lie_subalgebra_of_ideal (I : set 𝔤) [hI : @lie.is_ideal R ri 𝔤 la I] :
(@is_lie_subalgebra R ri 𝔤 la I) :=
begin
  constructor,
  intros x y hx hy,
  apply hI.closed,
  exact hy
end

def ad (x : 𝔤) := λ y, [x,y]

lemma ad_is_linear (x : 𝔤) : is_linear_map (ad x) := lie_algebra.right_linear x

variables (𝔤)

@[class] def is_abelian : Prop := ∀ x y : 𝔤, [x,y] = 0

class is_simple : Prop :=
(no_proper_ideals : ∀ (I : set 𝔤), (@lie.is_ideal R ri 𝔤 la I) → (I = {0} ∨ I = set.univ))
(not_abelian : ¬is_abelian 𝔤)

variables {𝔤}

-- set_option trace.class_instances true

instance subset.lie_algebra {𝔥 : set 𝔤} [H : @is_lie_subalgebra R ri 𝔤 la 𝔥] :
lie_algebra R 𝔥 :=
{ to_module := subset.module 𝔥,
  bracket := λ x y, ⟨[x.1,y.1], is_lie_subalgebra.closed _ x.2 y.2⟩,
  left_linear := begin
    intro y,
    constructor,
    { intros x₁ x₂,
      apply subtype.eq,
      apply (lie_algebra.left_linear y.val).add },
    { intros r x,
      apply subtype.eq,
      apply (lie_algebra.left_linear y.val).smul }
  end,
  right_linear := begin
    intro x,
    constructor,
    { intros y₁ y₂,
      apply subtype.eq,
      apply (lie_algebra.right_linear x.val).add },
    { intros r y,
      apply subtype.eq,
      apply (lie_algebra.right_linear x.val).smul }
  end,
  alternating := assume ⟨x,_⟩, subtype.eq $ lie_algebra.alternating _,
  Jacobi_identity := assume ⟨x,_⟩ ⟨y,_⟩ ⟨z,_⟩, subtype.eq $ lie_algebra.Jacobi_identity _ _ _,
  anti_comm := assume ⟨x,_⟩ ⟨y,_⟩, subtype.eq $ lie_algebra.anti_comm _ _
}

class is_cartan_subalgebra (𝔥 : set 𝔤) [@is_lie_subalgebra R ri 𝔤 la 𝔥] : Prop :=
(abelian : is_abelian 𝔥)
(maximal : ∀ (𝔥' : set 𝔤) [@is_lie_subalgebra R ri 𝔤 la 𝔥'] [is_abelian 𝔥'], 𝔥 ⊂ 𝔥' → 𝔥 = 𝔥')

variables {𝔥 : set 𝔤} [H : @is_lie_subalgebra R ri 𝔤 la 𝔥] [@is_cartan_subalgebra R ri 𝔤 la 𝔥 H]
include H

class is_root (α : module.dual R 𝔥) : Prop :=
(ne_zero : α ≠ 0)
(eigenvector : ∃ x : 𝔤, x ≠ 0 ∧ ∀ h : 𝔥, [h.1,x] = α.1(h) • x)

end generalities

section complex_lie_algebras

variables {𝔤 : Type u} [la : lie_algebra ℂ 𝔤]
variables {𝔥 : set 𝔤} [H : @is_lie_subalgebra _ _ 𝔤 la 𝔥] [isC : @is_cartan_subalgebra _ _ 𝔤 la 𝔥 H]
include la H isC

instance complex.of_real_ring_hom : is_ring_hom complex.of_real :=
{ map_add := complex.of_real_add,
  map_mul := complex.of_real_mul,
  map_one := complex.of_real_one }

def Φ := {α : module.dual ℂ 𝔥 | is_root α}

def E := @span ℝ _ _ (module.restriction_of_scalars complex.of_real (module.dual ℂ 𝔥)) Φ

-- noncomputable instance vector_space_of_module_over_field : vector_space ℂ 𝔤 := {}

variables (fin_dim : vector_space.dim ℂ 𝔤 < cardinal.omega)

local attribute [instance] classical.prop_decidable

theorem neg_root (α : module.dual ℂ 𝔥) : (α ∈ (@Φ _ _ _ _ isC)) → -α ∈ (@Φ _ _ _ _ isC) :=
begin
  sorry
end


theorem scalar_multiple_root (α ∈ (@Φ _ _ _ _ isC)) (c : ℂ) : (c • α) ∈ (@Φ _ _ _ _ isC) →
c = 1 ∨ c = -1 :=
begin
  intro hyp,
  by_contradiction,
  sorry
end

theorem finitely_many_roots : set.finite (@Φ _ _ _ _ isC) :=
begin
  have f : (subtype (@Φ _ _ _ _ isC)) → 𝔤 := λ α, classical.some α.property.eigenvector,
  have f_inj : function.injective f :=
  begin
    unfold function.injective,
    intros α₁ α₂ hyp,
    repeat {apply subtype.eq},
    apply funext,
    intro h,
    dsimp,
    have foo : [h.1, f α₁] = [h.1, f α₂] := by rw hyp,
    have bar : α₁.val.1(h) • (f α₁) = α₂.val.1(h) • (f α₁) :=
    begin
      sorry
    end,
    sorry
  end,
  apply set.finite_preimage,
end

end complex_lie_algebras

-- Need a finite-fimensional Lie algebra over a field for this one
-- def Killing_form := λ x y : 𝔤, @vector_space.endomorphism.trace _ _ _ _ (ad x ∘ ad y)
-- (@is_linear_map.comp _ _ _ _ (comm_ring.to_ring R) _ _ _ _ _ (ad_is_linear x) (ad_is_linear y))

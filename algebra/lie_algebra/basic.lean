import tactic.ring data.complex.basic linear_algebra.dimension linear_algebra.tensor_product ring_theory.algebra

universes u v w

-- 𝔤: \Mfg
class lie_algebra (R : out_param $ Type u) (𝔤 : Type v) [out_param $ comm_ring R] [add_comm_group 𝔤]
  extends module R 𝔤 :=
(bracket : 𝔤 →ₗ 𝔤 →ₗ 𝔤)
(notation `⟮ ` a `, ` b ` ⟯` := (bracket : 𝔤 → 𝔤 →ₗ 𝔤) a b)
(alternating  : ∀ x : 𝔤, ⟮x,x⟯ = 0)
(Jacobi_identity : ∀ x y z : 𝔤, ⟮x,⟮y,z⟯⟯ + ⟮z,⟮x,y⟯⟯ + ⟮y,⟮z,x⟯⟯ = 0)
(anti_comm    : ∀ x y : 𝔤, ⟮x,y⟯ = -⟮y,x⟯)

instance lie_algebra.to_vector_space {α : Type u} {β : Type v} [discrete_field α] [add_comm_group β] [lie_algebra α β] : vector_space α β := {}

variables (R : Type u) [comm_ring R]
variables (𝔤 : Type v) [add_comm_group 𝔤] [lie_algebra R 𝔤]
include R

-- ⟮ : \([
notation `⟮ ` a `, ` b ` ⟯` := lie_algebra.bracket _ a b
notation `⟮ ` a `, ` b ` ⟯[`𝔤`]` := lie_algebra.bracket 𝔤 a b

section from_algebra

variables {R} {S : Type w} [ring S] (i : algebra R S)

set_option class.instance_max_depth 60
definition ring.to_lie_algebra : lie_algebra R i.right :=
{ bracket := show algebra.right i →ₗ algebra.right i →ₗ algebra.right i,
    from i.lmul - i.lmul.flip,
  alternating := λ _, sub_self _,
  Jacobi_identity := λ x y z, show (x*(y*z-z*y)-(y*z-z*y)*x) +
      (z*(x*y-y*x)-(x*y-y*x)*z) + (y*(z*x-x*z)-(z*x-x*z)*y) = 0,
    by simp [mul_add, add_mul, mul_assoc],
  anti_comm := λ _ _, (neg_sub _ _).symm,
  .. i }
end from_algebra

set_option class.instance_max_depth 35

/-- `𝔥` is a Lie subalgebra: a set closed under the Lie bracket. -/
structure lie_subalgebra extends submodule R 𝔤 :=
(bracket {x y} : x ∈ carrier → y ∈ carrier → ⟮x,y⟯[𝔤] ∈ carrier)

instance : has_coe_to_sort (lie_subalgebra R 𝔤) :=
⟨_, λ 𝔥, ↥𝔥.carrier⟩

/-- `I` is an ideal: for all x ∈ 𝔤 and y in I: [x,y] ∈ I. -/
structure lie_ideal extends submodule R 𝔤 :=
(bracket {x y} : y ∈ carrier → ⟮x,y⟯[𝔤] ∈ carrier)

variables {R 𝔤}

namespace lie_ideal

def lie_ideal.subalgebra (I : lie_ideal R 𝔤) : lie_subalgebra R 𝔤 :=
{ bracket := λ _ _ _ hy, I.bracket hy,
  .. I }

theorem ext : ∀ {I J : lie_ideal R 𝔤}, I.carrier = J.carrier → I = J
| ⟨⟨Ic, _, _, _⟩, _⟩ ⟨⟨Jc, _, _, _⟩, _⟩ rfl := rfl

inductive in_span (s : set 𝔤) : 𝔤 → Prop
| basic : ∀ {x}, x ∈ s → in_span x
| zero : in_span 0
| add : ∀ {x y}, in_span x → in_span y → in_span (x+y)
| smul : ∀ {c x}, in_span x → in_span (c • x)
| bracket : ∀ {x y}, in_span y → in_span ⟮x,y⟯[𝔤]

def span (s : set 𝔤) : lie_ideal R 𝔤 :=
{ carrier := {x | in_span s x},
  zero := in_span.zero s,
  add := λ _ _, in_span.add,
  smul := λ _ _, in_span.smul,
  bracket := λ _ _, in_span.bracket }

instance : partial_order (lie_ideal R 𝔤) :=
partial_order.lift (λ I, I.carrier) (λ _ _, ext)

variables {s : set 𝔤}

lemma subset_span : s ⊆ (span s).carrier :=
λ x h, in_span.basic h

lemma mem_span {x} : x ∈ (span s).carrier ↔ ∀ p : lie_ideal R 𝔤, s ⊆ p.carrier → x ∈ p.carrier :=
⟨λ H p hsp, begin
  induction H with x hxs x y hx hy ihx ihy c x hx ihx x y hy ihy,
  { exact hsp hxs },
  { exact p.zero },
  { exact p.add ihx ihy },
  { exact p.smul c ihx },
  { exact p.bracket ihy }
end, λ H, H _ subset_span⟩

theorem span_le {s : set 𝔤} {t : lie_ideal R 𝔤} :
  span s ≤ t ↔ s ≤ t.carrier :=
⟨set.subset.trans subset_span, λ ss x h, mem_span.1 h t ss⟩

protected def gi : galois_insertion (@span R _ 𝔤 _ _) (λ I, I.carrier) :=
{ choice := λ s _, span s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

instance : lattice.complete_lattice (lie_ideal R 𝔤) :=
lie_ideal.gi.lift_complete_lattice

end lie_ideal

namespace lie_subalgebra

theorem ext : ∀ {I J : lie_subalgebra R 𝔤}, I.carrier = J.carrier → I = J
| ⟨⟨Ic, _, _, _⟩, _⟩ ⟨⟨Jc, _, _, _⟩, _⟩ rfl := rfl

inductive in_span (s : set 𝔤) : 𝔤 → Prop
| basic : ∀ {x}, x ∈ s → in_span x
| zero : in_span 0
| add : ∀ {x y}, in_span x → in_span y → in_span (x+y)
| smul : ∀ {c x}, in_span x → in_span (c • x)
| bracket : ∀ {x y}, in_span x → in_span y → in_span ⟮x,y⟯[𝔤]

def span (s : set 𝔤) : lie_subalgebra R 𝔤 :=
{ carrier := {x | in_span s x},
  zero := in_span.zero s,
  add := λ _ _, in_span.add,
  smul := λ _ _, in_span.smul,
  bracket := λ _ _, in_span.bracket }

instance : partial_order (lie_subalgebra R 𝔤) :=
partial_order.lift (λ I, I.carrier) (λ _ _, ext)

variables {s : set 𝔤}

lemma subset_span : s ⊆ (span s).carrier :=
λ x h, in_span.basic h

lemma mem_span {x} : x ∈ (span s).carrier ↔ ∀ p : lie_subalgebra R 𝔤, s ⊆ p.carrier → x ∈ p.carrier :=
⟨λ H p hsp, begin
  induction H with x hxs x y hx hy ihx ihy c x hx ihx x y hx hy ihx ihy,
  { exact hsp hxs },
  { exact p.zero },
  { exact p.add ihx ihy },
  { exact p.smul c ihx },
  { exact p.bracket ihx ihy }
end, λ H, H _ subset_span⟩

theorem span_le {s : set 𝔤} {t : lie_subalgebra R 𝔤} :
  span s ≤ t ↔ s ≤ t.carrier :=
⟨set.subset.trans subset_span, λ ss x h, mem_span.1 h t ss⟩

protected def gi : galois_insertion (@span R _ 𝔤 _ _) (λ I, I.carrier) :=
{ choice := λ s _, span s,
  gc := λ s t, span_le,
  le_l_u := λ s, subset_span,
  choice_eq := λ s h, rfl }

instance : lattice.complete_lattice (lie_subalgebra R 𝔤) :=
lie_subalgebra.gi.lift_complete_lattice

end lie_subalgebra

def ad (x : 𝔤) : 𝔤 →ₗ 𝔤 := lie_algebra.bracket 𝔤 x

variables (𝔤)

@[class] def is_abelian : Prop := ∀ x y : 𝔤, ⟮x,y⟯[𝔤] = 0

class is_simple : Prop :=
(no_proper_ideals : ∀ I : lie_ideal R 𝔤, (I = ⊥ ∨ I = ⊤))
(not_abelian : ¬is_abelian 𝔤)

variables {𝔤}

namespace lie_subalgebra

instance (𝔥 : lie_subalgebra R 𝔤) : add_comm_group 𝔥 :=
submodule.add_comm_group _

instance (𝔥 : lie_subalgebra R 𝔤) : module R 𝔥 :=
submodule.module _

instance (𝔥 : lie_subalgebra R 𝔤) : lie_algebra R 𝔥 :=
{ bracket := linear_map.mk₂ (λ x y, ⟨⟮x,y⟯[𝔤], 𝔥.bracket x.2 y.2⟩)
    (λ m₁ m₂ n, subtype.eq $ linear_map.map_add₂ _ _ _ _)
    (λ c m n, subtype.eq $ linear_map.map_smul₂ _ _ _ _)
    (λ m n₁ n₂, subtype.eq $ linear_map.map_add _ _ _)
    (λ c m n, subtype.eq $ linear_map.map_smul _ _ _),
  Jacobi_identity := λ x y z, subtype.eq $ lie_algebra.Jacobi_identity x y z,
  alternating := λ x, subtype.eq $ lie_algebra.alternating x,
  anti_comm := λ x y, subtype.eq $ lie_algebra.anti_comm x y }

end lie_subalgebra

variables (R 𝔤)
class cartan_subalgebra extends lie_subalgebra R 𝔤 :=
(abelian : is_abelian to_lie_subalgebra)
(maximal : ∀ (𝔥' : lie_subalgebra R 𝔤) [is_abelian 𝔥'], to_lie_subalgebra ≤ 𝔥' → to_lie_subalgebra = 𝔥')

instance : has_coe_to_sort (cartan_subalgebra R 𝔤) :=
⟨_, λ 𝔥, ↥𝔥.carrier⟩

namespace cartan_subalgebra

instance (𝔥 : cartan_subalgebra R 𝔤) : add_comm_group 𝔥 :=
submodule.add_comm_group _

instance (𝔥 : cartan_subalgebra R 𝔤) : lie_algebra R 𝔥 :=
lie_subalgebra.lie_algebra _

end cartan_subalgebra

variables {R 𝔤}

class is_root (𝔥 : cartan_subalgebra R 𝔤) (α : 𝔥 →ₗ R) : Prop :=
(ne_zero : α ≠ 0)
(eigenvector : ∃ x : 𝔤, x ≠ 0 ∧ ∀ h : 𝔥, ⟮h,x⟯[𝔤] = α h • x)

section complex_lie_algebras

omit R
variables [lie_algebra ℂ 𝔤] (𝔥 : cartan_subalgebra ℂ 𝔤)

instance complex.of_real_ring_hom : is_ring_hom complex.of_real :=
{ map_add := complex.of_real_add,
  map_mul := complex.of_real_mul,
  map_one := complex.of_real_one }

def Φ : set (𝔥 →ₗ ℂ) := {α : 𝔥 →ₗ ℂ | is_root 𝔥 α}

def restriction {α : Type u} {β : Type v}
  [ring α] [ring β] (f : α → β) (hf : is_ring_hom f)
  (γ : Type w) [add_comm_group γ] [module β γ] : Type w :=
γ

instance restriction.add_comm_group {α : Type u} {β : Type v}
  [ring α] [ring β] (f : α → β) (hf : is_ring_hom f)
  (γ : Type w) [add_comm_group γ] [module β γ] : add_comm_group (restriction f hf γ) :=
_inst_7

instance restriction.module {α : Type u} {β : Type v}
  [ring α] [ring β] (f : α → β) (hf : is_ring_hom f)
  (γ : Type w) [add_comm_group γ] [module β γ] : module α (restriction f hf γ) := module.of_core
{ smul := λ c x, (f c • x : γ),
  add_smul := λ r s x, show f (r+s) • _ = f r • _ + f s • _, by rw [is_ring_hom.map_add f, add_smul],
  mul_smul := λ r s x, show f (r*s) • _ = f r • (f s • _), by rw [is_ring_hom.map_mul f, mul_smul],
  one_smul := λ x, show f 1 • _ = _, by rw [is_ring_hom.map_one f, one_smul],
  smul_add := λ _ _ _, smul_add _ _ _ }

--def E : submodule ℝ (restriction complex.of_real (by apply_instance) (𝔥 →ₗ ℂ)) := submodule.span Φ

-- noncomputable instance vector_space_of_module_over_field : vector_space ℂ 𝔤 := {}

variables (fin_dim : vector_space.dim ℂ 𝔤 < cardinal.omega)

local attribute [instance] classical.prop_decidable

set_option class.instance_max_depth 40
theorem neg_root (α) (H : α ∈ Φ 𝔥) : -α ∈ Φ 𝔥 :=
begin
  sorry
end

theorem scalar_multiple_root (α ∈ Φ 𝔥) (c : ℂ) : c • α ∈ Φ 𝔥 → c = 1 ∨ c = -1 :=
begin
  intro hyp,
  by_contradiction,
  sorry
end

theorem finitely_many_roots : set.finite (Φ 𝔥) :=
begin
  have f : (subtype (Φ 𝔥)) → 𝔤 := λ α, classical.some α.property.eigenvector,
  have f_inj : function.injective f :=
  begin
    unfold function.injective,
    intros α₁ α₂ hyp,
    repeat {apply subtype.eq},
    sorry
  end,
  apply set.finite_preimage,
  sorry,
  sorry
end

end complex_lie_algebras

-- Need a finite-fimensional Lie algebra over a field for this one
-- def Killing_form := λ x y : 𝔤, @vector_space.endomorphism.trace _ _ _ _ (ad x ∘ ad y)
-- (@is_linear_map.comp _ _ _ _ (comm_ring.to_ring R) _ _ _ _ _ (ad_is_linear x) (ad_is_linear y))

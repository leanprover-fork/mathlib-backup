import category_theory.transfinite.composition
import set_theory.cofinality

universes u v

namespace category_theory.transfinite
open category_theory

section
variables {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]

lemma upper_bound_of_cofinality {ι : Type v} (f : ι → {j : γ // j < ⊤})
  (h : cardinal.mk ι < (ordinal.type ((<) : γ → γ → Prop)).cof) :
  ∃ j, j < ⊤ ∧ ∀ i, (f i).val ≤ j :=
sorry

lemma is_limit_of_cofinality
  (h : cardinal.omega ≤ (ordinal.type ((<) : γ → γ → Prop)).cof) :
  is_limit (⊤ : γ) :=
sorry

end

section

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

-- X is κ-small with respect to I if any map from X to the end of a
-- transfinite composition of maps from I whose length has cofinality
-- at least κ factors through some earlier object in the composition.
def κ_small (I : morphism_class C) (κ : cardinal) (X : C) : Prop :=
∀ (γ : Type v) [lattice.order_top γ], by exactI ∀ [is_well_order γ (<)],
  κ ≤ (ordinal.type ((<) : γ → γ → Prop)).cof →
∀ (c : transfinite_composition I γ) (f : X ⟶ c.F.obj ⊤),
∃ (j : γ) (hj : j < ⊤) (g : X ⟶ c.F.obj j),
  g ≫ c.F.map ⟨⟨lattice.le_top⟩⟩ = f

def small (I : morphism_class C) (X : C) : Prop := ∃ κ, κ_small I κ X

end

section Set

lemma jointly_surjective {J : Type v} [small_category J] (F : J ⥤ Type v)
  {t : limits.cocone F} (h : limits.is_colimit t) (x : t.X) :
  ∃ j y, t.ι.app j y = x :=
begin
  suffices : (λ (x : t.X), ulift.up (∃ j y, t.ι.app j y = x)) = (λ _, ulift.up true),
  { have := congr_fun this x,
    have H := congr_arg ulift.down this,
    dsimp at H,
    rwa eq_true at H },
  refine h.hom_ext _,
  intro j, ext y,
  erw iff_true,
  exact ⟨j, y, rfl⟩
end

variables (I : morphism_class (Type v)) (X : Type v)

lemma is_small : small I X :=
begin
  have : ∃ κ, cardinal.mk X < κ ∧ κ.is_regular,
  { refine ⟨(max cardinal.omega (cardinal.mk X)).succ, _, cardinal.succ_is_regular (le_max_left _ _)⟩,
    exact lt_of_le_of_lt (le_max_right _ _) (cardinal.lt_succ_self _) },
  rcases this with ⟨κ, hκ₁, hκ₂⟩,
  refine ⟨κ, _⟩,
  intros γ I₁ I₂ hγ c f, resetI,
  have : ∀ x, ∃ j y, (c.F.map_cocone (cocone_at ⊤)).ι.app j y = f x,
  { intro x,
    cases c.limit ⊤ (is_limit_of_cofinality _) with hlim,
    refine jointly_surjective _ hlim _,
    exact le_trans hκ₂.1 hγ },
  choose jx yx hy using this,
  rcases upper_bound_of_cofinality jx (lt_of_lt_of_le hκ₁ hγ) with ⟨j, hj₁, hj₂⟩,
  refine ⟨j, hj₁, λ x, c.F.map ⟨⟨hj₂ x⟩⟩ (yx x), _⟩,
  ext x,
  rw ←hy,
  change (c.F.map _ ≫ c.F.map _) (yx x) = c.F.map _ (yx x),
  rw ←c.F.map_comp, refl,
end

end Set

end category_theory.transfinite

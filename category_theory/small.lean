import category_theory.category
import tactic.tidy
import set_theory.cofinality

universe u
open set function

local notation `card` := cardinal.mk.{u} -- Maybe this is a bad idea?

lemma cardinal.le_of_injective {α β : Type u} (f : α → β) (h : injective f) : card α ≤ card β :=
⟨⟨f, h⟩⟩

lemma cardinal.le_of_subtype {α : Type u} {p : set α} : card p ≤ card α :=
⟨⟨subtype.val, by tidy⟩⟩

lemma cardinal.ge_of_surjective {α β : Type u} (f : α → β) (h : surjective f) : card α ≥ card β :=
⟨embedding.of_surjective h⟩

open cardinal

def regular_cardinal := {κ : cardinal.{u} // is_regular κ}
instance : has_coe regular_cardinal.{u} cardinal.{u} := by unfold regular_cardinal; apply_instance

lemma regular_cardinal.infinite (κ : regular_cardinal.{u}) : omega.{u} ≤ ↑κ := κ.2.1

variables (κ : regular_cardinal.{u})

lemma is_small_of_finite {S : Type u} [fintype S] : card S < κ :=
calc card S < omega : lt_omega_iff_fintype.mpr ⟨by apply_instance⟩
        ... ≤ κ     : κ.infinite

lemma small_of_small_sigma_of_small {I : Type u} (hI : card I < κ) {f : I → Type u}
  (hf : ∀ i, card (f i) < κ) : card (sigma f) < κ :=
by rw ←sum_mk; exact sum_lt_of_is_regular (λ (i : I), card (f i)) κ.property hI hf

lemma small_of_small_union_of_small {I : Type u} (hI : card I < κ) {α : Type u} (f : I → set α)
  (hf : ∀ i, card (f i) < κ) : card (Union f) < κ :=
have card (Union f) ≤ card (sigma (λ i, f i)), from
  ge_of_surjective (λ ⟨i, x, hx⟩, ⟨x, subset_Union _ i hx⟩)
    (λ ⟨x, hx⟩, let ⟨i, hi⟩ := mem_Union.mp hx in ⟨⟨i, x, hi⟩, rfl⟩),
lt_of_le_of_lt this (small_of_small_sigma_of_small κ hI hf)

namespace category_theory
def is_kappa_small (I : Type u) [small_category I] : Prop :=
card (Σ (X Y : I), X ⟶ Y) < κ

lemma ob_small_of_small {I : Type u} [small_category I] (hI : is_kappa_small κ I) :
  card I < κ :=
have card I ≤ card (Σ (X Y : I), X ⟶ Y), from
  le_of_injective (λ i, ⟨i, i, category.id i⟩) (by tidy),
lt_of_le_of_lt this hI

lemma kappa_small_of_ob_and_hom_small {I : Type u} [small_category I]
  (h₀ : card I < κ) (h₁ : ∀ (X Y : I), card (X ⟶ Y) < κ) :
  is_kappa_small κ I :=
begin
  apply small_of_small_sigma_of_small κ h₀, intro X,
  apply small_of_small_sigma_of_small κ h₀, intro Y,
  exact h₁ X Y
end

-- TODO: Move all the size estimates about subgraphs here? & reverse the import

end category_theory

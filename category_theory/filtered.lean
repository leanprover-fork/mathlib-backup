/- Categories which are small relative to a cardinal κ.
   κ-filtered categories.
   Normally we care about these concepts for categories which are
   used to index (co)limits, so we work with small_categories. -/

import category_theory.category
import category_theory.functor
import category_theory.limits.shape -- for cocone
import set_theory.cofinality

universes u u' v'

open classical cardinal

def regular_cardinal := {κ : cardinal.{u} // is_regular κ}
instance : has_coe regular_cardinal.{u} cardinal.{u} := by unfold regular_cardinal; apply_instance

lemma regular_cardinal.infinite (κ : regular_cardinal.{u}) : cardinal.omega.{u} ≤ ↑κ := κ.2.1

variables (κ : regular_cardinal.{u})

lemma is_small_of_finite {S : Type u} [fintype S] : cardinal.mk S < κ :=
calc mk S < omega : lt_omega_iff_fintype.mpr ⟨by apply_instance⟩
      ... ≤ κ     : κ.infinite

-- Why isn't this already, like, the definition
lemma small_of_small_sigma_of_small {I : Type u} (hI : mk I < κ) {f : I → Type u}
  (hf : ∀ i, mk (f i) < κ) : mk (sigma f) < κ :=
sorry
/-
calc
  mk (sigma f)
    = sum (λ i, mk (f i))             : by simp
... < prod (λ (i : I), κ.1)  : sum_lt_prod _ _ hf
... = κ^(mk I)  : by rw prod_const; refl
... = κ         : sorry-/

namespace category_theory
local infixr ` ↝ `:80 := category_theory.functor


def is_kappa_small (I : Type u) [small_category I] : Prop :=
cardinal.mk (Σ (X Y : I), X ⟶ Y) < κ

lemma ob_small_of_small {I : Type u} [small_category I] (hI : is_kappa_small κ I) :
  cardinal.mk I < κ :=
sorry

lemma kappa_small_of_ob_and_hom_small {I : Type u} [small_category I]
  (h₀ : cardinal.mk I < κ) (h₁ : ∀ (X Y : I), cardinal.mk (X ⟶ Y) < κ) :
  is_kappa_small κ I :=
begin
  apply small_of_small_sigma_of_small κ h₀, intro X,
  apply small_of_small_sigma_of_small κ h₀, intro Y,
  exact h₁ X Y
end

-- filtered categories

structure kappa_filtered (C : Type u) [small_category C] : Prop :=
(has_cocones : ∀ {I : Type u} [small_category I] (hI : is_kappa_small κ I) (F : I ↝ C),
  nonempty (limits.cocone F))

-- [A&R, 1.21]
structure kappa_filtered' (C : Type u) [small_category C] : Prop :=
(cone_objs : ∀ {I : Type u} (hI : cardinal.mk I < κ) (F : I → C),
  nonempty Σ (Z : C), Π i, F i ⟶ Z)
(cone_parallel : ∀ {X Y : C} (I : Type u) (hI : cardinal.mk I < κ) (F : I → (X ⟶ Y)),
  ∃ (Z : C) (g : Y ⟶ Z), ∀ i j, F i ≫ g = F j ≫ g)

structure subgraph (C : Type u) [small_category C] : Type u :=
(objs : set C)
(homs : Π X Y : objs, set (X.1 ⟶ Y.1))

structure kappa_filtered'' (C : Type u) [small_category C] : Prop :=
(cone_subgraph : ∀ (S : subgraph C) (hS₀ : cardinal.mk S.objs < κ)
  (hS₁ : cardinal.mk (Σ X Y, S.homs X Y) < κ),
  ∃ (Z : C) (g : Π X : S.objs, X.1 ⟶ Z), ∀ X Y (f : S.homs X Y), f.1 ≫ g Y = g X)

variables {C : Type u} [small_category C]

section 
-- kappa_filtered → kappa_filtered'

def discrete (ob : Type u) : Type u := ob
instance discrete_category (ob : Type u) : small_category (discrete ob) :=
{ hom := λ X Y, ulift (plift (X = Y)),
  id := λ X, ⟨⟨rfl⟩⟩,
  comp := λ X Y Z f g, ⟨⟨f.1.1.trans g.1.1⟩⟩ }

def discrete_functor_of_function {ob : Type u} {D : Type u'} [category.{u' v'} D] (F : ob → D) :
  discrete ob ↝ D :=
{ obj := F, map' := λ X Y f, eq_to_iso (congr_arg F f.1.1) }

lemma discrete_is_small {ob : Type u} (h : cardinal.mk ob < κ) :
  is_kappa_small κ (discrete ob) :=
begin
  apply kappa_small_of_ob_and_hom_small,
  { exact h },
  { intros X Y, change cardinal.mk.{u} (ulift (plift (X = Y))) < κ,
    have : subsingleton (ulift (plift (X = Y))) := by apply_instance,
    calc cardinal.mk.{u} (ulift (plift (X = Y))) ≤ 1 : le_one_iff_subsingleton.mpr this
      ... < omega  : one_lt_omega
      ... ≤ κ      : κ.infinite }
end

inductive suspension (mor : Type u) : Type u
| src {} : suspension
| tgt {} : suspension
open suspension

instance suspension_category (mor : Type u) : small_category (suspension mor) :=
{ hom := λ X Y, match X, Y with
  | src, src := punit
  | src, tgt := mor
  | tgt, src := pempty
  | tgt, tgt := punit
  end,
  id := λ X, match X with
  | src := punit.star
  | tgt := punit.star
  end,
  comp := λ X Y Z f g, match X, Y, Z, f, g with
  | src, src, src, punit.star, punit.star := punit.star
  | src, src, tgt, punit.star, f := f
  | src, tgt, tgt, f, punit.star := f
  | tgt, tgt, tgt, punit.star, punit.star := punit.star
  end,
  id_comp' := λ X Y f, by cases X; cases Y; try { cases f }; refl,
  comp_id' := λ X Y f, by cases X; cases Y; try { cases f }; refl,
  assoc' := λ W X Y Z f g h,
    by cases W; cases X; cases Y; cases Z; try { cases f }; try { cases g }; try { cases h }; refl }

def suspension_functor_of_function {mor : Type u} {D : Type u'} [category.{u' v'} D]
  {A B : D} (F : mor → (A ⟶ B)) : suspension mor ↝ D :=
{ obj := λ X, match X with | src := A | tgt := B end,
  map' := λ X Y f, match X, Y, f with
  | src, src, punit.star := category.id A
  | src, tgt, f := F f
  | tgt, tgt, punit.star := category.id B
  end,
  map_id' := λ X, by cases X; refl,
  map_comp' := λ X Y Z f g, by cases X; cases Y; cases Z; tidy }

instance {mor : Type u} : fintype (suspension mor) :=
⟨⟨src::tgt::0, by simp⟩, λ x, by cases x; simp⟩

-- TODO: move this
instance punit.fintype : fintype punit.{u+1} :=
⟨⟨punit.star::0, by simp⟩, λ x, by cases x; simp⟩

lemma suspension_is_small {mor : Type u} (h : cardinal.mk mor < κ) :
  is_kappa_small κ (suspension mor) :=
begin
  apply kappa_small_of_ob_and_hom_small,
  { apply is_small_of_finite },
  { rintros (_|_) (_|_),
    { change mk punit < _, apply is_small_of_finite },
    { exact h },
    { change mk pempty < _, apply is_small_of_finite },
    { change mk punit < _, apply is_small_of_finite } }
end

lemma one_implies_two (h : kappa_filtered κ C) : kappa_filtered' κ C :=
{ cone_objs := assume I hI F,
    let ⟨t⟩ := h.has_cocones (discrete_is_small κ hI) (discrete_functor_of_function F) in
    ⟨⟨t.X, λ i, t.ι i⟩⟩,
  cone_parallel := assume X Y I hI F,
    let ⟨t⟩ := h.has_cocones (suspension_is_small κ hI) (suspension_functor_of_function F) in
    have ∀ k, F k ≫ t.ι tgt = t.ι src, from assume k, t.w (show @src I ⟶ @tgt I, from k),
    ⟨t.X, t.ι tgt, λ i j, (this i).trans (this j).symm⟩ }

lemma kappa_filtered'.cone_parallel_two (h : kappa_filtered' κ C) {X Y : C} (f g : X ⟶ Y) :
  ∃ (Z : C) (h : Y ⟶ Z), f ≫ h = g ≫ h :=
let ⟨Z, h, hh⟩ :=
  h.cone_parallel (ulift bool) (is_small_of_finite _) (λ i, match i.down with | ff := f | tt := g end) in
⟨Z, h, hh ⟨ff⟩ ⟨tt⟩⟩

lemma two_implies_three (h : kappa_filtered' κ C) : kappa_filtered'' κ C :=
{ cone_subgraph := assume S hS₀ hS₁,
  -- The strategy is as follows:
  -- 1. Form a cocone on all the objects of S, with new vertex Z₀ and cocone maps e_X : X → Z₀
  -- 2. For each morphism f : X → Y in S, coequalize f_X and f_Y ∘ f, via a new map g_f : Z₀ → Z_f
  -- 3. Form a cocone on all the objects Z_f, with new vertex Z₁ and cocone maps j_f : Z_f → Z₁
  -- 4. Coequalize all the morphisms h_f ∘ g_f, with new vertex Z. Call their common composition l.
  -- Then we can build a cocone on all of S which maps X to Z via l ∘ e_X.
  -- If there aren't any morphisms in S, then we have a problem in step 4, but then we can just
  -- use the original cocone Z₀.
  let ⟨⟨Z₀, e⟩⟩ := h.cone_objs hS₀ (λ X, X) in
  have ∀ (f : Σ X Y, S.homs X Y), ∃ (p : Σ Z, Z₀ ⟶ Z), e f.1 ≫ p.2 = (f.2.2.val ≫ e f.2.1) ≫ p.2,
  from assume ⟨X, Y, f⟩, let ⟨Z, h, hh⟩ := h.cone_parallel_two κ (e X) (f.val ≫ e Y) in ⟨⟨Z, h⟩, hh⟩,
  let ⟨g, hg⟩ := axiom_of_choice this,
      ⟨⟨Z₁, j⟩⟩ := h.cone_objs hS₁ (λ f, (g f).1),
      ⟨Z, k, hk⟩ := h.cone_parallel (Σ X Y, S.homs X Y) hS₁ (λ f, (g f).2 ≫ j f) in
  by_cases
    (λ (hhom : nonempty (Σ X Y, S.homs X Y)),
      let ⟨f₀⟩ := hhom in
      have ∀ f : Σ X Y, S.homs X Y, (g f₀).2 ≫ j f₀ ≫ k = (g f).2 ≫ j f ≫ k,
      from assume f, by simpa using hk f₀ f,
      ⟨Z, λ X, e X ≫ (g f₀).2 ≫ j f₀ ≫ k, λ X Y f,
        calc f.val ≫ e Y ≫ (g f₀).snd ≫ j f₀ ≫ k
            = f.val ≫ e Y ≫ (g ⟨X, Y, f⟩).snd ≫ j ⟨X, Y, f⟩ ≫ k   : by rw this
        ... = ((f.val ≫ e Y) ≫ (g ⟨X, Y, f⟩).snd) ≫ j ⟨X, Y, f⟩ ≫ k : by simp
        ... = (e X ≫ (g ⟨X, Y, f⟩).snd) ≫ j ⟨X, Y, f⟩ ≫ k         : by rw hg ⟨X, Y, f⟩
        ... = e X ≫ (g ⟨X, Y, f⟩).snd ≫ j ⟨X, Y, f⟩ ≫ k           : by simp
        ... = e X ≫ (g f₀).snd ≫ j f₀ ≫ k                         : by rw this⟩)
    (λ nohoms, ⟨Z₀, λ X, e X, λ X Y f, by refine absurd _ nohoms; exact ⟨⟨X, Y, f⟩⟩⟩) }

lemma three_implies_one (h : kappa_filtered'' κ C) : kappa_filtered κ C :=
{ has_cocones := assume I catI hI F, by letI := catI; exact
  let S : subgraph C :=
        { objs := {X | ∃ i, F i = X},
          homs := λ X Y, {f | ∃ (ijg : Σ (i j : I), i ⟶ j), F.map ijg.2.2 == f} },
      -- Need: objs is κ-small because it is the image of the κ-small set I (by ob_small_of_small)
      -- Σ X Y, S.homs X Y is κ-small because it is the image of the κ-small set Σ (i j : I), i ⟶ j
      ⟨Z, g, hg⟩ := h.cone_subgraph S sorry sorry in
  ⟨{ X := Z, ι := λ i, g ⟨F i, i, rfl⟩,
     w := assume i i' f,  hg ⟨F i, i, rfl⟩ ⟨F i', i', rfl⟩ ⟨F.map f, ⟨i, i', f⟩, heq.refl _⟩ }⟩ }


end

end category_theory

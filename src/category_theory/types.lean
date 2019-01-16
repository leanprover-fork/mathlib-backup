-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl

import category_theory.functor_category
import category_theory.fully_faithful

namespace category_theory

universes v v' w u u' -- declare the `v`'s first; see `category_theory.category` for an explanation

instance types : large_category (Type u) :=
{ hom     := λ a b, (a → b),
  id      := λ a, id,
  comp    := λ _ _ _ f g, g ∘ f }

@[simp] lemma types_hom {α β : Type u} : (α ⟶ β) = (α → β) := rfl
@[simp] lemma types_id {α : Type u} (a : α) : (𝟙 α : α → α) a = a := rfl
@[simp] lemma types_comp {α β γ : Type u} (f : α → β) (g : β → γ) (a : α) : (((f : α ⟶ β) ≫ (g : β ⟶ γ)) : α ⟶ γ) a = g (f a) := rfl

namespace functor_to_types
variables {C : Type u} [𝒞 : category.{v} C] (F G H : C ⥤ (Type w)) {X Y Z : C}
include 𝒞
variables (σ : F ⟹ G) (τ : G ⟹ H)

@[simp] lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) (a : F.obj X) : (F.map (f ≫ g)) a = (F.map g) ((F.map f) a) :=
by simp

@[simp] lemma map_id (a : F.obj X) : (F.map (𝟙 X)) a = a :=
by simp

lemma naturality (f : X ⟶ Y) (x : F.obj X) : σ.app Y ((F.map f) x) = (G.map f) (σ.app X x) :=
congr_fun (σ.naturality f) x

@[simp] lemma vcomp (x : F.obj X) : (σ ⊟ τ).app X x = τ.app X (σ.app X x) := rfl

variables {D : Type u'} [𝒟 : category.{u'} D] (I J : D ⥤ C) (ρ : I ⟹ J) {W : D}

@[simp] lemma hcomp (x : (I ⋙ F).obj W) : (ρ ◫ σ).app W x = (G.map (ρ.app W)) (σ.app (I.obj W) x) := rfl

end functor_to_types

def ulift_trivial (V : Type u) : ulift.{u} V ≅ V := by tidy

def ulift_functor : (Type u) ⥤ (Type (max u v)) :=
{ obj := λ X, ulift.{v} X,
  map := λ X Y f, λ x : ulift.{v} X, ulift.up (f x.down) }

@[simp] lemma ulift_functor.map {X Y : Type u} (f : X ⟶ Y) (x : ulift.{v} X) :
  ulift_functor.map f x = ulift.up (f x.down) := rfl

instance ulift_functor_faithful : fully_faithful ulift_functor :=
{ preimage := λ X Y f x, (f (ulift.up x)).down,
  injectivity' := λ X Y f g p, funext $ λ x,
    congr_arg ulift.down ((congr_fun p (ulift.up x)) : ((ulift.up (f x)) = (ulift.up (g x)))) }

section forget
variables {C : Type u → Type v} {hom : ∀α β, C α → C β → (α → β) → Prop} [i : concrete_category hom]
include i

/-- The forgetful functor from a bundled category to `Type`. -/
def forget : bundled C ⥤ Type u := { obj := bundled.α, map := λa b h, h.1 }

instance forget.faithful : faithful (forget : bundled C ⥤ Type u) := {}

end forget

end category_theory

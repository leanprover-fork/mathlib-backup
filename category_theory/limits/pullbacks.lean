-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.shapes.pullbacks
import category_theory.limits.limits

open category_theory

namespace category_theory.limits

universes u v w

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables {X Y Z : C}

attribute [simp] walking_cospan_hom_id walking_span_hom_id

open walking_cospan
open walking_span
open walking_cospan_hom
open walking_span_hom

section pullback

variables {f : X ⟶ Z} {g : Y ⟶ Z}

def is_pullback (t : square f g) := is_limit t

variables {t : square f g}

instance is_pullback_subsingleton : subsingleton (is_pullback t) :=
by dsimp [is_pullback]; apply_instance

lemma is_pullback.hom_ext (p : is_pullback t) {W : C} {k h : W ⟶ t.X}
  (w_left : k ≫ t.π.app left = h ≫ t.π.app left)
  (w_right : k ≫ t.π.app right = h ≫ t.π.app right) : k = h :=
begin
 rw [p.hom_lift k, p.hom_lift h]; congr,
 ext j, cases j,
 exact w_left,
 exact w_right,
 have v := t.π.naturality walking_cospan_hom.inl,
 simp at v,
 erw category.id_comp at v,
 rw [v, ←category.assoc, w_left, category.assoc],
end

end pullback

section pushout
variables {f : X ⟶ Y} {g : X ⟶ Z}

def is_pushout (t : cosquare f g) := is_colimit t

variables {t : cosquare f g}

instance is_pushout_subsingleton : subsingleton (is_pushout t) :=
by dsimp [is_pushout]; apply_instance

lemma is_pushout.hom_ext (p : is_pushout t) {W : C} {k h : t.X ⟶ W}
  (w_left : t.ι.app left ≫ k = t.ι.app left ≫ h)
  (w_right : t.ι.app right ≫ k = t.ι.app right ≫ h) : k = h :=
begin
 rw [p.hom_desc k, p.hom_desc h]; congr,
 ext j, cases j,
 have v := t.ι.naturality walking_span_hom.fst,
 simp at v,
 erw category.comp_id at v,
 rw [←v, category.assoc, w_left, ←category.assoc],
 exact w_left,
 exact w_right,
end

end pushout

variable (C)

-- TODO turn these into pis
class has_pullbacks :=
(square : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), square.{u v} f g)
(is_pullback : Π {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z), is_pullback (square f g) . obviously)
class has_pushouts :=
(cosquare : Π {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), cosquare.{u v} f g)
(is_pushout : Π {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z), is_pushout (cosquare f g) . obviously)

variable {C}

-- Special cases of this may be marked with [instance] as desired.
def has_pullbacks_of_has_limits
  [limits.has_limits_of_shape.{u v} walking_cospan C] : has_pullbacks.{u v} C :=
{ square := λ X Y Z f g, limit.cone (cospan f g),
  is_pullback := λ X Y Z f g, limit.is_limit (cospan f g) }
def has_pushouts_of_has_colimits
  [limits.has_colimits_of_shape.{u v} walking_span C] : has_pushouts.{u v} C :=
{ cosquare := λ X Y Z f g, colimit.cocone (span f g),
  is_pushout := λ X Y Z f g, colimit.is_colimit (span f g) }

section pullback
variable [has_pullbacks.{u v} C]
variables (f : X ⟶ Z) (g : Y ⟶ Z)

def pullback.square : square f g := has_pullbacks.square.{u v} f g
def pullback := (pullback.square f g).X
def pullback.π₁ : pullback f g ⟶ X := (pullback.square f g).π₁
def pullback.π₂ : pullback f g ⟶ Y := (pullback.square f g).π₂
@[simp] lemma pullback.w : pullback.π₁ f g ≫ f = pullback.π₂ f g ≫ g :=
begin
  erw ((pullback.square f g).w inl),
  erw ((pullback.square f g).w inr)
end
-- TODO rename
def pullback.universal_property : is_pullback (pullback.square f g) :=
has_pullbacks.is_pullback.{u v} C f g

def has_limits_of_shape_of_has_pullbacks [has_pullbacks.{u v} C] :
  limits.has_limits_of_shape.{u v} walking_cospan.{v} C :=
λ F,
{ cone := cone.of_square (pullback.square (F.map inl) (F.map inr)),
  is_limit := let is_pullback := pullback.universal_property (F.map inl) (F.map inr) in
  { lift := λ s, is_pullback.lift (square.of_cone s),
    fac' := λ s j,
    begin
      dsimp at *,
      cases j; simp,
    end,
    uniq' := λ s m w, is_pullback.uniq (square.of_cone s) m
      (λ j, begin have h := w j, cases j; simp at *; exact h end) } }.

@[extensionality] lemma pullback.hom_ext [has_pullbacks.{u v} C] {W : C}
  {k h : W ⟶ pullback f g}
  (w_left : k ≫ pullback.π₁ f g = h ≫ pullback.π₁ f g)
  (w_right : k ≫ pullback.π₂ f g = h ≫ pullback.π₂ f g) : k = h :=
(pullback.universal_property f g).hom_ext w_left w_right

def pullback.lift [has_pullbacks.{u v} C] {W : C}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) : W ⟶ pullback f g :=
(pullback.universal_property f g).lift (square.mk f' g' eq)

@[simp] lemma pullback.lift_π₁ [has_pullbacks.{u v} C] {W : C}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) :
  pullback.lift f g f' g' eq ≫ pullback.π₁ f g = f' :=
(pullback.universal_property f g).fac (square.mk f' g' eq) _

@[simp] lemma pullback.lift_π₂ [has_pullbacks.{u v} C] {W : C}
  (f' : W ⟶ X) (g' : W ⟶ Y) (eq : f' ≫ f = g' ≫ g) :
  pullback.lift f g f' g' eq ≫ pullback.π₂ f g = g' :=
(pullback.universal_property f g).fac (square.mk f' g' eq) _

@[simp] lemma pullback.lift_id [has_pullbacks.{u v} C]
  (eq : pullback.π₁ f g ≫ f = pullback.π₂ f g ≫ g) :
  pullback.lift f g _ _ eq = 𝟙 _ :=
begin
  refine ((pullback.universal_property f g).uniq _ _ _).symm,
  rintros (_ | _ | _),
  { dsimp [square.mk], simp, refl },
  { dsimp [square.mk], simp, refl },
  { dsimp [square.mk], simp,
    have := (pullback.square f g).π.naturality walking_cospan_hom.inr,
    dsimp at this,
    simpa }
end

def pullback.hom_iso {P : C} : (P ⟶ pullback f g) ≅ { p : (P ⟶ X) × (P ⟶ Y) // p.1 ≫ f = p.2 ≫ g } :=
{ hom := λ k,
  ⟨ (k ≫ pullback.π₁ f g, k ≫ pullback.π₂ f g),
    begin
      rw [category.assoc, category.assoc],
      rw pullback.w,
    end ⟩,
  inv := λ p, pullback.lift f g p.val.1 p.val.2 p.property }

end pullback

section pushout
variable [has_pushouts.{u v} C]
variables (f : X ⟶ Y) (g : X ⟶ Z)

def pushout.cosquare : cosquare f g := has_pushouts.cosquare.{u v} f g
def pushout := (pushout.cosquare f g).X
def pushout.ι₁ : Y ⟶ pushout f g := (pushout.cosquare f g).ι₁
def pushout.ι₂ : Z ⟶ pushout f g := (pushout.cosquare f g).ι₂
@[simp] lemma pushout.w : f ≫ pushout.ι₁ f g = g ≫ pushout.ι₂ f g :=
begin
  erw ((pushout.cosquare f g).w fst),
  erw ((pushout.cosquare f g).w snd)
end
-- TODO rename
def pushout.universal_property : is_pushout (pushout.cosquare f g) :=
has_pushouts.is_pushout.{u v} C f g

def has_colimits_of_shape_of_has_pushouts [has_pushouts.{u v} C] :
  limits.has_colimits_of_shape.{u v} walking_span.{v} C :=
λ F,
{ cocone := cocone.of_cosquare (pushout.cosquare (F.map fst) (F.map snd)),
  is_colimit := let is_pushout := pushout.universal_property (F.map fst) (F.map snd) in
  { desc := λ s, is_pushout.desc (cosquare.of_cocone s),
    fac' := λ s j,
    begin
      dsimp at *,
      cases j; simp,
    end,
    uniq' := λ s m w, is_pushout.uniq (cosquare.of_cocone s) m
      (λ j, begin have h := w j, cases j; simp at *; exact h end) } }.

@[extensionality] lemma pushout.hom_ext [has_pushouts.{u v} C] {W : C}
  {k h : pushout f g ⟶ W}
  (w_left : pushout.ι₁ f g ≫ k = pushout.ι₁ f g ≫ h)
  (w_right : pushout.ι₂ f g ≫ k = pushout.ι₂ f g ≫ h) : k = h :=
(pushout.universal_property f g).hom_ext w_left w_right

def pushout.desc [has_pushouts.{u v} C] {W : C}
  (f' : Y ⟶ W) (g' : Z ⟶ W) (eq : f ≫ f' = g ≫ g') : pushout f g ⟶ W :=
(pushout.universal_property f g).desc (cosquare.mk f' g' eq)

@[simp] lemma pushout.lift_π₁ [has_pushouts.{u v} C] {W : C}
  (f' : Y ⟶ W) (g' : Z ⟶ W) (eq : f ≫ f' = g ≫ g') :
  pushout.ι₁ f g ≫ pushout.desc f g f' g' eq = f' :=
(pushout.universal_property f g).fac (cosquare.mk f' g' eq) _

@[simp] lemma pushout.lift_π₂ [has_pushouts.{u v} C] {W : C}
  (f' : Y ⟶ W) (g' : Z ⟶ W) (eq : f ≫ f' = g ≫ g') :
  pushout.ι₂ f g ≫ pushout.desc f g f' g' eq = g' :=
(pushout.universal_property f g).fac (cosquare.mk f' g' eq) _

@[simp] lemma pushout.lift_id [has_pushouts.{u v} C]
  (eq : f ≫ pushout.ι₁ f g = g ≫ pushout.ι₂ f g) :
  pushout.desc f g _ _ eq = 𝟙 _ :=
begin
  refine ((pushout.universal_property f g).uniq _ _ _).symm,
  rintros (_ | _ | _),
  { dsimp [cosquare.mk], simp,
    have := (pushout.cosquare f g).ι.naturality walking_span_hom.snd,
    dsimp at this,
    erw ← this,
    simpa },
  { dsimp [cosquare.mk], erw category.comp_id, refl },
  { dsimp [cosquare.mk], erw category.comp_id, refl },
end

def pushout.hom_iso {P : C} : (pushout f g ⟶ P) ≅ { p : (Y ⟶ P) × (Z ⟶ P) // f ≫ p.1 = g ≫ p.2 } :=
{ hom := λ k,
  ⟨ (pushout.ι₁ f g ≫ k, pushout.ι₂ f g ≫ k),
    begin
      rw [←category.assoc, ←category.assoc],
      rw pushout.w,
    end ⟩,
  inv := λ p, pushout.desc f g p.val.1 p.val.2 p.property }

end pushout

end category_theory.limits

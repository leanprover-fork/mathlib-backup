-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.limits.pullbacks
import category_theory.limits.shapes.equalizers

open category_theory

namespace category_theory.limits

universes u v w

open walking_pair
open walking_pair_hom

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y : C}
variables {f g : X ⟶ Y}

def is_equalizer (t : fork f g) := is_limit t
def is_coequalizer (t : cofork f g) := is_colimit t

lemma is_equalizer.mono {t : fork f g} (h : is_equalizer t) : mono t.ι :=
⟨λ W (e₁ e₂ : W ⟶ t.X) H, begin
   unfold fork.ι at H,
   apply h.hom_ext,
   rintro (_|_),
   { exact H },
   { rw [←t.w left, ←category.assoc, ←category.assoc, H] }
 end⟩

lemma is_coequalizer.epi {t : cofork f g} (h : is_coequalizer t) : epi t.π :=
⟨λ W (e₁ e₂ : t.X ⟶ W) H, begin
   unfold cofork.π at H,
   apply h.hom_ext,
   rintro (_|_),
   { rw [←t.w left, category.assoc, category.assoc, H] },
   { exact H }
 end⟩

variables {t : fork f g}
variables {s : cofork f g}

instance is_equalizer_subsingleton : subsingleton (is_equalizer t) :=
by dsimp [is_equalizer]; apply_instance
instance is_coequalizer_subsingleton : subsingleton (is_coequalizer s) :=
by dsimp [is_coequalizer]; apply_instance

class has_equalizer {X Y : C} (f g : X ⟶ Y) :=
(fork : fork.{u v} f g)
(is_equalizer : is_equalizer fork . obviously)
class has_coequalizer {X Y : C} (f g : X ⟶ Y) :=
(cofork : cofork.{u v} f g)
(is_coequalizer : is_coequalizer cofork . obviously)

variable (C)

-- TODO replace these
class has_equalizers :=
(fork : Π {X Y : C} (f g : X ⟶ Y), fork.{u v} f g)
(is_equalizer : Π {X Y : C} (f g : X ⟶ Y), is_equalizer (fork f g) . obviously)
class has_coequalizers :=
(cofork : Π {X Y : C} (f g : X ⟶ Y), cofork.{u v} f g)
(is_coequalizer : Π {X Y : C} (f g : X ⟶ Y), is_coequalizer (cofork f g) . obviously)

variable {C}

instance has_equalizer_of_has_equalizers [has_equalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) :
  has_equalizer.{u v} f g :=
{ fork := has_equalizers.fork f g,
  is_equalizer := has_equalizers.is_equalizer C f g }
instance has_coequalizer_of_has_coequalizers [has_coequalizers.{u v} C] {X Y : C} (f g : X ⟶ Y) :
  has_coequalizer.{u v} f g :=
{ cofork := has_coequalizers.cofork f g,
  is_coequalizer := has_coequalizers.is_coequalizer C f g }

-- Special cases of this may be marked with [instance] as desired.
def has_equalizers_of_has_limits [limits.has_limits_of_shape.{u v} walking_pair C] :
  has_equalizers.{u v} C :=
{ fork := λ X Y f g, limit.cone (pair f g),
  is_equalizer := λ X Y f g, limit.is_limit (pair f g) }
def has_coequalizers_of_has_colimits [limits.has_colimits_of_shape.{u v} walking_pair C] :
  has_coequalizers.{u v} C :=
{ cofork := λ X Y f g, colimit.cocone (pair f g),
  is_coequalizer := λ X Y f g, colimit.is_colimit (pair f g) }

variable {C}

section
variables (f g)

def equalizer.fork [has_equalizer f g] : fork f g := has_equalizer.fork.{u v} f g
def coequalizer.cofork [has_coequalizer f g] : cofork f g := has_coequalizer.cofork.{u v} f g
def equalizer [has_equalizer f g] := (equalizer.fork f g).X
def coequalizer [has_coequalizer f g] := (coequalizer.cofork f g).X
def equalizer.ι [has_equalizer f g] : equalizer f g ⟶ X := (equalizer.fork f g).π.app zero
def coequalizer.π [has_coequalizer f g] : Y ⟶ coequalizer f g := (coequalizer.cofork f g).ι.app one
@[simp] lemma equalizer.w [has_equalizer f g] : equalizer.ι f g ≫ f = equalizer.ι f g ≫ g :=
begin
  erw ((equalizer.fork f g).w left),
  erw ((equalizer.fork f g).w right)
end
@[simp] lemma coequalizer.w
  [has_coequalizer f g] : f ≫ coequalizer.π f g = g ≫ coequalizer.π f g :=
begin
  erw ((coequalizer.cofork f g).w left),
  erw ((coequalizer.cofork f g).w right)
end
def equalizer.universal_property [has_equalizer f g] : is_equalizer (equalizer.fork f g) :=
has_equalizer.is_equalizer f g
def coequalizer.universal_property
  [has_coequalizer f g] : is_coequalizer (coequalizer.cofork f g) :=
has_coequalizer.is_coequalizer f g

def equalizer.lift
  [has_equalizer f g] {P : C} (h : P ⟶ X) (w : h ≫ f = h ≫ g) : P ⟶ equalizer f g :=
(equalizer.universal_property f g).lift (fork.of_ι h w)
def coequalizer.desc
  [has_coequalizer f g] {P : C} (h : Y ⟶ P) (w : f ≫ h = g ≫ h) : coequalizer f g ⟶ P :=
(coequalizer.universal_property f g).desc (cofork.of_π h w)

@[simp] lemma equalizer.lift_ι [has_equalizer f g] {P : C} (h : P ⟶ X) (w : h ≫ f = h ≫ g) :
  equalizer.lift f g h w ≫ equalizer.ι f g = h :=
is_limit.fac _ _ _
@[simp] lemma coequalizer.π_desc [has_coequalizer f g] {P : C} (h : Y ⟶ P) (w : f ≫ h = g ≫ h) :
  coequalizer.π f g ≫ coequalizer.desc f g h w = h :=
is_colimit.fac _ _ _

instance [has_equalizer f g] : mono (equalizer.ι f g) :=
(has_equalizer.is_equalizer f g).mono
instance [has_coequalizer f g] : epi (coequalizer.π f g) :=
(has_coequalizer.is_coequalizer f g).epi

@[extensionality] lemma equalizer.hom_ext [has_equalizer f g] {P : C}
  {h k : P ⟶ equalizer f g}
  (w : h ≫ equalizer.ι f g = k ≫ equalizer.ι f g) : h = k := mono.right_cancellation h k w
@[extensionality] lemma coequalizer.hom_ext [has_coequalizer f g] {P : C}
  {h k : coequalizer f g ⟶ P}
  (w : coequalizer.π f g ≫ h = coequalizer.π f g ≫ k) : h = k := epi.left_cancellation h k w

def equalizer.hom_iso [has_equalizer f g] {P : C} :
  (P ⟶ equalizer f g) ≅ { p : P ⟶ X // p ≫ f = p ≫ g } :=
{ hom := λ k,
  ⟨ k ≫ equalizer.ι f g,
    begin
      rw [category.assoc, category.assoc],
      rw equalizer.w,
    end ⟩,
  inv := λ p, equalizer.lift f g p.val p.property }
def coequalizer.hom_iso [has_coequalizer f g] {P : C} :
  (coequalizer f g ⟶ P) ≅ { p : Y ⟶ P // f ≫ p = g ≫ p } :=
{ hom := λ k,
  ⟨ coequalizer.π f g ≫ k,
    begin
      rw [←category.assoc, ←category.assoc],
      rw coequalizer.w,
    end ⟩,
  inv := λ p, coequalizer.desc f g p.val p.property }

def has_limits_of_shape_of_has_equalizers [has_equalizers.{u v} C] :
  limits.has_limits_of_shape.{u v} walking_pair.{v} C :=
λ F,
{ cone := cone.of_fork (equalizer.fork (F.map left) (F.map right)),
  is_limit := let is_equalizer := equalizer.universal_property (F.map left) (F.map right) in
  { lift := λ s, is_equalizer.lift (fork.of_cone s),
    fac' := λ s j,
    begin
      dsimp at *,
      cases j; simp,
    end,
    uniq' := λ s m w, is_equalizer.uniq (fork.of_cone s) m
      (λ j, begin have h := w j, cases j; simp at *; exact h end) } }

def has_colimits_of_shape_of_has_coequalizers [has_coequalizers.{u v} C] :
  limits.has_colimits_of_shape.{u v} walking_pair.{v} C :=
λ F,
{ cocone := cocone.of_cofork (coequalizer.cofork (F.map left) (F.map right)),
  is_colimit :=
  let is_coequalizer := coequalizer.universal_property (F.map left) (F.map right) in
  { desc := λ s, is_coequalizer.desc (cofork.of_cocone s),
    fac' := λ s j,
    begin
      dsimp at *,
      cases j; simp,
    end,
    uniq' := λ s m w, is_coequalizer.uniq (cofork.of_cocone s) m
      (λ j, begin have h := w j, cases j; simp at *; exact h end) } }

end

end category_theory.limits

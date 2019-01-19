-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.limits.limits
import category_theory.limits.shapes.products
import category_theory.discrete_category

open category_theory

namespace category_theory.limits

universes u v w

variables {β : Type v}
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section products
variables {f : β → C}

def is_product (t : fan f) := is_limit t

variables {t : fan f}

instance is_product_subsingleton : subsingleton (is_product t) :=
by dsimp [is_product]; apply_instance

variable {C}

class has_product {β : Type v} (f : β → C) :=
(fan : fan.{u v} f)
(is_product : is_product fan)

variable (C)

section
omit 𝒞
@[class] def has_products_of_shape (β : Type v) (C : Type u) [𝒞 : category.{u v} C] : Type (max u v) :=
Π f : β → C, has_product f
end

@[class] def has_products : Type (max u (v+1)) :=
Π {β : Type v}, by exactI has_products_of_shape β C

variable {C}

instance has_product_of_has_products_of_shape
  {β : Type v} [H : has_products_of_shape.{u v} β C] (f : β → C) : has_product f :=
H f

instance has_products_of_shape_of_has_products
  {β : Type v} [H : has_products.{u v} C] : has_products_of_shape.{u v} β C :=
H

-- Special cases of this may be marked with [instance] as desired.
def has_products_of_shape_of_has_limits_of_shape
  [limits.has_limits_of_shape.{u v} (discrete β) C] : has_products_of_shape.{u v} β C :=
λ f,
{ fan := limit.cone (functor.of_function f),
  is_product := limit.is_limit (functor.of_function f) }
def has_products_of_has_limits
  [∀ β : Type v, limits.has_limits_of_shape.{u v} (discrete β) C] : has_products.{u v} C :=
λ β f,
{ fan := limit.cone (functor.of_function f),
  is_product := limit.is_limit (functor.of_function f) }

def has_limit_of_has_product
  {β : Type v} (f : β → C) [i : has_product f] : limits.has_limit (functor.of_function f) :=
{ cone := has_product.fan f,
  is_limit := has_product.is_product f }

def has_limits_of_shape_of_has_products_of_shape
  {β : Type v} [has_products_of_shape.{u v} β C] :
  limits.has_limits_of_shape.{u v} (discrete β) C :=
λ F,
{ cone := cone.of_fan (has_product.fan F.obj),
  is_limit := let is_product := has_product.is_product F.obj in
  { lift := λ s, is_product.lift (fan.of_cone s),
    fac' := λ s j, is_product.fac (fan.of_cone s) j,
    uniq' := λ s m j, is_product.uniq (fan.of_cone s) m j } }

section

local attribute [instance] has_limit_of_has_product has_limits_of_shape_of_has_products_of_shape

def pi.fan (f : β → C) [has_product f] : fan f := has_product.fan.{u v} f
protected def pi (f : β → C) [has_product f] : C := (pi.fan f).X
def pi.π (f : β → C) [has_product f] (b : β) : limits.pi f ⟶ f b :=
(pi.fan f).π.app b
def pi.universal_property (f : β → C) [has_product f] : is_product (pi.fan f) :=
has_product.is_product.{u v} f

@[simp] lemma pi.fan_π
  (f : β → C) [has_product f] (b : β) :
  (pi.fan f).π.app b = @pi.π _ C _ f _ b := rfl

@[simp] def cone.of_function
  {f : β → C} {P : C} (p : Π b, P ⟶ f b) : cone (functor.of_function f) :=
{ X := P,
  π := { app := p } }

def pi.lift {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) : P ⟶ limits.pi f :=
limit.lift _ (cone.of_function p)

@[simp] lemma pi.lift_π
  {f : β → C} [has_product f] {P : C} (p : Π b, P ⟶ f b) (b : β) : pi.lift p ≫ pi.π f b = p b :=
limit.lift_π (cone.of_function p) b

def pi.map
  {f : β → C} [has_product f] {g : β → C} [has_product g] (k : Π b, f b ⟶ g b) :
  (limits.pi f) ⟶ (limits.pi g) :=
pi.lift (λ b, pi.π f b ≫ k b)

@[simp] lemma pi.map_π
  {f : β → C} [has_product f] {g : β → C} [has_product g] (k : Π b, f b ⟶ g b) (b : β) :
  pi.map k ≫ pi.π g b = pi.π f b ≫ k b :=
by erw is_limit.fac; refl

def pi.pre {α} (f : α → C) [has_product.{u v} f] (h : β → α) [has_product.{u v} (f ∘ h)] :
  limits.pi f ⟶ limits.pi (f ∘ h) :=
pi.lift (λ g, pi.π f (h g))

@[simp] lemma pi.pre_π {α}
  (f : α → C) [has_product.{u v} f] (h : β → α) [has_product.{u v} (f ∘ h)] (b : β) :
  pi.pre f h ≫ pi.π (f ∘ h) b = pi.π f (h b) :=
by erw is_limit.fac; refl

section

variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def pi.post (f : β → C) [has_product f] (G : C ⥤ D) [has_product (G.obj ∘ f)] :
  G.obj (limits.pi f) ⟶ (limits.pi (G.obj ∘ f)) :=
@is_limit.lift _ _ _ _ _
  (pi.fan (G.obj ∘ f))
  (pi.universal_property _)
  { X := _,
    π := { app := λ b, G.map (pi.π f b) } }

@[simp] lemma pi.post_π (f : β → C) [has_product f] (G : C ⥤ D) [has_product (G.obj ∘ f)] (b : β) :
  pi.post f G ≫ pi.π _ b = G.map (pi.π f b) :=
by erw is_limit.fac; refl
end

@[extensionality] lemma pi.hom_ext
  {f : β → C} [has_product f]
  {X : C} {g h : X ⟶ limits.pi f} (w : ∀ b, g ≫ pi.π f b = h ≫ pi.π f b) : g = h :=
limit.hom_ext w

def pi.hom_iso {f : β → C} [has_product f] {P : C} : (P ⟶ limits.pi f) ≅ Π b, P ⟶ f b :=
{ hom := λ g b, g ≫ pi.π f b,
  inv := λ g, pi.lift g }

@[simp] def pi.lift_map
  [has_products_of_shape.{u v} β C] {f : β → C} {g : β → C}
  {P : C} (p : Π b, P ⟶ f b) (k : Π b, f b ⟶ g b) :
  pi.lift p ≫ pi.map k = pi.lift (λ b, p b ≫ k b) :=
limit.lift_map (nat_trans.of_function k) (cone.of_function p)

@[simp] def pi.map_map [has_products_of_shape.{u v} β C] {f1 : β → C} {f2 : β → C} {f3 : β → C}
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  pi.map (λ b, k1 b ≫ k2 b) = pi.map k1 ≫ pi.map k2 :=
lim.map_comp (nat_trans.of_function k1) (nat_trans.of_function k2)

@[simp] def pi.lift_pre
  {α : Type v} {f : β → C} [has_product f]
  {P : C} (p : Π b, P ⟶ f b) (h : α → β) [has_product (f ∘ h)]:
  pi.lift p ≫ pi.pre _ h = pi.lift (λ a, p (h a)) :=
by ext1; simp.

def pi.map_pre
  {α : Type v} [has_products_of_shape.{u v} β C] [has_products_of_shape.{u v} α C]
  {f g : β → C} (k : Π b : β, f b ⟶ g b)
  (e : α → β) :
  pi.map k ≫ pi.pre g e = pi.pre f e ≫ pi.map (λ a, k (e a)) :=
limit.map_pre (nat_trans.of_function k) (discrete.lift e)

@[simp] lemma pi.pre_pre
  {γ δ : Type v}
  [has_products_of_shape.{u v} β C]
  [has_products_of_shape.{u v} γ C]
  [has_products_of_shape.{u v} δ C]
  (f : β → C) (g : γ → β) (h : δ → γ) :
  pi.pre f g ≫ pi.pre (f ∘ g) h = pi.pre f (g ∘ h) :=
by ext1; simp.

section
variables {D : Type u} [category.{u v} D] [has_products.{u v} D]

@[simp] def pi.lift_post
  [has_products_of_shape.{u v} β C] {f : β → C}
  {P : C} (k : Π b : β, P ⟶ f b) (G : C ⥤ D) :
  G.map (pi.lift k) ≫ pi.post f G = pi.lift (λ b, G.map (k b)) :=
begin
  /- `obviously` says -/
  ext1, dsimp, simp,
  erw ←functor.map_comp,
  simp,
end


def pi.map_post
  [has_products_of_shape.{u v} β C] {f g : β → C} (k : Π b : β, f b ⟶ g b) (H : C ⥤ D) :
  H.map (pi.map k) ≫ pi.post g H = pi.post f H ≫ pi.map (λ b, H.map (k b)) :=
limit.map_post (nat_trans.of_function k) H

def pi.pre_post
  {α} [has_products_of_shape.{u v} β C] [has_products_of_shape.{u v} α C]
  (f : β → C) (g : α → β) (G : C ⥤ D) :
  G.map (pi.pre f g) ≫ pi.post (f ∘ g) G = pi.post f G ≫ pi.pre (G.obj ∘ f) g :=
limit.pre_post (discrete.lift g) (functor.of_function f) G

@[simp] def pi.post_post
  [has_products_of_shape.{u v} β C]
  {E : Type u} [category.{u v} E] [has_products.{u v} E] (f : β → C) (G : C ⥤ D) (H : D ⥤ E) :
  H.map (pi.post f G) ≫ pi.post (G.obj ∘ f) H = pi.post f (G ⋙ H) :=
limit.post_post (functor.of_function f) G H
end
end
end products

section coproducts
variables {f : β → C}

def is_coproduct (t : cofan f) := is_colimit t

variables {t : cofan f}

instance is_coproduct_subsingleton : subsingleton (is_coproduct t) :=
by dsimp [is_coproduct]; apply_instance

variable {C}

class has_coproduct {β : Type v} (f : β → C) :=
(cofan : cofan.{u v} f)
(is_coproduct : is_coproduct cofan)

variable (C)

section
omit 𝒞
@[class] def has_coproducts_of_shape (β : Type v) (C : Type u) [𝒞 : category.{u v} C] : Type (max u v) :=
Π f : β → C, has_coproduct f
end

@[class] def has_coproducts : Type (max u (v+1)) :=
Π {β : Type v}, by exactI has_coproducts_of_shape β C

variable {C}

instance has_coproduct_of_has_coproducts_of_shape
  {β : Type v} [H : has_coproducts_of_shape.{u v} β C] (f : β → C) : has_coproduct f :=
H f

instance has_coproducts_of_shape_of_has_coproducts
  {β : Type v} [H : has_coproducts.{u v} C] : has_coproducts_of_shape.{u v} β C :=
H

-- Special cases of this may be marked with [instance] as desired.
def has_coproducts_of_shape_of_has_colimits_of_shape
  [limits.has_colimits_of_shape.{u v} (discrete β) C] : has_coproducts_of_shape.{u v} β C :=
λ f,
{ cofan := colimit.cocone (functor.of_function f),
  is_coproduct := colimit.is_colimit (functor.of_function f) }
def has_coproducts_of_has_colimits
  [∀ β : Type v, limits.has_colimits_of_shape.{u v} (discrete β) C] : has_coproducts.{u v} C :=
λ β f,
{ cofan := colimit.cocone (functor.of_function f),
  is_coproduct := colimit.is_colimit (functor.of_function f) }

def has_colimit_of_has_coproduct
  {β : Type v} (f : β → C) [has_coproduct f] : limits.has_colimit (functor.of_function f) :=
{ cocone := has_coproduct.cofan f,
  is_colimit := has_coproduct.is_coproduct f }

def has_colimits_of_shape_of_has_coproducts_of_shape
  {β : Type v} [has_coproducts_of_shape.{u v} β C] :
  limits.has_colimits_of_shape.{u v} (discrete β) C :=
λ F,
{ cocone := cocone.of_cofan (has_coproduct.cofan F.obj),
  is_colimit := let is_coproduct := has_coproduct.is_coproduct F.obj in
  { desc := λ s, is_coproduct.desc (cofan.of_cocone s),
    fac' := λ s j, is_coproduct.fac (cofan.of_cocone s) j,
    uniq' := λ s m j, is_coproduct.uniq (cofan.of_cocone s) m j } }

section

local attribute [instance] has_colimit_of_has_coproduct
                           has_colimits_of_shape_of_has_coproducts_of_shape

def sigma.cofan (f : β → C) [has_coproduct f] := has_coproduct.cofan.{u v} f
protected def sigma (f : β → C) [has_coproduct f] : C := (sigma.cofan f).X
def sigma.ι (f : β → C) [has_coproduct f] (b : β) : f b ⟶ limits.sigma f :=
(sigma.cofan f).ι.app b
def sigma.universal_property (f : β → C) [has_coproduct f] : is_coproduct (sigma.cofan f) :=
has_coproduct.is_coproduct.{u v} f

@[simp] lemma sigma.cofan_ι
  (f : β → C) [has_coproduct f] (b : β) :
  (sigma.cofan f).ι.app b = @sigma.ι _ C _ f _ b := rfl

@[simp] def cocone.of_function
  {f : β → C} {P : C} (p : Π b, f b ⟶ P) : cocone (functor.of_function f) :=
{ X := P,
  ι := { app := p } }

def sigma.desc {f : β → C} [has_coproduct f] {P : C} (p : Π b, f b ⟶ P) : limits.sigma f ⟶ P :=
colimit.desc _ (cocone.of_function p)

@[simp] lemma sigma.ι_desc {f : β → C} [has_coproduct f] {P : C} (p : Π b, f b ⟶ P) (b : β) :
  sigma.ι f b ≫ sigma.desc p = p b :=
colimit.ι_desc (cocone.of_function p) b

def sigma.map
  {f : β → C} [has_coproduct f] {g : β → C} [has_coproduct g] (k : Π b, f b ⟶ g b) :
  (limits.sigma f) ⟶ (limits.sigma g) :=
sigma.desc (λ b, k b ≫ sigma.ι g b)

@[simp] lemma sigma.ι_map
  {f : β → C} [has_coproduct f] {g : β → C} [has_coproduct g] (k : Π b, f b ⟶ g b) (b : β) :
  sigma.ι f b ≫ sigma.map k = k b ≫ sigma.ι g b :=
by erw is_colimit.fac; refl

def sigma.pre {α} (f : α → C) [has_coproduct.{u v} f] (h : β → α) [has_coproduct (f ∘ h)] :
  limits.sigma (f ∘ h) ⟶ limits.sigma f :=
sigma.desc (λ g, sigma.ι f (h g))

@[simp] lemma sigma.ι_pre
  {α} (f : α → C) [has_coproduct.{u v} f] (h : β → α) [has_coproduct (f ∘ h)] (b : β) :
  sigma.ι (f ∘ h) b ≫ sigma.pre f h = sigma.ι f (h b) :=
by erw is_colimit.fac; refl

section
variables {D : Type u} [𝒟 : category.{u v} D]
include 𝒟

def sigma.post (f : β → C) [has_coproduct f] (G : C ⥤ D) [has_coproduct (G.obj ∘ f)] :
  (limits.sigma (G.obj ∘ f)) ⟶ G.obj (limits.sigma f) :=
@is_colimit.desc _ _ _ _ _
  (sigma.cofan (G.obj ∘ f))
  (sigma.universal_property _)
  { X := _,
    ι := { app := λ b, G.map (sigma.ι f b) } }

@[simp] lemma sigma.ι_post
  (f : β → C) [has_coproduct f] (G : C ⥤ D) [has_coproduct (G.obj ∘ f)] (b : β) :
  sigma.ι _ b ≫ sigma.post f G = G.map (sigma.ι f b) :=
by erw is_colimit.fac; refl
end

@[extensionality] lemma sigma.hom_ext
  (f : β → C) [has_coproduct f]
  {X : C} (g h : limits.sigma f ⟶ X) (w : ∀ b, sigma.ι f b ≫ g = sigma.ι f b ≫ h) :
  g = h :=
colimit.hom_ext w

def sigma.hom_iso {f : β → C} [has_coproduct f] {P : C} : (limits.sigma f ⟶ P) ≅ Π b, f b ⟶ P :=
{ hom := λ g b, sigma.ι f b ≫ g,
  inv := λ g, sigma.desc g }

@[simp] lemma sigma.map_desc
  [has_coproducts_of_shape.{u v} β C]
  {f : β → C} {g : β → C} {P : C} (k : Π b, f b ⟶ g b) (p : Π b, g b ⟶ P) :
  sigma.map k ≫ sigma.desc p = sigma.desc (λ b, k b ≫ p b) :=
colimit.map_desc (nat_trans.of_function k) (cocone.of_function p)

@[simp] lemma sigma.map_map
  {f1 : β → C} [has_coproduct.{u v} f1]
  {f2 : β → C} [has_coproduct.{u v} f2]
  {f3 : β → C} [has_coproduct.{u v} f3]
  (k1 : Π b, f1 b ⟶ f2 b) (k2 : Π b, f2 b ⟶ f3 b) :
  sigma.map k1 ≫ sigma.map k2 = sigma.map (λ b, k1 b ≫ k2 b) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  simp,
end.

@[simp] lemma sigma.pre_desc
  {α : Type v} {f : β → C} [has_coproduct.{u v} f]
  {P : C} (p : Π b, f b ⟶ P)
  (h : α → β) [has_coproduct.{u v} (f ∘ h)] :
  sigma.pre _ h ≫ sigma.desc p = sigma.desc (λ a, p (h a)) :=
begin
  /- `obviously` says -/
  ext1,
  simp,
  rw ←category.assoc,
  simp,
end

def sigma.pre_map
  {α : Type v} {f g : β → C} [has_coproduct.{u v} f] [has_coproduct.{u v} g]
  (k : Π b : β, f b ⟶ g b) (e : α → β)
  [has_coproduct.{u v} (f ∘ e)] [has_coproduct.{u v} (g ∘ e)] :
  sigma.pre f e ≫ sigma.map k = sigma.map (λ a, k (e a)) ≫ sigma.pre g e :=
begin
  /- `obviously` says -/
  ext1,
  rw ←category.assoc,
  erw sigma.ι_desc,
  rw ←category.assoc,
  simp,
end.

@[simp] lemma sigma.pre_pre
  {γ δ : Type v}
  (f : β → C) [has_coproduct.{u v} f]
  (g : γ → β) [has_coproduct.{u v} (f ∘ g)]
  (h : δ → γ) [has_coproduct.{u v} ((f ∘ g) ∘ h)]:
  sigma.pre (f ∘ g) h ≫ sigma.pre f g = sigma.pre f (g ∘ h) :=
begin
  ext1,
  rw ←category.assoc,
  simp,
  rw sigma.ι_pre f,
end.

section
variables {D : Type u} [category.{u v} D]

@[simp] def sigma.post_desc
  {f : β → C} [has_coproduct.{u v} f]
  {P : C} (k : Π b : β, f b ⟶ P)
  (G : C ⥤ D) [has_coproduct.{u v} (G.obj ∘ f)] :
  sigma.post f G ≫ G.map (sigma.desc k) = sigma.desc (λ b, G.map (k b)) :=
begin
  /- `obvously` says -/
  ext1, simp,
  rw ←category.assoc,
  rw sigma.ι_post,
  rw ←functor.map_comp,
  rw sigma.ι_desc,
end.

def sigma.map_post
  {f g : β → C} [has_coproduct.{u v} f] [has_coproduct.{u v} g]
  (k : Π b : β, f b ⟶ g b)
  (H : C ⥤ D) [has_coproduct.{u v} (H.obj ∘ f)] [has_coproduct.{u v} (H.obj ∘ g)] :
  @sigma.map _ _ _ (H.obj ∘ f) _ (H.obj ∘ g) _ (λ b, H.map (k b)) ≫ sigma.post g H =
    sigma.post f H ≫ H.map (sigma.map k) :=
begin
  /- `obviously` says -/
  ext1,
  dsimp at *,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  rw ←category.assoc,
  simp,
  rw ←functor.map_comp,
  rw ←functor.map_comp,
  rw sigma.ι_map,
end.

def sigma.pre_post
  {α} (f : β → C) [has_coproduct.{u v} f]
  (g : α → β) [has_coproduct.{u v} (f ∘ g)]
  (G : C ⥤ D) [has_coproduct.{u v} (G.obj ∘ f)] [has_coproduct.{u v} (G.obj ∘ f ∘ g)] :
  sigma.pre (G.obj ∘ f) g ≫ sigma.post f G = sigma.post (f ∘ g) G ≫ G.map (sigma.pre f g) :=
begin
  /- `obviously` says -/
  ext1,
  dsimp at *,
  rw [←category.assoc, sigma.ι_pre, sigma.ι_post, ←category.assoc,
      sigma.ι_post, ←functor.map_comp, sigma.ι_pre]
end

-- TODO? As needed.
/-
@[simp] def sigma.post_post
  {E : Type u} [category.{u v} E]
  (f : β → C) [has_coproduct.{u v} f]
  (G : C ⥤ D) [has_coproduct.{u v} (G.obj ∘ f)]
  (H : D ⥤ E) [has_coproduct.{u v} (H.obj ∘ G.obj ∘ f)]:
  sigma.post (G.obj ∘ f) H ≫ H.map (sigma.post f G) = sigma.post f (G ⋙ H) := ...
-/

end
end
end coproducts

end category_theory.limits

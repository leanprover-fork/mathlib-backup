import category_theory.transfinite.composition

section
universe u
def change (α : Type u) {β : Type u} (e : β = α) : α → β := e.mpr
end

section
open category_theory
universes u v u' v'
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

@[simp] def change_hom (a b : C) {a' b' : C} (ea : a' = a) (eb : b' = b) (f : a ⟶ b) : a' ⟶ b' :=
eq_to_hom ea ≫ f ≫ eq_to_hom eb.symm

lemma heq_of_eq_hom {a b a' b' : C} {f : a ⟶ b} {f' : a' ⟶ b'} (ea : a' = a) (eb : b' = b) :
  change_hom a b ea eb f = f' → f == f' :=
by cases ea; cases eb; simp

@[simp] lemma eq_to_hom_trans_assoc {X Y Z W : C} (p : X = Y) (q : Y = Z) (f : Z ⟶ W) :
  eq_to_hom p ≫ eq_to_hom q ≫ f = eq_to_hom (p.trans q) ≫ f :=
by cases p; cases q; simp

lemma I_change_hom (I : category_theory.transfinite.morphism_class C)
  {a b a' b' : C} {ea : a' = a} {eb : b' = b}
  (f : a ⟶ b) : I (eq_to_hom ea ≫ f ≫ eq_to_hom eb.symm) ↔ I f :=
by cases ea; cases eb; simp

lemma I_change_hom' (I : category_theory.transfinite.morphism_class C)
  {a b a' : C} {ea : a' = a} (f : a ⟶ b) : I (eq_to_hom ea ≫ f) ↔ I f :=
by cases ea; simp

lemma is_colimit_of_iso {J : Type v} [small_category J] {F G : J ⥤ C} (α : F ≅ G)
  {t : limits.cocone G} (ht : limits.is_colimit t) :
  limits.is_colimit (t.precompose α.hom) :=
sorry                           -- TODO

@[simp] lemma full_subcategory_inclusion_obj (Z : C → Prop) (X) :
  (full_subcategory_inclusion Z).obj X = X.val :=
rfl

@[simp] lemma full_subcategory_inclusion_map (Z : C → Prop) {X Y} (f : X ⟶ Y) :
  (full_subcategory_inclusion Z).map f = f :=
rfl

variables {D : Type u'} [𝒟 : category.{u' v'} D]
include 𝒟

lemma category_theory.functor.ext {F G : C ⥤ D} (h_obj : ∀ X, F.obj X = G.obj X)
  (h_map : ∀ X Y f, F.map f = eq_to_hom (h_obj X) ≫ G.map f ≫ eq_to_hom (h_obj Y).symm) :
  F = G :=
begin
  cases F with F_obj _ _ _, cases G with G_obj _ _ _,
  have : F_obj = G_obj, by ext X; apply h_obj,
  subst this,
  congr,
  ext X Y f,
  simpa using h_map X Y f
end

lemma category_theory.functor.eq_obj {F G : C ⥤ D} (h : F = G) (X) : F.obj X = G.obj X :=
by subst h

lemma category_theory.functor.eq_hom {F G : C ⥤ D} (h : F = G) {X Y} (f : X ⟶ Y) :
  F.map f = eq_to_hom (category_theory.functor.eq_obj h X) ≫ G.map f ≫ eq_to_hom (category_theory.functor.eq_obj h Y).symm :=
by subst h; simp

@[simp] lemma category_theory.nat_trans.eq_to_hom_app {F G : C ⥤ D} (h : F = G) (X : C) :
  (eq_to_hom h : F ⟹ G).app X = eq_to_hom (category_theory.functor.eq_obj h X) :=
by subst h; refl

-- We actually don't need this?
universes u'' v'' u''' v'''
lemma category_theory.functor.assoc_eq {E : Type u''} [category.{u'' v''} E]
  {F : Type u'''} [category.{u''' v'''} F]
  (G : C ⥤ D) (H : D ⥤ E) (I : E ⥤ F) : (G ⋙ H) ⋙ I = G ⋙ H ⋙ I :=
rfl

end

namespace category_theory.transfinite

universes u v

section
variables {γ : Type v} [partial_order γ]

def below_top (j : γ) : Type v := {i // i ≤ j}

instance below_top.order_top (j : γ) : lattice.order_top (below_top j) :=
{ top := ⟨j, le_refl j⟩,
  le_top := λ i, i.property,
  .. (show partial_order (below_top j), by dunfold below_top; apply_instance) }

instance [is_well_order γ (<)] (j : γ) : is_well_order (below_top j) (<) :=
show is_well_order _ (subrel (<) {i | i ≤ j}), by apply_instance

def below_initial_seg {j j' : γ} (h : j ≤ j') : initial_seg ((<) : below_top j → below_top j → Prop) ((<) : below_top j' → below_top j' → Prop) :=
{ to_fun := λ i, ⟨i.val, le_trans i.property h⟩,
  ord := by intros; refl,
  inj := by tidy,
  init := λ ⟨i, hi⟩ ⟨i', hi'⟩ hii', ⟨⟨i', le_trans (le_of_lt hii') hi⟩, rfl⟩ }

def open_to_closed (j : γ) : initial_seg ((<) : {i // i < j} → {i // i < j} → Prop) ((<) : below_top j → below_top j → Prop) :=
{ to_fun := λ i, ⟨i.val, le_of_lt i.property⟩,
  ord := by tidy,
  inj := by tidy,
  init := λ ⟨i, hi⟩ ⟨i', hi'⟩ hii', ⟨⟨i', lt_trans hii' hi⟩, rfl⟩ }

/-
def embed {j j' : γ} (h : j ≤ j') : below_top j ⥤ below_top j' :=
{ obj := λ i, ⟨i.val, le_trans i.property h⟩,
  map := λ _ _ f, f } -/


end

section
variables {β γ : Type v} [partial_order β] [partial_order γ]
def iseg (β γ) [partial_order β] [partial_order γ] := initial_seg ((<) : β → β → Prop) ((<) : γ → γ → Prop)

variables (f : iseg β γ)

def inclusion_functor : β ⥤ γ :=
{ obj := f.to_fun,
  map := λ b₁ b₂ h, ⟨⟨sorry⟩⟩ }
end

section

variables {γ : Type v} [lattice.order_top γ]

def to_below_top : γ ⥤ below_top (⊤ : γ) :=
{ obj := λ j, ⟨j, lattice.le_top⟩,
  map := λ _ _ f, f }

variables [is_well_order γ (<)]

lemma is_bot_iff (j : γ) (i : below_top j) : (i = bot) ↔ (i.1 = bot) :=
sorry

lemma is_succ_iff (j : γ) (i i' : below_top j) : is_succ i i' ↔ is_succ i.1 i'.1 :=
sorry

lemma is_limit_iff (j : γ) (i : below_top j) : is_limit i ↔ is_limit i.1 :=
sorry

def embed {j j' : γ} (h : j ≤ j') : below_top j ⥤ below_top j' :=
inclusion_functor (below_initial_seg h)

@[simp] lemma embed_obj_val {j j' : γ} (h : j ≤ j') (p : below_top j) :
  ((embed h).obj p).val = p.val :=
rfl

end

section restrict
local infix ` ≼i `:50 := initial_seg

open category_theory

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

variables
  {β : Type v} [lattice.order_top β] [is_well_order β (<)]
  {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]
  (f : initial_seg ((<) : β → β → Prop) ((<) : γ → γ → Prop))

variables (F : γ ⥤ C)

-- TODO: Somehow this got a bit too complicated, we have inclusion_functor and also embed?
-- I guess it's okay, just put the related definitions together

def restriction : β ⥤ C := inclusion_functor f ⋙ F

lemma smooth_at_iff_restriction_smooth_at (i : β) :
  smooth_at F (f i) ↔ smooth_at (restriction f F) i :=
sorry

end restrict


end category_theory.transfinite

/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Extends filter limits to partial functions and relations. Characterizes limits at a point,
possibly restricted to a set.
-/
import data.pfun data.set.basic
import order.filter
import analysis.topology.topological_space
import analysis.metric_space
import tactic.squeeze

variables {α : Type*} {β : Type*} {γ : Type*}

/-
move to data.subtype.
-/

namespace subtype

theorem val_image_subset (s : set α) (t : set (subtype s)) : t.image val ⊆ s :=
λ x ⟨y, yt, yvaleq⟩, by rw ←yvaleq; exact y.property

theorem val_image_univ (s : set α) : @val _ s '' set.univ = s :=
set.eq_of_subset_of_subset (val_image_subset _ _) (λ x xs, ⟨⟨x, xs⟩, ⟨set.mem_univ _, rfl⟩⟩)

end subtype

/-
Operations on set-valued functions, aka partial multifunctions, aka relations.
-/

def rel (α : Type*) (β : Type*):= α → β → Prop

namespace rel

variables {δ : Type*} (r : rel α β)

def inv : rel β α := flip r

lemma inv_def (x : α) (y : β) : r.inv y x ↔ r x y := iff.rfl

lemma inv_inv : inv (inv r) = r := by { ext x y, reflexivity }

def dom := {x | ∃ y, r x y}

def codom := {y | ∃ x, r x y}

lemma codom_inv : r.inv.codom = r.dom := by { ext x y, reflexivity }

lemma dom_inv : r.inv.dom = r.codom := by { ext x y, reflexivity}

def comp (r : rel α β) (s : rel β γ) : rel α γ :=
λ x z, ∃ y, r x y ∧ s y z 

infixr  ` ∘ `      :=rel.comp

lemma comp_assoc (r : rel α β) (s : rel β γ) (t : rel γ δ) :
  (r ∘ s) ∘ t = r ∘ s ∘ t :=
begin
  unfold comp, ext x w, split,
  { rintros ⟨z, ⟨y, rxy, syz⟩, tzw⟩, exact ⟨y, rxy, z, syz, tzw⟩ },
  rintros ⟨y, rxy, z, syz, tzw⟩, exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩
end

@[simp]
lemma comp_right_id (r : rel α β) : r ∘ @eq β = r :=
by { unfold comp, ext y, simp }

@[simp]
lemma comp_left_id (r : rel α β) : @eq α ∘ r = r :=
by { unfold comp, ext x, simp }

lemma inv_id : inv (@eq α) = @eq α :=
by { ext x y, split; apply eq.symm }

lemma inv_comp (r : rel α β) (s : rel β γ) : inv (r ∘ s) = inv s ∘ inv r :=
by { ext x z, simp [comp, inv, flip, and.comm] }

def image (s : set α) : set β := {y | ∃ x ∈ s, r x y}

lemma mem_image (y : β) (s : set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
iff.refl _

lemma image_mono {s t : set α} (h : s ⊆ t) : r.image s ⊆ r.image t :=
assume y ⟨x, xs, rxy⟩, ⟨x, h xs, rxy⟩

lemma image_inter (s t : set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
assume y ⟨x, ⟨xs, xt⟩, rxy⟩, ⟨⟨x, xs, rxy⟩, ⟨x, xt, rxy⟩⟩

lemma image_union (s t : set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
set.eq_of_subset_of_subset
  (λ y ⟨x, xst, rxy⟩, 
    begin 
      cases xst with xs xt, 
      { left, exact ⟨x, xs, rxy⟩ },
      right, exact ⟨x, xt, rxy⟩ 
    end)
  (λ y ymem, 
    begin 
      rcases ymem with ⟨x, xs, rxy⟩ | ⟨x, xt, rxy⟩; existsi x,
      { split, { left, exact xs }, exact rxy},
      split, { right, exact xt }, exact rxy 
    end)

@[simp]
lemma image_id (s : set α) : image (@eq α) s = s :=
by { ext x, simp [mem_image] }

lemma image_comp (s : rel β γ) (t : set α) : image (r ∘ s) t = image s (image r t) :=
begin 
  ext z, simp only [mem_image, comp], split,
  { rintros ⟨x, xt, y, rxy, syz⟩, exact ⟨y, ⟨x, xt, rxy⟩, syz⟩ },
  rintros ⟨y, ⟨x, xt, rxy⟩, syz⟩, exact ⟨x, xt, y, rxy, syz⟩
end

lemma image_univ : r.image set.univ = r.codom := by { ext y, simp [mem_image, codom] }

def preimage (s : set β) : set α := image (inv r) s

lemma mem_preimage (x : α) (s : set β) : x ∈ preimage r s ↔ ∃ y ∈ s, r x y :=
iff.refl _

lemma preimage_def (s : set β) : preimage r s = {x | ∃ y ∈ s, r x y} :=
set.ext $ λ x, mem_preimage _ _ _

lemma preimage_mono {s t : set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
image_mono _ h

lemma preimage_inter (s t : set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
image_inter _ s t

lemma preimage_union (s t : set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
image_union _ s t

lemma preimage_id (s : set α) : preimage (@eq α) s = s :=
by simp only [preimage, inv_id, image_id]

lemma preimage_comp (s : rel β γ) (t : set γ) : 
  preimage (r ∘ s) t = preimage r (preimage s t) :=
by simp only [preimage, inv_comp, image_comp]

lemma preimage_univ : r.preimage set.univ = r.dom :=
by { rw [preimage, image_univ, codom_inv] }

def core (s : set β) := {x | ∀ y, r x y → y ∈ s}

lemma mem_core (x : α) (s : set β) : x ∈ core r s ↔ ∀ y, r x y → y ∈ s :=
iff.refl _

lemma core_mono {s t : set β} (h : s ⊆ t) : r.core s ⊆ r.core t :=
assume x h' y rxy, h (h' y rxy)

lemma core_inter (s t : set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
set.ext (by simp [mem_core, imp_and_distrib, forall_and_distrib])

lemma core_union (s t : set β) : r.core (s ∪ t) ⊇ r.core s ∪ r.core t :=
λ x, 
  begin 
    simp [mem_core], intro h, cases h with hs ht; intros y rxy,
    { left, exact hs y rxy },
    right, exact ht y rxy 
  end

lemma core_univ : r.core set.univ = set.univ := set.ext (by simp [mem_core])

lemma core_id (s : set α): core (@eq α) s = s :=
by simp [core]

lemma core_comp (r : rel α β) (s : rel β γ) (t : set γ) :
  core (r ∘ s) t = core r (core s t) :=
begin 
  ext x, simp [core, comp], split,
  { intros h y rxy z syz, exact h z y rxy syz },
  intros h z y rzy syz, exact h y rzy z syz
end

end rel

/-
Image, preimage, and function graph.
-/

namespace function

def graph (f : α → β) : rel α β := λ x y, f x = y

end function

namespace set

local attribute [instance] classical.prop_decidable

theorem inter_subset (a b c : set α) : a ∩ b ⊆ c ↔ a ⊆ -b ∪ c :=
begin
  split,
  { intros h x xa, by_cases h' : x ∈ b, simp [h ⟨xa, h'⟩], simp [h'] },
  intros h x, rintro ⟨xa, xb⟩, cases h xa, contradiction, assumption
end 

-- TODO: if image were defined with bounded quantification in corelib, the next two would 
-- be definitional

lemma image_eq (f : α → β) (s : set α) : f '' s = (function.graph f).image s :=
by simp [set.image, function.graph, rel.image]

lemma preimage_eq (f : α → β) (s : set β) : 
  f ⁻¹' s = (function.graph f).preimage s :=
by simp [set.preimage, function.graph, rel.preimage, rel.inv, flip, rel.image]

lemma preimage_eq_core (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph f).core s := 
 by simp [set.preimage, function.graph, rel.core]
 
end set

/-
Image, preimage, and core on partial functions.
-/

namespace roption

theorem mem_eq (a : α) (o : roption α) : (a ∈ o) = (∃ h, o.get h = a) :=
rfl

@[simp]
theorem mem_restrict (p : Prop) (o : roption α) (h : p → o.dom) (a : α) : 
  a ∈ restrict p o h ↔ p ∧ a ∈ o :=
begin
  cases o, dsimp [restrict, mem_eq], split,
  { rintro ⟨h₀, h₁⟩, exact ⟨h₀, ⟨_, h₁⟩⟩ },
  rintro ⟨h₀, h₁, h₂⟩, exact ⟨h₀, h₂⟩ 
end

end roption

namespace pfun

@[simp]
theorem mem_restrict {f : α →. β} {s : set α} (h : s ⊆ f.dom) (a : α) (b : β) :
  b ∈ restrict f h a ↔ a ∈ s ∧ b ∈ f a :=
by { simp [restrict], reflexivity }

def res (f : α → β) (s : set α) : α →. β :=
restrict (pfun.lift f) (set.subset_univ s)

theorem mem_res (f : α → β) (s : set α) (a : α) (b : β) :
  b ∈ res f s a ↔ (a ∈ s ∧ f a = b) :=
by { simp [res], split; {intro h, simp [h]} }

theorem mem_dom (f : α →. β) (x : α) : x ∈ dom f ↔ ∃ y, y ∈ f x :=
by simp [dom, set.mem_def, roption.dom_iff_mem]

theorem dom_eq (f : α →. β) : dom f = { x | ∃ y, y ∈ f x } :=
set.ext (mem_dom f)

theorem res_univ (f : α → β) : pfun.res f set.univ = f :=
rfl

-- TODO: change pfun.graph to this
def graph' (f : α →. β) : rel α β := λ x y, y ∈ f x 

end pfun

namespace pfun

variables (f : α →. β) 

def image (s : set α) : set β := rel.image f.graph' s

lemma image_def (s : set α) : image f s = {y | ∃ x ∈ s, y ∈ f x} := rfl

lemma mem_image (y : β) (s : set α) : y ∈ image f s ↔ ∃ x ∈ s, y ∈ f x :=
iff.refl _

lemma image_mono {s t : set α} (h : s ⊆ t) : f.image s ⊆ f.image t :=
rel.image_mono _ h

lemma image_inter (s t : set α) : f.image (s ∩ t) ⊆ f.image s ∩ f.image t :=
rel.image_inter _ s t

lemma image_union (s t : set α) : f.image (s ∪ t) = f.image s ∪ f.image t :=
rel.image_union _ s t

def preimage (s : set β) : set α := rel.preimage (λ x y, y ∈ f x) s

lemma preimage_def (s : set β) : preimage f s = {x | ∃ y ∈ s, y ∈ f x} := rfl

def mem_preimage (s : set β) (x : α) : x ∈ preimage f s ↔ ∃ y ∈ s, y ∈ f x :=
iff.refl _

lemma preimage_mono {s t : set β} (h : s ⊆ t) : f.preimage s ⊆ f.preimage t :=
rel.preimage_mono _ h

lemma preimage_inter (s t : set β) : f.preimage (s ∩ t) ⊆ f.preimage s ∩ f.preimage t :=
rel.preimage_inter _ s t

lemma preimage_union (s t : set β) : f.preimage (s ∪ t) = f.preimage s ∪ f.preimage t :=
rel.preimage_union _ s t

lemma preimage_univ : f.preimage set.univ = f.dom :=
by ext; simp [mem_preimage, mem_dom]

def core (s : set β) : set α := rel.core f.graph' s 

lemma core_def (s : set β) : core f s = {x | ∀ y, y ∈ f x → y ∈ s} := rfl

lemma mem_core (x : α) (s : set β) : x ∈ core f s ↔ (∀ y, y ∈ f x → y ∈ s) := 
iff.rfl

lemma core_mono {s t : set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
rel.core_mono _ h

lemma core_inter (f : α →. β) (s t : set β) : f.core (s ∩ t) = f.core s ∩ f.core t :=
rel.core_inter _ s t

lemma mem_core_res (f : α → β) (s : set α) (t : set β) (x : α) : 
  x ∈ core (res f s) t ↔ (x ∈ s → f x ∈ t) :=
begin
  simp [mem_core, mem_res], split,
  { intros h h', apply h _ h', reflexivity },
  intros h y xs fxeq, rw ←fxeq, exact h xs
end

section
local attribute  [instance] classical.prop_decidable

lemma core_res (f : α → β) (s : set α) (t : set β) : core (res f s) t = -s ∪ f ⁻¹' t :=
by { ext, rw mem_core_res, by_cases h : x ∈ s; simp [h] }

end

end pfun

/-
General filter facts.
-/

namespace filter

theorem le_map_comap_of_surjective' {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l.sets) 
    (hf : ∀ y ∈ u, ∃ x, f x = y) :
  l ≤ map f (comap f l) :=
assume s ⟨t, tl, ht⟩,
have t ∩ u ⊆ s, from
  assume x ⟨xt, xu⟩,
  exists.elim (hf x xu) $ λ a faeq,
  by { rw ←faeq, apply ht, change f a ∈ t, rw faeq, exact xt },
mem_sets_of_superset (inter_mem_sets tl ul) this

theorem map_comap_of_surjective' {f : α → β} {l : filter β} {u : set β} (ul : u ∈ l.sets) 
    (hf : ∀ y ∈ u, ∃ x, f x = y)  :
  map f (comap f l) = l :=
le_antisymm map_comap_le (le_map_comap_of_surjective' ul hf)

theorem le_map_comap_of_surjective {f : α → β} (hf : function.surjective f) (l : filter β) :
  l ≤ map f (comap f l) :=
le_map_comap_of_surjective' univ_mem_sets (λ y _, hf y)

theorem map_comap_of_surjective {f : α → β} (hf : function.surjective f) (l : filter β) :
  map f (comap f l) = l :=
le_antisymm map_comap_le (le_map_comap_of_surjective hf l)

end filter

/-
Generalize tendsto to relations.
-/

namespace filter 

def rmap (r : rel α β) (f : filter α) : filter β :=
{ sets             := r.core ⁻¹' f.sets,
  univ_sets        := by { simp [rel.core], apply univ_mem_sets },
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ rel.core_mono _ st,
  inter_sets       := by { simp [set.preimage, rel.core_inter], exact λ s t, inter_mem_sets } }

theorem rmap_sets (r : rel α β) (f : filter α) : (rmap r f).sets = r.core ⁻¹' f.sets := rfl

@[simp]
theorem mem_rmap (r : rel α β) (l : filter α) (s : set β) : s ∈ (l.rmap r).sets ↔ r.core s ∈ l.sets :=
iff.refl _

@[simp]
theorem rmap_rmap (r : rel α β) (s : rel β γ) (l : filter α) :
  rmap s (rmap r l) = rmap (r ∘ s) l :=
filter_eq $ 
by simp [rmap_sets, set.preimage, rel.core_comp]

@[simp]
lemma rmap_compose (r : rel α β) (s : rel β γ) : rmap s ∘ rmap r = rmap (r ∘ s) :=
funext $ rmap_rmap _ _

def rtendsto (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁.rmap r ≤ l₂

theorem rtendsto_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ ∀ s ∈ l₂.sets, r.core s ∈ l₁.sets :=
iff.refl _

def rcomap (r : rel α β) (f : filter β) : filter α :=
{ sets             := rel.image (λ s t, r.core s ⊆ t) f.sets,
  univ_sets        := ⟨set.univ, univ_mem_sets, set.subset_univ _⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', set.subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩, 
                        ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, 
                          set.subset.trans (by rw rel.core_inter)
                                           (set.inter_subset_inter ha₂ hb₂)⟩ }

theorem rcomap_sets (r : rel α β) (f : filter β) : 
  (rcomap r f).sets = rel.image (λ s t, r.core s ⊆ t) f.sets := rfl

@[simp]
theorem rcomap_rcomap (r : rel α β) (s : rel β γ) (l : filter γ) :
  rcomap r (rcomap s l) = rcomap (r ∘ s) l :=
filter_eq $ 
begin
  ext t, simp [rcomap_sets, rel.image, rel.core_comp], split,
  { rintros ⟨u, ⟨v, vsets, hv⟩, h⟩,
    exact ⟨v, vsets, set.subset.trans (rel.core_mono _ hv) h⟩ },
  rintros ⟨t, tsets, ht⟩,
  exact ⟨rel.core s t, ⟨t, tsets, set.subset.refl _⟩, ht⟩ 
end

@[simp]
lemma rcomap_compose (r : rel α β) (s : rel β γ) : rcomap r ∘ rcomap s = rcomap (r ∘ s) :=
funext $ rcomap_rcomap _ _

theorem rtendsto_iff_le_comap (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ l₁ ≤ l₂.rcomap r :=
begin 
  rw rtendsto_def, simp [filter.le_def, rcomap, rel.mem_image], split,
  intros h s t tl₂ h',
  { exact mem_sets_of_superset (h t tl₂) h' },
  intros h t tl₂,
  apply h _ t tl₂ (set.subset.refl _), 
end 

/-
Interestingly, there does not seem to be a way to express this relation using a forward map.
Given a filter `f` on `α`, we want a filter `f'` on `β` such that `r.preimage s ∈ f.sets` if 
and only if `s ∈ f'`. But the intersection of two sets satsifying the lhs may be empty.  
-/

def rcomap' (r : rel α β) (f : filter β) : filter α :=
{ sets             := rel.image (λ s t, r.preimage s ⊆ t) f.sets,
  univ_sets        := ⟨set.univ, univ_mem_sets, set.subset_univ _⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', set.subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩, 
                        ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, 
                          set.subset.trans (@rel.preimage_inter _ _ r _ _) 
                                           (set.inter_subset_inter ha₂ hb₂)⟩ }

@[simp]
def mem_rcomap' (r : rel α β) (l : filter β) (s : set α) : 
  s ∈ (l.rcomap' r).sets ↔ ∃ t ∈ l.sets, rel.preimage r t ⊆ s :=
iff.refl _

theorem rcomap'_sets (r : rel α β) (f : filter β) : 
  (rcomap' r f).sets = rel.image (λ s t, r.preimage s ⊆ t) f.sets := rfl

@[simp]
theorem rcomap'_rcomap' (r : rel α β) (s : rel β γ) (l : filter γ) :
  rcomap' r (rcomap' s l) = rcomap' (r ∘ s) l :=
filter_eq $ 
begin
  ext t, simp [rcomap'_sets, rel.image, rel.preimage_comp], split,
  { rintros ⟨u, ⟨v, vsets, hv⟩, h⟩,
    exact ⟨v, vsets, set.subset.trans (rel.preimage_mono _ hv) h⟩ },
  rintros ⟨t, tsets, ht⟩,
  exact ⟨rel.preimage s t, ⟨t, tsets, set.subset.refl _⟩, ht⟩ 
end

@[simp]
lemma rcomap'_compose (r : rel α β) (s : rel β γ) : rcomap' r ∘ rcomap' s = rcomap' (r ∘ s) :=
funext $ rcomap'_rcomap' _ _

def rtendsto' (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁ ≤ l₂.rcomap' r

theorem rtendsto'_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto' r l₁ l₂ ↔ ∀ s ∈ l₂.sets, r.preimage s ∈ l₁.sets :=
begin
  unfold rtendsto', unfold rcomap', simp [le_def, rel.mem_image], split,
  { intros h s hs, apply (h _ _ hs (set.subset.refl _)) },
  intros h s t ht h', apply mem_sets_of_superset (h t ht) h'  
end

end filter

/-
Extend filters to partial functions.
-/

namespace filter

def pmap (f : α →. β) (l : filter α) : filter β :=
filter.rmap f.graph' l

@[simp]
def mem_pmap (f : α →. β) (l : filter α) (s : set β) : s ∈ (l.pmap f).sets ↔ f.core s ∈ l.sets :=
iff.refl _

def ptendsto (f : α →. β) (l₁ : filter α) (l₂ : filter β) := l₁.pmap f ≤ l₂

theorem ptendsto_def (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
  ptendsto f l₁ l₂ ↔ ∀ s ∈ l₂.sets, f.core s ∈ l₁.sets :=
iff.refl _

theorem pmap_res (l : filter α) (s : set α) (f : α → β) :
  pmap (pfun.res f s) l = map f (l ⊓ principal s) :=
filter_eq $ 
begin
  apply set.ext, intro t, simp [pfun.core_res], split,
  { intro h, constructor, split, { exact h },
    constructor, split, { reflexivity }, 
    simp [set.inter_distrib_right], apply set.inter_subset_left },
  rintro ⟨t₁, h₁, t₂, h₂, h₃⟩, apply mem_sets_of_superset h₁, rw ← set.inter_subset,
  exact set.subset.trans (set.inter_subset_inter_right _ h₂) h₃ 
end

theorem tendsto_iff_ptendsto (l₁ : filter α) (l₂ : filter β) (s : set α) (f : α → β) :
  tendsto f (l₁ ⊓ principal s) l₂ ↔ ptendsto (pfun.res f s) l₁ l₂ :=
by simp only [tendsto, ptendsto, pmap_res]

theorem tendsto_iff_ptendsto' (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ ptendsto (pfun.res f set.univ) l₁ l₂ :=
by { rw ← tendsto_iff_ptendsto, simp [principal_univ] }

/- relate relational version to function and partial function versions -/

theorem ptendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α →. β) :
  ptendsto f l₁ l₂ ↔ rtendsto f.graph' l₁ l₂ :=
iff.refl _

theorem tendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto (function.graph f) l₁ l₂ :=
by { simp [tendsto_def, function.graph, rtendsto_def, rel.core, set.preimage] }

theorem tendsto_iff_rtendsto' (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto' (function.graph f) l₁ l₂ :=
by { simp [tendsto_def, function.graph, rtendsto'_def, rel.preimage_def, set.preimage] }

end filter

open filter

section

variable [topological_space α]

def at_within (a : α) (s : set α) : filter α := nhds a ⊓ principal (s \ singleton a)

def at_pt (a : α) : filter α := at_within a set.univ

theorem mem_at_within (t : set α) (a : α) (s : set α) :
  t ∈ (at_within a s).sets ↔ ∃ u, is_open u ∧ a ∈ u ∧ u ∩ (s \ {a}) ⊆ t  :=
begin
  simp [at_within, mem_inf_sets, nhds_sets, principal], split,
  { rintros ⟨t₁, ⟨⟨u, usubt₁, openu, au⟩, ⟨t₂, sasubt₂, t₁t₂subt⟩⟩ ⟩,
    exact ⟨u, openu, au, 
      set.subset.trans (set.inter_subset_inter usubt₁ sasubt₂) t₁t₂subt⟩ },
  rintros ⟨u, openu, au, hu⟩, 
  exact ⟨u, ⟨⟨u, set.subset.refl u, openu, au⟩, ⟨_, set.subset.refl _, hu⟩⟩⟩
end

theorem mem_at_pt (t : set α) (a : α) :
  t ∈ (at_pt a).sets ↔ ∃ u, is_open u ∧ a ∈ u ∧ u \ {a} ⊆ t :=
by simp [at_pt, mem_at_within, (set.inter_diff_assoc _ _ _).symm]

theorem rtendsto_at_within (r : rel α β) (a : α) (s : set α) (l : filter β) :
  rtendsto r (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ u, is_open u ∧ a ∈ u ∧ ∀ x ∈ u ∩ s, x ≠ a → ∀ y, r x y → y ∈ t :=
by simp [rtendsto_def, mem_at_within, set.subset_def, rel.mem_core]

theorem rtendsto'_at_within (r : rel α β) (a : α) (s : set α) (l : filter β) :
  rtendsto' r (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ u, is_open u ∧ a ∈ u ∧ ∀ x ∈ u ∩ s, x ≠ a → ∃ y ∈ t, r x y :=
by simp [rtendsto'_def, mem_at_within, set.subset_def, rel.mem_preimage]

theorem ptendsto_at_within (f : α →. β) (a : α) (s : set α) (l : filter β) :
  ptendsto f (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ u, is_open u ∧ a ∈ u ∧ ∀ x ∈ u ∩ s, x ≠ a → ∀ y ∈ f x, y ∈ t :=
by rw [ptendsto_iff_rtendsto, rtendsto_at_within, pfun.graph']

theorem tendsto_at_within (f : α → β) (a : α) (s : set α) (l : filter β) :
  tendsto f (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ u, is_open u ∧ a ∈ u ∧ ∀ x ∈ u ∩ s, x ≠ a → f x ∈ t :=
by rw [tendsto_iff_ptendsto', ptendsto_at_within, pfun.res_univ]; 
    simp only [pfun.coe_val, roption.mem_some_iff, forall_eq]

theorem rtendsto_at_pt (r : rel α β) (a : α) (l : filter β) :
  rtendsto r (at_pt a) l ↔ 
    ∀ t ∈ l.sets, ∃ u : set α, is_open u ∧ a ∈ u ∧ ∀ x ∈ u, x ≠ a → ∀ y, r x y → y ∈ t :=
by rw [at_pt, rtendsto_at_within]; simp only [set.inter_univ]

theorem rtendsto'_at_pt (r : rel α β) (a : α) (l : filter β) :
  rtendsto' r (at_pt a) l ↔  
    ∀ t ∈ l.sets, ∃ u : set α, is_open u ∧ a ∈ u ∧ ∀ x ∈ u, x ≠ a → ∃ y ∈ t, r x y :=
by rw [at_pt, rtendsto'_at_within]; simp only [set.inter_univ]

theorem ptendsto_at_pt (f : α →. β) (a : α) (l : filter β) :
  ptendsto f (at_pt a) l ↔ 
    ∀ t ∈ l.sets, ∃ u : set α, is_open u ∧ a ∈ u ∧ ∀ x ∈ u, x ≠ a → ∀ y ∈ f x, y ∈ t :=
by rw [at_pt, ptendsto_at_within]; simp only [set.inter_univ]

theorem tendsto_at_pt (f : α → β) (a : α) (l : filter β) :
  tendsto f (at_pt a) l ↔ 
    ∀ t ∈ l.sets, ∃ u : set α, is_open u ∧ a ∈ u ∧ ∀ x ∈ u, x ≠ a → f x ∈ t :=
by rw [at_pt, tendsto_at_within]; simp only [set.inter_univ]

/- nhds in the induced topology -/

theorem mem_nhds_induced [T : topological_space α] (f : β → α) (a : β) (s : set β) : 
  s ∈ (@nhds β (topological_space.induced f T) a).sets ↔ ∃ u ∈ (nhds (f a)).sets, f ⁻¹' u ⊆ s :=
begin
  simp only [nhds_sets, is_open_induced_iff, exists_prop, set.mem_set_of_eq], 
  split,
  { rintros ⟨u, usub, ⟨v, openv, ueq⟩, au⟩, 
    exact ⟨v, ⟨v, set.subset.refl v, openv, by rwa ueq at au⟩, by rw ←ueq; exact usub⟩ }, 
  rintros ⟨u, ⟨v, vsubu, openv, amem⟩, finvsub⟩,
  exact ⟨f ⁻¹' v, set.subset.trans (set.preimage_mono vsubu) finvsub, ⟨⟨v, openv, rfl⟩, amem⟩⟩
end

theorem nhds_induced [T : topological_space α] (f : β → α) (a : β) : 
  @nhds β (topological_space.induced f T) a = comap f (nhds (f a)) :=
filter_eq $ by ext s; rw mem_nhds_induced; rw mem_comap_sets

theorem map_nhds_induced_of_surjective [T : topological_space α] 
    {f : β → α} (hf : function.surjective f) (a : β) (s : set α) : 
  map f (@nhds β (topological_space.induced f T) a) = nhds (f a) :=
by rw [nhds_induced, map_comap_of_surjective hf]

/- nhds in the subspace topology -/

theorem mem_nhds_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) : 
  t ∈ (nhds a).sets ↔ ∃ u ∈ (nhds a.val).sets, (@subtype.val α s) ⁻¹' u ⊆ t :=
begin
 rw mem_nhds_induced
end

theorem nhds_subtype (s : set α) (a : {x // x ∈ s}) :
  nhds a = comap subtype.val (nhds a.val) :=
by rw nhds_induced

theorem principal_subtype_eq (s : set α) (t : set {x // x ∈ s}) :
  principal t = comap subtype.val (principal (subtype.val '' t)) :=
by rw comap_principal; rw set.preimage_image_eq; apply subtype.val_injective

theorem mem_at_within_subtype (s : set α) (a : {x // x ∈ s}) (t u : set {x // x ∈ s}) :
  t ∈ (at_within a u).sets ↔ 
    t ∈ (comap (@subtype.val _ s) (at_within (a.val) (subtype.val '' u))).sets :=
have h₀ : (@subtype.val _ s) '' -{a} = s ∩ -{a.val},
  begin 
    ext x, cases a with a as, simp, split,
    { rintros ⟨y, ys, yne, yeq⟩, rw ←yeq, exact ⟨ys, yne⟩ },
    rintros ⟨xs, xne⟩, exact ⟨x, xs, xne, rfl⟩ 
  end, 
have h₁ : subtype.val '' u ⊆ s, from subtype.val_image_subset _ _, 
have subtype.val '' (u \ {a}) = subtype.val '' u \ {a.val}, 
  begin
    rw [set.diff_eq, ←set.image_inter subtype.val_injective, h₀, ←set.inter_assoc],
    rw [set.inter_eq_self_of_subset_left h₁, set.diff_eq]
  end,
by rw [at_within, nhds_subtype, principal_subtype_eq, ←comap_inf, this, ←at_within]

theorem at_within_subtype (s : set α) (a : {x // x ∈ s}) (t : set {x // x ∈ s}) : 
  at_within a t = comap (@subtype.val _ s) (at_within (a.val) (subtype.val '' t)) :=
filter_eq $ by ext u; rw mem_at_within_subtype

theorem at_within_eq_map_subtype_val {s : set α} {a : α} (h : a ∈ s) :
  at_within a s = map subtype.val (at_pt ⟨a, h⟩) :=
have h₀ : s ∈ (at_within a s).sets,
  by { rw [mem_at_within], existsi set.univ, simp [set.diff_eq] },  
have h₁ : ∀ y ∈ s, ∃ x, @subtype.val _ s x = y,
  from λ y h, ⟨⟨y, h⟩, rfl⟩,   
begin
  rw [at_pt, at_within_subtype, subtype.val_image_univ],
  symmetry,
  exact map_comap_of_surjective' h₀ h₁
end

theorem tendsto_at_within_iff_subtype {s : set α} {a : α} (h : a ∈ s) (f : α → β) (l : filter β) :
  tendsto f (at_within a s) l ↔ tendsto (f ∘ (@subtype.val _ s)) (at_pt ⟨a, h⟩) l :=
by rw [tendsto, tendsto, at_within_eq_map_subtype_val h, ←(@filter.map_map _ _ _ _ subtype.val)]

end

namespace metric

variable [metric_space α]

theorem mem_at_within (t : set α) (a : α) (s : set α) :
  t ∈ (at_within a s).sets ↔ ∃ δ > 0, ∀ x ∈ s, dist x a < δ → x ≠ a → x ∈ t :=
begin
  rw mem_at_within, split,
  { rintros ⟨u, openu, au, hu⟩,
    have h := is_open_metric.mp openu a au,
    rcases h with ⟨δ, δgt0, ballsub⟩,
    existsi δ, existsi δgt0,
    rintros x xs distxa xnea,
    apply hu,
    split,
    { show x ∈ u, apply ballsub, apply distxa },
    split, { exact xs },
    dsimp, rw set.mem_singleton_iff,
    exact xnea },
  rintros ⟨δ, δgt0, h⟩,
  existsi ball a δ, split, { apply is_open_ball },
  split, { apply mem_ball_self δgt0 },
  rintros x ⟨distx, xs, xna⟩,
  apply h x xs distx,
  rwa set.mem_singleton_iff at xna
end

theorem mem_at_pt (t : set α) (a : α) :
  t ∈ (at_pt a).sets ↔ ∃ δ > 0, ∀ x, dist x a < δ → x ≠ a → x ∈ t :=
by rw [at_pt, mem_at_within]; simp

theorem rtendsto_at_within (r : rel α β) (a : α) (s : set α) (l : filter β) :
  rtendsto r (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ δ > 0, ∀ x ∈ s, dist x a < δ → x ≠ a → ∀ y, r x y → y ∈ t :=
by simp [rtendsto_def, mem_at_within, set.subset_def, rel.mem_core]

theorem rtendsto'_at_within (r : rel α β) (a : α) (s : set α) (l : filter β) :
  rtendsto' r (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ δ > 0, ∀ x ∈ s, dist x a < δ ∧ x ≠ a → ∃ y ∈ t, r x y :=
by simp [rtendsto'_def, mem_at_within, set.subset_def, rel.mem_preimage]

theorem ptendsto_at_within (f : α →. β) (a : α) (s : set α) (l : filter β) :
  ptendsto f (at_within a s) l ↔ 
    ∀ t ∈ l.sets, ∃ δ > 0, ∀ x ∈ s, dist x a < δ → x ≠ a → ∀ y ∈ f x, y ∈ t :=
by rw [ptendsto_iff_rtendsto, rtendsto_at_within, pfun.graph']

theorem tendsto_at_within (f : α → β) (a : α) (s : set α) (l : filter β) :
  tendsto f (at_within a s) l ↔ ∀ t ∈ l.sets, ∃ δ > 0, ∀ x ∈ s, dist x a < δ → x ≠ a → f x ∈ t :=
by rw [tendsto_iff_ptendsto', ptendsto_at_within, pfun.res_univ]; 
    simp only [pfun.coe_val, roption.mem_some_iff, forall_eq]

theorem rtendsto_at_pt (r : rel α β) (a : α) (l : filter β) :
  rtendsto r (at_pt a) l ↔ ∀ t ∈ l.sets, ∃ δ > 0, ∀ x, dist x a < δ → x ≠ a → ∀ y, r x y → y ∈ t :=
by rw [at_pt, rtendsto_at_within]; simp

theorem rtendsto'_at_pt (r : rel α β) (a : α) (l : filter β) :
  rtendsto' r (at_pt a) l ↔ ∀ t ∈ l.sets, ∃ δ > 0, ∀ x, dist x a < δ → x ≠ a → ∃ y ∈ t, r x y :=
by rw [at_pt, rtendsto'_at_within]; simp

theorem ptendsto_at_pt (f : α →. β) (a : α) (l : filter β) :
  ptendsto f (at_pt a) l ↔ ∀ t ∈ l.sets, ∃ δ > 0, ∀ x, dist x a < δ → x ≠ a → ∀ y ∈ f x, y ∈ t :=
by rw [at_pt, ptendsto_at_within]; simp

theorem tendsto_at_pt (f : α → β) (a : α) (l : filter β) :
  tendsto f (at_pt a) l ↔ ∀ t ∈ l.sets, ∃ δ > 0, ∀ x, dist x a < δ → x ≠ a → f x ∈ t :=
by rw [at_pt, tendsto_at_within]; simp

end metric




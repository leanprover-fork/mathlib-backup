/- Categories which are small relative to a cardinal κ.
   κ-filtered categories.
   Normally we care about these concepts for categories which are
   used to index (co)limits, so we work with small_categories. -/

import category_theory.category
import category_theory.functor
import category_theory.limits.shape -- for cocone
import category_theory.preorder
import category_theory.products
import set_theory.cofinality

universes u u' v'

open classical cardinal function set

def is_singleton (α : Type u) : Prop := nonempty (α ≃ unit)

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
local infixr ` ↝ `:80 := category_theory.functor

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

-- filtered categories

structure kappa_filtered (C : Type u) [small_category C] : Prop :=
(cocone_functor : ∀ {I : Type u} [small_category I] (hI : is_kappa_small κ I) (F : I ↝ C),
  nonempty (limits.cocone F))

-- [A&R, 1.21]
structure kappa_filtered' (C : Type u) [small_category C] : Prop :=
(cocone_objs : ∀ {I : Type u} (hI : card I < κ) (F : I → C),
  nonempty Σ (Z : C), Π i, F i ⟶ Z)
(cocone_parallel : ∀ {X Y : C} (I : Type u) (hI : card I < κ) (F : I → (X ⟶ Y)),
  ∃ (Z : C) (g : Y ⟶ Z), ∀ i j, F i ≫ g = F j ≫ g)

-- I think this made things much too complicated.
-- Better would be (mors : set (Σ X Y, X ⟶ Y)) and a condition that endpoints of a mor are in objs
structure subgraph (C : Type u) [small_category C] : Type u :=
(objs : set C)
(homs : Π X Y : objs, set (X.1 ⟶ Y.1))

def subgraph.is_kappa_small {C : Type u} [small_category C] (S : subgraph C) : Prop :=
card S.objs < κ ∧ card (Σ X Y, S.homs X Y) < κ

lemma subgraph.hom_small_of_kappa_small {C : Type u} [small_category C] {S : subgraph C}
  (h : S.is_kappa_small κ) (X Y : S.objs) : card (S.homs X Y) < κ :=
lt_of_le_of_lt
  (le_of_injective (λ f, show Σ X Y, S.homs X Y, from ⟨X, Y, f⟩) (by tidy)) h.2

-- TODO: Deduplicate with category version?
lemma subgraph.kappa_small_of_ob_and_hom_small {C : Type u} [small_category C] {S : subgraph C}
  (h₀ : card S.objs < κ) (h₁ : ∀ (X Y : S.objs), card (S.homs X Y) < κ) :
  S.is_kappa_small κ :=
begin
  refine ⟨h₀, _⟩,
  apply small_of_small_sigma_of_small κ h₀, intro X,
  apply small_of_small_sigma_of_small κ h₀, intro Y,
  exact h₁ X Y
end

section subgraph_stuff
variables {C : Type u} [small_category C]

def le_subgraph (S T : subgraph C) : Prop :=
∃ h₀ : S.objs ⊆ T.objs, ∀ (X Y : S.objs),
  S.homs X Y ⊆ T.homs ⟨X.1, by exact h₀ X.2⟩ ⟨Y.1, by exact h₀ Y.2⟩

instance : preorder (subgraph C) :=
{ le := le_subgraph,
  le_refl := by tidy,
  le_trans := λ S T U hST hTU, ⟨by tidy, begin
    rcases hST with ⟨_, hST₂⟩, rcases hTU with ⟨_, hTU₂⟩,
    intros X Y f hf, exact hTU₂ _ _ (hST₂ _ _ hf)
  end⟩ }

section singleton_subgraph
variables (c : C)

inductive singleton_objs : set C
| is_c : singleton_objs c
open singleton_objs

inductive singleton_homs : Π (X Y : singleton_objs c), set (X.1 ⟶ Y.1)
| is_id_c : singleton_homs ⟨c, is_c c⟩ ⟨c, is_c c⟩ (category.id c)

def singleton_subgraph : subgraph C :=
{ objs := singleton_objs c, homs := singleton_homs c }

lemma singleton_subgraph_is_small : (singleton_subgraph c).is_kappa_small κ := sorry

end singleton_subgraph

section single_morphism_subgraph
variables {c d : C} (f : c ⟶ d)
include f

inductive single_morphism_objs : set C
| src : single_morphism_objs c
| tgt : single_morphism_objs d
open single_morphism_objs

inductive single_morphism_homs : Π (X Y : single_morphism_objs f), set (X.1 ⟶ Y.1)
| is_f : single_morphism_homs ⟨c, src f⟩ ⟨d, tgt f⟩ f

def single_morphism_subgraph : subgraph C :=
{ objs := single_morphism_objs f, homs := single_morphism_homs f }

lemma single_morphism_subgraph_is_small : (single_morphism_subgraph f).is_kappa_small κ := sorry

end single_morphism_subgraph

section union_subgraph
variables {ι : Type u} (S : ι → subgraph C)

inductive union_subgraph_objs : set C
| mem_obj : Π (i : ι) (X : C) (hX : X ∈ (S i).objs), union_subgraph_objs X
open union_subgraph_objs

inductive union_subgraph_homs : Π (X Y : union_subgraph_objs S), set (X.1 ⟶ Y.1)
| mem_hom : Π (i : ι) (X Y : (S i).objs) (f : X.1 ⟶ Y.1) (hf : f ∈ (S i).homs X Y),
  union_subgraph_homs ⟨X.1, mem_obj i _ X.2⟩ ⟨Y.1, mem_obj i _ Y.2⟩ f

def union_subgraph : subgraph C :=
{ objs := union_subgraph_objs S, homs := union_subgraph_homs S }

lemma subgraph_union (i : ι) : S i ≤ union_subgraph S :=
⟨assume X hX, mem_obj i X hX,
 assume X Y f hf, union_subgraph_homs.mem_hom i X Y f hf⟩

lemma union_small_of_small (hι : card ι < κ) (h : ∀ i, (S i).is_kappa_small κ) :
  (union_subgraph S).is_kappa_small κ :=
sorry

end union_subgraph

section image_subgraph
variables {D : Type u} [small_category D]
variables (F : C ↝ D) (S : subgraph C)

inductive image_subgraph_objs : set D
| img_obj : Π (X : S.objs), image_subgraph_objs (F X)
open image_subgraph_objs

inductive image_subgraph_homs : Π (X Y : image_subgraph_objs F S), set (X.1 ⟶ Y.1)
| img_hom : Π (X Y : S.objs) (f : X.1 ⟶ Y.1) (hf : f ∈ S.homs X Y),
  image_subgraph_homs ⟨F X.1, img_obj F X⟩ ⟨F Y.1, img_obj F Y⟩ (F.map f)

def image_subgraph : subgraph D :=
{ objs := image_subgraph_objs F S, homs := image_subgraph_homs F S }

lemma image_small_of_small (hS : S.is_kappa_small κ) : (image_subgraph F S).is_kappa_small κ :=
sorry
-- TODO: We actually proved this already, below. Move that proof here

end image_subgraph
end subgraph_stuff


structure kappa_filtered'' (C : Type u) [small_category C] : Prop :=
(cocone_subgraph : ∀ (S : subgraph C) (h : S.is_kappa_small κ),
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

lemma discrete_is_small {ob : Type u} (h : card ob < κ) : is_kappa_small κ (discrete ob) :=
begin
  apply kappa_small_of_ob_and_hom_small,
  { exact h },
  { intros X Y, change card (ulift (plift (X = Y))) < κ,
    have : subsingleton (ulift (plift (X = Y))) := by apply_instance,
    calc card (ulift (plift (X = Y))) ≤ 1 : le_one_iff_subsingleton.mpr this
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

lemma suspension_is_small {mor : Type u} (h : card mor < κ) :
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

lemma filtered_implies_filtered' (h : kappa_filtered κ C) : kappa_filtered' κ C :=
{ cocone_objs := assume I hI F,
    let ⟨t⟩ := h.cocone_functor (discrete_is_small κ hI) (discrete_functor_of_function F) in
    ⟨⟨t.X, λ i, t.ι i⟩⟩,
  cocone_parallel := assume X Y I hI F,
    let ⟨t⟩ := h.cocone_functor (suspension_is_small κ hI) (suspension_functor_of_function F) in
    have ∀ k, F k ≫ t.ι tgt = t.ι src, from assume k, t.w (show @src I ⟶ @tgt I, from k),
    ⟨t.X, t.ι tgt, λ i j, (this i).trans (this j).symm⟩ }

lemma kappa_filtered'.cone_parallel_two (h : kappa_filtered' κ C) {X Y : C} (f g : X ⟶ Y) :
  ∃ (Z : C) (h : Y ⟶ Z), f ≫ h = g ≫ h :=
let ⟨Z, h, hh⟩ :=
  h.cocone_parallel (ulift bool) (is_small_of_finite _)
    (λ i, match i.down with | ff := f | tt := g end) in
⟨Z, h, hh ⟨ff⟩ ⟨tt⟩⟩

lemma filtered'_implies_filtered'' (h : kappa_filtered' κ C) : kappa_filtered'' κ C :=
{ cocone_subgraph := assume S ⟨hS₀, hS₁⟩,
  -- The strategy is as follows:
  -- 1. Form a cocone on all the objects of S, with new vertex Z₀ and cocone maps e_X : X → Z₀
  -- 2. For each morphism f : X → Y in S, coequalize f_X and f_Y ∘ f, via a new map g_f : Z₀ → Z_f
  -- 3. Form a cocone on all the objects Z_f, with new vertex Z₁ and cocone maps j_f : Z_f → Z₁
  -- 4. Coequalize all the morphisms h_f ∘ g_f, with new vertex Z. Call their common composition l.
  -- Then we can build a cocone on all of S which maps X to Z via l ∘ e_X.
  -- If there aren't any morphisms in S, then we have a problem in step 4, but then we can just
  -- use the original cocone Z₀.
  let ⟨⟨Z₀, e⟩⟩ := h.cocone_objs hS₀ (λ X, X) in
  have ∀ (f : Σ X Y, S.homs X Y), ∃ (p : Σ Z, Z₀ ⟶ Z), e f.1 ≫ p.2 = (f.2.2.val ≫ e f.2.1) ≫ p.2,
  from assume ⟨X, Y, f⟩, let ⟨Z, h, hh⟩ := h.cone_parallel_two κ (e X) (f.val ≫ e Y) in ⟨⟨Z, h⟩, hh⟩,
  let ⟨g, hg⟩ := axiom_of_choice this,
      ⟨⟨Z₁, j⟩⟩ := h.cocone_objs hS₁ (λ f, (g f).1),
      ⟨Z, k, hk⟩ := h.cocone_parallel (Σ X Y, S.homs X Y) hS₁ (λ f, (g f).2 ≫ j f) in
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

lemma filtered''_implies_filtered (h : kappa_filtered'' κ C) : kappa_filtered κ C :=
{ cocone_functor := assume I catI hI F, by letI := catI; exact
  let S : subgraph C :=
        { objs := {X | ∃ i, F i = X},
          homs := λ X Y, {f | ∃ (ijg : Σ (i j : I), i ⟶ j), F ijg.1 = X ∧ F ijg.2.1 = Y ∧ F.map ijg.2.2 == f} } in
  have hS₀ : card S.objs < κ, begin
    refine lt_of_le_of_lt _ (ob_small_of_small κ hI),
    refine ge_of_surjective (λ i, ⟨F i, i, rfl⟩) _,
    rintro ⟨X, i, rfl⟩, exact ⟨i, rfl⟩
  end,
  have hS₁ : card (Σ X Y, S.homs X Y) < κ, begin
    refine lt_of_le_of_lt _ hI,
    refine ge_of_surjective
      (λ ijg, ⟨⟨F ijg.1, ijg.1, rfl⟩, ⟨F ijg.2.1, ijg.2.1, rfl⟩, F.map ijg.2.2, ijg, rfl, rfl, heq.rfl⟩) _,
    rintro ⟨⟨X, _⟩, ⟨Y, _⟩, ⟨f, ijg, ⟨⟩, ⟨⟩, ⟨⟩⟩⟩,
    exact ⟨ijg, rfl⟩
  end,
  let ⟨Z, g, hg⟩ := h.cocone_subgraph S ⟨hS₀, hS₁⟩ in
  ⟨{ X := Z, ι := λ i, g ⟨F i, i, rfl⟩,
     w := assume i i' f, hg ⟨F i, i, rfl⟩ ⟨F i', i', rfl⟩ ⟨F.map f, ⟨i, i', f⟩, rfl, rfl, heq.rfl⟩ }⟩ }

lemma filtered'_iff_filtered : kappa_filtered' κ C ↔ kappa_filtered κ C :=
⟨λ h, filtered''_implies_filtered κ (filtered'_implies_filtered'' κ h),
 λ h, filtered_implies_filtered' κ h⟩

lemma filtered''_iff_filtered : kappa_filtered'' κ C ↔ kappa_filtered κ C :=
⟨λ h, filtered''_implies_filtered κ h,
 λ h, filtered'_implies_filtered'' κ (filtered_implies_filtered' κ h)⟩

-- Next: A filtered category admits a cofinal functor from a directed one

section directed_from_filtered

-- We will need all the following properties of Z to define the functor I → C:
-- 1. For every X ∈ S, there is a unique map e_X : X → Z that belongs to S.
-- 2. The identity of Z belongs to S (so e_Z = 𝟙 Z).
-- 3. For each f : X → Y ∈ S, we have e_Y ∘ f = e_X.
-- These are guaranteed by the ability to take a cocone on a subgraph.
structure is_end (S : subgraph C) (Z : S.objs) :=
(e : Π (X : S.objs), X.1 ⟶ Z.1)
(mem : ∀ (X : S.objs), e X ∈ S.homs X Z)
(id : e Z = category.id Z)
-- TODO: ⦃X Y⦄?
(comp : ∀ (X Y : S.objs) (f : X.1 ⟶ Y.1) (hf : f ∈ S.homs X Y), f ≫ e Y = e X)

variables (C)
-- The proof in [A&R] considers subcategories with a unique terminal
-- object. We've replaced subcategories with subgraphs and a terminal
-- object with an "end" as defined above. But the end does not
-- actually have to be unique either, it just needs to be chosen along
-- with the subgraph.
structure I : Type u :=
(S : subgraph C)
(hS : S.is_kappa_small κ)
(Z : S.objs)
(hZ : is_end S Z)

instance I.preorder : preorder (I κ C) :=
{ le := λ S T, S.1 ≤ T.1,
  le_refl := λ S, le_refl S.1,
  le_trans := λ S T U hST hTU, le_trans hST hTU }

-- This is not the real definition, but good enough for our purposes
-- (it is what we are going to prove anyways).
variables {C}
def cofinal {J : Type u} [small_category J] (G : J ↝ C) : Prop :=
(∀ c, ∃ i, nonempty (c ⟶ G i)) ∧
(∀ c i i' (f : c ⟶ G i) (f' : c ⟶ G i'), ∃ i'' (g : i ⟶ i'') (g' : i' ⟶ i''),
  f ≫ G.map g = f' ≫ G.map g')

variables (C)
structure conclusion :=
(I : Type u)
[preI : preorder I]
(hI : kappa_filtered κ I)       -- TODO: kappa_directed, for preorders?
(F : I ↝ C)
(hF : cofinal F)

section part_I
def part_I_condition : Prop :=
∀ (S : subgraph C), S.is_kappa_small κ → ∃ (T : I κ C), S ≤ T.S

variables (hC : part_I_condition κ C)

variables {κ C}
lemma I_kappa_directed {α : Type u} (hα : card α < κ) (f : α → I κ C) : ∃ T, ∀ a, f a ≤ T :=
let S : subgraph C :=
      { objs := ⋃ (a : α), (f a).S.objs,
        homs := λ X Y, ⋃ (a : {a : α // X.1 ∈ (f a).S.objs ∧ Y.1 ∈ (f a).S.objs}),
          (f a.1).S.homs ⟨X, a.2.1⟩ ⟨Y, a.2.2⟩ },
    ⟨T, h⟩ := hC S $ begin
      apply subgraph.kappa_small_of_ob_and_hom_small,
      { apply small_of_small_union_of_small, { exact hα }, { exact (λ a, (f a).hS.1) } },
      { intros X Y,
        apply small_of_small_union_of_small,
        { exact lt_of_le_of_lt le_of_subtype hα },
        { rintro ⟨a, aX, aY⟩, apply subgraph.hom_small_of_kappa_small, exact (f a).hS } }
    end in
⟨T, assume a, show (f a).S ≤ T.S, begin
  refine le_trans _ h,
  refine ⟨subset_Union (λ a, (f a).S.objs) a, _⟩,
  rintros ⟨_,X₂⟩ ⟨_,Y₂⟩ f hf, simp, exact ⟨a, ⟨X₂, Y₂⟩, hf⟩
 end⟩

-- TODO: general equivalence between kappa_directed & kappa_filtered for preorders
lemma I_kappa_filtered : kappa_filtered κ (I κ C) :=
(filtered'_iff_filtered κ).mp
  { cocone_objs := λ α hα F, let ⟨T, hT⟩ := I_kappa_directed hC hα F in ⟨⟨T, λ a, ⟨⟨hT a⟩⟩⟩⟩,
    cocone_parallel := λ _ Y _ _ _, ⟨Y, category.id Y, by tidy⟩ }

variables (κ C)
def F : I κ C ↝ C :=
{ obj := λ S, S.Z,
  map' := λ S T h, T.hZ.e ⟨S.Z.1, (Exists.fst h.down.down) S.Z.2⟩,
  map_id' := λ S, by convert S.hZ.id; simp,
  map_comp' := λ S T U hST hTU, begin
    symmetry,
    -- TODO: Clean this up
    apply U.hZ.comp
      ⟨S.Z.1, (Exists.fst (hST ≫ hTU).down.down) S.Z.2⟩
      ⟨T.Z.1, (Exists.fst hTU.down.down) T.Z.2⟩,
    rcases hTU with ⟨⟨⟨h₁, h₂⟩⟩⟩,
    apply h₂,
    apply T.hZ.mem
  end }

-- Next, we have to prove that F is cofinal.
variables {C}

inductive union_index : Type u
| uS | uT | uf | uf'
open union_index

instance union_index.fintype : fintype union_index := sorry

include hC
local attribute [elab_simple] subgraph_union
lemma cofinal_F : cofinal (F κ C) :=
⟨begin
   intro c,
   refine ⟨⟨singleton_subgraph c, _, ⟨c, singleton_objs.is_c c⟩, ⟨_, _, _, _⟩⟩, ⟨category.id c⟩⟩,
   { exact singleton_subgraph_is_small κ c },
   { rintro ⟨_, ⟨⟩⟩, apply category.id },
   { rintro ⟨_, ⟨⟩⟩, exact singleton_homs.is_id_c c },
   { refl },
   { rintros ⟨_, ⟨⟩⟩ ⟨_, ⟨⟩⟩ f ⟨⟩, simp }
 end,
 begin
   intros c S T f f',
   let U_ : union_index → subgraph C := λ i, match i with
   | uS := S.S
   | uT := T.S
   | uf := single_morphism_subgraph f
   | uf' := single_morphism_subgraph f'
   end,
   let U₀ := union_subgraph U_,
   have U_small : ∀ i, (U_ i).is_kappa_small κ := λ i, match i with
   | uS := S.hS
   | uT := T.hS
   | uf := single_morphism_subgraph_is_small κ f
   | uf' := single_morphism_subgraph_is_small κ f'
   end,
   have U₀_small : U₀.is_kappa_small κ := union_small_of_small κ U_ (is_small_of_finite κ) U_small,
   rcases hC U₀ U₀_small with ⟨U, hU⟩,
   refine ⟨U, ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, _⟩,
   -- TODO: Refactor all this reasoning about membership/subgraphs (also in def of F)
   { change S.S ≤ U.S, exact le_trans (subgraph_union U_ uS) hU },
   { change T.S ≤ U.S, exact le_trans (subgraph_union U_ uT) hU },
   { have : c ∈ U.S.objs := (le_trans (subgraph_union U_ uf) hU).fst (single_morphism_objs.src f),
     have h1 := U.hZ.comp ⟨c, this⟩ ⟨_, (le_trans (subgraph_union U_ uS) hU).fst S.Z.2⟩ f
       (by rcases le_trans (subgraph_union U_ uf) hU with ⟨_, hhom⟩;
           exact hhom _ _ (single_morphism_homs.is_f f)),
     have h2 := U.hZ.comp ⟨c, this⟩ ⟨_, (le_trans (subgraph_union U_ uT) hU).fst T.Z.2⟩ f'
       (by rcases le_trans (subgraph_union U_ uf') hU with ⟨_, hhom⟩;
           exact hhom _ _ (single_morphism_homs.is_f f')),
     erw [h1, h2] }
 end⟩

lemma part_I : nonempty (conclusion κ C) :=
⟨⟨I κ C, I_kappa_filtered hC, F κ C, cofinal_F κ hC⟩⟩

end part_I

section part_II

-- Now we show that if K is a set of cardinality κ which we view as an
-- indiscrete category, then C × K has the property required for
-- part_I and the functor C × K → C is cofinal.

section K
variables (K : Type u) (hK : card K = κ)

section indiscrete
def indiscrete (α : Type u) : Type u := α
instance indiscrete.small_category (α : Type u) : small_category (indiscrete α) :=
{ hom := λ X Y, punit,
  id := λ X, punit.star,
  comp := λ X Y Z f g, punit.star }
end indiscrete

include hK
lemma CxK_part_I (hC : kappa_filtered κ C) : part_I_condition κ (C × indiscrete K) :=
assume S hS,
  let S' := image_subgraph (prod.fst.{u u u u} C (indiscrete K)) S in
  have S'_small : S'.is_kappa_small κ, from image_small_of_small κ _ _ hS,
  let ⟨Z, g, h⟩ := ((filtered''_iff_filtered κ).mpr hC).cocone_subgraph S' S'_small in
  let ks : set K := _root_.prod.snd '' S.objs in
  have ks ≠ univ, begin
    intro H, change _root_.prod.snd '' set_of S.objs = univ at H,
    rw [←subtype_val_range, ←range_comp, range_iff_surjective] at H,
    apply not_le_of_lt hS.1,
    convert ge_of_surjective _ H,
    exact hK.symm
  end,
  let ⟨k, _, hk⟩ := exists_of_ssubset ⟨subset_univ ks, this⟩ in
  let T : subgraph (C × indiscrete K) := _ in
  -- We need to take S and throw in all the maps to (Z, k) determined by the cocone g.
  -- Then (Z, k) will be an end of this subgraph.
  ⟨⟨T, _, ⟨⟨Z, k⟩, _⟩, _⟩, _⟩

end K

end part_II

end directed_from_filtered

end

end category_theory

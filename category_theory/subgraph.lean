import category_theory.functor
import category_theory.small

universe u

open cardinal

local notation `card` := cardinal.mk

variables (κ : regular_cardinal.{u})

namespace category_theory
local infixr ` ↝ `:80 := category_theory.functor

-- I think this made things much too complicated.
-- Better would be (mors : set (Σ X Y, X ⟶ Y)) and a condition that endpoints of a mor are in objs
structure subgraph (C : Type u) [small_category C] : Type u :=
(objs : set C)
(homs : Π X Y : C, set (X ⟶ Y))
(dom_mem : Π {X Y} {f : X ⟶ Y}, f ∈ homs X Y → X ∈ objs . obviously)
(cod_mem : Π {X Y} {f : X ⟶ Y}, f ∈ homs X Y → Y ∈ objs . obviously)

def subgraph.dom {C : Type u} [small_category C] (S : subgraph C) {X Y : C} (f : S.homs X Y) : S.objs :=
⟨X, S.dom_mem f.property⟩

def subgraph.cod {C : Type u} [small_category C] (S : subgraph C) {X Y : C} (f : S.homs X Y) : S.objs :=
⟨Y, S.cod_mem f.property⟩

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
  refine ⟨h₀, _⟩, admit
/-  apply small_of_small_sigma_of_small κ h₀, intro X,
  apply small_of_small_sigma_of_small κ h₀, intro Y,
  exact h₁ X Y -/
end

variables {C : Type u} [small_category C]

-- Also, use ⊆ notation?
--def le_subgraph (S T : subgraph C) : Prop :=
instance : has_subset (subgraph C) :=
⟨λ S T, S.objs ⊆ T.objs ∧ ∀ X Y, S.homs X Y ⊆ T.homs X Y⟩
/-
∃ h₀ : S.objs ⊆ T.objs, ∀ (X Y : S.objs),
  S.homs X Y ⊆ T.homs ⟨X.1, by exact h₀ X.2⟩ ⟨Y.1, by exact h₀ Y.2⟩
-/

instance : preorder (subgraph C) :=
{ le := (⊆),
  le_refl := by tidy,
  le_trans := by tidy }

instance subgraph.has_mem_obj : has_mem C (subgraph C) := { mem := λ X S, X ∈ S.objs }

lemma obj_mem_of_mem_of_subgraph {X : C} {S T : subgraph C} (hX : X ∈ S) (h : S ≤ T) : X ∈ T :=
h.1 hX

lemma hom_mem_of_mem_of_subgraph {X Y : C} {f : X ⟶ Y} {S T : subgraph C}
  (hf : f ∈ S.homs X Y) (h : S ≤ T) : f ∈ T.homs X Y :=
by tidy

instance : has_emptyc (subgraph C) :=
⟨{ objs := ∅, homs := λ X Y, ∅, dom_mem := by tidy, cod_mem := by tidy }⟩

section singleton_subgraph
variables (c : C)

inductive singleton_objs : set C
| is_c : singleton_objs c
open singleton_objs

inductive singleton_homs : Π (X Y : C), set (X ⟶ Y)
| is_id_c : singleton_homs c c (category.id c)

def singleton_subgraph : subgraph C :=
{ objs := singleton_objs c,
  homs := singleton_homs c,
  dom_mem := by rintros _ _ _ ⟨⟩; exact is_c c,
  cod_mem := by rintros _ _ _ ⟨⟩; exact is_c c }

@[simp] lemma obj_mem_singleton_subgraph : c ∈ singleton_subgraph c := sorry

lemma singleton_subgraph_is_small : (singleton_subgraph c).is_kappa_small κ := sorry

end singleton_subgraph

section single_morphism_subgraph
variables {c d : C} (f : c ⟶ d)
include f

inductive single_morphism_objs : set C
| dom : single_morphism_objs c
| cod : single_morphism_objs d
open single_morphism_objs

inductive single_morphism_homs : Π (X Y : C), set (X ⟶ Y)
| is_f : single_morphism_homs c d f

def single_morphism_subgraph : subgraph C :=
{ objs := single_morphism_objs f,
  homs := single_morphism_homs f,
  dom_mem := by rintros _ _ _ ⟨⟩; exact dom f,
  cod_mem := by rintros _ _ _ ⟨⟩; exact cod f }

@[simp] lemma dom_mem_single_morphism {X Y : C} (f : X ⟶ Y) : X ∈ single_morphism_subgraph f := sorry
@[simp] lemma cod_mem_single_morphism {X Y : C} (f : X ⟶ Y) : Y ∈ single_morphism_subgraph f := sorry
@[simp] lemma mem_single_morphism {X Y : C} (f : X ⟶ Y) : f ∈ (single_morphism_subgraph f).homs X Y :=
sorry

@[simp] lemma single_morphism_subgraph_is_small : (single_morphism_subgraph f).is_kappa_small κ := sorry

end single_morphism_subgraph

instance : has_union (subgraph C) :=
⟨λ S T,
 { objs := S.objs ∪ T.objs,
   homs := λ X Y, S.homs X Y ∪ T.homs X Y,
   dom_mem := λ X Y f hf, begin cases hf, exact or.inl (S.dom_mem hf), exact or.inr (T.dom_mem hf) end,
   cod_mem := λ X Y f hf, begin cases hf, exact or.inl (S.cod_mem hf), exact or.inr (T.cod_mem hf) end }⟩

@[simp] lemma obj_mem_union_eq (X : C) (S T : subgraph C) : X ∈ S ∪ T = (X ∈ S ∨ X ∈ T) := rfl
@[simp] lemma hom_mem_union_eq {X Y : C} (f : X ⟶ Y) (S T : subgraph C) :
  f ∈ (S ∪ T).homs X Y = (f ∈ S.homs X Y ∨ f ∈ T.homs X Y) := rfl

@[simp] lemma subgraph_union_left (S T : subgraph C) : S ⊆ S ∪ T := sorry
@[simp] lemma subgraph_union_right (S T : subgraph C) : T ⊆ S ∪ T := sorry

lemma union_small_of_small_of_small {S T : subgraph C} :
  S.is_kappa_small κ → T.is_kappa_small κ → (S ∪ T).is_kappa_small κ :=
sorry

@[simp] lemma union_small_iff {S T : subgraph C} :
  (S ∪ T).is_kappa_small κ ↔ (S.is_kappa_small κ ∧ T.is_kappa_small κ) := sorry

section union_subgraph
variables {ι : Type u} (S : ι → subgraph C)

inductive union_subgraph_objs : set C
| mem_obj : Π (i : ι) {X : C} (hX : X ∈ (S i).objs), union_subgraph_objs X
open union_subgraph_objs

inductive union_subgraph_homs : Π (X Y : C), set (X ⟶ Y)
| mem_hom : Π (i : ι) {X Y : C} {f : X ⟶ Y} (hf : f ∈ (S i).homs X Y), union_subgraph_homs X Y f

def union_subgraph : subgraph C :=
{ objs := union_subgraph_objs S, homs := union_subgraph_homs S,
  dom_mem := λ X Y f hf, by cases hf with i _ _ _ hf; exact mem_obj i ((S i).dom_mem hf),
  cod_mem := λ X Y f hf, by cases hf with i _ _ _ hf; exact mem_obj i ((S i).cod_mem hf) }

lemma subgraph_union (i : ι) : S i ≤ union_subgraph S :=
⟨assume X hX, mem_obj i hX,
 assume X Y f hf, union_subgraph_homs.mem_hom i hf⟩

lemma union_small_of_small (hι : card ι < κ) (h : ∀ i, (S i).is_kappa_small κ) :
  (union_subgraph S).is_kappa_small κ :=
sorry

end union_subgraph

section image_subgraph
variables {D : Type u} [small_category D]
variables (F : C ↝ D) (S : subgraph C)

inductive image_subgraph_objs : set D
| img_obj : Π {X : C} (hX : X ∈ S.objs), image_subgraph_objs (F X)
open image_subgraph_objs

inductive image_subgraph_homs : Π (X Y : D), set (X ⟶ Y)
| img_hom : Π {X Y : C} {f : X ⟶ Y} (hf : f ∈ S.homs X Y),
  image_subgraph_homs (F X) (F Y) (F.map f)

def image_subgraph : subgraph D :=
{ objs := image_subgraph_objs F S,
  homs := image_subgraph_homs F S,
  dom_mem := λ _ _ _ hf, by cases hf with _ _ f hf'; exact img_obj F (S.dom_mem hf'),
  cod_mem := λ _ _ _ hf, by cases hf with _ _ f hf'; exact img_obj F (S.cod_mem hf') }

lemma image_small_of_small (hS : S.is_kappa_small κ) : (image_subgraph F S).is_kappa_small κ :=
sorry
-- TODO: We actually proved this already, below. Move that proof here

end image_subgraph

end category_theory


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

lemma obj_mem_of_mem_of_subgraph {X : C} {S T : subgraph C} (hX : X ∈ S.objs) (h : S ≤ T) : X ∈ T.objs :=
h.fst hX

lemma hom_mem_of_mem_of_subgraph {S T : subgraph C} {X Y : S.objs} {f : X.1 ⟶ Y.1}
  (h : S ≤ T) (hf : f ∈ S.homs X Y) : f ∈ T.homs ⟨X.1, h.fst X.2⟩ ⟨Y.1, h.fst Y.2⟩ :=
by rcases h with ⟨_, hhom⟩; exact hhom _ _ hf

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

end category_theory


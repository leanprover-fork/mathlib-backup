/- Categories which are small relative to a cardinal κ.
   κ-filtered categories.
   Normally we care about these concepts for categories which are
   used to index (co)limits, so we work with small_categories. -/

import category_theory.category
import category_theory.functor
import category_theory.limits.shape -- for cocone
import category_theory.products
import category_theory.small
import category_theory.subgraph
import set_theory.cofinality

universes u u' v'

open classical cardinal function set

local notation `card` := cardinal.mk.{u} -- Maybe this is a bad idea?
variables (κ : regular_cardinal.{u})

namespace category_theory
local infixr ` ↝ `:80 := category_theory.functor

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

structure kappa_filtered'' (C : Type u) [small_category C] : Prop :=
(cocone_subgraph : ∀ (S : subgraph C) (h : S.is_kappa_small κ),
  ∃ (Z : C) (g : Π X : S.objs, X.1 ⟶ Z), ∀ X Y (f : S.homs X Y), f.1 ≫ g (S.cod f) = g (S.dom f))

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
  have ∀ (f : Σ X Y, S.homs X Y), ∃ (p : Σ Z, Z₀ ⟶ Z),
    e (S.dom f.2.2) ≫ p.2 = (f.2.2.val ≫ e (S.cod f.2.2)) ≫ p.2,
  from assume ⟨X, Y, f⟩,
    let ⟨Z, h, hh⟩ := h.cone_parallel_two κ (e (S.dom f)) (f.val ≫ e (S.cod f)) in ⟨⟨Z, h⟩, hh⟩,
  let ⟨g, hg⟩ := axiom_of_choice this,
      ⟨⟨Z₁, j⟩⟩ := h.cocone_objs hS₁ (λ f, (g f).1),
      ⟨Z, k, hk⟩ := h.cocone_parallel (Σ X Y, S.homs X Y) hS₁ (λ f, (g f).2 ≫ j f) in
  by_cases
    (λ (hhom : nonempty (Σ X Y, S.homs X Y)),
      let ⟨f₀⟩ := hhom in
      have ∀ f : Σ X Y, S.homs X Y, (g f₀).2 ≫ j f₀ ≫ k = (g f).2 ≫ j f ≫ k,
      from assume f, by simpa using hk f₀ f,
      ⟨Z, λ X, e X ≫ (g f₀).2 ≫ j f₀ ≫ k, λ _ _ f,
        let X := S.dom f, Y := S.cod f in
        calc f.val ≫ e Y ≫ (g f₀).snd ≫ j f₀ ≫ k
            = f.val ≫ e Y ≫ (g ⟨X, Y, f⟩).snd ≫ j ⟨X, Y, f⟩ ≫ k   : by rw this
        ... = ((f.val ≫ e Y) ≫ (g ⟨X, Y, f⟩).snd) ≫ j ⟨X, Y, f⟩ ≫ k : by simp
        ... = (e X ≫ (g ⟨X, Y, f⟩).snd) ≫ j ⟨X, Y, f⟩ ≫ k         : by rw hg ⟨X, Y, f⟩
        ... = e X ≫ (g ⟨X, Y, f⟩).snd ≫ j ⟨X, Y, f⟩ ≫ k           : by simp
        ... = e X ≫ (g f₀).snd ≫ j f₀ ≫ k                         : by rw this⟩)
    (λ nohoms, ⟨Z₀, λ X, e X, λ X Y f, by refine absurd _ nohoms; exact ⟨⟨X, Y, f⟩⟩⟩) }

lemma filtered''_implies_filtered (h : kappa_filtered'' κ C) : kappa_filtered κ C :=
{ cocone_functor := assume I catI hI F, by exactI
  -- TODO: image of entire subcategory of I?
  let S : subgraph C :=
        { objs := {X | ∃ i, F i = X},
          homs := λ X Y, {f | ∃ (ijg : Σ (i j : I), i ⟶ j), F ijg.1 = X ∧ F ijg.2.1 = Y ∧ F.map ijg.2.2 == f},
          dom_mem := sorry,
          cod_mem := sorry } in
  have hS₀ : card S.objs < κ, begin
    refine lt_of_le_of_lt _ (ob_small_of_small κ hI),
    refine ge_of_surjective (λ i, ⟨F i, i, rfl⟩) _,
    rintro ⟨X, i, rfl⟩, exact ⟨i, rfl⟩
  end,
  have hS₁ : card (Σ X Y, S.homs X Y) < κ, begin
    refine lt_of_le_of_lt _ hI,
    refine ge_of_surjective
      (λ ijg, ⟨F ijg.1, F ijg.2.1, F.map ijg.2.2, ijg, rfl, rfl, heq.rfl⟩) _,
    rintro ⟨X, Y, ⟨f, ijg, ⟨⟩, ⟨⟩, ⟨⟩⟩⟩,
    exact ⟨ijg, rfl⟩
  end,
  let ⟨Z, g, hg⟩ := h.cocone_subgraph S ⟨hS₀, hS₁⟩ in
  ⟨{ X := Z, ι := λ i, g ⟨F i, i, rfl⟩,
     w := assume i i' f, hg (F i) (F i') ⟨F.map f, ⟨i, i', f⟩, rfl, rfl, heq.rfl⟩ }⟩ }

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
-- TODO: Move this proof to image_small_of_small
/-let S : subgraph C :=
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
    end in-/
let S : subgraph C := union_subgraph (λ a, (f a).S),
    hS : S.is_kappa_small κ := sorry,
    ⟨T, h⟩ := hC S hS in
⟨T, assume a, show (f a).S ≤ T.S, by refine le_trans _ h; exact subgraph_union _ a⟩

-- TODO: general equivalence between kappa_directed & kappa_filtered for preorders
lemma I_kappa_filtered : kappa_filtered κ (I κ C) :=
(filtered'_iff_filtered κ).mp
  { cocone_objs := λ α hα F, let ⟨T, hT⟩ := I_kappa_directed hC hα F in ⟨⟨T, λ a, ⟨⟨hT a⟩⟩⟩⟩,
    cocone_parallel := λ _ Y _ _ _, ⟨Y, category.id Y, by tidy⟩ }

variables (κ C)
def F : I κ C ↝ C :=
{ obj := λ S, S.Z,
  map' := λ S T h, T.hZ.e ⟨S.Z.1, h.down.down.1 S.Z.2⟩,
  map_id' := λ S, by convert S.hZ.id; simp,
  map_comp' := λ S T U hST hTU, begin
    symmetry,
    -- TODO: Clean this up
    apply U.hZ.comp
      ⟨S.Z.1, (hST ≫ hTU).down.down.1 S.Z.2⟩
      ⟨T.Z.1, hTU.down.down.1 T.Z.2⟩,
    rcases hTU with ⟨⟨⟨h₁, h₂⟩⟩⟩,
    apply h₂,
    apply T.hZ.mem
  end }

-- Next, we have to prove that F is cofinal.
variables {C}

include hC
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
   let U₀ := S.S ∪ T.S ∪ single_morphism_subgraph f ∪ single_morphism_subgraph f',
   have U₀_small : U₀.is_kappa_small κ := by simp [S.hS, T.hS],
   rcases hC U₀ U₀_small with ⟨U, hU⟩,
   have SU : S.S ≤ U.S,
   { refine le_trans _ hU,
     repeat { apply le_refl <|> refine le_trans _ (subgraph_union_left _ _) } },
   have TU : T.S ≤ U.S,
   { refine le_trans _ hU,
     repeat { apply subgraph_union_right <|> refine le_trans _ (subgraph_union_left _ _) } },
   refine ⟨U, ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, _⟩,
   -- TODO: Refactor all this reasoning about membership/subgraphs (also in def of F)
   -- It's still not great.
   { exact SU }, { exact TU },
   { have : c ∈ U₀ := by simp,
     have : c ∈ U.S := hU.1 this,
     have h1 := U.hZ.comp ⟨c, this⟩ ⟨_, SU.1 S.Z.2⟩ f (hU.2 _ _ (by simp)),
     have h2 := U.hZ.comp ⟨c, this⟩ ⟨_, TU.1 T.Z.2⟩ f' (hU.2 _ _ (by simp)),
     erw [h1, h2] }
 end⟩

lemma part_I : nonempty (conclusion κ C) :=
⟨⟨I κ C, I_kappa_filtered hC, F κ C, cofinal_F κ hC⟩⟩

end part_I

section part_II

-- Now we show that if K is a set of cardinality κ which we view as an
-- indiscrete category, then C × K has the property required for
-- part_I and the functor C × K → C is cofinal.

-- First we show that if C is "freshly filtered" in that we can choose
-- a cocone on any κ-small subgraph S with a vertex not belonging to
-- S, then C satisfies the part_I property.

structure freshly_filtered (C : Type u) [small_category C] : Prop :=
(cocone_subgraph : ∀ (S : subgraph C) (h : S.is_kappa_small κ),
  ∃ (Z : C) (g : Π X : S.objs, X.1 ⟶ Z), Z ∉ S.objs ∧
    ∀ X Y (f : S.homs X Y), f.1 ≫ g (S.cod f) = g (S.dom f))

local attribute [instance] prop_decidable

lemma part_I_of_freshly_filtered (hC : freshly_filtered κ C) : part_I_condition κ C :=
assume S hS,
  let ⟨Z, g, hZ, h⟩ := hC.cocone_subgraph S hS in
  let T : subgraph C :=
    S ∪ singleton_subgraph Z ∪ union_subgraph (λ (X : S.objs), single_morphism_subgraph (g X)) in
  have memT : ∀ {X}, X ∈ T → X ∈ S ∨ X = Z, begin
    intros X hX,
    rcases hX with hX₁|hX₂,
    { rcases hX₁ with hX₁|⟨⟨⟩⟩, { exact or.inl hX₁ }, { exact or.inr rfl } },
    { rcases hX₂ with ⟨i, _, _, _, ⟨⟨⟩⟩⟩,
      { exact or.inl i.2 },
      { exact or.inr rfl } }
  end,
  have memS : ∀ {X}, X ∈ S → X ≠ Z, from assume X hS hX, by rw hX at hS; exact absurd hS hZ,
  let g' : Π X : T.objs, X.1 ⟶ Z := λ X,
    if H : X.1 = Z
    then (eq_to_iso H).hom
    else g ⟨X.1, (memT X.2).resolve_right H⟩ in
  begin
    refine ⟨⟨T, _, ⟨Z, _⟩, ⟨g', _, _, _⟩⟩, _⟩,
    -- TODO: Can we make simp kill this entire smallness subgoal?
    { apply union_small_of_small_of_small,
      { exact union_small_of_small_of_small κ hS (singleton_subgraph_is_small _ _) },
      { apply union_small_of_small κ _ hS.1, intro i,
        apply single_morphism_subgraph_is_small } },
    { change Z ∈ T, simp [T] },
    { dsimp [g'], intro X,
      rcases memT X.2 with h₁|h₂,
      { have : X.1 ≠ Z, from memS h₁,
        simp [this], refine hom_mem_of_mem_of_subgraph _ (subgraph_union_right _ _),
        refine hom_mem_of_mem_of_subgraph _ (subgraph_union _ ⟨X.1, h₁⟩),
        apply mem_single_morphism },
      { cases X with X₁ X₂,
        simp [dif_pos h₂],
        refine hom_mem_of_mem_of_subgraph _ (subgraph_union_left _ _),
        refine hom_mem_of_mem_of_subgraph _ (subgraph_union_right _ _),
        cases h₂,
        exact singleton_homs.is_id_c Z } },
      { simp [g'], refl },
      { intros X Y f hf,
        rcases hf with hf|hf₃,
        { rcases hf with hf₁|hf₂,
          { have XZ : X.1 ≠ Z, from memS (S.dom_mem hf₁),
            have YZ : Y.1 ≠ Z, from memS (S.cod_mem hf₁),
            simp [g', dif_neg, XZ, YZ], exact h X.1 Y.1 ⟨f, hf₁⟩ },
          { cases X, cases Y, cases hf₂, simp } },
        { cases X, cases Y, rcases hf₃ with ⟨i, _, _, _, ⟨⟩⟩,
          have iZ : i.1 ≠ Z, from memS i.2,
          cases i, simp [g', dif_neg iZ], refl } },
      { exact le_trans (subgraph_union_left _ _) (subgraph_union_left _ _) }
  end


section K
variables (K : Type u) (hK : card K = κ)

section indiscrete
def indiscrete (α : Type u) : Type u := α
instance indiscrete.small_category (α : Type u) : small_category (indiscrete α) :=
{ hom := λ X Y, punit,
  id := λ X, punit.star,
  comp := λ X Y Z f g, punit.star }
end indiscrete

-- Then we show that if C is κ-filtered and K is a set of cardinality
-- κ then C × K is freshly filtered.
include hK
lemma CxK_part_I' (hC : kappa_filtered κ C) : freshly_filtered κ (C × indiscrete K) :=
{ cocone_subgraph := assume S hS,
  let S' := image_subgraph (prod.fst.{u u u u} C (indiscrete K)) S in
  have S'_small : S'.is_kappa_small κ, from image_small_of_small κ _ _ hS,
  let ⟨Z, g, h⟩ := ((filtered''_iff_filtered κ).mpr hC).cocone_subgraph S' S'_small in
  let ks : set (discrete K) := _root_.prod.snd '' S.objs in
  have ks ≠ univ, begin
    intro H, change _root_.prod.snd '' set_of S.objs = univ at H,
    rw [←subtype_val_range, ←range_comp, range_iff_surjective] at H,
    apply not_le_of_lt hS.1,
    convert ge_of_surjective _ H,
    exact hK.symm
  end,
  let ⟨k, _, hk⟩ := exists_of_ssubset ⟨subset_univ ks, this⟩ in
  let Z' : C × indiscrete K := ⟨Z, k⟩ in
  have Z' ∉ S, from assume h, by refine absurd _ hk; exact ⟨Z', h, rfl⟩,
  ⟨Z', λ X, (g ⟨X.1.1, image_subgraph_objs.img_obj _ X.2⟩, punit.star), this, begin
     intros X Y f,
     apply prod.ext,
     { exact h X.1 Y.1 ⟨f.1.1, image_subgraph_homs.img_hom _ f.2⟩ },
     { apply subsingleton.elim }
   end⟩ }
omit hK

lemma CxK_part_I'' (hC : kappa_filtered κ C) : part_I_condition κ (C × indiscrete K) :=
part_I_of_freshly_filtered κ _ (CxK_part_I' κ C K hK hC)

lemma part_II (hC : kappa_filtered κ C) : nonempty (conclusion κ (C × indiscrete K)) :=
part_I κ (CxK_part_I'' κ C K hK hC)

end K

-- Remaining: check the projection C × indiscrete K → C is cofinal and then conclude

end part_II

end directed_from_filtered

end

end category_theory

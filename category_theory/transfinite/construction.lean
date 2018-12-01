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

noncomputable theory

local attribute [instance] classical.dec

open category_theory category_theory.functor

universes u v

namespace category_theory.transfinite

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

section
variables {β γ : Type v} [partial_order β] [partial_order γ]
def iseg (β γ) [partial_order β] [partial_order γ] := initial_seg ((<) : β → β → Prop) ((<) : γ → γ → Prop)

variables (f : iseg β γ)

def inclusion_functor : β ⥤ γ :=
{ obj := f.to_fun,
  map := λ b₁ b₂ h, ⟨⟨sorry⟩⟩ }
end

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

namespace category_theory.transfinite
section

parameters {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

section build
/- Note on building transfinite compositions

Suppose our aim is to construct a transfinite composition of some
particular "length" γ, γ being a well-ordered type with a greatest
element. This consists of a collection of objects X i for i : γ and
morphisms X i → X j for i j : γ, i ≤ j satisfying some conditions. We
want to construct these by transfinite recursion, forming a colimit at
limit stages and applying some other construction at successor stages.

This is tricky to do by a direct recursion because the objects and
morphisms depend on each other. Obviously the map we append at stage
i+1 must depend on the object X i, but at limit stages we need to form
the next object as a colimit and this construction depends on all the
previous maps. Moreover, in order to continue the construction and
form this colimit, we need to use the fact that the maps chosen so far
actually do define a functor.

In order to organize this construction, we apply the principle of
"consistent recursion". Namely, we will construct for each i : γ a
transfinite composition on the closed initial segment [⊥, i] of γ,
while requiring that for each i < j, the transfinite composition on
[⊥, i] is (strictly!) equal to the restriction of the transfinite
composition on [⊥, j]. (This condition relies on the ability to talk
about the *set* of objects of a category. If we wanted to use only
equivalence-invariant concepts, we'd need to instead construct
isomorphisms here which in turn satisfy some coherence conditions.)
At the end of the process, we have a transfinite composition on [⊥, ⊤]
which we transfer to the original type γ.

This section contains the building blocks for such a construction. For
each type of i (base case, successor case and limit case), we provide
a constructor for building a transfinite composition on [⊥, i] from
consistent transfinite compositions on the earlier segments, and a
lemma showing that the new transfinite composition is consistent with
the previous ones. We also provide a "finalizing" constructor which
transfers a transfinite composition on [⊥, ⊤] to γ.

(TODO: Probably want something more general for this last step, namely
restricting a transfinite composition along the inclusion of an
initial segment (ordinal.initial_seg). Then apply to γ → [⊥, ⊤].)

-/

parameters {I : morphism_class C}

section restrict
local infix ` ≼i `:50 := initial_seg

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

section extension
  
-- * k is the stage we're constructing
-- * Z encodes the choices of all the earlier segments
-- * hZ is the condition that these were compatible

parameters {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]
parameters {k : γ} (Z : Π (i < k), transfinite_composition I (below_top i))
parameters (hZ : ∀ i i' (hik : i < k) (hi'k : i' < k) (hii' : i < i'),
  (Z i hik).F = embed (le_of_lt hii') ⋙ (Z i' hi'k).F)

-- We can include the case i = i' for free
lemma hZ' (i i') (hik : i < k) (hi'k : i' < k) (hii' : i ≤ i') :
  (Z i hik).F = embed hii' ⋙ (Z i' hi'k).F :=
let hZ := hZ in
begin
  cases eq_or_lt_of_le hii' with hii' hii',
  { subst hii',
    fapply category_theory.functor.ext,
    { intros p, cases p, refl },
    { intros p p' hpp', cases p, cases p', dsimp, simp, congr } },
  { apply hZ, exact hii' }
end

/- Note on the domain of prev_F

`prev_F` is the functor obtained as the "union" of all the previous
sequences. Informally it is defined on the open interval [⊥, k). To
construct an extension to the closed interval [⊥, k], we have to
specify a cocone on `prev_F` (called `new` below).

In the limit case, we need to check that the extended functor is
"smooth at k". Because the extended functor is defined on [⊥, k], this
condition involves a diagram defined on {i : [⊥, k] // i < ⊤}. We set
up `prev_F` as a diagram indexed on the same type in order to
facilitate comparison between `new` and the cocone that appears in the
smoothness condition.

-/

-- Glue the previous choices `Z` to define a functor on the open
-- interval [⊥, k). See [Note on the domain of prev_F].
def prev_F : {p : below_top k // p < ⊤} ⥤ C :=
{ obj := λ p, (Z p.val.val p.property).F.obj ⊤,
  map := λ p p' hpp',
    eq_to_hom (eq_obj (hZ' p.val.val p'.val.val p.property p'.property hpp'.down.down) _) ≫
    (Z p'.val.val p'.property).F.map hpp',
  map_id' := λ p, by erw (Z _ _).F.map_id; simp; refl,
  map_comp' := λ p p' p'' hpp' hp'p'', let hZ' := hZ' in begin
    rw eq_hom (hZ' p'.val.val p''.val.val p'.property p''.property hp'p''.down.down) _,
    erw (Z p''.val.val p''.property).F.map_comp,
    dsimp, simp, congr
  end }

-- TODO: Maybe we should prove that `prev_F` extends the `Z`s, and
-- then use that to prove `extend_tcomp_F_extends` from
-- `extend_tcomp_F_extends_prev`?

-- Now, the new stuff! We specify this as a cocone in anticipation of
-- the fact that we'll want to form a colimit at limit stages.
parameters (new : limits.cocone prev_F)

-- Taking this apart into components,
-- * X is the new object
-- * f encodes maps from the previous objects to X
-- * hf is the condition that these maps form a cocone

def X := new.X
def f : Π i (hik : i < k), (Z i hik).F.obj ⊤ ⟶ X :=
λ i hik, new.ι.app ⟨⟨i, le_of_lt hik⟩, hik⟩
lemma hf (i i') (hik : i < k) (hi'k : i' < k) (hii' : i ≤ i') :
  f i hik =
  eq_to_hom (eq_obj (hZ' i i' hik hi'k hii') ⊤) ≫
  (Z i' hi'k).F.map ⟨⟨lattice.le_top⟩⟩ ≫ f i' hi'k :=
begin
  dunfold f,
  rw ←category.assoc,
  let p : {p : below_top k // p < ⊤} := ⟨⟨i, _⟩, hik⟩,
  let p' : {p : below_top k // p < ⊤} := ⟨⟨i', _⟩, hi'k⟩,
  have : p ⟶ p' := ⟨⟨hii'⟩⟩,
  convert (new.w this).symm
end

-- Now build the new underlying functor
def extend_tcomp_F : below_top k ⥤ C :=
{ obj := λ p, if hp : p.val < k then prev_F.obj ⟨p, hp⟩ else X,
  map := λ p p' hpp',
    if hp' : p'.val < k then
      have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
      change_hom (prev_F.obj ⟨p, hp⟩) (prev_F.obj ⟨p', hp'⟩)
        (by simp [hp]) (by simp [hp'])
      (prev_F.map hpp')
    else if hp : p.val < k then
      change_hom (prev_F.obj ⟨p, hp⟩) X (by simp [hp]) (by simp [hp']) (f p.val hp)
    else
      change_hom X X (by simp [hp]) (by simp [hp']) (𝟙 X),
  map_id' := λ p,
    by split_ifs; { dsimp [change_hom], try { erw prev_F.map_id }, simp },
  map_comp' := λ p p' p'' hpp' hp'p'', let hf := hf in begin
    by_cases hp'' : p''.val < k,
    { have hp' : p'.val < k, from lt_of_le_of_lt hp'p''.down.down hp'',
      have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
      simp [hp, hp', hp''],
      erw prev_F.map_comp,
      simp },
    by_cases hp' : p'.val < k,
    { have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
      simp [hp, hp', hp''],
      dsimp [prev_F] { iota := tt },
      simp [hf p.val p'.val hp hp' hpp'.down.down],
      congr },
    by_cases hp : p.val < k; { simp [hp, hp', hp'', change_hom] }
  end }

-- TODO: Does the following lemma trivialize this one?
lemma extend_tcomp_F_extends (i) (hik : i < k) :
  embed (le_of_lt hik) ⋙ extend_tcomp_F = (Z i hik).F :=
let hZ' := hZ' in
begin
  dunfold extend_tcomp_F,
  fapply category_theory.functor.ext,
  { rintro ⟨p₁, p₂⟩,
    have hp : p₁ < k, from lt_of_le_of_lt p₂ hik,
    simpa [hp, prev_F] using eq_obj (hZ' p₁ i _ _ p₂) ⊤ },
  { rintro ⟨p₁, p₂⟩ ⟨p'₁, p'₂⟩ hpp',
    have hp : p₁ < k, from lt_of_le_of_lt p₂ hik,
    have hp' : p'₁ < k, from lt_of_le_of_lt p'₂ hik,
    dsimp, simp [hp, hp'],
    dsimp [prev_F] { iota := tt },
    erw eq_hom (hZ' p'₁ i hp' hik p'₂) ⟨⟨_⟩⟩,
    dsimp, simp, congr }
end

lemma extend_tcomp_F_extends_prev :
  full_subcategory_inclusion (λ p, p < ⊤) ⋙ extend_tcomp_F = prev_F :=
begin
  dunfold extend_tcomp_F,
  fapply category_theory.functor.ext,
  { intro p,
    have hp : p.val.val < k, from p.property,
    simp [hp] },
  { intros p p' hpp',
    have hp : p.val.val < k, from p.property,
    have hp' : p'.val.val < k, from p'.property,
    dsimp,
    simp [hp, hp'],
    refl }
end

-- Transport `new` to a cocone on the restriction of the extended
-- functor `extend_tcomp_F`, for use in verifying the limit stage
-- condition.
def new' : limits.cocone (full_subcategory_inclusion (λ p, p < ⊤) ⋙ extend_tcomp_F) :=
new.precompose (eq_to_hom extend_tcomp_F_extends_prev)

lemma new'_app (p e) : new'.ι.app p = eq_to_hom e ≫ f p.val.val p.property :=
begin
  rcases p with ⟨⟨_,_⟩,_⟩,
  dsimp [f, new', limits.cocone.precompose],
  simp,
  refl
end

-- These cones are actually just *equal*, but as we don't have an
-- extensionality lemma for cocones currently, and we do have
-- `is_colimit.of_iso_colimit`, defining an iso is more convenient.
-- The actual isomorphism is irrelevant for our purposes (we discard
-- the colimit structure in `transfinite_composition` anyways), so
-- mark this as a lemma.
lemma extend_tcomp_F_cone_iso : (extend_tcomp_F).map_cocone (cocone_at ⊤) ≅ new' :=
begin
  ext, swap,
  { exact category_theory.eq_to_iso (dif_neg (not_lt_of_le (le_refl k))) },
  { dsimp [extend_tcomp_F],
    have : ¬((⊤ : below_top k).val < k), from not_lt_of_le (le_refl k),
    simp [this],
    dsimp [full_subcategory_inclusion],
    have : j.val.val < k, from j.property,
    simp [this],
    rw new'_app,
    refl }
end

-- Assumptions needed to guarantee that the new functor is still a
-- transfinite composition.
parameters (hsucc : ∀ j (hjk : is_succ j k), I (f j hjk.lt))
parameters (hlimit : is_limit k → limits.is_colimit new)
include hsucc hlimit

-- Using the above identifications, we conclude that the extended
-- functor is smooth in the limit case.
lemma extend_tcomp_F_smooth (hk : is_limit k) : smooth_at extend_tcomp_F ⊤ :=
⟨(is_colimit_of_iso (eq_to_iso extend_tcomp_F_extends_prev) (hlimit hk)).of_iso_colimit
  extend_tcomp_F_cone_iso.symm⟩

def extend_tcomp : transfinite_composition I (below_top k) :=
{ F := extend_tcomp_F,
  succ := λ p p' spp', let f := f in begin
    dunfold extend_tcomp_F,
    have hp : p.val < k, from lt_of_lt_of_le spp'.lt p'.property,
    by_cases hp' : p'.val < k,
    { simp [hp, hp', I_change_hom I], dsimp [prev_F], simp [I_change_hom' I],
      apply (Z p'.val hp').succ,
      rwa is_succ_iff at ⊢ spp' },
    { have : p'.val = k, from (eq_or_lt_of_le p'.property).resolve_right hp',
      have : I (f p.val hp), by apply hsucc; rwa [is_succ_iff, this] at spp',
      simpa [hp, hp', I_change_hom I] using this }
  end,
  limit := λ p plim,
  let extend_tcomp_F := extend_tcomp_F,
      extend_tcomp_F_smooth := extend_tcomp_F_smooth in begin
    by_cases hp : p.val < k,    -- TODO: use some other cases thing to get equality, and above
    { apply (smooth_at_iff_restriction_smooth_at (below_initial_seg (le_of_lt hp))
        extend_tcomp_F (⊤ : below_top p.val)).mpr,
      dsimp [restriction],
      erw extend_tcomp_F_extends,
      apply (Z _ _).limit,
      rwa is_limit_iff at ⊢ plim },
    { have hp : p.val = k, from (eq_or_lt_of_le p.property).resolve_right hp,
      rw [is_limit_iff, hp] at plim,
      have : p = (⊤ : below_top k), from subtype.eq hp, rw this,
      exact extend_tcomp_F_smooth plim }
  end }

end extension

#exit

parameters [limits.has_colimits C]
parameters {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]

section induction
-- Construction of each stage of a transfinite composition: bot, succ, limit.

section bot
-- To start, the required data is just an object X
parameters (X : C)

/-- A transfinite composition of "length zero". It consists of a
  single object, X. The conditions on successor and limit steps are
  vacuously satisfied. -/
def build_tcomp_bot : transfinite_composition I (below_top (bot : γ)) :=
{ F := (const _).obj X,
  succ := begin
    intros i j h,
    refine absurd (lt_of_lt_of_le h.lt _) (not_lt_bot _),
    change j.val ≤ _,
    convert j.property,
    rw ←is_bot_iff
  end,
  limit := begin
    intros j h,
    refine absurd j.property (not_le_of_lt _),
    convert h.bot_lt,
    symmetry,
    rw ←is_bot_iff
  end }

/-- The base case is vacuously consistent with previous stages,
  because there are none. TODO: Determine what form is most convenient
  at the use site -/
lemma build_tcomp_bot_consistent : true := trivial

end bot

-- In the remaining two cases (succ and build),
-- * k is the stage we're constructing
-- * Z encodes the choices of all the earlier segments
-- * hZ is the condition that these were compatible

parameters {k : γ} (Z : Π (i < k), transfinite_composition I (below_top i))
parameters (hZ : ∀ i i' (hik : i < k) (hi'k : i' < k) (hii' : i < i'),
  embed (le_of_lt hii') ⋙ (Z i' hi'k).F = (Z i hik).F)

-- We can include the case i = i' for free
lemma hZ' : ∀ i i' (hik : i < k) (hi'k : i' < k) (hii' : i ≤ i'),
  embed hii' ⋙ (Z i' hi'k).F = (Z i hik).F :=
sorry

section succ
-- The successor case: Suppose k is the successor of another element j.
parameters {j : γ} (hjk : is_succ j k)

-- To extend the construction, we should give a morphism from the end
-- of the previous stage which belongs to I.
parameters {Y : C} (f : (Z j hjk.lt).F.obj ⊤ ⟶ Y) (hf : I f)

-- TODO: is this the best way to make a short name for ⟨p.1, hjk.le_of_lt_succ hp⟩

-- TODO: This below is unused
@[reducible] private def restriction {p : below_top k} (hp : p.1 < k) : below_top j :=
⟨p.1, hjk.le_of_lt_succ hp⟩

local notation `restr` hp:1000 := (⟨subtype.val _, hjk.le_of_lt_succ hp⟩ : below_top _)

include hf

-- First build the new underlying functor
def build_tcomp_succ_F : below_top k ⥤ C :=
  { obj := λ p, if hp : p.val < k then (Z j hjk.lt).F.obj (restr hp) else Y,
    map := λ p p' hpp',
      if hp' : p'.val < k then
        have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
        change_hom ((Z j hjk.lt).F.obj (restr hp)) ((Z j hjk.lt).F.obj (restr hp'))
          (by simp [hp]) (by simp [hp'])
        ((Z j hjk.lt).F.map hpp')
      else if hp : p.val < k then
        change_hom ((Z j hjk.lt).F.obj (restr hp)) Y
          (by simp [hp]) (by simp [hp'])
        ((Z j hjk.lt).F.map ⟨⟨lattice.le_top⟩⟩ ≫ f)
      else
        change_hom Y Y (by simp [hp]) (by simp [hp']) (𝟙 Y),
    map_id' := λ p, begin
      split_ifs;
      { dsimp [change_hom],
        try { erw (Z j _).F.map_id },
        simp }
    end,
    map_comp' := λ p p' p'' hpp' hp'p'', begin
      by_cases hp'' : p''.val < k,
      { have hp' : p'.val < k, from lt_of_le_of_lt hp'p''.down.down hp'',
        have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
        simp [hp, hp', hp''],
        erw (Z j hjk.lt).F.map_comp  
          (show restr hp ⟶ restr hp', from hpp')
          (show restr hp' ⟶ restr hp'', from hp'p''),
        simp },
      by_cases hp' : p'.val < k,
      { have hp : p.val < k, from lt_of_le_of_lt hpp'.down.down hp',
        simp [hp, hp', hp''],
        erw (Z j hjk.lt).F.map_comp  
          (show restr hp ⟶ restr hp', from hpp')
          ⟨⟨lattice.le_top⟩⟩,
        simp },
      by_cases hp : p.val < k; { simp [hp, hp', hp'', change_hom] }
    end }

lemma build_tcomp_succ_F_extends_j : embed hjk.le ⋙ build_tcomp_succ_F = (Z j hjk.lt).F :=
begin
  dunfold build_tcomp_succ_F,
  fapply category_theory.functor.ext,
  { intro p,
    have hp : ((embed hjk.le).obj p).val < k, from lt_of_le_of_lt p.property hjk.lt,
    simp [hp],
    cases p, refl },
  { intros p p' hpp',
    have hp : ((embed hjk.le).obj p).val < k, from lt_of_le_of_lt p.property hjk.lt,
    have hp' : ((embed hjk.le).obj p').val < k, from lt_of_le_of_lt p'.property hjk.lt,
    dsimp, simp [hp, hp'],
    cases p, cases p', congr }
end

/-- A transfinite composition formed by extending the previous one by
  a single morphism, f. -/
def build_tcomp_succ : transfinite_composition I (below_top k) :=
{ F := build_tcomp_succ_F,
  succ := λ p p' spp', begin
    dunfold build_tcomp_succ_F,
    have hp : p.val < k, from lt_of_lt_of_le spp'.lt p'.property,
    by_cases hp' : p'.val < k,
    { simp [hp, hp', -change_hom, I_change_hom I],
      refine (Z j hjk.lt).succ (restr hp) (restr hp') _,
      -- Need to know that is_succ (restr hp) (restr hp'), still.
      sorry },
    { simp [hp, hp', -change_hom, I_change_hom I],
      have : p.val = j, from sorry,
      -- ^ p'.val is k, and we have is_succ j k and is_succ p p'.
      subst this,
      convert hf,
      convert category.id_comp _ _,
      apply (Z _ _).F.map_id }
  end,
  limit := λ p hp, begin
    have hp : p.val < k, from sorry, -- it's a limit ordinal, not successor
    have : p = (below_initial_seg hjk.le) (restr hp), by cases p; refl,
    rw this,
    rw smooth_at_iff_restriction_smooth_at (below_initial_seg hjk.le),
    dsimp [restriction],
    erw build_tcomp_succ_F_extends_j,
    apply (Z j _).limit,
    sorry -- it's still a limit ordinal
  end }

lemma build_tcomp_succ_extends (i) (hik : i < k) :
  embed (le_of_lt hik) ⋙ build_tcomp_succ.F = (Z i hik).F :=
have bt : _ := build_tcomp_succ_F_extends_j,
have _ := hZ' i j hik hjk.lt (hjk.le_of_lt_succ hik),
by rw [←this, ←bt]; refl

end succ

section limit
-- The limit case: k is a limit step.
parameters (hk : is_limit k)

-- Maybe we could have made this more uniform? Always ask for a new
-- object plus compatible maps from the ends of each previous
-- composition.

include hZ
def build_tcomp_limit_diagram : {i // i < k} ⥤ C :=
{ obj := λ p, (Z p.val p.property).F.obj ⊤,
  map := λ p p' hpp',
    eq_to_hom (eq_obj (hZ' p.val p'.val p.property p'.property hpp'.down.down).symm _) ≫
    (Z p'.val p'.property).F.map hpp',
  map_id' := λ p, by erw (Z _ _).F.map_id; simp; refl,
  map_comp' := λ p p' p'' hpp' hp'p'', let hZ' := hZ' in begin
    rw eq_hom (hZ' p'.val p''.val p'.property p''.property hp'p''.down.down).symm
      (show (⟨p.val, hpp'.down.down⟩ : below_top p'.val) ⟶ (⟨p'.val, le_refl _⟩ : below_top p'.val),
       from hpp'),
    dsimp,
    simp,
    congr,
    apply (Z p''.val p''.property).F.map_comp,
  end }

/-
def build_tcomp_limit_F : below_top k ⥤ C :=
{ obj := λ p,
    if hp : p.val < k then (Z p.val hp).F.obj ⊤ else
    limits.colimit _ }
-/

end limit

end induction

end build

#exit

variables (F : C ⥤ C) (α : functor.id C ⟹ F)

variables (γ : Type v) [lattice.order_top γ] [is_well_order γ (<)]

#check transfinite_composition

-- no! use an inductive Prop
def strict_image : morphism_class C :=
λ X Y f, Y = F.obj X ∧ f == α.app X

noncomputable def build_transfinite_composition (X : C) :
  Σ' (c : transfinite_composition (strict_image F α) γ), c.F.obj bot = X :=
begin
  suffices : Π (i : γ), Σ' (c : transfinite_composition (strict_image F α) (below_top i)),
    c.F.obj bot = X,
  { have c' := this ⊤,
    refine ⟨⟨to_below_top.comp c'.fst.F, _, _⟩, _⟩,
    { intros i j h, apply c'.fst.succ, rwa is_succ_iff },
    { intros j h,
      have := c'.fst.limit (to_below_top.obj j) (by rwa is_limit_iff),
      dsimp [smooth_at] at ⊢ this,
      -- This is a mess--we need to show that the transported diagram is still a colimit
      sorry },
    { convert c'.snd using 1,
      change c'.fst.F.obj _ = _,
      congr,
      rw is_bot_iff,
      refl } },

  refine crec (is_well_order.wf (<))
    (λ i i hii' p p', embed (le_of_lt hii') ⋙ p'.1.F = p.1.F) _,
  rintros j ⟨Z, hZ⟩,

  rcases is_bot_or_succ_or_limit j with ⟨_,rfl⟩|⟨i,_,hij⟩|⟨_,hj⟩,

  { refine ⟨⟨⟨(category_theory.functor.const _).obj X, _, _⟩, _⟩, _⟩,
    { intros i j h,
      refine absurd (lt_of_lt_of_le h.lt _) (not_lt_bot _),
      change j.val ≤ _,
      convert j.property,
      rw ←is_bot_iff },
    { intros j h,
      refine absurd j.property (not_le_of_lt _),
      convert h.bot_lt,
      symmetry,
      rw ←is_bot_iff },
    { refl },
    { exact λ j h, absurd h (not_lt_bot _) } },

  { refine ⟨⟨⟨_, _, _⟩, _⟩, _⟩,
    -- Should do some preliminary constructions first.
    -- Extending a functor from `below_top j` to `below_top j'` where `is_succ j j'`, etc.
},
end

end
end category_theory.transfinite

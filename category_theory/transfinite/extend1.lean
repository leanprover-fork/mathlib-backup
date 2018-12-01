import category_theory.transfinite.misc

noncomputable theory
local attribute [instance] classical.dec

universes u v

namespace category_theory.transfinite
namespace extend1
section

open category_theory category_theory.functor

-- General parameters for constructing a transfinite composition
parameters {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
parameters {I : morphism_class C}
parameters {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]

-- Parameters describing the previous stages
-- * k is the stage we're constructing
-- * Z encodes the choices of all the earlier segments
-- * hZ is the condition that these were compatible

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

lemma extend_tcomp_F_extends_prev_F :
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

lemma extend_tcomp_F_top : extend_tcomp_F.obj ⊤ = new.X :=
begin
  dunfold extend_tcomp_F,
  have : ¬((⊤ : below_top k).val < k), from lt_irrefl _,
  simp [this], refl
end

-- Transport `new` to a cocone on the restriction of the extended
-- functor `extend_tcomp_F`, for use in verifying the limit stage
-- condition.
def new' : limits.cocone (full_subcategory_inclusion (λ p, p < ⊤) ⋙ extend_tcomp_F) :=
new.precompose (eq_to_hom extend_tcomp_F_extends_prev_F)

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
⟨(is_colimit_of_iso (eq_to_iso extend_tcomp_F_extends_prev_F) (hlimit hk)).of_iso_colimit
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

end
end extend1
end category_theory.transfinite

import category_theory.full_subcategory
import category_theory.limits.limits
import logic.crec
import set_theory.ordinal

universes u v

namespace category_theory.transfinite

open category_theory category_theory.limits

variables {C : Type u} [𝒞 : category.{u v} C]

section
variables {γ : Type v} [partial_order γ]

def below (j : γ) : Type v := {i // i < j}
instance (j : γ) : partial_order (below j) := by dunfold below; apply_instance

def cocone_at (j : γ) : cocone (full_subcategory_inclusion (λ i, i < j)) :=
{ X := j, ι := { app := λ i, ⟨⟨le_of_lt i.property⟩⟩ } }

include 𝒞

def smooth_at (F : γ ⥤ C) (j : γ) : Type (max u v) :=
is_colimit (F.map_cocone (cocone_at j))

end

section morphism_class
variables (C)
include 𝒞
def morphism_class : Type (max u v) := Π ⦃X Y : C⦄, set (X ⟶ Y)
end morphism_class

variables (I : morphism_class C)

variables {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]

noncomputable def bot : γ :=
well_founded.min (is_well_order.wf (<)) set.univ
  (set.ne_empty_of_mem (show ⊤ ∈ set.univ, by trivial))

lemma bot_le (i : γ) : bot ≤ i :=
sorry

noncomputable def ix {o : ordinal} (ho : o < ordinal.type ((<) : γ → γ → Prop)) : γ :=
o.enum _ ho

def succ_hom {o : ordinal} (ho : o.succ < ordinal.type ((<) : γ → γ → Prop)) :
  ix (lt_trans o.lt_succ_self ho) ⟶ ix ho :=
ulift.up $ plift.up $ le_of_lt $ (ordinal.enum_lt _ ho).mpr o.lt_succ_self

variables (γ)
include 𝒞

structure transfinite_composition :=
(F : γ ⥤ C)
(succ : ∀ (o : ordinal) (ho : o.succ < ordinal.type _), I (F.map (succ_hom ho)))
(limit : ∀ (o : ordinal) ho, o.is_limit → smooth_at F (ordinal.enum (<) o ho))

variables {I γ}

noncomputable def transfinite_composition.composition
  (c : transfinite_composition.{u v} I γ) : c.F.obj bot ⟶ c.F.obj ⊤ :=
c.F.map ⟨⟨lattice.le_top⟩⟩

section lp

variables {C}

def lp {a b x y : C} (f : a ⟶ b) (g : x ⟶ y) : Prop :=
∀ (h : a ⟶ x) (k : b ⟶ y), h ≫ g = f ≫ k → ∃ l : b ⟶ x, f ≫ l = h ∧ l ≫ g = k

def llp {x y : C} (g : x ⟶ y) : morphism_class C := λ a b, {f | lp f g}

theorem llp_closed_under_transfinite_composition {x y : C} (g : x ⟶ y)
  (c : transfinite_composition (llp g) γ) : lp c.composition g :=
begin
  intros h k S,
  suffices : Π i, Σ' li : c.F.obj i ⟶ x,
    c.F.map ⟨⟨bot_le i⟩⟩ ≫ li = h ∧ li ≫ g = c.F.map ⟨⟨lattice.le_top⟩⟩ ≫ k,
  { rcases this ⊤ with ⟨l, L⟩,
    refine ⟨l, _⟩,
    convert ←L using 2,
    convert category.id_comp _ _,
    apply c.F.map_id },
  refine crec (is_well_order.wf ((<) : γ → γ → Prop))
    (λ i i' hii' p p', c.F.map ⟨⟨le_of_lt hii'⟩⟩ ≫ p'.1 = p.1) _,
  rintros j ⟨l, hl⟩,

  -- The inductive consistency hypothesis only applies for i < i',
  -- but also holds automatically for i = i'.
  have hl' : ∀ i i' (hij : i < j) (hi'j : i' < j) (hii' : i ≤ i'),
    c.F.map ⟨⟨hii'⟩⟩ ≫ (l i' hi'j).fst = (l i hij).fst,
  { intros,
    cases eq_or_lt_of_le hii' with hii' hii',
    { subst hii', convert category.id_comp _ _, apply c.F.map_id },
    { exact hl i i' hij hi'j hii' } },

  apply classical.indefinite_description,
  rcases (ordinal.typein (<) j).zero_or_succ_or_limit with H|⟨o, H⟩|H,

  -- Base case
  { have : j = bot, from sorry,
    subst this,
    fsplit,
    { refine ⟨h, _, S⟩,
      convert category.id_comp _ _,
      apply c.F.map_id },
    { exact λ i ria, absurd ria (not_lt_of_le (bot_le i)) } },

  -- Successor case
  { have os : o.succ < ordinal.type ((<) : γ → γ → Prop),
      by rw ←H; apply ordinal.typein_lt_type,
    have : j = ix os,
    { convert (ordinal.enum_typein _ _).symm,
      { exact H.symm },
      { apply ordinal.typein_lt_type } },
    subst this,
    -- We already constructed a lift up to `ix o`, and need to extend to `ix o.succ`.
    rcases classical.indefinite_description _
      (c.succ o os (l (ix (lt_trans o.lt_succ_self os)) _).1 (c.F.map ⟨⟨lattice.le_top⟩⟩ ≫ k) _) with ⟨l', hl'₁, hl'₂⟩,
    fsplit,
    { refine ⟨l', _, hl'₂⟩,
      -- New top triangle commutes
      { rw ←(l (ix (lt_trans o.lt_succ_self os)) _).snd.1,
        rw [←hl'₁, ←category.assoc, ←c.F.map_comp], refl } },
    -- New map extends the old ones
    { intros i ria,
      -- By hl'₁, we extended the immediately preceding map, but we need to check all
      -- XXX: Need to handle the cases i = o, i < o separately
      rw ←hl' i (ix (lt_trans o.lt_succ_self os)) ria _ _,
      conv { to_rhs, rw [←hl'₁, ←category.assoc, ←c.F.map_comp] },
      refl,
      sorry },
    { exact (ordinal.enum_lt _ _).mpr o.lt_succ_self },
    -- New bottom quadrilateral commutes
    { rw [←category.assoc, ←c.F.map_comp],
        apply (l (ix _) _).snd.2 } },

  -- Limit case
  { revert H,
    generalize H₁ : ordinal.typein has_lt.lt j = o,
    intro H,
    have ho : o < ordinal.type ((<) : γ → γ → Prop),
      by rw ←H₁; apply ordinal.typein_lt_type,
    have : j = ix ho,
    { convert (ordinal.enum_typein _ _).symm,
      { exact H₁.symm },
      { apply ordinal.typein_lt_type } },
    subst this,
    -- Extend to the limit by gluing all the maps `l i` for `i < j`
    let t : cocone (full_subcategory_inclusion (λ i, i < ix ho) ⋙ c.F) :=
    { X := x, ι := { app := λ i, (l i.1 i.2).1, naturality' := begin
        rintros i i' ⟨⟨hii'⟩⟩,
        convert hl' i.1 i'.1 i.2 _ _,
        apply category.comp_id
      end } },
    let l' := (c.limit _ ho H).desc t,
    refine ⟨⟨l', _, _⟩, _⟩,
    -- New top triangle commutes
    { have : bot < ix ho, from sorry,
      rw ←(l bot this).snd.1,
      convert (c.limit _ ho H).fac t ⟨bot, _⟩,
      { convert category.id_comp _ _,
        apply c.F.map_id } },
    -- New bottom quadrilateral commutes
    { apply (c.limit _ ho H).hom_ext,
      rintro ⟨i, io⟩,
      rw [←category.assoc, ←category.assoc],
      convert (l i io).snd.2,
      { apply (c.limit _ ho H).fac },
      { erw ←c.F.map_comp, refl } },
    -- New map extends the old ones
    { exact λ i ria, (c.limit _ ho H).fac t ⟨i, ria⟩ } }
end

end lp

end category_theory.transfinite

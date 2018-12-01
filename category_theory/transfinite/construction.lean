import category_theory.transfinite.extend2

noncomputable theory

local attribute [instance] classical.dec

open category_theory category_theory.functor

universes u v

namespace category_theory.transfinite
section

parameters {C : Type u} [𝒞 : category.{u v} C] [limits.has_colimits C]
include 𝒞

parameters {I : morphism_class C}

parameters {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]


variables (F : C ⥤ C) (α : functor.id C ⟹ F)


-- no! use an inductive Prop
def strict_image : morphism_class C :=
λ X Y f, Y = F.obj X ∧ f == α.app X

def strict_image_intro {X : C} : strict_image F α (α.app X) := ⟨rfl, heq.rfl⟩

noncomputable def build_transfinite_composition (X : C) :
  Σ' (c : transfinite_composition (strict_image F α) γ), c.F.obj bot = X :=
begin
  suffices : Π (i : γ), Σ' (c : transfinite_composition (strict_image F α) (below_top i)),
    i = bot → c.F.obj bot = X,
  { have c' := this ⊤,
    refine ⟨⟨to_below_top.comp c'.fst.F, _, _⟩, _⟩,
    { intros i j h, apply c'.fst.succ, rwa is_succ_iff },
    { intros j h,
      have := c'.fst.limit (to_below_top.obj j) (by rwa is_limit_iff),
      dsimp [smooth_at] at ⊢ this,
      -- This is a mess--we need to show that the transported diagram is still a colimit
      sorry },
    { sorry -- Instead, use compatibility with earlier stages... this all needs reorg
      -- For that matter, we should be able to use crec_def and avoid carrying this
      -- condition at all.
/-
      convert c'.snd _ using 1,
      change c'.fst.F.obj _ = _,
      congr,
      rw is_bot_iff,
      refl -/ } },

  refine crec (is_well_order.wf (<))
    (λ i i hii' p p', p.1.F = embed (le_of_lt hii') ⋙ p'.1.F) _,
  rintros j ⟨Z, hZ⟩,

  rcases is_bot_or_succ_or_limit j with ⟨_,rfl⟩|⟨i,_,hij⟩|⟨_,hj⟩,

  { refine ⟨⟨_, _⟩, _⟩,
    { exact extend2.extend_tcomp_bot (λ i hi, (Z i hi).1) hZ rfl X },
    { intro, apply extend2.extend_tcomp_bot_bot },
    { apply extend1.extend_tcomp_F_extends } },

  { refine ⟨⟨_, _⟩, _⟩,
    { refine extend2.extend_tcomp_succ (λ i hi, (Z i hi).1) hZ hij (α.app _) _,
      apply strict_image_intro },
    { intro hj', subst j, exact absurd hij not_is_succ_bot },
    { apply extend1.extend_tcomp_F_extends } },

  { refine ⟨⟨_, _⟩, _⟩,
    { exact extend2.extend_tcomp_limit (λ i hi, (Z i hi).1) hZ hj },
    { intro hj', subst j, exact absurd hj not_is_limit_bot },
    { apply extend1.extend_tcomp_F_extends } }
end

end
end category_theory.transfinite

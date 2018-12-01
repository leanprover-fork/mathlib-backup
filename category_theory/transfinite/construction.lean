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
  have ci : Π (i : γ), Σ' (c : transfinite_composition (strict_image F α) (below_top i)),
    c.F.obj bot = X,
  { refine crec (is_well_order.wf (<))
      (λ i i hii' c c', c.1.F = embed (le_of_lt hii') ⋙ c'.1.F) _,
    rintros j ⟨Z, hZ⟩,
    let Z' := λ i hi, (Z i hi).1,
    rcases is_bot_or_succ_or_limit j with ⟨_,rfl⟩|⟨i,_,hij⟩|⟨_,hj⟩;
    [refine ⟨⟨extend2.extend_tcomp_bot Z' hZ rfl X, _⟩, _⟩,
     refine ⟨⟨extend2.extend_tcomp_succ Z' hZ hij (α.app _) (by apply strict_image_intro), _⟩, _⟩,
     refine ⟨⟨extend2.extend_tcomp_limit Z' hZ hj, _⟩, _⟩],
    all_goals { try { apply extend1.extend_tcomp_F_extends } },
    apply extend2.extend_tcomp_bot_bot,
    all_goals
    { have : bot < j, from sorry,
      have : (bot : below_top j) = (embed (le_of_lt this)).obj bot, from sorry,
      change (extend1.extend_tcomp_F _ _ _).obj _ = _,
      rw this,
      change (embed _ ⋙ extend1.extend_tcomp_F _ _ _).obj _ = _,
      rw ←extend1.extend_tcomp_F_extends,
      apply (Z bot _).snd } },

  -- TODO: Construct the new transfinite composition at a higher level
  refine ⟨⟨to_below_top.comp (ci ⊤).1.F, _, _⟩, _⟩,
  { intros i j h, apply (ci ⊤).1.succ, rwa is_succ_iff },
  { intros j h,
    have := (ci ⊤).1.limit (to_below_top.obj j) (by rwa is_limit_iff),
    dsimp [smooth_at] at ⊢ this,
    -- This is a mess--we need to show that the transported diagram is still a colimit
    sorry },
  { change (ci ⊤).1.F.obj _ = X,
    convert (ci ⊤).snd,
    rw is_bot_iff, refl }
end

end
end category_theory.transfinite

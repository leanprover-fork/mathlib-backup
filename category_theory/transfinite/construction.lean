import category_theory.transfinite.misc

noncomputable theory

local attribute [instance] classical.dec

open category_theory category_theory.functor

universes u v

namespace category_theory.transfinite
section

parameters {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

parameters {I : morphism_class C}

parameters {γ : Type v} [lattice.order_top γ] [is_well_order γ (<)]


variables (F : C ⥤ C) (α : functor.id C ⟹ F)


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

  all_goals { sorry },

/-
  { refine ⟨⟨⟨_, _, _⟩, _⟩, _⟩,
    -- Should do some preliminary constructions first.
    -- Extending a functor from `below_top j` to `below_top j'` where `is_succ j j'`, etc.
}, -/
end

end
end category_theory.transfinite

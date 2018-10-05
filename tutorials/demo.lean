import algebra.group
import data.set.basic
import analysis.real
import tactic.norm_num
import tactic.ring

-- Basic logical manipulations
example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
begin
  rintro ⟨hyp1, hyp2⟩,
  apply hyp1,
  left,
  assumption,
end

-- The same can be done automatically
example (P Q R : Prop) : ((P ∨ Q → R) ∧ P) → R :=
by finish

-- Basic naive set theory. Secretely exactly the same kind of reasonning
-- as in the previous example
example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext x,
  split,
  { rintro ⟨x_1, x_B | x_C⟩,
    { left,
      split,
      { assumption },
      { assumption } },
    { right,
      split,
      { assumption },
      { assumption } } },
  { rintro (⟨x_A, x_B⟩|⟨x_A, x_C⟩),
    { split,
      { assumption },
      { left,
        assumption } },
    { split,
      { assumption },
      { right,
        assumption } } }
end

-- It can also be mostly automated
example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
by ext ; split ; finish

-- And of course it's already there
example (X : Type) (A B C : set X) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
set.inter_distrib_left _ _ _

-- axiom of choice is no problem
example (X Y : Type) (f : X → Y) :
  (∀ y : Y, ∃ x : X, f(x) = y) ↔ (∃ g : Y → X, f ∘ g = id) :=
begin
  split,
  { intro hyp,
    choose g H using hyp,
    existsi g,
    ext y,
    exact H y },
  { rintros ⟨g, H⟩ y,
    existsi g y,
    exact congr_fun H y }
end

-- Some computation and basic algebraic structure
example (G H : Type) [group G] [group H] (f : G → H)
  (Hyp : ∀ a b : G, f (a*b) = f a * f b) : f 1 = 1 :=
begin
  have key := calc
   f 1 = f (1*1) : by simp
   ... = f 1 * f 1 : Hyp 1 1,
  exact mul_self_iff_eq_one.1 (eq.symm key)
end

-- Some proof by induction
example (u : ℕ → ℝ) (H : ∀ n, u (n+1) = 2*u n) (H' : u 0 > 0) :
  ∀ n, u n > 0 :=
begin
  intro n,
  induction n with n IH,
  { exact H' },
  { rw H,
    apply mul_pos,
    norm_num,
    exact IH }
end

-- With some automated computation in a commutative ring
example (α : Type) [comm_ring α] (a b : α) : (a+b)^3 = a^3 + b^3 + 3*a*b^2 + 3*a^2*b :=
by ring
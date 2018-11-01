import .limit ..bounded_linear_maps

open filter

variables {E : Type*} [normed_space ℝ E]
variables {F : Type*} [normed_space ℝ F]

/-
TODO(Jeremy): extend this to partial functions `f`? It is a pain in the neck: we want to say `f` is defined at `x`, and replace `f x` below by that value; and also use the monad to lift all the operations to partial values. Probably not worth it. In most cases, there will be an open neighborhood around x where s is defined, and we can just set the partial function to 0 elsewhere. 
-/

def has_derivative_at_within (f : E → F) (x : E) (s : set E) (f' : E → F) :=
is_bounded_linear_map f' ∧ 
  tendsto (λ x', ∥x' - x∥⁻¹ • (f x' - f x - f' (x' - x)))
    (at_within x s) (nhds 0)

def has_derivative_at (f : E → F) (x : E) (f' : E → F) [is_bounded_linear_map f'] :=
has_derivative_at_within f x set.univ f' 
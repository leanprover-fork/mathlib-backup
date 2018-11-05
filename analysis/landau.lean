import order.filter
import algebra.field
import analysis.topology.topological_space
import analysis.normed_space
import tactic.find
import linear_algebra
import analysis.bounded_linear_maps
open classical finset function filter
local attribute [instance] prop_decidable

noncomputable theory

variables {α β γ : Type}
variables [normed_space ℝ α] [normed_space ℝ β] [normed_space ℝ γ]

def littleo (F : set (set α)) (f : α → β) (e : α → γ) :=
   ∀ ε : ℝ, ε > 0 → F {x | ∥f x∥ ≤ ε * ∥e x∥}

lemma littleo0 (F : filter α) (e : α → γ) : littleo (sets F) (0 : α → β) e :=
begin
  intros ε ε_gt0, simp,
  apply univ_mem_sets',
  intros a, simp,
  apply mul_nonneg,
  {linarith},
  {apply norm_nonneg}
end

def mklittleo (F : set (set α)) (f : α → β) (e : α → γ) :=
  if littleo F f e then f else 0

notation `o[`f`]_(`F`) ` e := mklittleo F f e
notation `o_(`F`) ` e := mklittleo F _ e
notation f `=` g ` +o_(` F `) ` e := (f = g + o[f - g]_(F) e)

theorem eqoP (F : filter α) (f g : α → β) (e : α → γ) :
  (∃ h, f = g + o[h]_(sets F) e) ↔ f = g +o_(sets F) e :=
begin
  split, swap, { exact assume ofg, ⟨f - g, ofg⟩ },
  { rintro ⟨h, eq_h⟩,
    rw [mklittleo] at eq_h,
    by_cases h_littleo : littleo (sets F) h e,
    {rw [if_pos h_littleo] at eq_h, simp [eq_h, mklittleo, if_pos h_littleo]},
    {simp [if_neg h_littleo] at eq_h, simp [eq_h, if_pos littleo0]}
   }
end

/- 
notation fx `=` gx ` +o_(` binder ` ↗ ` F `) ` ex :=
  (fx = gx + o[λ x, fx - gx]_(F x) ex)

def is_differential (f : α → β) (x : α) (df : α → β) :=
   is_bounded_linear_map df ∧
   (∀ h, f (x + h) = f x + df h +o_(h ∈ sets (nhds 0)) h)
 -/
class is_differential (f : α → β) (x : α) (df : α → β)
   extends is_bounded_linear_map df :=
   (diff_eq : (λ h, f (x + h)) = (λ _, f x) + df +o_(sets (nhds 0)) id)

lemma is_differential.eq {f : α → β} {x : α} {df : α → β} :
  is_differential f x df → 
  ∀ h, f (x + h) = f x + df h + (o[λ h, f (x + h) - f x]_(sets (nhds 0)) id) h :=
sorry

theorem chain_rule (f : α → β) (g : β → γ) (x : α) (df : α → β) (dg : β → γ) :
  is_differential f x df → 
  is_differential g (f x) dg →
  is_differential (g ∘ f) x (dg ∘ df) :=
begin
  assume diff_f diff_g,
  split, { exact is_bounded_linear_map.comp diff_g.1 diff_f.1 },
  rw ←eqoP, existsi _,
  { ext y, simp, rw [diff_f.eq, add_assoc (f x), diff_g.eq],
    rw [diff_g.add], repeat {rw[add_assoc]}, congr' 2,
    sorry 
  }
   
  /- rw ←eqoP,
  conv {
      
  funext,
  change (λ (h : α), g (f (x + h))) = (λ (_x : α), (g ∘ f) x) + dg ∘ df + o[h]_((nhds 0).sets) id,
  
  }, -/
  -- {ext h, simp [show _, by have := congr_fun eqf h; dsimp at this; exact this], }
 -- {ext h, simp, have := congr_fun eqf h, dsimp at this, rw this, }
end
#check congr_fun
/-Let littleo_def (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall eps : R, 0 < eps -> \forall x \near F, `|[f x]| <= eps * `|[g x]|.
-/
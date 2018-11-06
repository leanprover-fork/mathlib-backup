import analysis.bounded_linear_maps
open classical filter

protected def filter.eventually {α : Type*} (p : α → Prop) (f : filter α) : Prop :=
{a | p a} ∈ f.sets

protected def filter.frequently {α : Type*} (p : α → Prop) (f : filter α) : Prop :=
{a | ¬ p a} ∉ f.sets

notation `∀ᶠ ` binders ` in ` f `, ` r:(scoped p, filter.eventually p f) := r

notation `∃ᶠ ` binders ` in ` f `, ` r:(scoped p, filter.frequently p f) := r

local attribute [instance, priority 0] prop_decidable

noncomputable theory

variables {α β γ : Type}
variables [normed_space ℝ α] [normed_space ℝ β] [normed_space ℝ γ]

section littleo
variables (F : filter α) (f g : α → β) (e : α → γ)

def littleo := ∀ ε : ℝ, ε > 0 → F.sets {x | ∥f x∥ ≤ ε * ∥e x∥}

lemma littleo0 : littleo F (0 : α → β) e :=
begin
  intros ε ε_gt0,
  suffices : F.sets {x : α | 0 ≤ ε * ∥e x∥}, by simp [this],
  apply univ_mem_sets',
  intros a, 
  exact mul_nonneg (by linarith) (norm_nonneg _)
end

def mklittleo := if littleo F f e then f else 0

notation `o[`f`]_(`F`) ` e := mklittleo F f e
notation `o_(`F`) ` e := mklittleo F _ e
notation f `=o_(` F `) ` e := (f = o[f]_(F) e)
notation f `=` g ` +o_(` F `) ` e := (f = g + o[f - g]_(F) e)

theorem addeqoP : (∃ h, f = g + o[h]_(F) e) ↔ f = g +o_(F) e :=
begin
  split, swap, { exact assume ofg, ⟨f - g, ofg⟩ },
  { rintro ⟨h, eq_h⟩,
    rw [mklittleo] at eq_h,
    by_cases h_littleo : littleo F h e ;
    simp [h_littleo] at eq_h ; simp [eq_h, mklittleo, h_littleo] }
end

theorem eqoP : (∃ h, f = o[h]_(F) e) ↔ (f =o_(F) e) :=
by simpa using addeqoP _ f 0 _

lemma littleoE : littleo F f e → mklittleo F f e = f :=
assume hf, by simp [mklittleo, hf]

lemma littleo_mklittleo : littleo F (mklittleo F f g) g :=
by by_cases H : littleo F f g; simp [mklittleo, H, littleo0]

lemma add_littleo (hf : f =o_(F) e) (hg : g =o_(F) e) : littleo F (f + g) e :=
sorry

lemma littleo_eq_littleo : o[f]_(F) e =o_(F) e :=
by rw ←eqoP ; existsi _ ; refl

lemma littleo_add : littleo F ((o[f]_(F) e) + o[g]_(F) e) e :=
by apply add_littleo ; apply littleo_eq_littleo

lemma addo : (o[f]_(F) e) + (o[g]_(F) e) =o_(F) e :=
by rw littleoE _ _ _ (littleo_add _ _ _ _)

lemma addox (x : α) :
  (o[f]_(F) e) x + (o[g]_(F) e) x = 
  (o[(o[f]_(F) e) + o[g]_(F) e]_(F) e) x := sorry
--Proof. by move: x; rewrite - /(_ + _ =1 _) {1}addo. Qed.
 

/- 
notation fx `=` gx ` +o_(` binder ` ↗ ` F `) ` ex :=
  (fx = gx + o[λ x, fx - gx]_(F x) ex)
-/
end littleo

section bigO
variables (F : filter α)  (f g : α → β) 

/-- `bigO_def F f g` means f is O(g) near F, expressed in weird way-/
def bigO_def := ∀ᶠ k in at_top, ∀ᶠ x in F, ∥f x∥ ≤ k * ∥g x∥

/-- `bigO_ex_def F f g` means f is O(g) near F, expressed in the usual way-/
def bigO_ex_def := ∃ k > 0, ∀ᶠ x in F, ∥f x∥ ≤ k * ∥g x∥

lemma bigO_exP : bigO_def F f g ↔ bigO_ex_def F f g :=
begin
  split; intro h, 
  { unfold bigO_def filter.eventually at h,
    rw mem_at_top_sets at h,
    rcases h with ⟨k, Hk⟩,
    existsi (max k 1),
    split,
    { change 0 < max k 1,
      rw lt_max_iff, 
      right, norm_num},
    { simpa using Hk (max k 1) (le_max_left _ _) } },
  { rcases h with ⟨k, kpos, Hk⟩,
    unfold bigO_def filter.eventually,
    rw mem_at_top_sets,
    existsi k,
    intros k' kk',
    apply F.sets_of_superset Hk,
    intros a ineq,
    exact calc 
      ∥f a∥ ≤ k * ∥g a∥ : ineq
        ... ≤ _ : mul_le_mul_of_nonneg_right kk' (norm_nonneg _) },
end

/-- Zero function is O(anything) -/
lemma bigO0 : bigO_def F (0 : α → β) g := 
begin
  rw bigO_exP,
  existsi (1 : ℝ),
  split, 
  norm_num,
  simpa using univ_mem_sets,
end

/-- mkbigO F g f builds a O(g) near F from f -/
def mkbigO (F : filter α) (g : α → β) (f : α → β) :=
  if bigO_def F f g then f else 0

lemma bigO_mkbigO : bigO_def F (mkbigO F g f) g :=
by by_cases H : bigO_def F f g; simp [mkbigO, H, bigO0]

notation `O_(`F`) ` g := mkbigO F g
notation f `=` g ` +O_(` F `) ` h := (f = g + mkbigO F h (f - g))


/- lemma addO : [O_F e of f] + [O_F e of g] =O_F e.
Proof. by rewrite [RHS]bigOE. Qed.

lemma addOx :
  [O_F e of f] x + [O_F e of g] x =
  [O_F e of [O_F e of f] + [O_F e of g]] x.
Proof. by move: x; rewrite - /(_ + _ =1 _) {1}addO. Qed.
 -/
end bigO

section littlebigo
variables (F : filter α) (f g : α → β) (e : α → γ)
/- 
lemma eqoO : [o_F e of f] =O_F e.
Proof. by apply/eqOP; exists 0 => k kgt0; apply: littleoP. Qed.

lemma compOo_eqo (h : β →  γ) :
  [O_ (0 : β) id of g] \o [o_ (0 : α) id of f] =o_ (0 : α) id.
Proof.
apply/eqoP => _ /posnumP[e].
have /bigO_exP [_ /posnumP[k]] := bigOP [bigO of [O_ (0 : V') id of g]].
move=> /locallyP [_ /posnumP[d] hd].
have ekgt0 : e%:num / k%:num > 0 by [].
have /(_ _ ekgt0) := littleoP [littleo of [o_ (0 : U) id of f]].
apply: filter_app; near=> x => leoxekx; apply: ler_trans (hd _ _) _; last first.
  by rewrite -ler_pdivl_mull // mulrA [_^-1 * _]mulrC.
rewrite -ball_normE /= normmB subr0; apply: ler_lt_trans leoxekx _.
rewrite -ltr_pdivl_mull //; near: x; rewrite /= locally_simpl.
apply/locallyP; exists ((e%:num / k%:num) ^-1 * d%:num)=> // x.
by rewrite -ball_normE /= normmB subr0.
Grab Existential Variables. all: end_near. Qed.

lemma compOo_eqox (h : β →  γ) :
  ∀ x, [O_ (0 : β) id of g] ([o_ (0 : α) id of f] x) =o_(x \near 0 : α) x.
Proof. by move=> x; rewrite -[X in X = _]/((_ \o _) x) compOo_eqo. Qed. -/
end littlebigo

/-
def is_differential (f : α → β) (x : α) (df : α → β) :=
   is_bounded_linear_map df ∧
   (∀ h, f (x + h) = f x + df h +o_(h ∈ sets (nhds 0)) h)
 -/
class is_differential (f : α → β) (x : α) (df : α → β)
   extends is_bounded_linear_map df :=
   (diff_eq : (λ h, f (x + h)) = (λ _, f x) + df +o_(nhds 0) id)

lemma is_differential.eq {f : α → β} {x : α} {df : α → β} :
  is_differential f x df → 
  ∀ h, f (x + h) = f x + df h + (o[λ h, f (x + h) - f x]_(nhds 0) id) h :=
sorry

theorem chain_rule (f : α → β) (g : β → γ) (x : α) (df : α → β) (dg : β → γ) :
  is_differential f x df → 
  is_differential g (f x) dg →
  is_differential (g ∘ f) x (dg ∘ df) :=
begin
  assume diff_f diff_g,
  split, { exact is_bounded_linear_map.comp diff_g.1 diff_f.1 },
  rw ←addeqoP, existsi _,
  { ext y, simp, rw [diff_f.eq, add_assoc (f x), diff_g.eq],
    rw [diff_g.add], repeat {rw[add_assoc]}, congr' 2,
    sorry 
  },
   
  /- rw ←eqoP,
  conv {
      
  funext,
  change (λ (h : α), g (f (x + h))) = (λ (_x : α), (g ∘ f) x) + dg ∘ df + o[h]_((nhds 0).sets) id,
  
  }, -/
  -- {ext h, simp [show _, by have := congr_fun eqf h; dsimp at this; exact this], }
 -- {ext h, simp, have := congr_fun eqf h, dsimp at this, rw this, }
  sorry
end
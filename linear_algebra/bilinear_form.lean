/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import algebra.module

class bilinear_form_space (α : Type*) (β : Type*) [ring α] extends module α β :=
(bilin : β → β → α)
(fst_add_lin : ∀ (x y z : β), bilin (x + y) z = bilin x z + bilin y z)
(fst_mul_lin : ∀ (x y : β) (a : α), bilin (a • x) y = a * (bilin x y))
(snd_add_lin : ∀ (x y z : β), bilin x (y + z) = bilin x y + bilin x z)
(snd_mul_lin : ∀ (a : α) (x y : β), bilin x (a • y) = a * (bilin x y)) 

namespace bilinear_form_space

open bilinear_form_space

variables (α : Type*) [ring α] {β : Type*} [bilinear_form_space α β]

lemma zero_bilin (x : β) :
bilin α 0 x = 0 := by rw [←zero_smul, fst_mul_lin, ring.zero_mul]; exact 0

lemma bilin_zero (x : β) :
bilin α x 0 = 0 := by rw [←zero_smul, snd_mul_lin, ring.zero_mul]; exact 0

lemma bilin_neg_left (x y : β) : 
bilin α (-x) y = -(bilin α x y : α) := by rw [←neg_one_smul, fst_mul_lin, neg_one_mul]

lemma bilin_neg_right (x y : β) : 
bilin α x (-y) = -(bilin α x y) := by rw [←neg_one_smul, snd_mul_lin, neg_one_mul]

lemma bilin_sub_left (x y z : β) :
bilin α (x - y) z = bilin α x z - bilin α y z := by rw [sub_eq_add_neg, fst_add_lin, bilin_neg_left]; refl

lemma bilin_sub_right (x y z : β) :
bilin α x (y - z) = bilin α x y - bilin α x z := by rw [sub_eq_add_neg, snd_add_lin, bilin_neg_right]; refl

def is_ortho (x y : β) : Prop :=
bilin α x y = 0

lemma ortho_zero (x : β) : 
is_ortho α 0 x := zero_bilin α x 

theorem ortho_mul_left (γ : Type*) [domain γ] [bilinear_form_space γ β] (x y : β) (a : γ) (ha : a ≠ 0) : 
(is_ortho γ x y) ↔ (is_ortho γ (a • x) y) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [fst_mul_lin, H, ring.mul_zero] },

  { intros H,
    rw [fst_mul_lin, mul_eq_zero] at H,
    cases H, 
    { trivial }, 

    { exact H }}
end

theorem ortho_mul_right (γ : Type*) [domain γ] [bilinear_form_space γ β] (x y : β) (a : γ) (ha : a ≠ 0) : 
(is_ortho γ x y) ↔ (is_ortho γ x (a • y)) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [snd_mul_lin, H, ring.mul_zero] },

  { intros H,
    rw [snd_mul_lin, mul_eq_zero] at H,
    cases H, 
    { trivial }, 

    { exact H }} 
end

end bilinear_form_space

class reflx_bilinear_form_space (α : Type*) (β : Type*) [ring α] extends bilinear_form_space α β := 
(is_reflx : ∀ {x y : β}, bilin x y = 0 → bilin y x = 0)

namespace reflx_sesquilinear_form_space

open reflx_bilinear_form_space bilinear_form_space

lemma ortho_sym {α : Type*} {β : Type*} [ring α] [reflx_bilinear_form_space α β] (x y : β) : 
is_ortho α x y ↔ is_ortho α y x := ⟨λ H, is_reflx H, λ H, is_reflx H⟩

end reflx_sesquilinear_form_space

class sym_bilinear_form_space (α : Type*) (β : Type*) [ring α] extends bilinear_form_space α β := 
(is_invo_sym : ∀ (x y : β), bilin x y = bilin y x)

namespace sym_sesquilinear_form_space

open sym_bilinear_form_space bilinear_form_space

instance reflx_sesquilinear_form_space (α : Type*) (β : Type*) [ring α] [sym_bilinear_form_space α β] : 
reflx_bilinear_form_space α β := ⟨λ x y H, (eq.subst (is_invo_sym α x y) (H))⟩ 

def ortho_sym {α : Type*} {β : Type*} [ring α] [sym_bilinear_form_space α β] (x y : β) : 
is_ortho α x y ↔ is_ortho α y x := reflx_sesquilinear_form_space.ortho_sym x y

end sym_sesquilinear_form_space

class alt_bilinear_form_space (α : Type*) (β : Type*) [ring α] extends bilinear_form_space α β := 
(is_alt : ∀ (x : β), bilin x x = 0)

namespace alt_bilinear_form_space

open alt_bilinear_form_space bilinear_form_space

lemma bilin_skew_sym {α : Type*} {β : Type*} [ring α] [alt_bilinear_form_space α β] (x y : β) :
bilin α x y = - bilin α y x :=
begin
  have H : bilin α (x + y) (x + y) = 0,
  { exact is_alt α (x + y)},
  rw fst_add_lin at H,
  rw snd_add_lin at H,
  rw snd_add_lin at H,
  rw is_alt at H,
  rw is_alt at H,
  rw ring.zero_add at H,
  rw ring.add_zero at H,
  rw add_eq_zero_iff_eq_neg at H,
  exact H,
end

end alt_bilinear_form_space

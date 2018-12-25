/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow 
-/

import algebra.module ring_theory.ring_hom_isom_invo

open module ring ring_invo

class has_sesq (α : Type*) (β : Type*) [ring α] extends module α β := 
(sesq : β → β → α) 

class sesquilinear_form_space (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) extends module α β := 
(sesq : β → β → α)
(fst_add_lin : ∀ (x y z : β), sesq (x + y) z = sesq x z + sesq y z)
(fst_mul_lin : ∀ (x y : β) (a : α), sesq (a • x) y = a * (sesq x y))
(snd_add_lin : ∀ (x y z : β), sesq x (y + z) = sesq x y + sesq x z)
(snd_mul_antilin : ∀ (a : α) (x y : β), sesq x (a • y) = (invo Hi a) * (sesq x y))  

namespace sesquilinear_form_space

open sesquilinear_form_space has_sesq

variables {α : Type*} [ring α] {β : Type*} (Hi : ring_invo α) [sesquilinear_form_space α β Hi]

lemma zero_sesq (x : β) :
sesq Hi 0 x = 0 := by rw [←zero_smul, fst_mul_lin, ring.zero_mul]; exact 0

lemma sesq_zero (x : β) :
sesq Hi x 0 = 0 := by rw [←zero_smul, snd_mul_antilin, map_zero, ring.zero_mul]; exact 0

lemma sesq_neg_left (x y : β) : 
sesq Hi (-x) y = -(sesq Hi x y : α) := by rw [←neg_one_smul, fst_mul_lin, neg_one_mul]

lemma sesq_neg_right (x y : β) : 
sesq Hi x (-y) = -(sesq Hi x y) := by rw [←neg_one_smul, snd_mul_antilin, map_neg, ring_invo.map_one, neg_one_mul]

lemma sesq_sub_left (x y z : β) :
sesq Hi (x - y) z = sesq Hi x z - sesq Hi y z := by rw [sub_eq_add_neg, fst_add_lin, sesq_neg_left]; refl

lemma sesq_sub_right (x y z : β) :
sesq Hi x (y - z) = sesq Hi x y - sesq Hi x z := by rw [sub_eq_add_neg, snd_add_lin, sesq_neg_right]; refl

def is_ortho (x y : β) : Prop :=
sesq Hi x y = 0

lemma ortho_zero (x : β) : 
is_ortho Hi 0 x := zero_sesq Hi x 
  
theorem ortho_mul_left {γ : Type*} [domain γ] (Hi : ring_invo γ) [sesquilinear_form_space γ β Hi] (x y : β) (a : γ) (ha : a ≠ 0) : 
(is_ortho Hi x y) ↔ (is_ortho Hi (a • x) y) :=
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

theorem ortho_mul_right {γ : Type*} [domain γ] (Hi : ring_invo γ) [sesquilinear_form_space γ β Hi] (x y : β) (a : γ) (ha : a ≠ 0) : 
(is_ortho Hi x y) ↔ (is_ortho Hi x (a • y)) :=
begin
  dunfold is_ortho,
  split,
  { intros H,
    rw [snd_mul_antilin, H, ring.mul_zero] },

  { intros H,
    rw [snd_mul_antilin, mul_eq_zero] at H,
    cases H, 
    { rw map_zero_iff at H,
        trivial }, 

    { exact H }}
end

end sesquilinear_form_space

class reflx_sesquilinear_form_space (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) extends sesquilinear_form_space α β Hi := 
(is_reflx : ∀ {x y : β}, sesq x y = 0 → sesq y x = 0)

namespace reflx_sesquilinear_form_space

open reflx_sesquilinear_form_space sesquilinear_form_space

lemma ortho_sym {α : Type*} {β : Type*} [ring α] (Hi : ring_invo α) [reflx_sesquilinear_form_space α β Hi] (x y : β) : 
is_ortho Hi x y ↔ is_ortho Hi y x := ⟨λ H, is_reflx H, λ H, is_reflx H⟩

end reflx_sesquilinear_form_space
 
class sym_sesquilinear_form_space (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) extends sesquilinear_form_space α β Hi := 
(map_sesq : ∀ (x y : β), invo Hi (sesq y x) = sesq x y)

namespace sym_sesquilinear_form_space

open sym_sesquilinear_form_space sesquilinear_form_space

instance reflx_sesquilinear_form_space (α : Type*) (β : Type*) [ring α] (Hi : ring_invo α) [sym_sesquilinear_form_space α β Hi] : 
reflx_sesquilinear_form_space α β Hi :=
⟨λ x y H, (map_zero_iff Hi).mp (( eq_comm.mp (map_sesq Hi x y)) ▸ (H))⟩ 

def ortho_sym {α : Type*} {β : Type*} [ring α] (Hi : ring_invo α) [sym_sesquilinear_form_space α β Hi] (x y : β) : 
is_ortho Hi x y ↔ is_ortho Hi y x := reflx_sesquilinear_form_space.ortho_sym Hi x y

end sym_sesquilinear_form_space

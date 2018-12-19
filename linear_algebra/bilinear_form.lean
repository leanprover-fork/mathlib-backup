/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import algebra.module

class bilinear_form_space (R : Type*) (V : Type*) [ring R] extends module R V :=
(bilin_form : V → V → R)
(fst_add_lin : ∀ (x y z : V), bilin_form (x + y) z = bilin_form x z + bilin_form y z)
(fst_mul_lin : ∀ (x y : V) (a : R), bilin_form (a • x) y = a * (bilin_form x y))
(snd_add_lin : ∀ (x y z : V), bilin_form x (y + z) = bilin_form x y + bilin_form x z)
(snd_mul_lin : ∀ (a : R) (x y : V), bilin_form x (a • y) = a * (bilin_form x y)) 

namespace bilinear_form_space

open bilinear_form_space

variables (R : Type*) [ring R] {V : Type*} [bilinear_form_space R V]

instance bilinear_form_space.has_zero (F : Type*) (W : Type*) [ring F] [bilinear_form_space F W] : has_zero W := begin apply_instance end

lemma zero_bilin (x : V) :
bilin_form R 0 x = 0 := by rw [←zero_smul, fst_mul_lin, ring.zero_mul]; exact 0

lemma bilin_zero (x : V) :
bilin_form R x 0 = 0 := by rw [←zero_smul, snd_mul_lin, ring.zero_mul]; exact 0

lemma bilin_neg_left (x y : V) : 
bilin_form R (-x) y = -(bilin_form R x y : R) := by rw [←neg_one_smul, fst_mul_lin, neg_one_mul]

lemma bilin_neg_right (x y : V) : 
bilin_form R x (-y) = -(bilin_form R x y) := by rw [←neg_one_smul, snd_mul_lin, neg_one_mul]

lemma bilin_sub_left (x y z : V) :
bilin_form R (x - y) z = bilin_form R x z - bilin_form R y z := by rw [sub_eq_add_neg, fst_add_lin, bilin_neg_left]; refl

lemma bilin_sub_right (x y z : V) :
bilin_form R x (y - z) = bilin_form R x y - bilin_form R x z := by rw [sub_eq_add_neg, snd_add_lin, bilin_neg_right]; refl

def is_ortho (x y : V) : Prop :=
bilin_form R x y = 0

lemma ortho_zero (x : V) : 
is_ortho R 0 x := zero_bilin R x 

theorem ortho_mul_left (D : Type*) [domain D] [bilinear_form_space D V] (x y : V) (a : D) (ha : a ≠ 0) : 
(is_ortho D x y) ↔ (is_ortho D (a • x) y) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [fst_mul_lin, H, ring.mul_zero],

    intros H,
    rw [fst_mul_lin, mul_eq_zero] at H,
    cases H, 
        trivial, 

        exact H, 
end

theorem ortho_mul_right (D : Type*) [domain D] [bilinear_form_space D V] (x y : V) (a : D) (ha : a ≠ 0) : 
(is_ortho D x y) ↔ (is_ortho D x (a • y)) :=
begin
dunfold is_ortho,
split,
    intros H,
    rw [snd_mul_lin, H, ring.mul_zero],

    intros H,
    rw [snd_mul_lin, mul_eq_zero] at H,
    cases H, 
        trivial, 

        exact H, 
end

end bilinear_form_space

class reflx_bilinear_form_space (R : Type*) (V : Type*) [ring R] extends bilinear_form_space R V := 
(is_reflx : ∀ {x y : V}, bilin_form x y = 0 → bilin_form y x = 0)

namespace reflx_sesquilinear_form_space

open reflx_bilinear_form_space bilinear_form_space

lemma ortho_sym {R : Type*} {V : Type*} [ring R] [reflx_bilinear_form_space R V] (x y : V) : 
is_ortho R x y ↔ is_ortho R y x := ⟨λ H, is_reflx H, λ H, is_reflx H⟩

end reflx_sesquilinear_form_space

class sym_bilinear_form_space (R : Type*) (V : Type*) [ring R] extends bilinear_form_space R V := 
(is_invo_sym : ∀ (x y : V), bilin_form x y = bilin_form y x)

namespace sym_sesquilinear_form_space

open sym_bilinear_form_space bilinear_form_space

instance reflx_sesquilinear_form_space (R : Type*) (V : Type*) [ring R] [sym_bilinear_form_space R V] : 
reflx_bilinear_form_space R V := ⟨λ x y H, (eq.subst (is_invo_sym R x y) (H))⟩ 

def ortho_sym {R : Type*} {V : Type*} [ring R] [sym_bilinear_form_space R V] (x y : V) : 
is_ortho R x y ↔ is_ortho R y x := reflx_sesquilinear_form_space.ortho_sym x y

end sym_sesquilinear_form_space

class alt_bilinear_form_space (R : Type*) (V : Type*) [ring R] extends bilinear_form_space R V := 
(is_alt : ∀ (x : V), bilin_form x x = 0)

namespace alt_bilinear_form_space

open alt_bilinear_form_space bilinear_form_space

lemma bilin_skew_sym {R : Type*} {V : Type*} [ring R] [alt_bilinear_form_space R V] (x y : V) :
bilin_form R x y = - bilin_form R y x :=
begin
have H : bilin_form R (x + y) (x + y) = 0,
    exact is_alt R (x + y),
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

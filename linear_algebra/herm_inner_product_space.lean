/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Andreas Swerdlow
-/

import analysis.normed_space linear_algebra.sesquilinear_form data.complex.basic analysis.metric_space
 
open vector_space field set complex real

set_option class.instance_max_depth 16

lemma I_mul_self : I * I = -1 := complex.ext (mul_re I I) (mul_im I I)

lemma smul_two {α : Type*} {β : Type*} [ring β] [module β α] (a : α) :
a + a = 2 • a := by rw [←one_add_one_eq_two, add_smul, one_smul]

lemma re_add_mul_I (a b : ℝ) : (↑a + I * ↑b).re = a := 
by rw [add_re, of_real_re, mul_re, I_re, of_real_im, mul_zero, zero_mul, sub_zero, field.add_zero]

lemma im_add_mul_I (a b : ℝ) : (↑a + I * ↑b).im = b := 
by rw [add_im , of_real_im, mul_im, I_re, I_im, of_real_re, zero_mul, field.zero_add, field.one_mul, field.zero_add]

lemma ne_comm {α : Type*} {a b : α} : a ≠ b ↔ b ≠ a :=
⟨ λ H, iff_subst (@eq_comm _ a b) H, 
  λ H, iff_subst (@eq_comm _ b a) H⟩ 

lemma conj_eq_real (x : ℂ) : x.im = 0 ↔ conj(x) = x :=
begin
  split,
    intros H,
    have hn : -x.im = 0,
      rw neg_eq_zero,
      exact H,
    rw ←conj_im at hn,
    have hie : x.im = (conj(x)).im,
      simp [H, hn], 
    rw eq_comm,
    apply complex.ext (eq_comm.mp (conj_re x)) hie, 
    
    intros H,
    have hie : (conj(x)).im = x.im,
      rw H,
    simp at hie,
    rw ←add_left_inj (x.im) at hie,
    simp at hie,
    rw eq_comm at hie,
    exact iff.elim_left add_self_eq_zero hie,
end

lemma ne_zero_im_zero_imp_re_ne_zero {x : ℂ} : x ≠ 0 → x.im = 0 → x.re ≠ 0 :=
begin
  intros H1 H2,
  have Hx : x = ↑x.re,
    rw [←re_add_im x, H2, of_real_zero, zero_mul, field.add_zero, of_real_re],
  rw Hx at H1,
  exact of_real_ne_zero.mp H1,
end

lemma re_of_real {x : ℂ} : x.im = 0 → ↑(x.re) = x :=
begin
  intros H,
  rw [←re_add_im x, H, of_real_zero, zero_mul, field.add_zero, of_real_inj, of_real_re],
end

lemma of_real_pow (x : ℝ) (a : ℕ) : (↑(x^a) : ℂ) = (↑x)^a :=
begin
  induction a with d Hd,
    simp,
  rw [pow_succ, pow_succ],
  rw of_real_mul,
  rw Hd,
end

def conj.equiv : equiv ℂ ℂ := 
⟨conj, conj, begin dunfold function.left_inverse, intros, simp, end, begin dunfold function.right_inverse, dunfold function.left_inverse, intros, simp, end⟩

noncomputable def conj.ring_isom : ring_isom ℂ ℂ := 
⟨conj.equiv, conj_one, conj_mul, conj_add⟩ 

noncomputable def conj.ring_invo : ring_invo ℂ :=
⟨comm_ring.isom_to_anti_isom conj.ring_isom, begin apply conj_conj end⟩

class herm_inner_product_space (α : Type*) extends sym_sesquilinear_form_space ℂ α conj.ring_invo :=
(sesq_self_re_nonneg : ∀ (x : α), (sesq_form x x).re ≥ 0)
(sesq_self_eq_zero_iff : ∀ (x : α), sesq_form x x = 0 ↔ x = 0)

namespace herm_inner_product_space

variables {α : Type*} [herm_inner_product_space α]

open herm_inner_product_space ring_invo

noncomputable def inprod : α → α → ℂ := (to_sym_sesquilinear_form_space α).sesq_form  

local notation a ∘ b := inprod a b

noncomputable instance herm_to_module : module ℂ α := 
(herm_inner_product_space.to_sym_sesquilinear_form_space α).to_sesquilinear_form_space.to_module

lemma conj_inprod (x y : α) : conj (x ∘ y) = y ∘ x := sym_sesquilinear_form_space.map_sesq conj.ring_invo y x 

lemma inprod_self_re_nonneg (x : α) : (x ∘ x).re ≥ 0 := sesq_self_re_nonneg x   

lemma inprod_self_eq_zero (x : α) : (inprod x x) = 0 ↔ x = (0 : α) := sesq_self_eq_zero_iff x

@[simp] lemma inprod_add_left (x y z : α) : 
(x + y) ∘ z = x ∘ z + y ∘ z := sesquilinear_form_space.fst_add_lin _ _ _ _

@[simp] lemma inprod_add_right (x y z : α) : 
x ∘ (y + z) = x ∘ y + x ∘ z := sesquilinear_form_space.snd_add_lin _ _ _ _

@[simp] lemma inprod_smul_left (a : ℂ) (x y : α) :
(a • x) ∘ y = a * (x ∘ y) := sesquilinear_form_space.fst_mul_lin _ _ _ _

@[simp] lemma inprod_smul_right (a : ℂ) (x y : α) :
x ∘ (a • y) = conj(a) * (x ∘ y) := sesquilinear_form_space.snd_mul_antilin _ _ _ _

/-
lemma inprod_smul_add_smul_left : ∀ (a b : ℂ), ∀ (x y z : α), (a • x + b • y) ∘ z = a * (x ∘ z) + b * (y ∘ z) := sorry

theorem inprod_smul_add_smul_right : 
∀ (a b : ℂ), ∀ (x y z : α), x ∘ ((a • y) + (b • z)) = conj(a) * (x ∘ y) + conj(b) * (x ∘ z):=
begin
  intros, 
  rw [←conj_inprod, inprod_smul_add_smul_left, conj_add, conj_mul, conj_inprod, conj_mul, conj_inprod],
end
-/

open sym_sesquilinear_form_space sesquilinear_form_space

@[simp] lemma zero_inprod (x : α) :
0 ∘ x = 0 := zero_sesq _ x  

@[simp] lemma inprod_zero (x : α) :
x ∘ 0 = 0 := sesq_zero _ x 

@[simp] lemma inprod_neg_left (x y : α) : 
-x ∘ y = -(x ∘ y) := sesq_neg_left _ x y 

@[simp] lemma inprod_neg_right (x y : α) : 
x ∘ -y = -(x ∘ y) := sesq_neg_right _ x y   

noncomputable instance complex.add_comm_group : add_comm_group ℂ := ring.to_add_comm_group ℂ  

lemma inprod_sub_left (x y z : α) : 
(x - y) ∘ z = (x ∘ z) - (y ∘ z) := sesq_sub_left conj.ring_invo x y z

lemma inprod_sub_right (x y z : α) : 
x ∘ (y - z) = (x ∘ y) - (x ∘ z) := sesq_sub_right conj.ring_invo x y z

theorem inprod_self_im (x : α) :
(x ∘ x).im = 0 := 
begin
  intros,
  have H : conj(x ∘ x) = x ∘ x,
    rw conj_inprod,
  rw conj_eq_real (x ∘ x),
  exact H, 
end

lemma inprod_self_re_eq_zero (x : α) : 
(x ∘ x).re = 0 ↔ x = 0 := 
begin
  split; intros H,
    suffices : x ∘ x = 0,
      exact (inprod_self_eq_zero x).mp this,
    apply complex.ext,
      simpa,

      rw inprod_self_im,
      rw zero_im,

    rw H,
    simp,
end

lemma inprod_self_ne_zero_iff {x : α} : 
(x ∘ x) ≠ 0 ↔ x ≠ 0 :=
⟨ λ H, (iff_false_left H).mp (inprod_self_eq_zero x), 
  λ H, (iff_false_right H).mp (inprod_self_eq_zero x)⟩ 

lemma inprod_self_re_ne_zero_iff {x : α} : 
(x ∘ x).re ≠ 0 ↔ x ≠ 0 :=
begin
  split; intros H,
    have Ho : (x ∘ x) ≠ 0,
      intros Hx,
      rw Hx at H,
      rw zero_re at H,
      trivial,
    exact inprod_self_ne_zero_iff.mp Ho,

    have Ho : (x ∘ x) ≠ 0,
      exact inprod_self_ne_zero_iff.mpr H,
    exact ne_zero_im_zero_imp_re_ne_zero Ho (inprod_self_im x), 
end

lemma inprod_re (x y : α) : (x ∘ y).re = (y ∘ x).re := 
by rw [←conj_inprod, conj_re]

lemma inprod_im (x y : α) : (x ∘ y).im = -(y ∘ x).im :=
by rw [←conj_inprod, conj_im]

noncomputable def herm_norm (x : α) := sqrt((x ∘ x).re)

local notation |a|  := herm_norm(a) 

lemma mul_self_herm_norm (x : α) : 
|x| * |x| = (x ∘ x).re :=
begin
  dunfold herm_norm,
  rw mul_self_sqrt (inprod_self_re_nonneg x),
end --change uses of mul_self_sqrt to this

lemma herm_norm_sqr (x : α) : 
|x|^2 = (x ∘ x).re := by rw pow_two; exact mul_self_herm_norm x

open classical

--set_option pp.all true

theorem abs_inprod_le_mul_herm_norm (x y : α) :
abs((x ∘ y)) ≤ |x|*|y| := 
begin
  intros,
  have ho : y = 0 ∨ y ≠ 0,
    apply em,
  cases ho,
    rw ho,
    dunfold herm_norm,
    simp,

    have H : 0 ≤ |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| * |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| ,
      dunfold herm_norm, 
      apply mul_nonneg (sqrt_nonneg (((x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y) ∘ (x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y)).re)) (sqrt_nonneg (((x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y) ∘ (x - (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) • y)).re)), 
    rw sub_eq_add_neg at H,
    rw of_real_mul at H,
    unfold herm_norm at H,
    rw mul_self_sqrt (inprod_self_re_nonneg ((x + -((x ∘ y / (↑(sqrt ((y ∘ y).re)) * ↑(sqrt ((y ∘ y).re)))) • y)))) at H, 
    rw ←of_real_mul at H,
    rw of_real_inj.mpr (mul_self_sqrt (inprod_self_re_nonneg y)) at H, 
    suffices H : 0 ≤ (x ∘ x).re + ((x ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re + ((x ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re + (-((x ∘ y / ↑((y ∘ y).re)) • y) ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re)),
      have he : (-((x ∘ y / ↑((y ∘ y).re)) • y) ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re = -(x ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re,
        rw inprod_neg_right,
        rw inprod_neg_right,
        rw inprod_neg_left,
        rw inprod_smul_left,
        rw inprod_smul_right,
        rw inprod_smul_right,
        have hr : y ∘ y = ↑((y ∘ y).re),
          rw re_of_real (inprod_self_im y),
        rw conj_div,
        rw conj_of_real,
        rw ←hr,
        rw div_mul_cancel (conj(x ∘ y)) ((iff_false_right ho).mp (inprod_self_eq_zero y)),
        rw div_mul_eq_mul_div,
        rw div_mul_eq_mul_div,
        rw field.mul_comm,
        refl, 
      rw he at H,
      rw add_neg_self at H,
      rw field.add_zero at H,
      rw inprod_neg_right at H,
      rw inprod_smul_right at H,
      rw conj_div at H,
      rw conj_of_real at H,
      dunfold herm_norm,
      dunfold complex.abs, 
      rw ←sqrt_mul (inprod_self_re_nonneg x),
      rw sqrt_le (norm_sq_nonneg (x ∘ y)) (mul_nonneg (inprod_self_re_nonneg x) (inprod_self_re_nonneg y)), 
      rw ←sub_le_iff_le_add' at H,
      rw sub_eq_neg_add at H,
      rw field.add_zero at H,
      rw div_mul_eq_mul_div at H,
      rw neg_re at H,
      rw neg_le_neg_iff at H,
      rw field.mul_comm at H,
      rw mul_conj at H,
      rw ←of_real_div at H,
      rw of_real_re at H,
      rw div_le_iff (lt_of_le_of_ne (inprod_self_re_nonneg y) ((ne_comm).mp (ne_zero_im_zero_imp_re_ne_zero  (inprod_self_ne_zero_iff.mpr ho) (inprod_self_im y)))) at H,
      exact H,
    rw inprod_add_left at H,
    rw inprod_add_right at H,
    rw inprod_add_right at H,
    rw add_re at H,
    rw add_re at H,
    rw add_re at H,
    rw inprod_re (-((x ∘ y / ↑((y ∘ y).re)) • y)) x at H,
    rw field.add_assoc at H,
    exact H,
end

def herm_norm_eq_zero_iff (x : α) :
|x| = 0 ↔ x = 0 := 
begin
  dunfold herm_norm,
  rw sqrt_eq_zero (inprod_self_re_nonneg x),
  exact (inprod_self_re_eq_zero x),
end

theorem abs_inprod_eq_mul_herm_norm_iff (x y : α) : 
abs(x ∘ y) = |x|*|y| ↔ (∃ (a : ℂ), x = a • y) ∨ (∃ (a : ℂ), y = a • x) :=
begin
  dunfold herm_norm,
  dunfold complex.abs,
  rw ←sqrt_mul (inprod_self_re_nonneg x),
  rw sqrt_inj (norm_sq_nonneg _) (mul_nonneg (inprod_self_re_nonneg x) (inprod_self_re_nonneg y)),
    
  split; intros H,
    have ho : y = 0 ∨ y ≠ 0,
      apply em,
    cases ho,
      rw ho,
      apply or.intro_right,
      apply exists.intro (0 : ℂ),
      rw zero_smul,

      suffices : |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| * |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| = 0,
        have Ht : |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| = 0,
          exact eq_zero_of_mul_self_eq_zero this,
        rw herm_norm_eq_zero_iff at Ht,
        unfold herm_norm at Ht,
        rw sub_eq_zero at Ht,
        exact or.intro_left _ (exists.intro (x ∘ y / ↑(sqrt ((y ∘ y).re) * sqrt ((y ∘ y).re))) Ht),
      have He : |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| * |x - ((x ∘ y)/(↑( |y|*|y| ))) • y| = |x|*|x| - (abs(x ∘ y)^2)/ ( |y|*|y| ),
        rw sub_eq_add_neg,
        rw of_real_mul,
        dunfold herm_norm,
        rw mul_self_sqrt (inprod_self_re_nonneg ((x + -((x ∘ y / (↑(sqrt ((y ∘ y).re)) * ↑(sqrt ((y ∘ y).re)))) • y)))), 
        rw ←of_real_mul,
        rw of_real_inj.mpr (mul_self_sqrt (inprod_self_re_nonneg y)),
        repeat {rw inprod_add_left <|> rw inprod_add_right <|> rw inprod_smul_left <|> rw inprod_smul_right},
        rw add_re,
        rw add_re,
        rw ←conj_inprod x (-((x ∘ y / ↑((y ∘ y).re)) • y)),
        rw mul_self_sqrt (inprod_self_re_nonneg x),
        rw mul_self_sqrt (inprod_self_re_nonneg y),
        rw pow_two,
        rw mul_self_abs,
        have he : (-((x ∘ y / ↑((y ∘ y).re)) • y) ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re = -(x ∘ -((x ∘ y / ↑((y ∘ y).re)) • y)).re,
          rw inprod_neg_right,
          rw inprod_neg_right,
          rw inprod_neg_left,
          rw inprod_smul_left,
          rw inprod_smul_right,
          rw inprod_smul_right,
          have hr : y ∘ y = ↑((y ∘ y).re),
            rw re_of_real (inprod_self_im y),
          rw conj_div,
          rw conj_of_real,
          rw ←hr,
          rw div_mul_cancel (conj(x ∘ y)) ((iff_false_right ho).mp (inprod_self_eq_zero y)),
          rw div_mul_eq_mul_div,
          rw div_mul_eq_mul_div,
          rw field.mul_comm,
          refl,
        rw add_re, 
        rw he,
        rw re_of_real (inprod_self_im y),
        rw conj_re,
        rw field.add_assoc,
        rw add_neg_self,
        rw field.add_zero,
        rw ←neg_smul,
        rw inprod_smul_right,
        rw mul_re,
        rw conj_re,
        rw conj_im,
        rw neg_re,
        rw neg_im,
        rw neg_neg,
        rw sub_eq_add_neg,
        rw neg_mul_eq_neg_mul_symm,
        rw ←neg_add,
        rw div_eq_inv_mul,
        rw mul_re,
        rw mul_im,
        rw inv_re,
        rw inv_im,
        rw inprod_self_im,
        rw neg_zero,
        rw zero_div,
        rw zero_mul,
        rw zero_mul,
        rw sub_zero,
        rw field.add_zero,
        rw field.mul_assoc,
        rw field.mul_assoc,
        rw ←field.left_distrib,
        dunfold norm_sq,
        rw inprod_self_im,
        rw mul_zero,
        rw field.add_zero,
        rw ←mul_div_right_comm,
        rw mul_div_mul_left _ (inprod_self_re_ne_zero_iff.mpr ho) (inprod_self_re_ne_zero_iff.mpr ho),
        ring,  
      rw He,
      rw sub_eq_zero,
      rw eq_comm,
      rw div_eq_iff_mul_eq,
      rw pow_two,
      rw mul_self_abs,
      rw mul_self_herm_norm,
      rw mul_self_herm_norm,
      rw H,
        rw mul_self_herm_norm,
        exact inprod_self_re_ne_zero_iff.mpr ho,

    dunfold complex.norm_sq,    
    cases H; cases H with a Ha; 
    rw Ha;
    repeat {rw inprod_smul_left};
    rw inprod_smul_right;
    repeat {rw mul_re};
    repeat {rw mul_im};
    rw conj_im;
    rw conj_re;
    rw inprod_self_im;
    ring,
end

noncomputable def herm_dist (x y : α) : ℝ := |x - y|

open metric_space

noncomputable instance to_metric_space : 
metric_space α := 
{ dist := λ x y, |x - y|, 
  dist_self := 
    begin
      intros,
      unfold dist, 
      rw sub_self,
      rw herm_norm_eq_zero_iff,
    end,
  eq_of_dist_eq_zero :=
    begin
      unfold dist,
      dunfold herm_norm,
      intros x y H,
      rw sqrt_eq_zero (inprod_self_re_nonneg (x - y)) at H,
      rw ←zero_re at H,
      have H1 : (x - y) ∘ (x - y) = 0,
        exact complex.ext H (inprod_self_im (x - y)),
      rw inprod_self_eq_zero (x - y) at H1,
      exact sub_eq_zero.mp H1,
    end,
  dist_comm := 
    begin
      intros,
      unfold dist, 
      dunfold herm_norm,
      rw sqrt_inj (inprod_self_re_nonneg (x - y)) (inprod_self_re_nonneg (y - x)),
      rw ←neg_sub,
      rw inprod_neg_left,
      rw inprod_neg_right,
      rw neg_neg,
    end,
  dist_triangle := 
    begin 
      unfold dist,
      suffices : ∀ (x y : α), |x + y| ≤ |x| + |y|,
      intros,
      have H : x - z = (x - y) + (y - z),
        simp,
      rw H, 
      exact this (x - y) (y - z),
    
      intros,
      have H : |x + y|*|x + y| = ((x + y) ∘ (x + y)).re,
        dunfold herm_norm,
        rw mul_self_sqrt (inprod_self_re_nonneg (x + y)),
      rw inprod_add_left at H,
      rw inprod_add_right at H,
      rw inprod_add_right at H,
      rw ←conj_inprod x y at H,
      rw field.add_assoc at H,
      rw ←field.add_assoc (x ∘ y) at H,
      rw add_conj at H,
      rw add_re at H,
      rw add_re at H,
      rw of_real_re at H, 
      have hle : 2*(x ∘ y).re ≤ 2*abs(x ∘ y),
        exact (mul_le_mul_left (lt_trans zero_lt_one (begin exact two_gt_one, end))).mpr (re_le_abs (x ∘ y)),
      rw ←sub_zero (2 * abs (x ∘ y)) at hle,
      rw le_sub at hle,
      suffices Hle :  |x + y| * |x + y| ≤ (x ∘ x).re + (y ∘ y).re + 2 * abs (x ∘ y),
        have Hcs : 2*abs(x ∘ y) ≤ 2*|x|*|y|,
          rw field.mul_assoc,
          exact (mul_le_mul_left (lt_trans zero_lt_one (begin exact two_gt_one, end))).mpr (abs_inprod_le_mul_herm_norm x y),
        have hz : 2*abs(x ∘ y) ≥ 0,
          rw two_mul,
          have ha : abs(x ∘ y) ≥ 0,
            exact abs_nonneg (x ∘ y),
          exact le_add_of_le_of_nonneg ha ha,
        unfold herm_norm at Hcs,
        rw ←sub_zero (2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re)) at Hcs,
        rw le_sub at Hcs,
        have Hs : |x + y|*|x + y| ≤ 2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re) - 2 * abs (x ∘ y) + ((x ∘ x).re + (y ∘ y).re + 2 * abs (x ∘ y)),
          apply le_add_of_nonneg_of_le Hcs Hle,
        rw sub_eq_add_neg at Hs,
        rw field.add_comm (2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re)) at Hs, 
        rw field.add_assoc ((x ∘ x).re) at Hs,
        rw field.add_comm at Hs,
        rw field.add_assoc at Hs,
        rw field.add_assoc at Hs, 
        rw add_neg_cancel_left at Hs, 
        have Hs' : |x + y| * |x + y| ≤ (x ∘ x).re + ((y ∘ y).re + 2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re)),
          exact Hs,
        have He : (x ∘ x).re + ((y ∘ y).re + 2 * sqrt ((x ∘ x).re) * sqrt ((y ∘ y).re)) = (herm_norm(x) + herm_norm(y))*(herm_norm(x) + herm_norm(y)),
          dunfold herm_norm,
          rw field.right_distrib,
          rw field.left_distrib,
          rw field.left_distrib,
          rw ←sqrt_mul ((inprod_self_re_nonneg x)), 
          rw sqrt_mul_self ((inprod_self_re_nonneg x)),
          rw ←pow_two,
          rw sqr_sqrt (inprod_self_re_nonneg y),
          ring,  
        rw He at Hs',
        apply (mul_self_le_mul_self_iff (begin intros, exact sqrt_nonneg (((x + y) ∘ (x + y)).re), end) (add_nonneg (begin intros, exact sqrt_nonneg ((x ∘ x).re), end) (begin intros, exact sqrt_nonneg ((y ∘ y).re), end))).mpr Hs',    
      
      suffices : |x + y| * |x + y| + 0 ≤ (x ∘ x).re + (2 * (x ∘ y).re + (y ∘ y).re) + (2 * abs (x ∘ y) - 2 * (x ∘ y).re),
        simpa using this,
      apply add_le_add (le_of_eq H) hle,
    end}

@[simp] lemma herm_norm_smul (a : ℂ) (x : α) : 
|a • x| = abs(a)*|x| := 
begin 
  intros, 
  dunfold herm_norm, 
  rw inprod_smul_left,
  rw inprod_smul_right,
  rw ←field.mul_assoc,
  rw mul_conj,
  rw mul_re,
  rw of_real_im,
  rw zero_mul,
  rw sub_zero,
  rw sqrt_mul,
  refl,
  rw of_real_re,
  exact norm_sq_nonneg a, 
end

@[simp] lemma of_real_herm_norm_sqr (x : α) : 
↑( |x|^2 ) = x ∘ x :=
begin
  dunfold herm_norm,
  rw sqr_sqrt (inprod_self_re_nonneg x),
  rw re_of_real (inprod_self_im x),
end

@[simp] lemma of_real_herm_norm_mul_self (x : α) : 
↑( |x|*|x| ) = x ∘ x :=
begin
  dunfold herm_norm,
  rw mul_self_sqrt (inprod_self_re_nonneg x),
  rw re_of_real (inprod_self_im x),
end

noncomputable instance complex.metric_space : metric_space ℂ :=
{ dist := λ x y, abs(x - y),
  dist_self := by simp,
  eq_of_dist_eq_zero := assume x y H, sub_eq_zero.mp (complex.abs_eq_zero.mp H),
  dist_comm := begin intros, unfold dist, rw ←neg_sub, rw complex.abs_neg, end,
  dist_triangle := abs_sub_le}

noncomputable instance complex.normed_field : normed_field ℂ :=
{ norm := abs,
  dist_eq := by intros; refl, 
  norm_mul := abs_mul,}

noncomputable instance herm_inner_product_space.normed_space : 
normed_space ℂ α := 
{ norm := herm_norm,
  dist_eq := by intros; refl,
  norm_smul := herm_norm_smul}

instance normed_space.module {W : Type*} {F : Type*} [normed_field F] [normed_space F W] : module F W := (normed_space.to_vector_space W).to_module

@[simp] lemma herm_norm_zero : 
|(0 : α)| = 0 := @norm_zero α _

lemma norm_smul_I {W : Type*} [normed_space ℂ W] (x : W) :
∥I • x∥ = ∥x∥ :=
begin
  rw norm_smul,
  unfold norm,
  rw abs_I,
  rw field.one_mul, 
end

@[simp] lemma herm_norm_smul_I (x : α) :
|I • x| = |x| := norm_smul_I x 

lemma norm_ne_zero_iff_ne_zero {G : Type*} [normed_group G] {g : G} : 
∥g∥ ≠ 0 ↔ g ≠ 0 := 
⟨ λ H, (iff_false_left H).mp (norm_eq_zero g), 
  λ H, (iff_false_right H).mp (norm_eq_zero g)⟩ 

theorem parallelogram_law (x y : α) :
|x + y|^2 + |x - y|^2 = 2*|x|^2 + 2*|y|^2 :=
begin
  dunfold herm_norm,
  rw sqr_sqrt (inprod_self_re_nonneg (x + y)),
  rw sqr_sqrt (inprod_self_re_nonneg (x - y)),
  rw sqr_sqrt (inprod_self_re_nonneg x),
  rw sqr_sqrt (inprod_self_re_nonneg y),
  suffices : (x ∘ x).re + ((x ∘ x).re + ((y ∘ y).re + (y ∘ y).re)) = 2 * (x ∘ x).re + 2 * (y ∘ y).re,
    rw inprod_add_left,
    rw inprod_add_right,
    rw inprod_add_right,
    rw inprod_sub_left,
    rw inprod_sub_right,
    rw inprod_sub_right,
    rw add_re,
    rw add_re,
    rw sub_re,
    rw sub_re,
    rw sub_re,
    simpa,
  rw ←conj_inprod y,
  rw conj_re,
  ring,
end

lemma inprod_self_add (x y : α) :
(x + y) ∘ (x + y) = (x ∘ x) + (y ∘ y) + (x ∘ y) + (y ∘ x) :=
begin
  rw inprod_add_left,
  rw inprod_add_right,
  rw inprod_add_right,
  simpa [field.add_assoc, field.add_comm],
end

def is_normalised (x : α) := |x| = 1

noncomputable def normalise (x : α) := ↑|x|⁻¹ • x 

lemma normalise_normalises (x : α) (ho : x ≠ 0) : 
is_normalised (normalise x) :=
begin
  dunfold is_normalised,
  dunfold normalise,
  dunfold herm_norm,
  rw inprod_smul_left,
  rw inprod_smul_right,
  rw conj_of_real,
  rw mul_re,
  rw mul_re,
  rw of_real_im,
  rw zero_mul,
  rw zero_mul,
  rw sub_zero,
  rw sub_zero,
  rw of_real_re,
  rw ←sqrt_one,
  rw sqrt_inj (mul_nonneg (inv_nonneg.mpr (sqrt_nonneg (x ∘ x).re)) (mul_nonneg (inv_nonneg.mpr (sqrt_nonneg (x ∘ x).re)) (inprod_self_re_nonneg x))) (zero_le_one), 
  rw ←sqrt_inv,
  rw ←field.mul_assoc,
  rw mul_self_sqrt, --(inv_nonneg.mpr (inprod_self_re_nonneg x)),
  rw field.inv_mul_cancel, 
    exact (ne_zero_im_zero_imp_re_ne_zero (inprod_self_ne_zero_iff.mpr ho) (inprod_self_im x)),
    exact (inv_nonneg.mpr (inprod_self_re_nonneg x)),
end

def normalise_set :
set α → set α := image(λ x, ↑|x|⁻¹ • x)

lemma normalise_set_normalises 
(A : set α) (Ho : (0 : α) ∉ A) : 
∀ x ∈ normalise_set(A), is_normalised x :=
begin
  dunfold normalise_set,
  dunfold image, 
  intros,
  have Ha : ∃ (a : α), a ∈ A ∧ normalise a = x,
    rw mem_set_of_eq at H, 
    exact H,
  apply (exists.elim Ha),
  intros a Hl,
  rw ←Hl.right,
  have ho : a ≠ 0,
    intros h,
    rw h at Hl,
    exact Ho Hl.left,
  exact normalise_normalises a ho,
end

def herm_ortho (x y : α) : Prop := x ∘ y = 0 

notation a ⊥ b := herm_ortho a b 

def herm_ortho_sym (x y : α) :
(x ⊥ y) ↔ (y ⊥ x) := ortho_sym (conj.ring_invo) x y 

lemma ortho_refl_iff_zero (x : α) : 
(x ⊥ x) ↔ x = 0 := (inprod_self_eq_zero x)

def herm_ortho_mul_left (x y : α) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ ((a • x) ⊥ y) := ortho_mul_left (conj.ring_invo) x y a ha

def herm_ortho_mul_right (x y : α) (a : ℂ) (ha : a ≠ 0) : 
(x ⊥ y) ↔ (x ⊥ (a • y)) := ortho_mul_right (conj.ring_invo) x y a ha

theorem ortho_imp_not_lindep (x y : α) (hx : x ≠ 0) (hy : y ≠ 0) : 
(x ⊥ y) → ¬∃ (a : ℂ), (a ≠ 0) ∧ (x = a • y ∨ a • x = y) :=
begin
  intros H1,
  apply not_exists.mpr,
  intros a,
  intros H2,
  unfold herm_ortho at H1,
  cases H2 with ha H2,
  cases H2,  
    rw H2 at H1,
    rw inprod_smul_left at H1,
    rw mul_eq_zero at H1,
    cases H1,
      trivial, 

      exact hy (((inprod_self_eq_zero y)).mp H1),
    
    rw ←H2 at H1,
    rw inprod_smul_right at H1,
    rw mul_eq_zero at H1,
    cases H1,
      exact ha ((conj_eq_zero).mp H1),

      exact hx (((inprod_self_eq_zero x)).mp H1),
end

theorem pythag_iden (x y : α) (H : x ⊥ y) :
|x + y|^2 = |x|^2 + |y|^2 :=
begin
  dunfold herm_norm,
  rw sqr_sqrt (inprod_self_re_nonneg (x + y)),
  rw sqr_sqrt (inprod_self_re_nonneg x),
  rw sqr_sqrt (inprod_self_re_nonneg y),
  rw inprod_self_add,
  unfold herm_ortho at H,
  rw [←conj_inprod x y, H],
  rw conj_zero,
  rw field.add_zero,
  rw field.add_zero,
  rw add_re,
end

def is_ortho_set (s : set α) :=
∀ x y ∈ s, (x ⊥ y) ↔ x ≠ y 

def is_orthonormal_set (s : set α) :=
is_ortho_set s ∧ ∀ x ∈ s, is_normalised x

noncomputable def proj (x y : α) :=
((x ∘ y)/( ↑|y|*|y| )) • y

lemma zero_proj (x : α) :
proj 0 x = 0 := by dunfold proj; simp

lemma proj_zero (x : α) :
proj x 0 = 0 := by dunfold proj; simp

lemma proj_self_eq_self (x : α) :
proj x x = x :=
begin
  have ho : x = 0 ∨ x ≠ 0,
    apply em,
  dunfold proj,
  cases ho,
    rw ho,
    simp,

    rw ←of_real_mul,
    rw of_real_herm_norm_mul_self,
    rw div_self (inprod_self_ne_zero_iff.mpr ho),
    rw one_smul,
end

lemma smul_proj (x y : α) {a : ℂ} : 
proj (a • x) y = a • (proj x y) :=
begin
  dunfold proj,
  rw inprod_smul_left,
  rw smul_smul,
  ring,
end

lemma proj_smul (x y : α) {a : ℂ} (ha : a ≠ 0) :
proj x (a • y) = proj x y := 
begin
  have Hy : y = 0 ∨ y ≠ 0,
    apply em,
  cases Hy,
    rw Hy,
    rw smul_zero,

    dunfold proj,
    rw inprod_smul_right,
    rw herm_norm_smul,
    rw of_real_mul,
    rw smul_smul,
    suffices :  ((↑(abs a) * ↑|y| * (↑(abs a) * ↑|y| ))⁻¹ * x ∘ y * conj a * a) • y = ((↑|y| * ↑|y| )⁻¹ * x ∘ y) • y,
      rw div_eq_inv_mul,
      rw div_eq_inv_mul,
      rw field.mul_comm (conj a),
      rw ←field.mul_assoc,
      exact this,
    rw field.mul_assoc,
    rw ←field.mul_comm a,
    rw mul_conj, 
    rw ←field.mul_assoc ( ↑(abs a) * ↑|y| ),
    rw field.mul_comm (↑(abs a)),
    rw field.mul_assoc ( ↑|y| ),
    rw ←of_real_mul,
    rw mul_self_abs,
    rw field.mul_comm ( ↑|y| ),
    rw field.mul_comm,
    rw field.mul_assoc,
    rw mul_inv_eq, 
    rw field.mul_comm,
    rw field.mul_assoc ((↑|y| * ↑|y| )⁻¹),
    rw field.mul_comm (↑(norm_sq a))⁻¹,
    rw field.mul_assoc,
    rw field.mul_assoc (x ∘ y),
    rw field.inv_mul_cancel,
    rw field.mul_one,
    refl,
    
    exact of_real_ne_zero.mpr ((iff_false_right ha).mp (norm_sq_eq_zero)),
    exact (mul_ne_zero (of_real_ne_zero.mpr ((norm_ne_zero_iff_ne_zero).mpr Hy)) (of_real_ne_zero.mpr ((norm_ne_zero_iff_ne_zero).mpr Hy))),
    exact of_real_ne_zero.mpr ((iff_false_right ha).mp (norm_sq_eq_zero)),
end

lemma norm_proj_le (x y : α) : 
|proj x y| ≤ |x| :=
begin
  have Hy : y = 0 ∨ y ≠ 0,
    apply em,
  cases Hy,
    rw Hy,
    rw proj_zero,
    rw herm_norm_zero,
    exact @norm_nonneg _ _ x,

    dunfold proj,
    rw herm_norm_smul,
    rw complex.abs_div,
    rw ←of_real_mul,
    rw abs_of_real,
    rw abs_mul_self,
    rw div_mul_comm,
    rw division_def,
    rw mul_inv',
    rw ←field.mul_assoc,
    rw field.mul_inv_cancel,
    rw field.one_mul,
    rw field.mul_comm,
    rw ←division_def,
    rw div_le_iff,
      exact abs_inprod_le_mul_herm_norm x y,
      exact (norm_pos_iff y).mpr Hy,
      exact norm_ne_zero_iff_ne_zero.mpr Hy,
end

lemma ortho_imp_proj_eq_zero {x y : α} :
(x ⊥ y) → proj x y = 0 := 
begin
  dunfold herm_ortho,
  dunfold proj,
  intros H,
  rw H,
  simp,
end

lemma proj_eq_self_iff_lindep {x y : α} :
proj x y = x ↔ ∃ (a : ℂ), x = a • y :=
begin
  split,
    dunfold proj, 
    intros H,
    exact exists.intro (x ∘ y / (↑|y| * ↑|y| )) (eq_comm.mp H),

    intros H,
    cases H with a Ha,
    rw Ha,
    rw smul_proj,
    rw proj_self_eq_self, 
end

end herm_inner_product_space

class Hilbert_space (α : Type*) extends herm_inner_product_space α :=
(complete : ∀{f : filter α}, cauchy f → ∃x, f ≤ nhds x) 

instance Hilbert_space.to_complete_space (α : Type*) [Hilbert_space α] : complete_space α :=
{complete := @Hilbert_space.complete α _}

-- Hilbert basis theorem

import ring_theory.noetherian
import data.polynomial

universe u

open polynomial

local attribute [instance, priority 1] classical.prop_decidable

lemma polynomial.zero_ring_degree {R} [comm_ring R] (h : (0 : R) = 1) (f : polynomial R) :
degree f = ⊥ := by rw ←leading_coeff_eq_zero_iff_deg_eq_bot;exact eq_zero_of_zero_eq_one _ h _

lemma polynomial.leading_term_f_mul_X_pow {R} [nonzero_comm_ring R] (f : polynomial R)
  (n : ℕ) (hf : f ≠ 0) :
leading_coeff (f * X ^ n) ≠ 0 := 
begin
 rw leading_coeff_mul';
 {
   rw [leading_coeff_X_pow,mul_one],
   intro h,apply hf,
   rwa ←leading_coeff_eq_zero,
 }
end

lemma polynomial.degree_mul_X_pow {R} [comm_ring R] {f : polynomial R} (hf : f ≠ 0) (n : ℕ) :
degree (f * X ^ n) = degree f + n :=
begin
  by_cases h01 : (0 : R) = 1, simp [polynomial.zero_ring_degree h01 _],
  letI : nonzero_comm_ring R := { zero_ne_one := h01, .. (infer_instance : comm_ring R) },
  rw degree_mul_eq',rw degree_X_pow,
  rw [leading_coeff_X_pow,mul_one],
  exact (iff_false_right hf).1 leading_coeff_eq_zero,
end

-- remark that g ≠ 0 is not necessary but I don't need the lemma in this case.
lemma polynomial.eq_degree_of_mul_X_pow {R} [comm_ring R] (f g : polynomial R)
  (h : nat_degree f ≤ nat_degree g) (hf : f ≠ 0) (hg : g ≠ 0):
degree (f * X ^ (nat_degree g - nat_degree f)) = degree g :=
begin
  by_cases h01 : (0 : R) = 1, simp [polynomial.zero_ring_degree h01 _],
  letI : nonzero_comm_ring R := { zero_ne_one := h01, .. (infer_instance : comm_ring R) },
  rw polynomial.degree_mul_X_pow hf,
  rw [degree_eq_nat_degree hf,←with_bot.coe_add,degree_eq_nat_degree hg,with_bot.coe_eq_coe],
  exact nat.add_sub_cancel' h,
end

-- zero ring a special case so let's deal with it separately
theorem hilbert_basis_zero_ring {R} [comm_ring R] (h : (0 : R) = 1) :
is_noetherian_ring (polynomial R) :=
ring.is_noetherian_of_zero_eq_one $ ext.2 $ λ n, by simp [h]

-- giving up on WLOG
theorem leading_term_aux {R} [nonzero_comm_ring R] {f g : polynomial R} (Hle : nat_degree f ≤ nat_degree g)
  (Hf : f ≠ 0) (Hg : g ≠ 0) (Hh : leading_coeff f + leading_coeff g ≠ 0) :
leading_coeff (f * X ^ (nat_degree g - nat_degree f) + g) = leading_coeff f + leading_coeff g :=
begin
  let h := f * X ^ (nat_degree g - nat_degree f) + g,
  have Htemp : leading_coeff f * leading_coeff (X ^ (nat_degree g - nat_degree f)) ≠ 0,
    rw [leading_coeff_X_pow,mul_one],
    exact (λ h, Hf $ leading_coeff_eq_zero.1 h),
  have Ha : leading_coeff f = leading_coeff (f * X ^ (nat_degree g - nat_degree f)),
    rw [leading_coeff_mul' Htemp,leading_coeff_X_pow,mul_one],
  convert leading_coeff_add_of_degree_eq _ _,
    rw [degree_mul_eq' Htemp, degree_X_pow, degree_eq_nat_degree Hf,degree_eq_nat_degree Hg],
    rw [←with_bot.coe_add,with_bot.coe_eq_coe],
    exact nat.add_sub_cancel' Hle,
  rwa [←Ha],
end

def leading_term_bdd_deg_ideal {R : Type u} [nonzero_comm_ring R] (I : ideal (polynomial R)) (n : ℕ) :
  ideal R :=
{ carrier := {c | ∃ f, f ∈ I ∧ degree f ≤ n ∧ leading_coeff f = c},
  zero := ⟨0, I.zero_mem, lattice.bot_le, rfl⟩,
  add := λ a b ⟨f, Hf⟩ ⟨g, Hg⟩, begin
    by_cases h0 : a + b = 0, rw h0, exact ⟨0, I.zero_mem, lattice.bot_le, rfl⟩,
    by_cases hf : f = 0, rw [←Hf.2.2, ←Hg.2.2, hf, leading_coeff_zero, zero_add],
      exact ⟨g,Hg.1,Hg.2.1,rfl⟩,
    by_cases hg : g = 0, rw [←Hf.2.2, ←Hg.2.2, hg, leading_coeff_zero, add_zero],
      exact ⟨f,Hf.1,Hf.2.1,rfl⟩,
    cases le_total (nat_degree f) (nat_degree g) with hd hd,
    { have := leading_term_aux hd hf hg (by rwa [← Hf.2.2, ← Hg.2.2] at h0),
      rw [← Hf.2.2, ← Hg.2.2],
      refine ⟨_, I.add_mem (I.mul_mem_right Hf.1) Hg.1,
        le_trans (degree_add_le _ _) (max_le _ Hg.2.1), this⟩,
      have : leading_coeff f * leading_coeff (X ^ (nat_degree g - nat_degree f)) ≠ 0,
      { rw [leading_coeff_X_pow, mul_one], exact mt leading_coeff_eq_zero.1 hf },
      rw [degree_mul_eq' this, degree_X_pow, degree_eq_nat_degree hf,
          ← with_bot.coe_add, nat.add_sub_cancel' hd, ← degree_eq_nat_degree hg],
      exact Hg.2.1 },
    { have := leading_term_aux hd hg hf (by rwa [← Hf.2.2, ← Hg.2.2, add_comm] at h0),
      rw [← Hf.2.2, ← Hg.2.2, add_comm],
      refine ⟨_, I.add_mem (I.mul_mem_right Hg.1) Hf.1,
        le_trans (degree_add_le _ _) (max_le _ Hf.2.1), this⟩,
      have : leading_coeff g * leading_coeff (X ^ (nat_degree f - nat_degree g)) ≠ 0,
      { rw [leading_coeff_X_pow, mul_one], exact mt leading_coeff_eq_zero.1 hg },
      rw [degree_mul_eq' this, degree_X_pow, degree_eq_nat_degree hg,
          ← with_bot.coe_add, nat.add_sub_cancel' hd, ← degree_eq_nat_degree hf],
      exact Hf.2.1 }
  end,
  smul := λ c a ⟨f, hf1, hf2, hf3⟩, begin
    by_cases h0 : c • a = 0,
    { rw h0, exact ⟨0, I.zero_mem, lattice.bot_le, rfl⟩ },
    by_cases hc : c = 0,
    { rw [hc, zero_smul], exact ⟨0, I.zero_mem, lattice.bot_le, rfl⟩ },
    refine ⟨C c * f, I.mul_mem_left hf1, le_trans (degree_mul_le _ _) _, _⟩,
    { rw [degree_C hc, zero_add], exact hf2 },
    { have : leading_coeff (C c) * leading_coeff f ≠ 0,
      { rw [leading_coeff_C, ← smul_eq_mul, hf3], exact h0 },
      rw [leading_coeff_mul' this, leading_coeff_C, hf3, smul_eq_mul] }
  end }

/-lemma leading_term_bdd_deg_ideal {R} [nonzero_comm_ring R] (I : set (polynomial R)) [is_submodule I] (n : ℕ) :
submodule R R :=
⟨{c : R | ∃ f, f ∈ I ∧ degree f ≤ n ∧ leading_coeff f = c},{
  zero_ := ⟨0,is_submodule.zero,lattice.bot_le,rfl⟩,
  add_ := λ a b ⟨f, Hf⟩ ⟨g, Hg⟩, begin
    by_cases h0 : a + b = 0, rw h0, exact ⟨0,is_submodule.zero,lattice.bot_le,rfl⟩,
    by_cases hf : f = 0, rw [←Hf.2.2, ←Hg.2.2, hf, leading_coeff_zero, zero_add],
      exact ⟨g,Hg.1,Hg.2.1,rfl⟩,
    by_cases hg : g = 0, rw [←Hf.2.2, ←Hg.2.2, hg, leading_coeff_zero, add_zero],
      exact ⟨f,Hf.1,Hf.2.1,rfl⟩,
    by_cases hd : nat_degree f ≤ nat_degree g,
    { let h := f * X ^ (nat_degree g - nat_degree f) + g,
      letI : comm_ring (polynomial R) := by apply_instance,
      letI : module (polynomial R) (polynomial R) := @ring.to_module (polynomial R) _,
--      letI : module (polynomial R) (polynomial R) := ring.to_module, --(comm_ring.to_ring XXX),-- by apply_instance, -- fails to generate instance
      letI : is_submodule I := _inst_2, -- also fails
      have HfXtemp : X ^ (nat_degree g - nat_degree f) ∈ I :=
        is_submodule.smul ((@polynomial.X R _ _) ^ (nat_degree g - nat_degree f)) Hf.1,
      have HfX : f * X ^ (nat_degree g - nat_degree f) ∈ I :=
        mul_comm (X ^ (nat_degree g - nat_degree f)) f ▸ is_submodule.smul ((@polynomial.X R _ _) ^ (nat_degree g - nat_degree f)) Hf.1,
      have hI : h ∈ I := is_submodule.add (mul_comm ▸ is_submodule.smul ((@polynomial.X R _ _) ^ (nat_degree g - nat_degree f)) Hf.1) Hg.1,
    -- prove deg h <= n
      let htemp : leading_coeff h = a + b := Hf.2.2 ▸ Hg.2.2 ▸ leading_term_aux hd hf hg (Hf.2.2.symm ▸ Hg.2.2.symm ▸ h0),
      exact ⟨h,begin end⟩,

    },
    sorry
  end,
  smul := sorry
}⟩-/

def ideal.leading_coeff {R : Type u} [nonzero_comm_ring R] (I : ideal (polynomial R)) : ideal R :=
{ carrier := leading_coeff '' I,
  zero := ⟨0, I.zero_mem, rfl⟩,
  add := λ a b ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩, begin
    by_cases h0 : a + b = 0, rw h0, exact ⟨0, I.zero_mem, rfl⟩,
    by_cases hf : f = 0, rw [← hf2, ← hg2, hf, leading_coeff_zero, zero_add], exact ⟨g, hg1, rfl⟩,
    by_cases hg : g = 0, rw [← hf2, ← hg2, hg, leading_coeff_zero, add_zero], exact ⟨f, hf1, rfl⟩,
    cases le_total (nat_degree f) (nat_degree g) with hd hd, -- can't get WLOG to work
    { refine ⟨f * X ^ (nat_degree g - nat_degree f) + g,
        I.add_mem (I.mul_mem_right hf1) hg1, _⟩,
      have := leading_term_aux hd hf hg (by rwa [hf2, hg2]),
      rwa [hf2, hg2] at this },
    { refine ⟨g * X ^ (nat_degree f - nat_degree g) + f,
        I.add_mem (I.mul_mem_right hg1) hf1, _⟩,
      have := leading_term_aux hd hg hf (by rwa [hf2, hg2, add_comm]),
      rwa [hf2, hg2, add_comm b a] at this }
  end,
  smul := λ c a ⟨f, hf1, hf2⟩, begin
    by_cases hcr : c • a = 0, rw hcr, exact ⟨0, I.zero_mem, rfl⟩,
    refine ⟨C c * f, I.mul_mem_left hf1, _⟩,
    have : leading_coeff (C c) * leading_coeff f ≠ 0,
    { rwa [leading_coeff_C, hf2, ← smul_eq_mul] },
    rw [leading_coeff_mul' this, leading_coeff_C, hf2, smul_eq_mul]
  end }

theorem hilbert_basis {R} [comm_ring R] (hR : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
begin
  -- deal with zero ring first
  by_cases h01 : (0 : R) = 1,
  { exact hilbert_basis_zero_ring h01 },
  letI : nonzero_comm_ring R := { zero_ne_one := h01, ..(infer_instance : comm_ring R) },
  /-let L : ideal R := {
    carrier := set.range leading_coeff,
    zero := ⟨0,rfl⟩,
    add := λ a b ⟨f,Hf⟩ ⟨g,Hg⟩, begin
      by_cases h0 : a + b = 0, rw h0, exact ⟨0, rfl⟩,
      by_cases hf : f = 0, rw [←Hf, ←Hg, hf, leading_coeff_zero, zero_add], exact ⟨g,rfl⟩,
      by_cases hg : g = 0, rw [←Hf, ←Hg, hg, leading_coeff_zero, add_zero], exact ⟨f,rfl⟩,
      by_cases hd : nat_degree f ≤ nat_degree g, -- can't get WLOG to work
      { let h := f * X ^ (nat_degree g - nat_degree f) + g,
        exact ⟨h, Hf ▸ Hg ▸ leading_term_aux hd hf hg (Hf.symm ▸ Hg.symm ▸ h0)⟩,
      },
      { let h := g * X ^ (nat_degree f - nat_degree g) + f,
        exact ⟨h, Hg ▸ Hf ▸ add_comm (leading_coeff g) (leading_coeff f) ▸ leading_term_aux (le_of_lt $ lt_of_not_ge hd) hg hf (Hg.symm ▸ Hf.symm ▸ add_comm a b ▸ h0)⟩,
      }
    end,
    smul := λ c r ⟨f,Hf⟩, begin
      rw smul_eq_mul,
      by_cases hcr : c * r = 0, rw hcr, exact ⟨0,rfl⟩,
      exact ⟨(C c)*f,begin
        rw leading_coeff_mul',
          rw [Hf,leading_coeff_C],
        rwa [Hf,leading_coeff_C],
      end⟩
    end,
  },
  cases hR L with GL HGL, -- is there a better way?-/
  intro I, change ideal (polynomial R) at I,
  cases hR I.leading_coeff with GL HGL,
  sorry
end

#print is_fg

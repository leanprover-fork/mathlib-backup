-- Hilbert basis theorem

import ring_theory.noetherian
import data.polynomial

universes u v w

def module_of_module_of_ring_hom {R : Type u} [ring R]
  {S : Type v} [ring S] (f : R → S) [is_ring_hom f]
  {M : Type w} [add_comm_group M] [module S M] : module R M :=
module.of_core {
  smul := λ r m, f r • m,
  smul_add := λ r, smul_add _,
  add_smul := λ r s x, show f (r + s) • x = _,
    by rw [is_ring_hom.map_add f, add_smul],
  mul_smul := λ r s x, show f (r * s) • x = _,
    by rw [is_ring_hom.map_mul f, mul_smul],
  one_smul := λ x, show f 1 • x = _,
    by rw [is_ring_hom.map_one f, one_smul],
}

section
local attribute [instance] module_of_module_of_ring_hom
def submodule_of_submodule_of_ring_hom {R : Type u} [ring R]
  {S : Type v} [ring S] (f : R → S) [is_ring_hom f]
  {M : Type w} [add_comm_group M] [module S M]
  (N : submodule S M) : submodule R M :=
{ carrier := N.carrier,
  zero := N.zero_mem,
  add := λ _ _, N.add_mem,
  smul := λ c x, N.smul_mem (f c) }
end

namespace polynomial

section
variables {R : Type u} [comm_semiring R] [decidable_eq R]

def degree_le_iff_coeff_zero (f : polynomial R) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem degree_C_mul_X_pow_le (r : R) (n : ℕ) : degree (C r * X^n : polynomial R) ≤ n :=
by rw [← single_eq_C_mul_X]; exact finset.sup_le (λ b hb,
by rw list.eq_of_mem_singleton (finsupp.support_single_subset hb); exact le_refl _)

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:R) n

theorem degree_X_le (n : ℕ) : degree (X : polynomial R) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:R) 1

theorem nat_degree_le_of_degree_le {p : polynomial R} {n : ℕ}
  (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

theorem with_bot.le_of_lt_succ {k : with_bot ℕ} {n : ℕ}
  (h : k < n+1) : k ≤ n :=
match k, h with
| none,     h := lattice.bot_le
| (some d), h := with_bot.coe_le_coe.2 (nat.le_of_lt_succ (with_bot.coe_lt_coe.1 h))
end

theorem leading_coeff_mul_X_pow {p : polynomial R} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
decidable.by_cases
  (assume H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (assume H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', leading_coeff_X_pow, mul_one];
       rwa [leading_coeff_X_pow, mul_one])

theorem exists_eq_add_C_leading_coeff_mul_X_pow_nat_degree {p : polynomial R} (H : p ≠ 0) :
  ∃ q : polynomial R, p = q + C (leading_coeff p) * X ^ (nat_degree p) ∧ degree q < degree p :=
⟨finsupp.erase (nat_degree p) p,
  by rw [← single_eq_C_mul_X]; exact finsupp.erase_add_single.symm,
  degree_erase_lt H⟩

theorem exists_eq_add_C_leading_coeff_mul_X_pow_of_nat_degree_le {p : polynomial R} (H : p ≠ 0)
  (n : ℕ) (hn : nat_degree p ≤ n) :
  ∃ q : polynomial R, p = q + C (coeff p n) * X ^ n ∧ degree q < n :=
or.cases_on (lt_or_eq_of_le hn)
  (λ h, have degree p < n := lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 h),
    ⟨p, by rw [coeff_eq_zero_of_degree_lt this, C_0, zero_mul, add_zero], this⟩)
  (λ h, by rw [← h, ← degree_eq_nat_degree H];
    exact exists_eq_add_C_leading_coeff_mul_X_pow_nat_degree H)

end

variables (R : Type u) [comm_ring R] [decidable_eq R]

def degree_le (n : with_bot ℕ) :
  submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : with_bot ℕ} {f : polynomial R} :
  f ∈ degree_le R n ↔ degree f ≤ n :=
by simp only [degree_le, submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl

theorem degree_le_eq_span_X_pow {n : ℕ} :
  degree_le R n = submodule.span ↑((finset.range (n+1)).image (λ n, X^n) : finset (polynomial R)) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_le.1 hp,
    induction n with n ih generalizing p,
    { rw submodule.mem_coe,
      change p ∈ submodule.span ↑(finset.image (λ n, X^n) (finset.singleton 0 : finset ℕ)),
      rw [eq_C_of_degree_le_zero hp, finset.image_singleton, finset.coe_singleton, submodule.mem_span_singleton],
      existsi coeff p 0,
      rw [← C_mul', pow_zero, mul_one] },
    by_cases hp0 : p = 0, { rw hp0, exact (submodule.mem_coe _).2 (submodule.zero_mem _) },
    rcases exists_eq_add_C_leading_coeff_mul_X_pow_of_nat_degree_le hp0 n.succ (nat_degree_le_of_degree_le hp) with ⟨q, hpq, hdq⟩,
    rw [finset.range_succ, finset.image_insert, finset.coe_insert, set.insert_eq, submodule.span_union],
    rw [submodule.mem_coe, hpq, submodule.mem_sup, C_mul'],
    refine ⟨_, _, _, _, add_comm _ _⟩,
    { rw submodule.mem_span_singleton, exact ⟨_, rfl⟩ },
    exact ih (with_bot.le_of_lt_succ hdq) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_le.2,
  apply le_trans (degree_X_pow_le _) (with_bot.coe_le_coe.2 $ nat.le_of_lt_succ $ finset.mem_range.1 hk)
end

end polynomial

variables {R : Type u} [comm_ring R] [decidable_eq R]

namespace ideal
open polynomial

variable (I : ideal (polynomial R))

def of_polynomial : submodule R (polynomial R) :=
{ carrier := (@submodule.carrier (polynomial R) (polynomial R) _ _ ring.to_module I : set (polynomial R)),
  zero := I.zero_mem,
  add := λ _ _, I.add_mem,
  smul := λ c x H, by rw [← C_mul'];
    exact @submodule.smul_mem (polynomial R) (polynomial R) _ _ ring.to_module _ _ _ H }

theorem mem_of_polynomial (x) : x ∈ I.of_polynomial ↔ x ∈ I := iff.rfl

def degree_le (n : ℕ) : submodule R (polynomial R) :=
degree_le R n ⊓ I.of_polynomial

def leading_coeff_nth (n : ℕ) : ideal R :=
(I.degree_le n).map $ lcoeff R n

theorem mem_leading_coeff_nth (n : ℕ) (x) :
  x ∈ I.leading_coeff_nth n ↔ ∃ p ∈ I, degree p ≤ n ∧ leading_coeff p = x :=
begin
  simp only [leading_coeff_nth, degree_le, submodule.mem_map, lcoeff_apply, submodule.mem_inf, mem_degree_le],
  split,
  { rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩,
    cases lt_or_eq_of_le hpdeg with hpdeg hpdeg,
    { refine ⟨0, I.zero_mem, lattice.bot_le, _⟩,
      rw [leading_coeff_zero, eq_comm],
      exact coeff_eq_zero_of_degree_lt hpdeg },
    { refine ⟨p, hpI, le_of_eq hpdeg, _⟩,
      rw [leading_coeff, nat_degree, hpdeg], refl } },
  { rintro ⟨p, hpI, hpdeg, rfl⟩,
    have : nat_degree p + (n - nat_degree p) = n,
    { exact nat.add_sub_cancel' (nat_degree_le_of_degree_le hpdeg) },
    refine ⟨p * X ^ (n - nat_degree p), ⟨_, I.mul_mem_right hpI⟩, _⟩,
    { apply le_trans (degree_mul_le _ _) _,
      apply le_trans (add_le_add' (degree_le_nat_degree) (degree_X_pow_le _)) _,
      rw [← with_bot.coe_add, this],
      exact le_refl _ },
    { rw [leading_coeff, ← coeff_mul_X_pow p (n - nat_degree p), this] } }
end

theorem mem_leading_coeff_nth_zero (x) :
  x ∈ I.leading_coeff_nth 0 ↔ C x ∈ I :=
(mem_leading_coeff_nth _ _ _).trans
⟨λ ⟨p, hpI, hpdeg, hpx⟩, by rwa [← hpx, leading_coeff,
  nat.eq_zero_of_le_zero (nat_degree_le_of_degree_le hpdeg),
  ← eq_C_of_degree_le_zero hpdeg],
λ hx, ⟨C x, hx, degree_C_le, leading_coeff_C x⟩⟩

theorem leading_coeff_nth_mono {m n : ℕ} (H : m ≤ n) :
  I.leading_coeff_nth m ≤ I.leading_coeff_nth n :=
begin
  intros r hr,
  simp only [submodule.mem_coe, mem_leading_coeff_nth] at hr ⊢,
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩,
  refine ⟨p * X ^ (n - m), I.mul_mem_right hpI, _, leading_coeff_mul_X_pow⟩,
  refine le_trans (degree_mul_le _ _) _,
  refine le_trans (add_le_add' hpdeg (degree_X_pow_le _)) _,
  rw [← with_bot.coe_add, nat.add_sub_cancel' H],
  exact le_refl _
end

def leading_coeff : ideal R :=
⨆ n : ℕ, I.leading_coeff_nth n

theorem mem_leading_coeff (x) :
  x ∈ I.leading_coeff ↔ ∃ p ∈ I, polynomial.leading_coeff p = x :=
begin
  rw [leading_coeff, submodule.mem_supr_of_directed],
  simp only [mem_leading_coeff_nth],
  { split, { rintro ⟨i, p, hpI, hpdeg, rfl⟩, exact ⟨p, hpI, rfl⟩ },
    rintro ⟨p, hpI, rfl⟩, exact ⟨nat_degree p, p, hpI, degree_le_nat_degree, rfl⟩ },
  { exact ⟨0⟩ },
  intros i j, exact ⟨i + j, I.leading_coeff_nth_mono (nat.le_add_right _ _),
    I.leading_coeff_nth_mono (nat.le_add_left _ _)⟩
end

theorem is_fg_degree_le (hnr : is_noetherian_ring R) (n : ℕ) :
  submodule.fg (I.degree_le n) :=
begin
  induction n with n ih,
  case nat.zero { sorry
    /-cases hnr (I.leading_coeff_nth 0) with s hs,
    refine ⟨s.map ⟨C, λ _ _, C_inj.1⟩, le_antisymm _ _⟩,
    { rw submodule.span_le,
      intros p hp,
      simp only [submodule.mem_coe, finset.mem_coe,
        finset.mem_map, function.embedding.coe_fn_mk,
        degree_le, submodule.mem_inf, mem_degree_le] at hp ⊢,
      rcases hp with ⟨r, hrs, rfl⟩,
      refine ⟨degree_C_le, _⟩,
      rw [mem_of_polynomial, ← mem_leading_coeff_nth_zero, ← hs],
      exact submodule.subset_span hrs },
    {  }-/
  },
  sorry
end

end ideal

theorem hilbert_basis (hnr : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
assume I : ideal (polynomial R),
let L := I.leading_coeff in
let M := well_founded.min (is_noetherian_iff_well_founded.1 hnr)
  (set.range I.leading_coeff_nth) (set.ne_empty_of_mem ⟨0, rfl⟩) in
have hm : M ∈ set.range I.leading_coeff_nth := well_founded.min_mem _ _ _,
let ⟨N, HN⟩ := hm in
have gen' : ∀ n, ∃ s : finset (polynomial R), (↑s : set (polynomial R)) ⊆ ↑I ∧
  (∀ x ∈ s, polynomial.degree x ≤ ↑n) ∧
  submodule.span (polynomial.lcoeff R n '' ↑s) = ideal.leading_coeff_nth I n := sorry,
let ⟨gen, hgen⟩ := classical.skolem.1 gen' in
⟨finset.bind (finset.range (N+1)) gen,
le_antisymm (ideal.span_le.2 $ λ p hp, let ⟨n, hnN, hpn⟩ := finset.mem_bind.1 hp in (hgen n).1 hpn) $
λ p hpI, begin
  generalize h : p.nat_degree = n,
  induction n using nat.strong_induction_on with n ih,
  sorry
end⟩

#check is_noetherian_iff_well_founded
#check well_founded.min
#check well_founded.min_mem
#check well_founded.not_lt_min
#check classical.skolem

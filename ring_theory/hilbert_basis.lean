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
is_noetherian_submodule_left.1 (is_noetherian_of_fg_of_noetherian _ hnr
  ⟨_, degree_le_eq_span_X_pow.symm⟩) _

end ideal

theorem hilbert_basis (hnr : is_noetherian_ring R) : is_noetherian_ring (polynomial R) :=
assume I : ideal (polynomial R),
let L := I.leading_coeff in
let M := well_founded.min (is_noetherian_iff_well_founded.1 hnr)
  (set.range I.leading_coeff_nth) (set.ne_empty_of_mem ⟨0, rfl⟩) in
have hm : M ∈ set.range I.leading_coeff_nth := well_founded.min_mem _ _ _,
let ⟨N, HN⟩ := hm, ⟨s, hs⟩ := I.is_fg_degree_le hnr N in
have hm2 : ∀ k, I.leading_coeff_nth k ≤ M := λ k, or.cases_on (le_or_lt k N)
  (λ h, HN ▸ I.leading_coeff_nth_mono h)
  (λ h x hx, classical.by_contradiction $ λ hxm,
    have ¬M < I.leading_coeff_nth k, by refine well_founded.not_lt_min
      (is_noetherian_iff_well_founded.1 hnr) _ _ _; exact ⟨k, rfl⟩,
    this ⟨HN ▸ I.leading_coeff_nth_mono (le_of_lt h), λ H, hxm (H hx)⟩),
⟨s, le_antisymm (ideal.span_le.2 $ λ x hx, have x ∈ I.degree_le N, from hs ▸ submodule.subset_span hx, this.2) $ begin
  intros p hp, generalize hn : p.nat_degree = k,
  induction k using nat.strong_induction_on with k ih generalizing p,
  cases le_or_lt k N,
  { subst k,
    have : p ∈ I.degree_le N,
    { exact ⟨polynomial.mem_degree_le.2 (le_trans polynomial.degree_le_nat_degree $ with_bot.coe_le_coe.2 h), hp⟩ },
    rw ← hs at this,
    apply submodule.span_induction this,
    { exact λ _ hx, ideal.subset_span hx },
    { exact (ideal.span ↑s).zero_mem },
    { exact λ _ _ h1 h2, (ideal.span ↑s).add_mem h1 h2 },
    { intros c f hf, rw ← polynomial.C_mul',
      exact (ideal.span ↑s).mul_mem_left hf } },
  { have hp0 : p ≠ 0,
    { rintro rfl, cases hn, exact nat.not_lt_zero _ h },
    have : (0 : R) ≠ 1,
    { intro h, apply hp0, ext i, refine (mul_one _).symm.trans _,
      rw [← h, mul_zero], refl },
    letI : nonzero_comm_ring R := { zero_ne_one := this,
      ..(infer_instance : comm_ring R) },
    have : p.leading_coeff ∈ I.leading_coeff_nth N,
    { rw HN, exact hm2 k ((I.mem_leading_coeff_nth _ _).2
        ⟨_, hp, hn ▸ polynomial.degree_le_nat_degree, rfl⟩) },
    rw I.mem_leading_coeff_nth at this,
    rcases this with ⟨q, hq, hdq, hlqp⟩,
    have hq0 : q ≠ 0,
    { intro H, rw [← polynomial.leading_coeff_eq_zero] at H,
      rw [hlqp, polynomial.leading_coeff_eq_zero] at H, exact hp0 H },
    have h1 : p.degree = (q * polynomial.X ^ (k - q.nat_degree)).degree,
    { rw [polynomial.degree_mul_eq', polynomial.degree_X_pow],
      rw [polynomial.degree_eq_nat_degree hp0, polynomial.degree_eq_nat_degree hq0],
      rw [← with_bot.coe_add, nat.add_sub_cancel', hn],
      { refine le_trans (polynomial.nat_degree_le_of_degree_le hdq) (le_of_lt h) },
      rw [polynomial.leading_coeff_X_pow, mul_one],
      exact mt polynomial.leading_coeff_eq_zero.1 hq0 },
    have h2 : p.leading_coeff = (q * polynomial.X ^ (k - q.nat_degree)).leading_coeff,
    { rw [← hlqp, polynomial.leading_coeff_mul_X_pow] },
    have := polynomial.degree_sub_lt h1 hp0 h2,
    rw [polynomial.degree_eq_nat_degree hp0] at this,
    rw ← sub_add_cancel p (q * polynomial.X ^ (k - q.nat_degree)),
    refine (ideal.span ↑s).add_mem _ ((ideal.span ↑s).mul_mem_right _),
    { by_cases hpq : p - q * polynomial.X ^ (k - q.nat_degree) = 0,
      { rw hpq, exact ideal.zero_mem _ },
      refine ih _ _ (I.sub_mem hp (I.mul_mem_right hq)) rfl,
      rwa [polynomial.degree_eq_nat_degree hpq, with_bot.coe_lt_coe, hn] at this },
    rw [polynomial.degree_eq_nat_degree hq0, with_bot.coe_le_coe] at hdq,
    exact ih _ (lt_of_le_of_lt hdq h) hq rfl }
end⟩

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

def deg_le_iff_coeff_zero (f : polynomial R) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem deg_C_mul_X_pow_le (r : R) (n : ℕ) : degree (C r * X^n : polynomial R) ≤ n :=
by rw [← single_eq_C_mul_X]; exact finset.sup_le (λ b hb,
by rw list.eq_of_mem_singleton (finsupp.support_single_subset hb); exact le_refl _)

theorem deg_X_pow_le (n : ℕ) : degree (X^n : polynomial R) ≤ n :=
by simpa only [C_1, one_mul] using deg_C_mul_X_pow_le (1:R) n

theorem deg_X_le (n : ℕ) : degree (X : polynomial R) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using deg_C_mul_X_pow_le (1:R) 1

end

variables (R : Type u) [comm_ring R] [decidable_eq R]

def deg_le (n : with_bot ℕ) :
  submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : ↑k > n, ((coeff_is_linear k).mk' _).ker

variable {R}

theorem mem_deg_le {n : with_bot ℕ} {f : polynomial R} :
  f ∈ deg_le R n ↔ degree f ≤ n :=
by simp only [deg_le, submodule.mem_infi, deg_le_iff_coeff_zero, linear_map.mem_ker]; refl

end polynomial

variables {R : Type u} [comm_ring R] [decidable_eq R]
variable (I : ideal (polynomial R))

def ideal.of_polynomial : submodule R (polynomial R) :=
{ carrier := (@submodule.carrier (polynomial R) (polynomial R) _ _ ring.to_module I : set (polynomial R)),
  zero := I.zero_mem,
  add := λ _ _, I.add_mem,
  smul := λ c x H, by rw [← polynomial.C_mul'];
    exact @submodule.smul_mem (polynomial R) (polynomial R) _ _ ring.to_module _ _ _ H }

theorem ideal.mem_of_polynomial (x) : x ∈ I.of_polynomial ↔ x ∈ I := iff.rfl

def ideal.leading_coeff : ideal R :=
⨆ n : ℕ, submodule.map ((polynomial.coeff_is_linear n).mk' _) $
  polynomial.deg_le R n ⊓ I.of_polynomial

theorem ideal.mem_leading_coeff (x) :
  x ∈ I.leading_coeff ↔ ∃ p ∈ I, polynomial.leading_coeff p = x :=
begin
  rw [ideal.leading_coeff, submodule.mem_supr_of_directed],
  simp only [submodule.mem_coe, submodule.mem_map, is_linear_map.mk'_apply, submodule.mem_inf, polynomial.mem_deg_le],
  { split,
    { rintro ⟨i, y, ⟨hydeg, hyI⟩, rfl⟩,
      cases lt_or_eq_of_le hydeg with hydeg hydeg,
      { refine ⟨0, I.zero_mem, _⟩,
        rw [polynomial.leading_coeff_zero, eq_comm],
         exact polynomial.coeff_eq_zero_of_degree_lt hydeg },
      { refine ⟨y, hyI, _⟩,
        rw [polynomial.leading_coeff, polynomial.nat_degree, hydeg], refl } },
    { rintro ⟨p, hpI, hpx⟩,
      exact ⟨p.nat_degree, p, ⟨polynomial.degree_le_nat_degree, hpI⟩, hpx⟩ } },
  { exact ⟨0⟩ },
  intros i j, existsi i + j, split,
  { intros r hr,
    erw [submodule.mem_map] at hr ⊢,
    simp only [is_linear_map.mk'_apply, submodule.mem_inf, polynomial.mem_deg_le] at hr ⊢,
    rcases hr with ⟨p, ⟨hpdeg, hpI⟩, rfl⟩,
    refine ⟨p * polynomial.X ^ j, ⟨_, I.mul_mem_right hpI⟩, _⟩,
    { refine le_trans (polynomial.degree_mul_le _ _) _,
      exact add_le_add' hpdeg (polynomial.deg_X_pow_le j) },
    { rw polynomial.coeff_mul_X_pow } },
  { intros r hr,
    erw [submodule.mem_map] at hr ⊢,
    simp only [is_linear_map.mk'_apply, submodule.mem_inf, polynomial.mem_deg_le] at hr ⊢,
    rcases hr with ⟨p, ⟨hpdeg, hpI⟩, rfl⟩,
    refine ⟨p * polynomial.X ^ i, ⟨_, I.mul_mem_right hpI⟩, _⟩,
    { refine le_trans (polynomial.degree_mul_le _ _) _,
      rw add_comm i j,
      exact add_le_add' hpdeg (polynomial.deg_X_pow_le i) },
    { rw [add_comm, polynomial.coeff_mul_X_pow] } }
end

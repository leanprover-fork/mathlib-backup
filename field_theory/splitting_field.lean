/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes

Definition of splitting fields, and definition of homomorphism into any field that splits
-/
import ring_theory.adjoin_root

universes u v w

variables {α : Type u} {β : Type v} {γ : Type w}

namespace splitting_field

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable
variables [discrete_field α] [discrete_field β] [discrete_field γ]
open polynomial adjoin_root

def irr_factor (f : polynomial α) : polynomial α :=
if hf : f ≠ 0 ∧ ¬is_unit f
then classical.some (is_noetherian_ring.exists_irreducible_factor
  principal_ideal_domain.is_noetherian_ring hf.2 hf.1)
else X

lemma irr_factor_dvd {f : polynomial α} (h : degree f ≠ 0) : irr_factor f ∣ f :=
if hf : f = 0
then by simp [hf]
else have hf : f ≠ 0 ∧ ¬ is_unit f, from ⟨hf, by rwa is_unit_iff_degree_eq_zero⟩,
  by rw [irr_factor, dif_pos hf]; exact
(classical.some_spec (is_noetherian_ring.exists_irreducible_factor
    principal_ideal_domain.is_noetherian_ring hf.2 hf.1)).2

@[instance] lemma irr_factor_irreducible (f : polynomial α) :
  irreducible (irr_factor f) :=
if hf : f ≠ 0 ∧ ¬ is_unit f
then by rw [irr_factor, dif_pos hf]; exact
 (classical.some_spec (is_noetherian_ring.exists_irreducible_factor
    principal_ideal_domain.is_noetherian_ring hf.2 hf.1)).1
else by rw [irr_factor, dif_neg hf];
  exact irreducible_of_degree_eq_one degree_X

section splits

variables (i : α → β) [is_field_hom i]

/-- a polynomial `splits` iff it is zero or all of its irreducible factors have `degree` 1 -/
def splits (f : polynomial α) : Prop :=
f = 0 ∨ ∀ {g : polynomial β}, irreducible g → g ∣ f.map i → degree g = 1

@[simp] lemma splits_zero : splits i (0 : polynomial α) := or.inl rfl

@[simp] lemma splits_C (a : α) : splits i (C a) :=
if ha : a = 0 then ha.symm ▸ (@C_0 α _ _).symm ▸ splits_zero i
else
have hia : i a ≠ 0, from mt ((is_add_group_hom.injective_iff i).1
  (is_field_hom.injective i) _) ha,
or.inr $ λ g hg ⟨p, hp⟩, absurd hg.1 (classical.not_not.2 (is_unit_iff_degree_eq_zero.2 $
  by have := congr_arg degree hp;
    simp [degree_C hia, @eq_comm (with_bot ℕ) 0,
      nat.with_bot.add_eq_zero_iff] at this; clear _fun_match; tautology))

lemma splits_of_degree_eq_one {f : polynomial α} (hf : degree f = 1) : splits i f :=
or.inr $ λ g hg ⟨p, hp⟩,
  by have := congr_arg degree hp;
  simp [nat.with_bot.add_eq_one_iff, hf, @eq_comm (with_bot ℕ) 1,
    mt is_unit_iff_degree_eq_zero.2 hg.1] at this;
  clear _fun_match; tauto

lemma splits_of_degree_le_one {f : polynomial α} (hf : degree f ≤ 1) : splits i f :=
begin
  cases h : degree f with n,
  { rw [degree_eq_bot.1 h]; exact splits_zero i },
  { cases n with n,
    { rw [eq_C_of_degree_le_zero (trans_rel_right (≤) h (le_refl _))];
      exact splits_C _ _ },
    { have hn : n = 0,
      { rw h at hf,
        cases n, { refl }, { exact absurd hf dec_trivial } },
      exact splits_of_degree_eq_one _ (by rw [h, hn]; refl) } }
end

lemma splits_mul {f g : polynomial α} (hf : splits i f) (hg : splits i g) : splits i (f * g) :=
if h : f * g = 0 then by simp [h]
else or.inr $ λ p hp hpf, ((principal_ideal_domain.prime_of_irreducible hp).2.2 _ _
    (show p ∣ map i f * map i g, by convert hpf; rw map_mul)).elim
  (hf.resolve_left (λ hf, by simpa [hf] using h) hp)
  (hg.resolve_left (λ hg, by simpa [hg] using h) hp)

lemma splits_of_splits_mul {f g: polynomial α} (hfg : f * g ≠ 0) (h : splits i (f * g)) :
  splits i f ∧ splits i g :=
⟨or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_right _ _)),
 or.inr $ λ g hgi hg, or.resolve_left h hfg hgi (by rw map_mul; exact dvd.trans hg (dvd_mul_left _ _))⟩

lemma splits_map_iff (j : β → γ) [is_field_hom j] {f : polynomial α} :
  splits j (f.map i) ↔ splits (λ x, j (i x)) f :=
by simp [splits, polynomial.map_map]

lemma exists_root_of_splits {f : polynomial α} (hs : splits i f) (hf0 : degree f ≠ 0) :
  ∃ x, eval₂ i x f = 0 :=
hs.elim (λ hf0, ⟨37, by simp [hf0]⟩) $
λ hs, let ⟨x, hx⟩ := exists_root_of_degree_eq_one
  (hs (irr_factor_irreducible (f.map i))
    (irr_factor_dvd (by simpa))) in
  ⟨x, let ⟨g, hg⟩ := irr_factor_dvd (show degree (f.map i) ≠ 0, by simpa) in
    by rw [← eval_map, hg, eval_mul, (show _ = _, from hx), zero_mul]⟩

lemma splits_of_splits_id : ∀ {f : polynomial α} (h : splits id f), splits i f
| f := λ h,
  if hf : degree f ≤ 1 then splits_of_degree_le_one _ hf
  else have hfi : ¬irreducible f := mt (h.resolve_left (λ hf0, by simpa [hf0] using hf))
    (show ¬ (f ∣ f.map id → degree f = 1),
      from λ h, absurd (h (by simp))
        (λ h, by simpa [h, lt_irrefl] using hf)),
  have hfu : ¬is_unit f,
    from λ h, by rw [is_unit_iff_degree_eq_zero] at h; rw h at hf;
      exact hf dec_trivial,
  let ⟨p, q, hpu, hqu, hpq⟩ := (irreducible_or_factor _ hfu).resolve_left hfi in
  have hpq0 : p * q ≠ 0, from λ hpq0, by simpa [hpq.symm, hpq0] using hf,
  have hf0 : f ≠ 0, from λ hf0, by simpa [hf0] using hf,
  have hwfp : degree p < degree f,
    by rw [euclidean_domain.eq_div_of_mul_eq_left (ne_zero_of_mul_ne_zero_left hpq0) hpq];
      exact degree_div_lt hf0  (degree_pos_of_ne_zero_of_nonunit
        (ne_zero_of_mul_ne_zero_left hpq0) hqu),
  have hwfp : degree q < degree f,
    by rw [euclidean_domain.eq_div_of_mul_eq_right (ne_zero_of_mul_ne_zero_right hpq0) hpq];
      exact degree_div_lt hf0  (degree_pos_of_ne_zero_of_nonunit
        (ne_zero_of_mul_ne_zero_right hpq0) hpu),
  (splits_map_iff id _).1 $ begin
    rw [map_id, ← hpq],
    rw [← hpq] at h,
    exact splits_mul _ (splits_of_splits_id (splits_of_splits_mul _ hpq0 h).1)
      (splits_of_splits_id (splits_of_splits_mul _ hpq0 h).2)
  end
using_well_founded {dec_tac := tactic.assumption}

lemma splits_comp_of_splits (j : β → γ) [is_field_hom j] {f : polynomial α}
  (h : splits i f) : splits (λ x, j (i x)) f :=
begin
  change i with (λ x, id (i x)) at h,
  rw [← splits_map_iff],
  rw [← splits_map_iff i id]  at h,
  exact splits_of_splits_id _ h
end

end splits

lemma mul_div_irr_factor_cancel {f : polynomial α} (h : degree f ≠ 0) :
  (X - C (root : adjoin_root (irr_factor f))) * (f.map coe / (X - C root)) = f.map coe :=
begin
  rw [mul_div_eq_iff_is_root, is_root.def],
  cases irr_factor_dvd h with g hg,
  conv_lhs { congr, skip, congr, skip, rw hg },
  rw [eval_map (coe : α → adjoin_root (irr_factor f)), eval₂_mul, eval₂_root, zero_mul],
end

protected lemma well_founded {n : ℕ} {f : polynomial α} (h : nat_degree f = n + 1) :
  nat_degree (f.map (coe : α → adjoin_root (irr_factor f)) / (X - C root)) = n :=
have hmd : (X - C root) * (f.map coe / (X - C root)) = f.map coe :=
  mul_div_irr_factor_cancel
    (show degree f ≠ 0, from mt nat_degree_eq_of_degree_eq_some (h.symm ▸ dec_trivial)),
have h0 : (X - C root : polynomial (adjoin_root (irr_factor f))) *
    (f.map coe / (X - C root)) ≠ 0,
  by rw hmd; exact mt (congr_arg nat_degree)
    (by rw [nat_degree_map, h]; exact dec_trivial),
(add_left_inj (nat_degree (X - C root : polynomial (adjoin_root (irr_factor f))))).1 $
  by rw [← nat_degree_mul_eq (ne_zero_of_mul_ne_zero_right h0) (ne_zero_of_mul_ne_zero_left h0),
     hmd, nat_degree_map, h, nat_degree_eq_of_degree_eq_some (degree_X_sub_C _), add_comm]

def splitting_field_aux_zero (α : Type u) (I : discrete_field α) (f : polynomial α)
  (hf : nat_degree f = 0) : Σ' (β : Type u) [discrete_field β] (i : α → β) [by exactI is_field_hom i],
   by exactI splits i f :=
⟨α, I, id, is_ring_hom.id,
  splits_of_degree_le_one _
    (calc degree f ≤ nat_degree f : degree_le_nat_degree
    ... ≤ 1 : by rw hf; exact dec_trivial)⟩

def splitting_field_aux_succ {n : ℕ} (α : Type u) (I : discrete_field α) (f : polynomial α)
  (hf : nat_degree f = n + 1)
  (ih : Π {α : Type u} [_inst_4 : discrete_field α] (f : polynomial α), nat_degree f = n →
    (Σ' (β : Type u) [_inst_5 : discrete_field β] (i : α → β) [_inst_6 : is_field_hom i],
    splits i f)) :
  Σ' (β : Type u) [discrete_field β] (i : α → β) [by exactI is_field_hom i],
   by exactI splits i f :=
have hf0 : f ≠ 0, from λ hf0, absurd hf (by rw hf0; exact dec_trivial),
have hdf0 : degree f ≠ 0, from mt nat_degree_eq_of_degree_eq_some (by rw hf; exact dec_trivial),
begin
  resetI,
  let β := ih (f.map (coe : α → adjoin_root (irr_factor f)) / (X - C root))
    (splitting_field.well_founded hf),
  letI := β.2.1, letI := β.2.2.2.1,
  refine ⟨β.1, β.2.1, λ a, β.2.2.1 ↑a, is_ring_hom.comp _ _, _⟩,
  -- proof of splitting property
  { refine (splits_map_iff (coe : α → adjoin_root (irr_factor f)) β.2.2.1).1 _,
    conv {congr, skip, rw ← mul_div_irr_factor_cancel hdf0},
    exact splits_mul _ (splits_of_degree_eq_one _ (degree_X_sub_C _)) β.2.2.2.2 }
end

noncomputable def splitting_field_aux : Π {n : ℕ} {α : Type u} [discrete_field α] (f : by exactI polynomial α)
  (hf : by exactI nat_degree f = n), by exactI Σ' (β : Type u) [discrete_field β] (i : α → β)
  [by exactI is_field_hom i], (by exactI splits i f)
| 0     := splitting_field_aux_zero
| (n+1) := λ α I f hf, splitting_field_aux_succ α I f hf (@splitting_field_aux n)

def type_aux {n : ℕ} (f : polynomial α) (hf : nat_degree f = n) : Type u :=
(splitting_field_aux f hf).1

instance {n : ℕ} (f : polynomial α) (hf : nat_degree f = n) :
  discrete_field (type_aux f hf) :=
(splitting_field_aux f hf).2.1

def mk_aux {n : ℕ} (f : polynomial α) (hf : nat_degree f = n) : α → type_aux f hf :=
(splitting_field_aux f hf).2.2.1

@[instance] lemma is_field_hom_mk_aux {n : ℕ} (f : polynomial α) (hf : nat_degree f = n) :
  is_field_hom (mk_aux f hf) :=
(splitting_field_aux f hf).2.2.2.1

attribute [reducible] splitting_field_aux type_aux splitting_field_aux_succ mk_aux

lemma exists_hom : Π (n : ℕ) {α : Type u} [discrete_field α] (f : by exactI polynomial α)
  (hf : by exactI nat_degree f = n)
  {β : Type v} [discrete_field β] (i : α → β) [by exactI is_field_hom i] (hif : by exactI splits i f),
  ∃ j : by exactI type_aux f hf → β,
  by exactI (∀ x, j (mk_aux f hf x) = i x) ∧
  by letI := (splitting_field_aux f hf).2.1; exact is_field_hom j
| 0     := λ α Iα f hf β Iβ i Ii hsf, by exactI ⟨i, λ x, rfl, Ii⟩
| (n+1) := λ α Iα f hf β Iβ i Ii hsf, begin
  resetI,
  have hdf0 : degree f ≠ 0, from mt nat_degree_eq_of_degree_eq_some (hf.symm ▸ dec_trivial),
  cases irr_factor_dvd hdf0 with g hg,
  have hf0 : f ≠ 0, from λ h, absurd hf (by rw [h, nat_degree_zero]; exact dec_trivial),
  have hif : irreducible (irr_factor f), by apply_instance,
  --show ∃ x, eval₂ j x (irr_factor f) = 0
  cases exists_root_of_splits i
    (splits_of_splits_mul i (λ hfi : irr_factor f * g = 0, absurd hf
        (by rw [hg, hfi, nat_degree_zero]; exact dec_trivial))
      (show splits i (irr_factor f * g), from hg ▸ hsf)).1
    (by rw [ne.def, ← is_unit_iff_degree_eq_zero]; exact hif.1) with x hx,
  have h₁ : splits (lift i x hx) (map coe f / (X - C root)) :=
    (splits_of_splits_mul _
      (show ((X : polynomial (adjoin_root (irr_factor f))) - C root) *
          (f.map coe / (X - C root)) ≠ 0,
        by rw [mul_div_irr_factor_cancel hdf0, ne.def, map_eq_zero]; exact hf0)
      (show splits (lift i x hx) ((X - C root) * (map coe f / (X - C root))),
        by rw [mul_div_irr_factor_cancel hdf0, splits_map_iff (coe : α → adjoin_root (irr_factor f))];
          simp only [lift_of, hsf])).2,
  have wf : nat_degree (map (coe : α → adjoin_root (irr_factor f)) f / (X - C root)) = n,
    from splitting_field.well_founded hf,
  cases exists_hom n _ wf (adjoin_root.lift i x hx) h₁ with k hk,
  dsimp [splitting_field_aux, type_aux, splitting_field_aux_succ, mk_aux],
  exact ⟨k, λ x, by conv_rhs { rw [← @lift_of _ _ _ _ _ _ i _ _ _ x, ← hk.1] }; refl, hk.2⟩,
end

end splitting_field

variable [discrete_field α]

/-- The splitting field of `f` is the "smallest" field extension that splits `f` -/
def splitting_field (f : polynomial α) := splitting_field.type_aux f rfl

namespace splitting_field

instance field (f : polynomial α) : discrete_field (splitting_field f) :=
by unfold splitting_field; apply_instance

def mk (f : polynomial α) : α → splitting_field f := mk_aux f rfl

instance (f : polynomial α) : is_field_hom (mk f) :=
by unfold mk; apply_instance

lemma splitting_field_splits (f : polynomial α) : splits (mk f) f :=
(splitting_field_aux f rfl).2.2.2.2

def lift {β : Type v} [discrete_field β] (i : α → β) [is_field_hom i] (f : polynomial α)
  (hβ : splits i f) : splitting_field f → β :=
classical.some (exists_hom _ f rfl i hβ)

@[instance] lemma lift_is_field_hom {β : Type v} [discrete_field β] (i : α → β) [is_field_hom i]
  (f : polynomial α) (hβ : splits i f) : is_field_hom (lift i f hβ) :=
(classical.some_spec (exists_hom _ f rfl i hβ)).2

@[simp] lemma lift_fixes {β : Type v} [discrete_field β] (i : α → β) [is_field_hom i]
  (f : polynomial α) (hβ : splits i f) : ∀ x, lift i f hβ (mk f x) = i x :=
(classical.some_spec (exists_hom _ f rfl i hβ)).1

attribute [irreducible] lift splitting_field splitting_field.field splitting_field.mk

end splitting_field

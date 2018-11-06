/-
Copyright (c) 2018 Mario Carneiro and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/

import algebra.module
import order.order_iso
import data.fintype data.polynomial
import linear_algebra.lc
import tactic.tidy
import ring_theory.ideals

open set lattice

namespace submodule
variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β]

def fg (s : submodule α β) : Prop := ∃ t : finset β, submodule.span ↑t = s

theorem fg_def {s : submodule α β} :
  s.fg ↔ ∃ t : set β, finite t ∧ span t = s :=
⟨λ ⟨t, h⟩, ⟨_, finset.finite_to_set t, h⟩, begin
  rintro ⟨t', h, rfl⟩,
  rcases finite.exists_finset_coe h with ⟨t, rfl⟩,
  exact ⟨t, rfl⟩
end⟩

theorem fg_sup {s₁ s₂ : submodule α β}
  (hs₁ : s₁.fg) (hs₂ : s₂.fg) : (s₁ ⊔ s₂).fg :=
let ⟨t₁, ht₁⟩ := fg_def.1 hs₁, ⟨t₂, ht₂⟩ := fg_def.1 hs₂ in
fg_def.2 ⟨t₁ ∪ t₂, finite_union ht₁.1 ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩

variables {γ : Type*} [add_comm_group γ] [module α γ]
variables (f : β →ₗ γ)

theorem fg_map {s : submodule α β} (hs : s.fg) : (s.map f).fg :=
let ⟨t, ht⟩ := fg_def.1 hs in fg_def.2 ⟨f '' t, finite_image _ ht.1, by rw [span_image, ht.2]⟩

variables {δ : Type*} [add_comm_group δ] [module α δ]

theorem fg_prod' {sb : submodule α β} {sc : submodule α γ}
  (hsb : sb.fg) (hsc : sc.fg) : (sb.prod sc).fg :=
let ⟨tb, htb⟩ := fg_def.1 hsb, ⟨tc, htc⟩ := fg_def.1 hsc in
fg_def.2 ⟨prod.inl '' tb ∪ prod.inr '' tc,
  finite_union (finite_image _ htb.1) (finite_image _ htc.1),
  by rw [linear_map.span_inl_union_inr, htb.2, htc.2]⟩

theorem fg_exact {s : submodule α β}
  (hs1 : (s.map f).fg) (hs2 : (s ⊓ f.ker).fg) : s.fg :=
begin
  haveI := classical.dec_eq β, haveI := classical.dec_eq γ,
  cases hs1 with t1 ht1, cases hs2 with t2 ht2,
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y,
  { intros y hy,
    have : y ∈ map f s, { rw ← ht1, exact subset_span hy },
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩,
    exact ⟨x, hx1, hx2⟩ },
  have : ∃ g : γ → β, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y,
  { choose g hg1 hg2,
    existsi λ y, if H : y ∈ t1 then g y H else 0,
    intros y H, split,
    { simp only [dif_pos H], apply hg1 },
    { simp only [dif_pos H], apply hg2 } },
  cases this with g hg, clear this,
  existsi t1.image g ∪ t2,
  rw [finset.coe_union, span_union, finset.coe_image],
  apply le_antisymm,
  { refine sup_le (span_le.2 $ image_subset_iff.2 _) (span_le.2 _),
    { intros y hy, exact (hg y hy).1 },
    { intros x hx, have := subset_span hx,
      rw ht2 at this,
      exact this.1 } },
  intros x hx,
  have : f x ∈ map f s, { rw mem_map, exact ⟨x, hx, rfl⟩ },
  rw [← ht1, mem_span_iff_lc] at this,
  rcases this with ⟨l, hl1, hl2⟩,
  refine mem_sup.2 ⟨lc.total β ((lc.map g : lc α γ → lc α β) l), _,
    x - lc.total β ((lc.map g : lc α γ → lc α β) l), _, add_sub_cancel'_right _ _⟩,
  { rw mem_span_iff_lc, refine ⟨_, _, rfl⟩,
    rw [← lc.map_supported g, mem_map],
    exact ⟨_, hl1, rfl⟩ },
  rw [ht2, mem_inf], split,
  { apply s.sub_mem hx,
    rw [lc.total_apply, lc.map_apply, finsupp.sum_map_domain_index],
    refine s.sum_mem _,
    { intros y hy, exact s.smul_mem _ (hg y (hl1 hy)).1 },
    { exact zero_smul }, { exact λ _ _ _, add_smul _ _ _ } },
  { rw [linear_map.mem_ker, f.map_sub, ← hl2],
    rw [lc.total_apply, lc.total_apply, lc.map_apply],
    rw [finsupp.sum_map_domain_index, finsupp.sum, finsupp.sum, f.map_sum],
    rw sub_eq_zero,
    refine finset.sum_congr rfl (λ y hy, _),
    rw [f.map_smul, (hg y (hl1 hy)).2],
    { exact zero_smul }, { exact λ _ _ _, add_smul _ _ _ } }
end

end submodule

def is_noetherian (α β) [ring α] [add_comm_group β] [module α β] : Prop :=
∀ (s : submodule α β), s.fg

theorem is_noetherian_prod {α β γ} [ring α] [add_comm_group β] [module α β] [add_comm_group γ] [module α γ]
  (hb : is_noetherian α β) (hc : is_noetherian α γ) : is_noetherian α (β × γ) :=
λ s, submodule.fg_exact (linear_map.snd β γ) (hc _) $
have s ⊓ linear_map.ker (linear_map.snd β γ) ≤ linear_map.range (linear_map.inl β γ),
from λ x ⟨hx1, hx2⟩, ⟨x.1, trivial, prod.ext rfl $ eq.symm $ linear_map.mem_ker.1 hx2⟩,
linear_map.map_comap_eq_self this ▸ submodule.fg_map _ (hb _)

theorem is_noetherian_iff_well_founded
  {α β} [ring α] [add_comm_group β] [module α β] :
  is_noetherian α β ↔ well_founded ((>) : submodule α β → submodule α β → Prop) :=
⟨λ h, begin
  apply order_embedding.well_founded_iff_no_descending_seq.2,
  swap, { apply is_strict_order.swap },
  rintro ⟨⟨N, hN⟩⟩,
  let M := ⨆ n, N n,
  rcases submodule.fg_def.1 (h M) with ⟨t, h₁, h₂⟩,
  have hN' : ∀ {a b}, a ≤ b → N a ≤ N b :=
    λ a b, (le_iff_le_of_strict_mono N (λ _ _, hN.1)).2,
  have : t ⊆ ⋃ i, (N i : set β),
  { rw [← submodule.Union_coe_of_directed _ N _],
    { show t ⊆ M, rw ← h₂,
      apply submodule.subset_span },
    { apply_instance },
    { exact λ i j, ⟨max i j,
        hN' (le_max_left _ _),
        hN' (le_max_right _ _)⟩ } },
  simp [subset_def] at this,
  choose f hf using show ∀ x : t, ∃ (i : ℕ), x.1 ∈ N i, { simpa },
  cases h₁ with h₁,
  let A := finset.sup (@finset.univ t h₁) f,
  have : M ≤ N A,
  { rw ← h₂, apply submodule.span_le.2,
    exact λ x h, hN' (finset.le_sup (@finset.mem_univ t h₁ _))
      (hf ⟨x, h⟩) },
  exact not_le_of_lt (hN.1 (nat.lt_succ_self A))
    (le_trans (le_supr _ _) this)
  end,
  begin
    assume h N,
    suffices : ∀ M ≤ N, ∃ s, finite s ∧ M ⊔ submodule.span s = N,
    { rcases this ⊥ bot_le with ⟨s, hs, e⟩,
      exact submodule.fg_def.2 ⟨s, hs, by simpa using e⟩ },
    refine λ M, h.induction M _, intros M IH MN,
    letI := classical.dec,
    by_cases h : ∀ x, x ∈ N → x ∈ M,
    { cases le_antisymm MN h, exact ⟨∅, by simp⟩ },
    { simp [not_forall] at h,
      rcases h with ⟨x, h, h₂⟩,
      have : ¬M ⊔ submodule.span {x} ≤ M,
      { intro hn, apply h₂,
        have := le_trans le_sup_right hn,
        exact submodule.span_le.1 this (mem_singleton x) },
      rcases IH (M ⊔ submodule.span {x})
        ⟨@le_sup_left _ _ M _, this⟩
        (sup_le MN (submodule.span_le.2 (by simpa))) with ⟨s, hs, hs₂⟩,
      refine ⟨insert x s, finite_insert _ hs, _⟩,
      rw [← hs₂, sup_assoc, ← submodule.span_union], simp }
  end⟩

def is_noetherian_ring (α) [ring α] : Prop := is_noetherian α α

theorem ring.is_noetherian_of_fintype (R M) [ring R] [add_comm_group M] [module R M] [fintype M] : is_noetherian R M :=
by letI := classical.dec; exact
assume s, ⟨to_finset s, by rw [finset.coe_to_finset', submodule.span_eq]⟩

theorem ring.is_noetherian_of_zero_eq_one {R} [ring R] (h01 : (0 : R) = 1) : is_noetherian_ring R :=
by haveI := subsingleton_of_zero_eq_one R h01;
   haveI := fintype.of_subsingleton (0:R);
   exact ring.is_noetherian_of_fintype R R

theorem is_noetherian_of_submodule_of_noetherian (R M) [ring R] [add_comm_group M] [module R M] (N : submodule R M)
  (h : is_noetherian R M) : is_noetherian R N :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  convert order_embedding.well_founded (order_embedding.rsymm (submodule.map_subtype.lt_order_embedding N)) h
end

theorem is_noetherian_of_quotient_of_noetherian (R) [ring R] (M) [add_comm_group M] [module R M] (N : submodule R M)
  (h : is_noetherian R M) : is_noetherian R N.quotient :=
begin
  rw is_noetherian_iff_well_founded at h ⊢,
  convert order_embedding.well_founded (order_embedding.rsymm (submodule.comap_mkq.lt_order_embedding N)) h
end

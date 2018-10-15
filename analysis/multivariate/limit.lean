/-
Experimenting with filters, limits, and partial functions.
-/
import data.pfun
import order.filter
import analysis.topology.topological_space
import data.set.basic

/-
Stuff that can go in other places.
-/

variables {α : Type*} {β : Type*} 

namespace set

local attribute [instance] classical.prop_decidable

theorem inter_subset (a b c : set α) : a ∩ b ⊆ c ↔ a ⊆ -b ∪ c :=
begin
  split,
  { intros h x xa, by_cases h' : x ∈ b, simp [h ⟨xa, h'⟩], simp [h'] },
  intros h x, rintro ⟨xa, xb⟩, cases h xa, contradiction, assumption
end 

end set

namespace roption

theorem mem_eq (a : α) (o : roption α) : (a ∈ o) = (∃ h, o.get h = a) :=
rfl

@[simp]
theorem mem_restrict (p : Prop) (o : roption α) (h : p → o.dom) (a : α) : 
  a ∈ restrict p o h ↔ p ∧ a ∈ o :=
begin
  cases o, dsimp [restrict, mem_eq], split,
  { rintro ⟨h₀, h₁⟩, exact ⟨h₀, ⟨_, h₁⟩⟩ },
  rintro ⟨h₀, h₁, h₂⟩, exact ⟨h₀, h₂⟩ 
end

end roption

namespace pfun

@[simp]
theorem mem_restrict (f : α →. β) {s : set α} (h : s ⊆ f.dom) (a : α) (b : β) :
  b ∈ restrict f h a ↔ a ∈ s ∧ b ∈ f a :=
by { simp [restrict], reflexivity }

def res (f : α → β) (s : set α) : α →. β :=
restrict (pfun.lift f) (set.subset_univ s)

theorem mem_res (f : α → β) (s : set α) (a : α) (b : β) :
  b ∈ res f s a ↔ (a ∈ s ∧ f a = b) :=
by { simp [res], split; {intro h, simp [h]} }

theorem dom_eq (f : α →. β) : dom f = { x | ∃ a, a ∈ f x } :=
by { ext, simp [dom, set.mem_def, roption.dom_iff_mem] }

def preimage (f : α →. β) (s : set β) : set α :=
{x | ∃ a ∈ f x, a ∈ s}

lemma preimage_univ (f : α →. β) : f.preimage set.univ = f.dom :=
by simp [ preimage, dom_eq ]

def core (f : α →. β) (s : set β) : set α :=
{x | ∀ a ∈ f x, a ∈ s}

lemma core_mono {f : α →. β} {s t : set β} (h : s ⊆ t) : f.core s ⊆ f.core t :=
by { simp [core], intros x h' a afx, exact h (h' a afx) }

lemma core_inter (f : α →. β) (s t : set β) : 
  f.core (s ∩ t) = f.core s ∩ f.core t :=
by { simp [core], ext, simp [imp_and_distrib, forall_and_distrib] }

lemma mem_core_res (f : α → β) (s : set α) (t : set β) (x : α) : 
  x ∈ core (res f s) t ↔ (x ∈ s → f x ∈ t) :=
begin
  simp [core, mem_res], split,
  { intros h h', apply h _ h', reflexivity},
  intros h y xs fxeq, rw ← fxeq, exact h xs 
end

section
local attribute  [instance] classical.prop_decidable

lemma core_res (f : α → β) (s : set α) (t : set β) : core (res f s) t = -s ∪ f ⁻¹' t :=
by { ext, rw mem_core_res, by_cases h : x ∈ s; simp [h] }

end

end pfun

/-
Extend filters to partial functions.
-/

namespace filter

def pmap (f : α →. β) (l : filter α) : filter β :=
{ sets             := f.core ⁻¹' l.sets,
  univ_sets        := by { simp [pfun.core], apply univ_mem_sets },
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ pfun.core_mono st,
  inter_sets       := by { simp [set.preimage, pfun.core_inter], 
                           exact λ s t, inter_mem_sets } }

@[simp]
def mem_pmap (f : α →. β) (l : filter α) (s : set β) : s ∈ (l.pmap f).sets ↔ f.core s ∈ l.sets :=
iff.refl _

def ptendsto (f : α →. β) (l₁ : filter α) (l₂ : filter β) := l₁.pmap f ≤ l₂

theorem ptendsto_def (f : α →. β) (l₁ : filter α) (l₂ : filter β) :
  ptendsto f l₁ l₂ ↔ ∀ s ∈ l₂.sets, f.core s ∈ l₁.sets :=
iff.refl _

theorem pmap_res (l : filter α) (s : set α) (f : α → β) :
  pmap (pfun.res f s) l = map f (l ⊓ principal s) :=
filter_eq $ 
begin
  apply set.ext, intro t, simp [pfun.core_res], split,
  { intro h, constructor, split, { exact h },
    constructor, split, { reflexivity }, 
    simp [set.inter_distrib_right], apply set.inter_subset_left },
  rintro ⟨t₁, h₁, t₂, h₂, h₃⟩, apply mem_sets_of_superset h₁, rw ← set.inter_subset,
  exact set.subset.trans (set.inter_subset_inter_right _ h₂) h₃ 
end

theorem tendsto_iff_ptendsto (l₁ : filter α) (l₂ : filter β) (s : set α) (f : α → β) :
  tendsto f (l₁ ⊓ principal s) l₂ ↔ ptendsto (pfun.res f s) l₁ l₂ :=
by simp only [tendsto, ptendsto, pmap_res]

theorem tendsto_iff_ptendsto' (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ ptendsto (pfun.res f set.univ) l₁ l₂ :=
by { rw ← tendsto_iff_ptendsto, simp [principal_univ] }

-- for later use

variable [topological_space α]

def at_within (a : α) (s : set α) : filter α := nhds a ⊓ principal (s \ singleton a)

end filter

/-
Operations on set-valued functions, aka partial multifunctions, aka relations.
-/

def rel (α : Type*) (β : Type*):= α → β → Prop

namespace rel

variable (r : rel α β)

def image (s : set α) := { y | ∃ x ∈ s, r x y }

def preimage (s : set β) := { x | ∃ y ∈ s, r x y }

lemma preimage_mono {r : rel α β} {s t : set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
assume x ⟨y, ys, rxy⟩, ⟨y, h ys, rxy⟩

lemma preimage_inter (s t : set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
assume x ⟨y, ⟨ys, yt⟩, rxy⟩, ⟨⟨y, ys, rxy⟩, ⟨y, yt, rxy⟩⟩ 

def core (s : set β) := { x | ∀ y, r x y → y ∈ s}

lemma core_mono {r : rel α β} {s t : set β} (h : s ⊆ t) : r.core s ⊆ r.core t :=
assume y h' x rxy, h (h' x rxy)

lemma core_inter (s t : set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
set.ext (by simp [core, imp_and_distrib, forall_and_distrib])

end rel

/-
Generalize tendsto to relations.
-/

namespace filter 

def rmap (r : rel α β) (f : filter α) : filter β :=
{ sets             := r.core ⁻¹' f.sets,
  univ_sets        := by {simp [rel.core], apply univ_mem_sets},
  sets_of_superset := assume s t hs st, mem_sets_of_superset hs $ rel.core_mono st,
  inter_sets       := by { simp [set.preimage, rel.core_inter], exact λ s t, inter_mem_sets } }

@[simp]
def mem_rmap (r : rel α β) (l : filter α) (s : set β) : s ∈ (l.rmap r).sets ↔ r.core s ∈ l.sets :=
iff.refl _

def rtendsto (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁.rmap r ≤ l₂

theorem rtendsto_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto r l₁ l₂ ↔ ∀ s ∈ l₂.sets, r.core s ∈ l₁.sets :=
iff.refl _

def rcomap (r : rel α β) (f : filter β) : filter α :=
{ sets             := { s | ∃t∈f.sets, r.preimage t ⊆ s },
  univ_sets        := ⟨set.univ, univ_mem_sets, by simp⟩,
  sets_of_superset := assume a b ⟨a', ha', ma'a⟩ ab, ⟨a', ha', set.subset.trans ma'a ab⟩,
  inter_sets       := assume a b ⟨a', ha₁, ha₂⟩ ⟨b', hb₁, hb₂⟩, 
                        ⟨a' ∩ b', inter_mem_sets ha₁ hb₁, 
                          set.subset.trans (@rel.preimage_inter _ _ r _ _) 
                                           (set.inter_subset_inter ha₂ hb₂)⟩ }

@[simp]
def mem_rcomap (r : rel α β) (l : filter β) (s : set α) : 
  s ∈ (l.rcomap r).sets ↔ ∃ t ∈ l.sets, rel.preimage r t ⊆ s :=
iff.refl _

def rtendsto' (r : rel α β) (l₁ : filter α) (l₂ : filter β) := l₁ ≤ l₂.rcomap r

theorem rtendsto'_def (r : rel α β) (l₁ : filter α) (l₂ : filter β) :
  rtendsto' r l₁ l₂ ↔ ∀ s ∈ l₂.sets, r.preimage s ∈ l₁.sets :=
begin
  unfold rtendsto', unfold rcomap, simp [le_def], split,
  { intros h s hs, apply (h _ _ hs (set.subset.refl _)) },
  intros h s t ht h', apply mem_sets_of_superset (h t ht) h'  
end

/- relate relational version to function and partial function versions -/

theorem ptendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α →. β) :
  ptendsto f l₁ l₂ ↔ rtendsto (λ x y, y ∈ f x) l₁ l₂ :=
iff.refl _

theorem tendsto_iff_rtendsto (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto (λ x y, f x = y) l₁ l₂ :=
by { simp [tendsto_def, rtendsto_def, rel.core, set.preimage] }

theorem tendsto_iff_rtendsto' (l₁ : filter α) (l₂ : filter β) (f : α → β) :
  tendsto f l₁ l₂ ↔ rtendsto' (λ x y, f x = y) l₁ l₂ :=
by { simp [tendsto_def, rtendsto'_def, rel.preimage, set.preimage] }

end filter



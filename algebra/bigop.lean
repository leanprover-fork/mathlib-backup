import tactic.ext
import tactic.linarith
import pending_lemmas

open list

variables {R : Type*} {I : Type*} (op : R → R → R) (nil: R)
          (r : list I) (P : I → Prop) [decidable_pred P] (F : I → R)

local infix ` ◆ `:70 := op -- type using \di


/- Starting from `F : I → R`, `r : list I`, a composition law `op` on `R`,
   a element `nil` in R, and a decidable predicate `P` on `I`,
   `apply_bigop op nil r P F` is the big "product", for operation `op`,
   of all `F i` for `i` in `r` if `P i`. All parenthesis are closed after
   inserting `nil` at the very end, like in `(a op (b op (c op nil)))`
   (using infix notation for op) -/
def apply_bigop := foldr (λ i, op (F i)) nil (filter P r)

-- alternate definition : foldr (λ i x, if P i then op (F i) x else x) nil r

/- We now define a notation with many variations depending on the list,
   predicate, operation -/

/- variable in filtered list -/

notation `big[`:0 op`/`:0 nil`]_(`:0 binder `∈` r `|` P:(scoped p, p)`)` F:(scoped f, f) :=
apply_bigop op nil r P F

notation `Σ_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) :=
apply_bigop (+) 0 r P F

notation `Π_(`:0 binder `∈` r `|` P:(scoped p, p) `)` F:(scoped f, f) :=
apply_bigop (*) 1 r P F

/- variable in unfiltered list -/

notation `big[`:0 op `/`:0 nil `]_(`:0 binder `∈` r `)` F:(scoped f, f) :=
apply_bigop op nil r (λ i, true) F

notation `Σ_(`:0 binder `∈` r `)` F:(scoped f, f) :=
apply_bigop (+) 0 r (λ i, true) F

notation `Π_(`:0 binder `∈` r `)` F:(scoped f, f) :=
apply_bigop (*) 1 r (λ i, true) F

/- variable is integers from a to b, b exclued, filtered -/

notation `big[`op`/`:0 nil`]_(`:0 binder`=`a`..`b `|` P:(scoped p, p)`)` F:(scoped f, f) :=
apply_bigop op nil (int.range a b) P F

notation `Σ_(`:0 binder`=`a`..`b `|` P:(scoped p, p)`)` F:(scoped f, f) :=
apply_bigop (+) 0 (int.range a b) P F

notation `Π_(`:0 binder`=`a`..` b `|` P:(scoped p, p)`)` F:(scoped f, f) :=
apply_bigop (*) 1 (int.range a b) P F


/- variable is integers from a to b, b exclued, unfiltered -/

notation `big[`:0 op `/`:0 nil `]_(`:0 binder `=` a `..` b `)` F:(scoped f, f) :=
apply_bigop op nil (int.range a b) (λ i, true) F

notation `Σ_(`:0 binder `=` a `..` b `)` F:(scoped f, f) :=
apply_bigop (+) 0 (int.range a b) (λ i, true) F

notation `Π_(`:0 binder `=` a `..` b `)` F:(scoped f, f) :=
apply_bigop (*) 1 (int.range a b) (λ i, true) F

local notation `?(F` h`)` := if P h then F h else nil

/- First lemmas, without assuming anything on `op` and `nil` -/

@[simp]
lemma big.nil : (big[(◆)/nil]_(i ∈ [] | (P i)) (F i)) = nil :=
by simp [apply_bigop]

lemma big.filter_mem [decidable_pred (λ i, i ∈ r)] :
  (big[(◆)/nil]_(i ∈ r) (F i)) = (big[(◆)/nil]_(i ∈ r | i ∈ r) (F i)) :=
by simp [apply_bigop]

lemma big_cons_true {h} (t) (Ph : P h) :
  (big[(◆)/nil]_(i ∈ h::t | (P i)) (F i)) = F h ◆ (big[(◆)/nil]_(i ∈ t | (P i)) (F i)):=
by simp [apply_bigop, Ph]

lemma big_cons_false {h} (t) (Ph : ¬ P h) :
  (big[(◆)/nil]_(i ∈ h::t | (P i)) (F i)) = (big[(◆)/nil]_(i ∈ t | (P i)) (F i)) :=
by simp [apply_bigop, Ph]

lemma big_rec (K : R → Prop) (Knil : K nil) (Kop : ∀ i x, P i → K x → K ((F i) ◆ x)) :
  K (big[(◆)/nil]_(i ∈ r | (P i)) (F i)) :=
begin
  induction r with h t IH,
  { simp[big.nil, Knil] },
  { by_cases H : P h,
    { simp [big_cons_true, H, Kop _ _ H IH] },
    { simp [big_cons_false, H, IH] } }
end

lemma big_ind (K : R → Prop) (Knil : K nil) (Kop : ∀ x y, K x → K y → K (x ◆ y))
(K_F : ∀ i, P i → K (F i)) :
  K (big[(◆)/nil]_(i ∈ r | (P i)) (F i)) :=
begin
  apply big_rec,
    exact Knil,
  intros i x P_i K_x,
  apply Kop ; tauto
end

lemma big_append_eq_of_not_mem [decidable_eq I] {j} (H : j ∉ r) :
  (big[(◆)/nil]_(i ∈ j::r | ((P i) ∧ i ≠ j)) (F i)) = big[(◆)/nil]_(i ∈ r | (P i)) (F i) :=
begin
  unfold apply_bigop,
  congr' 1,
  rw list.filter_cons_of_neg,
  apply list.filter_congr,
  { intros x x_in,
    simp [show x ≠ j, by { intro H', rw ←H' at H, contradiction }] },
  { finish }
end

-- A version of extensionality where we assume same (◆)/nil and same list
lemma big.ext (P') [decidable_pred P'] (F' : I → R)
  (HP : ∀ i ∈ r, P i ↔ P' i) (HF : ∀ i ∈ r, F i = F' i) :
  (big[(◆)/nil]_(i ∈ r | (P i)) (F i)) = (big[(◆)/nil]_(i ∈ r | (P' i)) (F' i)) :=
begin
  unfold apply_bigop,
  rw list.filter_congr HP,
  apply list.foldr_ext,
  intros _ i_r _,
  simp[HF, mem_filter.1 i_r]
end


lemma big.map {J : Type*} (f : I → J) (P : J → Prop) [decidable_pred P] (F : J → R) :
  (big[(◆)/nil]_(j ∈ map f r | (P j)) (F j)) = (big[(◆)/nil]_(i ∈ r | (P (f i))) (F (f i))) :=
by simp[apply_bigop, filter_map_comm, foldr_map]

--set_option pp.all true

lemma big.empty_range (P : ℤ → Prop) [decidable_pred P] (F : ℤ → R) (a b : ℤ)
  (H : b ≤ a) : (big[(◆)/nil]_(i=a..b | (P i)) (F i)) = nil :=
begin
  convert big.nil op nil P F,
  exact (int.range_eq_nil _ _).2 H
end

lemma big.shift (P : ℤ → Prop) [decidable_pred P] (F : ℤ → R) (a b k : ℤ) :
  (big[(◆)/nil]_(i=a..b | (P i)) (F i)) = (big[(◆)/nil]_(i=(a+k)..(b+k) | (P (i-k))) (F (i-k))) :=
begin
  rw [int.range_shift, big.map],
  congr ; ext ; ring
end

/- Now we go towards assuming (R, op, nil) is a monoid -/

/- Also need to make sure old hierarchy talks to new one.
   Associativity seems ok but we need: -/
instance add_monoid_is_left_id (α : Type*) [add_monoid α] : is_left_id α (+) 0 := ⟨by simp⟩

instance add_monoid_is_right_id (α : Type*) [add_monoid α] : is_right_id α (+) 0 := ⟨by simp⟩


instance monoid_is_left_id (α : Type*) [monoid α] : is_left_id α (*) 1 := ⟨by simp⟩

instance monoid_is_right_id (α : Type*) [monoid α] : is_right_id α (*) 1 := ⟨by simp⟩


section nil_left_id
/- Assuming only that nil is left neutral for op -/
variable [is_left_id R op nil]
open is_left_id

lemma big.cons {h} (t) :
  (big[(◆)/nil]_(i ∈ h::t | (P i)) (F i)) = ?(F h) ◆ (big[(◆)/nil]_(i ∈ t | (P i)) (F i)):=
begin
  by_cases H : P h,
  { simp [H, big_cons_true] },
  { simp [H, big_cons_false, left_id op] }
end
end nil_left_id

section nil_right_id
/- Assuming only that nil is left neutral for op -/
variable [is_right_id R op nil]
open is_right_id

lemma big.one_term (i₀ : I) : (big[(◆)/nil]_(i ∈ [i₀]) F i) = F i₀ :=
by simp [apply_bigop, right_id op]

lemma big.one_term' (i₀ : I) :
  (big[(◆)/nil]_(i ∈ [i₀] | P i) F i) = if P i₀ then F i₀ else nil :=
by by_cases H : P i₀;  simp [H, apply_bigop, right_id op]

end nil_right_id

section left_monoid
/- Assume that (R, op) is almost a monoid with neutral element nil -/

variables [is_left_id R op nil] [is_associative R op]
open is_left_id is_associative

lemma big.append (r₁ r₂ : list I) :
  (big[(◆)/nil]_(i ∈ r₁++r₂ | (P i)) (F i)) =
  (big[(◆)/nil]_(i ∈ r₁ | (P i)) (F i)) ◆ (big[(◆)/nil]_(i ∈ r₂ | (P i)) (F i)) :=
begin
  let Op := λ l, big[(◆)/nil]_(i ∈ l | (P i)) (F i),
  induction r₁ with h t IH,
  { exact (eq.symm $ calc
    Op [] ◆ Op r₂ =  nil ◆ (big[(◆)/nil]_(i ∈ r₂ | P i)F i) : by {dsimp [Op], rw big.nil}
    ... = _ : left_id _ _ )},
  { have : ?(F h) ◆ Op t = Op (h :: t) :=
    eq.symm (big.cons _ _ _ _ _),
    exact calc
    Op (h :: t ++ r₂)
        = Op (h :: (t ++ r₂))      : rfl
    ... = ?(F h) ◆ Op (t ++ r₂)    : big.cons _ _ _ _ _
    ... = ?(F h) ◆ (Op t ◆ Op r₂)  : by simp [Op, IH]
    ... = (?(F h) ◆ Op t) ◆ Op r₂  : eq.symm $ assoc _ _ _ _
    ... = Op (h::t) ◆ Op r₂        : by rw this }
end
end left_monoid

section monoid
variables [is_left_id R op nil] [is_right_id R op nil] [is_associative R op]
open is_left_id is_right_id is_associative

lemma big.concat (i) :
  (big[(◆)/nil]_(j ∈ concat r i | (P j)) (F j)) =
  (big[(◆)/nil]_(j ∈ r | (P j)) (F j)) ◆ (if P i then F i else nil) :=
by simp [big.append,big.one_term']

lemma big.concat_true (i) :
  (big[(◆)/nil]_(i ∈ concat r i) (F i)) =
  (big[(◆)/nil]_(i ∈ r) (F i)) ◆ F i :=
by apply big.concat

lemma big.concat_range_true (F : ℤ → R) {a b : ℤ} (h : a < b) :
  (big[(◆)/nil]_(i =a..b) (F i)) =
  (big[(◆)/nil]_(i =a..b-1) (F i)) ◆ F (b-1) :=
by rw int_range_eq_concat h ; apply big.concat_true

lemma big.commute_through {a : R} (H : ∀ i, P i → a ◆ F i = F i ◆ a) :
  a ◆ (big[(◆)/nil]_(i ∈ r | (P i)) F i) = (big[(◆)/nil]_(i ∈ r | (P i)) (F i)) ◆ a :=
 begin
  let K := λ x, (a ◆ x = x ◆ a),
  change K (big[(◆)/nil]_(i ∈ r | (P i)) F i),
  apply big_ind ; dsimp [K],
  { simp [left_id op, right_id op] },
  { intros x y xop yop,
    rw [assoc op, ←assoc op, xop, ← yop, assoc op]},
  { exact H }
end

lemma big.reverse_of_commute (H : ∀ i j, P i  → P j → F i ◆ F j = F j ◆ F i) :
  (big[(◆)/nil]_(i ∈ r | (P i)) F i) = (big[(◆)/nil]_(i ∈ reverse r | (P i)) (F i)) :=
begin
  induction r with h t IH,
  { simp },
  { rw [big.cons, reverse_cons, ←concat_eq_append, big.concat],
    by_cases Ph : P h,
    { simp only [Ph],
      rw IH,
      apply big.commute_through,
      simp * {contextual := true } },
    { simp [Ph, left_id op, right_id op, IH, H] { contextual := true } } }
end

lemma big.reverse_range_of_commute (P : ℤ → Prop) [decidable_pred P] (F : ℤ → R) (a b : ℤ) (H : ∀ i j, P i  → P j → F i ◆ F j = F j ◆ F i) :
  (big[(◆)/nil]_(i=a..b | (P i)) F i) = (big[(◆)/nil]_(i=a..b | (P (a+b-i-1))) (F (a+b-i-1))) :=
by rw [big.reverse_of_commute _ _ _ _ _ H, reverse_int_range_map_int_range, big.map]

lemma big.gather_of_commute (F G : I → R) [decidable_eq I]
  (H : ∀ n n' (h : n < r.length) (h' : n' < r.length),
    n ≠ n' → F (r.nth_le n h) ◆ G (r.nth_le n' h') = G (r.nth_le n' h') ◆ F (r.nth_le n h)) :
  (big[(◆)/nil]_(i ∈ r) F i) ◆ (big[(◆)/nil]_(i ∈ r) G i) =
  big[(◆)/nil]_(i ∈ r) F i ◆ G i :=
begin
  induction r with a t IH,
  { simp,
    rw left_id op },
  { have key : ∀ i ∈ t, G a ◆ F i = F i ◆ G a,
    { intros i i_in,
      rcases nth_le_of_mem i_in with ⟨n, h, Hn⟩,
      specialize H (n+1) 0 (nat.succ_lt_succ h) (nat.succ_pos _),
      simp at H,
      rw ←Hn,
      exact H.symm },
    simp only [big_cons_true] ,
    conv_lhs {
      rw assoc op,
      congr, skip,
      rw ←assoc op,
      congr,
      rw big.filter_mem,
      rw ←big.commute_through _ _ _ _ _ key,
    },
    rw [assoc op, assoc op, ←big.filter_mem],
    congr,
    apply IH,
    introv neq,
    replace neq : n + 1 ≠ n' + 1 := λ hneq, neq (nat.succ_inj hneq),
    specialize H (n+1) (n'+1) (nat.succ_lt_succ h) (nat.succ_lt_succ h') neq,
    rwa nth_le_cons at H },
end

lemma big.gather_of_commute_int (F G : ℤ → R) (a b) (H : ∀ i j, i ≠ j → F i ◆ G j = G j ◆ F i) :
  (big[(◆)/nil]_(i = a..b) F i) ◆ (big[(◆)/nil]_(i = a..b) G i) = big[(◆)/nil]_(i = a..b) F i ◆ G i :=
begin
  apply big.gather_of_commute,
  introv neq,
  apply H,
  simp [int.range, neq],
end

lemma apply_ite {nil : R} {φ : R → R} (Hnil : φ nil = nil) (h : I) :
  φ (ite (P h) (F h) nil) = ite (P h) (φ (F h)) nil :=
calc
      φ (ite (P h) (F h) nil) = ite (P h) (φ $ F h) (φ nil) : by { by_cases H : P h; simp[H] }
      ... = ite (P h) (φ $ F h) nil : by rw Hnil

lemma big.mph {φ : R → R}
  (Hop : ∀ a b : R, φ (a ◆ b) = φ a ◆ φ b) (Hnil : φ nil = nil) :
  φ (big[(◆)/nil]_(i ∈ r | (P i)) F i) = big[(◆)/nil]_(i ∈ r | (P i)) φ (F i) :=
begin
  induction r with h t IH,
  { simp [big.nil, Hnil] },
  { rw [big.cons, Hop, IH, apply_ite _ _ Hnil, ←(big.cons op nil P _ t)] }
end

lemma big.anti_mph {φ : R → R}
  (Hop : ∀ a b : R, φ (a ◆ b) = φ b ◆ φ a) (Hnil : φ nil = nil) :
  φ (big[(◆)/nil]_(i ∈ r | (P i)) F i) = big[(◆)/nil]_(i ∈ r.reverse | (P i)) φ (F i) :=
begin
  induction r with h t IH,
  { simp [big.nil, Hnil] },
  { rw [big.cons, Hop, apply_ite _ _ Hnil, reverse_cons', concat_eq_append, big.append, IH, big.one_term'] }
end

lemma big.range_anti_mph {φ : R → R} (P : ℤ → Prop) [decidable_pred P] (F : ℤ → R) (a b : ℤ)
  (Hop : ∀ a b : R, φ (a ◆ b) = φ b ◆ φ a) (Hnil : φ nil = nil) :
  φ (big[(◆)/nil]_(i=a..b | (P i)) F i) = big[(◆)/nil]_(i=a..b | (P (a+b-i-1))) φ (F (a+b-i-1)) :=
by rw [big.anti_mph _ _ _ _ _ Hop Hnil, reverse_int_range_map_int_range, big.map]

end monoid

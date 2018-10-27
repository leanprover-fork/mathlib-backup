# Coercions from numbers #

This document is not about coercions in general -- see [section 10.6 of TPIL](https://leanprover.github.io/theorem_proving_in_lean/type_classes.html#coercions-using-type-classes) for a general overview. This is an overview of how to work with the coercions `ℕ → ℤ → ℚ → ℝ → ℂ` (maps which mathemaicians fondly call "the identity function") and also the the natural coercions from `ℤ` to a general ring and so on.

In brief: this document might help if you have three integers `x y z`, a proof that `x * y = z`, and a goal which looks like `↑x * ↑y = ↑z` and which you suspect is a statement about real numbers. 

An overview of what we will cover here:

*) When `simp` works.

*) `int.cast_mul` and how to avoid it

*) What to do when your goal is "mathematically the same as" a hypothesis modulo coercions.

# Overview of the casts

What structure do we need on a general type `α` in order to get a natural
map from `ℕ` to it? Well, if we know `α` has `zero`, `one` and `add` then this would be enough, as we see here:

`example (α : Type) [has_zero α] [has_one α] [has_add α] (n : ℕ) : α := n`

For example, if `α` is a semiring, ring or field, then there's a natural map from `ℕ` to `α`.

```lean
import data.real.basic

example (n : ℕ) : ℝ := n

example (α : Type) [semiring α] (n : ℕ) : α := n
```

Similarly, if `α` has additive inverses, e.g. `α` is a ring or a field, then there is a natural map from `ℤ` to `α`, and if `α` is a characteristic zero division ring (for example `ℝ` or `ℂ`) then there is a natural map from `ℚ` to `α`. There is as far as I know no analogous general construction giving maps from `ℝ` or `ℂ` to general algebraic structures, however there is a coercion from `ℝ` to `ℂ`:

```lean
import data.complex.basic

def from_R_to_C (r : ℝ) : ℂ := r

#print from_R_to_C 
-- def from_R_to_C : ℝ → ℂ := λ (r : ℝ), ↑r
```

Looking at the definition of the function, we see that Lean is using `↑` to mean "use a coercion".

# A subtlety with automatic coercions

Before we go on, let me get this potentially confusing issue out of the way. Because there's a coercion from `ℤ` to `ℝ` one can just write `a : ℝ` if `a` is an integer, and Lean knows you mean the corresponding real number. Watch out for this gotcha though:

```lean
variables (a b : ℤ) 

#check (a + b : ℝ) -- ↑a + ↑b : ℝ
#check ((a + b : ℤ) : ℝ) -- ↑(a + b) : ℝ
```

I was initially surprised that these two terms didn't evaluate to exactly the same thing. What is happening here is that for the first term, Lean knows that the type of `a + b` is supposed to be `ℝ`, so it then decides that the addition we want must be `real.add`, so it then decides that we must want `a` and `b` to be reals, giving us `↑a + ↑b`. In the second term, we explicitly say that we want `a + b` to be treated like an integer, and so Lean does the addition first.

# The problems people have with coercions.

Here are two types of problems that people run into with coercions.

1) They are faced with a goal which is "obvious in maths", e.g.

```
a b : ℤ
⊢ ↑(a + b) = ↑a + ↑b
```

with the goal being an equality of real numbers.

2) They are faced with a goal which is "the same as a hypothesis", or "the same as something they know how to prove", e.g.

```
a b c : ℤ,
H : a + b * c = 12
⊢ ↑a + ↑b * ↑c = 12
```

These situations are different, and you must know how to deal with them both. Before I explain how, here's a passing comment. If you do not actually even *understand* what the goal says, because you have lost track of whether `↑a` means the rational number `a`, or the real number `a` or the complex number `a`, try writing `set_option pp.all true` before your theorem and then taking another look. For example, what was `↑(a + b) = ↑a + ↑b` above might now become around 25 lines of output, starting with

```
⊢ @eq.{1} real
    (@coe.{1 1} int real
       (@coe_to_lift.{1 1} int real
          (@coe_base.{1 1} int real
	  ...
```

and the very first line tells you that the goal is an equality between two real numbers (and the second line indicates that the left hand side of this equality is a coercion from the integers).

### "Obvious in maths" goals.

These should all be provable with `simp`. Examples:

```lean
import data.complex.basic

example (a b : ℤ) : ((a + b : ℤ) : ℝ) = a + b :=
-- ↑(a + b) = ↑a + ↑b
by simp

example (a : ℤ) (b : ℕ) (c : ℚ) (d : ℝ) :
(a : ℂ) + b * c - d = (((a + ((b * c) : ℚ) : ℚ) - d) : ℝ) :=
-- ⊢ ↑a + ↑b * ↑c - ↑d = ↑(↑(↑a + ↑b * c) - d)
by simp
```

If you do want to prove these "by hand" for some reason, then you can write `set_option trace.simplify.rewrite true` before your theorem, see what `simp` is doing, and then mimic it.

```lean
import data.complex.basic

example (a b : ℤ) : ((a + b : ℤ) : ℝ) = a + b := int.cast_add a b

set_option trace.simplify.rewrite true
example (a : ℤ) (b : ℕ) (c : ℚ) (d : ℝ) :
(a : ℂ) + b * c - d = (((a + ((b * c) : ℚ) : ℚ) - d) : ℝ) :=
begin
  rw rat.cast_add,
  rw rat.cast_coe_int,
  rw complex.of_real_sub,
  rw complex.of_real_add,
  rw rat.cast_mul,
  rw complex.of_real_mul,
  rw rat.cast_coe_nat,
  rw complex.of_real_int_cast,
  rw complex.of_real_nat_cast,
  rw complex.of_real_rat_cast,
end
```

The second example shows the difficulties that you face when trying to do this by hand. Some of the lemmas are of this form:

```
rat.cast_add : ∀ (m n : ℚ), ↑(m + n) = ↑m + ↑n
```

This lemma is in the `rat` namespace, and it says that if you are coercing *from* `rat` to somewhere else, then adding and then coercing is the same as coercing and then adding.

But others are of this form:

```lean
complex.of_real_mul : ∀ (r s : ℝ), ↑(r * s) = ↑r * ↑s
```

This lemma is in the `complex` namespace, but it is about coercions *to* the complexes from the reals. Writing code by hand is full of pitfalls like this? Why is this? Is this just poor design? No, it's much more complicated than this. The problem is that the coercions from `nat` to `int`, and from `real` to `complex` are *not* defined as special cases of generic coercions from `nat` to a general semiring or from `real` to a general complete field -- mathlib's designers made a conscious decision to use other more computationally efficient coercions, hence the confusion. The designers are not bothered by this, because `simp` works!

### "I have a hypothesis which says this already" goals

```
example (a b c : ℤ) (H : a + b * c = 12) : (a : ℝ) + b * c = 12 :=
/-
a b c : ℤ,
H : a + b * c = 12
⊢ ↑a + ↑b * ↑c = 12
-/
begin
  have H2 : (a : ℝ) + b * c = ((a + b * c : ℤ) : ℝ) := by simp,
  rw H2,
  rw H,
  simp,
end
```

In this example, a hypothesis says that `a + b * c = 12` (this is a statement about integers), and the goal is to prove a version of this for real numbers. Unfortunately the goal is not `↑(a + b * c) = 12`, each of `a`, `b` and `c` are being coerced individually. However `↑a + ↑b * ↑c = ↑(a + b * c)` is exactly a "trivial in maths" goal which `simp` can prove, and then one can rewrite this and *then* rewrite `H` and get the goal into a form that `simp` can deal with.


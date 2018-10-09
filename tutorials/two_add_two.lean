

/- INTRODUCTION
This tutorial introduces the basics of interactive theorem proving in Lean.
Key points:
- basic boilerplate at the top of the file,
- basic grammar of stating and proving,
- how to interact with the proof assistant.

We will set ourselves the lofty goal of proving 2 + 2 = 4.
-/

/- COMMENTS
As you can see, one can write comments containing arbitrary text
between the delimiters slash-dash and dash-slash.
Alternatively, one can write one-line comments by prepending the line with dash-dash:

    -- This is a one-line comment.
-/

/- TOP OF THE FILE
Typically, the top of a file will look something like this:

    -- Copied from ring_theory/ideals.lean
    import algebra.module tactic.ring linear_algebra.quotient_module

    universes u v
    variables {α : Type u} {β : Type v} [comm_ring α] {a b : α}
    open set function

    local attribute [instance] classical.prop_decidable

1. The first line is an import statement. It imports definitions and lemmas from other files.
These files are either part of the current project, or part of a separate library.
Separate libraries should be added using leanpkg -- a package manager for Lean.
2. The second line introduces two universe levels. These are like Grothendieck universes in ZFC.
3. The third line declares several variables that may be used throughout this file.
In particular, `α` is a type equipped with the structure of a commutative ring, `β` is an arbitrary type,
and `a,b` are two terms of type `α`.
4. The next line opens two namespaces: set and function. This means that one can now call `univ`
instead of `set.univ`: one no longer has to prepend `set` or `function` to the names of lemmas
that one is using. (Unless there is a naming conflict with other open namespaces.)
5. The final line of this header states that this file uses classical logic. This means that we can
the law of excluded middle can be used, so that `p ∨ ¬p` is true for every proposition `p`.

In this tutorial file we don't actually need any of such header lines,
since the natural numbers are part of core Lean.
-/

/- BASIC GRAMMAR
The most important keywords in Lean are:
- definition (or def)
- lemma (or theorem)
- sorry

The first two explain themselves. The third (sorry) is very useful to use as a stop-gap. It is a keyword
that can prove everything, but Lean will remember and output a warning that lemma such-and-such uses sorry.

Besides `definition` there are other keywords to introduce new types, such as `inductive` for inductive types,
and `structure` and `class` (which be have like tuples with named entries).

Let us illustrate the use of these keywords by stating our lemma:
-/

-- lemma two_add_two : 2 + 2 = 4 := sorry

/-
It is a feature of dependent type theory that there is no strict difference between a definition and a lemma.
We can see this in action by dissecting the example above:

lemma           keyword
two_add_two     name of lemma/definition; a term of the type that follows
:               "is a term of"
2 + 2 = 4       type
:=              "defined as"
sorry           proof/definition

-/

/- BASIC INTERACTION
One of the key features of Lean is that it is interactive. If you have opened this file in an editor with Lean support
then you can interact with Lean while proving a lemma. Examples of such editors are VScode, emacs, and CoCalc (online).
This tutorial assumes you are using VScode and have installed the Lean extension for VScode.

In the upper right hand of your editor window there is a group of buttons. The left-most of these is called
"Info view: Display Goal". Click it, or type Ctrl-Shift-Enter.
-/

-- Uncomment the following line and put your cursor on `sorry`.
-- lemma two_add_two : 2 + 2 = 4 := sorry

-- As mentioned above, Lean will warn you that your lemma is using sorry.

-- In the following line, we introduced some errors. Lean will tell you that something is wrong.
-- lema two_add_two : 2 + 2 =  := srry

-- In the following line, we give a non-proof. Lean will figure this out and tell you.
-- lemma two_add_two : 2 + 2 = 4 := nat.add

-- The window with Lean messages will display:
    -- type mismatch, term
    --   nat.add
    -- has type
    --   ℕ → ℕ → ℕ : Type
    -- but is expected to have type
    --   2 + 2 = 4 : Prop

-- nat.add is a function that takes two natural numbers and returns a third (in fact, the sum of the inputs).
-- Therefore it has type `ℕ → ℕ → ℕ`. Lean correctly figures out that this is not what it expects, namely
-- a term of type `2 + 2 = 4`.

/- PROVING OUR GOAL
Finally, let us actually prove that 2 + 2 = 4. In Lean, the natural numbers are set up in a way that is very similar
to Peano arithmetic. This means that there is a natural number called `zero` (and in fact we can just use `0`);
and there is a function `succ : ℕ → ℕ` that sends a natural number to its successor.
So we get

    2 = succ (succ zero)
    4 = succ (succ (succ (succ zero)))

The definition of addition is also done by induction. We can see this using the interaction.
-/

-- Uncomment the following line. It will print something unreadable, but don't worry.
-- #print nat.add

/-
You can look up the actual definition in two ways: Ctrl-click on `nat.add`, or right-click and select
"Go to Definition". This will open a new tab with a file that belongs to core Lean. It will place you
at the definition of nat.add, which reads as follows

    namespace nat
      protected def add : nat → nat → nat
      | a  zero     := a
      | a  (succ b) := succ (add a b)
    
    -- .. some more lines
    end nat -- <- this closes the namespac

But this means that `2 + 2` is notation for

    add (succ (succ zero)) (succ (succ zero)) -- which reduces to
    succ (add (succ (succ zero)) (succ zero)) -- which reduces to
    succ (succ (add (succ (succ zero)) zero)) -- which reduces to
    succ (succ (succ (succ zero)))

for which we can use the notation `4`. In other words, our lemma is true by definition, and we can use
reflexivity of equality to prove it:
-/

lemma two_add_two : 2 + 2 = 4 := rfl

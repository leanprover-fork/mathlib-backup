/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Opposites.
-/

universes u

variables (α : Type u)

def opposite : Type u := α

namespace opposite
variables {α}
def op : α → opposite α := id
def unop : opposite α → α := id
theorem op_inj : function.injective (op : α → opposite α) := λ _ _, id
theorem unop_inj : function.injective (unop : opposite α → α) := λ _ _, id
variables (α)

attribute [irreducible] opposite

instance [has_add α] : has_add (opposite α) :=
{ add := λ x y, op (unop y + unop x) }

instance [add_semigroup α] : add_semigroup (opposite α) :=
{ add_assoc := λ x y z, unop_inj $ eq.symm $ add_assoc (unop z) (unop y) (unop x),
  .. opposite.has_add α }

instance [add_right_cancel_semigroup α] : add_left_cancel_semigroup (opposite α) :=
{ add_left_cancel := λ x y z H, unop_inj $ add_right_cancel $ op_inj H,
  .. opposite.add_semigroup α }

instance [add_left_cancel_semigroup α] : add_right_cancel_semigroup (opposite α) :=
{ add_right_cancel := λ x y z H, unop_inj $ add_left_cancel $ op_inj H,
  .. opposite.add_semigroup α }

instance [add_comm_semigroup α] : add_comm_semigroup (opposite α) :=
{ add_comm := λ x y, unop_inj $ add_comm (unop y) (unop x),
  .. opposite.add_semigroup α }

instance [has_zero α] : has_zero (opposite α) :=
{ zero := op 0 }

instance [add_monoid α] : add_monoid (opposite α) :=
{ zero_add := λ x, unop_inj $ add_zero $ unop x,
  add_zero := λ x, unop_inj $ zero_add $ unop x,
  .. opposite.add_semigroup α, .. opposite.has_zero α }

instance [add_comm_monoid α] : add_comm_monoid (opposite α) :=
{ .. opposite.add_monoid α, .. opposite.add_comm_semigroup α }

instance [has_neg α] : has_neg (opposite α) :=
{ neg := λ x, op $ -(unop x) }

instance [add_group α] : add_group (opposite α) :=
{ add_left_neg := λ x, unop_inj $ add_neg_self $ unop x,
  .. opposite.add_monoid α, .. opposite.has_neg α }

instance [add_comm_group α] : add_comm_group (opposite α) :=
{ .. opposite.add_group α, .. opposite.add_comm_monoid α }

instance [has_mul α] : has_mul (opposite α) :=
{ mul := λ x y, op (unop y * unop x) }

instance [semigroup α] : semigroup (opposite α) :=
{ mul_assoc := λ x y z, unop_inj $ eq.symm $ mul_assoc (unop z) (unop y) (unop x),
  .. opposite.has_mul α }

instance [right_cancel_semigroup α] : left_cancel_semigroup (opposite α) :=
{ mul_left_cancel := λ x y z H, unop_inj $ mul_right_cancel $ op_inj H,
  .. opposite.semigroup α }

instance [left_cancel_semigroup α] : right_cancel_semigroup (opposite α) :=
{ mul_right_cancel := λ x y z H, unop_inj $ mul_left_cancel $ op_inj H,
  .. opposite.semigroup α }

instance [comm_semigroup α] : comm_semigroup (opposite α) :=
{ mul_comm := λ x y, unop_inj $ mul_comm (unop y) (unop x),
  .. opposite.semigroup α }

instance [has_one α] : has_one (opposite α) :=
{ one := op 1 }

instance [monoid α] : monoid (opposite α) :=
{ one_mul := λ x, unop_inj $ mul_one $ unop x,
  mul_one := λ x, unop_inj $ one_mul $ unop x,
  .. opposite.semigroup α, .. opposite.has_one α }

instance [comm_monoid α] : comm_monoid (opposite α) :=
{ .. opposite.monoid α, .. opposite.comm_semigroup α }

instance [has_inv α] : has_inv (opposite α) :=
{ inv := λ x, op $ (unop x)⁻¹ }

instance [group α] : group (opposite α) :=
{ mul_left_inv := λ x, unop_inj $ mul_inv_self $ unop x,
  .. opposite.monoid α, .. opposite.has_inv α }

instance [comm_group α] : comm_group (opposite α) :=
{ .. opposite.group α, .. opposite.comm_monoid α }

instance [distrib α] : distrib (opposite α) :=
{ left_distrib := λ x y z, unop_inj $ add_mul (unop z) (unop y) (unop x),
  right_distrib := λ x y z, unop_inj $ mul_add (unop z) (unop y) (unop x),
  .. opposite.has_add α, .. opposite.has_mul α }

instance [semiring α] : semiring (opposite α) :=
{ zero_mul := λ x, unop_inj $ mul_zero $ unop x,
  mul_zero := λ x, unop_inj $ zero_mul $ unop x,
  .. opposite.add_comm_monoid α, .. opposite.monoid α, .. opposite.distrib α }

instance [ring α] : ring (opposite α) :=
{ .. opposite.add_comm_group α, .. opposite.monoid α, .. opposite.semiring α }

instance [comm_ring α] : comm_ring (opposite α) :=
{ .. opposite.ring α, .. opposite.comm_semigroup α }

instance [zero_ne_one_class α] : zero_ne_one_class (opposite α) :=
{ zero_ne_one := λ h, zero_ne_one $ op_inj h,
  .. opposite.has_zero α, .. opposite.has_one α }

instance [integral_domain α] : integral_domain (opposite α) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y (H : op _ = op (0:α)),
    or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ op_inj H) or.inr or.inl,
  .. opposite.comm_ring α, .. opposite.zero_ne_one_class α }

instance [field α] : field (opposite α) :=
{ mul_inv_cancel := λ x hx, unop_inj $ inv_mul_cancel $ λ hx', hx $ unop_inj hx',
  inv_mul_cancel := λ x hx, unop_inj $ mul_inv_cancel $ λ hx', hx $ unop_inj hx',
  .. opposite.comm_ring α, .. opposite.zero_ne_one_class α, .. opposite.has_inv α }

end opposite

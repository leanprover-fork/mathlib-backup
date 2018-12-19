import algebra.ring data.equiv.basic

variables {R : Type*} {F : Type*}

class is_ring_anti_hom [ring R] [ring F] (f : R → F) : Prop :=
(map_one : f 1 = 1)
(map_mul : ∀ {x y : R}, f (x * y) = f y * f x)
(map_add : ∀ {x y : R}, f (x + y) = f x + f y) 

namespace is_ring_anti_hom

variables [ring R] [ring F] (f : R → F) [is_ring_anti_hom f]

instance : is_add_group_hom f :=
⟨λ _ _, is_ring_anti_hom.map_add f⟩

lemma map_zero : f 0 = 0 :=
is_add_group_hom.zero f

lemma map_neg {x} : f (-x) = -f x :=
is_add_group_hom.neg f x

lemma map_sub {x y} : f (x - y) = f x - f y :=
is_add_group_hom.sub f x y

end is_ring_anti_hom

variables (R F)

structure ring_isom [ring R] [ring F] extends R ≃ F :=
[hom : is_ring_hom to_fun]

namespace ring_isom

variables {R F} [ring R] [ring F] (Hs : ring_isom R F) (x y : R)

instance : has_coe_to_fun (ring_isom R F) :=
⟨_, λ Hs, Hs.to_fun⟩

instance : is_ring_hom Hs := Hs.hom

lemma map_add : Hs (x + y) = Hs x + Hs y :=
is_ring_hom.map_add Hs

lemma map_zero : Hs 0 = 0 :=
is_ring_hom.map_zero Hs

lemma map_neg : Hs (-x) = -Hs x :=
is_ring_hom.map_neg Hs

lemma map_sub : Hs (x - y) = Hs x - Hs y :=
is_ring_hom.map_sub Hs

lemma map_mul : Hs (x * y) = Hs x * Hs y :=
is_ring_hom.map_mul Hs

lemma map_one : Hs 1 = 1 :=
is_ring_hom.map_one Hs

lemma map_neg_one : Hs (-1) = -1 :=
Hs.map_one ▸ Hs.map_neg 1

lemma bijective : function.bijective Hs :=
Hs.to_equiv.bijective

lemma map_zero_iff {x : R} : Hs x = 0 ↔ x = 0 := 
⟨λ H, Hs.bijective.1 $ H.symm ▸ Hs.map_zero.symm,
λ H, H.symm ▸ Hs.map_zero⟩

variables (R)
protected def refl [ring R] : ring_isom R R := 
{ hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  .. equiv.refl R }

end ring_isom

def ring_auto [ring R] := ring_isom R R 

structure ring_anti_isom [ring R] [ring F] extends R ≃ F :=
[anti_hom : is_ring_anti_hom to_fun]

namespace ring_anti_isom 

variables {R F} [ring R] [ring F] (Hs : ring_anti_isom R F) (x y : R)

instance : has_coe_to_fun (ring_anti_isom R F) :=
⟨_, λ Hs, Hs.to_fun⟩

instance : is_ring_anti_hom Hs := Hs.anti_hom

lemma map_add : Hs (x + y) = Hs x + Hs y :=
is_ring_anti_hom.map_add Hs

lemma map_zero : Hs 0 = 0 :=
is_ring_anti_hom.map_zero Hs

lemma map_neg : Hs (-x) = -Hs x :=
is_ring_anti_hom.map_neg Hs

lemma map_sub : Hs (x - y) = Hs x - Hs y :=
is_ring_anti_hom.map_sub Hs

lemma map_mul : Hs (x * y) = Hs y * Hs x :=
is_ring_anti_hom.map_mul Hs

lemma map_one : Hs 1 = 1 :=
is_ring_anti_hom.map_one Hs

lemma map_neg_one : Hs (-1) = -1 :=
Hs.map_one ▸ Hs.map_neg 1

lemma bijective : function.bijective Hs := Hs.to_equiv.bijective

lemma map_zero_iff {x : R} : Hs x = 0 ↔ x = 0 := 
⟨λ H, Hs.bijective.1 $ H.symm ▸ Hs.map_zero.symm,
λ H, H.symm ▸ Hs.map_zero⟩

end ring_anti_isom

def ring_anti_auto [ring R] := ring_anti_isom R R

structure ring_invo [ring R] :=
(to_fun : R → R)
[anti_hom : is_ring_anti_hom to_fun]
(to_fun_to_fun : ∀ x, to_fun (to_fun x) = x)

open ring_invo

namespace ring_invo

variables {R} [ring R] (Hi : ring_invo R) (x y : R)

instance : has_coe_to_fun (ring_invo R) :=
⟨_, λ Hi, Hi.to_fun⟩

instance : is_ring_anti_hom Hi := Hi.anti_hom

def to_ring_anti_auto : ring_anti_auto R :=
{ inv_fun := Hi,
  left_inv := Hi.to_fun_to_fun,
  right_inv := Hi.to_fun_to_fun,
  .. Hi }

lemma map_add : Hi (x + y) = Hi x + Hi y :=
Hi.to_ring_anti_auto.map_add x y

lemma map_zero : Hi 0 = 0 :=
Hi.to_ring_anti_auto.map_zero

lemma map_neg : Hi (-x) = -Hi x :=
Hi.to_ring_anti_auto.map_neg x

lemma map_sub : Hi (x - y) = Hi x - Hi y :=
Hi.to_ring_anti_auto.map_sub x y

lemma map_mul : Hi (x * y) = Hi y * Hi x :=
Hi.to_ring_anti_auto.map_mul x y

lemma map_one : Hi 1 = 1 :=
Hi.to_ring_anti_auto.map_one

lemma map_neg_one : Hi (-1) = -1 :=
Hi.to_ring_anti_auto.map_neg_one

lemma bijective : function.bijective Hi :=
Hi.to_ring_anti_auto.bijective

lemma map_zero_iff {x : R} : Hi x = 0 ↔ x = 0 := 
Hi.to_ring_anti_auto.map_zero_iff

end ring_invo

section comm_ring
variables (R F) [comm_ring R] [comm_ring F]

protected def ring_invo.id : ring_invo R :=
{ anti_hom := ⟨rfl, mul_comm, λ _ _, rfl⟩,
  to_fun_to_fun := λ _, rfl,
  .. equiv.refl R }

protected def ring_anti_isom.refl : ring_anti_isom R R :=
(ring_invo.id R).to_ring_anti_auto

variables {R F}

theorem comm_ring.hom_to_anti_hom (f : R → F) [is_ring_hom f] : is_ring_anti_hom f :=
{ map_add := λ _ _, is_ring_hom.map_add f,
  map_mul := λ _ _, by rw [is_ring_hom.map_mul f, mul_comm],
  map_one := is_ring_hom.map_one f}

theorem comm_ring.anti_hom_to_hom (f : R → F) [is_ring_anti_hom f] : is_ring_hom f :=
{ map_add := λ _ _, is_ring_anti_hom.map_add f,
  map_mul := λ _ _, by rw [is_ring_anti_hom.map_mul f, mul_comm],
  map_one := is_ring_anti_hom.map_one f}

def comm_ring.isom_to_anti_isom (Hs : ring_isom R F) : ring_anti_isom R F :=
{ anti_hom := comm_ring.hom_to_anti_hom Hs,
  .. Hs.to_equiv }

def comm_ring.anti_isom_to_isom (Hs : ring_anti_isom R F) : ring_isom R F :=
{ hom := comm_ring.anti_hom_to_hom Hs,
  .. Hs.to_equiv }

end comm_ring

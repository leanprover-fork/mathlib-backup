import algebra.ring data.equiv.basic

open ring

structure ring_isom (R : Type*) (F : Type*) [ring R] [ring F] extends equiv R F := 
(isom_is_hom : is_ring_hom (equiv.to_fun to_equiv))

namespace ring_isom

variables {R : Type*} {F : Type*} [ring R] [ring F] (Hs : ring_isom R F) (x y : R)

open ring_isom

def isom := (equiv.to_fun Hs.to_equiv)

instance : is_ring_hom (isom Hs) := ring_isom.isom_is_hom Hs 

def map_add :
isom Hs (x + y) = isom Hs x + isom Hs y := is_ring_hom.map_add (isom Hs)

def map_mul :
isom Hs (x * y) = isom Hs x * isom Hs y := is_ring_hom.map_mul (isom Hs)

def map_one :
isom Hs (1) = 1 := is_ring_hom.map_one (isom Hs)

lemma bijective : 
function.bijective (isom Hs) := equiv.bijective Hs.to_equiv

lemma map_zero : 
isom Hs (0 : R) = 0 :=
exists.elim 
    ((bijective Hs).right 0) 
    (λ a H, 
    have He : (isom Hs a) * (isom Hs 0) = 0, 
        from (eq_comm.mp H) ▸ (ring.zero_mul (isom Hs 0)),
    (ring.mul_zero a) ▸ ((eq_comm.mp (map_mul Hs a 0)) ▸ He))

lemma map_zero_iff {x : R} :
isom Hs x = 0 ↔ x = 0 := 
⟨ λ H, (function.injective.eq_iff (bijective Hs).left).mp ((eq_comm.mp (map_zero Hs)) ▸ H), 
  λ H, (eq_comm.mp H) ▸ (map_zero Hs) ⟩ 

lemma map_neg : 
isom Hs (-x) = -isom Hs x :=
have H : isom Hs (-x + x) = 0, 
    from eq_comm.mp (neg_add_self x) ▸ map_zero Hs,
add_eq_zero_iff_eq_neg.mp ((map_add Hs (-x) x) ▸ H) 

lemma map_neg_one : 
isom Hs (-1) = -1 := (map_one Hs) ▸ (map_neg Hs 1)

end ring_isom

def ring_auto {R : Type*} [ring R] := ring_isom R R 

class is_ring_anti_hom {R : Type*} {F :Type*} [ring R] [ring F] (f : R → F) : Prop := 
(map_add : ∀ {x y : R}, f (x + y) = f x + f y) 
(map_mul : ∀ {x y : R}, f (x * y) = f y * f x)
(map_one : f 1 = 1)

structure ring_anti_isom (R : Type*) (F : Type*) [ring R] [ring F] extends equiv R F := 
(anti_isom_is_anti_hom : is_ring_anti_hom (equiv.to_fun to_equiv))

namespace ring_anti_isom 

variables {R : Type*} {F : Type*} [ring R] [ring F] (Hs : ring_anti_isom R F) (x y : R)

open ring_anti_isom

def anti_isom  := (equiv.to_fun Hs.to_equiv)

instance : is_ring_anti_hom (anti_isom Hs) := ring_anti_isom.anti_isom_is_anti_hom Hs 

def map_add :
anti_isom Hs (x + y) = anti_isom Hs x + anti_isom Hs y := is_ring_anti_hom.map_add (anti_isom Hs) 

def map_mul :
anti_isom Hs (x * y) = anti_isom Hs y * anti_isom Hs x := is_ring_anti_hom.map_mul (anti_isom Hs)

def map_one :
anti_isom Hs (1) = 1 := is_ring_anti_hom.map_one (anti_isom Hs)

lemma bijective : 
function.bijective (anti_isom Hs) := equiv.bijective Hs.to_equiv

lemma map_zero : 
anti_isom Hs 0 = 0 :=
exists.elim 
    ((bijective Hs).right 0) 
    (λ a H, 
    have He : (anti_isom Hs 0) * (anti_isom Hs a) = 0, 
        from (eq_comm.mp H) ▸ (ring.mul_zero (anti_isom Hs 0)),
    (ring.mul_zero a) ▸ ((eq_comm.mp (ring_anti_isom.map_mul Hs a 0)) ▸ He)) 

lemma map_zero_iff {x : R} :
anti_isom Hs x = 0 ↔ x = 0 := 
⟨ λ H, (function.injective.eq_iff (bijective Hs).left).mp ((eq_comm.mp (map_zero Hs)) ▸ H), 
  λ H, (eq_comm.mp H) ▸ (map_zero Hs) ⟩ 

lemma map_neg : 
anti_isom Hs (-x) = -anti_isom Hs x :=
have H : anti_isom Hs (-x + x) = 0, 
    from eq_comm.mp (neg_add_self x) ▸ map_zero Hs,
add_eq_zero_iff_eq_neg.mp ((ring_anti_isom.map_add Hs (-x) x) ▸ H) 

lemma map_neg_one : 
anti_isom Hs (-1) = -1 := (ring_anti_isom.map_one Hs) ▸ (map_neg Hs 1) 

end ring_anti_isom

def comm_ring.hom_to_anti_hom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (f : R → F) [is_ring_hom f] :
is_ring_anti_hom f :=
{ map_add := λ {x y : R}, is_ring_hom.map_add f,
  map_mul := begin intros, have He : mul x y = x * y, refl, rw He, rw mul_comm, rw is_ring_hom.map_mul f, refl, end,
  map_one := is_ring_hom.map_one f}

def comm_ring.anti_hom_to_hom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (f : R → F) [is_ring_anti_hom f] :
is_ring_hom f :=
{ map_add := λ {x y : R}, is_ring_anti_hom.map_add f,
  map_mul := begin begin intros, have He : mul x y = x * y, refl, rw He, rw mul_comm, rw is_ring_anti_hom.map_mul f, refl, end, end,
  map_one := is_ring_anti_hom.map_one f}

instance ring_isom.to_is_ring_hom {R : Type*} {F : Type*} [ring R] [ring F] (Hs : ring_isom R F) : 
is_ring_hom Hs.to_equiv.to_fun := Hs.isom_is_hom

instance ring_anti_isom.to_is_ring_anti_hom {R : Type*} {F : Type*} [ring R] [ring F] (Hs : ring_anti_isom R F) : 
is_ring_anti_hom Hs.to_equiv.to_fun := Hs.anti_isom_is_anti_hom

def comm_ring.isom_to_anti_isom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (Hs : ring_isom R F) : 
ring_anti_isom R F := 
{ to_equiv := Hs.to_equiv,
  anti_isom_is_anti_hom := comm_ring.hom_to_anti_hom (ring_isom.isom Hs)}

def comm_ring.anti_isom_to_isom {R : Type*} {F : Type*} [comm_ring R] [comm_ring F] (Hs : ring_anti_isom R F) : 
ring_isom R F := 
{ to_equiv := Hs.to_equiv,
  isom_is_hom := comm_ring.anti_hom_to_hom (ring_anti_isom.anti_isom Hs)}

def ring_anti_auto {R : Type*} [ring R] := ring_anti_isom R R

structure ring_invo (R : Type*) [ring R] extends ring_anti_isom R R :=
(invo_comp_self : ∀ (x : R), (equiv.to_fun to_equiv) (((equiv.to_fun to_equiv) x)) = x)

open ring_invo

namespace ring_invo

variables {R : Type*} [ring R] (Hi : ring_invo R) (x y : R)

def invo := equiv.to_fun (ring_anti_isom.to_equiv Hi.to_ring_anti_isom) 

def map_add :
invo Hi (x + y) = invo Hi (x) + invo Hi (y) := ring_anti_isom.map_add (Hi.to_ring_anti_isom) x y

def map_mul :
invo Hi (x * y) = invo Hi (y) * invo Hi (x) := ring_anti_isom.map_mul (Hi.to_ring_anti_isom) x y

def map_one : 
invo Hi (1 : R) = 1 := ring_anti_isom.map_one (Hi.to_ring_anti_isom) 

def invo_invo :
invo Hi (invo Hi (x)) = x := invo_comp_self Hi x
 
def bijective : 
function.bijective (invo Hi) := equiv.bijective (ring_invo.to_ring_anti_isom Hi).to_equiv

def map_zero : 
invo Hi (0 : R) = 0 := ring_anti_isom.map_zero (Hi.to_ring_anti_isom)

def map_zero_iff {x : R} :
invo Hi x = 0 ↔ x = 0 := ring_anti_isom.map_zero_iff (Hi.to_ring_anti_isom)

def map_neg : 
invo Hi (-x) = -(invo Hi x) := ring_anti_isom.map_neg (Hi.to_ring_anti_isom) x

def map_neg_one : 
invo Hi (-1 : R) = -1 := ring_anti_isom.map_neg_one (Hi.to_ring_anti_isom)

end ring_invo
set_option trace.simplify true

def id_is_equiv (R : Type*) : equiv R R := 
⟨id, id, λ x, by rw [id.def, id.def], λ x, by rw [id.def, id.def]⟩ 

def id_is_isom (R : Type*) [ring R] : ring_isom R R := 
⟨ id_is_equiv R, 
  λ (x y : R), by dunfold id_is_equiv; simp only [id.def], 
  by dunfold id_is_equiv; simp, 
  by dunfold id_is_equiv; simp only [id.def]⟩

def id_is_anti_isom (R : Type*) [comm_ring R] : ring_anti_isom R R := comm_ring.isom_to_anti_isom (id_is_isom R) 

def id_is_invo (R : Type*) [comm_ring R] : ring_invo R :=
⟨ id_is_anti_isom R, 
  begin 
    dunfold id_is_anti_isom id_is_isom id_is_equiv comm_ring.isom_to_anti_isom, 
    simp, 
  end⟩ 

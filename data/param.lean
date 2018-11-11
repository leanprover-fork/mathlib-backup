/-
Copyright (c) 2016 Cyril Cohen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
author: Cyril Cohen <cyril.cohen@inria.fr>
with contributions and help from Robert Y. Lewis <rob.y.lewis@gmail.com>
and Johannes Hölzl <johannes.hoelzl@gmx.de>

Binary parametricity translation (WIP)

the translation is adapted from
/Parametricity in an Impredicative Sort/
by Chantal Keller and Marc Lasson
in Computer Science Logic 2012 (CSL’12).
-/

import tactic
open expr native tactic
open lean.parser interactive

meta def expr.instantiate_lam (nv : expr) : expr → expr
| (lam nm bi tp bd) := bd.instantiate_var nv
| e := app e nv

meta def expr.mk_subst_or_app : expr → list expr → expr
| e []      := e
| e (x::xs) := (x.instantiate_lam e).mk_subst_or_app xs

private def bid := binder_info.default

meta def expr.strip_lam : expr → nat → option expr
| (lam _ _ _ bd) (nat.succ n) := bd.strip_lam n
| t 0 := return t
| _ _ := none

meta def name.ext (ext : string) (x : name) : name :=
  (x.to_string ++ ext : string)

meta def param.intro (lconsts : name_map (expr × expr × expr))
    (x : name) (α0 α1 αR : expr) (body : expr) :
      tactic ((expr × expr × expr) × name_map (expr × expr × expr) × expr) := do
  uniq_name0 ← mk_fresh_name,
  let fresh0 := expr.local_const uniq_name0 (x.ext "0") bid α0,
  fresh1 ← mk_local_def (x.ext "1") α1,
  freshR ← mk_local_def (x.ext "R") (αR.mk_subst_or_app [fresh0, fresh1]),
  let freshs := (fresh0, fresh1, freshR),
  return (freshs, lconsts.insert uniq_name0 freshs, body.instantiate_var fresh0)

meta def expr.abstract_ : (name → binder_info → expr → expr → expr) →
  expr → expr → expr
| k e (expr.local_const n m bi α) := k m bi α (e.abstract_local n)
| k e _                           := e

meta def name.param (n : nat) (x : name) : name :=
  "param" ++ to_string n ++ x

meta def expr.param' (p := 2) : expr → name_map (expr × expr × expr) →
  tactic (expr × expr × expr)
| (var         db)  _ := fail $ "expr.param: cannot translate a var"
| (sort        lvl) _ := do
  return (sort lvl, sort lvl,
    lam "α0" bid (sort lvl) $ lam "α1" bid (sort lvl) $
    pi "x0" bid (var 1) $ pi "x1" bid (var 1) $ sort lvl)
| c@(const       x lvls) _ := do
   env ← get_env,
   if env.is_recursor x then
   match env.inductive_type_of x with
   | none := do
     trace $ "expr.param: " ++ to_string x ++ " has no inductive_type_of",
     fail "STOP"
   | (some i) := do
     trace $ "expr.param: " ++ to_string x ++ " not yet implemented",
     fail "STOP"
   end
   else return (c, c, const (x.param p) lvls)
| c@(local_const x pry binfo α) lconsts := lconsts.find x
| (app         u v) lconsts := do
  (u0, u1, uR) ← u.param' lconsts,
  (v0, v1, vR) ← v.param' lconsts,
  trace $ "u= " ++ to_string u ++ ";   uR= " ++ to_string uR,
  return (app u0 v0, app u1 v1, uR v0 v1 vR)
| (lam         x binfo α body) lconsts := do
  (α0, α1, αR) ← α.param' lconsts,
  ((x0, x1, xR), lconstsx, bodyx) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← bodyx.param' lconstsx,
  let t0 := body0.abstract_ lam x0,
  let t1 := body1.abstract_ lam x1,
  let tR := ((bodyR.abstract_ lam xR).abstract_ lam x1).abstract_ lam x0,
  return (t0, t1, tR)
| (pi          x binfo α body) lconsts := do
  (α0, α1, αR) ← α.param' lconsts,
  ((x0, x1, xR), lconstsx, bodyx) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← bodyx.param' lconstsx,
  let t0 := body0.abstract_ pi x0,
  let t1 := body1.abstract_ pi x1,
  f0 ← mk_local_def "f0" t0,
  f1 ← mk_local_def "f1" t1,
  let tR := (((((bodyR.mk_subst_or_app [f0 x0, f1 x1]
     ).abstract_ pi xR).abstract_ pi x1).abstract_ pi x0
     ).abstract_ lam f1).abstract_ lam f0,
  return (t0, t1, tR)
| (elet        x α val body) lconsts := fail $
  "param': elet not implemented"
  -- [WRONG CODE!!!]
  -- (α0, α1, αR) ← α.param',
  -- (val0, val1, valR) ← val.param',
  -- (body0, body1, bodyR) ← body.param',
  -- let t0_ := elet (x.ext "0") α0 val0,
  -- let t1_ := elet (x.ext "1") α1 val1,
  -- let tR := t0_ $ t1_ $ elet (x.ext "R") stripped_αR valR bodyR,
  -- return (t0_ body0, t1_ body1, tR)
  -- [/WRONG CODE!!!]
| exp@_ _ := fail $
  "expr.param': expression " ++ exp.to_string ++ " is not translatable"

meta def expr.param (t : expr) (p := 2) (lconst := mk_name_map) :=
  expr.param' p t lconst

#print declaration

-- could replace the consts argument with

meta def param.inductive (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  ind_decl ← get_decl n,
  guard $ env.is_inductive n,
  let ctors := env.constructors_of n,
  let nparams := env.inductive_num_params n,
  let indices := env.inductive_num_indices n,
  let univs := ind_decl.univ_params,
  let lvls := univs.map level.param,
  i ← return $ const n lvls,
  let ty := ind_decl.type,
  trace lvls,
  (ty0, ty1, tyR) ← ty.param p,
  ctorsR ← ctors.mmap (λ n : name, do
    decl ← get_decl n,
    c ← return $ const n lvls,
    let ty := decl.type,
    (ty0, ty1, tyR) ← ty.param p,
    return (n.param p, tyR.mk_subst_or_app [c, c])),
  trace ctors,
  trace $ to_string (tyR.mk_subst_or_app [i, i]),
  trace $ to_string ctorsR,
  add_inductive (n.param p) univs ((p + 1) * nparams)
    (tyR.mk_subst_or_app [i, i]) ctorsR

meta def param.def (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  guard $ env.is_definition n,
  decl ← env.get n,
  match decl with
  | (declaration.defn _ univs α body _ _) := do
    (_, _, αR) ← α.param 2,
    (_, _, bodyR) ← body.param 2,
    let lvls := univs.map level.param,
    d ← return $ const n lvls,
    let tyR := αR.mk_subst_or_app [d, d],
    trace tyR,
    trace bodyR,
    add_decl $ mk_definition (n.param 2) univs tyR bodyR
  | _ := fail $ "param.def:  not a definition"
  end

meta def param.decl (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  if env.is_inductive n then param.inductive p n
  else if env.is_definition n then param.def p n
  else fail $ "translate: cannot translate " ++ to_string n

@[user_command]
meta def param_cmd (_ : parse $ tk "#param") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.decl 2)

----------------------
-- Working examples --
----------------------

#param punit pprod bool nat and or list
#param has_zero has_one has_neg has_add has_mul

#check param.«2».bool
#print nat.rec
#print param.«2».nat.rec
#print nat.succ
#print param.«2».nat.succ
#print param.«2».punit

#print nat.below

--------------------------
-- Not working examples --
--------------------------

#param nat.below

universe l
def nat.rec.type := Π {C : ℕ → Sort l}, C 0 → (Π (n : ℕ), C n → C (nat.succ n)) → Π (n : ℕ), C n

#print nat.rec.type
#param nat.rec.type

def param.«2».nat.rec.type : nat.rec.type → nat.rec.type → Sort (imax (max 1 (l+1)) l 1 l) :=
  λ (f0 f1 : Π (C0 : ℕ → Sort l), C0 0 → (Π (n0 : ℕ), C0 n0 → C0 (nat.succ n0)) → Π (n0 : ℕ), C0 n0),
  Π (C0 C1 : ℕ → Sort l) (CR : Π (a0 a1 : ℕ), param.«2».nat a0 a1 → C0 a0 → C1 a1 → Sort l) (a0 : C0 0)
  (a1 : C1 0),
    CR 0 0 (param.«2».has_zero.zero ℕ ℕ param.«2».nat nat.has_zero nat.has_zero param.«2».nat.has_zero) a0
      a1 →
    Π (a0_1 : Π (n0 : ℕ), C0 n0 → C0 (nat.succ n0)) (a1_1 : Π (n1 : ℕ), C1 n1 → C1 (nat.succ n1)),
      (Π (n0 n1 : ℕ) (nR : param.«2».nat n0 n1) (a0 : C0 n0) (a1 : C1 n1),
         CR n0 n1 nR a0 a1 →
         CR (nat.succ n0) (nat.succ n1) (param.«2».nat.succ n0 n1 nR) (a0_1 n0 a0) (a1_1 n1 a1)) →
      Π (n0 n1 : ℕ) (nR : param.«2».nat n0 n1), CR n0 n1 nR (f0 C0 a0 a0_1 n0) (f1 C1 a1 a1_1 n1)





def param.«2».nat.below : Π (C0 C1 : ℕ → Sort l),
  (Π (n0 n1 : ℕ), param.«2».nat n0 n1 → C0 n0 → C1 n1 → Sort l) →
  Π (n0 n1 : ℕ), param.«2».nat n0 n1 → nat.below C0 n0 → nat.below C1 n1 → Sort (max 1 l) :=
λ (C0 C1 : ℕ → Sort l) (CR : Π (n0 n1 : ℕ), param.«2».nat n0 n1 → C0 n0 → C1 n1 → Sort l)
(n0 n1 : ℕ) (nR : param.«2».nat n0 n1),

param.«2».nat.rec  (λ (n0 : ℕ), Sort (max 1 l)) (λ (n1 : ℕ), Sort (max 1 l))
    (λ (n0 n1 : ℕ) (nR : param.«2».nat n0 n1)
    (α0 α1 : Sort (max 1 l)), α0 → α1 → Sort (max 1 l))
    param.«2».punit
    (λ (n0 : ℕ) (ih0 : Sort (max 1 l)), pprod (pprod (C0 n0) ih0) punit)
    (λ (n1 : ℕ) (ih1 : Sort (max 1 l)), pprod (pprod (C1 n1) ih1) punit)
    (λ (n0 n1 : ℕ) (nR : param.«2».nat n0 n1) (ih0 ih1 : Sort (max 1 l)) (ihR : ih0 → ih1 → Sort (max 1 l)),
       param.«2».pprod (pprod (C0 n0) ih0) (pprod (C1 n1) ih1)
         (param.«2».pprod (C0 n0) (C1 n1) (CR n0 n1 nR) ih0 ih1 ihR)
         punit
         punit
         param.«2».punit)
    n0
    n1
    nR

run_cmd do
  let e := `(λ α : Type, λ x : α, x),
  let t := `(∀ α : Type, α → α),
  (t0,t1,tR) ← t.param 2,
  (e0,e1,eR) ← e.param 2,
  teR ← infer_type eR,
  unify teR (tR.mk_app [e, e])

#exit

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

#check mk_const

meta def expr.param' (p := 2) : expr → name_map (expr × expr × expr) →
  tactic (expr × expr × expr)
| (var         db)  _ := fail $ "expr.param: cannot translate a var"
| (sort        lvl) _ := do
  return (sort lvl, sort lvl,
    lam "α0" bid (sort lvl) $ lam "α1" bid (sort lvl) $
    pi "x0" bid (var 1) $ pi "x1" bid (var 1) $ sort lvl)
| c@(const       x lvls) _ := do
   trace $ "lvls(" ++ to_string x ++ ")=" ++ to_string lvls,
   ls   ← mk_num_meta_univs lvls.length,
   return (c, c, const (x.param p) ls)
| c@(local_const x pry binfo α) lconsts := lconsts.find x
| (app         u v) lconsts := do
  (u0, u1, uR) ← u.param' lconsts,
  (v0, v1, vR) ← v.param' lconsts,
  return (app u0 v0, app u1 v1, uR.mk_app [v0, v1, vR])
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
  let tR := (((((bodyR.mk_subst_or_app [app f0 x0, app f1 x1]
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

meta def expr.param (p := 2) (t : expr) (lconst := mk_name_map) :=
  expr.param' p t lconst

-- could replace the consts argument with
meta def param.inductive (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  ind_decl ← get_decl n,
  guard $ env.is_inductive n,
  i ← mk_const n,
  let ctors := env.constructors_of n,
  let nparams := env.inductive_num_params n,
  let indices := env.inductive_num_indices n,
  let ty := ind_decl.type,
  (ty0, ty1, tyR) ← ty.param p,
  ctorsR ← ctors.mmap (λ n : name, do
    decl ← get_decl n,
    c ← mk_const n,
    let ty := decl.type,
    (ty0, ty1, tyR) ← ty.param p,
    return (n.param p, tyR.mk_subst_or_app [c, c])),
  trace ctors,
  trace ctorsR,
  trace (tyR.mk_subst_or_app [i, i]),
  add_inductive (n.param p) ind_decl.univ_params ((p + 1) * nparams)
    (tyR.mk_subst_or_app [i, i]) ctorsR

meta def param.def (p := 2) (n : name) : tactic unit := do
  env ← get_env,
  guard $ env.is_definition n,
  decl ← env.get n,
  match decl with
  | (declaration.defn _ lvls α body _ _) := do
    (_, _, αR) ← α.param 2,
    (_, _, bodyR) ← body.param 2,
    trace αR,
    trace bodyR,
    add_decl $ mk_definition (n.param 2) lvls αR bodyR
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

#param bool nat

#check param.«2».bool
#print param.«2».nat.rec

#print and

#param and


--------------------------
-- Not working examples --
--------------------------
universes u v w

#print punit


#param punit

-- handmade def
inductive param.«2».punit : punit → punit → Type u
| star : param.«2».punit punit.star punit.star

#print param.«2».punit

#print pprod

#param pprod

inductive param.«2».pprod : Π (α0 α1 : Type u), (α0 → α1 → Type u) →
  Π (β0 β1 : Type v), (β0 → β1 → Type v) →
  pprod α0 β0 → pprod α1 β1 → Type ((max 1 u v) + 1)
| mk : Π (α0 α1 : Type u) (αR : α0 → α1 → Type u) (β0 β1 : Type v) (βR : β0 → β1 → Type v)
  (fst0 : α0) (fst1 : α1), αR fst0 fst1 →
    Π (snd0 : β0) (snd1 : β1),
      βR snd0 snd1 → param.«2».pprod α0 α1 αR β0 β1 βR ⟨fst0, snd0⟩ ⟨fst1, snd1⟩

#param prod

#param bool.size_of


#print nat.below

#param nat.below

run_cmd do
  let e := `(λ α : Type, λ x : α, x),
  let t := `(∀ α : Type, α → α),
  (t0,t1,tR) ← t.param 2,
  (e0,e1,eR) ← e.param 2,
  teR ← infer_type eR,
  unify teR (tR.mk_app [e, e])

#exit

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

meta def name.param (n : nat) (x : name) : name := "param" ++ to_string n ++ x

meta def expr.param (p := 2) : expr → name_map (expr × expr × expr) →
  tactic (expr × expr × expr)
| (var         db)  _ := fail $ "param: cannot translate a var"
| (sort        lvl) _ :=
  return (sort lvl, sort lvl,
    lam "α0" bid (sort lvl) $ lam "α1" bid (sort lvl) $
    pi "x0" bid (var 1) $ pi "x1" bid (var 1) $ sort lvl)
| c@(const       x lvls) _ := do
   cR ← mk_const (x.param p),
   return (c, c, cR)
| c@(local_const x pry binfo α) lconsts := lconsts.find x
| (app         u v) lconsts := do
  (u0, u1, uR) ← u.param lconsts,
  (v0, v1, vR) ← v.param lconsts,
  return (app u0 v0, app u1 v1, uR.mk_app [v0, v1, vR])
| (lam         x binfo α body) lconsts := do
  (α0, α1, αR) ← α.param lconsts,
  ((x0, x1, xR), lconstsx, bodyx) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← bodyx.param lconstsx,
  let t0 := body0.abstract_ lam x0,
  let t1 := body1.abstract_ lam x1,
  let tR := ((bodyR.abstract_ lam xR).abstract_ lam x1).abstract_ lam x0,
  return (t0, t1, tR)
| (pi          x binfo α body) lconsts := do
  (α0, α1, αR) ← α.param lconsts,
  ((x0, x1, xR), lconstsx, bodyx) ← param.intro lconsts x α0 α1 αR body,
  (body0, body1, bodyR) ← bodyx.param lconstsx,
  let t0 := body0.abstract_ pi x0,
  let t1 := body1.abstract_ pi x1,
  f0 ← mk_local_def "f0" t0,
  f1 ← mk_local_def "f1" t1,
  let tR := (((((bodyR.mk_subst_or_app [app f0 x0, app f1 x1]
     ).abstract_ pi xR).abstract_ pi x1).abstract_ pi x0
     ).abstract_ lam f1).abstract_ lam f0,
  return (t0, t1, tR)
| (elet        x α val body) lconsts := fail $
  "param: elet not implemented"
  -- [WRONG CODE!!!]
  -- (α0, α1, αR) ← α.param,
  -- (val0, val1, valR) ← val.param,
  -- (body0, body1, bodyR) ← body.param,
  -- let t0_ := elet (x.ext "0") α0 val0,
  -- let t1_ := elet (x.ext "1") α1 val1,
  -- let tR := t0_ $ t1_ $ elet (x.ext "R") stripped_αR valR bodyR,
  -- return (t0_ body0, t1_ body1, tR)
  -- [/WRONG CODE!!!]
| exp@_ _ := fail $
  "parma: expression " ++ exp.to_string ++ " is not translatable"

-- could replace the consts argument with 
meta def param.inductive (p := 2) (n : name) :
  tactic unit := do
  env ← get_env,
  ind_decl ← get_decl n,
  guard $ env.is_inductive n,
  i ← mk_const n,
  let ctors := env.constructors_of n,
  let nparams := env.inductive_num_params n,
  let indices := env.inductive_num_indices n,
  let ty := ind_decl.type,
  (ty0, ty1, tyR) ← ty.param p mk_name_map,
  ctorsR ← ctors.mmap (λ n : name, do
    decl ← get_decl n,
    c ← mk_const n,
    let ty := decl.type,
    (ty0, ty1, tyR) ← ty.param p mk_name_map,
    return (n.param p, tyR.mk_subst_or_app [c, c])),
  add_inductive (n.param p) ind_decl.univ_params ((p + 1) * nparams)
    (tyR.mk_subst_or_app [i, i]) ctorsR

#check lean.parser

@[user_command]
meta def param_cmd (_ : parse $ tk "#param") : lean.parser unit := do
  ns ← many ident,
  of_tactic $ ns.mmap' (param.inductive 2)

#param bool

#param punit

#check param.«2».nat.

#print nat.brec_on
#print param.«2».nat.rec

#exit

@[user_attribute]
meta def parametricity_attr : user_attribute (name_map name) name :=
{ name      := `parametricity,
  descr     := "Parametricity rules",
  cache_cfg := ⟨λ ns, ns.mfoldl (λ dict n, do
    val ← parametricity_attr.get_param n
    pure $ dict.insert n (val ++ n)) mk_name_map, []⟩,
  parser    := lean.parser.ident,
  after_set := some $ λ src _ _, do
    val ← parametricity_attr.get_param src,
    param2.inductive src val }

--run_cmd param2.inductive mk_name_map `nat `param2
attribute [parametricity param2] nat

-- at any given time, you can get the updated consts map:
run_cmd parametricity_attr.get_cache >>= trace

#check param2.nat
#check param2.nat.succ

run_cmd do
  let e := `(λ α : Type, λ x : α, x),
  let t := `(∀ α : Type, α → α),
  (t0,t1,tR) ← t.param2 mk_name_map mk_name_map,
  (e0,e1,eR) ← e.param2 mk_name_map mk_name_map,
  teR ← infer_type eR,
  unify teR (tR.mk_app [e, e])

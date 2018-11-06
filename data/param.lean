-- author: Cyril Cohen <cyril.cohen@inria.fr>
-- with contributions and help from Rob Lewis <rob.y.lewis@gmail.com>

import tactic
open expr native tactic

meta def expr.instantiate_lam (nv : expr) : expr → expr
| (lam nm bi tp bd) := bd.replace
    (λ e i, match e with
            | var k := if i = k then nv else none
            | _ := none
            end)
| e := app e nv

meta def expr.mk_subst_or_app : expr → list expr → expr
| e []      := e
| e (x::xs) := (x.instantiate_lam e).mk_subst_or_app xs

-- run_cmd tactic.trace $ expr.instantiate_lam `(2) `(λ x : ℕ, x + 1)

private def bid := binder_info.default

meta def expr.strip_lam : expr → nat → option expr
| (lam _ _ _ bd) (nat.succ n) := bd.strip_lam n
| t 0 := return t
| _ _ := none

meta def name.ext (ext : string) (x : name) : name :=
  (x.to_string ++ ext : string)

meta def expr.param2
   (consts : name_map expr)
   (lconsts : name_map (expr × expr × expr)) :
   expr → tactic (expr × expr × expr) 
| (var         db)  := return (var (3 * db), var (3 * db + 1), var (3 * db + 2))
| (sort        lvl) := 
  return (sort lvl, sort lvl,
    lam "α0" bid (sort lvl) $ lam "α1" bid (sort lvl) $
    pi "x0" bid (var 1) $ pi "x1" bid (var 1) $ sort lvl)
| c@(const       x lvls) :=
   match consts.find x with
   | some cR := return (c, c, cR)
   | _ := fail $ "param: no translation for constant " ++ to_string x
   end
| c@(local_const x pry binfo α) := lconsts.find x
| (app         u v) := do
  (u0, u1, uR) ← u.param2,
  (v0, v1, vR) ← v.param2,
  return (app u0 v0, app u1 v1, uR.mk_app [v0, v1, vR])
| (lam         x binfo α body) := do
  (α0, α1, αR) ← α.param2,
  stripped_αR ← αR.strip_lam 2,
  (body0, body1, bodyR) ← body.param2,
  let t0_ := lam (x.ext "0") binfo α0,
  let t1_ := lam (x.ext "1") binfo α1,
  let tR := t0_ $ t1_ $ lam (x.ext "R") binfo stripped_αR bodyR,
  return (t0_ body0, t1_ body1, tR)
| (pi          x binfo α body) := do
  (α0, α1, αR) ← α.param2,
  stripped_αR ← αR.strip_lam 2,
  (body0, body1, bodyR) ← body.param2,
  let t0_ := pi (x.ext "0") binfo α0,
  let t1_ := pi (x.ext "1") binfo α1,
  let tR := lam ("f0") bid (t0_ body0) $ lam ("f1") bid (t1_ body1) $
            t0_ $ t1_ $ pi (x.ext "R") binfo stripped_αR $
            (bodyR.mk_subst_or_app [app (var 4) (var 2), app (var 3) (var 1)]),
  return (t0_ body0, t1_ body1, tR)
| (elet        x α val body) := do
  (α0, α1, αR) ← α.param2,
  stripped_αR ← αR.strip_lam 2,
  (val0, val1, valR) ← val.param2,
  (body0, body1, bodyR) ← body.param2,
  let t0_ := elet (x.ext "0") α0 val0,
  let t1_ := elet (x.ext "1") α1 val1,
  let tR := t0_ $ t1_ $ elet (x.ext "R") stripped_αR valR bodyR,
  return (t0_ body0, t1_ body1, tR)
| exp@_ := fail $ "parma: expression " ++ exp.to_string ++ " is not translatable"

#check has_to_tactic_format

run_cmd expr.param2 mk_name_map mk_name_map `(λ α : Type, α) >>= tactic.trace

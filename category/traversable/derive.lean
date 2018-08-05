/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Simon Hudon

Automation to construct `traversable` instances
-/

import category.traversable.basic
       category.traversable.lemmas
       category.basic data.list.basic
import tactic.basic tactic.cache

namespace tactic.interactive

open tactic list monad functor

/-- similar to `nested_traverse` but for `functor` -/
meta def nested_map (f v : expr) : expr → tactic expr
| t :=
do t ← instantiate_mvars t,
   mcond (succeeds $ is_def_eq t v)
      (pure f)
      (if ¬ v.occurs (t.app_fn)
          then do
            cl ← mk_app ``functor [t.app_fn],
            _inst ← mk_instance cl,
            f' ← nested_map t.app_arg,
            mk_mapp ``functor.map [t.app_fn,_inst,none,none,f']
          else fail format!"type {t} is not a functor with respect to variable {v}")

/-- similar to `traverse_field` but for `functor` -/
meta def map_field (n : name) (cl f α β e : expr) : tactic expr :=
do t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then fail "recursive types not supported"
   else if α =ₐ e then pure β
   else if α.occurs t
   then do f' ← nested_map f α t,
           pure $ f' e
   else
         (is_def_eq t.app_fn cl >> mk_app ``comp.mk [e])
     <|> pure e

/-- similar to `traverse_constructor` but for `functor` -/
meta def map_constructor (c n : name) (f α β : expr) (args₀ rec_call : list expr) : tactic expr :=
do g ← target,
   args' ← mmap (map_field n g.app_fn f α β) args₀,
   constr ← mk_const c,
   let r := constr.mk_app (args' ++ rec_call),
   return r

/-- derive the `map` definition of a `functor` -/
meta def mk_map (type : name) (cs : list name) :=
do ls ← local_context,
   [α,β,f,x] ← tactic.intro_lst [`α,`β,`f,`x],
   xs ← tactic.induction x,
   () <$ mzip_with' (λ (c : name) (x : name × list expr × list (name × expr)),
      do let args := x.2.1,
         (args,rec_call) ← args.mpartition $ λ e, (bnot ∘ β.occurs) <$> infer_type e,
         let args₀ := args.take $ args.length - rec_call.length,
         map_constructor c type f α β (ls ++ β :: args₀) rec_call >>= tactic.exact)
      cs xs

meta def mk_mapp_aux' : expr → expr → list expr → tactic expr
| fn (expr.pi n bi d b) (a::as) :=
do infer_type a >>= unify d,
   fn ← head_beta (fn a),
   t ← whnf (b.instantiate_var a),
   mk_mapp_aux' fn t as
| fn _ _ := pure fn

meta def mk_mapp' (fn : expr) (args : list expr) : tactic expr :=
do t ← infer_type fn >>= whnf,
   mk_mapp_aux' fn t args

/-- derive the equations for a specific `map` definition -/
meta def derive_map_equations (n : name) (vs : list expr) (tgt : expr) : tactic unit :=
do e ← get_env,
   ((e.constructors_of n).enum_from 1).mmap' $ λ ⟨i,c⟩,
   do { mk_meta_var tgt >>= set_goals ∘ pure,
        vs ← intro_lst $ vs.map expr.local_pp_name,
        [α,β,f] ← tactic.intro_lst [`α,`β,`f] >>= mmap instantiate_mvars,
        c' ← mk_mapp c $ vs.map some ++ [α],
        tgt' ← infer_type c' >>= pis vs,
        mk_meta_var tgt' >>= set_goals ∘ pure,
        vs ← tactic.intro_lst $ vs.map expr.local_pp_name,
        vs' ← tactic.intros,
        c' ← mk_mapp c $ vs.map some ++ [α],
        arg ← mk_mapp' c' vs',
        n_map ← mk_const (n <.> "map"),
        let call_map := λ x, mk_mapp' n_map (vs ++ [α,β,f,x]),
        lhs ← call_map arg,
        (args,rec_call) ← vs'.mpartition $
          λ e, ((≠ n) ∘ expr.const_name ∘ expr.get_app_fn) <$> infer_type e,
        rec_call ← rec_call.mmap call_map,
        rhs ← map_constructor c n f α β (vs ++ α :: args) rec_call,
        monad.join $ unify <$> infer_type lhs <*> infer_type rhs,
        eqn ← mk_app ``eq [lhs,rhs],
        let ws := eqn.list_local_consts,
        eqn ← pis ws.reverse eqn,
        eqn ← instantiate_mvars eqn,
        (_,pr) ← solve_aux eqn (tactic.intros >> refine ``(rfl)),
        let eqn_n := n <.> "map" <.> "equations" <.> to_string format!"_eqn_{i}",
        pr ← instantiate_mvars pr,
        add_decl $ declaration.thm eqn_n eqn.collect_univ_params eqn (pure pr),
        return () },
   set_goals [],
   return ()

meta def derive_functor : tactic unit :=
do vs ← local_context,
   `(functor %%f) ← target,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   let cs := env.constructors_of n,
   refine ``( { functor . map := _ , .. } ),
   tgt ← target,
   extract_def (n <.> "map") $ mk_map n cs,
   tgt ← pis vs tgt,
   derive_map_equations n vs tgt

/-- `seq_apply_constructor f [x,y,z]` synthesizes `f <*> x <*> y <*> z` -/
private meta def seq_apply_constructor : expr → list (expr ⊕ expr) → tactic (list (tactic expr) × expr)
| e (sum.inr x :: xs) := prod.map (cons intro1)   id <$> (to_expr ``(%%e <*> %%x) >>= flip seq_apply_constructor xs)
| e (sum.inl x :: xs) := prod.map (cons $ pure x) id <$> seq_apply_constructor e xs
| e [] := return ([],e)

/-- ``nested_traverse f α (list (array n (list α)))`` synthesizes the expression
`traverse (traverse (traverse f))`. `nested_traverse` assumes that `α` appears in
`(list (array n (list α)))` -/
meta def nested_traverse (f v : expr) : expr → tactic expr
| t :=
do t ← instantiate_mvars t,
   mcond (succeeds $ is_def_eq t v)
      (pure f)
      (if ¬ v.occurs (t.app_fn)
          then do
            cl ← mk_app ``traversable [t.app_fn],
            _inst ← mk_instance cl,
            f' ← nested_traverse t.app_arg,
            mk_mapp ``traversable.traverse [t.app_fn,_inst,none,none,none,none,f']
          else fail format!"type {t} is not traversable with respect to variable {v}")

/--
For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_field `foo appl_inst f `α `(x : list α)`` synthesizes
`traverse f x` as part of traversing `foo1`. -/
meta def traverse_field (n : name) (appl_inst cl f v e : expr) : tactic (expr ⊕ expr) :=
do t ← infer_type e >>= whnf,
   if t.get_app_fn.const_name = n
   then fail "recursive types not supported"
   else if v.occurs t
   then do f' ← nested_traverse f v t,
           pure $ sum.inr $ f' e
   else
         (is_def_eq t.app_fn cl >> sum.inr <$> mk_app ``comp.mk [e])
     <|> pure (sum.inl e)

/--
For a sum type `inductive foo (α : Type) | foo1 : list α → ℕ → foo | ...`
``traverse_constructor `foo1 `foo appl_inst f `α `β [`(x : list α), `(y : ℕ)]``
synthesizes `foo1 <$> traverse f x <*> pure y.` -/
meta def traverse_constructor (c n : name) (appl_inst f α β : expr) (args₀ rec_call : list expr) : tactic expr :=
do g ← target,
   args' ← mmap (traverse_field n appl_inst g.app_fn f α) args₀,
   constr ← mk_const c,
   v ← mk_mvar,
   constr' ← to_expr ``(@pure _ (%%appl_inst).to_has_pure _ %%v),
   (vars_intro,r) ← seq_apply_constructor constr' (args' ++ rec_call.map sum.inr),
   gs ← get_goals,
   set_goals [v],
   vs ← vars_intro.mmap id,
   tactic.exact (constr.mk_app vs),
   done,
   set_goals gs,
   return r

/-- derive the `traverse` definition of a `traversable` instance -/
meta def mk_traverse (type : name) (cs : list name) := do
do ls ← local_context,
   [m,appl_inst,α,β,f,x] ← tactic.intro_lst [`m,`appl_inst,`α,`β,`f,`x],
   reset_instance_cache,
   xs ← tactic.induction x,
   () <$ mzip_with'
      (λ (c : name) (x : name × list expr × list (name × expr)),
      do let args := x.2.1,
         (args,rec_call) ← args.mpartition $ λ e, (bnot ∘ β.occurs) <$> infer_type e,
         let args₀ := args.take $ args.length - rec_call.length,
         traverse_constructor c type appl_inst f α β (ls ++ β :: args₀) rec_call >>= tactic.exact)
      cs xs

open applicative

/-- derive the equations for a specific `traverse` definition -/
meta def derive_traverse_equations (n : name) (vs : list expr) (tgt : expr) : tactic unit :=
do e ← get_env,
   ((e.constructors_of n).enum_from 1).mmap' $ λ ⟨i,c⟩,
   do { mk_meta_var tgt >>= set_goals ∘ pure,
        vs ← intro_lst $ vs.map expr.local_pp_name,
        [m,appl_inst,α,β,f] ← tactic.intro_lst [`m,`appl_inst,`α,`β,`f] >>= mmap instantiate_mvars,
        c' ← mk_mapp c $ vs.map some ++ [α],
        tgt' ← infer_type c' >>= pis vs,
        mk_meta_var tgt' >>= set_goals ∘ pure,
        vs ← tactic.intro_lst $ vs.map expr.local_pp_name,
        c' ← mk_mapp c $ vs.map some ++ [α],
        vs' ← tactic.intros,
        arg ← mk_mapp' c' vs',
        n_map ← mk_const (n <.> "traverse"),
        let call_traverse := λ x, mk_mapp' n_map (vs ++ [m,appl_inst,α,β,f,x]),
        lhs ← call_traverse arg,
        (args,rec_call) ← vs'.mpartition $
          λ e, ((≠ n) ∘ expr.const_name ∘ expr.get_app_fn) <$> infer_type e,
        rec_call ← rec_call.mmap call_traverse,
        rhs ← traverse_constructor c n appl_inst f α β (vs ++ β :: args) rec_call,
        monad.join $ unify <$> infer_type lhs <*> infer_type rhs,
        eqn ← mk_app ``eq [lhs,rhs],
        let ws := eqn.list_local_consts,
        eqn ← pis ws.reverse eqn,
        eqn ← instantiate_mvars eqn,
        (_,pr) ← solve_aux eqn (tactic.intros >> refine ``(rfl)),
        let eqn_n := n <.> "traverse" <.> "equations" <.> to_string format!"_eqn_{i}",
        pr ← instantiate_mvars pr,
        add_decl $ declaration.thm eqn_n eqn.collect_univ_params eqn (pure pr),
        return () },
   set_goals [],
   return ()

meta def derive_traverse : tactic unit :=
do vs ← local_context,
   `(traversable %%f) ← target,
   env ← get_env,
   let n := f.get_app_fn.const_name,
   let cs := env.constructors_of n,
   constructor,
   tgt ← target,
   extract_def (n <.> "traverse") $ mk_traverse n cs,
   tgt ← pis vs tgt,
   derive_traverse_equations n vs tgt,
   pure ()

meta def mk_one_instance
  (n : name)
  (cls : name)
  (tac : tactic unit)
  (mk_inst : name → expr → tactic expr := λ n arg, mk_app n [arg]) :
  tactic unit :=
do decl ← get_decl n,
   cls_decl ← get_decl cls,
   env ← get_env,
   guard (env.is_inductive n) <|> fail format!"failed to derive '{cls}', '{n}' is not an inductive type",
   let ls := decl.univ_params.map $ λ n, level.param n,
   -- incrementally build up target expression `Π (hp : p) [cls hp] ..., cls (n.{ls} hp ...)`
   -- where `p ...` are the inductive parameter types of `n`
   let tgt : expr := expr.const n ls,
   ⟨params, _⟩ ← mk_local_pis (decl.type.instantiate_univ_params (decl.univ_params.zip ls)),
   let params := params.init,
   let tgt := tgt.mk_app params,
   tgt ← mk_inst cls tgt,
   tgt ← params.enum.mfoldr (λ ⟨i, param⟩ tgt,
   do -- add typeclass hypothesis for each inductive parameter
      tgt ← do {
        guard $ i < env.inductive_num_params n,
        param_cls ← mk_app cls [param],
        pure $ expr.pi `a binder_info.inst_implicit param_cls tgt
      } <|> pure tgt,
      pure $ tgt.bind_pi param
   ) tgt,
   () <$ mk_instance tgt <|> do
     (_, val) ← tactic.solve_aux tgt (do
       tactic.intros >> tac),
     val ← instantiate_mvars val,
     let trusted := decl.is_trusted ∧ cls_decl.is_trusted,
     add_decl (declaration.defn (n ++ cls)
               decl.univ_params
               tgt val reducibility_hints.abbrev trusted),
     set_basic_attribute `instance (n ++ cls) tt

open interactive


meta def get_equations_of (n : name) : tactic (list pexpr) :=
do e ← get_env,
   let pre := n <.> "equations",
   let x := e.fold [] $ λ d xs, if pre.is_prefix_of d.to_name then d.to_name :: xs else xs,
   x.mmap resolve_name

meta def derive_lawful_functor : tactic unit :=
do `(@is_lawful_functor %%f %%d) ← target,
   refine ``( { .. } ),
   let n := f.get_app_fn.const_name,
   solve1 (do
     vs ← tactic.intros,
     try $ dunfold [``functor.map] (loc.ns [none]),
     dunfold [n <.> "map",``id] (loc.ns [none]),
     () <$ tactic.induction vs.ilast; `[simp [functor.map_id,*]]),
   focus1 (do
     vs ← tactic.intros,
     try $ dunfold [``functor.map] (loc.ns [none]),
     dunfold [n <.> "map",``id] (loc.ns [none]),
     () <$ tactic.induction vs.ilast; `[simp [functor.map_comp_map,*]]),
   return ()

meta def simp_functor (rs : list simp_arg_type := []) : tactic unit :=
simp none ff rs [`functor_norm] (loc.ns [none])

meta def derive_lawful_traversable : tactic unit :=
do `(@is_lawful_traversable %%f %%d) ← target,
   let n := f.get_app_fn.const_name,
   eqns  ← get_equations_of (n <.> "traverse"),
   eqns' ← get_equations_of (n <.> "map"),
   let rs := eqns.map simp_arg_type.expr ++
             eqns'.map simp_arg_type.expr ++
             [simp_arg_type.all_hyps
             ],
   let rs₀ := [ simp_arg_type.expr ``(traversable.map_traverse') ],
   let rs₁ := [ simp_arg_type.expr ``(traversable.traverse_map') ],
   let rs₂ := [ simp_arg_type.expr ``(function.comp) ],
   constructor,
   gs ← get_goals,
   gs ← mzip_with (λ g tac,
    do set_goals [g],
       vs ← tactic.intros,
       resetI,
       dunfold [``traversable.traverse,``functor.map] (loc.ns [none]),
       () <$ tactic.induction vs.ilast;
         simp_functor rs;
         (refl <|> tac),
       get_goals ) gs
      [ refl,
        simp_functor (rs ++ rs₂),
        (simp_functor (rs ++ rs₀) ; refl),
        `[ simp [traversable.traverse_map' g,traversable.traverse_map' ((<$>) g)] ],
        `[ simp only [traversable.naturality_pf η] ],
        skip, skip, skip, skip, skip ],
   set_goals gs.join,
   return ()

open function

meta def higher_order_derive_handler
  (cls : name)
  (tac : tactic unit)
  (deps : list derive_handler := [])
  (mk_inst : name → expr → tactic expr := λ n arg, mk_app n [arg])
  (enable_checks : bool) :
  derive_handler :=
λ p n,
if p.is_constant_of cls ∨ ¬ enable_checks then
do mmap' (λ f : derive_handler, f p n) deps,
   mk_one_instance n cls tac mk_inst,
   pure tt
else pure ff

meta def functor_derive_handler' : bool → derive_handler :=
higher_order_derive_handler ``functor derive_functor

@[derive_handler]
meta def functor_derive_handler : derive_handler :=
functor_derive_handler' tt

meta def traversable_derive_handler' : bool → derive_handler :=
higher_order_derive_handler ``traversable derive_traverse [functor_derive_handler' ff]

@[derive_handler]
meta def traversable_derive_handler : derive_handler :=
traversable_derive_handler' tt

meta def lawful_functor_derive_handler' : bool → derive_handler :=
higher_order_derive_handler
  ``is_lawful_functor derive_lawful_functor
  [traversable_derive_handler' ff]
  (λ n arg, mk_mapp n [arg,none])

@[derive_handler]
meta def lawful_functor_derive_handler : derive_handler :=
lawful_functor_derive_handler' tt

@[derive_handler]
meta def lawful_traversable_derive_handler : derive_handler :=
higher_order_derive_handler
  ``is_lawful_traversable derive_lawful_traversable
  [traversable_derive_handler' ff,
   lawful_functor_derive_handler' ff]
  (λ n arg, mk_mapp n [arg,none])
  tt

end tactic.interactive
/-
Copyright (c) 2026 Bas Spitters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bas Spitters
-/

module

public import VCVio.OracleComp.SimSemantics.QueryImpl.Basic

/-!
# Transporting oracle computations along polynomial lenses

A lens `l : PFunctor.Lens spec.toPFunctor spec'.toPFunctor` sends each `spec`-query `t` to the
`spec'`-query `l.toFunA t` and translates each answer back by `l.toFunB t`. This file defines the
two actions of such a lens:

* on computations, `OracleComp.mapLens l : OracleComp spec α → OracleComp spec' α`, which is
  PolyFun's `PFunctor.FreeM.mapLens`. It is a monad morphism and functorial in the lens
  (`mapLens_pure`, `mapLens_bind`, `mapLens_map`, `mapLens_id`, `mapLens_mapLens`), and
  `mapLens_liftM_query` gives its action on a single query;
* on handlers, `QueryImpl.comapLens impl l : QueryImpl spec m`, which pulls a handler for `spec'`
  back to `spec` by answering `t` with `impl (l.toFunA t)`, mapped by `l.toFunB t`.

`simulateQ_mapLens` relates the two actions, and `liftComp`, the lift along an oracle-spec
inclusion, is `mapLens` along the inclusion's lens `OracleSpec.liftLens`.
-/

public section

universe u u' u'' v w

open OracleSpec PFunctor

open scoped PFunctor

namespace OracleComp

section mapLens

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  {spec : OracleSpec.{u, v} ι} {spec' : OracleSpec.{u', v} ι'}
  {spec'' : OracleSpec.{u'', v} ι''} {α β : Type w}

/-- Transport an oracle computation along a polynomial lens: each query `t` to `spec` is
replaced by the query `l.toFunA t` to `spec'`, whose answer is translated back by
`l.toFunB t`. -/
@[expose]
def mapLens (l : Lens spec.toPFunctor spec'.toPFunctor) (oa : OracleComp spec α) :
    OracleComp spec' α :=
  FreeM.mapLens l oa

/-- Transport along a lens fixes `pure`. -/
@[simp]
lemma mapLens_pure (l : Lens spec.toPFunctor spec'.toPFunctor) (x : α) :
    (pure x : OracleComp spec α).mapLens l = pure x :=
  FreeM.mapLens_pure l x

/-- Transport along a lens on a query node: the query is relabelled forward and each answer of
the new query is translated back before entering the continuation. -/
lemma mapLens_queryBind (l : Lens spec.toPFunctor spec'.toPFunctor) (t : spec.Domain)
    (k : spec.Range t → OracleComp spec α) :
    (queryBind t k).mapLens l = queryBind (l.toFunA t) fun d => (k (l.toFunB t d)).mapLens l :=
  FreeM.mapLens_liftBind l t k

/-- Transport along a lens commutes with `bind`. -/
@[simp]
lemma mapLens_bind (l : Lens spec.toPFunctor spec'.toPFunctor) (oa : OracleComp spec α)
    (f : α → OracleComp spec β) :
    (oa >>= f).mapLens l = oa.mapLens l >>= fun a => (f a).mapLens l :=
  FreeM.mapLens_bind' l oa f

/-- Transport along a lens commutes with `map`. -/
@[simp]
lemma mapLens_map (l : Lens spec.toPFunctor spec'.toPFunctor) (f : α → β)
    (oa : OracleComp spec α) :
    (f <$> oa).mapLens l = f <$> oa.mapLens l :=
  FreeM.mapLens_map l f oa

/-- Transport along the identity lens is the identity. -/
@[simp]
lemma mapLens_id (oa : OracleComp spec α) :
    oa.mapLens (Lens.id spec.toPFunctor) = oa :=
  FreeM.mapLens_id oa

/-- Transport along two lenses in turn is transport along their composite. -/
@[simp]
lemma mapLens_mapLens (l₂ : Lens spec'.toPFunctor spec''.toPFunctor)
    (l₁ : Lens spec.toPFunctor spec'.toPFunctor) (oa : OracleComp spec α) :
    (oa.mapLens l₁).mapLens l₂ = oa.mapLens (l₂ ∘ₗ l₁) :=
  FreeM.mapLens_mapLens l₂ l₁ oa

/-- A single query `t` is transported to the query `l.toFunA t`, its answer mapped back by
`l.toFunB t`. -/
@[simp]
lemma mapLens_liftM_query {spec : OracleSpec.{u, w} ι} {spec' : OracleSpec.{u', w} ι'}
    (l : Lens spec.toPFunctor spec'.toPFunctor) (t : spec.Domain) :
    (liftM (spec.query t) : OracleComp spec (spec.Range t)).mapLens l =
      l.toFunB t <$> (liftM (spec'.query (l.toFunA t)) : OracleComp spec' _) :=
  rfl

end mapLens

end OracleComp

namespace QueryImpl

variable {ι : Type u} {ι' : Type u'} {spec : OracleSpec.{u, v} ι}
  {spec' : OracleSpec.{u', v} ι'} {m : Type v → Type w}

/-- Pull a handler for `spec'` back along a lens into `spec'`: a `spec`-query `t` is answered by
`impl (l.toFunA t)`, mapped by `l.toFunB t`. -/
@[expose]
def comapLens [Functor m] (impl : QueryImpl spec' m) (l : Lens spec.toPFunctor spec'.toPFunctor) :
    QueryImpl spec m :=
  fun t => l.toFunB t <$> impl (l.toFunA t)

/-- The pulled-back handler at a query `t`. -/
@[simp]
lemma comapLens_apply [Functor m] (impl : QueryImpl spec' m)
    (l : Lens spec.toPFunctor spec'.toPFunctor) (t : spec.Domain) :
    impl.comapLens l t = l.toFunB t <$> impl (l.toFunA t) := rfl

/-- Pulling a handler back along the identity lens returns the handler. -/
@[simp]
lemma comapLens_id [Functor m] [LawfulFunctor m] (impl : QueryImpl spec m) :
    impl.comapLens (Lens.id spec.toPFunctor) = impl := by
  grind only [comapLens_apply, id_map']

end QueryImpl

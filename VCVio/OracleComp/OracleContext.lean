/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.OracleComp.SimSemantics.Append

/-!
# Bundled Oracle Specs and Implementations

This file defines a type `OracleContext spec.Domain m` that provides an ambient set of oracles,
along with an implementation of those oracles in the monad `m`.
-/

@[expose] public section

universe u v w

open OracleSpec OracleComp

/-- An `OracleContext spec.Domain m` bundles a specification `spec` of oracles with input set `spec.Domain`
and an implementation of the oracles in terms of the monad `m`. -/
structure OracleContext (m : Type v → Type w) : Type (max u v w + 1) where
  /-- The ambient oracles, with query inputs indexed by `spec.Domain`. -/
  spec : OracleSpec.{u,v}
  /-- The interpretation of each query to `spec` as a computation in `m`. -/
  impl : QueryImpl spec m

/-- Convert an `OracleSpec` into an `OracleContext` with `OracleComp` as the implementation monad,
using the identity implementation for queries. -/
@[reducible]
def OracleSpec.defaultContext (spec : OracleSpec) :
    OracleContext spec.Domain (OracleComp spec) where
  spec := spec
  impl := QueryImpl.id' spec

namespace OracleContext

instance {m : Type u → Type v} [Pure m] : Inhabited (OracleContext spec.Domain m) :=
  ⟨{ spec := spec.Domain →ₒ PUnit, impl _ := pure PUnit.unit }⟩

variable {ι'} {spec : OracleSpec} {m : Type u → Type v}

/-- Convert a `QueryImpl` into an `OracleContext` by bundling the `OracleSpec` corresponding
to the particular implementation. -/
@[reducible] def ofImpl (impl : QueryImpl spec m) : OracleContext spec.Domain m where
  spec := spec
  impl := impl

/-- Combine two oracle contexts with the same target monad, giving access to both ambient
oracles and implementing queries to each independently. -/
@[reducible] protected def add (O : OracleContext spec.Domain m) (O' : OracleContext ι' m) :
    OracleContext (spec.Domain ⊕ ι') m where
  spec := O.spec + O'.spec
  impl := O.impl + O'.impl

instance : HAdd (OracleContext spec.Domain m) (OracleContext ι' m) (OracleContext (spec.Domain ⊕ ι') m) where
  hAdd := OracleContext.add

@[simp] lemma add_def (O : OracleContext spec.Domain m) (O' : OracleContext ι' m) :
    O + O' = O.add O' := rfl

lemma spec_add (O : OracleContext spec.Domain m) (O' : OracleContext ι' m) :
    (O + O').spec = O.spec + O'.spec := rfl

lemma impl_add (O : OracleContext spec.Domain m) (O' : OracleContext ι' m) :
    (O + O').impl = O.impl + O'.impl := rfl

end OracleContext

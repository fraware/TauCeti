/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Cover

/-!
# Total boundedness under uniform approximation

This file records a small compactness lemma used by approximation arguments.  A subset of a
pseudometric space is totally bounded if, at every positive scale, all of its points can be
uniformly approximated at that scale by points of some totally bounded set.

The statement is deliberately independent of function spaces, measures, or Sobolev theory.  In
the Fréchet--Kolmogorov argument it is the final topological step: mollified functions form a
totally bounded family, uniform approximation transfers total boundedness back to the original
family, and completeness then upgrades the closure to a compact set.

## Main declaration

* `TauCeti.totallyBounded_of_uniform_approx`: total boundedness transfers through uniformly
  arbitrarily accurate approximants.

## Provenance

The proof is adapted from `uda-lab/leray-hopf` (Apache-2.0), commit
`e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc`,
`LerayHopf/Bochner/StepFunctionCompactness.lean` (`totallyBounded_of_uniform_approx'`).  The
statement is renamed and documented for Tau Ceti; the argument is the same finite-net triangle
inequality proof.
-/

public section

namespace TauCeti

open Set

/-- A set that is uniformly approximable, at every positive scale, by a totally bounded set is
totally bounded.

More precisely, if for every `ε > 0` there is a totally bounded set `A` such that each point of
`S` lies within `ε` of some point of `A`, then `S` is totally bounded. -/
theorem totallyBounded_of_uniform_approx {α : Type*} [PseudoMetricSpace α] (S : Set α)
    (happrox : ∀ ε > 0, ∃ A : Set α, TotallyBounded A ∧
      ∀ s ∈ S, ∃ a ∈ A, dist s a < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨A, hA, hAapprox⟩ := happrox (ε / 2) (by linarith)
  obtain ⟨t, ht_fin, ht_cover⟩ := (Metric.totallyBounded_iff.mp hA) (ε / 2) (by linarith)
  refine ⟨t, ht_fin, fun s hs => ?_⟩
  obtain ⟨a, haA, hsa⟩ := hAapprox s hs
  have ha_mem : a ∈ ⋃ y ∈ t, Metric.ball y (ε / 2) := ht_cover haA
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at ha_mem ⊢
  obtain ⟨y, hyt, hay⟩ := ha_mem
  refine ⟨y, hyt, ?_⟩
  calc
    dist s y ≤ dist s a + dist a y := dist_triangle s a y
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

end TauCeti

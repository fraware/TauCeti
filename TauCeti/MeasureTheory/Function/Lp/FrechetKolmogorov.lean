/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.TotallyBounded
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Fréchet--Kolmogorov compactness in `L²`

This module develops the `L²` compactness criterion used by the Rellich--Kondrachov theorem on
bounded domains.  The intended public theorem is the localized Fréchet--Kolmogorov criterion:
a uniformly `L²`-bounded family of global representatives whose translations are uniformly
continuous in `L²` has precompact restrictions to a fixed compact ball.

The proof follows the standard mollification argument.  Convolution with a normalized smooth
compactly supported kernel gives a uniformly equibounded, equicontinuous family on the ball;
Arzelà--Ascoli makes the mollified family precompact, and the uniform translation modulus makes
mollification a uniform `L²` approximation.  The final transfer from approximants to the original
family is `TauCeti.totallyBounded_of_uniform_approx`.

The global `L²` bound on representatives is load-bearing: a bound only on one fixed ball together
with a translation modulus does not control mass in the annulus reached by the mollifier.  This
module therefore does not claim that local boundedness plus translation continuity alone implies
compactness.

The measure is the canonical `volume` on a finite-dimensional real inner-product space.  This is
the setting needed by the PDE roadmap and avoids introducing irrelevant Haar-measure parameters
into the eventual compactness API.

## Provenance

The proof architecture and several low-level lemmas are adapted from `uda-lab/leray-hopf`
(Apache-2.0), commit `e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc`,
`LerayHopf/R3/FrechetKolmogorov.lean`.  The Tau Ceti version is generalized away from the
three-dimensional Navier--Stokes setting and written against Tau Ceti's current Mathlib pin.

## References

Lane A.6 of `TauCetiRoadmap/PDE/README.md`; H. Brezis, *Functional Analysis, Sobolev Spaces and
Partial Differential Equations*, Chapter 4; L. C. Evans, *Partial Differential Equations*,
Chapter 5.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Convolution ENNReal Topology

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

/-! ### Restricted `L²` classes and translations -/

/-- Restrict a whole-space `L²` class to a set by changing the underlying measure to
`volume.restrict s`.  This is implementation plumbing for the compactness proof; the public
criterion will expose only the compactness property that later PDE arguments consume. -/
private noncomputable def restrictL2 (s : Set E) (f : Lp ℝ 2 (volume : Measure E)) :
    Lp ℝ 2 ((volume : Measure E).restrict s) :=
  ((Lp.memLp f).restrict s).toLp _

private theorem coeFn_restrictL2 (s : Set E) (f : Lp ℝ 2 (volume : Measure E)) :
    (restrictL2 s f : E → ℝ) =ᵐ[(volume : Measure E).restrict s] (f : E → ℝ) :=
  MemLp.coeFn_toLp _

/-- Restriction cannot increase the `L²` norm. -/
private theorem norm_restrictL2_le (s : Set E) (f : Lp ℝ 2 (volume : Measure E)) :
    ‖restrictL2 s f‖ ≤ ‖f‖ := by
  rw [restrictL2, Lp.norm_toLp, Lp.norm_def]
  refine ENNReal.toReal_mono (Lp.memLp f).2.ne ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- Whole-space `L²` translation by `h`, represented by `x ↦ f (x + h)`. -/
private noncomputable def translateL2 (h : E) (f : Lp ℝ 2 (volume : Measure E)) :
    Lp ℝ 2 (volume : Measure E) :=
  Lp.compMeasurePreserving (· + h)
    (measurePreserving_add_right (volume : Measure E) h) f

private theorem coeFn_translateL2 (h : E) (f : Lp ℝ 2 (volume : Measure E)) :
    (translateL2 h f : E → ℝ) =ᵐ[volume] fun x => f (x + h) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right (volume : Measure E) h)

/-- Translation of a fixed `L²` class is continuous in the shift. -/
private theorem continuous_translateL2 (f : Lp ℝ 2 (volume : Measure E)) :
    Continuous fun h : E => translateL2 h f := by
  let g : E → C(E, E) := fun h => ⟨(· + h), continuous_id.add continuous_const⟩
  have hg : Continuous g := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    show Continuous (fun p : E × E => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have hgm : ∀ h : E, MeasurePreserving (g h) (volume : Measure E) volume := fun h =>
    measurePreserving_add_right (volume : Measure E) h
  have hcont := Continuous.compMeasurePreservingLp
    (μ := (volume : Measure E)) (ν := (volume : Measure E)) (E := ℝ) (p := 2)
    (f := fun _ : E => f) (g := g) continuous_const hg hgm (by simp)
  simpa [translateL2, g] using hcont

@[simp]
private theorem translateL2_zero (f : Lp ℝ 2 (volume : Measure E)) : translateL2 0 f = f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_translateL2 (0 : E) f] with x hx
  simpa using hx

/-- The `L²` translation modulus of a fixed class vanishes at the origin. -/
private theorem tendsto_norm_translateL2_sub (f : Lp ℝ 2 (volume : Measure E)) :
    Tendsto (fun h : E => ‖translateL2 h f - f‖) (𝓝 0) (𝓝 0) := by
  have hsub : Continuous fun h : E => translateL2 h f - f :=
    (continuous_translateL2 f).sub continuous_const
  have hnorm := hsub.norm.tendsto 0
  simpa using hnorm

/-! ### A normalized compactly supported mollifier -/

/-- A concrete smooth bump with support radius `r / 2`. -/
private noncomputable def frechetKolmogorovBump (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : E) where
  rIn := r / 3
  rOut := r / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- The normalized nonnegative mollifier associated to `frechetKolmogorovBump`. -/
private noncomputable def frechetKolmogorovKernel (r : ℝ) (hr : 0 < r) : E → ℝ :=
  (frechetKolmogorovBump (E := E) r hr).normed (volume : Measure E)

private theorem contDiff_frechetKolmogorovKernel (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (frechetKolmogorovKernel (E := E) r hr) :=
  (frechetKolmogorovBump (E := E) r hr).contDiff_normed

private theorem hasCompactSupport_frechetKolmogorovKernel (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (frechetKolmogorovKernel (E := E) r hr) :=
  (frechetKolmogorovBump (E := E) r hr).hasCompactSupport_normed

private theorem frechetKolmogorovKernel_nonneg (r : ℝ) (hr : 0 < r) (x : E) :
    0 ≤ frechetKolmogorovKernel (E := E) r hr x :=
  (frechetKolmogorovBump (E := E) r hr).nonneg_normed x

private theorem integral_frechetKolmogorovKernel (r : ℝ) (hr : 0 < r) :
    ∫ x : E, frechetKolmogorovKernel (E := E) r hr x ∂volume = 1 :=
  (frechetKolmogorovBump (E := E) r hr).integral_normed

private theorem tsupport_frechetKolmogorovKernel (r : ℝ) (hr : 0 < r) :
    tsupport (frechetKolmogorovKernel (E := E) r hr) =
      Metric.closedBall (0 : E) (r / 2) := by
  exact (frechetKolmogorovBump (E := E) r hr).tsupport_normed_eq

private theorem frechetKolmogorovKernel_even (r : ℝ) (hr : 0 < r) (x : E) :
    frechetKolmogorovKernel (E := E) r hr (-x) =
      frechetKolmogorovKernel (E := E) r hr x :=
  (frechetKolmogorovBump (E := E) r hr).normed_neg x

/-- The mollifier as an `L²` class. -/
private noncomputable def frechetKolmogorovKernelL2 (r : ℝ) (hr : 0 < r) :
    Lp ℝ 2 (volume : Measure E) :=
  (contDiff_frechetKolmogorovKernel (E := E) r hr).continuous
    |>.memLp_of_hasCompactSupport
      (hasCompactSupport_frechetKolmogorovKernel (E := E) r hr)
    |>.toLp _

/-- The mollifier's own `L²` translation modulus vanishes. -/
private theorem tendsto_norm_translate_frechetKolmogorovKernelL2_sub (r : ℝ) (hr : 0 < r) :
    Tendsto
      (fun h : E =>
        ‖translateL2 h (frechetKolmogorovKernelL2 (E := E) r hr) -
          frechetKolmogorovKernelL2 (E := E) r hr‖)
      (𝓝 0) (𝓝 0) :=
  tendsto_norm_translateL2_sub (frechetKolmogorovKernelL2 (E := E) r hr)

/-! ### Pointwise mollification -/

/-- Pointwise convolution of a whole-space `L²` representative with the normalized smooth kernel.
The `L²` function is placed on the left and the compactly supported smooth kernel on the right so
that both the pointwise formula `∫ y, f y * η (x - y)` and Mathlib's convolution-regularity API
line up directly. -/
private noncomputable def frechetKolmogorovMollify (r : ℝ) (hr : 0 < r)
    (f : Lp ℝ 2 (volume : Measure E)) : E → ℝ :=
  (f : E → ℝ) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    frechetKolmogorovKernel (E := E) r hr

/-- Mollification of an `L²` function by the normalized bump is smooth. -/
private theorem contDiff_frechetKolmogorovMollify (r : ℝ) (hr : 0 < r)
    (f : Lp ℝ 2 (volume : Measure E)) :
    ContDiff ℝ ∞ (frechetKolmogorovMollify (E := E) r hr f) := by
  exact (hasCompactSupport_frechetKolmogorovKernel (E := E) r hr).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ)
    ((Lp.memLp f).locallyIntegrable (by norm_num))
    (contDiff_frechetKolmogorovKernel (E := E) r hr)

end TauCeti

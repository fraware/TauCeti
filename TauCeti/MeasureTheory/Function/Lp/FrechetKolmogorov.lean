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

/-- Global Cauchy--Schwarz bound for the pointwise mollification.  The estimate is valid at every
point, not only on the compact ball used later by Arzelà--Ascoli. -/
private theorem norm_frechetKolmogorovMollify_le (r : ℝ) (hr : 0 < r)
    (f : Lp ℝ 2 (volume : Measure E)) (x : E) :
    ‖frechetKolmogorovMollify (E := E) r hr f x‖ ≤
      ‖frechetKolmogorovKernelL2 (E := E) r hr‖ * ‖f‖ := by
  classical
  have hηmem : MemLp (frechetKolmogorovKernel (E := E) r hr) 2 (volume : Measure E) :=
    (contDiff_frechetKolmogorovKernel (E := E) r hr).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_frechetKolmogorovKernel (E := E) r hr)
  have hηaesm : AEStronglyMeasurable (frechetKolmogorovKernel (E := E) r hr)
      (volume : Measure E) := hηmem.aestronglyMeasurable
  have hmp := Measure.measurePreserving_sub_left (volume : Measure E) x
  have ha : MemLp
      (fun y : E => |frechetKolmogorovKernel (E := E) r hr (x - y)|) 2
      (volume : Measure E) :=
    (hηmem.comp_measurePreserving hmp).abs
  have hb : MemLp (fun y : E => ‖(f : E → ℝ) y‖) 2 (volume : Measure E) :=
    (Lp.memLp f).norm
  have hstep : ‖frechetKolmogorovMollify (E := E) r hr f x‖ ≤
      ∫ y : E, |frechetKolmogorovKernel (E := E) r hr (x - y)| * ‖(f : E → ℝ) y‖
        ∂(volume : Measure E) := by
    rw [frechetKolmogorovMollify, MeasureTheory.convolution]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae ?_))
    filter_upwards with y
    simp only [ContinuousLinearMap.lsmul_apply, norm_smul, Real.norm_eq_abs]
    ring
  have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
  rw [L2.inner_def] at hcs
  have heq :
      (∫ y : E, |frechetKolmogorovKernel (E := E) r hr (x - y)| * ‖(f : E → ℝ) y‖
          ∂(volume : Measure E)) =
        ∫ y : E, inner ℝ ((ha.toLp _ : E → ℝ) y) ((hb.toLp _ : E → ℝ) y)
          ∂(volume : Measure E) := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y hay hby
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hay, hby, mul_comm]
  have hna : ‖ha.toLp _‖ = ‖frechetKolmogorovKernelL2 (E := E) r hr‖ := by
    rw [frechetKolmogorovKernelL2, Lp.norm_toLp, Lp.norm_toLp]
    congr 1
    have habs : AEStronglyMeasurable
        (fun y : E => |frechetKolmogorovKernel (E := E) r hr y|) (volume : Measure E) :=
      hηaesm.norm.congr (by filter_upwards with y using (Real.norm_eq_abs _))
    rw [show (fun y : E => |frechetKolmogorovKernel (E := E) r hr (x - y)|) =
        (fun y : E => |frechetKolmogorovKernel (E := E) r hr y|) ∘ (fun y => x - y) from rfl,
      eLpNorm_comp_measurePreserving habs hmp]
    rw [show (fun y : E => |frechetKolmogorovKernel (E := E) r hr y|) =
        (fun y : E => ‖frechetKolmogorovKernel (E := E) r hr y‖) from
          funext fun y => (Real.norm_eq_abs _).symm,
      eLpNorm_norm]
  have hnb : ‖hb.toLp _‖ = ‖f‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, ← eLpNorm_norm (f : E → ℝ)]
  calc
    ‖frechetKolmogorovMollify (E := E) r hr f x‖
        ≤ ∫ y : E, |frechetKolmogorovKernel (E := E) r hr (x - y)| * ‖(f : E → ℝ) y‖
            ∂(volume : Measure E) := hstep
    _ = ∫ y : E, inner ℝ ((ha.toLp _ : E → ℝ) y) ((hb.toLp _ : E → ℝ) y)
          ∂(volume : Measure E) := heq
    _ ≤ ‖ha.toLp _‖ * ‖hb.toLp _‖ := hcs
    _ = ‖frechetKolmogorovKernelL2 (E := E) r hr‖ * ‖f‖ := by rw [hna, hnb]

/-- The pointwise representative of a translated-kernel difference. -/
private theorem coeFn_translate_frechetKolmogorovKernelL2_sub (r : ℝ) (hr : 0 < r) (v : E) :
    ((translateL2 v (frechetKolmogorovKernelL2 (E := E) r hr) -
        frechetKolmogorovKernelL2 (E := E) r hr : Lp ℝ 2 (volume : Measure E)) : E → ℝ)
      =ᵐ[volume] fun w : E =>
        frechetKolmogorovKernel (E := E) r hr (w + v) -
          frechetKolmogorovKernel (E := E) r hr w := by
  have hsub := Lp.coeFn_sub
    (translateL2 v (frechetKolmogorovKernelL2 (E := E) r hr))
    (frechetKolmogorovKernelL2 (E := E) r hr)
  have htr : (translateL2 v (frechetKolmogorovKernelL2 (E := E) r hr) : E → ℝ)
      =ᵐ[volume] fun w : E =>
        (frechetKolmogorovKernelL2 (E := E) r hr : E → ℝ) (w + v) :=
    coeFn_translateL2 v (frechetKolmogorovKernelL2 (E := E) r hr)
  have hker : (frechetKolmogorovKernelL2 (E := E) r hr : E → ℝ)
      =ᵐ[volume] frechetKolmogorovKernel (E := E) r hr := by
    rw [frechetKolmogorovKernelL2]
    exact MemLp.coeFn_toLp _
  have hkershift :
      (fun w : E => (frechetKolmogorovKernelL2 (E := E) r hr : E → ℝ) (w + v))
        =ᵐ[volume] fun w : E => frechetKolmogorovKernel (E := E) r hr (w + v) :=
    (measurePreserving_add_right (volume : Measure E) v).quasiMeasurePreserving.ae_eq_comp hker
  filter_upwards [hsub, htr, hkershift, hker] with w hw1 hw2 hw3 hw4
  rw [hw1]
  simp only [Pi.sub_apply]
  rw [hw2, hw3, hw4]

/-- The `L²` norm of a translated kernel-slice difference is the kernel translation modulus. -/
private theorem norm_toLp_frechetKolmogorovKernel_slice_sub_eq (r : ℝ) (hr : 0 < r)
    (x y : E)
    (ha : MemLp
      (fun z : E =>
        |frechetKolmogorovKernel (E := E) r hr (x - z) -
          frechetKolmogorovKernel (E := E) r hr (y - z)|)
      2 (volume : Measure E)) :
    ‖ha.toLp _‖ =
      ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
        frechetKolmogorovKernelL2 (E := E) r hr‖ := by
  have hηmem : MemLp (frechetKolmogorovKernel (E := E) r hr) 2 (volume : Measure E) :=
    (contDiff_frechetKolmogorovKernel (E := E) r hr).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_frechetKolmogorovKernel (E := E) r hr)
  have hηaesm : AEStronglyMeasurable (frechetKolmogorovKernel (E := E) r hr)
      (volume : Measure E) := hηmem.aestronglyMeasurable
  have hmpy := Measure.measurePreserving_sub_left (volume : Measure E) y
  rw [Lp.norm_toLp]
  rw [Lp.norm_def,
    eLpNorm_congr_ae (coeFn_translate_frechetKolmogorovKernelL2_sub (E := E) r hr (x - y))]
  have hcompose :
      (fun z : E =>
        |frechetKolmogorovKernel (E := E) r hr (x - z) -
          frechetKolmogorovKernel (E := E) r hr (y - z)|) =
        (fun w : E =>
          |frechetKolmogorovKernel (E := E) r hr (w + (x - y)) -
            frechetKolmogorovKernel (E := E) r hr w|) ∘ (fun z : E => y - z) := by
    funext z
    simp only [Function.comp_apply]
    congr 2
    congr 1
    abel
  have hshiftm : AEStronglyMeasurable
      (fun w : E => frechetKolmogorovKernel (E := E) r hr (w + (x - y)))
      (volume : Measure E) :=
    hηaesm.comp_measurePreserving
      (measurePreserving_add_right (volume : Measure E) (x - y))
  have habsm : AEStronglyMeasurable
      (fun w : E =>
        |frechetKolmogorovKernel (E := E) r hr (w + (x - y)) -
          frechetKolmogorovKernel (E := E) r hr w|)
      (volume : Measure E) :=
    (hshiftm.sub hηaesm).norm.congr (by filter_upwards with w using (Real.norm_eq_abs _))
  rw [hcompose, eLpNorm_comp_measurePreserving habsm hmpy]
  rw [show (fun w : E =>
      |frechetKolmogorovKernel (E := E) r hr (w + (x - y)) -
        frechetKolmogorovKernel (E := E) r hr w|) =
      (fun w : E =>
        ‖frechetKolmogorovKernel (E := E) r hr (w + (x - y)) -
          frechetKolmogorovKernel (E := E) r hr w‖) from
        funext fun w => (Real.norm_eq_abs _).symm,
    eLpNorm_norm]

/-- The mollified function inherits a quantitative modulus of continuity from the kernel. -/
private theorem norm_frechetKolmogorovMollify_sub_le (r : ℝ) (hr : 0 < r)
    (f : Lp ℝ 2 (volume : Measure E)) (x y : E) :
    ‖frechetKolmogorovMollify (E := E) r hr f x -
        frechetKolmogorovMollify (E := E) r hr f y‖ ≤
      ‖f‖ *
        ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
          frechetKolmogorovKernelL2 (E := E) r hr‖ := by
  classical
  have hηmem : MemLp (frechetKolmogorovKernel (E := E) r hr) 2 (volume : Measure E) :=
    (contDiff_frechetKolmogorovKernel (E := E) r hr).continuous.memLp_of_hasCompactSupport
      (hasCompactSupport_frechetKolmogorovKernel (E := E) r hr)
  have hmpx := Measure.measurePreserving_sub_left (volume : Measure E) x
  have hmpy := Measure.measurePreserving_sub_left (volume : Measure E) y
  have haxmem : MemLp (fun z : E => frechetKolmogorovKernel (E := E) r hr (x - z)) 2
      (volume : Measure E) := hηmem.comp_measurePreserving hmpx
  have haymem : MemLp (fun z : E => frechetKolmogorovKernel (E := E) r hr (y - z)) 2
      (volume : Measure E) := hηmem.comp_measurePreserving hmpy
  have ha : MemLp
      (fun z : E =>
        |frechetKolmogorovKernel (E := E) r hr (x - z) -
          frechetKolmogorovKernel (E := E) r hr (y - z)|)
      2 (volume : Measure E) := (haxmem.sub haymem).abs
  have hb : MemLp (fun z : E => ‖(f : E → ℝ) z‖) 2 (volume : Measure E) :=
    (Lp.memLp f).norm
  have hfx : Integrable
      (fun z : E => (f : E → ℝ) z * frechetKolmogorovKernel (E := E) r hr (x - z))
      (volume : Measure E) :=
    MemLp.integrable_mul (q := 2) (Lp.memLp f) haxmem
  have hfy : Integrable
      (fun z : E => (f : E → ℝ) z * frechetKolmogorovKernel (E := E) r hr (y - z))
      (volume : Measure E) :=
    MemLp.integrable_mul (q := 2) (Lp.memLp f) haymem
  have hdiff :
      frechetKolmogorovMollify (E := E) r hr f x -
          frechetKolmogorovMollify (E := E) r hr f y =
        ∫ z : E, (f : E → ℝ) z *
          (frechetKolmogorovKernel (E := E) r hr (x - z) -
            frechetKolmogorovKernel (E := E) r hr (y - z))
          ∂(volume : Measure E) := by
    simp only [frechetKolmogorovMollify, MeasureTheory.convolution,
      ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    rw [← integral_sub hfx hfy]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  have hstep :
      ‖frechetKolmogorovMollify (E := E) r hr f x -
          frechetKolmogorovMollify (E := E) r hr f y‖ ≤
        ∫ z : E,
          |frechetKolmogorovKernel (E := E) r hr (x - z) -
            frechetKolmogorovKernel (E := E) r hr (y - z)| * ‖(f : E → ℝ) z‖
          ∂(volume : Measure E) := by
    rw [hdiff]
    refine le_trans (norm_integral_le_integral_norm _) (le_of_eq (integral_congr_ae ?_))
    filter_upwards with z
    simp only [norm_mul, Real.norm_eq_abs]
    ring
  have hcs := real_inner_le_norm (ha.toLp _) (hb.toLp _)
  rw [L2.inner_def] at hcs
  have heq :
      (∫ z : E,
          |frechetKolmogorovKernel (E := E) r hr (x - z) -
            frechetKolmogorovKernel (E := E) r hr (y - z)| * ‖(f : E → ℝ) z‖
          ∂(volume : Measure E)) =
        ∫ z : E, inner ℝ ((ha.toLp _ : E → ℝ) z) ((hb.toLp _ : E → ℝ) z)
          ∂(volume : Measure E) := by
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with z haz hbz
    simp only [RCLike.inner_apply, conj_trivial]
    rw [haz, hbz, mul_comm]
  have hna : ‖ha.toLp _‖ =
      ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
        frechetKolmogorovKernelL2 (E := E) r hr‖ :=
    norm_toLp_frechetKolmogorovKernel_slice_sub_eq (E := E) r hr x y ha
  have hnb : ‖hb.toLp _‖ = ‖f‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, ← eLpNorm_norm (f : E → ℝ)]
  calc
    ‖frechetKolmogorovMollify (E := E) r hr f x -
        frechetKolmogorovMollify (E := E) r hr f y‖
        ≤ ∫ z : E,
            |frechetKolmogorovKernel (E := E) r hr (x - z) -
              frechetKolmogorovKernel (E := E) r hr (y - z)| * ‖(f : E → ℝ) z‖
            ∂(volume : Measure E) := hstep
    _ = ∫ z : E, inner ℝ ((ha.toLp _ : E → ℝ) z) ((hb.toLp _ : E → ℝ) z)
          ∂(volume : Measure E) := heq
    _ ≤ ‖ha.toLp _‖ * ‖hb.toLp _‖ := hcs
    _ = ‖f‖ *
        ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
          frechetKolmogorovKernelL2 (E := E) r hr‖ := by rw [hna, hnb, mul_comm]

/-! ### Uniform bounds for a mollified family -/

/-- A globally `L²`-bounded family has a common pointwise bound after mollification. -/
private theorem mollified_family_uniformly_bounded (r : ℝ) (hr : 0 < r) (C : ℝ)
    (S : Set (Lp ℝ 2 (volume : Measure E))) (hbd : ∀ f ∈ S, ‖f‖ ≤ C) :
    ∃ B : ℝ, ∀ f ∈ S, ∀ x : E,
      ‖frechetKolmogorovMollify (E := E) r hr f x‖ ≤ B := by
  refine ⟨‖frechetKolmogorovKernelL2 (E := E) r hr‖ * max C 0, fun f hf x => ?_⟩
  calc
    ‖frechetKolmogorovMollify (E := E) r hr f x‖
        ≤ ‖frechetKolmogorovKernelL2 (E := E) r hr‖ * ‖f‖ :=
      norm_frechetKolmogorovMollify_le (E := E) r hr f x
    _ ≤ ‖frechetKolmogorovKernelL2 (E := E) r hr‖ * max C 0 :=
      mul_le_mul_of_nonneg_left ((hbd f hf).trans (le_max_left C 0)) (norm_nonneg _)

/-- A globally `L²`-bounded family is uniformly equicontinuous after mollification.  The modulus is
controlled solely by the common `L²` bound and the kernel's own `L²` translation modulus. -/
private theorem mollified_family_equicontinuous (r : ℝ) (hr : 0 < r) (C : ℝ)
    (S : Set (Lp ℝ 2 (volume : Measure E))) (hbd : ∀ f ∈ S, ‖f‖ ≤ C) :
    ∀ ε > 0, ∃ δ > 0, ∀ f ∈ S, ∀ x y : E, ‖x - y‖ < δ →
      ‖frechetKolmogorovMollify (E := E) r hr f x -
        frechetKolmogorovMollify (E := E) r hr f y‖ < ε := by
  intro ε hε
  set M : ℝ := max C 0 + 1 with hM
  have hMpos : 0 < M := by positivity
  have htend := tendsto_norm_translate_frechetKolmogorovKernelL2_sub (E := E) r hr
  have hpos : 0 < ε / M := div_pos hε hMpos
  have hball : {z : ℝ | z < ε / M} ∈ 𝓝 (0 : ℝ) :=
    IsOpen.mem_nhds isOpen_Iio (by simpa using hpos)
  have hpre :
      (fun h : E =>
        ‖translateL2 h (frechetKolmogorovKernelL2 (E := E) r hr) -
          frechetKolmogorovKernelL2 (E := E) r hr‖) ⁻¹' {z : ℝ | z < ε / M} ∈
        𝓝 (0 : E) := htend hball
  rw [Metric.mem_nhds_iff] at hpre
  obtain ⟨δ, hδpos, hδsub⟩ := hpre
  refine ⟨δ, hδpos, fun f hf x y hxy => ?_⟩
  have hmem : x - y ∈ Metric.ball (0 : E) δ := by
    simp only [Metric.mem_ball, dist_zero_right]
    simpa using hxy
  have hmod_lt :
      ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
        frechetKolmogorovKernelL2 (E := E) r hr‖ < ε / M :=
    hδsub hmem
  have hmod_nonneg : 0 ≤
      ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
        frechetKolmogorovKernelL2 (E := E) r hr‖ := norm_nonneg _
  have hCM : C ≤ M := by
    rw [hM]
    linarith [le_max_left C 0]
  have hmass : ‖f‖ ≤ M := (hbd f hf).trans hCM
  calc
    ‖frechetKolmogorovMollify (E := E) r hr f x -
        frechetKolmogorovMollify (E := E) r hr f y‖
        ≤ ‖f‖ *
          ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
            frechetKolmogorovKernelL2 (E := E) r hr‖ :=
      norm_frechetKolmogorovMollify_sub_le (E := E) r hr f x y
    _ ≤ M *
          ‖translateL2 (x - y) (frechetKolmogorovKernelL2 (E := E) r hr) -
            frechetKolmogorovKernelL2 (E := E) r hr‖ :=
      mul_le_mul_of_nonneg_right hmass hmod_nonneg
    _ < M * (ε / M) := mul_lt_mul_of_pos_left hmod_lt hMpos
    _ = ε := by field_simp

end TauCeti

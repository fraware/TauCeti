/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev

/-!
# Mass-floor Gårding bound on `H¹(Ω)`

This file lifts the integrated mass-floor Gårding estimate to Sobolev functions. A uniform lower
bound on the mass coefficient contributes directly to the `L²` part of the `H¹` graph norm and
can therefore remove the negative value term created when the drift is absorbed by Young's
inequality.

## Main declaration

* `TauCeti.PDE.UniformlyEllipticOn.garding_energyFormH1_self_of_mass_lower_bound`.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open MeasureTheory Set TopologicalSpace

section Domain

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ}
  {lam Lam beta gamma massFloor : ℝ}

namespace UniformlyEllipticOn

/-- **Gårding's inequality with a mass floor on `H¹(Ω)`.** If the mass coefficient is bounded
below by `μ`, then

`(λ/2)‖∇u‖² + (μ - β²/(2λ))‖u‖² ≤ a(u,u)`.

This is the Sobolev-function form of
`TauCeti.PDE.UniformlyEllipticOn.garding_energyFormIntegral_self_of_mass_lower_bound_on`.
It retains the contribution of the mass floor instead of discarding it as the nonnegative-mass
Gårding bound does. -/
theorem garding_energyFormH1_self_of_mass_lower_bound
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), massFloor ≤ c x)
    (u : W1p mu Omega 2) :
    lam / 2 * ‖W1p.gradient u‖ ^ 2 +
        (massFloor - beta ^ 2 / (2 * lam)) * ‖W1p.value u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  have hmem : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hgrad := integrable_norm_jetField_snd_sq u
  have hval := integrable_jetField_fst_sq u
  have hlower : Integrable
      (fun x => lam / 2 * ‖(jetField u x).2‖ ^ 2 +
        (massFloor - beta ^ 2 / (2 * lam)) * (jetField u x).1 ^ 2)
      (mu.restrict Omega) :=
    (hgrad.const_mul _).add (hval.const_mul _)
  have hClassical :
      @UniformlyEllipticOn (EuclideanSpace ℝ ι) ι _ (Classical.decEq ι)
        (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam := by
    rwa [Subsingleton.elim (Classical.decEq ι) ‹DecidableEq ι›]
  have key := garding_energyFormIntegral_self_of_mass_lower_bound_on
    (μ := mu.restrict Omega) (U := jetField u) hClassical hmem
    (hmem.mono hb_bound) (hmem.mono hc_lower) hlower
    (integrable_energyIntegrand_jetField h ha hb hc hb_bound hc_bound u u)
  rw [energyFormH1_def]
  rw [energyFormIntegral_def] at key
  refine le_trans (le_of_eq ?_) key
  rw [integral_add (hgrad.const_mul _) (hval.const_mul _), integral_const_mul,
    integral_const_mul, integral_norm_jetField_snd_sq_eq_norm_gradient_sq,
    integral_jetField_fst_sq_eq_norm_value_sq]

end UniformlyEllipticOn

end Domain

end PDE

end TauCeti
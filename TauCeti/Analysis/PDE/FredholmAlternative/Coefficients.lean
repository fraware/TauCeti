/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FredholmAlternative

/-!
# The Fredholm alternative from coefficient bounds

This file closes the coefficient-level reduction behind Lane D.18 of the PDE roadmap. For a
uniformly elliptic divergence-form operator with bounded measurable drift and mass coefficients,
add a scalar mass large enough to make the energy form coercive. The compact-perturbation
Fredholm alternative from `TauCeti.Analysis.PDE.FredholmAlternative` then applies, and
subtracting the same scalar mass recovers the original weak Dirichlet problem.

If the ellipticity floor is `λ > 0`, the drift is bounded by `β`, and `|c| ≤ γ`, the chosen shift is

`κ = γ + β²/(2λ) + λ/2`.

The shifted mass coefficient has lower bound `β²/(2λ) + λ/2`, so the mass-floor Gårding estimate
gives the explicit coercivity bound `(λ/2) ‖u‖²_{H¹}`. No Poincaré estimate, drift-smallness
condition, or sign condition on the original mass coefficient is used in this reduction.

## Main declaration

* `TauCeti.PDE.UniformlyEllipticOn.fredholmAlternative_isWeakSolutionDirichlet_of_bounds`:
  the Fredholm dichotomy for bounded measurable coefficients on a bounded domain, with the
  homogeneous weak-solution space exhibited as a nontrivial finite-dimensional subspace in the
  non-unique branch.

## References

Lane D, item 18 of `TauCetiRoadmap/PDE/README.md`; L. C. Evans, *Partial Differential Equations*,
Section 6.2.3; D. Gilbarg and N. Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Chapter 8, Theorem 8.3.
-/

public section

noncomputable section

namespace TauCeti

namespace PDE

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal InnerProduct InnerProductSpace

variable {ι : Type*} [Fintype ι] {mu : Measure (EuclideanSpace ℝ ι)} [mu.IsAddHaarMeasure]
  {Omega : Opens (EuclideanSpace ℝ ι)} {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ}
  {b : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι}
  {c : EuclideanSpace ℝ ι → ℝ} {lam Lam beta gamma : ℝ}

noncomputable local instance instDecidableEqFredholmCoefficients : DecidableEq ι :=
  Classical.decEq ι

/-- Adding a constant to the mass coefficient adds the corresponding `L²` mass form. The
integrability hypothesis is exactly what is needed to use linearity of the Bochner integral. -/
private theorem energyFormH1_add_const_mass
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (kappa : ℝ) (u v : W1p mu Omega 2) :
    energyFormH1 a b (fun x => c x + kappa) u v =
      energyFormH1 a b c u v +
        kappa * ⟪W1p.value u, W1p.value v⟫_ℝ := by
  have hbase := integrable_energyIntegrand_jetField hcoeff u v
  have hinner := L2.integrable_inner (𝕜 := ℝ) (W1p.value u) (W1p.value v)
  rw [energyFormH1_def, energyFormH1_def, L2.inner_def, ← integral_const_mul]
  rw [← integral_add hbase (hinner.const_mul kappa)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [energyIntegrand_apply, massForm_apply, jetField_apply, RCLike.inner_apply]
    ring

/-- A scalar mass shift of `c + κ` by `κ` is exactly the weak problem with mass coefficient `c`.
The bounded-coefficient hypothesis prevents any non-integrable Bochner-integral degeneracy. -/
private theorem isWeakSolutionDirichletMassShift_add_const_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (kappa : ℝ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b (fun x => c x + kappa) kappa f u ↔
      IsWeakSolutionDirichlet a b c f u := by
  rw [isWeakSolutionDirichletMassShift_iff, isWeakSolutionDirichlet_iff]
  constructor
  · intro hu v
    have hv := hu v
    rw [energyFormH1_add_const_mass hcoeff kappa] at hv
    simpa using hv
  · intro hu v
    rw [energyFormH1_add_const_mass hcoeff kappa]
    simpa using hu v

/-- Sobolev-level Gårding lower bound with an arbitrary lower floor on the mass coefficient.
This is kept proof-local because its consumer here is the coefficient-level Fredholm reduction. -/
private theorem garding_energyFormH1_self_of_mass_lower_bound
    {muFloor : ℝ}
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_lower : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), muFloor ≤ c x)
    (u : W1p mu Omega 2) :
    lam / 2 * ‖W1p.gradient u‖ ^ 2 +
        (muFloor - beta ^ 2 / (2 * lam)) * ‖W1p.value u‖ ^ 2
      ≤ energyFormH1 a b c u u := by
  have hmem : ∀ᵐ x ∂mu.restrict (Omega : Set (EuclideanSpace ℝ ι)),
      x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hgrad := integrable_norm_jetField_snd_sq u
  have hval := integrable_jetField_fst_sq u
  have hlower : Integrable (fun x => lam / 2 * ‖(jetField u x).2‖ ^ 2 +
      (muFloor - beta ^ 2 / (2 * lam)) * (jetField u x).1 ^ 2) (mu.restrict Omega) :=
    (hgrad.const_mul _).add (hval.const_mul _)
  have key := UniformlyEllipticOn.garding_energyFormIntegral_self_of_mass_lower_bound_on
    (μ := mu.restrict Omega) (U := jetField u) h hmem
    (hmem.mono hb_bound) (hmem.mono hc_lower) hlower
    (integrable_energyIntegrand_jetField hcoeff u u)
  rw [energyFormH1_def]
  rw [energyFormIntegral_def] at key
  refine le_trans (le_of_eq ?_) key
  rw [integral_add (hgrad.const_mul _) (hval.const_mul _), integral_const_mul,
    integral_const_mul, integral_norm_jetField_snd_sq_eq_norm_gradient_sq,
    integral_jetField_fst_sq_eq_norm_value_sq]

/-- Membership in the compact-perturbation kernel is exactly the homogeneous weak Dirichlet
equation after undoing the scalar mass shift. Kept private so the coefficient theorem exposes the
solution space without adding a second public kernel abstraction. -/
private theorem mem_ker_one_sub_smul_dirichletMassOperator_iff_isWeakSolutionDirichlet
    (kappa : ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (hcoeffShift :
      MemLp (fun x => energyIntegrand (a x) (b x) (c x + kappa)) ⊤ (mu.restrict Omega))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeffShift)) (u : W1p0 mu Omega 2) :
    u ∈ LinearMap.ker
      ((1 - kappa • dirichletMassOperator hcoeffShift hcoercive :
        W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) :
          W1p0 mu Omega 2 →ₗ[ℝ] W1p0 mu Omega 2) ↔
      IsWeakSolutionDirichlet a b c 0 u := by
  rw [LinearMap.mem_ker]
  have hzeroSol :
      IsWeakSolutionDirichlet a b (fun x => c x + kappa) 0 (0 : W1p0 mu Omega 2) := by
    rw [isWeakSolutionDirichlet_iff]
    intro v
    rw [← dirichletForcing_apply_eq_setIntegral]
    have hnorm_le : ‖dirichletForcing (0 : Lp ℝ 2 (mu.restrict Omega)) v‖ ≤ 0 := by
      calc
        ‖dirichletForcing (0 : Lp ℝ 2 (mu.restrict Omega)) v‖
            ≤ ‖(0 : Lp ℝ 2 (mu.restrict Omega))‖ * ‖v‖ :=
          norm_dirichletForcing_apply_le (0 : Lp ℝ 2 (mu.restrict Omega)) v
        _ = 0 := by simp
    have hnorm : ‖dirichletForcing (0 : Lp ℝ 2 (mu.restrict Omega)) v‖ = 0 :=
      le_antisymm hnorm_le (norm_nonneg _)
    have hforcing : dirichletForcing (0 : Lp ℝ 2 (mu.restrict Omega)) v = 0 :=
      norm_eq_zero.mp hnorm
    simp [hforcing]
  have hzero : weakSolutionDirichlet hcoeffShift hcoercive 0 = 0 :=
    (eq_weakSolutionDirichlet hcoeffShift hcoercive hzeroSol).symm
  constructor
  · intro hop
    have hop' :
        (1 - kappa • dirichletMassOperator hcoeffShift hcoercive :
          W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) u =
            weakSolutionDirichlet hcoeffShift hcoercive 0 :=
      hop.trans hzero.symm
    have hshift :
        IsWeakSolutionDirichletMassShift a b (fun x => c x + kappa) kappa 0 u :=
      (isWeakSolutionDirichletMassShift_iff_operator_eq
        hcoeffShift hcoercive kappa 0 u).2 hop'
    exact (isWeakSolutionDirichletMassShift_add_const_iff hcoeff kappa 0 u).1 hshift
  · intro hu
    have hshift :
        IsWeakSolutionDirichletMassShift a b (fun x => c x + kappa) kappa 0 u :=
      (isWeakSolutionDirichletMassShift_add_const_iff hcoeff kappa 0 u).2 hu
    have hop' :
        (1 - kappa • dirichletMassOperator hcoeffShift hcoercive :
          W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) u =
            weakSolutionDirichlet hcoeffShift hcoercive 0 :=
      (isWeakSolutionDirichletMassShift_iff_operator_eq
        hcoeffShift hcoercive kappa 0 u).1 hshift
    exact hop'.trans hzero

namespace UniformlyEllipticOn

/-- **The coefficient-level Fredholm alternative for the weak Dirichlet problem.**

Let `a` be uniformly elliptic with constants `0 < λ ≤ Λ`, let the measurable drift satisfy
`‖b‖ ≤ β`, and let the measurable mass coefficient satisfy `‖c‖ ≤ γ`. On a bounded domain,
either the homogeneous weak-solution space is a nontrivial finite-dimensional subspace of
`H¹₀(Ω)`, or every `L²` forcing has a unique weak solution.

The proof shifts the mass by
`κ = γ + β²/(2λ) + λ/2`. The shifted form is coercive with explicit constant `λ/2`; Rellich then
makes the mass perturbation compact, so the existing variational Fredholm alternative applies.
The finite-dimensional kernel is characterized extensionally by the original homogeneous weak
equation, and the shift is eliminated before the coefficient-level conclusion is stated. -/
theorem fredholmAlternative_isWeakSolutionDirichlet_of_bounds
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega))
    (hb : AEStronglyMeasurable b (mu.restrict Omega))
    (hc : AEStronglyMeasurable c (mu.restrict Omega))
    (hb_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖b x‖ ≤ beta)
    (hc_bound : ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x‖ ≤ gamma)
    (hOmega : IsBounded (Omega : Set (EuclideanSpace ℝ ι))) :
    (∃ K : Submodule ℝ (W1p0 mu Omega 2),
        K ≠ ⊥ ∧ FiniteDimensional ℝ K ∧
          ∀ u : W1p0 mu Omega 2, u ∈ K ↔ IsWeakSolutionDirichlet a b c 0 u) ∨
      ∀ f : Lp ℝ 2 (mu.restrict Omega),
        ∃! u : W1p0 mu Omega 2, IsWeakSolutionDirichlet a b c f u := by
  let muFloor : ℝ := beta ^ 2 / (2 * lam) + lam / 2
  let kappa : ℝ := gamma + muFloor
  have hcoeff :
      MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega) := by
    exact memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_bound
  have hc_shift_meas :
      AEStronglyMeasurable (fun x => c x + kappa) (mu.restrict Omega) :=
    hc.add aestronglyMeasurable_const
  have hc_shift_bound :
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), ‖c x + kappa‖ ≤ gamma + ‖kappa‖ := by
    intro x hx
    exact (norm_add_le _ _).trans (add_le_add (hc_bound x hx) le_rfl)
  have hcoeffShift :
      MemLp (fun x => energyIntegrand (a x) (b x) (c x + kappa)) ⊤
        (mu.restrict Omega) := by
    exact memLp_energyIntegrand_of_bounds h.upper_nonneg ha hb hc_shift_meas
      (fun _x hx eta xi => h.upper_bound hx eta xi) hb_bound hc_shift_bound
  have hc_shift_lower :
      ∀ x ∈ (Omega : Set (EuclideanSpace ℝ ι)), muFloor ≤ c x + kappa := by
    intro x hx
    have habs : |c x| ≤ gamma := by
      simpa [Real.norm_eq_abs] using hc_bound x hx
    have hcge : -gamma ≤ c x := (abs_le.mp habs).1
    dsimp [kappa]
    linarith
  have hlower : ∀ w : W1p0 mu Omega 2,
      lam / 2 * ‖w‖ ^ 2 ≤
        energyFormH1 a b (fun x => c x + kappa)
          (w : W1p mu Omega 2) (w : W1p mu Omega 2) := by
    intro w
    have hg := garding_energyFormH1_self_of_mass_lower_bound
      (muFloor := muFloor) h hcoeffShift hb_bound hc_shift_lower (w : W1p mu Omega 2)
    -- `W1p0` is a closed subspace of `W1p`; expose its inherited ambient norm so the
    -- established value-gradient norm identity applies without introducing a duplicate lemma.
    change lam / 2 * ‖(w : W1p mu Omega 2)‖ ^ 2 ≤ _
    rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
    have hcoeffEq : muFloor - beta ^ 2 / (2 * lam) = lam / 2 := by
      dsimp [muFloor]
      ring
    rw [hcoeffEq] at hg
    simpa [mul_add, add_comm] using hg
  have hcoercive : IsCoercive (energyFormH1L0 hcoeffShift) :=
    isCoercive_energyFormH1L0 hcoeffShift (half_pos h.pos) hlower
  let K : Submodule ℝ (W1p0 mu Omega 2) :=
    LinearMap.ker
      ((1 - kappa • dirichletMassOperator hcoeffShift hcoercive :
        W1p0 mu Omega 2 →L[ℝ] W1p0 mu Omega 2) :
          W1p0 mu Omega 2 →ₗ[ℝ] W1p0 mu Omega 2)
  have hKfinite : FiniteDimensional ℝ K := by
    dsimp [K]
    exact finiteDimensional_ker_one_sub_smul_dirichletMassOperator
      hcoeffShift hcoercive hOmega kappa
  have hKmem (u : W1p0 mu Omega 2) :
      u ∈ K ↔ IsWeakSolutionDirichlet a b c 0 u := by
    dsimp [K]
    exact mem_ker_one_sub_smul_dirichletMassOperator_iff_isWeakSolutionDirichlet
      kappa hcoeff hcoeffShift hcoercive u
  rcases fredholmAlternative_isWeakSolutionDirichletMassShift
      hcoeffShift hcoercive hOmega kappa with hkernel | hsolvable
  · left
    have hKne : K ≠ ⊥ := by
      obtain ⟨u, hune, hu⟩ := hkernel
      have huK : u ∈ K := (hKmem u).2
        ((isWeakSolutionDirichletMassShift_add_const_iff hcoeff kappa 0 u).mp hu)
      intro hKbot
      have hu0 : u = 0 := by
        rw [hKbot] at huK
        simpa using huK
      exact hune hu0
    exact ⟨K, hKne, hKfinite, hKmem⟩
  · right
    intro f
    obtain ⟨u, hu, huniq⟩ := hsolvable f
    refine ⟨u, (isWeakSolutionDirichletMassShift_add_const_iff hcoeff kappa f u).mp hu, ?_⟩
    intro y hy
    exact huniq y ((isWeakSolutionDirichletMassShift_add_const_iff hcoeff kappa f y).mpr hy)

end UniformlyEllipticOn

end PDE

end TauCeti

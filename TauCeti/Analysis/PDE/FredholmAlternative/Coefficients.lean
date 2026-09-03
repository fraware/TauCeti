/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FredholmAlternative
public import TauCeti.Analysis.PDE.EnergyForm.MassFloor

/-!
# The Fredholm alternative from coefficient bounds

For bounded measurable coefficients on a bounded domain, an explicit mass shift makes the
Dirichlet form coercive. Rellich compactness and the existing mass-shift Fredholm theorem then give
the coefficient-level dichotomy for weak Dirichlet problems.

## Main declaration

* `TauCeti.PDE.UniformlyEllipticOn.fredholmAlternative_isWeakSolutionDirichlet_of_bounds`.

## References

L. C. Evans, *Partial Differential Equations*, Section 6.2.3; D. Gilbarg and N. Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Chapter 8, Theorem 8.3.
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

/-- Shifting `c + κ` by `κ` recovers the weak problem with mass coefficient `c`. -/
private theorem isWeakSolutionDirichletMassShift_add_const_iff
    (hcoeff : MemLp (fun x => energyIntegrand (a x) (b x) (c x)) ⊤ (mu.restrict Omega))
    (kappa : ℝ) (f : Lp ℝ 2 (mu.restrict Omega)) (u : W1p0 mu Omega 2) :
    IsWeakSolutionDirichletMassShift a b (fun x => c x + kappa) kappa f u ↔
      IsWeakSolutionDirichlet a b c f u := by
  have hadd (v : W1p0 mu Omega 2) :
      energyFormH1 a b (fun x => c x + kappa)
          (u : W1p mu Omega 2) (v : W1p mu Omega 2) =
        energyFormH1 a b c (u : W1p mu Omega 2) (v : W1p mu Omega 2) +
          kappa * ⟪W1p.value (u : W1p mu Omega 2),
            W1p.value (v : W1p mu Omega 2)⟫_ℝ := by
    have hbase := PDE.integrable_energyIntegrand_jetField hcoeff
      (u : W1p mu Omega 2) (v : W1p mu Omega 2)
    have hinner := L2.integrable_inner (𝕜 := ℝ)
      (W1p.value (u : W1p mu Omega 2)) (W1p.value (v : W1p mu Omega 2))
    rw [energyFormH1_def, energyFormH1_def, L2.inner_def, ← integral_const_mul]
    rw [← integral_add hbase (hinner.const_mul kappa)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp [energyIntegrand_apply, massForm_apply, jetField_apply, RCLike.inner_apply]
      ring
  rw [isWeakSolutionDirichletMassShift_iff, isWeakSolutionDirichlet_iff]
  constructor
  · intro hu v
    have hv := hu v
    rw [hadd v] at hv
    simpa using hv
  · intro hu v
    rw [hadd v]
    simpa using hu v

/-- The compact-perturbation kernel is the homogeneous weak-solution space after undoing the mass
shift. -/
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
    change energyFormH1 a b (fun x => c x + kappa) (0 : W1p mu Omega 2)
        (v : W1p mu Omega 2) =
      ∫ x in Omega, (0 : Lp ℝ 2 (mu.restrict Omega)) x *
        W1p.value (v : W1p mu Omega 2) x ∂mu
    rw [energyFormH1_zero_left]
    symm
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero (E := ℝ) (p := 2) (μ := mu.restrict Omega)] with x hx
    rw [hx]
    simp
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

/-- Fredholm alternative for a uniformly elliptic weak Dirichlet problem with bounded measurable
lower-order coefficients on a bounded domain. The non-unique branch is its nontrivial
finite-dimensional homogeneous solution space. -/
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
      h ha hb hc_shift_meas hb_bound hc_shift_bound hc_shift_lower
      (w : W1p mu Omega 2)
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

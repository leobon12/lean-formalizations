import InteractingSLE.Spec.Coupling.SafeStop
import QuantumZipper.Proofs.GFF.K3.C5Interface

/-!
# The Loewner Green energy is the covariance of a zero-boundary GFF

Packet PROVE-T11-L312 (Specification §3.3, L519 and L578: "`Var((h⁰, φ)) = E_τ(φ)`", "Since `E_t(φ) ≥ 0`, the
bracket increment is bounded by `E_0(φ)`", L550). For a continuous driver `w` with `w 0 = 0`, a time `t ≥ 0` and a
test function `ψ` on `ℍ` whose support avoids the hull `K_t`, the frozen energy
`E_t(ψ) = ∬ ψ(y) G(f_t y, f_t z) ψ(z)` is the dual Dirichlet norm `‖ψ‖²_{H⁻¹(ℍ ∖ K_t)}` of `ψ` (conformal
covariance of the Green function: `f_t` maps `ℍ ∖ K_t` conformally onto `ℍ`, QuantumZipper
`K3.isConformalOnto_fwdMap`, and LQGMetric `zeroGFFTestCov_eq_green`). In particular `E_t(ψ) ≥ 0`, so the
characteristic-function martingale `exp(iθ (𝔥_t, ψ) − θ² E_t(ψ)/2)` has modulus at most one.

## Main results

* `isProtected_of_disjoint`: a compact set avoiding `K_t` is protected at some positive height;
* `loewnerGreenEnergy_eq_zeroGFFTestCov`: `E_t(ψ) = zeroGFFTestCov (ℍ ∖ K_t) ψ ψ`;
* `loewnerGreenEnergy_nonneg`: `0 ≤ E_t(ψ)`;
* `norm_cexp_testMean_le_one`: `‖exp(iθX − θ² E/2)‖ ≤ 1` for `E ≥ 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open Ito

variable {w : ℝ → ℝ} {t : ℝ}

/-- `ℍ ∖ K_t` as an open set, for a continuous driver. -/
def hullComplOpens (hw : Continuous w) (ht : 0 ≤ t) : TopologicalSpace.Opens ℂ :=
  ⟨H \ fwdHull w t, FwdHolo.isOpen_compl_fwdHull hw ht⟩

theorem coe_hullComplOpens (hw : Continuous w) (ht : 0 ≤ t) :
    (hullComplOpens hw ht : Set ℂ) = H \ fwdHull w t := rfl

theorem tsupport_subset_H (ψ : LQGMetric.TestOn upperHalfPlaneOpens) : tsupport ψ ⊆ H :=
  ψ.tsupport_subset

/-- The support of `ψ`, as a subset of `ℍ ∖ K_t`. -/
theorem tsupport_subset_diff_fwdHull (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull w t)) : tsupport ψ ⊆ H \ fwdHull w t :=
  fun _ hz => ⟨tsupport_subset_H ψ hz, fun h => hψ.ne_of_mem hz h rfl⟩

/-- A test function on `ℍ` whose support avoids `K_t`, as a test function on `ℍ ∖ K_t`. -/
def testOnHullCompl (hw : Continuous w) (ht : 0 ≤ t) (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hψ : Disjoint (tsupport ψ) (fwdHull w t)) : LQGMetric.TestOn (hullComplOpens hw ht) where
  toFun := ψ
  contDiff' := ψ.contDiff
  hasCompactSupport' := ψ.hasCompactSupport
  tsupport_subset' := tsupport_subset_diff_fwdHull ψ hψ

@[simp] theorem coe_testOnHullCompl (hw : Continuous w) (ht : 0 ≤ t)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψ : Disjoint (tsupport ψ) (fwdHull w t)) :
    ⇑(testOnHullCompl hw ht ψ hψ) = ⇑ψ := rfl

/-- **A compact set avoiding the hull is protected**: if `K ⊆ ℍ ∖ K_t` is compact, then `Im f_t ≥ δ` on `K` for
some `δ > 0`. -/
theorem exists_isProtected_of_isCompact (hw : Continuous w) (ht : 0 ≤ t) {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ H \ fwdHull w t) : ∃ δ > 0, IsProtected w t δ K := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)⟩
  · have hc : ContinuousOn (fun z => (fwdMap w t z).im) K := fun z hz =>
      (Complex.continuous_im.continuousAt.comp
        (FwdHolo.hasDerivAt_fwdMap hw ht (hKH hz)).continuousAt).continuousWithinAt
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne hc
    exact ⟨(fwdMap w t z₀).im, im_fwdMap_pos hw ht (hKH hz₀) ⟨ht, le_rfl⟩,
      fun z hz => ⟨hKH hz, hmin hz⟩⟩

/-- The support of a test function avoiding `K_t` is protected at some positive height. -/
theorem exists_isProtected_tsupport (hw : Continuous w) (ht : 0 ≤ t)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψ : Disjoint (tsupport ψ) (fwdHull w t)) :
    ∃ δ > 0, IsProtected w t δ (tsupport ψ) :=
  exists_isProtected_of_isCompact hw ht ψ.hasCompactSupport.isCompact
    (tsupport_subset_diff_fwdHull ψ hψ)

/-- **Conformal covariance of the Loewner Green energy**: for a continuous driver `w` with `w 0 = 0` and a test
function `ψ` whose support avoids `K_t`, `E_t(ψ) = ‖ψ‖²_{H⁻¹(ℍ ∖ K_t)}`, the variance of `(h⁰, ψ)` for a
zero-boundary GFF `h⁰` on `ℍ ∖ K_t` (Specification L578, "`Var((h⁰, φ)) = E_τ(φ)`"). -/
theorem loewnerGreenEnergy_eq_zeroGFFTestCov (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψ : Disjoint (tsupport ψ) (fwdHull w t)) :
    loewnerGreenEnergy w t ψ =
      zeroGFFTestCov (hullComplOpens hw ht) (testOnHullCompl hw ht ψ hψ)
        (testOnHullCompl hw ht ψ hψ) := by
  obtain ⟨δ, hδ, hK⟩ := exists_isProtected_tsupport hw ht ψ hψ
  have hg := LQGMetric.zeroGFFTestCov_eq_green (V := hullComplOpens hw ht) sdiff_subset
    (K3.isConformalOnto_fwdMap hw hw0 ht) (testOnHullCompl hw ht ψ hψ)
    (testOnHullCompl hw ht ψ hψ)
  rw [hg, loewnerGreenEnergy_eq_integral_prod ψ.continuous ψ.hasCompactSupport hK hw ht hδ
    ⟨ht, le_rfl⟩]
  congr 1
  funext p
  simp only [energyIntegrand, coe_testOnHullCompl]
  ring

/-- **`E_t(ψ) ≥ 0`** for a test function whose support avoids `K_t` (continuous driver, `w 0 = 0`). -/
theorem loewnerGreenEnergy_nonneg (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t)
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) (hψ : Disjoint (tsupport ψ) (fwdHull w t)) :
    0 ≤ loewnerGreenEnergy w t ψ := by
  rw [loewnerGreenEnergy_eq_zeroGFFTestCov hw hw0 ht ψ hψ]
  exact LQGMetric.zeroGFFTestCov_self_nonneg
    (LQGMetric.zbAdmissible_of_subset_H (U := hullComplOpens hw ht) sdiff_subset) _

/-- `‖exp(iθX − θ² E/2)‖ ≤ 1` when `E ≥ 0`. -/
theorem norm_cexp_testMean_le_one (θ X : ℝ) {E : ℝ} (hE : 0 ≤ E) :
    ‖Complex.exp (Complex.I * θ * (X : ℂ) - θ ^ 2 * (E : ℂ) / 2)‖ ≤ 1 := by
  rw [Complex.norm_exp, re_cexp_arg, Real.exp_le_one_iff]
  have := mul_nonneg (sq_nonneg θ) hE
  linarith

end Coupling

end InteractingSLE

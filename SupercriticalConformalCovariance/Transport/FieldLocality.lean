import SupercriticalConformalCovariance.Transport.UniversalDomain
import SupercriticalConformalCovariance.Reversal.Inverse
import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SmallGammaGeodesics.CC.LocalityConf

/-! Restriction of the forward conformal field is a measurable function of the source restriction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set TopologicalSpace Function
open scoped Distributions
open LQGMetric (DistOn TestOn TestC pairJ pairJInv comb)
open scoped ENNReal
open SupercriticalConformalCovariance (IsConformalBijection confPullbackField confPushTest)

namespace SupercriticalConformalCovariance.Transport

variable {φ : ℂ → ℂ} {U V A B : Opens ℂ}

private def testV (hBA : B ≤ V) (c : LQGMetric.CoordJ) : TestOn V :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := B) (Ω₂ := V) (comb B c)

private def testC (hBA : B ≤ V) (c : LQGMetric.CoordJ) : TestC :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) (testV hBA c)

private theorem testC_support (hBA : B ≤ V) (c : LQGMetric.CoordJ) :
    tsupport (testC hBA c : ℂ → ℝ) ⊆ B := by
  have e : (testC hBA c : ℂ → ℝ) = comb B c := by
    funext x
    simp only [testC, testV, TestFunction.monoCLM_apply]
    rw [if_pos ⟨le_rfl, le_top⟩]
    simp only [TestFunction.monoCLM_apply]
    rw [if_pos ⟨le_rfl, hBA⟩]
  rw [e]
  exact (comb B c).tsupport_subset

private def pushedC (hφ : IsConformalBijection φ U V) (hBV : B ≤ V)
    (c : LQGMetric.CoordJ) : TestC :=
  TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤)
    (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (testV hBV c))

/-- A compactly contained source open set supports every pushed target-coordinate test. -/
theorem pushed_coord_support (hφ : IsConformalBijection φ U V)
    (hAU : A ≤ U) (hcl : closure (A : Set ℂ) ⊆ U)
    (hbd : Bornology.IsBounded (A : Set ℂ))
    (hB : (B : Set ℂ) = φ '' A) (hBV : B ≤ V) (c : LQGMetric.CoordJ) :
    tsupport (pushedC hφ hBV c : ℂ → ℝ) ⊆ A := by
  let hconf : SmallGammaGeodesics.CC.IsConfNbhd φ U A :=
    ⟨U.isOpen, A.isOpen, hbd, hcl, hφ.1, hφ.2.injOn⟩
  have hg : tsupport (testC hBV c : ℂ → ℝ) ⊆ φ '' A := by
    rw [← hB]
    exact testC_support hBV c
  have hpull : SmallGammaGeodesics.CC.IsConfPull φ U (testC hBV c)
      (pushedC hφ hBV c) := by
    intro x
    have he := SupercriticalConformalCovariance.Reversal.confPushTest_inverse_eq_confPullFun hφ (testV hBV c)
    have hc := congrFun he x
    simpa only [pushedC, testC, SmallGammaGeodesics.CC.coe_monoCLM_top,
      SmallGammaGeodesics.CC.confPullFun] using hc
  exact hpull.tsupport_subset_V hconf hg

private def pushedA (hφ : IsConformalBijection φ U V) (hAU : A ≤ U)
    (hcl : closure (A : Set ℂ) ⊆ U) (hbd : Bornology.IsBounded (A : Set ℂ))
    (hB : (B : Set ℂ) = φ '' A) (hBV : B ≤ V) (c : LQGMetric.CoordJ) : TestOn A :=
  SmallGammaGeodesics.CC.testOnOfSupp A (pushedC hφ hBV c)
    (pushed_coord_support hφ hAU hcl hbd hB hBV c)

private theorem pushedA_mono (hφ : IsConformalBijection φ U V) (hAU : A ≤ U)
    (hcl : closure (A : Set ℂ) ⊆ U) (hbd : Bornology.IsBounded (A : Set ℂ))
    (hB : (B : Set ℂ) = φ '' A) (hBV : B ≤ V) (c : LQGMetric.CoordJ) :
    TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := A) (Ω₂ := U)
      (pushedA hφ hAU hcl hbd hB hBV c) =
      confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (testV hBV c) := by
  ext x
  simp only [TestFunction.monoCLM_apply]
  rw [if_pos ⟨le_rfl, hAU⟩]
  change (pushedC hφ hBV c : ℂ → ℝ) x = _
  rw [show (pushedC hφ hBV c : ℂ → ℝ) =
    (confPushTest (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) (testV hBV c) : ℂ → ℝ) from
    SmallGammaGeodesics.CC.coe_monoCLM_top U _]

/-- The transported field restricted to `B = φ(A)` factors measurably through the source field
restricted to `A`. This is deterministic, independent of the GFF law. -/
theorem exists_measurable_forward_restrict (Q : ℝ) (hφ : IsConformalBijection φ U V)
    (hAU : A ≤ U) (hcl : closure (A : Set ℂ) ⊆ U)
    (hbd : Bornology.IsBounded (A : Set ℂ))
    (hB : (B : Set ℂ) = φ '' A) (hBV : B ≤ V) :
    ∃ R : DistOn A → DistOn B, Measurable R ∧
      ∀ h : DistOn U,
        SupercriticalConformalCovariance.Domain.restrictOn hBV
          (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) h) =
        R (SupercriticalConformalCovariance.Domain.restrictOn hAU h) := by
  let t : LQGMetric.CoordJ → TestOn A :=
    pushedA hφ hAU hcl hbd hB hBV
  let k : LQGMetric.CoordJ → ℝ := fun c =>
    Distribution.ofFun V (fun x => Q * Real.log ‖deriv (invFunOn φ U) x‖) volume ⊤
      (testV hBV c)
  let R : DistOn A → DistOn B := fun x => pairJInv B (fun c => x (t c) + k c)
  refine ⟨R, (LQGMetric.measurable_pairJInv B).comp
    (measurable_pi_iff.2 fun c => (LQGMetric.measurable_distOn_apply (t c)).add_const (k c)), ?_⟩
  intro h
  have he : (fun c => SupercriticalConformalCovariance.Domain.restrictOn hAU h (t c) + k c) =
      pairJ B (SupercriticalConformalCovariance.Domain.restrictOn hBV
        (confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) h)) := by
    funext c
    change h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := A) (Ω₂ := U) (t c)) + k c =
      confPullbackField Q (SupercriticalConformalCovariance.Reversal.inverse_conformal hφ) h (testV hBV c)
    rw [pushedA_mono hφ hAU hcl hbd hB hBV c]
    rfl
  change _ = pairJInv B (fun c => SupercriticalConformalCovariance.Domain.restrictOn hAU h (t c) + k c)
  rw [he, LQGMetric.pairJInv_pairJ]

end SupercriticalConformalCovariance.Transport

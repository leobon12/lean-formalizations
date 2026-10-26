import SupercriticalConformalCovariance.GPull.Correction

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set
open LQGMetric
open SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

theorem ofFun_continuousOn_apply {U : Opens ℂ} {u : ℂ → ℝ}
    (hu : ContinuousOn u (U : Set ℂ)) (ψ : TestOn U) :
    Distribution.ofFun U u volume ⊤ ψ = ∫ x, u x * ψ x := by
  have hloc : LocallyIntegrableOn u (U : Set ℂ) volume :=
    hu.locallyIntegrableOn U.isOpen.measurableSet
  rw [Distribution.ofFun_apply hloc]
  congr 1
  funext x
  simp only [smul_eq_mul]
  ring

theorem ofFun_extZ_apply_eq {U : Opens ℂ} (f : C(U, ℝ))
    {u : ℂ → ℝ} (hu : ContinuousOn u (U : Set ℂ))
    (hfu : ∀ x (hx : x ∈ (U : Set ℂ)), f ⟨x, hx⟩ = u x)
    (ψ : TestOn U) :
    Distribution.ofFun U (Function.extend Subtype.val f 0) volume ⊤ ψ =
      ∫ x, u x * ψ x := by
  have heq : Function.extend Subtype.val (f : U → ℝ) (0 : ℂ → ℝ)
      =ᵐ[volume.restrict (U : Set ℂ)] u := by
    apply (ae_restrict_iff' U.isOpen.measurableSet).2
    exact Filter.Eventually.of_forall fun x hx => by
      conv_lhs => rw [show x = ((⟨x, hx⟩ : U) : ℂ) from rfl]
      rw [Subtype.val_injective.extend_apply]
      exact hfu x hx
  rw [Distribution.ofFun_congr_ae heq]
  exact ofFun_continuousOn_apply hu ψ

theorem continuousOn_extZ {U : Opens ℂ} (f : C(U, ℝ)) :
    ContinuousOn (Function.extend Subtype.val f 0) (U : Set ℂ) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous fun x : U => Function.extend Subtype.val f 0 (x : ℂ)
  convert f.continuous using 1
  funext x
  exact Subtype.val_injective.extend_apply _ _ x

theorem ofFun_extZ_pair {U : Opens ℂ} (f : C(U, ℝ)) (ψ : TestOn U) :
    Distribution.ofFun U (Function.extend Subtype.val f 0) volume ⊤ ψ =
      ∫ x, Function.extend Subtype.val f 0 x * ψ x :=
  ofFun_continuousOn_apply (continuousOn_extZ f) ψ

theorem ofCont_restrict_pair {U : Opens ℂ} (c : C(ℂ, ℝ)) (ψ : TestOn U) :
    restrictTo U (ofCont c) ψ = ∫ x, c x * ψ x := by
  change ofCont c
    (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) ψ) = _
  rw [LQGMetric.ofCont_apply]
  simp only [TestFunction.monoCLM_apply]
  simp only [if_pos (show (⊤ : ℕ∞) ≤ ⊤ ∧ U ≤ ⊤ from ⟨le_refl _, le_top⟩)]
  change (∫ x, ψ x * c x) = _
  congr 1
  funext x
  ring

theorem ofFun_confPull_pair {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (f : C(V, ℝ)) (ψ : TestOn U) :
    (SupercriticalConformalCovariance.ZBConformal.distPullback hφ
      (Distribution.ofFun V (Function.extend Subtype.val f 0) volume ⊤)) ψ =
      ∫ x, Function.extend Subtype.val f 0 (φ x) * ψ x := by
  rw [SupercriticalConformalCovariance.ZBConformal.distPullback_apply, ofFun_extZ_pair]
  exact SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hφ ψ
    (Function.extend Subtype.val f 0)

theorem ofCont_confPull_pair {U V : Opens ℂ} {φ : ℂ → ℂ}
    (hφ : IsConformalBijection φ U V) (c : C(ℂ, ℝ)) (ψ : TestOn U) :
    (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V (ofCont c))) ψ =
      ∫ x, c (φ x) * ψ x := by
  rw [SupercriticalConformalCovariance.ZBConformal.distPullback_apply, ofCont_restrict_pair]
  exact SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hφ ψ c

theorem integral_test_add {U : Opens ℂ} {a b : ℂ → ℝ}
    (ha : ContinuousOn a (U : Set ℂ)) (hb : ContinuousOn b (U : Set ℂ))
    (ψ : TestOn U) :
    (∫ x, (a x + b x) * ψ x) =
      (∫ x, a x * ψ x) + ∫ x, b x * ψ x := by
  have ia : Integrable (fun x => a x * ψ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using ψ.integrable_smul
      (ha.locallyIntegrableOn (μ := volume) U.isOpen.measurableSet)
  have ib : Integrable (fun x => b x * ψ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using ψ.integrable_smul
      (hb.locallyIntegrableOn (μ := volume) U.isOpen.measurableSet)
  have he : (fun x => (a x + b x) * ψ x) =
      (fun x => a x * ψ x + b x * ψ x) := by funext x; ring
  rw [he, integral_add ia ib]

theorem integral_test_sub {U : Opens ℂ} {a b : ℂ → ℝ}
    (ha : ContinuousOn a (U : Set ℂ)) (hb : ContinuousOn b (U : Set ℂ))
    (ψ : TestOn U) :
    (∫ x, (a x - b x) * ψ x) =
      (∫ x, a x * ψ x) - ∫ x, b x * ψ x := by
  have ia : Integrable (fun x => a x * ψ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using ψ.integrable_smul
      (ha.locallyIntegrableOn (μ := volume) U.isOpen.measurableSet)
  have ib : Integrable (fun x => b x * ψ x) volume := by
    simpa only [smul_eq_mul, mul_comm] using ψ.integrable_smul
      (hb.locallyIntegrableOn (μ := volume) U.isOpen.measurableSet)
  have he : (fun x => (a x - b x) * ψ x) =
      (fun x => a x * ψ x - b x * ψ x) := by funext x; ring
  rw [he, integral_sub ia ib]


end SupercriticalConformalCovariance.GPull

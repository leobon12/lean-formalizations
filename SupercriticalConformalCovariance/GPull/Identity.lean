import SupercriticalConformalCovariance.GPull.Pairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory TopologicalSpace Set
open LQGMetric SupercriticalConformalCovariance

namespace SupercriticalConformalCovariance.GPull

/-- The distribution identity resulting from the two Markov decompositions. -/
theorem pullback_realization_identity
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (Q : ℝ) (h : DistOn V) (h₀ w g FV FU : DistC)
    (c : C(ℂ, ℝ)) (f : C(V, ℝ)) (k : C(U, ℝ))
    (HV HU : ℂ → ℝ)
    (hh : h = restrictTo V h₀ +
      Distribution.ofFun V (Function.extend Subtype.val f 0) volume ⊤)
    (hw : h₀ = w + ofCont c)
    (hVc : Continuous fun x : U => HV (φ x))
    (hUc : Continuous fun x : U => HU x)
    (hVpair : ∀ ψ : TestOn U,
      (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V w) -
        SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ =
        ∫ x, HV (φ x) * ψ x)
    (hUpair : ∀ ψ : TestOn U,
      restrictTo U (g - FU) ψ = ∫ x, HU x * ψ x)
    (hzero : restrictTo U FU =
      SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV))
    (hk : ∀ x : U, k x = HV (φ x) - HU x +
      c (φ x) + f ⟨φ x, hφ.2.mapsTo x.property⟩ +
      Q * Real.log ‖deriv φ x‖) :
    confPullbackField Q hφ h =
      restrictTo U g +
        Distribution.ofFun U (Function.extend Subtype.val k 0) volume ⊤ := by
  ext ψ
  let A : ℂ → ℝ := fun x => HV (φ x)
  let B : ℂ → ℝ := HU
  let C : ℂ → ℝ := fun x => c (φ x)
  let D : ℂ → ℝ := fun x => Function.extend Subtype.val f 0 (φ x)
  let E : ℂ → ℝ := fun x => Q * Real.log ‖deriv φ x‖
  have hAc : ContinuousOn A (U : Set ℂ) :=
    continuousOn_iff_continuous_domRestrict.mpr hVc
  have hBc : ContinuousOn B (U : Set ℂ) :=
    continuousOn_iff_continuous_domRestrict.mpr hUc
  have hCc : ContinuousOn C (U : Set ℂ) :=
    c.continuous.comp_continuousOn hφ.1.continuousOn
  have hDc : ContinuousOn D (U : Set ℂ) :=
    (continuousOn_extZ f).comp hφ.1.continuousOn hφ.2.mapsTo
  have hEc : ContinuousOn E (U : Set ℂ) := continuousOn_logDeriv Q hφ
  have hkc : ContinuousOn (fun x => A x - B x + C x + D x + E x)
      (U : Set ℂ) := (((hAc.sub hBc).add hCc).add hDc).add hEc
  have hkp : Distribution.ofFun U (Function.extend Subtype.val k 0) volume ⊤ ψ =
      (∫ x, (A x - B x + C x + D x + E x) * ψ x) := by
    apply ofFun_extZ_apply_eq k hkc
    intro x hx
    have hφx := hφ.2.mapsTo hx
    have he : Function.extend Subtype.val (f : V → ℝ) 0 (φ x) =
        f ⟨φ x, hφx⟩ := by
      conv_lhs => rw [show φ x = ((⟨φ x, hφx⟩ : V) : ℂ) from rfl]
      rw [Subtype.val_injective.extend_apply]
    simpa only [A, B, C, D, E, he] using (hk ⟨x, hx⟩)
  have hkint : Distribution.ofFun U (Function.extend Subtype.val k 0) volume ⊤ ψ =
      (∫ x, A x * ψ x) - (∫ x, B x * ψ x) +
      (∫ x, C x * ψ x) + (∫ x, D x * ψ x) +
      (∫ x, E x * ψ x) := by
    rw [hkp]
    calc
      (∫ x, (A x - B x + C x + D x + E x) * ψ x) =
          (∫ x, (A x - B x + C x + D x) * ψ x) + ∫ x, E x * ψ x := by
            exact integral_test_add (((hAc.sub hBc).add hCc).add hDc) hEc ψ
      _ = ((∫ x, (A x - B x + C x) * ψ x) + ∫ x, D x * ψ x) +
          ∫ x, E x * ψ x := by
            have hp := integral_test_add ((hAc.sub hBc).add hCc) hDc ψ
            simpa only [Pi.add_apply, Pi.sub_apply] using congrArg
              (fun t : ℝ => t + ∫ x, E x * ψ x) hp
      _ = (((∫ x, (A x - B x) * ψ x) + ∫ x, C x * ψ x) +
          ∫ x, D x * ψ x) + ∫ x, E x * ψ x := by
            have hp := integral_test_add (hAc.sub hBc) hCc ψ
            simpa only [Pi.add_apply, Pi.sub_apply] using congrArg
              (fun t : ℝ => (t + ∫ x, D x * ψ x) + ∫ x, E x * ψ x) hp
      _ = _ := by
        have hp := integral_test_sub hAc hBc ψ
        simpa only [Pi.sub_apply] using congrArg
          (fun t : ℝ => ((t + ∫ x, C x * ψ x) + ∫ x, D x * ψ x) +
            ∫ x, E x * ψ x) hp
  have hwp : (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V w)) ψ =
      (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ +
        ∫ x, A x * ψ x := by
    have hp := hVpair ψ
    rw [sub_apply] at hp
    calc
      _ = ((SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V w)) ψ -
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ) +
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ := by ring
      _ = (∫ x, A x * ψ x) +
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ := by
            rw [hp]
      _ = _ := by ring
  have hgp : restrictTo U g ψ =
      (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ +
        ∫ x, B x * ψ x := by
    have hp := hUpair ψ
    have hs : restrictTo U (g - FU) ψ =
        restrictTo U g ψ - restrictTo U FU ψ := rfl
    rw [hs, hzero, SupercriticalConformalCovariance.ZBConformal.distPullback_apply] at hp
    change (restrictTo U g) ψ -
      (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ =
      ∫ x, B x * ψ x at hp
    calc
      _ = (restrictTo U g ψ -
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ) +
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ := by ring
      _ = (∫ x, B x * ψ x) +
          (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V FV)) ψ := by
            rw [hp]
      _ = _ := by ring
  have hhp : (SupercriticalConformalCovariance.ZBConformal.distPullback hφ h) ψ =
      (SupercriticalConformalCovariance.ZBConformal.distPullback hφ (restrictTo V w)) ψ +
      (∫ x, C x * ψ x) + (∫ x, D x * ψ x) := by
    rw [hh, hw]
    simp only [SupercriticalConformalCovariance.ZBConformal.distPullback_apply, add_apply]
    rw [show (restrictTo V (w + ofCont c))
      (confPushTest hφ ψ) = (restrictTo V w) (confPushTest hφ ψ) +
      (restrictTo V (ofCont c)) (confPushTest hφ ψ) from rfl]
    rw [ofCont_restrict_pair, ofFun_extZ_pair]
    rw [SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hφ ψ c,
      SupercriticalConformalCovariance.ZBConformal.integral_mul_confPushTest hφ ψ
        (Function.extend Subtype.val f 0)]
  have hlog : Distribution.ofFun U E volume ⊤ ψ = ∫ x, E x * ψ x :=
    ofFun_continuousOn_apply hEc ψ
  change (SupercriticalConformalCovariance.ZBConformal.distPullback hφ h) ψ +
      Distribution.ofFun U E volume ⊤ ψ =
      restrictTo U g ψ +
        Distribution.ofFun U (Function.extend Subtype.val k 0) volume ⊤ ψ
  rw [hhp, hwp, hgp, hkint, hlog]
  ring


end SupercriticalConformalCovariance.GPull

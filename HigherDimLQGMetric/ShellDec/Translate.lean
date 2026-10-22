import HigherDimLQGMetric.ShellDec.CountableHolder
import HigherDimLQGMetric.LGF.Invariance

/-!
# Translation of the mean-zero shell sigma algebra
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

private theorem shellTranslateSupport {d : ℕ} (z c : Rd d) (a b : ℝ)
    (φ : TestRd0 d)
    (hs : tsupport (φ.1 : Rd d → ℝ) ⊆ ann c a b) :
    tsupport ((testAffinePull0 1 z φ).1 : Rd d → ℝ) ⊆
      ann (c + z) a b := by
  rw [testAffinePull0_val, tsupport_testAffinePull one_ne_zero]
  rintro x ⟨y, hy, rfl⟩
  have h := hs hy
  change a < ‖y - c‖ ∧ ‖y - c‖ < b at h
  change a < ‖affinePt 1 z y - (c + z)‖ ∧
    ‖affinePt 1 z y - (c + z)‖ < b
  have heq : affinePt 1 z y - (c + z) = y - c := by simp [affinePt_apply]
  simpa only [heq] using h

private theorem fieldSigma0_affineComp_one_le {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (h : Ω → DistRd d) (z c : Rd d) (a b : ℝ) :
    fieldSigma0 (fun ω => affineComp 1 z (h ω)) (ann c a b) ≤
      fieldSigma0 h (ann (c + z) a b) := by
  have hsrc : Measurable[fieldSigma0 h (ann (c + z) a b)]
      (fun ω (ψ : {ψ : TestRd0 d //
        tsupport (ψ.1 : Rd d → ℝ) ⊆ ann (c + z) a b}) =>
        h ω ψ.1.1) := Measurable.of_comap_le le_rfl
  have hm : Measurable[fieldSigma0 h (ann (c + z) a b)]
      (fun ω (φ : {φ : TestRd0 d //
        tsupport (φ.1 : Rd d → ℝ) ⊆ ann c a b}) =>
        affineComp 1 z (h ω) φ.1.1) := by
    refine (@measurable_pi_iff _ _ _
      (fieldSigma0 h (ann (c + z) a b)) _ _).2 fun φ => ?_
    let ψ : {ψ : TestRd0 d //
        tsupport (ψ.1 : Rd d → ℝ) ⊆ ann (c + z) a b} :=
      ⟨testAffinePull0 1 z φ.1, shellTranslateSupport z c a b φ.1 φ.2⟩
    have heq : (fun ω => affineComp 1 z (h ω) φ.1.1) =
        fun ω => h ω ψ.1.1 := by
      funext ω
      exact affineComp_one_apply z (h ω) φ.1.1
    rw [heq]
    exact (measurable_pi_apply ψ).comp hsrc
  exact hm.comap_le

/-- Translating the field by `z` turns shells about `z` into shells about zero,
with equality of the generated mean-zero sigma algebras. -/
theorem fieldSigma0_ann_translate {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (h : Ω → DistRd d)
    (z : Rd d) (a b : ℝ) :
    fieldSigma0 (fun ω => affineComp 1 z (h ω)) (ann 0 a b) =
      fieldSigma0 h (ann z a b) := by
  apply le_antisymm
  · simpa using fieldSigma0_affineComp_one_le h z 0 a b
  · have h := fieldSigma0_affineComp_one_le
      (fun ω => affineComp 1 z (h ω)) (-z) z a b
    simpa [affineComp_affineComp, add_comm, add_left_comm, add_assoc]
      using h

end HigherDimLQGMetric

import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Pin
import HigherDimLQGMetric.ShellDec.Functional

/-!
# Locality of recentred mean-zero events (packet P4)

The mean-zero sigma algebra ignores the random constant subtracted by
`recentre`. Scaling pulls every generating test function to its affine image.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory Set
open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Pulling back a mean-zero field sigma algebra by recentering only needs
the affine image of the test-function domain. -/
theorem p4_fieldSigma0_recentre_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (h : Ω → DistRd d) {r : ℝ} (hr : 0 < r) (s : ℝ) (z : Rd d)
    {U V : Set (Rd d)} (hUV : affinePt r z '' U ⊆ V) :
    fieldSigma0 (fun ω => recentre s r z (h ω)) U ≤ fieldSigma0 h V := by
  have hsrc : Measurable[fieldSigma0 h V]
      (fun ω (ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V}) =>
        h ω ψ.1.1) := Measurable.of_comap_le le_rfl
  have hm : Measurable[fieldSigma0 h V]
      (fun ω (φ : {φ : TestRd0 d // tsupport (φ.1 : Rd d → ℝ) ⊆ U}) =>
        recentre s r z (h ω) φ.1.1) := by
    refine (@measurable_pi_iff _ _ _ (fieldSigma0 h V) _ _).2 fun φ => ?_
    let ψ : {ψ : TestRd0 d // tsupport (ψ.1 : Rd d → ℝ) ⊆ V} :=
      ⟨testAffinePull0 r z φ.1, by
        rw [testAffinePull0_val, tsupport_testAffinePull hr.ne']
        exact (Set.image_mono φ.2).trans hUV⟩
    have heq : (fun ω => recentre s r z (h ω) φ.1.1) =
        fun ω => (r ^ d)⁻¹ * h ω ψ.1.1 := by
      funext ω
      simp only [recentre, addConst_apply_testRd0, affineComp_apply]
      rfl
    rw [heq]
    exact measurable_const.mul ((measurable_pi_apply ψ).comp hsrc)
  exact hm.comap_le

/-- Pull back an almost-sure local event under the law of the recentred field. -/
theorem p4_aeEventIn_recentre {d : ℕ} (hd : 2 ≤ d)
    {s s₀ r : ℝ} (hs : 0 < s) (hs₀ : 0 < s₀) (hr : 0 < r)
    (z : Rd d) {U V : Set (Rd d)} (hUV : affinePt r z '' U ⊆ V)
    {E : Set (DistRd d)} (hE : AEEventIn (pinLaw d s) (fieldSigma0 id U) E) :
    AEEventIn (pinLaw d s₀) (fieldSigma0 id V)
      {g | recentre s r z g ∈ E} := by
  obtain ⟨G, hG, hEG⟩ := hE
  have hle := p4_fieldSigma0_recentre_le (h := id) hr s z hUV
  refine ⟨{g | recentre s r z g ∈ G}, ?_, ?_⟩
  · apply hle
    show MeasurableSet[fieldSigma0 (fun g => recentre s r z (id g)) U]
      {g | recentre s r z g ∈ G}
    have heq : fieldSigma0 (fun g => recentre s r z (id g)) U =
        MeasurableSpace.comap (recentre s r z) (fieldSigma0 id U) := by
      simp only [fieldSigma0, MeasurableSpace.comap_comp]
      rfl
    rw [heq]
    exact MeasurableSpace.measurableSet_comap.mpr ⟨G, hG, rfl⟩
  · exact ae_recentre_of_ae hd hs hs₀ hr z hEG

end HigherDimLQGContinuity

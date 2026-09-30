import QuantumZipper.Proofs.Thm18.G1SideScaleDet
import QuantumZipper.Proofs.Thm18.G1RegRepScale
import QuantumZipper.Proofs.Thm18.G1Side3Cls
import QuantumZipper.Proofs.Thm18.G1ProfileConvBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-SIDE3 (6): the pulled-back canonical field at one interior circle

For the unscaled wedge field `w`, a scale `s > 0` and a map `ψ` continuous near a folded circle
`fc(z, r)` inside `ℍ` and mapping it into `ℍ`: if the smoothed free-field pairings on the pushed
circle `(sψ)_* fc(z, r)` converge as the smoothing radius tends to `0`, then the raw value of the
pulled-back canonical field `coordChange (rescale w Q s) ψ Q` at `fc(z, r)` is the raw value of
`coordChange w (s ψ) Q` there (`raw_rescale_eq`): scale consistency
(`Thm18Asm.G1.scaleConsistentAt_of_continuum`) from the continuum limit of the wedge field
(`G1Side.wedge_continuum_of_free`), then `Thm18Asm.G1Meas.coordChange_rescale_apply`.
Duplantier–Sheffield 2011 (1.3)/(5.1) for dilations; own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace G1Side

theorem closedBall_subset_H {z : ℂ} {r : ℝ} (hr : r < z.im) : closedBall z r ⊆ H := by
  intro u hu
  show 0 < u.im
  have h := Complex.abs_im_le_norm (u - z)
  rw [← dist_eq_norm] at h
  have := mem_closedBall.1 hu
  rw [Complex.sub_im, abs_le] at h
  linarith [h.1]

theorem ae_fc_mem_closedBall {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 ≤ r) :
    ∀ᵐ u ∂foldedCircle z r, u ∈ closedBall z r := by
  filter_upwards [Thm18Asm.G1RC.foldedCircle_ae_dist_le' hz hr] with u hu
  exact mem_closedBall.2 hu

/-- **Raw value of the pulled-back canonical field at an interior circle.** -/
theorem raw_rescale_eq {Q : ℝ} {x0 : FieldSample} {F : ℂ × ℝ → ℝ}
    (hgood : WedgeTK.GoodRad x0 F)
    (hraw : ∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
      x0 (foldedCircle (dyadicRoundC n z) (radius k)) = F (dyadicRoundC n z, radius k))
    {A : ℝ → ℝ} (hA : Continuous A) (hW : IsRegularSample (wedgeField (lateralPart x0) A Q))
    {ψ : ℂ → ℂ} (hψm : Measurable ψ) {z : ℂ} {r : ℝ} (hr0 : 0 < r) (hrz : r < z.im)
    (hψc : ContinuousOn ψ (closedBall z r)) (hψH : MapsTo ψ (closedBall z r) H)
    (hd : ∀ᵐ u ∂foldedCircle z r, deriv ψ u ≠ 0)
    (hi : Integrable (fun u => Real.log ‖deriv ψ u‖) (foldedCircle z r)) {s : ℝ} (hs : 0 < s)
    (hY : ∃ Y : ℝ, Tendsto (fun σ => ∫ v, F (v, σ)
      ∂((foldedCircle z r).map fun u => (s : ℂ) * ψ u)) (𝓝[>] 0) (𝓝 Y)) :
    coordChange (rescale (wedgeField (lateralPart x0) A Q) Q s) ψ Q (foldedCircle z r) =
      coordChange (wedgeField (lateralPart x0) A Q) (fun u => (s : ℂ) * ψ u) Q
        (foldedCircle z r) := by
  set w := wedgeField (lateralPart x0) A Q with hwdef
  have hzH : z ∈ Hbar := by
    show (0 : ℝ) ≤ z.im; linarith
  have hmS : Measurable fun u : ℂ => (s : ℂ) * u := measurable_const_mul _
  have hsψ : Measurable fun u => (s : ℂ) * ψ u := hmS.comp hψm
  have hmap : ((foldedCircle z r).map ψ).map (fun u => (s : ℂ) * u) =
      (foldedCircle z r).map fun u => (s : ℂ) * ψ u := by
    rw [Measure.map_map hmS hψm]; rfl
  have hball := ae_fc_mem_closedBall hzH hr0.le
  have hHbm : MeasurableSet Hbar :=
    (isClosed_le continuous_const Complex.continuous_im).measurableSet
  have hν : ∀ᵐ u ∂((foldedCircle z r).map ψ), u ∈ Hbar := by
    refine (ae_map_iff hψm.aemeasurable hHbm).2 ?_
    filter_upwards [hball] with u hu
    exact show (0 : ℝ) ≤ (ψ u).im from le_of_lt (hψH hu)
  -- the compact carrier of the pushed circle
  set Kc := (fun u => (s : ℂ) * ψ u) '' closedBall z r with hKcdef
  have hKc : IsCompact Kc :=
    (isCompact_closedBall z r).image_of_continuousOn (continuousOn_const.mul hψc)
  have hKcH : Kc ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    show 0 < ((s : ℂ) * ψ u).im
    rw [Complex.im_ofReal_mul]
    exact mul_pos hs (hψH hu)
  have hKcHb : Kc ⊆ Hbar := fun v hv => show (0 : ℝ) ≤ v.im from le_of_lt (hKcH hv)
  haveI : IsProbabilityMeasure ((foldedCircle z r).map fun u => (s : ℂ) * ψ u) :=
    (Measure.isProbabilityMeasure_map_iff hsψ.aemeasurable).2 inferInstance
  have hμK : ∀ᵐ v ∂((foldedCircle z r).map fun u => (s : ℂ) * ψ u), v ∈ Kc := by
    refine (ae_map_iff hsψ.aemeasurable hKc.isClosed.measurableSet).2 ?_
    filter_upwards [hball] with u hu
    exact mem_image_of_mem _ hu
  obtain ⟨c₀, hc₀, hsep⟩ : ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ v ∈ Kc, c₀ ≤ ‖v‖ := by
    rcases Kc.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨v₀, hv₀, hmin⟩ := hKc.exists_isMinOn hne continuous_norm.continuousOn
      refine ⟨‖v₀‖, norm_pos_iff.2 fun h => ?_, fun v hv => hmin hv⟩
      have h1 : (0 : ℝ) < v₀.im := hKcH hv₀
      rw [h] at h1
      simp at h1
  obtain ⟨Y, hYt⟩ := hY
  obtain ⟨hint, L, hL⟩ := wedge_continuum_of_free hgood hraw hA Q hW hKc hKcHb hμK hc₀ hsep hYt
  have hsc : Thm18Asm.G1.ScaleConsistentAt w Q s ((foldedCircle z r).map ψ) :=
    Thm18Asm.G1.scaleConsistentAt_of_continuum hW Q hs hν (by rw [hmap]; exact hint)
      (L := L) (by rw [hmap]; exact hL)
  exact Thm18Asm.G1Meas.coordChange_rescale_apply w hψm Q hs _ hsc hd hi

end G1Side
end QuantumZipper

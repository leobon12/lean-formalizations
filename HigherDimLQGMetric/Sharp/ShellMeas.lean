import HigherDimLQGMetric.Sharp.CountableShell
import HigherDimLQGMetric.Events.Locality

/-!
# Shell observables as field-measurable random variables modulo constants

For a whole-space LGF, both normalized shell quantities have versions
measurable for the mean-zero field pairings on a slightly larger annulus.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

theorem fieldSigma0_le_ambient
    {Ω : Type} [MeasurableSpace Ω] {h : Ω → DistRd d}
    (hh : Measurable h) (J : Set (Rd d)) :
    fieldSigma0 h J ≤ (inferInstance : MeasurableSpace Ω) := by
  unfold fieldSigma0
  apply Measurable.comap_le
  refine measurable_pi_iff.2 fun φ => ?_
  exact (measurable_distOn_apply φ.1.1).comp hh

private theorem sphere_outer_ann {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z r ⊆ ann z (r / 4) (4 * r) := by
  intro u hu
  have h := mem_sphere_iff_norm.1 hu
  show r / 4 < ‖u - z‖ ∧ ‖u - z‖ < 4 * r
  rw [h]
  constructor <;> linarith

private theorem sphere_inner_ann {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z r ⊆ ann z (r / 2) (2 * r) := by
  intro u hu
  have h := mem_sphere_iff_norm.1 hu
  show r / 2 < ‖u - z‖ ∧ ‖u - z‖ < 2 * r
  rw [h]
  constructor <;> linarith

private theorem halfsphere_outer_ann {r : ℝ} (hr : 0 < r) (z : Rd d) :
    sphere z (r / 2) ⊆ ann z (r / 4) (4 * r) := by
  intro u hu
  have h := mem_sphere_iff_norm.1 hu
  show r / 4 < ‖u - z‖ ∧ ‖u - z‖ < 4 * r
  rw [h]
  constructor <;> linarith

private theorem inner_ann_subset_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    ann z (r / 2) (2 * r) ⊆ ann z (r / 4) (4 * r) := by
  intro u hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

private theorem closed_half_ann_subset_outer {r : ℝ} (hr : 0 < r) (z : Rd d) :
    annCl z (r / 2) r ⊆ ann z (r / 4) (4 * r) := by
  intro u hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

theorem IsWeakExpMetric.exists_shellVersions
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ : ℝ} {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {r : ℝ} (hr : 0 < r) :
    ∃ Fdiam Facross : Ω → ℝ≥0∞,
      Measurable[fieldSigma0 h (ann z (r / 4) (4 * r))] Fdiam ∧
      Measurable[fieldSigma0 h (ann z (r / 4) (4 * r))] Facross ∧
      ∀ᵐ ω ∂P,
        Fdiam ω = ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) *
          sphereDiam (D (h ω)) z r ∧
        Facross ω = ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) *
          acrossDist (D (h ω)) z (r / 2) r := by
  have : NeZero d := ⟨by omega⟩
  let J := shellOpens z (r / 4) (4 * r)
  let V := shellOpens z (r / 2) (2 * r)
  obtain ⟨q, hqS, hqDense⟩ := exists_denseSeq_rd
    (S := sphere z r) (NormedSpace.sphere_nonempty.2 hr.le)
  obtain ⟨t, htS, htDense⟩ := exists_denseSeq_rd
    (S := sphere z (r / 2)) (NormedSpace.sphere_nonempty.2 (half_pos hr).le)
  obtain ⟨F₁, hF₁m, hF₁ae⟩ := hD.exists_measurable_expNormalized_internal hd hh
    V J (inner_ann_subset_outer hr z) z hr (sphere_outer_ann hr z)
  obtain ⟨F₂, hF₂m, hF₂ae⟩ := hD.exists_measurable_expNormalized_internal hd hh
    J J le_rfl z hr (sphere_outer_ann hr z)
  let Fdiam : Ω → ℝ≥0∞ := fun ω => ⨆ p : ℕ × ℕ, F₁ ω (q p.1) (q p.2)
  let Facross : Ω → ℝ≥0∞ := fun ω => ⨅ p : ℕ × ℕ, F₂ ω (t p.1) (q p.2)
  have hFdm : Measurable[fieldSigma0 h (ann z (r / 4) (4 * r))] Fdiam := by
    exact Measurable.iSup fun p =>
      (measurable_pi_apply (q p.2)).comp
        ((measurable_pi_apply (q p.1)).comp hF₁m)
  have hFam : Measurable[fieldSigma0 h (ann z (r / 4) (4 * r))] Facross := by
    exact Measurable.iInf fun p =>
      (measurable_pi_apply (q p.2)).comp
        ((measurable_pi_apply (t p.1)).comp hF₂m)
  refine ⟨Fdiam, Facross, hFdm, hFam, ?_⟩
  filter_upwards [hF₁ae, hF₂ae, hD.length P h hh.isLGFPlusCont] with ω h₁ h₂ hLen
  constructor
  · have hqV : ∀ n, q n ∈ V := fun n => sphere_inner_ann hr z (hqS n)
    have hdense := sphereDiam_eq_iSup_dense (D (h ω)) hLen V.isOpen
      (sphere_inner_ann hr z) hqS hqDense
    change Fdiam ω = _
    simp only [Fdiam, h₁ _ (hqV _) _ (hqV _), ← ENNReal.mul_iSup]
    exact congrArg (fun x => ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z)) * x)
      hdense.symm
  · have htJ : ∀ n, t n ∈ J := fun n => halfsphere_outer_ann hr z (htS n)
    have hqJ : ∀ n, q n ∈ J := fun n => sphere_outer_ann hr z (hqS n)
    have hdense := setDistIn_eq_iInf_dense (D (h ω)) hLen J.isOpen
      (halfsphere_outer_ann hr z) (sphere_outer_ann hr z) htS hqS htDense hqDense
    have hacross := acrossDist_eq_setDistIn (D (h ω)) hLen J.isOpen
      (by linarith : r / 2 < r) (closed_half_ann_subset_outer hr z)
    change Facross ω = _
    simp only [Facross, h₂ _ (htJ _) _ (hqJ _)]
    rw [hacross, hdense,
      ENNReal.mul_iInf_of_ne
        (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top]

/-- The comparison shell event is measurable modulo constants. -/
theorem shellCompare_aeEventIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistRd d} {ξ : ℝ}
    {D₁ D₂ : DistRd d → ContMetric d} {c₁ c₂ : ℝ → ℝ}
    (hD₁ : IsWeakExpMetric d ξ D₁ c₁) (hD₂ : IsWeakExpMetric d ξ D₂ c₂)
    (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) (z : Rd d)
    {r : ℝ} (hr : 0 < r) (C : ℝ) :
    AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r)))
      {ω | sphereDiam (D₂ (h ω)) z r ≤
        ENNReal.ofReal C * acrossDist (D₁ (h ω)) z (r / 2) r} := by
  obtain ⟨_, A, _, hAm, hAae⟩ := hD₁.exists_shellVersions hd hh z hr
  obtain ⟨B, _, hBm, _, hBae⟩ := hD₂.exists_shellVersions hd hh z hr
  refine ⟨{ω | B ω ≤ ENNReal.ofReal C * A ω},
    measurableSet_le hBm (measurable_const.mul hAm), ?_⟩
  filter_upwards [hAae, hBae] with ω hA hB
  apply propext
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z))
  have hq0 : q ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  rw [hB.1, hA.2]
  change _ ↔ q * sphereDiam (D₂ (h ω)) z r ≤
    ENNReal.ofReal C * (q * acrossDist (D₁ (h ω)) z (r / 2) r)
  rw [mul_left_comm (ENNReal.ofReal C) q,
    ENNReal.mul_le_mul_iff_right hq0 hqtop]

/-- The recentered shell restriction is measurable from mean-zero field pairings,
so a `shellSigma` event is an `AEEventIn` event for `fieldSigma0`. -/
theorem shellSigma_event_aeEventIn
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistRd d} (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    (z : Rd d) {r : ℝ} (hr : 0 < r) (E : Set Ω)
    (hE : MeasurableSet[shellSigma h z r (1 / 4) 4] E) :
    AEEventIn P (fieldSigma0 h (ann z (r / 4) (4 * r))) E := by
  let J := shellOpens z (r / 4) (4 * r)
  have hSJ : sphere z r ⊆ J := sphere_outer_ann hr z
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_recentered_restrict hd hh
    J J le_rfl z hr hSJ
  have hJ : shellOpens z ((1 / 4) * r) (4 * r) = J := by
    ext u
    change ((1 / 4) * r < ‖u - z‖ ∧ ‖u - z‖ < 4 * r) ↔
      (r / 4 < ‖u - z‖ ∧ ‖u - z‖ < 4 * r)
    constructor <;> intro hu <;> constructor <;> nlinarith [hu.1, hu.2]
  have hSigma : shellSigma h z r (1 / 4) 4 =
      MeasurableSpace.comap
        (fun ω => restrictTo J (addConst (h ω) (-sphereAvg (h ω) r z))) inferInstance := by
    change MeasurableSpace.comap
      (fun ω => restrictTo (shellOpens z ((1 / 4) * r) (4 * r))
        (addConst (h ω) (-sphereAvg (h ω) r z))) inferInstance = _
    rw [hJ]
  rw [hSigma] at hE
  obtain ⟨B, hB, hEeq⟩ := MeasurableSpace.measurableSet_comap.mp hE
  refine ⟨F ⁻¹' B, hFm hB, ?_⟩
  filter_upwards [hFae] with ω hω
  have hmem : ω ∈ E ↔
      restrictTo J (addConst (h ω) (-sphereAvg (h ω) r z)) ∈ B := by
    rw [← hEeq]
    rfl
  apply propext
  exact hmem.trans (by simp only [mem_preimage, hω])

end HigherDimLQGMetric

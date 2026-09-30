import QuantumZipper.Proofs.Thm18.G3Za9
import QuantumZipper.Proofs.Thm18.G3Za4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-A, item (b), layer 4: the zoom of the Palm field through a G0 map

`ae_agreeNear_zoom_palm`: let `V` be a free field, `x ∈ ℝ`, `f₀ = γ(−log |· − x|) + h₀` near `x`
(`h₀` continuous, `f₀` measurable), `S` any measure, `ψ` an admissible map of G0. There is
`r > 0` such that almost surely, for every level `L`,

  `zoomFieldVia γ L (normAt S (ofFun f₀ + V)) x ψ`   agrees near `0` (radius `r`) with
  `addConst (coordChange (ofFun (f₀(· + x)) + rawTranslate V x) ψ Q) (L/γ − (ofFun f₀ + V)(S))`.

Together with `G3Za.exists_g0Setup_palm` (applied to the free field `rawTranslate V x`, the
profile `f₀(· + x)` and the measure `S` translated by `−x`) this identifies the zoom of the Palm
field of `G3WedgePalmIdStmt` with a D3⁺ model with `α = γ`, the Palm normalization included
(`(ofFun f₀ + V)(S) = ∫ f₀ dS + V(S)`, the first term deterministic). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology ComplexConjugate
open scoped ENNReal NNReal

namespace QuantumZipper
namespace G3Za

open G3Cv

variable {Φ : ℂ → ℂ} {r₀ ρ r₁ m M : ℝ}

/-- Support, atoms and log-integrability of a pulled-back circle. -/
theorem pullCircle_props (hD : PullData Φ 0 r₀ ρ r₁ m M) (hΦ0 : Φ 0 = 0) {c : ℂ} {r : ℝ}
    (hr : 0 < r) (hcr : ‖c‖ + r ≤ ρ) :
    IsProbabilityMeasure (pullCircle Φ c r) ∧
    (∀ᵐ w ∂pullCircle Φ c r, w ∈ closedBall ((0 : ℝ) : ℂ) (M * ρ) ∩ Hbar) ∧
    (∀ᵐ w ∂pullCircle Φ c r, w ≠ ((0 : ℝ) : ℂ)) ∧
    Integrable (fun w : ℂ => Real.log ‖w - ((0 : ℝ) : ℂ)‖) (pullCircle Φ c r) := by
  have hcr' : ‖c - ((0 : ℝ) : ℂ)‖ + r ≤ ρ := by simpa using hcr
  have hP : IsProbabilityMeasure (pullCircle Φ c r) :=
    (Measure.isProbabilityMeasure_map_iff hD.conf.meas.aemeasurable).2 inferInstance
  have hnull := foldedCircle_compl_null (b := 0) hr hcr'
  have hae := ae_mem_of_compl_null_g3cv hnull
  have h00 : ((0 : ℝ) : ℂ) ∈ closedBall ((0 : ℝ) : ℂ) ρ := mem_closedBall_self hD.hρ.le
  have hbl : ∀ u ∈ closedBall ((0 : ℝ) : ℂ) ρ, m * ‖u‖ ≤ ‖Φ u‖ ∧ ‖Φ u‖ ≤ M * ‖u‖ := by
    intro u hu
    have hb := hD.bl.2.2 u hu _ h00
    simpa [hΦ0] using hb
  refine ⟨hP, ?_, ?_, ?_⟩
  · refine (ae_map_iff (p := fun w => w ∈ closedBall ((0 : ℝ) : ℂ) (M * ρ) ∩ Hbar)
      hD.conf.meas.aemeasurable
      (by exact (isClosed_closedBall.inter isClosed_Hbar).measurableSet)).2 ?_
    filter_upwards [hae] with u hu
    refine ⟨?_, hD.up u hu⟩
    have h1 := (hbl u hu.1).2
    have h2 : ‖u‖ ≤ ρ := by simpa using hu.1
    rw [mem_closedBall, Complex.ofReal_zero, dist_zero_right]
    nlinarith [hD.bl.2.1]
  · refine (ae_map_iff (p := fun w => w ≠ ((0 : ℝ) : ℂ)) hD.conf.meas.aemeasurable
      (by exact (measurableSet_singleton _).compl)).2 ?_
    filter_upwards [hae, F1.ae_ne_zero_fc c hr] with u hu hu0 h0
    have h1 := (hbl u hu.1).1
    rw [Complex.ofReal_zero] at h0
    rw [h0, norm_zero] at h1
    have : 0 < m * ‖u‖ := mul_pos hD.bl.1 (norm_pos_iff.2 hu0)
    linarith
  · rw [pullCircle, integrable_map_measure (measurable_log_norm_sub 0).aestronglyMeasurable
      hD.conf.meas.aemeasurable]
    have := integrable_log_norm_comp_fc hD hΦ0 hr hcr
    refine this.congr (ae_of_all _ fun u => ?_)
    simp

/-- **The zoom of the Palm field through a G0 map** (a.s., near `0`, all levels). -/
theorem ae_agreeNear_zoom_palm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → FieldSample} (hV : IsFreeGFFModConstH V P)
    {r₀' : ℝ} {ψ : ℂ → ℂ} (hr₀ : 0 < r₀') (hψ : Thm18Asm.IsG0Map r₀' ψ) (γ : ℝ)
    {x ρf : ℝ} (hρf : 0 < ρf) {f₀ h₀ : ℂ → ℝ}
    (hf : ∀ u ∈ closedBall (x : ℂ) ρf ∩ Hbar, f₀ u = γ * -Real.log ‖u - x‖ + h₀ u)
    (hh : Continuous h₀) (hfm : Measurable f₀) (S : Measure ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ᵐ ω ∂P, ∀ L : ℝ,
      D3Plus.AgreeNear (Thm18Asm.zoomFieldVia γ L (PalmNorm.normAt S (ofFun f₀ + V ω)) x ψ)
        (addConst (coordChange (ofFun (fun u => f₀ (u + x)) + rawTranslate (V ω) x) ψ (Qc γ))
          (L / γ - (ofFun f₀ + V ω) S)) r := by
  obtain ⟨Ψ, r₀, ρ, r₁, m, M, hr₁0, hD, heq⟩ := pullData_of_isG0Map hr₀ hψ
  have hr₀0 : 0 < r₀ := hD.conf.pos
  have hΨ0 : Ψ 0 = 0 := by
    rw [heq (mem_ball_self hr₀0)]; exact hψ.2.2.2.1
  have hM := hD.bl.2.1
  set ρ₁ := ρf / 2 with hρ₁
  set ρ' := min ρ (ρ₁ / (2 * M)) with hρ'
  have hρ'0 : 0 < ρ' := lt_min hD.hρ (by positivity)
  have hMρ' : M * ρ' < ρ₁ := by
    have h1 : ρ' ≤ ρ₁ / (2 * M) := min_le_right _ _
    have h2 : M * ρ' ≤ M * (ρ₁ / (2 * M)) := mul_le_mul_of_nonneg_left h1 hM.le
    have h3 : M * (ρ₁ / (2 * M)) = ρ₁ / 2 := by field_simp
    have : 0 < ρ₁ := by positivity
    linarith
  have hD' : PullData Ψ 0 r₀ ρ' (ρ' / 2) m M :=
    G3Za.PullData.shrink hD (by positivity) (by linarith) (min_le_left _ _)
  have hρ'r₀ : ρ' < r₀ := hD'.hρr
  set f₁ : ℂ → ℝ := fun u => f₀ (u + x) with hf₁
  have hf₁m : Measurable f₁ := hfm.comp (measurable_id.add measurable_const)
  have hf₁e : ∀ u ∈ closedBall (0 : ℂ) ρf ∩ Hbar,
      f₁ u = γ * -Real.log ‖u‖ + (fun u => h₀ (u + x)) u := by
    intro u hu
    have hmem : u + x ∈ closedBall (x : ℂ) ρf ∩ Hbar := by
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        simpa using hu.1
      · have := hu.2; simp only [Hbar, mem_setOf_eq, Complex.add_im, Complex.ofReal_im,
          add_zero] at this ⊢; exact this
    simp only [hf₁, hf _ hmem, add_sub_cancel_right]
  have hh₁ : Continuous fun u => h₀ (u + x) := hh.comp (continuous_id.add continuous_const)
  have hV₁ := isFree_rawTranslate hV x
  set r := ρ' / 2 with hr
  refine ⟨r, by positivity, ?_⟩
  have hc : ∀ n : ℕ, (Set.range (dyadicRoundC n)).Countable := fun n => by
    have hsub : Set.range (dyadicRoundC n) ⊆
        Set.range (fun p : ℤ × ℤ =>
          (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
      rintro _ ⟨z, rfl⟩
      exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
    exact (Set.countable_range _).mono hsub
  have hreg : ∀ᵐ ω ∂P, RegCont.RegAvgGood (rawTranslate (V ω) x) :=
    ae_all_iff.2 fun k => FrostmanReg.ae_circleAvg_tendsto_frostman hV₁ k
  have hall : ∀ᵐ ω ∂P, ∀ n k, ∀ d ∈ Set.range (dyadicRoundC n), ‖d‖ + radius k < r →
      Tendsto (fun j => ∫ w, avgReg (rawTranslate (V ω) x) j w ∂pullCircle Ψ d (radius k))
        atTop (𝓝 (rawTranslate (V ω) x (pullCircle Ψ d (radius k)))) := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro k
    rw [ae_ball_iff (hc n)]
    intro d _
    by_cases hd : ‖d‖ + radius k < r
    · exact (ae_tendsto_avgReg_pullCircle hV₁ hD' (radius_pos k)
        (by simp; linarith)).mono fun ω h _ => h
    · exact ae_of_all _ fun ω h => absurd h hd
  filter_upwards [hreg, hall, ae_agreeNear_translate_palm hV hf hh hfm
    (by linarith : ρ₁ < ρf) S] with ω hreg hω hag L n k z hz
  set d := dyadicRoundC n z
  have hk0 := radius_pos k
  have hdk : ‖d‖ + radius k ≤ ρ' := by linarith
  obtain ⟨hP, hν, hνp, hlog⟩ := pullCircle_props hD' hΨ0 hk0 hdk
  have hA := hω n k d ⟨z, rfl⟩ hz
  set c := -((ofFun f₀ + V ω) S) with hcdef
  have hball : ∀ᵐ u ∂foldedCircle d (radius k), u ∈ ball (0 : ℂ) r₀ := by
    have hnull := foldedCircle_compl_null (b := 0) hk0 (by simpa using hdk)
    exact (ae_mem_of_compl_null_g3cv hnull).mono fun u hu => by
      have h1 : ‖u‖ ≤ ρ' := by simpa using hu.1
      rw [mem_ball, dist_zero_right]; linarith
  have hνc : pullCircle Ψ d (radius k) (closedBall 0 (M * ρ'))ᶜ = 0 := by
    have h : ∀ᵐ w ∂pullCircle Ψ d (radius k), w ∈ closedBall (0 : ℂ) (M * ρ') :=
      hν.mono fun w hw => by simpa using hw.1
    exact h
  have hf₁' : ∀ u ∈ closedBall ((0 : ℝ) : ℂ) ρf ∩ Hbar,
      f₁ u = γ * -Real.log ‖u - ((0 : ℝ) : ℂ)‖ + (fun u => h₀ (u + x)) u := by
    intro u hu; simpa using hf₁e u (by simpa using hu)
  have hMρf : M * ρ' < ρf := by linarith
  have e1 := evalReg_addConst_ofFun_add_logSing hreg hf₁' hh₁ hMρf c hν hνp hlog hA
  have e2 := evalReg_ofFun_add_logSing hreg hf₁' hh₁ hMρf hν hνp hlog hA
  have e3 : evalReg (translate (PalmNorm.normAt S (ofFun f₀ + V ω)) (x : ℂ))
      (pullCircle Ψ d (radius k)) =
      evalReg (addConst (ofFun f₁ + rawTranslate (V ω) x) c) (pullCircle Ψ d (radius k)) :=
    D3Plus.evalReg_congr hag hνc hMρ'
  simp only [Thm18Asm.zoomFieldVia, addConst, measure_univ, ENNReal.toReal_one, mul_one]
  rw [coordChange_congr_ball heq hball, coordChange_congr_ball heq hball]
  simp only [coordChange]
  have hmap : (foldedCircle d (radius k)).map Ψ = pullCircle Ψ d (radius k) := rfl
  rw [hmap, e3, e1, e2]
  ring

end G3Za
end QuantumZipper

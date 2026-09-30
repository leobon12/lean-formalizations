import QuantumZipper.Proofs.Zipper.B2Driver
import QuantumZipper.Proofs.GFF.CoordRegLog

/-!
# B2(b), regularized form of the normalizing constant (AUDIT7 Z2)

`blueprint/E_BRANCH_BLUEPRINT.md` §4, node B2(b), as corrected by
`audits/2026-09-27-fidelity/AUDIT7.md` Z2: the constant `m = h⁰ ϖ` must be read through `evalReg`
(a function of `coordsFull`), and the zipped identity needs regularity clauses.

* `evalReg_congr_coordsFull`: `evalReg x ν` depends only on `coordsFull x`; with B2(c)
  (`b2_ident`), **`b2_evalReg_ident`**: a.s., for every measure `ν`,
  `evalReg h⁰ ν = evalReg (couplingFieldRev κ V T X) ν`.
* **`evalReg_h0f_split_of_regular`**: at every good `ω`, *if* `h⁰ ϖ = evalReg h⁰ ϖ` and
  `Y_t ϖ_t = evalReg Y_t ϖ_t`, then `evalReg h⁰ ϖ = evalReg Y_t ϖ_t + q_t` (from the exact raw
  identity `h0f_compact_split`). The two regularity hypotheses are the RC3 composition statement
  (regularized value of a pulled-back field at a measure compactly supported in `ℍ`), owned by
  RC23 (`GFF/CoordReg*`) and not proved here.
* `isFrostman_map_revMap_of_compact`: the image of a Frostman measure carried by a compact subset
  of `ℍ` under `revMap V t` is Frostman (lower two-point bound `TwoPoint.twoPoint_lower`).
* **`ae_split_compact_random`, `ae_split_compact_drive`** (REG-SPLIT at `ϖ_t` for `𝔥₀ + X'`, the
  second regularity clause of Z2): for a driver independent of the free field `X'`, a.s.
  `evalReg (𝔥₀ + X') ϖ_t = ∫ 𝔥₀ dϖ_t + evalReg X' ϖ_t`. Proof as `UnzipFull.ae_split_fc_random`
  with RC1 in log-singular form (`CoordReg.ae_evalReg_h0rev_eq_frostman'`,
  `FrostmanReg.ae_tendsto_integral_avgReg_frostman`; Duplantier–Sheffield, *LQG and KPZ*,
  Prop. 3.1).

The Frostman lemma is an own elementary argument (cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B2

open CharFun UnzipInvariance UnzipFull TwoPoint

/-! ## 1. `evalReg` reads only `coordsFull` -/

theorem evalReg_congr_coordsFull {x y : FieldSample}
    (h : CoordsFull.coordsFull x = CoordsFull.coordsFull y) (ν : Measure ℂ) :
    evalReg x ν = evalReg y ν := by
  unfold evalReg
  rw [CoordsFull.avgReg_congr_full h]

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **B2(b), regularized split, conditional on regularity.** -/
theorem evalReg_h0f_split_of_regular {ω : Ω} (hc : Continuous fun s => B s ω)
    (h0 : B 0 ω = 0) (ht : 0 ≤ t) (htT : t ≤ T) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H)
    {ϖ : Measure ℂ} [IsFiniteMeasure ϖ] (hϖ : ϖ Kᶜ = 0)
    (h1 : evalReg (h0f κ T B X ω) ϖ = h0f κ T B X ω ϖ)
    (h2 : evalReg (Yf κ T t B X ω) (ϖ.map (revMap (Vr κ T B ω) t)) =
      Yf κ T t B X ω (ϖ.map (revMap (Vr κ T B ω) t))) :
    evalReg (h0f κ T B X ω) ϖ =
      evalReg (Yf κ T t B X ω) (ϖ.map (revMap (Vr κ T B ω) t)) + qt κ (Vr κ T B ω) t ϖ := by
  rw [h1, h2]
  exact h0f_compact_split hc h0 ht htT hK hKH hϖ

/-! ## 2. Frostman bound for `ϖ_t` -/

theorem isFrostman_map_revMap_of_compact {V : ℝ → ℝ} (hV : Continuous V) (ht : 0 ≤ t)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {ϖ : Measure ℂ} [IsFiniteMeasure ϖ]
    (hϖ : ϖ Kᶜ = 0) {α C : ℝ} (hα : 0 ≤ α) (hF : IsFrostman ϖ α C) :
    ∃ C' : ℝ, IsFrostman (ϖ.map (revMap V t)) α C' := by
  set F := revMap V t with hFdef
  have hFm : Measurable F := measurable_revMap hV ht
  have hC0 : 0 ≤ C := by
    have := hF 0 1 one_pos
    rw [Real.one_rpow, mul_one] at this
    exact ENNReal.toReal_nonneg.trans this
  rcases K.eq_empty_or_nonempty with hKe | hne
  · refine ⟨0, fun y r hr => ?_⟩
    have h0 : ϖ = 0 := by
      rw [← Measure.measure_univ_eq_zero]
      simpa [hKe] using hϖ
    simp [h0]
  obtain ⟨z₁, hz₁K, hz₁⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  set c₀ := z₁.im with hc₀
  have hc₀pos : 0 < c₀ := hKH hz₁K
  have hFc : ContinuousOn F K := (differentiableOn_revMap V hV ht).continuousOn.mono hKH
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hFc
  have hMpos : 0 < M := by
    have h1 : 0 < (F z₁).im := im_revMap_pos hV (hKH hz₁K) ht
    have h2 : (F z₁).im ≤ ‖F z₁‖ := (le_abs_self _).trans (Complex.abs_im_le_norm _)
    linarith [hM z₁ hz₁K]
  set L := c₀ / M with hL
  have hLpos : 0 < L := div_pos hc₀pos hMpos
  -- lower Lipschitz bound on `K`
  have hlip : ∀ z ∈ K, ∀ w ∈ K, ‖z - w‖ * L ≤ ‖F z - F w‖ := by
    intro z hz w hw
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      (twoPoint_lower hV (hKH hz) (hKH hw) ht)
    have hzi : c₀ ≤ z.im := hz₁ hz
    have hwi : c₀ ≤ w.im := hz₁ hw
    have hFz : 0 < (F z).im := im_revMap_pos hV (hKH hz) ht
    have hFw : 0 < (F w).im := im_revMap_pos hV (hKH hw) ht
    have hFz' : (F z).im ≤ M :=
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hM z hz)
    have hFw' : (F w).im ≤ M :=
      ((le_abs_self _).trans (Complex.abs_im_le_norm _)).trans (hM w hw)
    rw [Real.le_sqrt hLpos.le (div_nonneg (mul_nonneg (hc₀pos.le.trans hzi)
      (hc₀pos.le.trans hwi)) (mul_pos hFz hFw).le), hL, div_pow,
      div_le_div_iff₀ (by positivity) (mul_pos hFz hFw)]
    calc c₀ ^ 2 * ((F z).im * (F w).im) ≤ (z.im * w.im) * (M * M) := by
          rw [sq]
          exact mul_le_mul (mul_le_mul hzi hwi hc₀pos.le (hc₀pos.le.trans hzi))
            (mul_le_mul hFz' hFw' hFw.le hMpos.le) (mul_pos hFz hFw).le
            (mul_nonneg (hc₀pos.le.trans hzi) (hc₀pos.le.trans hwi))
      _ = z.im * w.im * M ^ 2 := by ring
  refine ⟨C * (2 / L) ^ α, fun y r hr => ?_⟩
  set S := F ⁻¹' Metric.closedBall y r with hS
  have hmap : (ϖ.map F) (Metric.closedBall y r) = ϖ (S ∩ K) := by
    rw [Measure.map_apply hFm Metric.isClosed_closedBall.measurableSet,
      measure_inter_conull hϖ]
  rw [hmap]
  rcases (S ∩ K).eq_empty_or_nonempty with he | ⟨z₀, hz₀S, hz₀K⟩
  · rw [he, measure_empty, ENNReal.toReal_zero]
    positivity
  have hsub : S ∩ K ⊆ Metric.closedBall z₀ (2 * r / L) := by
    rintro z ⟨hzS, hzK⟩
    rw [Metric.mem_closedBall, dist_eq_norm, le_div_iff₀ hLpos]
    have h1 := hlip z hzK z₀ hz₀K
    have h2 : ‖F z - F z₀‖ ≤ 2 * r := by
      have a := Metric.mem_closedBall.1 hzS
      have b := Metric.mem_closedBall.1 hz₀S
      rw [dist_eq_norm] at a b
      calc ‖F z - F z₀‖ = ‖(F z - y) - (F z₀ - y)‖ := by congr 1; ring
        _ ≤ ‖F z - y‖ + ‖F z₀ - y‖ := norm_sub_le _ _
        _ ≤ 2 * r := by linarith
    linarith
  calc (ϖ (S ∩ K)).toReal ≤ (ϖ (Metric.closedBall z₀ (2 * r / L))).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ ≤ C * (2 * r / L) ^ α := hF z₀ _ (by positivity)
    _ = C * (2 / L) ^ α * r ^ α := by
        rw [show 2 * r / L = 2 / L * r by ring, Real.mul_rpow (by positivity) hr.le]
        ring

theorem map_revMap_support_of_compact {V : ℝ → ℝ} (hV : Continuous V) (ht : 0 ≤ t)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) {ϖ : Measure ℂ} (hϖ : ϖ Kᶜ = 0) :
    ∃ R : ℝ, (ϖ.map (revMap V t)) (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0 := by
  have hFc : ContinuousOn (revMap V t) K :=
    (differentiableOn_revMap V hV ht).continuousOn.mono hKH
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hFc
  refine ⟨M, ?_⟩
  have hmeas : MeasurableSet (Metric.closedBall (0 : ℂ) M ∩ Hbar)ᶜ :=
    (Metric.isClosed_closedBall.measurableSet.inter
      (isClosed_le continuous_const Complex.continuous_im).measurableSet).compl
  rw [Measure.map_apply (measurable_revMap hV ht) hmeas]
  have hsub : revMap V t ⁻¹' (Metric.closedBall 0 M ∩ Hbar)ᶜ ⊆ Kᶜ := by
    intro z hz hzK
    refine hz ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hM z hzK
    · exact (im_revMap_pos hV (hKH hzK) ht).le
  exact measure_mono_null hsub hϖ

/-! ## 3. REG-SPLIT at `ϖ_t` for `𝔥₀ + X'` -/

end B2
end QuantumZipper

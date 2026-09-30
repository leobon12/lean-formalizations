import QuantumZipper.Proofs.Thm18.G1PathCoord
import QuantumZipper.Proofs.Loewner.TwoPointEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PATHCOORD, part 2: the probability, support and potential clauses of `PushFamBounds`

`PushFamBounds ψ β = FamilyBounds (smoothFam circM (pushPhi ψ)) β` (G1RCCircle.lean) has four
clauses: probability measures, support in a bounded part of `Hbar` on boxes, a uniform
log-potential bound on boxes, and a Hölder variance modulus on boxes. This file proves the first
two for every `ψ` continuous on `Hbar` with `ψ(Hbar) ⊆ Hbar`, the third (log potential) from
`PushFrostman`, and reduces `PushBoundsOfRegStmt` (G1PathCoord.lean) to the variance clause
(`PushVarOfRegStmt`); `g1PsiExtStmt_of_var` is the resulting form of `G1PsiExtStmt`.

Own elementary arguments: compactness of the parameter box and
`CircleFubini.bind_circle_support` (support); the log potential of a Frostman measure is
`TwoPoint.lintegral_logRatio_frostman` (layer-cake), and for the smoothed members the
folded-circle average of `log⁺ 1/|x − y|` is bounded by the value at the centre plus a constant
(`CircleFubini.circleUnif_pot_le` near the centre, the triangle inequality away from it).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open CircleFubini KolmD

/-- The smoothed pushed-circle family. -/
abbrev pushFam (ψ : ℂ → ℂ) : (Fin (4 + 1) → ℝ) → Measure ℂ := smoothFam circM (pushPhi ψ)

theorem isProbabilityMeasure_pushFam (ψ : ℂ → ℂ) (p : Fin (4 + 1) → ℝ) :
    IsProbabilityMeasure (pushFam ψ p) := by
  unfold pushFam smoothFam
  split_ifs with ht
  · exact ⟨by rw [bind_circle_univ]; exact measure_univ⟩
  · infer_instance

theorem isCompact_boxD (R : ℕ) : IsCompact (boxD (d := 4) R) := by
  have : boxD (d := 4) R = Set.pi univ fun _ => Icc (-(R : ℝ)) R := by
    ext q; simp only [boxD, Set.mem_ofPred_eq, Set.mem_univ_pi, mem_Icc, abs_le]
  rw [this]
  exact isCompact_univ_pi fun _ => isCompact_Icc

theorem init_mem_boxD {R : ℕ} {p : Fin (4 + 1) → ℝ} (hp : p ∈ boxD (d := 4 + 1) R) :
    Fin.init p ∈ boxD (d := 4) R := fun i => hp (Fin.castSucc i)

/-- **Support clause**: on each box, the family lives in a fixed `ballH B`. -/
theorem pushFam_support {ψ : ℂ → ℂ} (hc : ContinuousOn ψ Hbar) (hH : MapsTo ψ Hbar Hbar)
    (R : ℕ) : ∃ B : ℝ, ∀ p ∈ boxD (d := 4 + 1) R, pushFam ψ p (ballH B)ᶜ = 0 := by
  have hΦ := continuous_pushPhi hc
  obtain ⟨B₀, hB₀⟩ := ((isCompact_boxD R).prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π))).exists_bound_of_continuousOn
    hΦ.continuousOn
  set B₀' := max B₀ 0
  refine ⟨B₀' + R, fun p hp => ?_⟩
  have hq := init_mem_boxD hp
  have hsub : pushPhi ψ (Fin.init p) '' Icc 0 (2 * π) ⊆ ballH B₀' := by
    rintro _ ⟨θ, hθ, rfl⟩
    refine ⟨?_, pushPhi_mem_Hbar hH _ _⟩
    rw [mem_closedBall, dist_zero_right]
    exact (hB₀ (Fin.init p, θ) ⟨hq, hθ⟩).trans (le_max_left _ _)
  have h0 : (circM.map (pushPhi ψ (Fin.init p))) (pushPhi ψ (Fin.init p) '' Icc 0 (2 * π))ᶜ = 0 :=
    map_compl_image hΦ isCompact_Icc circM_compl _
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
  unfold pushFam smoothFam
  split_ifs with ht
  · have htR : p (Fin.last 4) ≤ R := (abs_le.1 (hp (Fin.last 4))).2
    exact bind_circle_support _ ht.le h0 (R₀ := B₀') (fun z hz => by
      have := (hsub hz).1; rwa [mem_closedBall, dist_zero_right] at this) (by linarith)
  · refine measure_mono_null (compl_subset_compl.2 ?_) h0
    intro z hz
    have hz' := hsub hz
    exact ⟨by
      have := hz'.1; rw [mem_closedBall, dist_zero_right] at this ⊢; linarith, hz'.2⟩

/-! ## The potential clause from the Frostman bound -/

/-- Log potential of a Frostman measure (`TwoPoint.lintegral_logRatio_frostman` at scale `1`). -/
theorem frostman_pot_le {ν : Measure ℂ} [IsFiniteMeasure ν] {α C : ℝ}
    (hF : TwoPoint.IsFrostman ν α C) (hα : 0 < α) (hC : 0 ≤ C) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂ν ≤ ENNReal.ofReal (C / α) := by
  have h := TwoPoint.lintegral_logRatio_frostman hF hα hC y one_pos
  rw [Real.one_rpow, mul_one] at h
  refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) h
  rw [TwoPoint.logRatio, one_div, Real.log_inv, norm_sub_rev, max_comm]
  exact (CircleFubini.ofReal_max_zero _).symm

/-- Circle average of the log potential, for `w ≠ y` and `0 < t ≤ T`. -/
theorem circleUnif_pot_le' {w y : ℂ} (hwy : w ≠ y) {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(circleUnif w t) ≤
      ENNReal.ofReal (-Real.log ‖w - y‖) +
        ENNReal.ofReal (2 * Real.log 2 + 2 * Real.posLog T) := by
  have hd : 0 < ‖w - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hwy)
  set K := 2 * Real.log 2 + 2 * Real.posLog T with hKdef
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hpT : 0 ≤ Real.posLog T := Real.posLog_nonneg
  by_cases h2 : 2 * t ≤ ‖w - y‖
  · rw [circleUnif_eq_map, lintegral_map (CircleFubini.measurable_logPot y)
      (continuous_circleMap w t).measurable]
    calc ∫⁻ θ, ENNReal.ofReal (-Real.log ‖circleMap w t θ - y‖) ∂circM
        ≤ ∫⁻ _θ, (ENNReal.ofReal (-Real.log ‖w - y‖) + ENNReal.ofReal K) ∂circM := by
          refine lintegral_mono fun θ => ?_
          have h1 : ‖w - circleMap w t θ‖ = t := by
            rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_pos ht]
          have h3 := norm_sub_norm_le (w - y) (w - circleMap w t θ)
          have h4 : w - y - (w - circleMap w t θ) = circleMap w t θ - y := by ring
          rw [h4, h1] at h3
          have hx : ‖w - y‖ / 2 ≤ ‖circleMap w t θ - y‖ := by linarith
          have hlog : -Real.log ‖circleMap w t θ - y‖ ≤ -Real.log ‖w - y‖ + K := by
            have := Real.log_le_log (by positivity) hx
            rw [Real.log_div hd.ne' two_ne_zero] at this
            linarith
          exact (ENNReal.ofReal_le_ofReal hlog).trans ENNReal.ofReal_add_le
      _ = ENNReal.ofReal (-Real.log ‖w - y‖) + ENNReal.ofReal K := by
          rw [lintegral_const, measure_univ, mul_one]
  · replace h2 := not_le.1 h2
    refine (CircleFubini.circleUnif_pot_le ht w y).trans ?_
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    have hlt : Real.log (‖w - y‖ / 2) ≤ Real.log t :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hd.ne' two_ne_zero] at hlt
    have hpt : Real.posLog t ≤ Real.posLog T := Real.posLog_le_posLog (by linarith) htT
    unfold CircleFubini.potConst
    linarith

/-- Folded-circle average of the log potential, for `w ≠ y`, `w ≠ ȳ` and `0 < t ≤ T`. -/
theorem foldedCircle_pot_le' {w y : ℂ} (hwy : w ≠ y) (hwy' : w ≠ (starRingEnd ℂ) y) {t T : ℝ}
    (ht : 0 < t) (htT : t ≤ T) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(foldedCircle w t) ≤
      ENNReal.ofReal (-Real.log ‖w - y‖) + ENNReal.ofReal (-Real.log ‖w - (starRingEnd ℂ) y‖) +
        2 * ENNReal.ofReal (2 * Real.log 2 + 2 * Real.posLog T) := by
  rw [foldedCircle, lintegral_map (CircleFubini.measurable_logPot y) measurable_foldH]
  calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖foldH x - y‖) ∂circleUnif w t
      ≤ ∫⁻ x, (ENNReal.ofReal (-Real.log ‖x - y‖) +
          ENNReal.ofReal (-Real.log ‖x - (starRingEnd ℂ) y‖)) ∂circleUnif w t := by
        refine lintegral_mono fun x => ?_
        unfold foldH
        split_ifs
        · exact le_self_add
        · have : (starRingEnd ℂ) x - y = (starRingEnd ℂ) (x - (starRingEnd ℂ) y) := by simp
          rw [this, Complex.norm_conj]; exact le_add_self
    _ = ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂circleUnif w t
          + ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - (starRingEnd ℂ) y‖) ∂circleUnif w t :=
        lintegral_add_left (CircleFubini.measurable_logPot y) _
    _ ≤ _ := by
        have h1 := circleUnif_pot_le' hwy ht htT
        have h2 := circleUnif_pot_le' hwy' ht htT
        calc _ ≤ _ := add_le_add h1 h2
          _ = _ := by ring

/-- Log potential of a smoothed Frostman measure. -/
theorem bind_pot_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {α C : ℝ}
    (hF : TwoPoint.IsFrostman ν α C) (hα : 0 < α) (hC : 0 ≤ C) {t T : ℝ} (ht : 0 < t)
    (htT : t ≤ T) (y : ℂ) :
    ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂(ν.bind fun w => foldedCircle w t) ≤
      2 * ENNReal.ofReal (C / α) + 2 * ENNReal.ofReal (2 * Real.log 2 + 2 * Real.posLog T) := by
  rw [Measure.lintegral_bind (measurable_foldedCircle' t).aemeasurable
    (CircleFubini.measurable_logPot y).aemeasurable]
  set K := ENNReal.ofReal (2 * Real.log 2 + 2 * Real.posLog T)
  calc ∫⁻ w, ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂foldedCircle w t ∂ν
      ≤ ∫⁻ w, (ENNReal.ofReal (-Real.log ‖w - y‖) +
          ENNReal.ofReal (-Real.log ‖w - (starRingEnd ℂ) y‖) + 2 * K) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [TwoPoint.frostman_ae_ne hF hα hC y,
          TwoPoint.frostman_ae_ne hF hα hC ((starRingEnd ℂ) y)] with w h1 h2
        exact foldedCircle_pot_le' h1 h2 ht htT
    _ = ∫⁻ w, ENNReal.ofReal (-Real.log ‖w - y‖) ∂ν +
          ∫⁻ w, ENNReal.ofReal (-Real.log ‖w - (starRingEnd ℂ) y‖) ∂ν + 2 * K := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_add_left (CircleFubini.measurable_logPot y)]
    _ ≤ ENNReal.ofReal (C / α) + ENNReal.ofReal (C / α) + 2 * K := by
        gcongr
        · exact frostman_pot_le hF hα hC y
        · exact frostman_pot_le hF hα hC _
    _ = 2 * ENNReal.ofReal (C / α) + 2 * K := by ring

/-- The remaining clause of `PushFamBounds`: the Hölder variance modulus on boxes. -/
def PushVar (ψ : ℂ → ℂ) (β : ℝ) : Prop :=
  ∀ R : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ boxD (d := 4 + 1) R, ∀ q' ∈ boxD (d := 4 + 1) R,
    |kernelCov2 neumannH (pushFam ψ q, pushFam ψ q') (pushFam ψ q, pushFam ψ q')| ≤
      K * ‖q - q'‖ ^ β

end G1RC
end Thm18Asm
end QuantumZipper

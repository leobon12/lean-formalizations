import QuantumZipper.Proofs.Zipper.LocLenF2Chain
import QuantumZipper.Proofs.Zipper.LocLenAddConst
import QuantumZipper.Proofs.Zipper.LocLenLocality
import QuantumZipper.Proofs.Zipper.F2WedgeCouple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R7-S2b: F2 step (2b) with open-arc lengths

Open-arc copy of `F2.step2b_of_inputs` (F2Step2b.lean:159). With the open-arc reading, B5
locality is **B4** `LocLen.unzipLengthsArc_eq_of_dyCircAgree`, which needs no boundary limit at
all, so the input `F2.WedgeUnzipLimitAllStmt` of the old proof (global limits of the unzipped
wedge field at every time) and the junk-case lemma disappear. Inputs: the proved coupling
`F2.wedgeLogCouplingStmt_holds` and the proved `LocLen.addConstAgreeArc_holds`. Hence
`step2bArc_holds : Step2bArcStmt` outright.

Sheffield arXiv:1012.4797 §5.4 pp. 70–71 (restriction to a small ball, locality, the additive
constant); Berestycki–Powell arXiv:2404.16642 p. 294. Own bookkeeping as the old file.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- At time `0` both open arcs are empty. -/
theorem agree_zero_time_arc (γ : ℝ) (x : FieldSample) {W : ℝ → ℝ} (hW0 : W 0 = 0) :
    (unzipLengthsArc γ (x, W) 0).1 = (unzipLengthsArc γ (x, W) 0).2 := by
  simp only [unzipLengthsArc, B5.sideImages_fst_zero_time hW0, F2.sideImages_snd_zero_time hW0]

/-- **Pathwise transfer by B4 locality** (copy of `F2.agree_of_dyCircAgree`, no boundary-limit
hypotheses). -/
theorem agree_of_dyCircAgree_arc {γ t M a : ℝ} {w y : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 < t) (hM : ∀ r ∈ Icc (0 : ℝ) t, |W r| ≤ M)
    (ha₁ : |(sideImages W t).1| < a) (ha₂ : |(sideImages W t).2| < a) {j₀ : ℕ}
    (hag : B5.DyCircAgree w y (Metric.ball 0 (2 * a + 6 * M + 6 * Real.sqrt t)) j₀)
    (hlen : (unzipLengthsArc γ (w, W) t).1 = (unzipLengthsArc γ (w, W) t).2) :
    (unzipLengthsArc γ (y, W) t).1 = (unzipLengthsArc γ (y, W) t).2 := by
  have ha0 : 0 < a := (abs_nonneg _).trans_lt ha₁
  have key : unzipLengthsArc γ (w, W) t = unzipLengthsArc γ (y, W) t := by
    refine unzipLengthsArc_eq_of_dyCircAgree w y hW hW hW0 hW0 ht.le (fun _ _ => rfl)
      (U := Ioo (-a) a) ?_ ?_ Metric.isOpen_ball ha0 ?_ hag
    · intro u hu
      have := (abs_lt.1 ha₁).1
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · intro u hu
      have := (abs_lt.1 ha₂).2
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · rintro u hu ⟨s, hs, hus⟩
      rw [Metric.mem_ball, dist_zero_right]
      have h1 := B5.norm_fwdMapInv_sub_le hW hW0 ht hM hu
      have h2 : ‖u‖ < 2 * a := by
        have hs' : ‖((s : ℝ) : ℂ)‖ < a := by
          rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_lt.2 ⟨hs.1, hs.2⟩
        calc ‖u‖ ≤ ‖u - (s : ℂ)‖ + ‖((s : ℝ) : ℂ)‖ := norm_le_norm_sub_add _ _
          _ < 2 * a := by rw [← dist_eq_norm]; linarith
      calc ‖fwdMapInv W t u‖ ≤ ‖fwdMapInv W t u - u‖ + ‖u‖ := norm_le_norm_sub_add _ _
        _ < _ := by linarith
  rw [← key]; exact hlen

/-- **F2 step (2b) with open arcs** from the coupling and the additive constant (copy of
`F2.step2b_of_inputs` without its global-limit input). -/
theorem step2bArc_of_inputs (hC : F2.WedgeLogCouplingStmt) (hK : AddConstAgreeArcStmt) :
    Step2bArcStmt := by
  intro hU κ hκ hκ4
  obtain ⟨M₁, hM₁, t₁, ht₁, hside⟩ := B5.sideSmallStmt (1 / 16) (by norm_num)
  refine ⟨min t₁ ((1 / 48) ^ 2), min M₁ (1 / 96), lt_min ht₁ (by norm_num),
    lt_min hM₁ (by norm_num), ?_⟩
  intro Ω _ P _ B X hB hX hind
  obtain ⟨Ω₂, _, Q, _, X', A, C, j₀, hX', hA, hXA, hB'', hind'', hag⟩ :=
    hC κ hκ hκ4 P B X hB hX hind
  have hUa := hU κ hκ hκ4 (P.prod Q) X' A _ hX' hA hXA hB'' hind''
  have hKa : ∀ᵐ ω ∂(P.prod Q), ∀ t : ℝ, 0 < t → ∀ c : ℝ,
      (unzipLengthsArc (Real.sqrt κ) (addConst (X ω.1 + F2.logSingField κ) c, drive κ B ω.1) t).1 =
        (unzipLengthsArc (Real.sqrt κ)
          (addConst (X ω.1 + F2.logSingField κ) c, drive κ B ω.1) t).2 →
      (unzipLengthsArc (Real.sqrt κ) (X ω.1 + F2.logSingField κ, drive κ B ω.1) t).1 =
        (unzipLengthsArc (Real.sqrt κ) (X ω.1 + F2.logSingField κ, drive κ B ω.1) t).2 :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae (hK κ hκ hκ4 P B X hB hX hind)
  refine F2.ae_of_ae_prod_fst (Q := Q) ?_
  filter_upwards [hUa, hKa, hag, hB''.cont, hB''.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    RS.ae_real_alive hB'' hκ hκ4.le] with ω hu hk hg hc h0 halive
  set W : ℝ → ℝ := drive κ B ω.1 with hWdef
  have hWc : Continuous W := drive_continuous hc
  have hW0 : W 0 = 0 := drive_zero h0
  intro t ht0 htt hMW
  rcases eq_or_lt_of_le ht0 with rfl | ht
  · exact agree_zero_time_arc _ _ hW0
  refine hk t ht (C ω) ?_
  obtain ⟨hs₁, hs₂⟩ := hside W hWc hW0 t ⟨ht, htt.trans (min_le_left _ _)⟩
    (fun x hx => halive x hx t ht.le) (fun r hr => (hMW r hr).trans (min_le_left _ _))
  have hsq : Real.sqrt t ≤ 1 / 48 := by
    calc Real.sqrt t ≤ Real.sqrt ((1 / 48) ^ 2) :=
          Real.sqrt_le_sqrt (htt.trans (min_le_right _ _))
      _ = 1 / 48 := Real.sqrt_sq (by norm_num)
  refine agree_of_dyCircAgree_arc hWc hW0 ht hMW hs₁ hs₂ (hg.mono (Metric.ball_subset_ball ?_))
    (hu t ht0)
  have : min M₁ (1 / 96) ≤ 1 / 96 := min_le_right _ _
  linarith

/-- **F2 step (2b) with open arcs holds.** -/
theorem step2bArc_holds : Step2bArcStmt :=
  step2bArc_of_inputs F2.wedgeLogCouplingStmt_holds addConstAgreeArc_holds

end LocLen
end QuantumZipper

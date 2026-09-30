import QuantumZipper.Proofs.Zipper.LocLenStep3Defs
import QuantumZipper.Proofs.Zipper.LocLenXGood
import QuantumZipper.Proofs.Zipper.F2Step3DensSign

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7a-D: rule (5.1) at the unzipped level on open arcs

Main results:

* `step3InvDensityArc_of_yGoodOff : YGoodOffAllStmt → Step3InvDensityArcStmt`;
* `step3LocalDensityArc_of_inv : Step3InvDensityArcStmt → Step3LocalDensityArcStmt`;
* closed forms `step3InvDensityArc_of_yMergeOffTip`, `step3LocalDensityArc_of_yMergeOffTip`.

Route (as `xGoodOffAll_of_yGoodOff`, LocLenXGood.lean): a.s., for all `t ≥ 0`, `x_t` and
`y_t + ψ_t` have the same coordinates (`WedgeUnzip.coords_unzX_eq`), where
`ψ_t = −γ log‖E_t‖` is continuous on `ℍ̄` off the root images `O^±_t`. The local rule (5.1)
`HasBdryLimitOn.add_ofFun` then gives `ν_{x_t} = e^{γψ_t/2} ν_{y_t} = |F_t|^{−γ²/2} ν_{y_t}` on
`(offSet)ᶜ`. Inverting the density (`F_t ≠ 0` off the root images) gives
`ν_{y_t} = |F_t|^{γ²/2} ν_{x_t}`.

Paper: Sheffield, arXiv:1012.4797, p. 70 (the wedge field is the `Γ⁰` field plus
`−γ log|f_t^{-1}|`, continuous away from the root images) and §5.1 rule (5.1);
Berestycki–Powell arXiv:2404.16642 Def 6.41 p. 229. The density inversion is elementary
(own bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Local boundary limits only read the countable coordinates. -/
theorem hasBdryLimitOn_congr_coords {γ : ℝ} {x y : FieldSample}
    (h : Factorization.coords x = Factorization.coords y) {U : Set ℝ} {ν : Measure ℝ} :
    HasBdryLimitOn γ x U ν ↔ HasBdryLimitOn γ y U ν := by
  refine hasBdryLimitOn_congr_avg ?_
  rw [← Factorization.avgReg_reconstruct_coords x, h, Factorization.avgReg_reconstruct_coords]

/-- **Rule (5.1), inverse direction, on open arcs**, from the `Γ⁰` goodness off the tip. -/
theorem step3InvDensityArc_of_yGoodOff (hY : YGoodOffAllStmt) : Step3InvDensityArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [WedgeUnzip.coords_unzX_eq hκ hκ4 hB hX hind, hY κ hκ hκ4 P B X hB hX hind,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.extNonvanishStmt_holds κ hκ hκ4 P B hB,
    xGoodOffAll_of_yGoodOff hY κ hκ hκ4 P B X hB hX hind,
    F2.step3SideSign_holds κ hκ hκ4 P B X hB hX hind]
    with ω hco hyω hCω hNVω hXω hSω t ht
  have hψ : ContinuousOn (WedgeUnzip.logTipFun κ (drive κ B ω) t)
      ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) := by
    intro u hu
    have hc : ContinuousWithinAt (F2.extInv (drive κ B ω) t)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      (hCω t ht u hu.2).mono inter_subset_right
    have hne : F2.extInv (drive κ B ω) t u ≠ 0 := hNVω t ht u hu.2 hu.1
    have hlog : ContinuousWithinAt (fun v => Real.log ‖F2.extInv (drive κ B ω) t v‖)
        ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ ∩ Hbar) u :=
      hc.norm.log (norm_ne_zero_iff.2 hne)
    exact (hlog.const_mul (Real.sqrt κ)).neg
  have hWo : IsOpen ((((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ) :=
    ((WedgeUnzip.isCompact_tipSet _ t).image Complex.continuous_ofReal).isClosed.isOpen_compl
  have hUo : IsOpen (offSet (drive κ B ω) t)ᶜ := (isClosed_offSet _ t).isOpen_compl
  have hUW : ∀ s ∈ (offSet (drive κ B ω) t)ᶜ,
      (s : ℂ) ∈ (((↑) : ℝ → ℂ) '' WedgeUnzip.tipSet (drive κ B ω) t)ᶜ := by
    rintro s hs ⟨u, hu, hus⟩
    obtain rfl := Complex.ofReal_injective hus
    apply hs
    rcases hu with rfl | rfl <;> simp [offSet]
  have hsub : (offSet (drive κ B ω) t)ᶜ ⊆ ({0} : Set ℝ)ᶜ :=
    compl_subset_compl.2 (singleton_subset_iff.2 (by simp [offSet]))
  obtain ⟨hyReg, ⟨ν, hν⟩, -⟩ := hyω t ht
  have hν' := hν.mono hUo hsub
  have hadd := hν'.add_ofFun hyReg hUo hWo hUW hψ
  refine ⟨(hSω t ht).1, (hSω t ht).2, (hXω t ht).1, hyReg, _, _,
    (hasBdryLimitOn_congr_coords (hco t ht)).2 hadd, hν', ?_⟩
  congr 1
  funext s
  simp [F1.lswDens, F1.lswPhi, WedgeUnzip.logTipFun, F2.extInv_ofReal]

/-- `e^{γ/2·(−γ log‖z‖)} · ‖z‖^{γ²/2} = 1` for `z ≠ 0`. -/
theorem lswDens_mul_logDens_eq_one {κ : ℝ} {z : ℂ} (hz : z ≠ 0) :
    ENNReal.ofReal (Real.exp (Real.sqrt κ / 2 * F1.lswPhi κ (fun _ => 0) z)) *
      F2.logDens (Real.sqrt κ) z = 1 := by
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  unfold F2.logDens F1.lswPhi
  rw [Real.rpow_def_of_pos hpos, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  have h0 : Real.sqrt κ / 2 * (-(Real.sqrt κ * Real.log ‖z‖) + 0) +
      Real.log ‖z‖ * (Real.sqrt κ ^ 2 / 2) = 0 := by ring
  rw [h0, Real.exp_zero, ENNReal.ofReal_one]

/-- **Rule (5.1) in the forward direction, on open arcs**, from the inverse direction. -/
theorem step3LocalDensityArc_of_inv (h : Step3InvDensityArcStmt) : Step3LocalDensityArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [h κ hκ hκ4 P B X hB hX hind,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB,
    WedgeUnzip.extNonvanishStmt_holds κ hκ hκ4 P B hB] with ω hω hCω hNVω t ht
  obtain ⟨h1, h2, hxR, hyR, νx, νy, hx, hy, hdens⟩ := hω t ht
  refine ⟨h1, h2, hxR, hyR, νx, νy, hx, hy, ?_⟩
  have hFc : Continuous (F2.invBdry (drive κ B ω) t) := by
    have hc := (hCω t ht).comp_continuous Complex.continuous_ofReal
      (fun x => show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp)
    simpa [Function.comp_def] using hc
  have hρm : Measurable (F1.lswDens κ (fun _ => 0) (F2.invBdry (drive κ B ω) t)) :=
    F1.measurable_lswDens continuous_const hFc.measurable
  have hgm : Measurable
      (fun w => F2.logDens (Real.sqrt κ) (F2.invBdry (drive κ B ω) t w)) := by
    unfold F2.logDens
    exact ENNReal.measurable_ofReal.comp
      ((continuous_norm.comp hFc).measurable.pow_const _)
  rw [hdens, ← withDensity_mul _ hρm hgm]
  conv_lhs => rw [← withDensity_one (μ := νy)]
  refine withDensity_congr_ae ?_
  have hUo : IsOpen (offSet (drive κ B ω) t)ᶜ := (isClosed_offSet _ t).isOpen_compl
  have hconc : ∀ᵐ w ∂νy, w ∈ (offSet (drive κ B ω) t)ᶜ :=
    measure_mono_null (fun w hw => hw) hy.1
  filter_upwards [hconc] with w hw
  have hne : F2.invBdry (drive κ B ω) t w ≠ 0 := by
    rw [← F2.extInv_ofReal]
    refine hNVω t ht _ (show (0 : ℝ) ≤ ((w : ℝ) : ℂ).im by simp) ?_
    rw [WedgeUnzip.ofReal_mem_tipPts_iff]
    intro hw'
    apply hw
    rcases hw' with hw' | hw' <;> simp [offSet, hw']
  simp only [Pi.one_apply, Pi.mul_apply, F1.lswDens]
  exact (lswDens_mul_logDens_eq_one hne).symm

/-- **Closed form**: rule (5.1), inverse direction, from the offset merging input. -/
theorem step3InvDensityArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    Step3InvDensityArcStmt :=
  step3InvDensityArc_of_yGoodOff (yGoodOffAll_of_yMergeOffTip hYO)

/-- **Closed form**: rule (5.1), forward direction, from the offset merging input. -/
theorem step3LocalDensityArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) :
    Step3LocalDensityArcStmt :=
  step3LocalDensityArc_of_inv (step3InvDensityArc_of_yMergeOffTip hYO)

end LocLen
end QuantumZipper

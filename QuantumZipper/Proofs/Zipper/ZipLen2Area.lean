import QuantumZipper.Proofs.Zipper.ZipLenMain
import QuantumZipper.Proofs.Zipper.WedgeYGoodArea
import QuantumZipper.Proofs.Zipper.AreaCoord
import QuantumZipper.Proofs.Zipper.PStarAreaCoord

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2: the `Γ⁰` area node `YAreaAllStmt` from the `Γ⁰` area merging rule

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.6, p. 21 (finite area
near `0`, infinite area near `∞`); Duplantier–Sheffield, *Liouville quantum gravity and KPZ*,
Invent. Math. 185 (2011), Prop. 2.1 (area coordinate change), in the Sheffield–Wang merging form
`WedgeUnzip.YAreaMergeStmt` (Sheffield–Wang, arXiv:1605.06171, proof of Thm 1.4, (3.5)–(3.7)).

* time `0`: `𝔥₀ + X = X + Lf(−2/√κ)`, so its area measure is `‖z‖² · μ_X`
  (`LogSingGood.hasAreaLimit_add_Lf`), finite on half-discs and of infinite total mass because
  `μ_X` is (`E6.ae_areaAll_freeField`) — `areaAll_add_Lf_two`;
* all times: the merging rule at unit offset (`GoodSample.tendsto_one_goodFilter`,
  `GoodSample.areaR_radius`) gives the area coordinate change `E6.coord_of_merge`, and
  `E6.areaAll_unzippedField_of_coord` transports `AreaAll` along the unzipping map.

Own elementary bookkeeping around the cited results. Main result: `yAreaAllStmt_of_merge`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

/-- **`AreaAll` for the free field plus `Lf(−2/γ)`** (area density `‖z‖²`). -/
theorem areaAll_add_Lf_two {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hxr : IsRegularSample x)
    (hA : HasAreaLimit γ x (qAreaMeasure γ x)) (hAll : E6.AreaAll γ x) :
    E6.AreaAll γ (x + ofFun (LogSingGood.Lf (-(2 / γ)))) := by
  obtain ⟨F, hF⟩ := hxr
  have hq : qAreaMeasure γ (x + ofFun (LogSingGood.Lf (-(2 / γ)))) =
      (qAreaMeasure γ x).withDensity
        (fun z => ENNReal.ofReal (‖z‖ ^ (-(-(2 / γ) * γ)))) :=
    GoodSample.qAreaMeasure_eq_of_hasAreaLimit ⟨_, LogSingGood.regular_add_Lf hF _⟩
      (LogSingGood.hasAreaLimit_add_Lf hF hA _)
  have he : -(-(2 / γ) * γ) = (2 : ℝ) := by field_simp
  rw [he] at hq
  set μ := qAreaMeasure γ x with hμ
  have hmeas : Measurable fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (2 : ℝ)) := by fun_prop
  unfold E6.AreaAll
  rw [hq]
  refine ⟨fun a => ?_, ?_⟩
  · have hS : MeasurableSet (Metric.ball (0 : ℂ) a ∩ H) :=
      (Metric.isOpen_ball.inter isOpen_H).measurableSet
    rw [withDensity_apply _ hS]
    calc ∫⁻ z in Metric.ball (0 : ℂ) a ∩ H, ENNReal.ofReal (‖z‖ ^ (2 : ℝ)) ∂μ
        ≤ ∫⁻ _z in Metric.ball (0 : ℂ) a ∩ H, ENNReal.ofReal (a ^ (2 : ℝ)) ∂μ := by
          refine setLIntegral_mono measurable_const fun z hz => ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖z‖ < a := by simpa [Metric.mem_ball, dist_zero_right] using hz.1
          exact Real.rpow_le_rpow (norm_nonneg z) h1.le (by norm_num)
      _ = ENNReal.ofReal (a ^ (2 : ℝ)) * μ (Metric.ball (0 : ℂ) a ∩ H) := setLIntegral_const _ _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hAll.1 a)
  · rw [withDensity_apply _ isOpen_H.measurableSet]
    refine eq_top_iff.2 ?_
    rw [← E6.qAreaMeasure_H_sub_closedBall_eq_top hAll.1 hAll.2 1, ← setLIntegral_one]
    have hD : MeasurableSet (H \ Metric.closedBall (0 : ℂ) 1) :=
      isOpen_H.measurableSet.diff Metric.isClosed_closedBall.measurableSet
    calc ∫⁻ _z in H \ Metric.closedBall (0 : ℂ) 1, (1 : ℝ≥0∞) ∂μ
        ≤ ∫⁻ z in H \ Metric.closedBall (0 : ℂ) 1, ENNReal.ofReal (‖z‖ ^ (2 : ℝ)) ∂μ := by
          refine setLIntegral_mono' hD fun z hz => ?_
          have h1 : 1 < ‖z‖ := by
            have := hz.2
            simpa [Metric.mem_closedBall, dist_zero_right, not_le] using this
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.one_le_rpow h1.le (by norm_num))
      _ ≤ ∫⁻ z in H, ENNReal.ofReal (‖z‖ ^ (2 : ℝ)) ∂μ := lintegral_mono_set sdiff_subset

variable {Ω : Type} [MeasurableSpace Ω]

/-- **`YAreaAllStmt` from the `Γ⁰` area merging rule** `WedgeUnzip.YAreaMergeStmt`. -/
theorem yAreaAllStmt_of_merge (hM : WedgeUnzip.YAreaMergeStmt) : YAreaAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := F2.sqrt_lt_two_of' hκ hκ4
  filter_upwards [hM κ hκ hκ4 P B X hB hX hind, RegSample.ae_isRegularSample hX,
    AreaOffsets.ae_hasAreaLimit hX hγ hγ2, E6.ae_areaAll_freeField hγ hγ2 hX,
    RegUnif.ae_drive_good hB κ,
    RegUnif.ae_forall_isRegularSample (κ := κ) (γ := Real.sqrt κ) hB hX hind]
    with ω hm hreg hA hAll hdr hregt t ht
  set W := drive κ B ω with hWdef
  have hy0 : E6.AreaAll (Real.sqrt κ) (ofFun (h0rev κ) + X ω) := by
    rw [WedgeUnzip.h0rev_add_eq_Lf]
    exact areaAll_add_Lf_two hγ hreg hA hAll
  have hy0reg : IsRegularSample (ofFun (h0rev κ) + X ω) := by
    rw [WedgeUnzip.h0rev_add_eq_Lf]
    obtain ⟨F, hF⟩ := hreg
    exact ⟨_, LogSingGood.regular_add_Lf hF _⟩
  obtain ⟨F0, hF0⟩ := hy0reg
  obtain ⟨Ft, hFt⟩ := (hregt t ht).1
  have hmerge : ∀ f : ℂ → ℝ, E6.IsAreaTest f →
      Tendsto (E6.mergeDiff (Real.sqrt κ) (ofFun (h0rev κ) + X ω) W f t) atTop (𝓝 0) := by
    rintro f ⟨hf, hfc, hfH⟩
    have h := (hm t ht f hf hfc hfH).comp GoodSample.tendsto_one_goodFilter
    refine h.congr fun k => ?_
    have e1 := GoodSample.areaR_radius (Real.sqrt κ) hFt k
    have e2 := GoodSample.areaR_radius (Real.sqrt κ) hF0 k
    simp only [Function.comp_apply, WedgeUnzip.mergeDiffG, E6.mergeDiff, goodRad]
    rw [e1, e2]
  have hcoord := E6.coord_of_merge hdr.1 hdr.2 ht hy0 hmerge
  rw [← unzippedField_cfg_eq]
  exact E6.areaAll_unzippedField_of_coord hdr.1 hdr.2 ht hy0 hcoord

end ZipLen
end B3d
end QuantumZipper

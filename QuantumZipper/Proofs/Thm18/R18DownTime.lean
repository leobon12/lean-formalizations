import QuantumZipper.Proofs.Thm18.R18RoundUpDet
import QuantumZipper.Proofs.Thm18.R18G4Nodes
import QuantumZipper.Proofs.Wire4
import QuantumZipper.Proofs.Zipper.WedgeLawReg
import QuantumZipper.Proofs.Zipper.AreaWinTransfer
import QuantumZipper.Proofs.Zipper.LocLenPStarArea
import QuantumZipper.Proofs.Zipper.PStarAreaAllBasic
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll
import QuantumZipper.Proofs.Zipper.WeldingUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 (helper R18-DOWNTIME): the scale of `Z^LEN_{−ℓ} ∘ Z^LEN_ℓ`, `b > 0`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
`Z^LEN_ℓ` zips up by welding and rescales by (1.8) so that `B₁(0)` "has area one in the
transformed quantum measure". The rescaling parameter `b` of the zipped configuration is the
area scale of the pushed area `(μ|_ℍ) ∘ revMap⁻¹`; this file proves `0 < b` a.s. (the first
conjunct of `R18.G4DownScaleTimeAStmt`, R18RoundUp.lean:59), and reduces that statement to the
welding node `G4WeldAStmt` and its time conjunct `G4DownTimeAStmt`.

Proof of `0 < b` (own elementary argument, the one of `E6.scaleParam_pos_of_area`,
HitScaleZip.lean:104, for a general measure): the wedge area is finite on half-discs and infinite
on `ℍ` (`LocLen.pStarAreaAll_of_yMergeOffTip` at time `0`, `E6.qAreaMeasure_unzippedField_zero`);
`revMap W' T` maps `ℍ` into `ℍ` (`TwoPoint.im_revMap_pos`) and moves far points by a bounded
amount (`exists_far_bound_revMap`), so the pushed measure is again finite on half-discs and
infinite on `ℍ`; then small half-discs have pushed mass `< 1` (continuity from above) and a large
one has mass `≥ 1`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Positive area scale** for a general measure finite on half-discs and infinite on `ℍ`
(the argument of `E6.scaleParam_pos_of_area`; own elementary). -/
theorem areaScale_pos_of_area {μ : Measure ℂ}
    (hfin : ∀ a : ℝ, μ (Metric.ball 0 a ∩ H) < ⊤) (hinf : μ H = ⊤) : 0 < areaScale μ := by
  have hmeasB : ∀ b : ℝ, MeasurableSet (Metric.ball (0 : ℂ) b ∩ H) := fun b =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  have hup : Tendsto (fun n : ℕ => μ (Metric.ball (0 : ℂ) n ∩ H)) atTop (𝓝 (μ H)) := by
    have hU : (⋃ n : ℕ, Metric.ball (0 : ℂ) n ∩ H) = H := by
      rw [← iUnion_inter, Metric.iUnion_ball_nat, univ_inter]
    have hmono : Monotone fun n : ℕ => Metric.ball (0 : ℂ) n ∩ H := fun m n hmn =>
      inter_subset_inter_left _ (Metric.ball_subset_ball (by exact_mod_cast hmn))
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rwa [hU] at this
  rw [hinf] at hup
  obtain ⟨N, hN⟩ := (hup.eventually (lt_mem_nhds ENNReal.one_lt_top)).exists
  have hmem : ((N : ℝ) + 1) ∈ {a : ℝ | 0 < a ∧ 1 ≤ μ (Metric.ball 0 a ∩ H)} :=
    ⟨by positivity, hN.le.trans (measure_mono (inter_subset_inter_left _
      (Metric.ball_subset_ball (by linarith))))⟩
  set s : ℕ → Set ℂ := fun n => Metric.ball (0 : ℂ) (1 / ((n : ℝ) + 1)) ∩ H with hs
  have hanti : Antitone s := by
    intro m n hmn
    refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    gcongr
  have hempty : (⋂ n, s n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    rw [mem_iInter] at hz
    have hz0 : z ∈ H := (hz 0).2
    have hzy : dist z (0 : ℂ) = 0 := by
      refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) dist_nonneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have := (hz n).1
      rw [Metric.mem_ball] at this
      linarith
    rw [dist_eq_zero] at hzy
    have him : z.im = 0 := by rw [hzy]; simp
    exact absurd hz0 (by simp [H, him])
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hmeasB _).nullMeasurableSet)
    hanti ⟨0, (hfin _).ne⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (zero_lt_one' ℝ≥0∞))).exists
  have hlb : ∀ a ∈ {a : ℝ | 0 < a ∧ 1 ≤ μ (Metric.ball 0 a ∩ H)}, 1 / ((n : ℝ) + 1) ≤ a := by
    rintro a ⟨-, h1a⟩
    by_contra hlt
    rw [not_le] at hlt
    exact absurd (h1a.trans (measure_mono (inter_subset_inter_left _
      (Metric.ball_subset_ball hlt.le)))) (not_le.2 hn)
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  exact hpos.trans_le (le_csInf ⟨_, hmem⟩ hlb)

/-- **The pushed area along the reverse flow keeps the area property**: if `μ` is finite on
half-discs and infinite on `ℍ`, so is `(μ|_ℍ).map (revMap W T)` (own elementary). -/
theorem areaAll_map_revMap {μ : Measure ℂ} {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hfin : ∀ a : ℝ, μ (Metric.ball 0 a ∩ H) < ⊤) (hinf : μ H = ⊤) :
    (∀ a : ℝ, ((μ.restrict H).map (revMap W T)) (Metric.ball 0 a ∩ H) < ⊤) ∧
      ((μ.restrict H).map (revMap W T)) H = ⊤ := by
  have hm : Measurable (revMap W T) := TwoPoint.measurable_revMap hW hT
  have hmeasB : ∀ b : ℝ, MeasurableSet (Metric.ball (0 : ℂ) b ∩ H) := fun b =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  have hHm : MeasurableSet H := isOpen_H.measurableSet
  refine ⟨fun a => ?_, ?_⟩
  · obtain ⟨C, R, hCR⟩ := WeldingUniqueness.exists_far_bound_revMap hW hT
    rw [Measure.map_apply hm (hmeasB a), Measure.restrict_apply (hm (hmeasB a))]
    refine lt_of_le_of_lt (measure_mono ?_) (hfin (max R (a + C + 1)))
    rintro z ⟨⟨hza, -⟩, hzH⟩
    refine ⟨?_, hzH⟩
    rw [Metric.mem_ball, dist_zero_right] at hza ⊢
    by_cases hzR : R ≤ ‖z‖
    · have h1 := hCR z hzH hzR
      have h2 : ‖z‖ ≤ ‖revMap W T z‖ + ‖revMap W T z - z‖ := by
        have := norm_sub_le (revMap W T z) (revMap W T z - z)
        simpa using this
      exact lt_of_lt_of_le (by linarith) (le_max_right _ _)
    · exact lt_of_lt_of_le (not_le.1 hzR) (le_max_left _ _)
  · rw [Measure.map_apply hm hHm, Measure.restrict_apply (hm hHm)]
    have e : revMap W T ⁻¹' H ∩ H = H := by
      refine inter_eq_right.2 fun z hz => ?_
      exact TwoPoint.im_revMap_pos hW hz hT
    rw [e, hinf]

/-- **A.s. the wedge area is finite on half-discs and infinite on `ℍ`** (Theorem 1.8 variables),
from `LocLen.pStarAreaAll_of_yMergeOffTip` at time `0`. -/
theorem ae_areaAll_wedgeA {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) : ∀ᵐ ω ∂P, E6.AreaAll γ (Y ω) := by
  have hA := LocLen.pStarAreaAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B
    (isPStarSample_of_setting hS)
  rw [Real.sqrt_sq hS.1.le] at hA
  filter_upwards [hA, wedgeRegSampleStmt_holds γ P Y hS.1 hS.2.1 hS.2.2.2.1, hS.2.2.1.cont,
    hS.2.2.1.eval_zero_ae_eq_zero] with ω hω hreg hc h0
  have e := E6.qAreaMeasure_unzippedField_zero (γ := γ)
    (drive_continuous (κ := γ ^ 2) hc) (drive_zero (κ := γ ^ 2) h0) hreg
  obtain ⟨h1, h2⟩ := hω 0 le_rfl
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

end R18
end QuantumZipper

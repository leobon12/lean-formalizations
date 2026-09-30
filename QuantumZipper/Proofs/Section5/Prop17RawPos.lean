import QuantumZipper.Proofs.Section5.Prop17RawLaw
import QuantumZipper.Proofs.Wire2b

/-!
# Proposition 1.7, node D5-e: scale positivity, and the final reduction to circle coordinates

* `scaleParam_translate_pos`: if `x` is good, its area measure is finite on every half-disc
  `B(0,R) ∩ ℍ` and gives `B(0,1) ∩ ℍ` unit mass, then every real translate `translate x y` has a
  positive scale parameter (`B(y,b) ∩ ℍ ↓ ∅` as `b ↓ 0`, and `B(y,|y|+1) ⊇ B(0,1)`);
* `prop17ScalePosStmt_holds`: `Prop17ScalePosStmt γ L` for `0 < γ < 2` (R23 (a)/(b) via `Wire2b`);
* `prop17RefShiftStmt_of_coordsStmt`: for `0 < γ < 2`,
  `Prop17RefCoordsShiftStmt γ L → Prop17RefShiftStmt γ L` with no other hypothesis: the raw test
  pairings are settled, and D5-e is reduced to the stationarity of the law of `coordsFull` of the
  reference wedge (Sheffield, arXiv:1012.4797, Prop. 1.7, proof pp. 25–26).

Own elementary arguments (continuity of measure from above; AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

theorem preimage_sub_ball_inter_H (y b : ℝ) :
    (fun z : ℂ => z - (y : ℂ)) ⁻¹' (Metric.ball 0 b ∩ H) = Metric.ball (y : ℂ) b ∩ H := by
  ext z
  simp [Metric.mem_ball, dist_eq_norm, H]

/-- **Positive scale parameter of real translates.** -/
theorem scaleParam_translate_pos {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x)
    (hfin : ∀ R : ℝ, qAreaMeasure γ x (Metric.ball 0 R ∩ H) < ⊤)
    (h1 : qAreaMeasure γ x (Metric.ball 0 1 ∩ H) = 1) (y : ℝ) :
    0 < scaleParam γ (translate x y) := by
  set μ := qAreaMeasure γ x with hμ
  have hmeasB : ∀ (c : ℂ) (b : ℝ), MeasurableSet (Metric.ball c b ∩ H) := fun c b =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  have hT : ∀ b : ℝ, qAreaMeasure γ (translate x y) (Metric.ball 0 b ∩ H) =
      μ (Metric.ball (y : ℂ) b ∩ H) := by
    intro b
    rw [GoodTransforms.qAreaMeasure_translate hx y,
      Measure.map_apply (show Measurable fun z : ℂ => z - (y : ℂ) by fun_prop) (hmeasB 0 b), preimage_sub_ball_inter_H]
  -- a small half-disc around `y` has mass `< 1`
  set s : ℕ → Set ℂ := fun n => Metric.ball (y : ℂ) (1 / ((n : ℝ) + 1)) ∩ H with hs
  have hanti : Antitone s := by
    intro m n hmn
    refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    gcongr
  have hfin1 : μ (s 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hfin (|y| + 1)).ne (measure_mono ?_)
    refine inter_subset_inter_left _ fun z hz => ?_
    have hz' : ‖z - (y : ℂ)‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h2 := norm_sub_norm_le z (y : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hempty : (⋂ n, s n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    rw [mem_iInter] at hz
    have hz0 : z ∈ H := (hz 0).2
    have hzy : dist z (y : ℂ) = 0 := by
      refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) dist_nonneg
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      have := (hz n).1
      rw [Metric.mem_ball] at this
      linarith
    rw [dist_eq_zero] at hzy
    have him : z.im = 0 := by rw [hzy]; simp
    exact absurd hz0 (by simp [H, him])
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hmeasB _ _).nullMeasurableSet)
    hanti ⟨0, hfin1⟩
  rw [hempty, measure_empty] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).exists
  have hmem : |y| + 1 ∈
      {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ (translate x y) (Metric.ball 0 a ∩ H)} := by
    refine ⟨by positivity, ?_⟩
    rw [hT, ← h1]
    refine measure_mono (inter_subset_inter_left _ fun z hz => ?_)
    rw [Metric.mem_ball, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_eq_norm]
    have h2 := norm_sub_le z (y : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    linarith
  have hlb : ∀ a ∈ {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ (translate x y) (Metric.ball 0 a ∩ H)},
      1 / ((n : ℝ) + 1) ≤ a := by
    rintro a ⟨-, h1a⟩
    by_contra hlt
    push Not at hlt
    rw [hT] at h1a
    have hle : μ (Metric.ball (y : ℂ) a ∩ H) ≤ μ (s n) :=
      measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hlt.le))
    exact absurd (h1a.trans hle) (not_le.2 hn)
  unfold scaleParam
  exact lt_of_lt_of_le (by positivity) (le_csInf ⟨_, hmem⟩ hlb)

/-- **Scale positivity**, both halves, for `0 < γ < 2`. -/
theorem prop17ScalePosStmt_holds {γ L : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    Prop17ScalePosStmt γ L := by
  intro Ω' _ P' X A hP hX hA hI
  have hα := gamma_lt_Qc' hγ hγ2
  filter_upwards [Wire2.ae_hasAreaProfile_wedgeField hγ hγ2 hα hX hA hI,
    LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP hX hA hI] with ω hp hg
  obtain ⟨ha, -⟩ := CanonicalGood.scaleParam_spec hp
  obtain ⟨hgc, hu⟩ := CanonicalGood.canonical_spec hγ hg hp
  refine ⟨ha, scaleParam_translate_pos hgc (fun R => ?_) hu _⟩
  rw [canonical, GoodTransforms.qAreaMeasure_rescale hg hγ ha,
    Measure.map_apply (show Measurable fun z : ℂ => z / ((scaleParam γ
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) : ℝ) : ℂ) by fun_prop)
      (AreaProfile.measurableSet_ball_inter_H R),
    GoodTransforms.preimage_div_ball_inter_H ha]
  exact lt_top_iff_ne_top.2 (hp.1 (R * scaleParam γ
    (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))))

/-- **D5-e reduced to circle coordinates.** For `0 < γ < 2`, the stationarity of the reference
wedge law (`Prop17RefShiftStmt`, the only open input of `Wire3.theorem1_7_of_refShiftStmt`)
follows from the stationarity of the law of its full circle coordinates. -/
theorem prop17RefShiftStmt_of_coordsStmt {γ L : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hcoords : Prop17RefCoordsShiftStmt γ L) : Prop17RefShiftStmt γ L := by
  have hα := gamma_lt_Qc' hγ hγ2
  have hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα
  have hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα
  exact prop17RefShiftStmt_of_coords hγ hγ2
    (WedgeMeasND.wedgeDataAEMeasStmt_of_inputs hfin hinf hγ hγ2)
    (WedgeMeasND.wedgeGoodStmt_of_inputs hfin hinf hγ hγ2) (prop17ScalePosStmt_holds hγ hγ2)
    hcoords

end Raw
end FieldLaw
end S5
end QuantumZipper

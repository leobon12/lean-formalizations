import QuantumZipper.Proofs.Section5.Prop17PalmZoomKer
import QuantumZipper.Proofs.LQG.AreaProfile
import QuantumZipper.Proofs.LQG.FiniteArea
import QuantumZipper.Proofs.Section5.Prop17RawPos

/-!
# Proposition 1.7, node D4⁺ (Palm zoom): positive zoom scales of the free field (PALMZOOM)

Part of node 1: a.s. every zoom `zoomField γ C (N_ϖ X) x` has a positive scale parameter. The
deterministic step (`scaleParam_zoomField_pos`: finite area of half-discs and infinite total area
give `0 < scaleParam`, uniformly in `C, x`) is an own elementary argument, the same as
`scaleParam_translate_pos`; the stochastic inputs are `FinArea.ae_qAreaMeasure_ball_lt_top` and
`AreaProfile.ae_qAreaMeasure_H_eq_top` (infinite total area).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open PalmNorm PalmShift

/-- **Positive zoom scales (deterministic).** -/
theorem scaleParam_zoomField_pos {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} (hy : IsLQGGood γ y)
    (hfin : ∀ a : ℝ, qAreaMeasure γ y (Metric.ball 0 a ∩ H) < ⊤)
    (hinf : qAreaMeasure γ y H = ⊤) (C x : ℝ) : 0 < scaleParam γ (zoomField γ C y x) := by
  set μ := qAreaMeasure γ y with hμ
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp C) with hk
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeasB : ∀ (c : ℂ) (b : ℝ), MeasurableSet (Metric.ball c b ∩ H) := fun c b =>
    (Metric.isOpen_ball.inter isOpen_H).measurableSet
  have hT : ∀ b : ℝ, qAreaMeasure γ (zoomField γ C y x) (Metric.ball 0 b ∩ H) =
      k * μ (Metric.ball (x : ℂ) b ∩ H) := by
    intro b
    rw [zoomField, GoodSample.qAreaMeasure_addConst (hy.translate x),
      GoodTransforms.qAreaMeasure_translate hy x, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (show Measurable fun z : ℂ => z - (x : ℂ) by fun_prop) (hmeasB 0 b),
      preimage_sub_ball_inter_H, mul_div_cancel₀ _ hγ.ne']
  -- a ball with area `≥ 1`
  have hup : Tendsto (fun n : ℕ => μ (Metric.ball (x : ℂ) n ∩ H)) atTop (𝓝 (μ H)) := by
    have hU : (⋃ n : ℕ, Metric.ball (x : ℂ) n ∩ H) = H := by
      rw [← iUnion_inter, Metric.iUnion_ball_nat, univ_inter]
    have hmono : Monotone fun n : ℕ => Metric.ball (x : ℂ) n ∩ H := fun m n hmn =>
      inter_subset_inter_left _ (Metric.ball_subset_ball (by exact_mod_cast hmn))
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rwa [hU] at this
  rw [hinf] at hup
  obtain ⟨N, hN⟩ := (hup.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top :
    ENNReal.ofReal (Real.exp (-C)) < ⊤))).exists
  have hkinv : k * ENNReal.ofReal (Real.exp (-C)) = 1 := by
    rw [hk, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel,
      Real.exp_zero, ENNReal.ofReal_one]
  have hmem : ((N : ℝ) + 1) ∈
      {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ (zoomField γ C y x) (Metric.ball 0 a ∩ H)} := by
    refine ⟨by positivity, ?_⟩
    rw [hT, ← hkinv]
    have hsub : Metric.ball (x : ℂ) N ∩ H ⊆ Metric.ball (x : ℂ) ((N : ℝ) + 1) ∩ H :=
      inter_subset_inter_left _ (Metric.ball_subset_ball (by linarith))
    have := hN.le.trans (measure_mono (μ := μ) hsub)
    gcongr
  -- a small half-disc has area `< e^{-C}`
  set s : ℕ → Set ℂ := fun n => Metric.ball (x : ℂ) (1 / ((n : ℝ) + 1)) ∩ H with hs
  have hanti : Antitone s := by
    intro m n hmn
    refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
    gcongr
  have hfin1 : μ (s 0) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (hfin (|x| + 1)).ne (measure_mono ?_)
    refine inter_subset_inter_left _ fun z hz => ?_
    have hz' : ‖z - (x : ℂ)‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have h2 := norm_sub_norm_le z (x : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hempty : (⋂ n, s n) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun z hz => ?_
    rw [mem_iInter] at hz
    have hz0 : z ∈ H := (hz 0).2
    have hzy : dist z (x : ℂ) = 0 := by
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
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 (Real.exp_pos (-C)) :
    (0 : ℝ≥0∞) < ENNReal.ofReal (Real.exp (-C))))).exists
  have hlb : ∀ a ∈ {a : ℝ | 0 < a ∧ 1 ≤ qAreaMeasure γ (zoomField γ C y x) (Metric.ball 0 a ∩ H)},
      1 / ((n : ℝ) + 1) ≤ a := by
    rintro a ⟨-, h1a⟩
    by_contra hlt
    push Not at hlt
    rw [hT] at h1a
    have hle : μ (Metric.ball (x : ℂ) a ∩ H) ≤ μ (s n) :=
      measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball hlt.le))
    have : k * μ (s n) < 1 := by
      rw [← hkinv]
      exact ENNReal.mul_lt_mul_right hk0 hkt hn
    have h2 : k * μ (Metric.ball (x : ℂ) a ∩ H) ≤ k * μ (s n) := by gcongr
    exact absurd (h1a.trans h2) (not_le.2 this)
  unfold scaleParam
  exact lt_of_lt_of_le (by positivity) (le_csInf ⟨_, hmem⟩ hlb)

/-- **Positive zoom scales of the normalized free field (a.s.).** -/
theorem ae_scaleParam_zoomField_freeFieldN_pos {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (ϖ : Measure ℂ) :
    ∀ᵐ ω ∂P, ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C (freeFieldN ϖ X ω) x) := by
  filter_upwards [AreaOffsets.ae_isLQGGood hX hγ hγ2, FinArea.ae_qAreaMeasure_ball_lt_top hX hγ hγ2,
    AreaProfile.ae_qAreaMeasure_H_eq_top hX hγ hγ2] with ω hg hfin hinf C x
  rw [freeFieldN_eq_addConst]
  set c := -(X ω ϖ)
  have hA : qAreaMeasure γ (addConst (X ω) c) =
      ENNReal.ofReal (Real.exp (γ * c)) • qAreaMeasure γ (X ω) :=
    GoodSample.qAreaMeasure_addConst hg c
  have hc0 : ENNReal.ofReal (Real.exp (γ * c)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  refine scaleParam_zoomField_pos hγ (hg.addConst c) (fun a => ?_) ?_ C x
  · rw [hA, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hfin a)
  · rw [hA, Measure.smul_apply, smul_eq_mul, hinf, ENNReal.mul_top hc0]

/-- **Node 1, remaining part (hypothesis):** a modification of `N_ϖ X` with measurable zoom
coordinates. -/
def Prop17FreeModStmt (γ : ℝ) (ϖ : Measure ℂ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    ∃ h : Ω → FieldSample, (∀ᵐ ω ∂P, h ω = freeFieldN ϖ X ω) ∧
      ∀ C : ℝ, Measurable (zoomCoords γ C h)

theorem prop17FreeRegRestStmt_of_mod {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ}
    (hmod : Prop17FreeModStmt γ ϖ) : Prop17FreeRegRestStmt γ ϖ := fun Ω _ P X hP hX =>
  ⟨ae_scaleParam_zoomField_freeFieldN_pos hX hγ hγ2 ϖ, hmod Ω _ P X hP hX⟩

end Raw
end FieldLaw
end S5
end QuantumZipper

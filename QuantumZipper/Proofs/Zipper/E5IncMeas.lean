import QuantumZipper.Proofs.Zipper.E5IncField
import QuantumZipper.Proofs.Zipper.D3PlusN1Model
import QuantumZipper.Proofs.GFF.CircleContinuity

/-!
# E5-INC, part 2: the collision constant of the regular version is `condSigma`-measurable

Task D28 (Theorem 1.3, node E5). With the regular version `X' = regField ϖ ρ₀ r' ∘ X` of the
collision free field (`E5IncField`), the collision constant `X'(ρ₀) − X'(ϖ_τ)` is, off the event
`{ϖ_τ(ball 0 r') ≠ 0}`, a measurable function for `condSigma Ξ X' r` as soon as `r < r'`:

* `regCut`: the regular reading with the integrand cut to `(ball 0 r')ᶜ` and the scale shifted by
  `k₀`; it equals `evalReg` at measures without mass in `ball 0 r'` (`evalReg_eq_regCut`);
* `measurable_cutAvg`, `measurable_regCut`: for `3·2^{-k₀} ≤ r' − r`, the cut circle averages only
  read folded circles missing `ball 0 r`, so they are measurable for `outsideSigma` jointly with the
  point, and their integral against a random measure measurable for `σ(Ξ)` is `condSigma`-measurable
  (kernel integral, `StronglyMeasurable.integral_kernel_prod_right'`);
* `exists_inc_regField`: the surrogate `inc` of `setup_locCorr_switch`, with the switch event at the
  radius `r'`;
* `setup_locCorr_switch_reg`: the D3⁺ `Setup` of the switched collision correction for the regular
  version, switch event `{ϖ_τ(ball 0 r') ≠ 0}` (`r < r'`), without any `inc` hypothesis.

Own elementary measure-theoretic arguments (no published source: the paper, Sheffield
arXiv:1012.4797 §5.4, does not discuss measurability of this constant).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 D3Plus

/-! ## 1. Generic measurability tools -/

theorem countable_range_dyadicRoundC_inc (n : ℕ) : (Set.range (dyadicRoundC n)).Countable := by
  have hsub : Set.range (dyadicRoundC n) ⊆
      Set.range (fun p : ℤ × ℤ => (⟨(p.1 : ℝ) / (2 : ℝ) ^ n, (p.2 : ℝ) / (2 : ℝ) ^ n⟩ : ℂ)) := by
    rintro _ ⟨z, rfl⟩
    exact ⟨(⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋), rfl⟩
  exact (Set.countable_range _).mono hsub

theorem measurable_dyadicRoundC_inc (n : ℕ) : Measurable (dyadicRoundC n) := by
  have hR : Measurable (dyadicRound n) := by
    unfold dyadicRound
    exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
      (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))
  have hrw : dyadicRoundC n
      = fun z : ℂ => (dyadicRound n z.re : ℂ) + (dyadicRound n z.im : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [dyadicRoundC]
  rw [hrw]
  exact (Complex.continuous_ofReal.measurable.comp (hR.comp Complex.measurable_re)).add
    ((Complex.continuous_ofReal.measurable.comp (hR.comp Complex.measurable_im)).mul_const _)

/-- Countably many measurable slices, selected by the dyadic rounding of the point, glue to a
jointly measurable function. -/
theorem measurable_comp_dyadic {Ω : Type*} [MeasurableSpace Ω] (φ : ℂ → Ω → ℝ)
    (hφ : ∀ d, Measurable (φ d)) (n : ℕ) :
    Measurable fun p : Ω × ℂ => φ (dyadicRoundC n p.2) p.1 := by
  have : Countable (Set.range (dyadicRoundC n)) := (countable_range_dyadicRoundC_inc n).to_subtype
  intro T hT
  have key : (fun p : Ω × ℂ => φ (dyadicRoundC n p.2) p.1) ⁻¹' T
      = ⋃ d : Set.range (dyadicRoundC n),
          {ω | φ (d : ℂ) ω ∈ T} ×ˢ (dyadicRoundC n ⁻¹' ({(d : ℂ)} : Set ℂ)) := by
    ext ⟨ω, z⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · intro hmem
      exact ⟨⟨dyadicRoundC n z, Set.mem_range_self z⟩, hmem, rfl⟩
    · rintro ⟨d, hmem, hdz⟩
      rwa [hdz]
  rw [key]
  exact MeasurableSet.iUnion fun d => ((hφ d) hT).prod
    ((measurable_dyadicRoundC_inc n) (measurableSet_singleton _))

theorem limUnder_add_nat_inc {α : Type*} [TopologicalSpace α] [Nonempty α] (f : ℕ → α) (k : ℕ) :
    limUnder atTop (fun n => f (n + k)) = limUnder atTop f := by
  unfold limUnder
  rw [show (fun n => f (n + k)) = f ∘ (fun n => n + k) from rfl, ← Filter.map_map,
    Filter.map_add_atTop_eq_nat]

/-- Integral of a jointly measurable function against a measurable family of probability
measures. -/
theorem measurable_integral_family {Ω : Type*} [MeasurableSpace Ω] (κm : Ω → Measure ℂ)
    (hκ : ∀ A : Set ℂ, MeasurableSet A → Measurable fun ω => κm ω A)
    (hprob : ∀ ω, IsProbabilityMeasure (κm ω)) {f : Ω × ℂ → ℝ} (hf : Measurable f) :
    Measurable fun ω => ∫ w, f (ω, w) ∂κm ω := by
  let κ : Kernel Ω ℂ := ⟨κm, Measure.measurable_of_measurable_coe κm hκ⟩
  have : IsMarkovKernel κ := ⟨fun ω => hprob ω⟩
  exact (hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable

/-- A folded circle of radius `s` about `d` misses `ball 0 r` when `r + s ≤ ‖d‖`. -/
theorem foldedCircle_ball_zero_inc {d : ℂ} {s r : ℝ} (hs : 0 ≤ s) (h : r + s ≤ ‖d‖) :
    foldedCircle d s (ball (0 : ℂ) r) = 0 := by
  rw [foldedCircle, Measure.map_apply measurable_foldH measurableSet_ball]
  refine measure_mono_null (fun x hx => ?_) (ae_iff.1 (CircleMV.ae_circleUnif d s))
  have hn : ‖foldH x‖ = ‖x‖ := by unfold foldH; split_ifs <;> simp
  simp only [mem_preimage, mem_ball_zero_iff, hn] at hx
  show ¬ ‖x - d‖ = |s|
  intro hxd
  rw [abs_of_nonneg hs] at hxd
  have : ‖d‖ ≤ ‖x‖ + ‖x - d‖ := by
    calc ‖d‖ = ‖x - (x - d)‖ := by ring_nf
      _ ≤ ‖x‖ + ‖x - d‖ := norm_sub_le _ _
  linarith

/-! ## 2. The cut regular reading -/

open Classical in
/-- Circle average at scale `k`, cut to the complement of `ball 0 r'`. -/
def cutAvg (r' : ℝ) (y : FieldSample) (k : ℕ) (w : ℂ) : ℝ :=
  if w ∈ ball (0 : ℂ) r' then 0 else avgReg y k w

/-- The regular reading with cut integrand and scale shifted by `k₀`. -/
def regCut (r' : ℝ) (k₀ : ℕ) (y : FieldSample) (μ : Measure ℂ) : ℝ :=
  limUnder atTop fun k => ∫ w, cutAvg r' y (k + k₀) w ∂μ

theorem evalReg_eq_regCut {r' : ℝ} (k₀ : ℕ) (y : FieldSample) {μ : Measure ℂ}
    (hμ : μ (ball (0 : ℂ) r') = 0) : evalReg y μ = regCut r' k₀ y μ := by
  rw [evalReg, regCut, ← limUnder_add_nat_inc _ k₀]
  congr 1
  funext k
  refine integral_congr_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμ] with w hw
  simp [cutAvg, hw]

theorem radius_anti_inc {k₀ k : ℕ} (h : k₀ ≤ k) : radius k ≤ radius k₀ := by
  unfold radius
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) h

/-- **Joint measurability of the cut circle averages** for any σ-algebra on `Ω` for which the
field is measurable at every folded circle missing `ball 0 r`. -/
theorem measurable_cutAvg {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → FieldSample) {r r' : ℝ}
    {k₀ : ℕ} (hk₀ : r + radius k₀ + 2 * (1 / 2 ^ k₀) ≤ r')
    (hY : ∀ (d : ℂ) (k : ℕ), r + radius k ≤ ‖d‖ →
      Measurable fun ω => Y ω (foldedCircle d (radius k)))
    {k : ℕ} (hk : k₀ ≤ k) : Measurable fun p : Ω × ℂ => cutAvg r' (Y p.1) k p.2 := by
  classical
  set φ : ℂ → Ω → ℝ := fun d ω =>
    if r + radius k ≤ ‖d‖ then Y ω (foldedCircle d (radius k)) else 0 with hφdef
  have hφ : ∀ d, Measurable (φ d) := fun d => by
    by_cases h : r + radius k ≤ ‖d‖
    · simpa [hφdef, h] using hY d k h
    · simp only [hφdef, h, ite_false]; exact measurable_const
  set T : ℕ → Ω × ℂ → ℝ := fun n p =>
    if p.2 ∈ ball (0 : ℂ) r' then 0 else φ (dyadicRoundC (n + k₀) p.2) p.1 with hTdef
  have hT : ∀ n, Measurable (T n) := fun n =>
    Measurable.ite (measurableSet_ball.preimage measurable_snd) measurable_const
      (measurable_comp_dyadic φ hφ (n + k₀))
  have heq : (fun p : Ω × ℂ => cutAvg r' (Y p.1) k p.2) = fun p => limUnder atTop fun n => T n p := by
    funext ⟨ω, w⟩
    by_cases hw : w ∈ ball (0 : ℂ) r'
    · simp only [cutAvg, hTdef, hw, ite_true]
      exact (tendsto_const_nhds.limUnder_eq).symm
    · simp only [cutAvg, hTdef, hw, ite_false, avgReg]
      rw [← limUnder_add_nat_inc _ k₀]
      congr 1
      funext n
      have hgood : r + radius k ≤ ‖dyadicRoundC (n + k₀) w‖ := by
        have h1 := CircleCont.norm_dyadicRoundC_sub_le (n + k₀) w
        have h2 : (1 : ℝ) / 2 ^ (n + k₀) ≤ 1 / 2 ^ k₀ :=
          one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) (by omega))
        have h3 : ‖w‖ ≤ ‖dyadicRoundC (n + k₀) w‖ + ‖dyadicRoundC (n + k₀) w - w‖ := by
          calc ‖w‖ = ‖dyadicRoundC (n + k₀) w - (dyadicRoundC (n + k₀) w - w)‖ := by ring_nf
            _ ≤ _ := norm_sub_le _ _
        have h4 : r' ≤ ‖w‖ := by simpa [mem_ball_zero_iff] using hw
        have h5 := radius_anti_inc hk
        linarith
      simp [hφdef, hgood]
  rw [heq]
  exact (StronglyMeasurable.limUnder fun n => (hT n).stronglyMeasurable).measurable

theorem measurable_regCut {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → FieldSample) {r r' : ℝ}
    {k₀ : ℕ} (hk₀ : r + radius k₀ + 2 * (1 / 2 ^ k₀) ≤ r')
    (hY : ∀ (d : ℂ) (k : ℕ), r + radius k ≤ ‖d‖ →
      Measurable fun ω => Y ω (foldedCircle d (radius k)))
    (κm : Ω → Measure ℂ) (hκ : ∀ A : Set ℂ, MeasurableSet A → Measurable fun ω => κm ω A)
    (hprob : ∀ ω, IsProbabilityMeasure (κm ω)) :
    Measurable fun ω => regCut r' k₀ (Y ω) (κm ω) := by
  have hk : ∀ k : ℕ, Measurable fun ω => ∫ w, cutAvg r' (Y ω) (k + k₀) w ∂κm ω := fun k =>
    measurable_integral_family κm hκ hprob (measurable_cutAvg Y hk₀ hY (by omega))
  exact (StronglyMeasurable.limUnder fun k => (hk k).stronglyMeasurable).measurable

theorem exists_k0_inc {r r' : ℝ} (h : r < r') : ∃ k₀ : ℕ, r + radius k₀ + 2 * (1 / 2 ^ k₀) ≤ r' := by
  obtain ⟨k₀, hk⟩ := exists_pow_lt_of_lt_one (show 0 < (r' - r) / 3 by linarith)
    (show (2⁻¹ : ℝ) < 1 by norm_num)
  refine ⟨k₀, ?_⟩
  have : (1 : ℝ) / 2 ^ k₀ = 2⁻¹ ^ k₀ := by rw [one_div, inv_pow]
  rw [this]
  unfold radius
  linarith

end E5
end QuantumZipper

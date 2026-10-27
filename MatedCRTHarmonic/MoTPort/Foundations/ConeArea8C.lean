/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.ConeArea8B
import Mathlib

/-!
# Cone area, part 23: the cone mass bounds; `IsQuantumCone` is self-guarding

**`coneMassBounds`**: `ConeArea7.ConeMassBounds γ W` for `0 < γ < 2`, `W > 0`; hence
**`coneScalePos`**, **`coneRefNonDirac`** and **`isQuantumCone_iff_unguarded'`** (the guard-free
characterization of `IsQuantumCone`, DMS Def. 4.10: the law identity alone).

Proof of the big-ball half (positive probability is enough). Off the origin the cone field is
`X + g`, `g(z) = Q s + A_s − R(|z|)`, `s = −log|z|` (ConeArea3B), so its area measure is
`e^{γ g} μ_X` (ConeArea3B `isVagueLimitOn_coneField_punctured` and uniqueness of vague limits).
On the support of the bump `bumpW` (ConeArea8B) we have `s ∈ [1/5, 3/2]`, hence if `A ≥ M` on
`[1/5, 3/2]`:

  `μ_cone(B(0,1)) ≥ ∫ bumpW dμ_cone ≥ e^{γM} massLat(X)`,

where `massLat γ x` is `massW` of the cone field with zero radial profile (the lateral part of `x`;
a measurable functional of `x` alone, a.s. positive by `ae_massW_pos`). The events
`{massLat(X) > 1/(n+1)}` (for some `n`, positive probability) and `{A ≥ log(n+1)/γ on
[1/5, 3/2] ∩ ℚ}` (positive probability: `B_{1/5}` is Gaussian and independent of the later
increments, mathlib `IsPreBrownianReal.indepFun_shift`) are independent (`X ⫫ A`), so their
intersection has positive probability, and on it some ball has cone mass `≥ 1`. The small-ball
half is `ae_exists_ball_lt_one` (ConeArea8).

Own argument (no published proof of this soft fact was found; DMS Def. 4.10 uses the unit-mass
circle-average embedding without comment). It needs only positive probability, so the
dyadic-scaling route of QZ `WedgeInfTotal` (a.s. infinite total mass) is not needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea8

open QuantumZipper LQGMetric ConeArea4

/-! ## Brownian motion above a level on a compact time interval -/

section BM

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- a Brownian motion stays above any level `M` at the rational times of `[a, b]`, `a > 0`, with
positive probability (Markov property at `a`: `B_a ∼ N(0,a)` is independent of the increments
after `a`, which are bounded on `[a,b]` with positive probability) -/
theorem measure_rat_ge_ne_zero (hB : IsBrownianReal B P) {a b : ℚ} (ha : 0 < a) (M : ℝ) :
    P {ω | ∀ q : ℚ, a ≤ q → q ≤ b → M ≤ B (q : ℝ).toNNReal ω} ≠ 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set a' : ℝ≥0 := (a : ℝ).toNNReal with ha'
  set L : ℝ≥0 := ((b - a : ℚ) : ℝ).toNNReal with hL
  set Wp : Ω → ℝ≥0 → ℝ := fun ω t => B (a' + t) ω - B a' ω with hWp
  have hind : IndepFun Wp (fun ω => B a' ω) P :=
    (hB.indepFun_shift a').comp measurable_id
      (measurable_pi_apply (⟨a', mem_Iic.2 le_rfl⟩ : Iic a'))
  set S : ℕ → Set (ℝ≥0 → ℝ) := fun K => ⋂ q : ℚ, ⋂ (_ : (q : ℝ).toNNReal ≤ L),
    {f | |f (q : ℝ).toNNReal| ≤ K} with hS
  have hSm : ∀ K, MeasurableSet (S K) := fun K => MeasurableSet.iInter fun q =>
    MeasurableSet.iInter fun _ =>
      measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply _)) measurable_const
  obtain ⟨K, hK⟩ : ∃ K : ℕ, P (Wp ⁻¹' S K) ≠ 0 := by
    by_contra h
    push Not at h
    have hU : P (⋃ K : ℕ, Wp ⁻¹' S K) = 0 := measure_iUnion_null h
    have hae : ∀ᵐ ω ∂P, ω ∈ ⋃ K : ℕ, Wp ⁻¹' S K := by
      filter_upwards [hB.cont] with ω hω
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := L)).exists_bound_of_continuousOn
        (f := fun t => B (a' + t) ω - B a' ω)
        ((hω.comp (continuous_const.add continuous_id)).sub continuous_const).continuousOn
      refine mem_iUnion.2 ⟨⌈C⌉₊, ?_⟩
      simp only [hS, mem_preimage, mem_iInter, mem_ofPred_eq]
      intro q hq
      have := hC _ ⟨bot_le, hq⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans (Nat.le_ceil C)
    have h1 : P univ = 0 := measure_mono_null (fun ω _ => by
        by_cases h' : ω ∈ ⋃ K : ℕ, Wp ⁻¹' S K
        · exact Or.inr h'
        · exact Or.inl h') (measure_union_null (ae_iff.1 hae) hU)
    simp at h1
  have hG : P ((fun ω => B a' ω) ⁻¹' Ici (M + K)) ≠ 0 := by
    have hlaw := hB.hasLaw_eval a'
    rw [← Measure.map_apply_of_aemeasurable hlaw.aemeasurable measurableSet_Ici, hlaw.map_eq]
    intro h0
    have ha0 : a' ≠ 0 := by
      rw [ha', Ne, Real.toNNReal_eq_zero, not_le]; exact_mod_cast ha
    have := gaussianReal_absolutelyContinuous' 0 ha0 h0
    rw [Real.volume_Ici] at this
    exact ENNReal.top_ne_zero this
  have hprod : P (Wp ⁻¹' S K ∩ (fun ω => B a' ω) ⁻¹' Ici (M + K)) ≠ 0 := by
    rw [hind.measure_inter_preimage_eq_mul _ _ (hSm K) measurableSet_Ici]
    exact mul_ne_zero hK hG
  refine fun h0 => hprod (measure_mono_null ?_ h0)
  rintro ω ⟨h1, h2⟩ q hq1 hq2
  simp only [hS, mem_preimage, mem_iInter, mem_ofPred_eq] at h1
  simp only [mem_preimage, mem_Ici] at h2
  have hr := h1 (q - a) (Real.toNNReal_le_toNNReal (by exact_mod_cast (by linarith : q - a ≤ b - a)))
  have e : a' + ((q - a : ℚ) : ℝ).toNNReal = ((q : ℚ) : ℝ).toNNReal := by
    rw [ha', ← Real.toNNReal_add (by exact_mod_cast ha.le)
      (by exact_mod_cast (sub_nonneg.2 hq1))]
    congr 1; push_cast; ring
  simp only [hWp, e] at hr
  have := (abs_le.1 hr).1
  linarith

/-- the event `{A ≥ M at the rational times of [1/5, 3/2]}` for the radial path -/
def aboveSet (M : ℝ) : Set (ℝ → ℝ) :=
  {f | ∀ q : ℚ, (1 / 5 : ℝ) ≤ q → (q : ℝ) ≤ 3 / 2 → M ≤ f q}

lemma measurableSet_aboveSet (M : ℝ) : MeasurableSet (aboveSet M) := by
  have e : aboveSet M = ⋂ q : ℚ, ⋂ (_ : (1 / 5 : ℝ) ≤ q), ⋂ (_ : (q : ℝ) ≤ 3 / 2),
      {f : ℝ → ℝ | M ≤ f q} := by
    ext f; simp [aboveSet]
  rw [e]
  exact MeasurableSet.iInter fun q => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_pi_apply _)

/-- **the cone radial process stays above any level on `[1/5, 3/2]` with positive probability** -/
theorem measure_cone_above_ne_zero {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsConeProcess α Q A P)
    (M : ℝ) : P ((fun ω t => A t ω) ⁻¹' aboveSet M) ≠ 0 := by
  obtain ⟨B, B', hB, -, -, hAe⟩ := hA
  refine fun h0 => measure_rat_ge_ne_zero hB (a := 1 / 5) (b := 3 / 2) (by norm_num)
    (M + |α - Q| * (3 / 2)) (measure_mono_null ?_ h0)
  intro ω hω q hq1 hq2
  have hq0 : (0 : ℝ) ≤ q := le_trans (by norm_num) hq1
  have := hω q (by rw [← Rat.cast_le (K := ℝ)]; push_cast; linarith)
    (by rw [← Rat.cast_le (K := ℝ)]; push_cast; linarith)
  show M ≤ A q ω
  rw [hAe, Cone.conePath_of_nonneg α Q _ _ hq0]
  have h3 : -|α - Q| * (3 / 2) ≤ (α - Q) * q := by
    nlinarith [neg_abs_le (α - Q), abs_nonneg (α - Q)]
  linarith

end BM

/-! ## Geometry of the bump support -/

lemma norm_bounds_of_mem {z : ℂ} (hz : z ∈ closedBall c₀ (1 / 40)) :
    2 / 5 ≤ ‖z‖ ∧ ‖z‖ ≤ 4 / 5 := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := Complex.abs_re_le_norm (z - c₀)
  have hc : ‖c₀‖ ≤ 3 / 4 := by
    have h2 : ‖c₀‖ ^ 2 = 1 / 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [c₀]; norm_num
    nlinarith [norm_nonneg c₀]
  constructor
  · have h1 := Complex.re_le_norm z
    have h2 : (z - c₀).re = z.re - 1 / 2 := by simp [c₀]
    rw [h2] at hre
    have := (abs_le.1 (hre.trans hz)).1
    linarith
  · have := norm_le_norm_add_norm_sub' z c₀
    linarith [norm_sub_rev z c₀]

lemma log_bounds_of_mem {z : ℂ} (hz : z ∈ closedBall c₀ (1 / 40)) :
    (1 / 5 : ℝ) ≤ -Real.log ‖z‖ ∧ -Real.log ‖z‖ ≤ 3 / 2 := by
  obtain ⟨h1, h2⟩ := norm_bounds_of_mem hz
  have hpos : 0 < ‖z‖ := by linarith
  constructor
  · have := Real.log_le_sub_one_of_pos hpos
    linarith
  · have hinv : ‖z‖⁻¹ ≤ 5 / 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]; linarith
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at this
    linarith

lemma zero_notMem_closedBall : (0 : ℂ) ∉ closedBall c₀ (1 / 40) := fun h => by
  have := (norm_bounds_of_mem h).1
  norm_num at this

lemma closedBall_subset_punctured : closedBall c₀ (1 / 40) ⊆ univ \ {0} :=
  fun _ hz => ⟨mem_univ _, fun h => zero_notMem_closedBall (by rw [mem_singleton_iff] at h; rwa [← h])⟩

/-! ## The lateral functional and the comparison -/

/-- the lateral bump mass: `massW` of the cone field with zero radial profile (the lateral part
`x − x_{|·|}(0)` of `x`); a measurable functional of `x` -/
def massLat (γ : ℝ) (x : Field) : ℝ≥0∞ :=
  massW γ (coneField (lateralPartC x) (fun _ => 0) 0)

lemma measurable_massLat (γ : ℝ) : Measurable (massLat γ) :=
  (measurable_massW γ).comp (ConeMeas2.measurable_coneField (X := fun x : Field => x)
    measurable_id (A := fun _ _ => (0 : ℝ)) measurable_const 0)

lemma measurable_expDens {a : ℝ → ℝ} (ha : Measurable a) (γ Q : ℝ) {R : ℝ → ℝ}
    (hR : Measurable R) :
    Measurable fun z => ENNReal.ofReal (Real.exp (γ * ConeArea3.coneShift a Q R z)) :=
  ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((ConeArea3.measurable_coneShift ha Q hR).const_mul γ))

/-! ## The mass bounds -/

end ConeArea8
end MatedCRTHarmonic.MoTPort

import LQGMetric.Prob.Median
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Medians (blueprint Lemma `lem:medians`)

A real number `m` is a median of a real random variable `X` if `P[X ≤ m] ≥ 1/2` and
`P[X ≥ m] ≥ 1/2` (blueprint Definition `def:median`); in Lean this is
`LQGMetric.IsMedian (P.map X) m`. The set of medians of a law `μ` is the interval
`[lowerMedianLaw μ, upperMedianLaw μ]`, and `X` has a unique median `q` iff this interval is `{q}`.

Blueprint Lemma `lem:medians`:

* (a) if `m` is a median of `X` and `φ : ℝ → ℝ` is non-decreasing, then `φ m` is a median of `φ(X)`
  (`IsMedian.map_comp_monotone`); if `X > 0` a.s., every median of `X` is positive
  (`IsMedian.pos_of_ae_pos`) and `log m` is a median of `log X` (`IsMedian.map_log`);
* (b) if `X_i → X` in probability along a filter, `X` has a unique median `q`, and `m_i` is a median
  of `X_i`, then `m_i → q` (`tendsto_of_isMedian_of_tendstoInMeasure`; the variant
  `tendsto_lowerMedianLaw_of_tendstoInMeasure` states uniqueness as
  `lowerMedianLaw = upperMedianLaw`).

The random variables are a.e.-measurable (in this Mathlib, the push-forward of a measure under a
map that is not a.e.-measurable is a Dirac mass, so medians carry no information about it).

The proof of (b) follows the blueprint: if `m_i ≥ q + ε` then
`1/2 ≤ P[X_i ≥ q + ε] ≤ P[X ≥ q + ε/2] + P[|X_i - X| ≥ ε/2]`, and `P[X ≥ q + ε/2] < 1/2` because
`q` is the upper median; symmetrically, `m_i ≤ q - ε` is impossible for `i` late in the filter
because `q` is the lower median.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

open LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## (a) Monotone images -/

/-- **Blueprint Lemma `lem:medians` (a).** If `m` is a median of `X` and `φ` is non-decreasing,
then `φ m` is a median of `φ(X)`. -/
theorem IsMedian.map_comp_monotone {X : Ω → ℝ} (hX : AEMeasurable X P) {m : ℝ}
    (hm : IsMedian (P.map X) m) {φ : ℝ → ℝ} (hφ : Monotone φ) :
    IsMedian (P.map fun ω => φ (X ω)) (φ m) := by
  have hmap : (P.map X).map φ = P.map fun ω => φ (X ω) :=
    AEMeasurable.map_map_of_aemeasurable hφ.measurable.aemeasurable hX
  rw [← hmap]
  exact IsMedian.map_monotone hφ hφ.measurable hm

/-- **Blueprint Lemma `lem:medians` (a).** If `X > 0` a.s., every median of `X` is positive. -/
theorem IsMedian.pos_of_ae_pos {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    {m : ℝ} (hm : IsMedian (P.map X) m) : 0 < m := by
  by_contra hm0
  push Not at hm0
  have h1 : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | X ω ≤ m} := ((isMedian_map_iff hX).1 hm).1
  have h0 : P {ω | X ω ≤ m} = 0 := by
    refine measure_mono_null (fun ω (hω : X ω ≤ m) => ?_) (ae_iff.1 hpos)
    show ¬ 0 < X ω
    exact not_lt.2 (hω.trans hm0)
  rw [h0] at h1
  exact absurd h1 (not_le.2 LQGMetric.inv_two_pos')

/-- **Blueprint Lemma `lem:medians` (a), logarithm.** If `X > 0` a.s. and `m` is a median of `X`,
then `log m` is a median of `log X`. -/
theorem IsMedian.map_log {X : Ω → ℝ} (hX : AEMeasurable X P) (hpos : ∀ᵐ ω ∂P, 0 < X ω)
    {m : ℝ} (hm : IsMedian (P.map X) m) :
    IsMedian (P.map fun ω => Real.log (X ω)) (Real.log m) := by
  have hm0 : 0 < m := IsMedian.pos_of_ae_pos hX hpos hm
  have hlog : AEMeasurable (fun ω => Real.log (X ω)) P := Real.measurable_log.comp_aemeasurable hX
  obtain ⟨h1, h2⟩ := (isMedian_map_iff hX).1 hm
  refine (isMedian_map_iff hlog).2 ⟨h1.trans (measure_mono_ae ?_), h2.trans (measure_mono ?_)⟩
  · filter_upwards [hpos] with ω hω hle
    exact Real.log_le_log hω hle
  · intro ω (hω : m ≤ X ω)
    exact Real.log_le_log hm0 hω

/-! ## Unique medians -/

/-- A law with a median `q` that is its only median has lower and upper median `q`. -/
theorem lowerMedianLaw_eq_and_upperMedianLaw_eq_of_unique {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {q : ℝ} (huniq : ∀ m, IsMedian μ m → m = q) :
    lowerMedianLaw μ = q ∧ upperMedianLaw μ = q :=
  ⟨huniq _ isMedian_lowerMedianLaw,
    huniq _ (isQuantile_upperQuantile inv_two_pos' inv_two_lt_one')⟩

/-! ## (b) Convergence of medians -/

section limit

variable [IsProbabilityMeasure P] {ι : Type*} {L : Filter ι}

/-- **Blueprint Lemma `lem:medians` (b).** Let `X_i → Z` in probability along a filter `L`, where
`Z` has the unique median `q`, and let `m_i` be a median of `X_i` (for `i` late in `L`). Then
`m_i → q`. -/
theorem tendsto_of_isMedian_of_tendstoInMeasure {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hconv : TendstoInMeasure P X L Z) (hX : ∀ᶠ i in L, AEMeasurable (X i) P)
    (hZ : AEMeasurable Z P) {q : ℝ} (huniq : ∀ m, IsMedian (P.map Z) m → m = q)
    {m : ι → ℝ} (hm : ∀ᶠ i in L, IsMedian (P.map (X i)) (m i)) : Tendsto m L (𝓝 q) := by
  obtain ⟨hlow, hup⟩ := lowerMedianLaw_eq_and_upperMedianLaw_eq_of_unique huniq
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  -- the two tails of the limit law are below `1/2`
  set a : ℝ≥0∞ := P {ω | Z ω ≤ q - ε / 2} with ha_def
  set b : ℝ≥0∞ := P {ω | q + ε / 2 ≤ Z ω} with hb_def
  have ha : a < 2⁻¹ := by
    have h := measure_Iic_lt_of_lt_lowerQuantile (μ := P.map Z) inv_two_pos' inv_two_lt_one'
      (show q - ε / 2 < lowerMedianLaw (P.map Z) by rw [hlow]; linarith)
    rwa [Measure.map_apply_of_aemeasurable hZ measurableSet_Iic] at h
  have hb : b < 2⁻¹ := by
    have h := measure_Ici_lt_of_upperQuantile_lt (μ := P.map Z) inv_two_pos' inv_two_lt_one'
      (show upperMedianLaw (P.map Z) < q + ε / 2 by rw [hup]; linarith)
    rwa [Measure.map_apply_of_aemeasurable hZ measurableSet_Ici, ENNReal.one_sub_inv_two] at h
  have hc : 0 < min (2⁻¹ - a) (2⁻¹ - b) := lt_min (tsub_pos_of_lt ha) (tsub_pos_of_lt hb)
  have hsmall : ∀ᶠ i in L,
      P {ω | ε / 2 ≤ dist (X i ω) (Z ω)} < min (2⁻¹ - a) (2⁻¹ - b) :=
    (tendstoInMeasure_iff_dist.1 hconv (ε / 2) hε2).eventually (gt_mem_nhds hc)
  filter_upwards [hX, hm, hsmall] with i hXi hmi hi
  obtain ⟨h1, h2⟩ := (isMedian_map_iff hXi).1 hmi
  have ha_ne : a ≠ ⊤ := (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  have hb_ne : b ≠ ⊤ := (prob_le_one.trans_lt ENNReal.one_lt_top).ne
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- `m i ≤ q - ε` would force `1/2 ≤ a + P[|X_i - Z| ≥ ε/2] < 1/2`
    by_contra hle
    push Not at hle
    have hsub : {ω | X i ω ≤ m i} ⊆
        {ω | Z ω ≤ q - ε / 2} ∪ {ω | ε / 2 ≤ dist (X i ω) (Z ω)} := by
      intro ω (hω : X i ω ≤ m i)
      by_cases hZω : Z ω ≤ q - ε / 2
      · exact Or.inl hZω
      · refine Or.inr ?_
        push Not at hZω
        show ε / 2 ≤ dist (X i ω) (Z ω)
        rw [Real.dist_eq, abs_sub_comm]
        refine le_trans ?_ (le_abs_self _)
        linarith
    have hlt : a + P {ω | ε / 2 ≤ dist (X i ω) (Z ω)} < 2⁻¹ := by
      calc a + P {ω | ε / 2 ≤ dist (X i ω) (Z ω)} < a + (2⁻¹ - a) :=
            ENNReal.add_lt_add_left ha_ne (hi.trans_le (min_le_left _ _))
        _ = 2⁻¹ := add_tsub_cancel_of_le ha.le
    exact absurd (h1.trans ((measure_mono hsub).trans (measure_union_le _ _)))
      (not_le.2 hlt)
  · -- `m i ≥ q + ε` would force `1/2 ≤ b + P[|X_i - Z| ≥ ε/2] < 1/2`
    by_contra hle
    push Not at hle
    have hsub : {ω | m i ≤ X i ω} ⊆
        {ω | q + ε / 2 ≤ Z ω} ∪ {ω | ε / 2 ≤ dist (X i ω) (Z ω)} := by
      intro ω (hω : m i ≤ X i ω)
      by_cases hZω : q + ε / 2 ≤ Z ω
      · exact Or.inl hZω
      · refine Or.inr ?_
        push Not at hZω
        show ε / 2 ≤ dist (X i ω) (Z ω)
        rw [Real.dist_eq]
        refine le_trans ?_ (le_abs_self _)
        linarith
    have hlt : b + P {ω | ε / 2 ≤ dist (X i ω) (Z ω)} < 2⁻¹ := by
      calc b + P {ω | ε / 2 ≤ dist (X i ω) (Z ω)} < b + (2⁻¹ - b) :=
            ENNReal.add_lt_add_left hb_ne (hi.trans_le (min_le_right _ _))
        _ = 2⁻¹ := add_tsub_cancel_of_le hb.le
    exact absurd (h2.trans ((measure_mono hsub).trans (measure_union_le _ _)))
      (not_le.2 hlt)

/-- **Blueprint Lemma `lem:medians` (b)**, with uniqueness of the median of the limit stated as
`lowerMedianLaw = upperMedianLaw`: medians of `X_i` converge to the median of `Z`. -/
theorem tendsto_lowerMedianLaw_of_tendstoInMeasure {X : ι → Ω → ℝ} {Z : Ω → ℝ}
    (hconv : TendstoInMeasure P X L Z) (hX : ∀ᶠ i in L, AEMeasurable (X i) P)
    (hZ : AEMeasurable Z P) (hU : lowerMedianLaw (P.map Z) = upperMedianLaw (P.map Z))
    {m : ι → ℝ} (hm : ∀ᶠ i in L, IsMedian (P.map (X i)) (m i)) :
    Tendsto m L (𝓝 (lowerMedianLaw (P.map Z))) := by
  refine tendsto_of_isMedian_of_tendstoInMeasure hconv hX hZ (fun m' hm' => ?_) hm
  exact (isQuantile_iff_eq_lowerQuantile inv_two_pos' inv_two_lt_one' hU).1 hm'

end limit

end GaussianLQG

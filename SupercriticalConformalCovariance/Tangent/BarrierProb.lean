import SupercriticalConformalCovariance.Tangent.BarrierWeyl
import SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.AX3
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeoCompactB
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge
import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import LQGMetric.Papers.GM.S1.Subseq

/-!
# Lemma 3.2 for a whole-plane GFF, with a margin

Paper l. 182–188 (Lemma 3.2). SupercriticalLQGUniqueness's `geoCompactB_prob` (uniform in the reference
radius `b`) gives, for a normalized whole-plane GFF, `around(A_{2b,4b}) < across(A_{2^J b,2^{J+1} b})`
with probability `≥ 1 − η` for `J` large. `exists_margin_prob` adds a margin `θ < 1`
(`around < θ · across`) by continuity of measure, for any whole-plane GFF (the event is invariant
under additive constants), which makes it stable under the vanishing Weyl corrections of the
transformed fields.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Tangent

open SupercriticalLQGUniqueness (LSCMetric EuclideanAnnulus aroundDist acrossDist IsStrongLQGMetric)
open SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36 (baseAnn innerScale outerScale
  GeoCompactEventB geoCompactB_prob)
open LQGMetric (DistC IsGFFPlusCont IsWholePlaneGFF)

/-- `around` scales with the metric. -/
theorem aroundDist_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ⊤)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (A : EuclideanAnnulus) :
    aroundDist E A = c * aroundDist D A := by
  unfold aroundDist
  simp only [SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.isCurve_iff_of_dist_scale
    D E c hc0 hcTop hscale,
    SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.len_eq_mul_of_dist_scale D E c hscale,
    ENNReal.mul_iInf_of_ne hc0 hcTop]

/-- `across` scales with the metric. -/
theorem acrossDist_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ⊤)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (B : EuclideanAnnulus) :
    acrossDist E B = c * acrossDist D B := by
  unfold acrossDist
  simp only [hscale, ENNReal.mul_iInf_of_ne hc0 hcTop]

/-- Strict inequalities between `around` and `θ · across` are invariant under scaling. -/
theorem around_lt_iff_of_dist_scale (D E : LSCMetric) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hcTop : c ≠ ⊤)
    (hscale : ∀ x y : ℂ, E (x, y) = c * D (x, y)) (A B : EuclideanAnnulus) (θ : ℝ≥0∞) :
    aroundDist E A < θ * acrossDist E B ↔ aroundDist D A < θ * acrossDist D B := by
  rw [aroundDist_of_dist_scale D E c hc0 hcTop hscale, acrossDist_of_dist_scale D E c hc0 hcTop hscale,
    mul_left_comm θ c]
  exact ENNReal.mul_lt_mul_iff_right hc0 hcTop

/-- The inner annulus `A_{2b,4b}(0)`. -/
def annA (b : Set.Ioi (0 : ℝ)) : EuclideanAnnulus := baseAnn.dilate (innerScale b) (innerScale b).2

/-- The outer annulus `A_{2^J b, 2^{J+1} b}(0)`. -/
def annB (J : ℕ) (b : Set.Ioi (0 : ℝ)) : EuclideanAnnulus :=
  baseAnn.dilate (outerScale J b) (outerScale J b).2

theorem annA_center (b : Set.Ioi (0 : ℝ)) : (annA b).center = 0 := by
  change ((2 * (b : ℝ)) • (0 : ℂ)) = 0
  exact smul_zero _

theorem annB_center (J : ℕ) (b : Set.Ioi (0 : ℝ)) : (annB J b).center = 0 := by
  change ((2 ^ J * (b : ℝ)) • (0 : ℂ)) = 0
  exact smul_zero _

theorem annA_innerRadius (b : Set.Ioi (0 : ℝ)) : (annA b).innerRadius = 2 * b := by
  change 2 * (b : ℝ) * 1 = 2 * b; ring

theorem annA_outerRadius (b : Set.Ioi (0 : ℝ)) : (annA b).outerRadius = 4 * b := by
  change 2 * (b : ℝ) * 2 = 4 * b; ring

theorem annB_innerRadius (J : ℕ) (b : Set.Ioi (0 : ℝ)) : (annB J b).innerRadius = 2 ^ J * b := by
  change 2 ^ J * (b : ℝ) * 1 = 2 ^ J * b; ring

theorem annB_outerRadius (J : ℕ) (b : Set.Ioi (0 : ℝ)) :
    (annB J b).outerRadius = 2 ^ (J + 1) * b := by
  change 2 ^ J * (b : ℝ) * 2 = 2 ^ (J + 1) * b; ring

/-- **Lemma 3.2's barrier with a margin, for any whole-plane GFF.** For `δ > 0` and `b > 0` there
are `J ≥ 2` and `θ ∈ (0, 1)` such that, for every whole-plane GFF `g`,
`around(A_{2b,4b}) < θ · across(A_{2^J b, 2^{J+1} b})` fails with probability at most `δ`. The
choice of `θ` depends on the law only through the law of a whole-plane GFF, i.e. not at all, but
here it is chosen for a given `g`. -/
theorem exists_margin_prob {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} (hQ : 0 < Q) {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {g : Ω → DistC} (hg : IsWholePlaneGFF g P) (b : Set.Ioi (0 : ℝ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ J : ℕ, 2 ≤ J ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      P {ω | marginEvent D (annA b) (annB J b) θ (g ω) = false} ≤ ENNReal.ofReal δ := by
  have hweak := SupercriticalLQGUniqueness.B2.Strong.isWeakLQGMetric_of_isStrongLQGMetric hD
  obtain ⟨J, hJ, hprob⟩ := geoCompactB_prob ξ Q hQ D hweak (δ / 2) (by positivity)
  refine ⟨J, hJ, ?_⟩
  -- the normalized field
  set c : Ω → ℝ := fun ω => -LQGMetric.circleAvg (g ω) 1 0 with hc
  set g' : Ω → DistC := fun ω => LQGMetric.addConst (g ω) (c ω) with hg'
  have hg'n := SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.normalize_new hg
  have hfail := hprob P g' hg'n b
  have hgc : IsGFFPlusCont g P := LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hg
  have hscale := SupercriticalLQGUniqueness.Uniqueness.Positivity.Witnesses.ae_addConst_eq_mul P g hgc
    ξ Q D hweak c
  -- the strict event for `g`, a.s. equal to the one for `g'`
  set E0 : Set Ω := {ω | aroundDist (D (g ω)) (annA b) < acrossDist (D (g ω)) (annB J b)} with hE0
  have hE0c : P E0ᶜ ≤ ENNReal.ofReal (δ / 2) := by
    refine le_trans (measure_mono_ae ?_) hfail
    filter_upwards [hscale] with ω hω hnot
    change ¬ GeoCompactEventB (D (g' ω)) J b
    intro hG
    apply hnot
    have hk0 : ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
    have h1 := (around_lt_iff_of_dist_scale (D (g ω)) (D (g' ω)) _ hk0 ENNReal.ofReal_ne_top
      (fun x y => hω (x, y)) (annA b) (annB J b) 1)
    simp only [one_mul] at h1
    exact h1.1 hG
  -- the margin events increase to (at least) the strict event
  set θk : ℕ → ℝ := fun k => 1 - 1 / ((k : ℝ) + 2) with hθk
  have hθk0 : ∀ k, 0 < θk k := fun k => by
    simp only [hθk]
    have : 1 / ((k : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith
  have hθk1 : ∀ k, θk k < 1 := fun k => by
    simp only [hθk]
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    linarith
  have hθkmono : Monotone θk := by
    intro i j hij
    simp only [hθk]
    have : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 2)
    linarith
  have hθklim : Tendsto θk atTop (𝓝 1) := by
    have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa [hθk] using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  set Ek : ℕ → Set Ω := fun k => {ω | marginEvent D (annA b) (annB J b) (θk k) (g ω) = true}
    with hEk
  have hEkm : ∀ k, MeasurableSet (Ek k) := fun k =>
    (measurable_marginEvent hD.1 _ _ _).comp hg.measurable (measurableSet_singleton true)
  have hEkmono : Monotone Ek := by
    intro i j hij ω hω
    simp only [hEk, mem_ofPred_eq, marginEvent_eq_true] at hω ⊢
    exact hω.trans_le (by gcongr; exact hθkmono hij)
  have hcover : E0 ⊆ ⋃ k, Ek k := by
    intro ω hω
    simp only [hE0, mem_ofPred_eq] at hω
    simp only [mem_iUnion, hEk, mem_ofPred_eq, marginEvent_eq_true]
    rcases eq_or_ne (acrossDist (D (g ω)) (annB J b)) ⊤ with htop | htop
    · refine ⟨0, ?_⟩
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (hθk0 0)).ne']
      exact hω.trans_le le_top
    · have ht : Tendsto (fun k => ENNReal.ofReal (θk k) * acrossDist (D (g ω)) (annB J b)) atTop
          (𝓝 (acrossDist (D (g ω)) (annB J b))) := by
        have := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal hθklim) (Or.inr htop)
        simpa using this
      exact (ht.eventually (lt_mem_nhds hω)).exists
  -- choose `k`
  have hsup : P (⋃ k, Ek k) = ⨆ k, P (Ek k) := hEkmono.measure_iUnion
  rcases le_or_gt 1 (ENNReal.ofReal δ) with hbig | hsmall
  · exact ⟨θk 0, hθk0 0, hθk1 0, (prob_le_one).trans hbig⟩
  have hlarge : 1 - ENNReal.ofReal δ < P (⋃ k, Ek k) := by
    have h1 : P E0 ≥ 1 - ENNReal.ofReal (δ / 2) := by
      have := prob_compl_eq_one_sub (μ := P) (s := E0) ?_
      · rw [this] at hE0c
        exact tsub_le_iff_tsub_le.1 hE0c
      · exact measurableSet_lt ((SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.measurable_aroundDist_fixed
          _).comp (hD.1.comp hg.measurable))
          ((SupercriticalLQGUniqueness.measurable_acrossDist _).comp (hD.1.comp hg.measurable))
    have h2 : 1 - ENNReal.ofReal δ < 1 - ENNReal.ofReal (δ / 2) :=
      ((ENNReal.cancel_of_ne ENNReal.one_ne_top).tsub_lt_tsub_iff_left_of_le
        (ENNReal.cancel_of_ne ENNReal.ofReal_ne_top) hsmall.le).2
        ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith))
    exact h2.trans_le (h1.le.trans (measure_mono hcover))
  rw [hsup] at hlarge
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hlarge
  refine ⟨θk k, hθk0 k, hθk1 k, ?_⟩
  have hc' : {ω | marginEvent D (annA b) (annB J b) (θk k) (g ω) = false} = (Ek k)ᶜ := by
    ext ω
    simp only [hEk, mem_compl_iff, mem_ofPred_eq, Bool.not_eq_true]
  rw [hc', prob_compl_eq_one_sub (hEkm k)]
  exact (tsub_le_iff_tsub_le.1 hk.le)

end SupercriticalConformalCovariance.Tangent

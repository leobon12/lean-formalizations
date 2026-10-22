import HigherDimLQGContinuity.Grid.Limit
import HigherDimLQGContinuity.Grid.Stochastic

/-! A jointly measurable continuous version on one positive parameter window. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- A deterministic parameter sequence converging to `ξ` has the canonical log profiles
converging in measure at every fixed spatial pair. -/
theorem gridProfile_eval_tendstoInMeasure {d : ℕ} (hd : 3 ≤ d)
    (hP : Prop37Shape d) {lo hi ξ : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    (hξ : ξ ∈ Icc lo hi) {t : ℕ → ℝ} (ht : ∀ k, t k ∈ Icc lo hi)
    (htend : Tendsto t atTop (𝓝 ξ))
    (D : DistRd d → ContMetric d) (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    (p : Rd d × Rd d) :
    TendstoInMeasure (normLGFLaw d)
      (fun k g => gridProfile d (t k) g p) atTop
      (fun g => logProfile (rho D g).1 p) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  let δ : ℝ := min (ε / 2) (1 / 16)
  have hδ : 0 < δ := lt_min (half_pos hε) (by norm_num)
  have hδ8 : δ < 1 / 8 := (min_le_right _ _).trans_lt (by norm_num)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  let R : ℝ := ‖p‖ + 1
  have hR : 1 ≤ R := by dsimp [R]; linarith [norm_nonneg p]
  have hpR : p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R := by
    constructor
    · rw [mem_closedBall, dist_zero_right]
      dsimp [R]
      linarith [norm_fst_le p]
    · rw [mem_closedBall, dist_zero_right]
      dsimp [R]
      linarith [norm_snd_le p]
  apply ENNReal.tendsto_atTop_zero.mpr
  intro b hb
  let η : ℝ := (min b 1).toReal
  have hb0 : 0 < min b (1 : ℝ≥0∞) := lt_min hb (by norm_num)
  have hbfin : min b (1 : ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)
  have hη : 0 < η := ENNReal.toReal_pos hb0.ne' hbfin
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (tendstoInMeasure_profile_of_tendsto hd hP hlo hlohi hhi hξ ht htend D hD
      hR hδ hδ8 η hη)
  refine ⟨N, fun k hk => ?_⟩
  have hincl : {g | ε ≤ dist (gridProfile d (t k) g p) (logProfile (rho D g).1 p)} ⊆
      {g | ENNReal.ofReal δ < supDistLU d R
        (gridProfile d (t k) g) (logProfile (rho D g).1)} := by
    intro g hg
    have he := endpt_edist_le_supDistLU (d := d) (R := R) hpR
      (F := gridProfile d (t k) g) (G := logProfile (rho D g).1)
    have hsmall : ENNReal.ofReal δ < edist
        (gridProfile d (t k) g p) (logProfile (rho D g).1 p) := by
      rw [edist_dist]
      exact (ENNReal.ofReal_lt_ofReal_iff (hε.trans_le hg)).2 (hδε.trans_le hg)
    exact hsmall.trans_le he
  calc
    normLGFLaw d {g | ε ≤ dist (gridProfile d (t k) g p)
      (logProfile (rho D g).1 p)} ≤
      normLGFLaw d {g | ENNReal.ofReal δ < supDistLU d R
        (gridProfile d (t k) g) (logProfile (rho D g).1)} := measure_mono hincl
    _ ≤ ENNReal.ofReal η := hN k hk
    _ = min b 1 := ENNReal.ofReal_toReal hbfin
    _ ≤ b := min_le_left _ _

/-- The compact-open limit is the logarithmic profile of every strong metric
at each deterministic parameter, almost surely. -/
theorem ae_limitProfile_eq_logProfile {d : ℕ} (hd : 3 ≤ d)
    (hP : Prop37Shape d) {lo hi ξ : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi)
    (hξ : ξ ∈ Icc lo hi)
    (D : DistRd d → ContMetric d) (hD : IsStrongExpMetric d ξ (distExp d ξ) D) :
    ∀ᵐ g ∂(normLGFLaw d),
      limitProfile d lo hi ξ g = logProfile (rho D g).1 := by
  classical
  choose m hm hnear using fun k : ℕ => exists_posNode_near hlohi hξ k
  let t : ℕ → ℝ := fun k => posNode lo hi k (m k)
  have ht (k : ℕ) : t k ∈ Icc lo hi := posNode_mem hlohi (hm k)
  have htend : Tendsto t atTop (𝓝 ξ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_)
      (tendsto_posWidth (lo := lo) (hi := hi))
    rw [Real.norm_eq_abs]
    exact hnear k
  have hsub : Ioc (0 : ℝ) hi ⊆ subcritSet d :=
    (gap24 (by omega : 2 ≤ d) ⟨hhi.1, hhi.2⟩).choose_spec.2.2.2.1
  have htS (k : ℕ) : t k ∈ subcritSet d :=
    hsub ⟨hlo.trans_le (ht k).1, (ht k).2⟩
  let q := TopologicalSpace.denseSeq (Rd d × Rd d)
  have hpoint (p : Rd d × Rd d) :
      ∀ᵐ g ∂(normLGFLaw d),
        limitProfile d lo hi ξ g p = logProfile (rho D g).1 p := by
    have hf (k : ℕ) : AEStronglyMeasurable
        (fun g : DistRd d => gridProfile d (t k) g p) (normLGFLaw d) :=
      (((continuous_eval_const p).measurable.comp
        (measurable_gridProfile hd (htS k))).aestronglyMeasurable)
    have hae : ∀ᵐ g ∂(normLGFLaw d),
        Tendsto (fun k : ℕ => gridProfile d (t k) g p) atTop
          (𝓝 (limitProfile d lo hi ξ g p)) := by
      filter_upwards [ae_posGood hd hP hlo hlohi hhi] with g hg
      have hpath : Tendsto (fun k : ℕ => limitProfile d lo hi (t k) g) atTop
          (𝓝 (limitProfile d lo hi ξ g)) :=
        ((continuous_limitProfile d hlohi hg).tendsto ξ).comp htend
      have heval : Tendsto (fun k : ℕ => limitProfile d lo hi (t k) g p) atTop
          (𝓝 (limitProfile d lo hi ξ g p)) :=
        (continuous_eval_const p).tendsto _ |>.comp hpath
      apply heval.congr'
      exact Eventually.of_forall fun k =>
        congrArg (fun F : C(Rd d × Rd d, ℝ) => F p)
          (limitProfile_node d hlohi hg k (hm k))
    let _ : IsProbabilityMeasure (normLGFLaw d) :=
      (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
    have h₁ := tendstoInMeasure_of_tendsto_ae hf hae
    have h₂ := gridProfile_eval_tendstoInMeasure hd hP hlo hlohi hhi hξ ht htend D hD p
    exact tendstoInMeasure_ae_unique h₁ h₂
  have hall : ∀ᵐ g ∂(normLGFLaw d), ∀ n : ℕ,
      limitProfile d lo hi ξ g (q n) = logProfile (rho D g).1 (q n) := by
    rw [ae_all_iff]
    intro n
    exact hpoint (q n)
  filter_upwards [hall] with g hg
  apply ContinuousMap.ext
  have heq := (TopologicalSpace.denseRange_denseSeq (Rd d × Rd d)).equalizer
    (limitProfile d lo hi ξ g).continuous (logProfile (rho D g).1).continuous
    (funext fun n => hg n)
  exact congrFun heq

theorem expProfile_nonneg {d : ℕ} (F : C(Rd d × Rd d, ℝ))
    (hF : 0 ≤ F) : 0 ≤ expProfile F := by
  intro p
  have hp : 0 ≤ F p := hF p
  have hexp : (1 : ℝ) ≤ Real.exp (F p) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
  change 0 ≤ Real.exp (F p) - 1
  linarith

/-- A continuous version on `[lo,hi]`, with the Euclidean fallback on the null
complement of the good event. -/
def windowVersion (d : ℕ) (lo hi : ℝ) (ξ : ℝ) (g : DistRd d) :
    C(Rd d × Rd d, ℝ) := by
  classical
  exact if g ∈ posGood d lo hi then expProfile (limitProfile d lo hi ξ g)
    else euclidDistC d

theorem measurable_windowVersion (d : ℕ) (hd : 3 ≤ d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) :
    Measurable (Function.uncurry (windowVersion d lo hi)) := by
  have hset : MeasurableSet {z : ℝ × DistRd d | z.2 ∈ posGood d lo hi} :=
    (measurable_posGood hd hlo hlohi hhi).preimage measurable_snd
  exact Measurable.ite hset
    (continuous_expProfile.measurable.comp
      (measurable_limitProfile d hd hlo hlohi hhi)) measurable_const

theorem windowVersion_spec {d : ℕ} (hd : 3 ≤ d) (hP : Prop37Shape d)
    {lo hi : ℝ} (hlo : 0 < lo) (hlohi : lo < hi)
    (hhi : 0 < hi ∧ Real.sqrt (2 * d) < distExp d hi) :
    ∃ (V : ℝ → DistRd d → C(Rd d × Rd d, ℝ)) (Good : Set (DistRd d)),
      MeasurableSet Good ∧ normLGFLaw d Goodᶜ = 0 ∧
      Measurable (Function.uncurry V) ∧
      (∀ g ∈ Good, ContinuousOn (fun ξ => V ξ g) (Icc lo hi) ∧
        ∀ ξ, 0 ≤ V ξ g) ∧
      ∀ ξ ∈ Icc lo hi, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ᵐ g ∂(normLGFLaw d), V ξ g = (rho D g).1 := by
  refine ⟨windowVersion d lo hi, posGood d lo hi,
    measurable_posGood hd hlo hlohi hhi,
    null_posGood_compl hd hP hlo hlohi hhi,
    measurable_windowVersion d hd hlo hlohi hhi, ?_, ?_⟩
  · intro g hg
    constructor
    · have hcont : Continuous (fun ξ => windowVersion d lo hi ξ g) := by
        have h := (continuous_expProfile (d := d)).comp
          (continuous_limitProfile d hlohi hg)
        simpa [windowVersion, hg, Function.comp_def] using h
      exact hcont.continuousOn
    · intro ξ
      simp only [windowVersion, hg, ite_true]
      exact expProfile_nonneg _ (limitProfile_nonneg d hlohi ξ g)
  · intro ξ hξ D hD
    filter_upwards [ae_posGood hd hP hlo hlohi hhi,
      ae_limitProfile_eq_logProfile hd hP hlo hlohi hhi hξ D hD] with g hg heq
    simp only [windowVersion, hg, ite_true, heq]
    exact expProfile_logProfile (rho D g).1 (fun p => ContMetric.nonneg (rho D g) p.1 p.2)

end HigherDimLQGContinuity

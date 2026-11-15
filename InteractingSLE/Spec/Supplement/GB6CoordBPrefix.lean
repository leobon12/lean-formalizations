/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBCurve
import InteractingSLE.Spec.Sec7.Lemma71EPrefix
import InteractingSLE.Spec.Sec7.PocketTraversalMeas

/-!
# Measurable drivers for driven curves that can visit the real boundary

This adapts `Lemma71EPrefix`'s capacity and rational-prefix arguments to
`PocketTraversal.IsDrivenCurve`. The arguments use continuity and local
Loewner drivers, and do not use simplicity or positive-time membership in `H`.
The driver reconstruction itself is reused from `PocketTraversalMeas`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.GB6.CoordB

open Sec7.Lemma71C Sec7.PocketTraversal Restart
open Sec7.Lemma71E (prefixEvent nonempty_dyadicSquare image_Icc_real_eq)

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ}

/-- **The capacity clock of a random driven curve is measurable.** -/
theorem measurable_capClock (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t) {u : ℝ}
    (hu : 0 ≤ u) : Measurable fun ω => capClock (γ ω) u := by
  set Γ : Ω → ℝ≥0 → ℂ := fun ω s => γ ω s with hΓ
  have hc : ∀ ω, Continuous (Γ ω) := fun ω =>
    (hγ ω).continuousOn.comp_continuous NNReal.continuous_coe fun s => s.2
  have hmeas := measurable_hcapHit_image hc (fun t => hm t t.2) u.toNNReal
  have heq : (fun ω => capClock (γ ω) u) =
      fun ω => (WholeField.hcapHit (Γ ω '' Icc 0 u.toNNReal)).toReal / 2 := by
    funext ω
    have h0 : (Γ ω 0).im ≤ 0 := by
      show (γ ω ((0 : ℝ≥0) : ℝ)).im ≤ 0
      rw [NNReal.coe_zero, (hγ ω).zero, Complex.zero_im]
    rw [hcapHit_image_eq (hc ω).continuousOn h0, capClock, image_Icc_real_eq hu]
    have hnn : 0 ≤ ConformalImage.hcapSet (fillH (Γ ω '' Icc 0 u.toNNReal)) := by
      have := (hγ ω).capClock_nonneg hu
      rw [capClock, image_Icc_real_eq hu] at this
      linarith
    rw [ENNReal.toReal_ofReal hnn]
  rw [heq]
  exact (ENNReal.measurable_toReal.comp hmeas).div_const _

omit [MeasurableSpace Ω] in
/-- `{r < T}` through the clock at integer times. -/
theorem setOf_lt_capLife_eq (hγ : ∀ ω, IsDrivenCurve (γ ω)) (r : ℝ≥0) :
    {ω | (r : ℝ≥0∞) < capLife (γ ω)} = ⋃ N : ℕ, {ω | (r : ℝ) < capClock (γ ω) N} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · intro h
    exact exists_lt_capClock_of_lt_capLife (by rwa [ENNReal.ofReal_coe_nnreal])
  · rintro ⟨N, hN⟩
    have h1 := (hγ ω).ofReal_capClock_lt (show (0 : ℝ) ≤ N by positivity)
    rw [← ENNReal.ofReal_coe_nnreal]
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hN.le) h1

/-- **The prefix meets a closed set, through rational times** (on `{r < T}`). -/
theorem prefix_nonempty_iff {g : ℝ → ℂ} (hg : IsDrivenCurve g) {r : ℝ≥0} (hr : (r : ℝ≥0∞) < capLife g)
    {Q : Set ℂ} (hQ : IsClosed Q) (hQne : Q.Nonempty) :
    (Q ∩ g '' Icc 0 (capInv g r)).Nonempty ↔
      ∀ j : ℕ, ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ capClock g q < r + 1 / ((j : ℝ) + 1) ∧
        infDist (g q) Q < 1 / ((j : ℝ) + 1) := by
  have hr' : ENNReal.ofReal (r : ℝ) < capLife g := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hu0, hur⟩ := hg.capInv_spec (NNReal.coe_nonneg r) hr'
  have hle_iff : ∀ t, 0 ≤ t → (t ≤ capInv g r ↔ capClock g t ≤ r) := fun t ht => by
    have := (hg.strictMonoOn_capClock.le_iff_le ht hu0).symm
    rwa [hur] at this
  constructor
  · rintro ⟨z, hzQ, t, ht, rfl⟩ j
    have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    -- continuity of the clock and of the curve at `t` within `[0, ∞)`
    have hcc := hg.continuousOn_capClock t ht.1
    have hgc := hg.continuousOn t ht.1
    have h1 : ∀ᶠ s in 𝓝[Ici 0] t, capClock g s < r + 1 / ((j : ℝ) + 1) := by
      have := (hle_iff t ht.1).1 ht.2
      exact hcc.eventually (gt_mem_nhds (by linarith))
    have h2 : ∀ᶠ s in 𝓝[Ici 0] t, dist (g s) (g t) < 1 / ((j : ℝ) + 1) :=
      hgc.eventually (ball_mem_nhds _ hj)
    obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhdsWithin_iff.1 (h1.and h2)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show t < t + δ by linarith)
    have hqI : (q : ℝ) ∈ ball t δ ∩ Ici 0 := by
      refine ⟨?_, le_of_lt (lt_of_le_of_lt ht.1 hq1)⟩
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    obtain ⟨hq3, hq4⟩ := hδs hqI
    refine ⟨q, hqI.2, hq3, lt_of_le_of_lt (infDist_le_dist_of_mem hzQ) hq4⟩
  · intro h
    choose q hq0 hqc hqd using h
    obtain ⟨N, hN⟩ := exists_lt_capClock_of_lt_capLife hr'
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt (show 0 < capClock g N - r by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    -- late rational times lie in `[0, N]`
    have hqN : ∀ j, j₀ ≤ j → ((q j : ℚ) : ℝ) ∈ Icc (0 : ℝ) N := by
      intro j hj
      refine ⟨hq0 j, ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      have h1 := hg.strictMonoOn_capClock hN0 (hq0 j) hlt
      have h2 : 1 / ((j : ℝ) + 1) ≤ 1 / ((j₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hj 1)
      linarith [hqc j]
    obtain ⟨t, ht, φ, hφ, hlim⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := N)).tendsto_subseq
      (x := fun i => ((q (i + j₀) : ℚ) : ℝ)) fun i => hqN _ (Nat.le_add_left _ _)
    have hφmono : Tendsto (fun i => φ i + j₀) atTop atTop :=
      tendsto_atTop_mono (fun i => Nat.le_add_right _ _) hφ.tendsto_atTop
    have hεlim : Tendsto (fun i => 1 / (((φ i + j₀ : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφmono
    have hlim' : Tendsto (fun i => ((q (φ i + j₀) : ℚ) : ℝ)) atTop (𝓝[Ici 0] t) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun i => hq0 _⟩
    -- the clock at `t` is at most `r`
    have hct : capClock g t ≤ r := by
      have hc := (hg.continuousOn_capClock t ht.1).tendsto.comp hlim'
      refine le_of_tendsto_of_tendsto' hc (by simpa using (tendsto_const_nhds (x := (r : ℝ))).add hεlim)
        fun i => (hqc _).le
    -- the curve at `t` lies in `Q`
    have hgt : g t ∈ Q := by
      have hd := ((continuous_infDist_pt Q).tendsto (g t)).comp ((hg.continuousOn t ht.1).tendsto.comp hlim')
      have h0 : infDist (g t) Q = 0 :=
        le_antisymm (le_of_tendsto_of_tendsto' hd hεlim fun i => (hqd _).le) infDist_nonneg
      exact (hQ.mem_iff_infDist_zero hQne).2 h0
    exact ⟨g t, hgt, t, ⟨ht.1, (hle_iff t ht.1).2 hct⟩, rfl⟩

/-- **The prefix events of a random driven curve are measurable.** -/
theorem measurableSet_prefixEvent (hγ : ∀ ω, IsDrivenCurve (γ ω)) (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t)
    (r : ℝ≥0) (n : ℕ) (k : ℤ × ℤ) : MeasurableSet (prefixEvent γ r n k) := by
  have heq : prefixEvent γ r n k = {ω | (r : ℝ≥0∞) < capLife (γ ω)} ∩
      ⋂ j : ℕ, ⋃ q : ℚ, {ω | 0 ≤ (q : ℝ) ∧ capClock (γ ω) q < r + 1 / ((j : ℝ) + 1) ∧
        infDist (γ ω q) (dyadicSquare n k) < 1 / ((j : ℝ) + 1)} := by
    ext ω
    simp only [prefixEvent, mem_inter_iff, mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · rintro ⟨hr, hne⟩
      exact ⟨hr, (prefix_nonempty_iff (hγ ω) hr (isClosed_dyadicSquare n k) (nonempty_dyadicSquare n k)).1 hne⟩
    · rintro ⟨hr, h⟩
      exact ⟨hr, (prefix_nonempty_iff (hγ ω) hr (isClosed_dyadicSquare n k) (nonempty_dyadicSquare n k)).2 h⟩
  rw [heq, setOf_lt_capLife_eq hγ]
  refine (MeasurableSet.iUnion fun N => measurableSet_lt measurable_const
    (measurable_capClock hγ hm (by positivity))).inter (MeasurableSet.iInter fun j => MeasurableSet.iUnion fun q => ?_)
  by_cases hq : 0 ≤ (q : ℝ)
  · simp only [hq, true_and]
    exact (measurableSet_lt (measurable_capClock hγ hm hq) measurable_const).inter
      (measurableSet_lt ((continuous_infDist_pt _).measurable.comp (hm q hq)) measurable_const)
  · simp [hq]


/-- The terminal capacity is a measurable function of the driven curve. -/
theorem measurable_capLife (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t) :
    Measurable fun ω => capLife (γ ω) :=
  Measurable.iSup fun n : ℕ => ENNReal.measurable_ofReal.comp
    (measurable_capClock hγ hm (by positivity : (0 : ℝ) ≤ n))

/-- Canonical driver evaluations are measurable on the live event. -/
theorem measurable_indicator_segDriver (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t) (t : ℝ≥0) :
    Measurable ({ω | (t : ℝ≥0∞) < capLife (γ ω)}.indicator
      fun ω => segDriver (γ ω) t) := by
  let E : Set Ω := {ω | (t : ℝ≥0∞) < capLife (γ ω)}
  have hE : MeasurableSet E := measurableSet_lt measurable_const (measurable_capLife hγ hm)
  apply Sec7.PocketTraversal.measurable_indicator_segDrv_of_isDrivenCurve
    t.coe_nonneg (fun ω _ => hγ ω) hE (fun ω hω => by
      change (t : ℝ≥0∞) < capLife (γ ω) at hω
      simpa only [ENNReal.ofReal_coe_nnreal] using hω)
  intro r hr0 hrt n k
  have he : E ∩ {ω | (dyadicSquare n k ∩ γ ω '' Icc 0 (capInv (γ ω) r)).Nonempty} =
      E ∩ prefixEvent γ r.toNNReal n k := by
    ext ω
    simp only [mem_inter_iff, prefixEvent, mem_ofPred_eq, Real.coe_toNNReal _ hr0]
    apply and_congr_right
    intro hω
    have hrL : (r.toNNReal : ℝ≥0∞) < capLife (γ ω) :=
      (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hrt)).trans_lt hω
    exact ⟨fun h => ⟨hrL, h⟩, fun h => h.2⟩
  rw [he]
  exact hE.inter (measurableSet_prefixEvent hγ hm _ n k)

open scoped Classical in
/-- The canonical driver, with value zero at and after its terminal capacity. -/
def drivenDriver (γ : Ω → ℝ → ℂ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if (t : ℝ≥0∞) < capLife (γ ω) then segDriver (γ ω) t else 0

theorem measurable_drivenDriver (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t) (t : ℝ≥0) :
    Measurable (drivenDriver γ t) := by
  have he : drivenDriver γ t = {ω | (t : ℝ≥0∞) < capLife (γ ω)}.indicator
      (fun ω => segDriver (γ ω) t) := by
    funext ω
    classical
    by_cases ht : (t : ℝ≥0∞) < capLife (γ ω)
    · rw [indicator_of_mem (show ω ∈ {ω | (t : ℝ≥0∞) < capLife (γ ω)} from ht)]
      simp only [drivenDriver, ht, ↓reduceIte]
    · rw [indicator_of_notMem (show ω ∉ {ω | (t : ℝ≥0∞) < capLife (γ ω)} from ht)]
      simp only [drivenDriver, ht, ↓reduceIte]
  rw [he]
  exact measurable_indicator_segDriver hγ hm t

omit [MeasurableSpace Ω] in
theorem drivenDriver_eq {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < capLife (γ ω)) :
    drivenDriver γ t ω = segDriver (γ ω) t := by
  simp only [drivenDriver, ht, ↓reduceIte]

omit [MeasurableSpace Ω] in
theorem continuousOn_drivenDriver (hγ : ∀ ω, IsDrivenCurve (γ ω)) (ω : Ω) :
    ContinuousOn (drivenDriver γ · ω) {t | (t : ℝ≥0∞) < capLife (γ ω)} :=
  (hγ ω).segDriver_spec.2.1.congr fun _ ht => drivenDriver_eq ht

omit [MeasurableSpace Ω] in
theorem drivenDriver_zero (hγ : ∀ ω, IsDrivenCurve (γ ω)) (ω : Ω) :
    drivenDriver γ 0 ω = 0 := by
  classical
  by_cases h : (0 : ℝ≥0∞) < capLife (γ ω)
  · rw [drivenDriver_eq (by simpa only [ENNReal.coe_zero] using h)]
    exact (hγ ω).segDriver_spec.1
  · simp only [drivenDriver, ENNReal.coe_zero, h, ↓reduceIte]

/-- Measurable local driver data ready for progressive regularization. -/
theorem adaptedBefore_drivenDriver (hγ : ∀ ω, IsDrivenCurve (γ ω))
    (hm : ∀ t, 0 ≤ t → Measurable fun ω => γ ω t) :
    AdaptedBefore (Filtration.const ℝ≥0 (inferInstance : MeasurableSpace Ω) le_rfl)
      (fun ω => capLife (γ ω)) (drivenDriver γ) := by
  intro t A hA
  exact (measurableSet_lt measurable_const (measurable_capLife hγ hm)).inter
    (measurable_drivenDriver hγ hm t hA)

omit [MeasurableSpace Ω] in
/-- The measurable driver retains the original curve's capacity-time hulls. -/
theorem fwdHull_drivenDriver (hγ : ∀ ω, IsDrivenCurve (γ ω)) (ω : Ω) {u : ℝ} (hu : 0 ≤ u) :
    QuantumZipper.fwdHull (fun r : ℝ => drivenDriver γ r.toNNReal ω) (capClock (γ ω) u) =
      fillH (γ ω '' Icc 0 u) := by
  have hc := hγ ω
  have hnn := hc.capClock_nonneg hu
  have hlt := hc.ofReal_capClock_lt hu
  obtain ⟨n, hn0, hn⟩ := hc.exists_pos_lt_capClock hnn hlt
  have he : QuantumZipper.fwdHull (fun r : ℝ => drivenDriver γ r.toNNReal ω) (capClock (γ ω) u) =
      QuantumZipper.fwdHull (fun r : ℝ => segDriver (γ ω) r.toNNReal) (capClock (γ ω) u) := by
    apply fwdHull_eq_of_eqOn hnn hn
    intro r hr
    apply drivenDriver_eq
    have hnr : ENNReal.ofReal r ≤ ENNReal.ofReal (capClock (γ ω) n) :=
      ENNReal.ofReal_le_ofReal hr.2
    exact hnr.trans_lt (hc.ofReal_capClock_lt hn0.le)
  rw [he, hc.fwdHull_segDriver hnn hlt, hc.capInv_eq hu]

end InteractingSLE.Supp8.GB6.CoordB

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Read
import InteractingSLE.Spec.Supplement.GB6SourceCContact
import InteractingSLE.Spec.Supplement.GW2ScheduleL25

/-!
# GW2's root cover: the protected root prefix read from the two stopped records

Packet PROVE-GW2-COVER. Lemma GW2's proof (`source/spec/p577-624.md` L1001–L1010): "Retain a bounded
original counterflow stopping history with interior current tip `p`. Its compact range is separated
from the unvisited original target `x` … Arbitrarily small available prefixes of that flow have an
interior tip and are separated from the retained counterflow … use the countable union of the
corresponding observed prefix events at times in `Q`"; for a boundary root `v`, "Their distance from
the retained counterflow is positive for all sufficiently small `v`".

The observed prefix event must be known at the root's stage start, i.e. be a Borel event of the
counterflow record at `s` and the root piece's record stopped at its root time `q₀`. This file gives
it with the landed total tip reader `RootA22.physicalTipRead`, at rational times only:

* `tipAt`, `SepRec`, `ProtRec`, `measurableSet_protRec`: the recorded event "the root piece is alive
  at `q₀` with an interior tip there, the counterflow tip is interior, and the two frozen recorded
  prefixes are uniformly separated in the inversion `z ↦ −1/z`, with the counterflow inside the disc
  of radius `1/x₀`";
* `sep_of_rat`: rational separation extends to all times (continuity and density);
* `lt_firstContactTime_of_sep`: a uniformly separated closed prefix ends strictly before the first
  inversion contact, for a trace continuous through its lifetime;
* `exists_small_sep`: a trace from `0` is uniformly separated on a positive initial interval from a
  bounded counterflow prefix when `x₀ · sup ‖α‖ ≤ 1/4`;
* `exists_mem_tip_mem_H`: a generating trace has interior tips at times of any dense set in every
  initial interval before its lifetime (Lemma 2.5: zero boundary occupation).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootCv

open Exist Staged StagedLaw Supp8.GB6

/-! ### The recorded event -/

/-- The recorded physical tip frozen at `v`. -/
def tipAt (v : ℝ≥0) (r : RecData) (t : ℝ≥0) : ℂ := RootA22.physicalTipRead (r, min t v)

theorem measurable_tipAt (v t : ℝ≥0) : Measurable fun r : RecData => tipAt v r t :=
  RootA22.measurable_physicalTipRead.comp (measurable_id.prodMk measurable_const)

/-- **Recorded uniform separation at level `n`** of the root prefix (record `p.2`, frozen at `q₀`,
from the root `x₀`) and the counterflow prefix (record `p.1`, frozen at `s`), at all rational
times: inversion separation `‖(x₀ + γ t) α u + 1‖ ≥ 1/(n+1)` and `x₀ ‖α u‖ ≤ 1 − 1/(n+1)`. -/
def SepRec (x₀ : ℝ) (q₀ s : ℝ≥0) (p : RecData × RecData) (n : ℕ) : Prop :=
  ∀ t u : ℚ, 1 / ((n : ℝ) + 1) ≤
      ‖((x₀ : ℂ) + tipAt q₀ p.2 (t : ℝ).toNNReal) * tipAt s p.1 (u : ℝ).toNNReal + 1‖ ∧
    x₀ * ‖tipAt s p.1 (u : ℝ).toNNReal‖ ≤ 1 - 1 / ((n : ℝ) + 1)

/-- **The recorded protected root prefix**: the root record is alive at its cutoff, the recorded
counterflow tip at `s` and the recorded physical root tip at `q₀` are interior, and the two recorded
prefixes are uniformly separated. -/
def ProtRec (x₀ : ℝ) (q₀ s : ℝ≥0) (p : RecData × RecData) : Prop :=
  p.2.2.2 = false ∧ RootA22.physicalTipRead (p.1, s) ∈ H ∧
    (x₀ : ℂ) + RootA22.physicalTipRead (p.2, q₀) ∈ H ∧ ∃ n : ℕ, SepRec x₀ q₀ s p n

theorem measurableSet_sepRec (x₀ : ℝ) (q₀ s : ℝ≥0) (n : ℕ) :
    MeasurableSet {p : RecData × RecData | SepRec x₀ q₀ s p n} := by
  simp only [SepRec, ofPred_forall]
  refine MeasurableSet.iInter fun t => MeasurableSet.iInter fun u => ?_
  have hγ : Measurable fun p : RecData × RecData => tipAt q₀ p.2 (t : ℝ).toNNReal :=
    (measurable_tipAt q₀ _).comp measurable_snd
  have hα : Measurable fun p : RecData × RecData => tipAt s p.1 (u : ℝ).toNNReal :=
    (measurable_tipAt s _).comp measurable_fst
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_le measurable_const
      (((measurable_const.add hγ).mul hα).add_const 1).norm
  · exact measurableSet_le (measurable_const.mul hα.norm) measurable_const

/-- The recorded protected prefix is a Borel event of the two records. -/
theorem measurableSet_protRec (x₀ : ℝ) (q₀ s : ℝ≥0) :
    MeasurableSet {p : RecData × RecData | ProtRec x₀ q₀ s p} := by
  have h1 : MeasurableSet {p : RecData × RecData | p.2.2.2 = false} :=
    (measurable_snd.comp (measurable_snd.comp measurable_snd)) (measurableSet_singleton false)
  have h2 : MeasurableSet {p : RecData × RecData | RootA22.physicalTipRead (p.1, s) ∈ H} :=
    (RootA22.measurable_physicalTipRead.comp (measurable_fst.prodMk measurable_const))
      QuantumZipper.isOpen_H.measurableSet
  have h3 : MeasurableSet {p : RecData × RecData | ∃ n : ℕ, SepRec x₀ q₀ s p n} := by
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion fun n => measurableSet_sepRec x₀ q₀ s n
  have h4 : MeasurableSet {p : RecData × RecData |
      (x₀ : ℂ) + RootA22.physicalTipRead (p.2, q₀) ∈ H} :=
    (measurable_const.add (RootA22.measurable_physicalTipRead.comp
      (measurable_snd.prodMk measurable_const))) QuantumZipper.isOpen_H.measurableSet
  exact h1.inter (h2.inter (h4.inter h3))

/-- The liveness flag of a record: alive at the cutoff exactly when the cutoff precedes the
lifetime. -/
theorem recOf_flag_eq_false_iff (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (recOf t e).2.2 = false ↔ t < e.2 := by
  change decide (e.2 ≤ t) = false ↔ t < e.2
  rw [decide_eq_false_iff_not, not_le]

/-! ### From rational times to all times -/

/-- **Rational separation extends to all times** for continuous frozen prefixes. -/
theorem sep_of_rat {f g : ℝ≥0 → ℂ} (hf : Continuous f) (hg : Continuous g) {x₀ δ : ℝ}
    (h : ∀ t u : ℚ, δ ≤ ‖((x₀ : ℂ) + f (t : ℝ).toNNReal) * g (u : ℝ).toNNReal + 1‖ ∧
      x₀ * ‖g (u : ℝ).toNNReal‖ ≤ 1 - δ) (t u : ℝ≥0) :
    δ ≤ ‖((x₀ : ℂ) + f t) * g u + 1‖ ∧ x₀ * ‖g u‖ ≤ 1 - δ := by
  have hd : DenseRange fun q : ℚ × ℚ => ((q.1 : ℝ).toNNReal, (q.2 : ℝ).toNNReal) :=
    denseRange_rat_toNNReal.prodMap denseRange_rat_toNNReal
  refine hd.induction_on (p := fun z : ℝ≥0 × ℝ≥0 =>
    δ ≤ ‖((x₀ : ℂ) + f z.1) * g z.2 + 1‖ ∧ x₀ * ‖g z.2‖ ≤ 1 - δ) (t, u) ?_ ?_
  · show IsClosed ({z : ℝ≥0 × ℝ≥0 | δ ≤ ‖((x₀ : ℂ) + f z.1) * g z.2 + 1‖} ∩
      {z : ℝ≥0 × ℝ≥0 | x₀ * ‖g z.2‖ ≤ 1 - δ})
    refine IsClosed.inter (isClosed_le continuous_const ?_) (isClosed_le ?_ continuous_const)
    · exact (((continuous_const.add (hf.comp continuous_fst)).mul (hg.comp continuous_snd)).add
        continuous_const).norm
    · exact continuous_const.mul (hg.comp continuous_snd).norm
  · intro q
    exact h q.1 q.2

/-! ### Strictly before the first contact -/

/-- **A uniformly separated closed prefix ends strictly before the first inversion contact.** If the
trace `γ` is continuous at its cutoff `q₀`, the counterflow prefix `α|[0,s]` is continuous, and
`‖(x₀ + γ t) α u + 1‖ ≥ δ > 0` on `[0, q₀] × [0, s]`, then `q₀` precedes the first time at which
`−1/(x₀ + γ t)` meets `α([0, s])`. -/
theorem lt_firstContactTime_of_sep {γ α : ℝ≥0 → ℂ} {x₀ δ : ℝ} {q₀ s : ℝ≥0}
    (hγ : ContinuousAt γ q₀) (hα : ContinuousOn α (Icc 0 s)) (hδ : 0 < δ)
    (hsep : ∀ t ≤ q₀, ∀ u ∈ Icc 0 s, δ ≤ ‖((x₀ : ℂ) + γ t) * α u + 1‖) :
    (q₀ : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x₀ : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
  obtain ⟨M, hM⟩ := ((isCompact_Icc.image_of_continuousOn hα).isBounded).subset_closedBall 0
  set M' : ℝ := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  have hαM : ∀ u ∈ Icc 0 s, ‖α u‖ ≤ M' := fun u hu => by
    have := hM ⟨u, hu, rfl⟩
    rw [mem_closedBall_zero_iff] at this
    linarith [le_abs_self M]
  have hε : 0 < δ / (2 * M') := by positivity
  obtain ⟨ε, hε0, hεγ⟩ := Metric.continuousAt_iff.1 hγ _ hε
  set η : ℝ≥0 := ⟨ε / 2, by positivity⟩ with hη
  have hη0 : (0 : ℝ) < η := by rw [hη]; change (0 : ℝ) < ε / 2; positivity
  -- no contact on `[0, q₀ + η]`
  have hno : ∀ t ≤ q₀ + η, ∀ u ∈ Icc 0 s, ((x₀ : ℂ) + γ t) * α u + 1 ≠ 0 := by
    intro t ht u hu
    rcases le_or_gt t q₀ with htq | htq
    · exact norm_pos_iff.1 (hδ.trans_le (hsep t htq u hu))
    · have hdist : dist t q₀ < ε := by
        rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 (show (q₀ : ℝ) < t from htq))]
        have : (t : ℝ) ≤ q₀ + η := by exact_mod_cast ht
        change (t : ℝ) - q₀ < ε
        have hη' : (η : ℝ) = ε / 2 := rfl
        linarith
      have hγt : ‖γ t - γ q₀‖ < δ / (2 * M') := by
        rw [← dist_eq_norm]; exact hεγ hdist
      have hsplit : ((x₀ : ℂ) + γ t) * α u + 1 =
          (((x₀ : ℂ) + γ q₀) * α u + 1) + (γ t - γ q₀) * α u := by ring
      have hbound : ‖(γ t - γ q₀) * α u‖ ≤ δ / 2 := by
        rw [norm_mul]
        calc ‖γ t - γ q₀‖ * ‖α u‖ ≤ δ / (2 * M') * M' :=
              mul_le_mul hγt.le (hαM u hu) (norm_nonneg _) hε.le
          _ = δ / 2 := by field_simp
      intro hz
      have h1 := hsep q₀ le_rfl u hu
      have h2 : ‖((x₀ : ℂ) + γ q₀) * α u + 1‖ ≤ δ / 2 := by
        have : ((x₀ : ℂ) + γ q₀) * α u + 1 = -((γ t - γ q₀) * α u) := by
          rw [hsplit] at hz; linear_combination hz
        rw [this, norm_neg]; exact hbound
      linarith
  refine lt_of_lt_of_le (b := ((q₀ + η : ℝ≥0) : ℝ≥0∞)) ?_ (le_iInf₂ fun t ht => ?_)
  · exact ENNReal.coe_lt_coe.2 (lt_add_of_pos_right _ (by exact_mod_cast hη0))
  · obtain ⟨u, hu, hue⟩ := ht
    have hc : ((x₀ : ℂ) + γ t) * α u + 1 = 0 := (SourceC.sphereInv_eq_iff _ _).1 hue.symm
    by_contra hlt
    exact hno t (ENNReal.coe_le_coe.1 (le_of_not_ge hlt)) u hu hc

/-! ### Small initial prefixes are separated -/

/-- **Small prefixes from `0` are separated** from a counterflow prefix bounded by `M`, for a root
`x₀ ∈ [0, 1/(4(M+1))]`: on a positive initial interval `‖(x₀ + γ t) α u + 1‖ ≥ 1/2` and
`x₀ ‖α u‖ ≤ 1/2`. -/
theorem exists_small_sep {γ α : ℝ≥0 → ℂ} {x₀ M : ℝ} {s : ℝ≥0} (hγ : ContinuousAt γ 0) (hγ0 : γ 0 = 0)
    (hM0 : 0 ≤ M) (hαM : ∀ u ∈ Icc 0 s, ‖α u‖ ≤ M) (hx₀ : 0 ≤ x₀) (hx₀M : x₀ * (M + 1) ≤ 1 / 4) :
    ∃ t₀ : ℝ≥0, 0 < t₀ ∧ ∀ t ≤ t₀, ∀ u ∈ Icc 0 s,
      1 / 2 ≤ ‖((x₀ : ℂ) + γ t) * α u + 1‖ ∧ x₀ * ‖α u‖ ≤ 1 / 2 := by
  have hε : (0 : ℝ) < 1 / (4 * (M + 1)) := by positivity
  obtain ⟨ε, hε0, hεγ⟩ := Metric.continuousAt_iff.1 hγ _ hε
  refine ⟨⟨ε / 2, by positivity⟩, by
    exact_mod_cast (show (0 : ℝ) < ε / 2 by positivity), ?_⟩
  intro t ht u hu
  have hdist : dist t 0 < ε := by
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]
    have : (t : ℝ) ≤ ε / 2 := by exact_mod_cast ht
    linarith
  have hγt : ‖γ t‖ < 1 / (4 * (M + 1)) := by
    have := hεγ hdist
    rwa [hγ0, dist_zero_right] at this
  have hαu := hαM u hu
  have hxα : x₀ * ‖α u‖ ≤ 1 / 4 := by
    calc x₀ * ‖α u‖ ≤ x₀ * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) hx₀
      _ ≤ 1 / 4 := hx₀M
  have hγα : ‖γ t‖ * ‖α u‖ ≤ 1 / 4 := by
    calc ‖γ t‖ * ‖α u‖ ≤ 1 / (4 * (M + 1)) * (M + 1) :=
          mul_le_mul hγt.le (by linarith) (norm_nonneg _) hε.le
      _ = 1 / 4 := by field_simp
  refine ⟨?_, by linarith⟩
  have hprod : ‖((x₀ : ℂ) + γ t) * α u‖ ≤ 1 / 2 := by
    rw [norm_mul]
    calc ‖(x₀ : ℂ) + γ t‖ * ‖α u‖ ≤ (x₀ + ‖γ t‖) * ‖α u‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
          calc ‖(x₀ : ℂ) + γ t‖ ≤ ‖(x₀ : ℂ)‖ + ‖γ t‖ := norm_add_le _ _
            _ = x₀ + ‖γ t‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hx₀]
      _ ≤ 1 / 2 := by nlinarith
  have h1 : ‖(1 : ℂ)‖ ≤ ‖((x₀ : ℂ) + γ t) * α u + 1‖ + ‖((x₀ : ℂ) + γ t) * α u‖ := by
    have := norm_sub_le (((x₀ : ℂ) + γ t) * α u + 1) (((x₀ : ℂ) + γ t) * α u)
    rwa [add_sub_cancel_left] at this
  rw [norm_one] at h1
  linarith

/-! ### Interior tips at times of a dense set -/

/-- A real translate of a point of `ℍ` is in `ℍ`. -/
theorem ofReal_add_mem_H_iff (x₀ : ℝ) (z : ℂ) : (x₀ : ℂ) + z ∈ H ↔ z ∈ H := by
  change 0 < ((x₀ : ℂ) + z).im ↔ 0 < z.im
  rw [Complex.add_im, Complex.ofReal_im, zero_add]

/-- **Interior tips at times of a dense set** (Lemma 2.5, zero boundary occupation): a generating
trace of a driver continuous before its lifetime `ζ`, from `0`, has `γ(q) ∈ ℍ` at some `q` of any
dense set `Q` in every interval `(0, b)`, `b ≤ ζ`. -/
theorem exists_mem_tip_mem_H {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ζ γ)
    (hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {Q : Set ℝ≥0} (hQ : Dense Q)
    {b : ℝ≥0} (hb0 : 0 < b) (hbζ : (b : ℝ≥0∞) ≤ ζ) :
    ∃ q ∈ Q, 0 < q ∧ q < b ∧ γ q ∈ H := by
  have hnull := hγ.volume_setOf_notMem_H hwc hw0
  obtain ⟨t, ht, htH⟩ : ∃ t ∈ Ioo (0 : ℝ) b, γ t.toNNReal ∈ H := by
    by_contra hne
    have hall : ∀ t ∈ Ioo (0 : ℝ) b, γ t.toNNReal ∉ H := fun t ht h => hne ⟨t, ht, h⟩
    have hsub : Ioo (0 : ℝ) b ⊆
        {t : ℝ | 0 ≤ t ∧ ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ∧ γ t.toNNReal ∉ H} := by
      intro t ht
      refine ⟨ht.1.le, lt_of_lt_of_le ?_ hbζ, hall t ht⟩
      exact ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2)
    have hpos : 0 < volume (Ioo (0 : ℝ) b) := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.2 (by simpa using hb0)
    exact hpos.ne' (measure_mono_null hsub hnull)
  set τ : ℝ≥0 := t.toNNReal with hτ
  have hτ0 : 0 < τ := Real.toNNReal_pos.2 ht.1
  have hτb : τ < b := (Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2
  have hτζ : (τ : ℝ≥0∞) < ζ := (ENNReal.coe_lt_coe.2 hτb).trans_le hbζ
  have hγτ : ContinuousAt γ τ :=
    hγ.2.1.continuousAt (Filter.mem_of_superset
      ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hτζ)
        fun u (hu : (u : ℝ≥0∞) < ζ) => show (u : ℝ≥0∞) ≤ ζ from hu.le)
  obtain ⟨U, hUo, hτU, hUH⟩ : ∃ U : Set ℝ≥0, IsOpen U ∧ τ ∈ U ∧ ∀ u ∈ U, γ u ∈ H := by
    have hpre : γ ⁻¹' H ∈ 𝓝 τ := hγτ.preimage_mem_nhds (QuantumZipper.isOpen_H.mem_nhds htH)
    obtain ⟨U, hU, hUo, hτU⟩ := mem_nhds_iff.1 hpre
    exact ⟨U, hUo, hτU, fun u hu => hU hu⟩
  obtain ⟨q, ⟨hqU, hq⟩, hqQ⟩ := hQ.inter_open_nonempty (U ∩ Ioo 0 b) (hUo.inter isOpen_Ioo)
    ⟨τ, hτU, hτ0, hτb⟩
  exact ⟨q, hqQ, hq.1, hq.2, hUH q hqU⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootCv

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.Aux7
import InteractingSLE.Spec.Zhan.Avoid
import InteractingSLE.Spec.Sec7.ContinuityProb3Random
import InteractingSLE.Foundations.Loewner.TraceCodingTop
import QuantumZipper.Proofs.RS.TraceShift

/-!
# The future trace stays away from the seed (`κ ≤ 4`, every admissible word)

Packet PROVE-ZHAN-B2. Astra, *Formalization proofs and dependency audit* (ruling R35), "Two-force transience,
including the seed case" (L1404–L1410): "Normalize its half-plane chart so the tip is zero … these two points are
exactly the inverse fibre of the original source. The future is a separated two-force law, whose entire range stays a
positive distance from both points by the preceding lemma. Compactness and the continuous inverse map show that the
original future stays a positive distance from zero." This is also the input "`0 ∉ closure η[1, ∞)`" of Rohde–Schramm's
transience argument ([RS05, proof of Theorem 7.1]).

This file proves it for every ordered force word with admissible side partial sums (marks at `0⁻`, `0⁺` allowed),
`0 < κ ≤ 4`, at every positive time `σ`:

* **deterministic base step** (`exists_pos_le_norm_of_shift_avoid`): if the trace `η` of a continuous driver has
  `η σ ≠ 0`, and the trace `η₂` of the driver restarted at `σ` stays a positive distance from every compact subset of
  `ℝ ∖ {0}`, then `η` stays a positive distance from `0` after `σ`. The continuous extension `F̄_σ` of `g_σ⁻¹`
  (`Sec7.IsGeneratingTraceIcc.extend_props`) has `F̄_σ⁻¹(0) ⊂ ℝ` compact and not containing `0` (its value at `0` is the
  tip `η σ ≠ 0`), `η(σ + s) = F̄_σ(η₂ s)` (`Sec7.IsGeneratingTraceIcc.join`), and `‖F̄_σ‖` has a positive minimum on
  the compact part of `ℍ̄` at distance `≥ d` from `F̄_σ⁻¹(0)`. No identification of the fibre is needed.
* **the Borel avoidance event** (`AvoidEvent`): infinite horizon, a continuous generating trace on `[0, ∞)`, and the
  rational-time trace values at positive distance from each `[−(n+1), −1/(n+1)] ∪ [1/(n+1), n+1]`; it is Borel in the
  (driver, horizon) pair (`measurableSet_avoidSet`), through the trace coding (`Sec7.topTraceCodingStatement`) and the
  measurable trace evaluations `LP.traceAt`.
* **restart** (`IsIntegratedSLEEvolution.ae_restart_avoidEvent`): by the conditional law at the time `σ`
  (PROVE-RANDRESTART2's `Sec7.RandRestart.measure_restart_codeEvent`), the uniform avoidance of PROVE-ZHAN-B
  (`Zhan.IsIntegratedSLEEvolution.ae_avoid_compact`) for every realized separated admissible word transfers to the
  restarted driver.

## Main results

* `exists_pos_le_norm_of_shift_avoid` (deterministic).
* `Zhan.IsIntegratedSLEEvolution.ae_exists_pos_le_norm_trace`: almost surely, for every `σ > 0`, every continuous
  generating trace on `[0, ∞)` stays a positive distance from `0` on `[σ, ∞)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open QuantumZipper (H Hbar fwdHull fwdMapInv)

variable {nL nR : ℕ}

/-! ### The deterministic base step -/

/-- **The base step.** Let `w` be a continuous driver with `w 0 = 0` and a continuous generating trace `η` on
`[0, ∞)`, let `σ ≥ 0` with `η σ ≠ 0`, and let `η₂` be a continuous generating trace on `[0, ∞)` of the driver
restarted at `σ` that stays a positive distance from every compact subset of `ℝ ∖ {0}`. Then `η` stays a positive
distance from `0` on `[σ, ∞)`. -/
theorem exists_pos_le_norm_of_shift_avoid {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) {σ : ℝ≥0} (hησ : η σ ≠ 0) {η₂ : ℝ≥0 → ℂ}
    (hη₂ : IsGeneratingTrace (Sec7.shiftNN w σ) ⊤ η₂)
    (havoid : ∀ I : Set ℝ, IsCompact I → (0 : ℝ) ∉ I → ∃ d > 0, ∀ t : ℝ≥0, ∀ x ∈ I, d ≤ ‖η₂ t - x‖) :
    ∃ d > 0, ∀ t : ℝ≥0, σ ≤ t → d ≤ ‖η t‖ := by
  have hwc : ContinuousOn w {s | (s : ℝ≥0∞) < ⊤} := hw.continuousOn
  have h₁ := Sec7.IsGeneratingTrace.isGeneratingTraceIcc hη hwc hw0 (σ := σ) ENNReal.coe_lt_top
  have hσt₂ : (σ : ℝ) < (σ : ℝ) + 1 := lt_add_one _
  have hfc : Continuous (frozenDrive w ((σ : ℝ) + 1)) := continuous_frozenDrive hw.continuousOn
  obtain ⟨hF, -, hEq, hcont, -, ⟨C, hC⟩, hF0⟩ := h₁.extend_props hσt₂ hfc hw0
  set Fb := extendFrom H (fwdMapInv (frozenDrive w ((σ : ℝ) + 1)) σ) with hFb
  -- the join identifies the future with `F̄_σ ∘ η₂`
  have hwc' : ContinuousOn w {s | (s : ℝ≥0∞) < (σ : ℝ≥0∞) + ⊤} := by rw [add_top]; exact hwc
  obtain ⟨hjoin, -⟩ := h₁.join hwc' hw0 hη₂
  rw [add_top] at hjoin
  have hjoinF : ∀ t : ℝ≥0, σ < t → η t = Fb (η₂ (t - σ)) := by
    intro t ht
    rw [hη.eq_of_le hjoin hwc hw0 le_top, Sec7.joinTrace_of_lt ht, hF]
  -- values of `η₂` lie in `ℍ̄`
  have hw₂ : Continuous fun s : ℝ => Sec7.shiftNN w σ s.toNNReal := by
    unfold Sec7.shiftNN
    exact ((hw.comp (continuous_const.add continuous_id)).sub continuous_const).comp continuous_real_toNNReal
  have hη₂H : ∀ s, η₂ s ∈ Hbar := fun s =>
    Sec4.im_nonneg_of_isGeneratingTrace hw₂ (Sec7.shiftNN_zero w σ) hη₂ s
  -- `F̄_σ` maps `ℍ` into `ℍ`
  have hf0 : frozenDrive w ((σ : ℝ) + 1) 0 = 0 := by
    simp [frozenDrive, min_eq_left (show (0 : ℝ) ≤ (σ : ℝ) + 1 by positivity), hw0]
  have hFbH : ∀ z ∈ H, Fb z ∈ H := fun z hz => by
    rw [hEq hz]
    exact QuantumZipper.RS.fwdMapInv_mem_H hfc hf0 σ.coe_nonneg hz
  have hRH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => by
    show 0 ≤ (x : ℂ).im
    simp
  -- the real fibre over `0`
  set Z : Set ℝ := {x | Fb x = 0} with hZ
  have hZc : IsCompact Z := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_eq ((hcont.comp_continuous Complex.continuous_ofReal hRH)) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := C)).subset fun x hx => ?_
      have h := hC x (hRH x)
      rw [show Fb x = 0 from hx, zero_sub, norm_neg] at h
      rw [Metric.mem_closedBall, dist_zero_right]
      simpa using h
  have h0Z : (0 : ℝ) ∉ Z := fun h => hησ (by
    have : Fb ((0 : ℝ) : ℂ) = 0 := h
    rw [Complex.ofReal_zero, hF0] at this
    exact this)
  obtain ⟨d', hd', hav⟩ := havoid Z hZc h0Z
  -- the compact set of candidate restarted positions near `0`
  set K : Set ℂ := (closedBall (0 : ℂ) (C + 1) ∩ Hbar) ∩ ⋂ x ∈ Z, {y | d' ≤ ‖y - x‖} with hK
  have hKc : IsCompact K := by
    refine ((isCompact_closedBall 0 (C + 1)).inter_right ?_).inter_right ?_
    · exact isClosed_le continuous_const Complex.continuous_im
    · exact isClosed_biInter fun x _ => isClosed_le continuous_const (continuous_id.sub continuous_const).norm
  have hKH : K ⊆ Hbar := fun y hy => hy.1.2
  have hne : ∀ y ∈ K, Fb y ≠ 0 := by
    intro y hy h
    rcases (show 0 ≤ y.im from hy.1.2).lt_or_eq with hpos | hzero
    · exact (show ¬ (0 < (0 : ℂ).im) by simp) (h ▸ hFbH y hpos)
    · have hy' : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hmem : y.re ∈ Z := by
        show Fb (y.re : ℂ) = 0
        rw [← hy']; exact h
      have h2 : d' ≤ ‖y - (y.re : ℂ)‖ := mem_iInter₂.1 hy.2 y.re hmem
      rw [← hy', sub_self, norm_zero] at h2
      linarith
  obtain ⟨m, hm, hmK⟩ : ∃ m > 0, ∀ y ∈ K, m ≤ ‖Fb y‖ := by
    rcases K.eq_empty_or_nonempty with hK0 | hK0
    · exact ⟨1, one_pos, fun y hy => by rw [hK0] at hy; exact hy.elim⟩
    · obtain ⟨y₀, hy₀, hmin⟩ := hKc.exists_isMinOn hK0 ((hcont.mono hKH).norm)
      exact ⟨‖Fb y₀‖, norm_pos_iff.2 (hne y₀ hy₀), fun y hy => hmin hy⟩
  refine ⟨min (min m 1) ‖η σ‖, lt_min (lt_min hm one_pos) (norm_pos_iff.2 hησ), fun t ht => ?_⟩
  rcases ht.lt_or_eq with ht | rfl
  · rw [hjoinF t ht]
    set y := η₂ (t - σ)
    by_cases hy : ‖y‖ ≤ C + 1
    · have hyK : y ∈ K := ⟨⟨by rwa [Metric.mem_closedBall, dist_zero_right], hη₂H _⟩,
        mem_iInter₂.2 fun x hx => hav (t - σ) x hx⟩
      exact (min_le_left _ _).trans ((min_le_left _ _).trans (hmK y hyK))
    · push Not at hy
      have h1 := hC y (hη₂H _)
      have h2 : ‖y‖ - ‖Fb y‖ ≤ ‖Fb y - y‖ := by
        have := norm_sub_norm_le y (Fb y)
        rw [norm_sub_rev] at this
        exact this
      exact (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  · exact min_le_right _ _

/-! ### Compact subsets of `ℝ ∖ {0}` -/

/-- The compact sets `[−(n+1), −1/(n+1)] ∪ [1/(n+1), n+1]`, exhausting `ℝ ∖ {0}`. -/
def avoidInt (n : ℕ) : Set ℝ :=
  Icc (-((n : ℝ) + 1)) (-(1 / ((n : ℝ) + 1))) ∪ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)

theorem isCompact_avoidInt (n : ℕ) : IsCompact (avoidInt n) := isCompact_Icc.union isCompact_Icc

theorem zero_notMem_avoidInt (n : ℕ) : (0 : ℝ) ∉ avoidInt n := by
  have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
  rintro (⟨-, h2⟩ | ⟨h1, -⟩) <;> linarith

theorem avoidInt_nonempty (n : ℕ) : (avoidInt n).Nonempty := by
  refine ⟨(n : ℝ) + 1, Or.inr ⟨?_, le_rfl⟩⟩
  rw [div_le_iff₀ (by positivity)]
  have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith

/-- Every compact subset of `ℝ ∖ {0}` lies in some `avoidInt n`. -/
theorem exists_subset_avoidInt {I : Set ℝ} (hI : IsCompact I) (h0 : (0 : ℝ) ∉ I) :
    ∃ n, I ⊆ avoidInt n := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨R, hR⟩ := hI.isBounded.exists_norm_le
  obtain ⟨x₀, hx₀, hmin⟩ := hI.exists_isMinOn hne continuous_norm.continuousOn
  have hε : 0 < ‖x₀‖ := norm_pos_iff.2 fun h => h0 (h ▸ hx₀)
  obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hε
  obtain ⟨n₂, hn₂⟩ := exists_nat_ge R
  refine ⟨max n₁ n₂, fun x hx => ?_⟩
  have hle₁ : ((n₁ : ℝ) + 1) ≤ ((max n₁ n₂ : ℕ) : ℝ) + 1 := by
    have : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_left n₁ n₂
    linarith
  have hle₂ : (n₂ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast le_max_right n₁ n₂
  have h1 : 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) ≤ ‖x‖ :=
    (one_div_le_one_div_of_le (by positivity) hle₁).trans (hn₁.le.trans (hmin hx))
  have h2 : ‖x‖ ≤ ((max n₁ n₂ : ℕ) : ℝ) + 1 := by linarith [hR x hx]
  rcases le_or_gt 0 x with hx0 | hx0
  · right
    rw [Real.norm_of_nonneg hx0] at h1 h2
    exact ⟨h1, h2⟩
  · left
    rw [Real.norm_of_nonpos hx0.le] at h1 h2
    exact ⟨by linarith, by linarith⟩

/-- `η` stays a positive distance from each `avoidInt n`. -/
def AvoidsReal (η : ℝ≥0 → ℂ) : Prop :=
  ∀ n : ℕ, ∃ d > 0, ∀ t : ℝ≥0, ∀ x ∈ avoidInt n, d ≤ ‖η t - x‖

theorem avoidsReal_iff {η : ℝ≥0 → ℂ} : AvoidsReal η ↔
    ∀ I : Set ℝ, IsCompact I → (0 : ℝ) ∉ I → ∃ d > 0, ∀ t : ℝ≥0, ∀ x ∈ I, d ≤ ‖η t - x‖ := by
  constructor
  · intro h I hI h0
    obtain ⟨n, hn⟩ := exists_subset_avoidInt hI h0
    obtain ⟨d, hd, hdist⟩ := h n
    exact ⟨d, hd, fun t x hx => hdist t x (hn hx)⟩
  · exact fun h n => h _ (isCompact_avoidInt n) (zero_notMem_avoidInt n)

/-! ### The Borel avoidance event -/

/-- `avoidInt n` in `ℂ`. -/
def avoidIntC (n : ℕ) : Set ℂ := ((↑) : ℝ → ℂ) '' avoidInt n

/-- The rational-time avoidance condition on the measurable trace evaluations. -/
def ratAvoidSet : Set (ℚ≥0 → ℝ) :=
  ⋂ n : ℕ, ⋃ k : ℕ, ⋂ q : ℚ≥0,
    {v | 1 / ((k : ℝ) + 1) ≤ infDist (LP.traceAt q (Sec7.extendRat v)) (avoidIntC n)}

theorem measurableSet_ratAvoidSet : MeasurableSet ratAvoidSet :=
  MeasurableSet.iInter fun _ => MeasurableSet.iUnion fun _ => MeasurableSet.iInter fun q =>
    measurableSet_le measurable_const ((continuous_infDist_pt _).measurable.comp
      ((LP.measurable_traceAt (q : ℝ≥0)).comp Sec7.measurable_extendRat))

/-- For a continuous driver with a generating trace on `[0, ∞)`, the rational avoidance condition is the avoidance
of every `avoidInt n` by the trace. -/
theorem ratVals_mem_ratAvoidSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) : (fun q : ℚ≥0 => w q) ∈ ratAvoidSet ↔ AvoidsReal η := by
  have htr : ∀ q : ℚ≥0, LP.traceAt q (Sec7.extendRat fun q : ℚ≥0 => w q) = η q := fun q => by
    rw [Sec7.extendRat_eq hw]
    exact LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  simp only [ratAvoidSet, mem_iInter, mem_iUnion, mem_ofPred_eq, htr]
  constructor
  · intro h n
    obtain ⟨k, hk⟩ := h n
    refine ⟨1 / ((k : ℝ) + 1), by positivity, fun t x hx => ?_⟩
    have hlim : Tendsto (fun m => infDist (η (Sec7.ratAbove t m)) (avoidIntC n)) atTop
        (𝓝 (infDist (η t) (avoidIntC n))) :=
      ((continuous_infDist_pt _).tendsto _).comp ((hηc.tendsto t).comp (Sec7.tendsto_ratAbove t))
    have hge := ge_of_tendsto' hlim fun m => hk (Sec7.ratAbove t m)
    calc 1 / ((k : ℝ) + 1) ≤ infDist (η t) (avoidIntC n) := hge
      _ ≤ dist (η t) x := infDist_le_dist_of_mem (mem_image_of_mem _ hx)
      _ = ‖η t - x‖ := dist_eq_norm _ _
  · intro h n
    obtain ⟨d, hd, hdist⟩ := h n
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hd
    refine ⟨k, fun q => ?_⟩
    rw [le_infDist (s := avoidIntC n) ((avoidInt_nonempty n).image _)]
    rintro _ ⟨x, hx, rfl⟩
    rw [dist_eq_norm]
    exact hk.le.trans (hdist q x hx)

/-- The trace coding on `[0, ∞)` (PROVE-TRACECODE). -/
def topSet : Set (ℚ≥0 → ℝ) := Classical.choose Sec7.topTraceCodingStatement

theorem measurableSet_topSet : MeasurableSet topSet :=
  (Classical.choose_spec Sec7.topTraceCodingStatement).1

theorem ratVals_mem_topSet_iff {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) :
    (fun q : ℚ≥0 => w q) ∈ topSet ↔ ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η :=
  (Classical.choose_spec Sec7.topTraceCodingStatement).2 w hw hw0

/-- **The avoidance event** of a (driver, horizon) pair: infinite horizon, a continuous generating trace on
`[0, ∞)`, and the rational avoidance condition. -/
def AvoidEvent (w : ℝ≥0 → ℝ) (τ : ℝ≥0∞) : Prop :=
  τ = ⊤ ∧ (fun q : ℚ≥0 => w q) ∈ topSet ∧ (fun q : ℚ≥0 => w q) ∈ ratAvoidSet

/-- The Borel set of (driver, horizon) pairs with the avoidance event. -/
def avoidSet : Set ((ℝ≥0 → ℝ) × ℝ≥0∞) :=
  (Prod.snd ⁻¹' {⊤}) ∩ ((fun x => fun q : ℚ≥0 => x.1 q) ⁻¹' (topSet ∩ ratAvoidSet))

theorem measurableSet_avoidSet : MeasurableSet avoidSet := by
  refine (measurable_snd (measurableSet_singleton ⊤)).inter ?_
  have hm : Measurable fun x : (ℝ≥0 → ℝ) × ℝ≥0∞ => fun q : ℚ≥0 => x.1 q :=
    measurable_pi_iff.2 fun q => (measurable_pi_apply _).comp measurable_fst
  exact hm (measurableSet_topSet.inter measurableSet_ratAvoidSet)

theorem AvoidEvent.of_avoidsReal {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (hav : AvoidsReal η) : AvoidEvent w ⊤ :=
  ⟨rfl, (ratVals_mem_topSet_iff hw hw0).2 ⟨η, hη⟩, (ratVals_mem_ratAvoidSet_iff hw hw0 hη).2 hav⟩

theorem not_avoidEvent_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hn : ¬ AvoidEvent w τ) : ¬ AvoidEvent w' τ := by
  rintro ⟨hτ, h2⟩
  subst hτ
  have : w = w' := funext fun t => h t ENNReal.coe_lt_top
  subst this
  exact hn ⟨rfl, h2⟩

/-! ### Transfer through the restart kernel -/

section Kernel

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

/-- The Borel set of solution codes whose driver has the avoidance event up to the lifetime. -/
def avoidCodeSet : Set (XCode nL nR) := (fun x => (cw x, cζ x)) ⁻¹' avoidSet

theorem measurableSet_avoidCodeSet : MeasurableSet (avoidCodeSet (nL := nL) (nR := nR)) :=
  measurable_cw_cζ measurableSet_avoidSet

/-- **Uniform avoidance at a realized separated admissible word** (PROVE-ZHAN-B): the canonical probability of the
complement of the avoidance event is zero. -/
theorem codeLaw_compl_avoidCodeSet_eq_zero {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hF : IsOrderedForceWord s.1 s.2)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR s.1 s.2) (hxL : ∀ i, s.1 i < 0) (hxR : ∀ j, 0 < s.2 j)
    (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    codeLaw κ ρL ρR (avoidCodeSet (nL := nL) (nR := nR))ᶜ s = 0 := by
  have hsep : ∀ i j, s.1 i < s.2 j := fun i j => (hxL i).trans (hxR j)
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{0} hsep hsolv
  have hav : ∀ᵐ ω ∂P, AvoidEvent (fun t => W t ω) (ζ ω) := by
    filter_upwards [IsIntegratedSLEEvolution.ae_avoid_compact hκ hκ4 hF hadm hxL hxR hE,
      hE.ae_exists_isGeneratingTrace_top_of_hasAdmissiblePartialSums hκ hF hadm hxL hxR,
      hE.2.2.2.2] with ω ⟨hζ, havω⟩ ⟨_, η, hη⟩ hp
    have hwc : Continuous fun t => W t ω := by
      have h := hp.2.2.2.1
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    rw [hζ]
    exact AvoidEvent.of_avoidsReal hwc hp.1 hη (avoidsReal_iff.2 (havω η hη))
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ AvoidEvent w τ)
    measurableSet_avoidCodeSet.compl (fun _ _ _ => Iff.rfl) not_avoidEvent_congr
  rw [← e]
  exact ae_iff.1 hav

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The restarted driver has the avoidance event.** For an admissible word, `0 < κ ≤ 4`, and every `σ > 0`, almost
surely the driver restarted at `σ` has a continuous generating trace on `[0, ∞)` staying a positive distance from
every compact subset of `ℝ ∖ {0}`. -/
theorem IsIntegratedSLEEvolution.ae_restart_avoidEvent [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {σ : ℝ≥0} (hσ : 0 < σ) :
    ∀ᵐ ω ∂P, AvoidEvent (fun t => W (σ + t) ω - W σ ω) (ζ ω - σ) := by
  have hT := isStoppingTime_const 𝓕 σ
  have hA : MeasurableSet[hT.measurableSpace] (restartEventTies σ xL xR W VL VR ζ) := by
    rw [IsStoppingTime.measurableSpace_const]
    exact measurableSet_restartEventTies σ hE
  have hAT : ∀ ω ∈ restartEventTies σ xL xR W VL VR ζ,
      (((fun _ => σ) ω : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (0 < (fun _ => σ) ω ∨ ∀ i j, xL i < xR j) :=
    fun ω hω => ⟨hω.1, Or.inl hσ⟩
  have hlaw := measure_restart_codeEvent hκ hE hT hA hAT (Φ := fun w τ => ¬ AvoidEvent w τ)
    measurableSet_avoidCodeSet.compl (fun _ _ _ => Iff.rfl) not_avoidEvent_congr
  have hAm : MeasurableSet (restartEventTies σ xL xR W VL VR ζ) := hT.measurableSpace_le _ hA
  have hzero : ∫⁻ ω in restartEventTies σ xL xR W VL VR ζ, codeLaw κ ρL ρR (avoidCodeSet (nL := nL) (nR := nR))ᶜ
      (wordAt W VL VR (fun _ => σ) ω) ∂P = 0 := by
    refine (setLIntegral_congr_fun_ae hAm ?_).trans (setLIntegral_const _ 0 |>.trans (zero_mul _))
    filter_upwards [ae_solvable_restart hκ hE hT hA hAT] with ω h hω
    obtain ⟨hFy, hadm', hxL', hxR'⟩ := word_of_mem_restartEventTies hF hadm hω
    exact codeLaw_compl_avoidCodeSet_eq_zero hκ hκ4 hFy hadm' hxL' hxR' (h hω).2
  rw [hzero] at hlaw
  have h1 : ∀ᵐ ω ∂P, ω ∈ restartEventTies σ xL xR W VL VR ζ →
      AvoidEvent (fun t => W (σ + t) ω - W σ ω) (ζ ω - σ) := by
    rw [ae_iff]
    refine le_antisymm (le_of_eq_of_le ?_ hlaw.le) bot_le
    congr 1
    ext ω
    simp only [mem_ofPred_eq, Classical.not_imp, mem_inter_iff]
  filter_upwards [h1, IsIntegratedSLEEvolution.ae_mem_restartEventTies hκ hF hadm hE] with ω h ⟨_, hmem⟩
  exact h (hmem σ hσ)

end Kernel

/-! ### The future trace stays away from the seed -/

section Assembly

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The future trace stays away from the seed** (`κ ≤ 4`; the avoidance input of the two-force transience proof,
Astra L1404–L1410, and of [RS05, Theorem 7.1]). For an ordered word with admissible side partial sums (marks at
`0⁻`, `0⁺` allowed), almost surely, for every `σ > 0`, every continuous generating trace on `[0, ∞)` stays a positive
distance from `0` on `[σ, ∞)`. -/
theorem IsIntegratedSLEEvolution.ae_exists_pos_le_norm_trace (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ σ : ℝ≥0, 0 < σ → ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∃ d > 0, ∀ t : ℝ≥0, σ ≤ t → d ≤ ‖η t‖ := by
  have : IsProbabilityMeasure P := hE.1.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 < q →
      AvoidEvent (fun t => W ((q : ℝ).toNNReal + t) ω - W (q : ℝ).toNNReal ω) (ζ ω - (q : ℝ).toNNReal) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : 0 < q
    · filter_upwards [IsIntegratedSLEEvolution.ae_restart_avoidEvent hκ hκ4 hF hadm hE
        (σ := (q : ℝ).toNNReal) (Real.toNNReal_pos.2 (by exact_mod_cast hq))] with ω h _
      exact h
    · exact Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hq, IsIntegratedSLEEvolution.ae_simple_trace hκ hκ4 hF hadm hE, hE.2.2.2.2] with ω hqω
    ⟨hζ, _, ηs, hηs, _, hH, _⟩ hp σ hσ η hη
  obtain ⟨q, hq0, hqσ⟩ := exists_rat_btwn (show (0 : ℝ) < σ from hσ)
  have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
  have hσ'pos : 0 < (q : ℝ).toNNReal := Real.toNNReal_pos.2 hq0
  have hσ'le : (q : ℝ).toNNReal ≤ σ := Real.toNNReal_le_iff_le_coe.2 hqσ.le
  have hwc : Continuous fun t => W t ω := by
    have h := hp.2.2.2.1
    rw [hζ] at h
    exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
  have hw0 : (fun t => W t ω) 0 = 0 := hp.1
  obtain ⟨-, hTop, hRat⟩ := hqω q hq0'
  have hwc₂ : Continuous (Sec7.shiftNN (fun t => W t ω) (q : ℝ).toNNReal) :=
    (hwc.comp (continuous_const.add continuous_id)).sub continuous_const
  obtain ⟨η₂, hη₂⟩ := (ratVals_mem_topSet_iff hwc₂ (Sec7.shiftNN_zero _ _)).1 hTop
  have hav₂ := (ratVals_mem_ratAvoidSet_iff hwc₂ (Sec7.shiftNN_zero _ _) hη₂).1 hRat
  have hησ' : η (q : ℝ).toNNReal ≠ 0 := by
    rw [hη.eq_of_le hηs hwc.continuousOn hw0 le_top]
    intro h
    have := hH _ hσ'pos
    rw [h] at this
    exact (lt_irrefl (0 : ℝ)) this
  obtain ⟨d, hd, hdσ⟩ := exists_pos_le_norm_of_shift_avoid hwc hw0 hη hησ' hη₂ (avoidsReal_iff.1 hav₂)
  exact ⟨d, hd, fun t ht => hdσ t (hσ'le.trans ht)⟩

end Assembly

end InteractingSLE.Zhan

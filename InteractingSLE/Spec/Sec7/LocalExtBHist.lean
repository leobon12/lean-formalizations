/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.DeterminationRestart

/-!
# From a field-determined killed history to field-determined stopped histories

Packet PROVE-LOCEXT-B (step 7 of the split in `planning/handoffs/PROVE-AUX52-55.md`). The two-seed input of Aux. lemma
55 (`LP.TwoSeedGraphInput`) determines the whole killed driving history of a coupling by its field
(`LP.IsFieldDeterminedHistory`). Aux. lemma 55 then reads off the history **stopped at the local stop** (p. 250: "Its
stopped history through `S` is in fact determined by …"). This file proves the general step: if the killed history is
a Borel function of the field, so is the stopped history `𝒳_σ = (σ, (X_{q ∧ σ})_{q ∈ ℚ≥0})` of the completed state at
every stopping time `σ ≤ ζ` of the frozen driving filtration.

* `aeComapSigma P h`: the events almost surely equal to an event of `σ(h)` (a σ-algebra);
* `killedDrivingSigma_le_aeComapSigma`: under a history graph, every event of the killed driving filtration is one;
* `isAEDeterminedBy_of_isStoppingTime`: every stopping time of the frozen driving filtration is determined by the field
  (a set of the usual augmentation is almost surely equal to a set of the killed driving filtration, and a stopping
  time is the infimum of the rationals `q` with `σ ≤ q`);
* `isAEDeterminedBy_completedState_apply`: the completed state at a determined random time `s ≤ ζ` is determined (by
  continuity on `[0, ζ]`: it is the limit of the killed path at the dyadic times `⌊2ⁿ(s − 2⁻ⁿ)⌋ / 2ⁿ < s`);
* **`isAEDeterminedBy_stoppedHistory_of_isHistoryGraph`** and its form for couplings,
  **`IsOptionalHullCoupling.isAEDeterminedBy_stoppedHistory`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace LocalExt

open Sec7 Determination

/-! ### Events almost surely in `σ(h)` -/

section Sigma

variable {Ω γ : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace γ]

/-- The events almost surely equal to an event of `σ(h)`. -/
@[instance_reducible]
def aeComapSigma (P : Measure Ω) (h : Ω → γ) : MeasurableSpace Ω where
  MeasurableSet' A := ∃ B : Set γ, MeasurableSet B ∧ A =ᵐ[P] h ⁻¹' B
  measurableSet_empty := ⟨∅, MeasurableSet.empty, by simp⟩
  measurableSet_compl A := fun ⟨B, hB, hAB⟩ => ⟨Bᶜ, hB.compl, by
    rw [preimage_compl]; exact hAB.compl⟩
  measurableSet_iUnion f hf := by
    choose B hB hfB using hf
    refine ⟨⋃ i, B i, MeasurableSet.iUnion hB, ?_⟩
    rw [preimage_iUnion]
    exact EventuallyEqSet.countable_iUnion hfB

theorem measurableSet_aeComapSigma_iff {P : Measure Ω} {h : Ω → γ} {A : Set Ω} :
    MeasurableSet[aeComapSigma P h] A ↔ ∃ B : Set γ, MeasurableSet B ∧ A =ᵐ[P] h ⁻¹' B := Iff.rfl

end Sigma

/-! ### Rationals in `WithTop ℝ≥0` -/

/-- Between a nonnegative real and a larger point of `WithTop ℝ≥0` there is a nonnegative rational. -/
theorem exists_nnrat_btwn_withTop {t : ℝ≥0} {c : WithTop ℝ≥0} (h : (t : WithTop ℝ≥0) < c) :
    ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ ((q : ℝ≥0) : WithTop ℝ≥0) < c := by
  obtain ⟨v, hv⟩ : ∃ v : ℝ≥0, t < v ∧ (v : WithTop ℝ≥0) ≤ c := by
    cases c with
    | top => exact ⟨t + 1, by simp, le_top⟩
    | coe v => exact ⟨v, WithTop.coe_lt_coe.1 h, le_rfl⟩
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) < (v : ℝ) from hv.1)
  have hr0 : 0 ≤ r := by
    have : (0 : ℝ) ≤ t := t.2
    exact_mod_cast (show (0 : ℝ) ≤ r by linarith)
  refine ⟨⟨r, hr0⟩, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe]; exact hr1
  · refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_) hv.2
    rw [← NNReal.coe_lt_coe]; exact hr2

/-- A point of `WithTop ℝ≥0` is the infimum of the nonnegative rationals above it. -/
theorem iInf_ite_le_eq (a : WithTop ℝ≥0) :
    (⨅ q : ℚ≥0, if a ≤ ((q : ℝ≥0) : WithTop ℝ≥0) then ((q : ℝ≥0) : WithTop ℝ≥0) else ⊤) = a := by
  refine le_antisymm ?_ (le_iInf fun q => by split_ifs with h; exacts [h, le_top])
  cases a with
  | top => exact le_top
  | coe t =>
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn_withTop hlt
    have hle := iInf_le (fun q : ℚ≥0 => if ((t : WithTop ℝ≥0) ≤ ((q : ℝ≥0) : WithTop ℝ≥0)) then
      ((q : ℝ≥0) : WithTop ℝ≥0) else ⊤) q
    rw [ite_eq_left (WithTop.coe_le_coe.2 hq1.le)] at hle
    exact absurd (lt_of_le_of_lt hle hq2) (lt_irrefl _)

/-! ### The killed driving filtration under a history graph -/

section Graph

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {Ψ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)}

/-- The state recorded by a history-graph value at a time. -/
def graphState (x : ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) (t : ℝ≥0) :
    ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  (x.2.1 t, fun i => x.2.2.1 i t, fun i => x.2.2.2 i t)

theorem measurable_graphState (t : ℝ≥0) :
    Measurable fun x : ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ) =>
      graphState x t :=
  ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_pi_iff.2 fun i => (measurable_pi_apply t).comp ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_snd.comp measurable_snd)))).prodMk
    (measurable_pi_iff.2 fun i => (measurable_pi_apply t).comp ((measurable_pi_apply i).comp
      (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

/-- On the graph event, the graph state is the driving state before the lifetime. -/
theorem graphState_eq_of_isHistoryGraph {ω : Ω}
    (hω : (Ψ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (Ψ (h ω)).2.1 t = W t ω ∧ (∀ i, (Ψ (h ω)).2.2.1 i t = VL i t ω) ∧ ∀ i, (Ψ (h ω)).2.2.2 i t = VR i t ω)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ ω) :
    graphState (Ψ (h ω)) t = drivingState W VL VR t ω := by
  obtain ⟨h1, h2, h3⟩ := hω.2 t ht
  simp only [graphState, drivingState, h1]
  exact Prod.ext rfl (Prod.ext (funext h2) (funext h3))

/-- **Under a history graph, every event of the killed driving filtration is almost surely an event of `σ(h)`.** -/
theorem killedDrivingSigma_le_aeComapSigma (hΨ : Measurable Ψ) (hg : IsHistoryGraph P h W VL VR ζ Ψ)
    (t : ℝ≥0) : killedDrivingSigma W VL VR ζ t ≤ aeComapSigma P h := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro _ ⟨r, -, A, hA, rfl⟩
  refine ⟨{x | (r : ℝ≥0∞) < (Ψ x).1 ∧ graphState (Ψ x) r ∈ A}, ?_, ?_⟩
  · exact (measurableSet_lt measurable_const (measurable_fst.comp hΨ)).inter
      (hA.preimage ((measurable_graphState r).comp hΨ))
  · filter_upwards [hg] with ω hω
    change ((r : ℝ≥0∞) < ζ ω ∧ drivingState W VL VR r ω ∈ A) =
      ((r : ℝ≥0∞) < (Ψ (h ω)).1 ∧ graphState (Ψ (h ω)) r ∈ A)
    rw [hω.1]
    refine propext ⟨fun ⟨hr, hm⟩ => ⟨hr, ?_⟩, fun ⟨hr, hm⟩ => ⟨hr, ?_⟩⟩
    · rw [graphState_eq_of_isHistoryGraph hω hr]; exact hm
    · rw [graphState_eq_of_isHistoryGraph hω hr] at hm; exact hm

/-! ### Dyadic times strictly below a time -/

/-- The index `⌊2ⁿ (s − 2⁻ⁿ)⌋₊` of the dyadic time `lowApprox n s`. -/
def lowIdx (n : ℕ) (s : ℝ≥0) : ℕ := ⌊(2 : ℝ≥0) ^ n * (s - (1 / 2 : ℝ≥0) ^ n)⌋₊

/-- The dyadic time `⌊2ⁿ (s − 2⁻ⁿ)⌋₊ / 2ⁿ`: strictly below `s > 0`, equal to `0` at `s = 0`, converging to `s`. -/
def lowApprox (n : ℕ) (s : ℝ≥0) : ℝ≥0 := (lowIdx n s : ℝ≥0) / 2 ^ n

theorem measurable_lowIdx (n : ℕ) : Measurable (lowIdx n) :=
  Measurable.nat_floor (measurable_const.mul (measurable_id.sub measurable_const))

theorem lowApprox_le_sub (n : ℕ) (s : ℝ≥0) : lowApprox n s ≤ s - (1 / 2 : ℝ≥0) ^ n := by
  unfold lowApprox lowIdx
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [div_le_iff₀ h2, mul_comm]
  exact Nat.floor_le (zero_le)

theorem lowApprox_lt {s : ℝ≥0} (hs : 0 < s) (n : ℕ) : lowApprox n s < s :=
  (lowApprox_le_sub n s).trans_lt (tsub_lt_self hs (pow_pos (by norm_num) n))

theorem lowApprox_zero (n : ℕ) : lowApprox n 0 = 0 := by
  simp [lowApprox, lowIdx]

theorem tendsto_lowApprox (s : ℝ≥0) : Tendsto (fun n => lowApprox n s) atTop (𝓝 s) := by
  rw [← NNReal.tendsto_coe]
  have h2 : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => pow_pos two_pos n
  have hlow : ∀ n : ℕ, (s : ℝ) - 2 * (1 / 2 : ℝ) ^ n ≤ (lowApprox n s : ℝ) := by
    intro n
    have ha : (s : ℝ) - (1 / 2 : ℝ) ^ n ≤ ((s - (1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub_def]; push_cast; exact le_max_left _ _
    have hfl := Nat.lt_floor_add_one ((2 : ℝ≥0) ^ n * (s - (1 / 2 : ℝ≥0) ^ n))
    have hfl' : (2 : ℝ) ^ n * ((s - (1 / 2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) < (lowIdx n s : ℝ) + 1 := by
      have := (NNReal.coe_lt_coe.2 hfl)
      push_cast at this
      exact this
    have hval : (lowApprox n s : ℝ) = (lowIdx n s : ℝ) / 2 ^ n := by
      simp [lowApprox]
    rw [hval, le_div_iff₀ (h2 n)]
    have e : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    nlinarith [h2 n]
  have hup : ∀ n : ℕ, (lowApprox n s : ℝ) ≤ s := fun n =>
    NNReal.coe_le_coe.2 ((lowApprox_le_sub n s).trans tsub_le_self)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow hup
  have : Tendsto (fun n : ℕ => (s : ℝ) - 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 ((s : ℝ) - 2 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)))
  simpa using this

theorem measurable_graphState_lowApprox (n : ℕ) :
    Measurable fun p : ℝ≥0 × (ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) =>
      graphState p.2 (lowApprox n p.1) := by
  have hk : Measurable fun q : ℕ × (ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) =>
      graphState q.2 ((q.1 : ℝ≥0) / 2 ^ n) :=
    measurable_from_prod_countable_right fun k => measurable_graphState ((k : ℝ≥0) / 2 ^ n)
  exact hk.comp (((measurable_lowIdx n).comp measurable_fst).prodMk measurable_snd)

theorem measurable_lowApprox (n : ℕ) : Measurable (lowApprox n) :=
  ((measurable_from_nat (f := fun k : ℕ => (k : ℝ≥0))).comp (measurable_lowIdx n)).div_const _

/-! ### Stopping times of the frozen driving filtration are determined -/

/-- **Every stopping time of the frozen driving filtration is determined by the field** when the killed history is: a
set of the usual augmentation at `q` is almost surely a set of the killed driving filtration at `q + 1`, hence almost
surely an event of `σ(h)`, and `σ = inf {q ∈ ℚ≥0 : σ ≤ q}`. -/
theorem isAEDeterminedBy_of_isStoppingTime {hX : IsMeasurableKilledDriving W VL VR ζ} (hΨ : Measurable Ψ)
    (hg : IsHistoryGraph P h W VL VR ζ Ψ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) σ) : IsAEDeterminedBy P h σ := by
  classical
  have hB : ∀ q : ℚ≥0, ∃ B : Set (LQGMetric.DistOn upperHalfPlaneOpens), MeasurableSet B ∧
      {ω | σ ω ≤ ((q : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[P] h ⁻¹' B := by
    intro q
    obtain ⟨A', hA', hAA'⟩ := Ito.exists_ae_eq_of_measurableSet_usualAugmentation
      (𝓕 := killedDrivingFiltration hX) (lt_add_one (q : ℝ≥0)) (hσ (q : ℝ≥0))
    obtain ⟨B, hBm, hA'B⟩ := killedDrivingSigma_le_aeComapSigma hΨ hg _ A' hA'
    exact ⟨B, hBm, hAA'.trans hA'B⟩
  choose B hBm hσB using hB
  refine ⟨fun x => ⨅ q : ℚ≥0, if x ∈ B q then ((q : ℝ≥0) : WithTop ℝ≥0) else ⊤,
    Measurable.iInf fun q => Measurable.ite (hBm q) measurable_const measurable_const, ?_⟩
  filter_upwards [ae_all_iff.2 hσB] with ω hω
  have hiff : ∀ q : ℚ≥0, (h ω ∈ B q) ↔ σ ω ≤ ((q : ℝ≥0) : WithTop ℝ≥0) := fun q => by
    have := hω q
    change (σ ω ≤ ((q : ℝ≥0) : WithTop ℝ≥0)) = (h ω ∈ B q) at this
    rw [this]
  simp only [hiff]
  exact (iInf_ite_le_eq (σ ω)).symm

/-! ### The completed state at a determined time -/

/-- The completed state at time `s` read from a history-graph value, approximated at the dyadic time
`lowApprox n s < s`; the junk value of `completedState` at a vanishing lifetime otherwise. -/
def approxState (n : ℕ) (s : ℝ≥0) (x : ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) :
    ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) :=
  if ((lowApprox n s : ℝ≥0) : ℝ≥0∞) < x.1 then graphState x (lowApprox n s)
  else limUnder (𝓝[<] (0 : ℝ≥0)) fun _ => (0 : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))

theorem measurable_approxState (n : ℕ) :
    Measurable fun p : ℝ≥0 × (ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)) =>
      approxState n p.1 p.2 := by
  refine Measurable.ite ?_ (measurable_graphState_lowApprox n) measurable_const
  exact measurableSet_lt (measurable_coe_nnreal_ennreal.comp
    ((measurable_lowApprox n).comp measurable_fst)) (measurable_fst.comp measurable_snd)

theorem nhdsLT_zero_nnreal : (𝓝[<] (0 : ℝ≥0)) = ⊥ := by
  rw [show Iio (0 : ℝ≥0) = ∅ by ext s; simp, nhdsWithin_empty]

/-- At a vanishing lifetime the completed state at `0` is the junk value. -/
theorem completedState_zero_of_not_lt {ω : Ω} (hζ : ¬ ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω) :
    completedState W VL VR ζ 0 ω =
      limUnder (𝓝[<] (0 : ℝ≥0)) fun _ => (0 : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) := by
  rw [completedState, ite_eq_right hζ]
  simp only [limUnder, nhdsLT_zero_nnreal, Filter.map_bot]

/-- **The completed state at a determined random time `s ≤ ζ` is determined** (continuity on `[0, ζ]`). -/
theorem isAEDeterminedBy_completedState_apply (hh : Measurable h) (hΨ : Measurable Ψ)
    (hg : IsHistoryGraph P h W VL VR ζ Ψ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => completedState W VL VR ζ t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)})
    {s : Ω → ℝ≥0} (hs : IsAEDeterminedBy P h s) (hsζ : ∀ᵐ ω ∂P, (s ω : ℝ≥0∞) ≤ ζ ω) :
    IsAEDeterminedBy P h fun ω => completedState W VL VR ζ (s ω) ω := by
  have hY : ∀ n, IsAEDeterminedBy P h fun ω => approxState n (s ω) (Ψ (h ω)) := fun n =>
    (hs.prodMk ⟨Ψ, hΨ, ae_of_all _ fun _ => rfl⟩).comp (measurable_approxState n)
  refine IsAEDeterminedBy.of_tendsto hh hY ?_
  filter_upwards [hg, hcont, hsζ] with ω hω hc hsle
  rcases eq_zero_or_pos (s ω) with hs0 | hs0
  · have hconst : ∀ n, approxState n (s ω) (Ψ (h ω)) = completedState W VL VR ζ (s ω) ω := by
      intro n
      rw [hs0, approxState, lowApprox_zero, hω.1]
      by_cases hζ : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω
      · rw [ite_eq_left hζ, graphState_eq_of_isHistoryGraph hω hζ, completedState, ite_eq_left hζ]
      · rw [ite_eq_right hζ, completedState_zero_of_not_lt hζ]
    simp_rw [hconst]
    exact tendsto_const_nhds
  · have hlt : ∀ n, ((lowApprox n (s ω) : ℝ≥0) : ℝ≥0∞) < ζ ω := fun n =>
      lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (lowApprox_lt hs0 n)) hsle
    have he : ∀ n, approxState n (s ω) (Ψ (h ω)) =
        completedState W VL VR ζ (lowApprox n (s ω)) ω := by
      intro n
      rw [approxState, hω.1, ite_eq_left (hlt n), graphState_eq_of_isHistoryGraph hω (hlt n), completedState,
        ite_eq_left (hlt n)]
    simp_rw [he]
    have hmem : ∀ n, lowApprox n (s ω) ∈
        {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)} := fun n => (hlt n).le
    exact (hc (s ω) hsle).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨tendsto_lowApprox _, Eventually.of_forall hmem⟩)

/-! ### Stopped histories -/

/-- **Under a history graph, the stopped history of the completed state at every stopping time `σ ≤ ζ` of the frozen
driving filtration is determined by the field.** -/
theorem isAEDeterminedBy_stoppedHistory_of_isHistoryGraph {hX : IsMeasurableKilledDriving W VL VR ζ}
    (hh : Measurable h) (hΨ : Measurable Ψ) (hg : IsHistoryGraph P h W VL VR ζ Ψ)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => completedState W VL VR ζ t ω)
      {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (ζ ω : WithTop ℝ≥0)})
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) σ)
    (hσζ : ∀ ω, σ ω ≤ (ζ ω : WithTop ℝ≥0)) :
    IsAEDeterminedBy P h (stoppedHistory (completedState W VL VR ζ) σ) := by
  have hσd := isAEDeterminedBy_of_isStoppingTime hΨ hg hσ
  refine hσd.prodMk (isAEDeterminedBy_pi fun q => ?_)
  refine isAEDeterminedBy_completedState_apply hh hΨ hg hcont ?_
    (ae_of_all _ fun ω => (stopAt_le σ q ω).trans (hσζ ω))
  exact hσd.comp (measurable_const.min (WithTop.measurable_untopD (q : ℝ≥0)))

end Graph

/-! ### Couplings -/

section Coupling

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **A field-determined coupling has field-determined stopped histories** at every stopping time `σ ≤ ζ` of its
frozen driving filtration (the step "its stopped history through `S` is determined" of Aux. lemma 55, p. 250). -/
theorem _root_.InteractingSLE.IsOptionalHullCoupling.isAEDeterminedBy_stoppedHistory (hκ : 0 < κ)
    [IsProbabilityMeasure P] (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hdet : LP.IsFieldDeterminedHistory P h W VL VR ζ) {hX : IsMeasurableKilledDriving W VL VR ζ}
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hX) σ)
    (hσζ : ∀ ω, σ ω ≤ (ζ ω : WithTop ℝ≥0)) :
    IsAEDeterminedBy P h (stoppedHistory (completedState W VL VR ζ) σ) := by
  obtain ⟨Ψ, hΨ, hg⟩ := isFieldDeterminedHistory_iff.1 hdet
  exact isAEDeterminedBy_stoppedHistory_of_isHistoryGraph hC.2.1 hΨ hg
    (ae_continuousOn_completedState hκ hC.1) hσ hσζ

end Coupling

end LocalExt

end InteractingSLE

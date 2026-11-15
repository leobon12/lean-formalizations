/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MhPast
import InteractingSLE.Spec.Supplement.SB2MgSets

/-!
# SB2(2)'s line filtration at real caps

Packet PROVE-SB2-LCMEAN, round 7. K2's (S) at SB2(2)'s lower piece `ℓ` needs a filtration indexed by the piece's own
time `t : ℝ≥0`, whose `t`-th σ-algebra holds the retained past of the program capped at `t`. Round 5's
`Mh.pastSigma_capSpec_mono` compared a rational cap with a later cap only. For regular drivers the stopped value at a
real cap `s` is a limit of the recorded values at rational times below `s`, so the comparison holds at real caps:

* `ratBelow x n`: a rational in `(x - 1/(n+1), x)`; `tendsto_ratBelow`;
* `capRecFromR s r`: the record of a piece stopped at the real time `s`, read from its record stopped at any later time
  (the stopped value after `s` is the `limsup` of the recorded values at `ratBelow s n`); measurable;
* **`readRec_retOf_capFromR`**: for a regular driver and `s ≤ t`,
  `readRec (retOf s e) = capRecFromR s (readRec (retOf t e))`;
* **`pastSigma_capSpec_mono_real`**: for everywhere regular drivers, the capped past at a real cap `s` lies in the
  capped past at any later cap;
* **`capFiltration`**: `t ↦ 𝓐 ⊔ pastSigma (capSpec w ℓ θ t) E (ℓ + 1)` as a `Filtration ℝ≥0`;
* **`exists_sb2LineFamily`**: SB2(2)'s line family for K2's (S): the filtration `t ↦` (upper past at stage `k`) `⊔`
  (capped walk past at cap `t`), and for each `t` the line set `A₁ t ∪ A₂ t` (round 4's marked stage sets at cap `t`),
  measurable, relatively closed, local and marked local for the filtration at `t` (K2's `hBm`, `hBc`, `hloc`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Mj

open Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField

/-! ### Rationals below a real number -/

theorem sub_one_div_lt_self (x : ℝ) (n : ℕ) : x - 1 / ((n : ℝ) + 1) < x :=
  sub_lt_self x Nat.one_div_pos_of_nat

/-- A rational in `(x - 1/(n+1), x)`. -/
def ratBelow (x : ℝ) (n : ℕ) : ℚ := Classical.choose (exists_rat_btwn (sub_one_div_lt_self x n))

theorem ratBelow_lt (x : ℝ) (n : ℕ) : (ratBelow x n : ℝ) < x :=
  (Classical.choose_spec (exists_rat_btwn (sub_one_div_lt_self x n))).2

theorem sub_lt_ratBelow (x : ℝ) (n : ℕ) : x - 1 / ((n : ℝ) + 1) < ratBelow x n :=
  (Classical.choose_spec (exists_rat_btwn (sub_one_div_lt_self x n))).1

theorem tendsto_ratBelow (x : ℝ) : Tendsto (fun n => (ratBelow x n : ℝ)) atTop (𝓝 x) := by
  have h1 : Tendsto (fun n : ℕ => x - 1 / ((n : ℝ) + 1)) atTop (𝓝 x) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa using (tendsto_const_nhds (x := x)).sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun n => (sub_lt_ratBelow x n).le)
    fun n => (ratBelow_lt x n).le

/-! ### Records at a real cap -/

/-- The record of a piece stopped at the real time `s`, read from its record stopped at a later time: before `s`
(or once the record has stopped by `s`) the recorded value; after `s`, the `limsup` of the recorded values at the
rationals `ratBelow s n` below `s`. -/
def capRecFromR (s : ℝ≥0) (r : RecData) : RecData :=
  (fun q : ℚ => if (q : ℝ) ≤ s ∨ r.2.1 ≤ (s : ℝ≥0∞) then r.1 q else limsup (fun n => r.1 (ratBelow s n)) atTop,
    min (s : ℝ≥0∞) r.2.1, r.2.2 && decide (r.2.1 ≤ (s : ℝ≥0∞)))

theorem measurable_capRecFromR (s : ℝ≥0) : Measurable (capRecFromR s) := by
  have hdec : (fun r : RecData => r.2.2 && decide (r.2.1 ≤ (s : ℝ≥0∞))) =
      fun r => if r.2.1 ≤ (s : ℝ≥0∞) then r.2.2 else false := by
    funext r
    by_cases hr : r.2.1 ≤ (s : ℝ≥0∞) <;> simp [hr]
  refine Measurable.prodMk (measurable_pi_iff.2 fun q => ?_)
    (Measurable.prodMk (measurable_const.min (measurable_fst.comp measurable_snd)) ?_)
  · have hset : MeasurableSet {r : RecData | (q : ℝ) ≤ s ∨ r.2.1 ≤ (s : ℝ≥0∞)} :=
      (MeasurableSet.const ((q : ℝ) ≤ s)).union
        (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
    exact Measurable.ite hset ((measurable_pi_apply q).comp measurable_fst)
      (Measurable.limsup fun n => (measurable_pi_apply _).comp measurable_fst)
  · show Measurable fun r : RecData => r.2.2 && decide (r.2.1 ≤ (s : ℝ≥0∞))
    rw [hdec]
    exact Measurable.ite (measurableSet_le (measurable_fst.comp measurable_snd) measurable_const)
      (measurable_snd.comp measurable_snd) measurable_const

/-- **The record at a real cap is read from the record at any later cap** (regular drivers). -/
theorem readRec_retOf_capFromR (s : ℝ≥0) {t : ℝ≥0∞} (hst : (s : ℝ≥0∞) ≤ t) {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (he : IsRegularDriver e) : readRec (retOf s e) = capRecFromR s (readRec (retOf t e)) := by
  have hmin : min (s : ℝ≥0∞) (min t e.2) = min (s : ℝ≥0∞) e.2 := by
    rw [← min_assoc, min_eq_left hst]
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ ?_)
  · show (readRec (retOf s e)).1 q = if (q : ℝ) ≤ s ∨ (readRec (retOf t e)).2.1 ≤ (s : ℝ≥0∞) then
      (readRec (retOf t e)).1 q else limsup (fun n => (readRec (retOf t e)).1 (ratBelow s n)) atTop
    by_cases hc : (q : ℝ) ≤ s ∨ (readRec (retOf t e)).2.1 ≤ (s : ℝ≥0∞)
    · rw [ite_eq_left hc]
      replace hc : (q : ℝ) ≤ s ∨ min t e.2 ≤ (s : ℝ≥0∞) := hc
      simp only [readRec, retOf]
      rcases hc with hq | hm
      · have hqs : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ s :=
          ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hq)
        have h1 : min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (s : ℝ≥0∞) e.2) =
            min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) e.2 := by
          rw [← min_assoc, min_eq_left hqs]
        have h2 : min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2) =
            min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) e.2 := by
          rw [← min_assoc, min_eq_left (hqs.trans hst)]
        rw [h1, h2]
      · have h1 : min (s : ℝ≥0∞) e.2 = min t e.2 :=
          le_antisymm (min_le_min_right _ hst) (le_min hm (min_le_right _ _))
        rw [h1]
    · rw [ite_eq_right hc]
      replace hc : ¬((q : ℝ) ≤ s ∨ min t e.2 ≤ (s : ℝ≥0∞)) := hc
      simp only [readRec, retOf]
      push Not at hc
      obtain ⟨hq, hm⟩ := hc
      have hsζ : (s : ℝ≥0∞) < e.2 := hm.trans_le (min_le_right _ _)
      have hst' : (s : ℝ≥0∞) < t := hm.trans_le (min_le_left _ _)
      have hqs : (s : ℝ≥0∞) ≤ (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) := by
        refine ENNReal.coe_le_coe.2 ?_
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ((s.2).trans hq.le)]
        exact hq.le
      have hL : min (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min (s : ℝ≥0∞) e.2) = s := by
        rw [min_eq_left hsζ.le, min_eq_right hqs]
      rw [hL, ENNReal.toNNReal_coe]
      have hseq : (fun n => e.1 (min ((((ratBelow s n : ℚ) : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal) =
          fun n => e.1 ((ratBelow s n : ℚ) : ℝ).toNNReal := by
        funext n
        have hn : ((((ratBelow s n : ℚ) : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min t e.2 := by
          refine le_trans (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 (ratBelow_lt s n).le)) ?_
          exact le_min hst'.le hsζ.le
        rw [min_eq_left hn, ENNReal.toNNReal_coe]
      rw [hseq]
      refine (Tendsto.limsup_eq ?_).symm
      have hopen : IsOpen {x : ℝ≥0 | (x : ℝ≥0∞) < e.2} := isOpen_lt ENNReal.continuous_coe continuous_const
      have hcont : ContinuousAt e.1 s := he.1.continuousAt (hopen.mem_nhds hsζ)
      have hlim : Tendsto (fun n => ((ratBelow s n : ℚ) : ℝ).toNNReal) atTop (𝓝 s) := by
        have := (continuous_real_toNNReal.tendsto (s : ℝ)).comp (tendsto_ratBelow (s : ℝ))
        rwa [Real.toNNReal_coe] at this
      exact hcont.tendsto.comp hlim
  · simp only [readRec, retOf, capRecFromR]
    exact hmin.symm
  · simp only [readRec, retOf, capRecFromR]
    by_cases hζ : e.2 ≤ t
    · have hL : min t e.2 = e.2 := min_eq_right hζ
      simp only [hL, hζ, decide_true, Bool.true_and]
    · have hσζ : ¬ e.2 ≤ (s : ℝ≥0∞) := fun h => hζ (h.trans hst)
      simp only [hζ, hσζ, decide_false, Bool.false_and]

/-! ### The capped pasts increase with a real cap -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {w : ExplSpec} {ℓ : ℕ} {θ : ℝ}

/-- **The capped retained pasts increase with the cap, at real caps** (everywhere regular drivers; instruction `ℓ` an
angle-`θ` flow of `w`). -/
theorem pastSigma_capSpec_mono_real {Ω : Type u} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ ≤ w.2.2.length) {t₀ : ℝ≥0∞}
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t₀))) {s : ℝ≥0} {t : ℝ≥0∞} (hst : (s : ℝ≥0∞) ≤ t) :
    pastSigma κ b jumps (capSpec w ℓ θ (s : ℝ≥0∞)) E (ℓ + 1) ≤ pastSigma κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) := by
  rw [pastSigma_eq_comap (spec := capSpec w ℓ θ (s : ℝ≥0∞))]
  let _ : MeasurableSpace Ω := pastSigma κ b jumps (capSpec w ℓ θ t) E (ℓ + 1)
  have hpm : Measurable (pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1)) :=
    comap_measurable (pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1))
  refine Measurable.comap_le (measurable_pi_iff.2 fun i => ?_)
  have hp : Measurable fun ω => pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) ω i :=
    (measurable_pi_apply i).comp hpm
  by_cases hi : (i : ℕ) < ℓ
  · have e : (fun ω => pastMap κ b jumps (capSpec w ℓ θ (s : ℝ≥0∞)) E (ℓ + 1) ω i) =
        fun ω => pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) ω i := by
      funext ω
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ θ (s : ℝ≥0∞)) (fun j => E j ω) (ℓ + 1)).2.2.1 i) =
        readRec ((ExplState.run κ b jumps (capSpec w ℓ θ t) (fun j => E j ω) (ℓ + 1)).2.2.1 i)
      rw [retained_run_succ_of_lt _ _ hi, retained_run_succ_of_lt _ _ hi,
        run_capSpec_of_le (τ := (s : ℝ≥0∞)) hℓ _ le_rfl, run_capSpec_of_le (τ := t) hℓ _ le_rfl]
    rw [e]
    exact hp
  · have hiℓ : (i : ℕ) = ℓ := le_antisymm (Nat.lt_succ_iff.1 i.2) (not_lt.1 hi)
    have e : (fun ω => pastMap κ b jumps (capSpec w ℓ θ (s : ℝ≥0∞)) E (ℓ + 1) ω i) =
        capRecFromR s ∘ fun ω => pastMap κ b jumps (capSpec w ℓ θ t) E (ℓ + 1) ω i := by
      funext ω
      change readRec ((ExplState.run κ b jumps (capSpec w ℓ θ (s : ℝ≥0∞)) (fun j => E j ω) (ℓ + 1)).2.2.1 i) =
        capRecFromR s (readRec ((ExplState.run κ b jumps (capSpec w ℓ θ t) (fun j => E j ω) (ℓ + 1)).2.2.1 i))
      rw [hiℓ, retained_run_succ_self, retained_run_succ_self, launches_run_capSpec_succ hℓ hwℓ,
        launches_run_capSpec_succ hℓ hwℓ, instrTime_capSpec hℓ, instrTime_capSpec hℓ]
      split_ifs
      · simp [capRecFromR, readRec]
      · exact readRec_retOf_capFromR s hst (hreg ℓ ω)
    rw [e]
    exact (measurable_capRecFromR s).comp hp

/-- **The capped line filtration**: `t ↦ 𝓐 ⊔ pastSigma (capSpec w ℓ θ t) E (ℓ + 1)` for a fixed sub-σ-algebra `𝓐`
(everywhere regular drivers; each capped past inside the ambient σ-algebra). -/
def capFiltration {Ω : Type u} (𝓐 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ ≤ w.2.2.length) {t₀ : ℝ≥0∞}
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t₀)))
    (hle : ∀ t : ℝ≥0, pastSigma κ b jumps (capSpec w ℓ θ (t : ℝ≥0∞)) E (ℓ + 1) ≤ mΩ)
    (h𝓐 : 𝓐 ≤ mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓐 ⊔ pastSigma κ b jumps (capSpec w ℓ θ (t : ℝ≥0∞)) E (ℓ + 1)
  mono' _ _ hst := sup_le_sup_left (pastSigma_capSpec_mono_real E hreg hℓ hwℓ (ENNReal.coe_le_coe.2 hst)) _
  le' t := sup_le h𝓐 (hle t)

theorem capFiltration_apply {Ω : Type u} (𝓐 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hℓ : ℓ ≤ w.2.2.length) {t₀ : ℝ≥0∞}
    (hwℓ : w.2.2[ℓ]? = some (Sum.inl (θ, t₀)))
    (hle : ∀ t : ℝ≥0, pastSigma κ b jumps (capSpec w ℓ θ (t : ℝ≥0∞)) E (ℓ + 1) ≤ mΩ)
    (h𝓐 : 𝓐 ≤ mΩ) (t : ℝ≥0) :
    capFiltration (κ := κ) (b := b) (jumps := jumps) 𝓐 E hreg hℓ hwℓ hle h𝓐 t =
      𝓐 ⊔ pastSigma κ b jumps (capSpec w ℓ θ (t : ℝ≥0∞)) E (ℓ + 1) := rfl

/-! ### SB2(2)'s line family for K2's (S) -/

section SB2

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **SB2(2)'s line family for K2's (S)**: a filtration `𝓖` indexed by the own time `t` of the lower piece `ℓ`, equal at
`t` to (upper past at stage `k`) `⊔` (walk past capped at `t`, after `ℓ + 1` instructions), and for each `t` the two
stage sets `A₁ t`, `A₂ t` of round 4 at cap `t`, whose union (K2's line set) is measurable, relatively closed, local and
marked local for `𝓖 t`; the sets are almost surely the filled versions of `A ∪ B_{<ℓ}` and `B_{≤ℓ,t}`. -/
theorem exists_sb2LineFamily (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ) {θ : ℝ}
    {t₀ : ℝ≥0∞} (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (θ, t₀)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ (t : ℝ≥0∞))
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ∧
      ∀ t : ℝ≥0,
        Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω) ∧
        (∀ ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω))) ∧
        IsLocalSet (A₁ t) (centredField h u₀) P ∧ IsLocalSet (A₂ t) (centredField h u₀) P ∧
        IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        ∀ᵐ ω ∂P, A₁ t ω = Mf.fillVer (fun ω =>
            WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
            WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ (t : ℝ≥0∞))
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ω ∧
          A₂ t ω = Mf.fillVer (WalkLaw.stageSet κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ (t : ℝ≥0∞))
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ω := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hup := hE' (Lu.upperSpec u l) (Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ)
  have hle : ∀ t : ℝ≥0, pastSigma κ b jumps
      (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ θ (t : ℝ≥0∞))
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ≤ mΩ :=
    fun t => (isStagedHistory_capSpec (τ := (t : ℝ≥0∞)) hb (hE' _ hw) (hreg' _) hℓ hwℓ).2.1 (ℓ + 1)
  have hset := fun t : ℝ≥0 =>
    Mg.exists_sb2LowerStageSets_marked (u := u) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ (t : ℝ≥0∞) hu₀
  choose A₁ A₂ hA₁m hA₂m hA₁σ hA₁l hA₂l hUl hUm hUloc hA₁c hA₂c hfill using hset
  refine ⟨capFiltration _ (StagedReg.regFam E _) (hreg' _) hℓ.le hwℓ hle (hup.2.1 k), A₁, A₂, fun t => rfl,
    fun t => ⟨(hUm t).mono (sup_le (hup.2.1 k) (hle t)) le_rfl, fun ω => ⟨union_subset (hA₁c t ω).1 (hA₂c t ω).1, ?_⟩,
      hA₁l t, hA₂l t, hUl t, hUloc t, hfill t⟩⟩
  have e : H \ (A₁ t ω ∪ A₂ t ω) = (H \ A₁ t ω) ∩ (H \ A₂ t ω) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff, not_or]
    tauto
  rw [e]
  exact (hA₁c t ω).2.inter (hA₂c t ω).2

end SB2

end InteractingSLE.Theorem14.SB.Mj

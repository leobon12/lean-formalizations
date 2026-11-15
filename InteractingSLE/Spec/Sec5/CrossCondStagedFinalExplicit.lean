/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalPast
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanRep
import InteractingSLE.Spec.Supplement.GW2ScheduleWit

/-!
# The staged cross-conditioning law: the staged prefix's own mean with the explicit stage word

Packet PROVE-CROSSCOND-STAGED4 (S2). PROVE-CROSSCOND-STAGED2's own mean of a staged prefix
(`Staged.exists_stageChartLaw`, `ae_forall_apply_eq_stageMean`, `exists_rep_stageMean`) carries an abstract word `β`
read off the past. The per-sample identification (`eqOn_imgChart_pastWord`) needs the **explicit** word: the iterated
stop word of the records, `wWord … (ℓ + 1) = pastWord (stopWord κ) c₀ spec.1 θ (ℓ + 1) (pastMap (ℓ + 1))`, the witness
of the landed `GW2Schedule.stageWitness_all`. Here:

* **`exists_stageChartLawW`**: the staged chart law with the explicit word (`stageLaw` replaced by `stageWitness_all`;
  the word after the pieces is `wWord … (ℓ + 1)` by `wWord_succ`);
* `stageMeanW` (the explicit stage mean `𝔤_{ℓ+1} ∘ F − χ ℓ_F`), **`ae_apply_eq_stageChartMeanW`**,
  **`ae_forall_apply_eq_stageMeanW`**, **`exists_rep_stageMeanW`**: the own mean and its representative in the form of
  `hwA`, with the explicit word (the landed proofs, `β` replaced by the explicit word);
* **`stage_records`**, **`stage_hw`**: on the success event, the records of the pieces are the pieces of the
  concatenated record driver `rpath (catN (stageDrv ℓ ω) T ℓ)` with own times `(Δ i).toNNReal` — the hypotheses `hw`,
  `htS` of `eqOn_imgChart_pastWord`.

R48: no Theorem 1.2/1.3 input (`stageWitness_all` needs only `IsStopLaw` and the staged history's own clauses).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

universe u

open Exist Exist.Staged Exist.StagedLaw Restart Theorem14.GW2Schedule Sec7.StripSideHeightProb LocalSets
open InteractingSLE.Sec5.CrossCond.Staged

section Explicit

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}

/-- **The staged chart law with the explicit word**: on the success event the field read in the chart after the pieces
`0, …, ℓ` is, given the records, the GFF with the data of the iterated stop word `wWord … (ℓ + 1)`. -/
theorem exists_stageChartLawW (c₀ : BoundaryWord) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) :
    ∃ Y : Ω → DistOn upperHalfPlaneOpens, Measurable Y ∧
      (∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
        IsChartTransport (stageChart κ b jumps spec Δ E ℓ ω) 1 0 (chiC κ) (h ω) (Y ω)) ∧
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
        P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | pastSigma κ b jumps spec E (ℓ + 1)] ω =
          gaussCF (wWord θ (stopWord κ) c₀ κ b jumps spec E (ℓ + 1) ω) ψ := by
  have hβA := isStopLaw_stopWord.{u} hκ
  obtain ⟨hβ, hY, hpath, hker⟩ := Theorem14.GW2Schedule.stageWitness_all θ Δ (stopWord κ) c₀ hβA hκ hb hc₀J hc₀ hh
    hgw hprog hΔ hS.1 hreg hS.2.2.2 ℓ
  set Y := Theorem14.GW2Schedule.wField κ b jumps spec h E ℓ with hYdef
  have hpost := post_stage (spec := spec) (E := E) (ℓ := ℓ) hβA runMeasStatement hκ hb hh
    (fun j _ => hS.1 j) (fun j _ => hreg j) (hS.2.2.2 ℓ) hβ hY hpath hker
  have hpm : Measurable (pastMap κ b jumps spec E (ℓ + 1)) :=
    measurable_pastMap runMeasStatement hb spec (fun j _ => hS.1 j) (fun j _ => hreg j) (ℓ + 1) le_rfl
  have hY' : Measurable fun ω => recField κ (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) (Y ω) :=
    Measurable.comp (g := fun q : RecData × DistOn upperHalfPlaneOpens => recField κ q.1 q.2)
      (f := fun ω => (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ), Y ω)) (measurable_recField κ)
      ((measurable_pi_iff.1 hpm (Fin.last ℓ)).prodMk hY)
  have hinstr : instrTime spec ℓ = Δ ℓ := by simp only [instrTime, hprog ℓ hℓ]
  have hang : instrAngle spec ℓ = θ ℓ := by simp only [instrAngle, hprog ℓ hℓ]
  have hlaunch : ∀ ω, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      (ExplState.run κ b jumps spec (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
    intro ω hω
    rw [(launches_run_gw2 hgw hprog hΔ _ hℓ).1 (hω.1.mono (Nat.le_succ ℓ))]
    exact Option.some_ne_none _
  refine ⟨_, hY', ?_, fun ψ => ?_⟩
  · filter_upwards [hpath] with ω hpω hω
    have hsℓ : AllSucc Δ (fun j => E j ω) ℓ := hω.1.mono (Nat.le_succ ℓ)
    obtain ⟨hconf, hlift, hT⟩ := hpω (hlaunch ω hω)
    have hchart : (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1 =
        succChart spec.1 Δ (fun j => E j ω) ℓ := ((run_gw2 hgw hprog hΔ _ ℓ hℓ.le).1 hsℓ).2
    have hT2 := isChartTransport_recField κ (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ)) (Y ω)
    have htrans := IsChartTransport.trans hconf (isConformal_recChart _) hlift (continuousOn_recChart_lift _) hT hT2
    -- the composite chart is the iterated chart of the record drivers
    obtain ⟨hdℓ, hgℓ⟩ := stageDrv_eq_of_mem hgw hprog hΔ hℓ hω (Nat.lt_succ_self ℓ)
    have hrecℓ : pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ) = recOf (Δ ℓ) (E ℓ ω) := by
      rw [pastMap_of_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ E hℓ hω.1]
      rfl
    have hcomp : (ExplState.run κ b jumps spec (fun j => E j ω) ℓ).2.2.2.2.1.trans
        (recChart (pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))) =
        iterChart spec.1 (stageDrv κ b jumps spec E ℓ ω) (fun j => (Δ j).toNNReal) ℓ := by
      rw [hchart, recChart, LocalExt.histChart, trans_id_loewner, hrecℓ, histTime_recHist_recOf,
        stopTime_eq_of_lt (hω.1 ℓ (Nat.lt_succ_self ℓ))]
      have e : LocalExt.histDrv (recHist (recOf (Δ ℓ) (E ℓ ω))) = stageDrv κ b jumps spec E ℓ ω ℓ := hdℓ.symm
      rw [e]
      refine succChart_loewner_eq_iterChart spec.1 Δ (fun j => E j ω) (stageDrv κ b jumps spec E ℓ ω)
        (fun j => (Δ j).toNNReal) ℓ fun j hj => ?_
      obtain ⟨hdj, hgj⟩ := stageDrv_eq_of_mem hgw hprog hΔ hℓ hω (Nat.lt_succ_of_lt hj)
      refine ⟨?_, stopTime_eq_of_lt (hω.1 j (Nat.lt_succ_of_lt hj))⟩
      rw [hdj]
      exact stopDrv_eq_rpath_recW (hreg j ω) hgj
    rw [hcomp] at htrans
    exact isChartTransport_catChartN_of_iterChart spec.1 (continuous_stageDrv ℓ ω) (stageDrv_zero ℓ ω) ℓ htrans
  · filter_upwards [hpost.2 ψ] with ω h1 hω
    have hfin : min (instrTime spec ℓ) (E ℓ ω).2 ≠ ⊤ := by
      rw [hinstr]
      exact ne_top_of_le_ne_top (hΔ ℓ) (min_le_left _ _)
    have h2 := h1 (hlaunch ω hω) hfin
    rw [hang] at h2
    rw [Theorem14.GW2Schedule.wWord_succ]
    exact h2

/-- **The explicit stage mean**: the mean of the iterated stop word read in the chart after the pieces, minus `χ` times
the chart's lift. -/
def stageMeanW (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (Δ : ℕ → ℝ≥0∞)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℕ → ℝ) (c₀ : BoundaryWord) (ℓ : ℕ) (ω : Ω) (z : ℂ) : ℝ :=
  (wWord θ (stopWord κ) c₀ κ b jumps spec E (ℓ + 1) ω).mean ((stageChart κ b jumps spec Δ E ℓ ω).1 z) -
    chiC κ * (stageChart κ b jumps spec Δ E ℓ ω).2.2 z

omit mΩ [StandardBorelSpace Ω] in
theorem isSorted_wWord_succ (c₀ : BoundaryWord) (ℓ : ℕ) (ω : Ω) :
    (wWord θ (stopWord κ) c₀ κ b jumps spec E (ℓ + 1) ω).IsSorted := by
  rw [wWord_succ]
  exact isSorted_stopWord κ _

omit mΩ [StandardBorelSpace Ω] in
theorem harmonicOnNhd_stageMeanW (c₀ : BoundaryWord) (ℓ : ℕ) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω)
      (stageChart κ b jumps spec Δ E ℓ ω).dom :=
  harmonicOnNhd_catChartN_mean κ spec.1 (continuous_stageDrv ℓ ω) (stageDrv_zero ℓ ω) ℓ
    ((wWord θ (stopWord κ) c₀ κ b jumps spec E (ℓ + 1) ω).isBoundedHarmonicExtension_mean
      (isSorted_wWord_succ c₀ ℓ ω)).1

/-- **The staged prefix's own mean with the explicit word**, one test function at a time. -/
theorem ae_apply_eq_stageChartMeanW (c₀ : BoundaryWord) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E (ℓ + 1)) A
      (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stageChart κ b jumps spec Δ E ℓ ω).dom))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      tsupport φ ⊆ (stageChart κ b jumps spec Δ E ℓ ω).dom →
      g ω φ = (∫ z, stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z * φ z) - ∫ z, u₀ z * φ z := by
  obtain ⟨Y, hY, htr, hlaw⟩ := exists_stageChartLawW c₀ hκ hb hc₀J hc₀ hh hS hreg hgw hprog hΔ hℓ
  exact fun φ => ae_apply_eq_chartMean_of_chartLaw (hS.2.1 (ℓ + 1)) (isConformal_stageChart Δ ℓ)
    (measurableSet_dom_stageChart Δ ℓ) (measurable_indicator_fwd_stageChart Δ ℓ)
    (measurableSet_closedBall_subset_stageChart Δ ℓ) (measurable_indicator_lift_stageChart Δ ℓ)
    (continuousOn_lift_stageChart Δ ℓ) hh hu₀ hY (measurableSet_stageGood hgw hprog hΔ hℓ) htr hlaw hA hloc hmark
    hAD hg φ

/-- **The staged prefix's own mean, for every test function at once**: in the setting of
`ae_apply_eq_stageChartMean`, almost surely on the success event, for every `φ` supported in the domain `D` after the
pieces, `g(φ) = ∫ (stageMean − 𝔥₀) φ`. -/
theorem ae_forall_apply_eq_stageMeanW (c₀ : BoundaryWord) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E (ℓ + 1)) A
      (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stageChart κ b jumps spec Δ E ℓ ω).dom))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ → ∀ φ : TestOn upperHalfPlaneOpens,
      tsupport φ ⊆ (stageChart κ b jumps spec Δ E ℓ ω).dom →
      g ω φ = ∫ z, (stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z - u₀ z) * φ z := by
  classical
  have hmean := ae_apply_eq_stageChartMeanW c₀ hκ hb hc₀J hc₀ hh hS hreg hgw hprog hΔ hℓ hu₀ hA hloc hmark hAD hg
  set G := stageGood κ b jumps spec Δ E ℓ with hG
  set D : Ω → Set ℂ := fun ω => ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) with hD
  -- the open set on which the representation is exchanged: `D` on the success event, `∅` off it
  set A' : Ω → Set ℂ := fun ω => if ω ∈ G then H \ D ω else H with hA'
  have hDH : ∀ ω, D ω ⊆ H := fun ω => (isConformal_stageChart Δ ℓ ω).dom_subset
  have hA'G : ∀ ω, ω ∈ G → H \ A' ω = D ω := fun ω hω => by
    simp only [hA', hω, ↓reduceIte, sdiff_sdiff_right_self]
    exact inter_eq_right.2 (hDH ω)
  have hA'n : ∀ ω, ω ∉ G → H \ A' ω = ∅ := fun ω hω => by simp only [hA', hω, ↓reduceIte, sdiff_self]
  set m : Ω → ℂ → ℝ := fun ω z => stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z - u₀ z with hm
  have hzero : ∀ ω, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A' ω → ω ∉ G → φ = 0 := by
    intro ω φ hφ hω
    rw [hA'n ω hω] at hφ
    exact Restart.eq_zero_of_tsupport_subset_empty hφ
  have hharm : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A' ω) := by
    filter_upwards [hg.2.1, hAD] with ω hgω hADω
    by_cases hω : ω ∈ G
    · obtain ⟨v, hv, hvg⟩ := hgω
      rw [hA'G ω hω]
      exact ⟨v, fun z hz => hv z ((hADω hω).1 hz), fun φ hφ => hvg φ (hφ.trans (hADω hω).1)⟩
    · refine ⟨fun _ => 0, fun z hz => ?_, fun φ hφ => ?_⟩
      · rw [hA'n ω hω] at hz
        exact absurd hz (notMem_empty z)
      · rw [hzero ω φ hφ hω, map_zero]
        simp
  have hopen : ∀ᵐ ω ∂P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · rw [hA'G ω hω]; exact (stageChart κ b jumps spec Δ E ℓ ω).dom.isOpen
    · rw [hA'n ω hω]; exact isOpen_empty
  have hmh : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ G
    · rw [hA'G ω hω]
      intro z hz
      exact (harmonicOnNhd_stageMeanW c₀ ℓ ω z hz).sub (hu₀.1 z (hDH ω hz))
    · rw [hA'n ω hω]
      intro z hz
      exact absurd hz (notMem_empty z)
  have hφ : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ H \ A' ω → g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hmean φ] with ω hω hsupp
    by_cases hωG : ω ∈ G
    · rw [hA'G ω hωG] at hsupp
      rw [hω hωG hsupp]
      have hc1 : ContinuousOn (stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω) (D ω) := fun z hz =>
        (harmonicOnNhd_stageMeanW c₀ ℓ ω z hz).1.continuousAt.continuousWithinAt
      have hc2 : ContinuousOn u₀ (D ω) := fun z hz => (hu₀.1 z (hDH ω hz)).1.continuousAt.continuousWithinAt
      have hi1 := WholeField.integrable_mul_testOn hc1 φ hsupp
      have hi2 := WholeField.integrable_mul_testOn hc2 φ hsupp
      change (∫ z, stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z * φ z) - ∫ z, u₀ z * φ z = _
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hm, stageMeanW]
      ring
    · rw [hzero ω φ hsupp hωG, map_zero]
      simp
  filter_upwards [WangWu.ae_forall_apply_eq_of_forall_ae hharm hopen hmh hφ] with ω hω hωG φ hsupp
  exact hω φ (by rw [hA'G ω hωG]; exact hsupp)

/-- **A representative of the staged prefix's own mean in the form of `hwA`**: if the explored set's complement is the
domain after the pieces on the success event, there is `wA` harmonic on `ℍ ∖ A` representing `g` there almost
surely for every test function, equal to `stageMean − 𝔥₀` on the success event. -/
theorem exists_rep_stageMeanW (c₀ : BoundaryWord) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) (hh : IsGFFWithBoundaryData P h b jumps)
    (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastSigma κ b jumps spec E (ℓ + 1)) A
      (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ → H \ A ω = (stageChart κ b jumps spec Δ E ℓ ω).dom)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∃ wA : Ω → ℂ → ℝ,
      (∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (wA ω) (H \ A ω) ∧
        ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, wA ω z * φ z) ∧
      ∀ ω, ω ∈ stageGood κ b jumps spec Δ E ℓ → H \ A ω = (stageChart κ b jumps spec Δ E ℓ ω).dom →
        wA ω = fun z => stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z - u₀ z := by
  classical
  have hAD' : ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
      ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stageChart κ b jumps spec Δ E ℓ ω).dom) := by
    filter_upwards [hAD] with ω hω hωG
    rw [hω hωG, sdiff_self]
    exact ⟨subset_rfl, isOpen_empty⟩
  have hall := ae_forall_apply_eq_stageMeanW c₀ hκ hb hc₀J hc₀ hh hS hreg hgw hprog hΔ hℓ hu₀ hA hloc hmark hAD' hg
  set good : Ω → Prop := fun ω => ω ∈ stageGood κ b jumps spec Δ E ℓ ∧
    H \ A ω = (stageChart κ b jumps spec Δ E ℓ ω).dom with hgood
  refine ⟨fun ω => if hω : good ω then fun z => stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z - u₀ z else
    if hr : IsHarmonicDistOn (g ω) (H \ A ω) then Classical.choose hr else fun _ => 0, ?_, fun ω hω hωD => ?_⟩
  · filter_upwards [hall, hg.2.1] with ω hω hgω
    by_cases hgd : good ω
    · simp only [hgd, ↓reduceDIte]
      refine ⟨?_, fun φ hφ => ?_⟩
      · rw [hgd.2]
        intro z hz
        exact (harmonicOnNhd_stageMeanW c₀ ℓ ω z hz).sub
          (hu₀.1 z ((isConformal_stageChart Δ ℓ ω).dom_subset hz))
      · rw [hgd.2] at hφ
        exact hω hgd.1 φ hφ
    · simp only [hgd, hgω, ↓reduceDIte]
      exact Classical.choose_spec hgω
  · have hgd : good ω := ⟨hω, hωD⟩
    simp only [hgd, ↓reduceDIte]

end Explicit
/-! ### The records of a staged flow program are the pieces of the concatenated record driver -/

section Records

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}

theorem startT_congr {T T' : ℕ → ℝ} {i : ℕ} (h : ∀ j < i, T j = T' j) : startT T i = startT T' i :=
  Finset.sum_congr rfl fun j hj => h j (Finset.mem_range.1 hj)

/-- **The records on the success event**: the own time of record `i` is `(Δ i).toNNReal` and its driver is the record
driver `stageDrv ℓ ω i`. -/
theorem stage_records (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ}
    (hℓ : ℓ < spec.2.2.length) {ω : Ω} (hω : ω ∈ stageGood κ b jumps spec Δ E ℓ) {i : ℕ} (hi : i ≤ ℓ) :
    recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω) i = ((Δ i).toNNReal : ℝ) ∧
      recSeqW (pastMap κ b jumps spec E (ℓ + 1) ω) i = Ito.rpath (stageDrv κ b jumps spec E ℓ ω i) := by
  have hi' : i < ℓ + 1 := Nat.lt_succ_of_le hi
  have hpm := pastMap_of_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ E hℓ hω.1
  have e : pastMap κ b jumps spec E (ℓ + 1) ω ⟨i, hi'⟩ = recOf (Δ i) (E i ω) := by rw [hpm]
  refine ⟨?_, ?_⟩
  · simp only [recSeqT, hi', ↓reduceDIte]
    rw [e, rtime_recOf, stopTime_eq_of_lt (hω.1 i hi')]
  · funext x
    simp only [recSeqW, hi', ↓reduceDIte, Ito.rpath, stageDrv]
    rfl

/-- **The record drivers are the pieces of the concatenated record driver** (the hypothesis `hw` of
`eqOn_imgChart_pastWord`), on the success event. -/
theorem stage_hw (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ}
    (hℓ : ℓ < spec.2.2.length) {ω : Ω} (hω : ω ∈ stageGood κ b jumps spec Δ E ℓ) (i : ℕ) :
    EqOn (recSeqW (pastMap κ b jumps spec E (ℓ + 1) ω) i)
      (shiftDrive (Ito.rpath (catN (stageDrv κ b jumps spec E ℓ ω) (fun j => (Δ j).toNNReal) ℓ))
        (startT (recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω)) i))
      (Icc 0 (recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω) i)) := by
  by_cases hi : i ≤ ℓ
  · obtain ⟨hT, hW⟩ := stage_records hgw hprog hΔ hℓ hω hi
    have hS : startT (recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω)) i =
        startT (fun j => (((fun j => (Δ j).toNNReal) j : ℝ≥0) : ℝ)) i :=
      startT_congr fun j hj => (stage_records hgw hprog hΔ hℓ hω (by omega)).1
    rw [hT, hW, hS]
    exact shiftDrive_rpath_catN (stageDrv_zero ℓ ω) hi
  · have hn : ¬ i < ℓ + 1 := by omega
    intro r hr
    have h0 : recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω) i = 0 := by simp only [recSeqT, hn, ↓reduceDIte]
    rw [h0] at hr
    obtain rfl : r = 0 := le_antisymm hr.2 hr.1
    simp only [recSeqW, hn, ↓reduceDIte, shiftDrive_zero_apply]

/-- The total own time of the records on the success event is the cumulative time of the stage chart. -/
theorem stage_total (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ}
    (hℓ : ℓ < spec.2.2.length) {ω : Ω} (hω : ω ∈ stageGood κ b jumps spec Δ E ℓ) :
    startT (recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω)) (ℓ + 1) = (cumT (fun j => (Δ j).toNNReal) ℓ : ℝ) := by
  rw [startT_congr (T' := fun j => (((fun j => (Δ j).toNNReal) j : ℝ≥0) : ℝ))
    fun j hj => (stage_records hgw hprog hΔ hℓ hω (by omega)).1, ← coe_startN, ← cumT_eq_startN]

/-- Positive own times give positive record times. -/
theorem stage_pos (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (hΔ0 : ∀ j, Δ j ≠ 0) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {ω : Ω} (hω : ω ∈ stageGood κ b jumps spec Δ E ℓ) :
    ∀ i ≤ ℓ, 0 < recSeqT (pastMap κ b jumps spec E (ℓ + 1) ω) i := fun i hi => by
  rw [(stage_records hgw hprog hΔ hℓ hω hi).1]
  exact NNReal.coe_pos.2 (ENNReal.toNNReal_pos (hΔ0 i) (hΔ i))

/-- **The explicit stage mean in the coordinates of the concatenated trace**: `𝔤_{ℓ+1} ∘ f_t − χ arg f_t′` at
`z − x₀` for the concatenated record driver and the cumulative time. -/
theorem stageMeanW_eq (c₀ : BoundaryWord) (ℓ : ℕ) (ω : Ω) (z : ℂ) :
    stageMeanW κ b jumps spec Δ E θ c₀ ℓ ω z =
      (wWord θ (stopWord κ) c₀ κ b jumps spec E (ℓ + 1) ω).mean
          (QuantumZipper.fwdMap (Ito.rpath (catN (stageDrv κ b jumps spec E ℓ ω) (fun j => (Δ j).toNNReal) ℓ))
            (cumT (fun j => (Δ j).toNNReal) ℓ) (z - spec.1)) -
        chiC κ * ((QuantumZipper.logDerivFwd (Ito.rpath (catN (stageDrv κ b jumps spec E ℓ ω)
          (fun j => (Δ j).toNNReal) ℓ)) (cumT (fun j => (Δ j).toNNReal) ℓ) (z - spec.1)).im + 0) := by
  simp only [stageMeanW, stageChart, catChartN, recenter_loewner_fst, recenter_loewner_lift]
  rfl

end Records

end InteractingSLE.Sec5.CrossCond.StagedFinal

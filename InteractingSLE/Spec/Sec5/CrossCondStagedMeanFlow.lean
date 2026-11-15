/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanCat
import InteractingSLE.Spec.Supplement.GW2SchedulePast

/-!
# The staged prefix's own mean, III: every stage of a flow program

Packet PROVE-CROSSCOND-STAGED2 (PROVE-CROSSCOND-STAGED §5.1 (ii)). For a staged history (frozen `IsStagedHistory`) of
a flow program (`Theorem14.GW2Schedule.IsFlowProg`: instructions `(θ_j, Δ_j)`, angle `θ_j` for the finite own time
`Δ_j`, the GW2 convention) — the angle-varying staged prefixes `α₁ ∪ ⋯ ∪ α_{ℓ+1}` of Proposition 5.9 (spec
pp. 142–148), GW2 and GB9 — and **any number of pieces**:

* `stageChart … ℓ ω`: the chart after the stopped pieces `0, …, ℓ`, read off the retained records (the recentred Loewner
  chart of the concatenated record drivers, `catChartN`); it is measurable in the retained past `pastSigma (ℓ + 1)`;
* **`ae_condExp_cexp_stageChart`** (the field given the records of all the stopped pieces, in the original
  coordinate): on the success event `stageGood` (every piece stopped before its lifetime, good records), for every test
  function `φ` supported in the domain `D` left after the pieces,
  `E[e^{i h(φ)} | 𝓟_{ℓ+1}] = exp(i ∫ (𝔤 ∘ F − χ ℓ) φ − ½ ‖φ‖²_{H⁻¹(D)})` with `𝔤` the bounded harmonic mean of the stop
  word `stopWord κ (β, θ_ℓ, record_ℓ)` (`β` the word of the conditional field at the launch of the last piece, read off
  the past before it) — the new force points created at the switch are the seed marks of the stop word;
* **`ae_apply_eq_stageChartMean`** (the staged prefix's own mean): every version of the local-set mean of a set retained
  with the records (local, history-avoidance local for `𝓟_{ℓ+1}`, `D` a clopen part of its complement) is
  `∫ (𝔤 ∘ F − χ ℓ) φ − ∫ 𝔥₀ φ` on `D`.

This is the landed single-stage law (`Exist.StagedLaw.stageLaw`, `post_stage`, by induction over the stages) read
through `Sec5.CrossCond.Staged.ae_condExp_cexp_of_chartLaw`, with the run's chart identified with the chart of the
concatenation (`iterChart_agree`). The two-angle case is `Sec7.StripSideHeightProb.ae_condExp_cexp_stopChart`.
Conditional helpers with distinct names; R48: no Theorem 1.2/1.3 input (`stageLaw` needs only the landed
`isStopLaw_stopWord` and `runMeasStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Staged

universe u

open Exist Exist.Staged Exist.StagedLaw Restart Theorem14.GW2Schedule Sec7.StripSideHeightProb LocalSets

/-! ### Deterministic: the run's chart is the iterated chart -/

section Det

/-- The composite with a centred Loewner chart is the Loewner stage. -/
theorem trans_id_loewner (c : Chart) (W : ℝ → ℝ) (t : ℝ) : c.trans (Chart.id.loewner W t) = c.loewner W t := by
  refine Prod.ext rfl (Prod.ext rfl ?_)
  funext z
  change (QuantumZipper.logDerivFwd W t (c.1 z)).im + 0 + c.2.2 z = (QuantumZipper.logDerivFwd W t (c.1 z)).im + c.2.2 z
  rw [add_zero]

/-- **The chart after `k` successful pieces, followed by piece `k`, is the iterated chart** of drivers agreeing with
the stopped drivers. -/
theorem succChart_loewner_eq_iterChart (x₀ : ℝ) (Δ : ℕ → ℝ≥0∞) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (w : ℕ → ℝ≥0 → ℝ) (T : ℕ → ℝ≥0) :
    ∀ k, (∀ j < k, stopDrv (Δ j) (D j) = Ito.rpath (w j) ∧ stopTime (Δ j) (D j) = T j) →
      (succChart x₀ Δ D k).loewner (Ito.rpath (w k)) (T k) = iterChart x₀ w T k
  | 0, _ => rfl
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := hk k (Nat.lt_succ_self k)
    have ih := succChart_loewner_eq_iterChart x₀ Δ D w T k fun j hj => hk j (Nat.lt_succ_of_lt hj)
    change ((succChart x₀ Δ D k).loewner (stopDrv (Δ k) (D k)) (stopTime (Δ k) (D k))).loewner _ _ = _
    rw [h1, h2, ih]
    rfl

/-- The stopped driver of a regular successful piece with a good record is the record driver. -/
theorem stopDrv_eq_rpath_recW {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) : stopDrv t e = Ito.rpath (recW (recOf t e)) := by
  funext x
  change (retOf t e).1 x.toNNReal = LocalExt.histDrv (recHist (recOf t e)) x.toNNReal
  rw [histDrv_recHist he hg]

theorem stopTime_eq_of_lt {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (ht : t < e.2) :
    stopTime t e = ((t.toNNReal : ℝ≥0) : ℝ) := by
  simp only [stopTime, min_eq_left ht.le]

theorem histTime_recHist_recOf (t : ℝ≥0∞) (e : (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ((LocalExt.histTime (recHist (recOf t e)) : ℝ≥0) : ℝ) = stopTime t e := rfl

end Det

/-! ### The records, the chart after the pieces and the success event -/

section Records

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The record drivers of the pieces `0, …, ℓ`, read off the retained past before `ℓ + 1` (`0` after `ℓ`). -/
def stageDrv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ)
    (ω : Ω) (j : ℕ) : ℝ≥0 → ℝ :=
  if hj : j < ℓ + 1 then recW (pastMap κ b jumps spec E (ℓ + 1) ω ⟨j, hj⟩) else fun _ => 0

/-- **The chart after the stopped pieces `0, …, ℓ`**, read off the retained records: the recentred Loewner chart of the
concatenated record drivers at the cumulative own time. -/
def stageChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (Δ : ℕ → ℝ≥0∞)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ) (ω : Ω) : Chart :=
  catChartN spec.1 (stageDrv κ b jumps spec E ℓ ω) (fun j => (Δ j).toNNReal) ℓ

/-- **The success event**: the pieces `0, …, ℓ` stopped before their lifetimes, with good records. -/
def stageGood (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (spec : ExplSpec) (Δ : ℕ → ℝ≥0∞)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ℓ : ℕ) : Set Ω :=
  {ω | AllSucc Δ (fun j => E j ω) (ℓ + 1)} ∩
    pastMap κ b jumps spec E (ℓ + 1) ⁻¹' {u | ∀ i, LocalExt.IsDrvGood (recHist (u i))}

theorem continuous_stageDrv (ℓ : ℕ) (ω : Ω) (j : ℕ) : Continuous (stageDrv κ b jumps spec E ℓ ω j) := by
  unfold stageDrv
  split_ifs
  · exact LocalExt.continuous_histDrv _
  · exact continuous_const

theorem stageDrv_zero (ℓ : ℕ) (ω : Ω) (j : ℕ) : stageDrv κ b jumps spec E ℓ ω j 0 = 0 := by
  unfold stageDrv
  split_ifs
  · exact LocalExt.histDrv_zero _
  · rfl

theorem isConformal_stageChart (Δ : ℕ → ℝ≥0∞) (ℓ : ℕ) (ω : Ω) :
    (stageChart κ b jumps spec Δ E ℓ ω).IsConformal :=
  isConformal_catChartN spec.1 (continuous_stageDrv ℓ ω) (stageDrv_zero ℓ ω) ℓ

theorem continuousOn_lift_stageChart (Δ : ℕ → ℝ≥0∞) (ℓ : ℕ) (ω : Ω) :
    ContinuousOn (stageChart κ b jumps spec Δ E ℓ ω).2.2 (stageChart κ b jumps spec Δ E ℓ ω).dom :=
  continuousOn_lift_catChartN spec.1 (continuous_stageDrv ℓ ω) (stageDrv_zero ℓ ω) ℓ

/-- The record drivers are measurable in the retained past. -/
theorem measurable_stageDrv_apply (ℓ j : ℕ) (s : ℝ≥0) :
    Measurable[pastSigma κ b jumps spec E (ℓ + 1)] fun ω => stageDrv κ b jumps spec E ℓ ω j s := by
  have hp : Measurable[pastSigma κ b jumps spec E (ℓ + 1)] (pastMap κ b jumps spec E (ℓ + 1)) := by
    rw [pastSigma_eq_comap]
    exact comap_measurable _
  by_cases hj : j < ℓ + 1
  · have e : (fun ω => stageDrv κ b jumps spec E ℓ ω j s) =
        (fun u : PastData (ℓ + 1) => recW (u ⟨j, hj⟩) s) ∘ pastMap κ b jumps spec E (ℓ + 1) := by
      funext ω
      simp only [stageDrv, hj, ↓reduceDIte, Function.comp_apply]
    rw [e]
    exact ((LocalExt.measurable_histDrv_apply (nL := 0) (nR := 0) s).comp
      (measurable_recHist.comp (measurable_pi_apply _))).comp hp
  · have e : (fun ω => stageDrv κ b jumps spec E ℓ ω j s) = fun _ => 0 := by
      funext ω
      simp only [stageDrv, hj, ↓reduceDIte]
    rw [e]
    exact measurable_const

theorem measurableSet_dom_stageChart (Δ : ℕ → ℝ≥0∞) (ℓ : ℕ) (z : ℂ) :
    MeasurableSet[pastSigma κ b jumps spec E (ℓ + 1)] {ω | z ∈ (stageChart κ b jumps spec Δ E ℓ ω).dom} :=
  measurableSet_mem_dom_catChartN (fun j => (Δ j).toNNReal) spec.1 (fun j ω => continuous_stageDrv ℓ ω j)
    (fun j ω => stageDrv_zero ℓ ω j) (fun j s => measurable_stageDrv_apply ℓ j s) ℓ z

theorem measurable_indicator_fwd_stageChart (Δ : ℕ → ℝ≥0∞) (ℓ : ℕ) (z : ℂ) :
    Measurable[pastSigma κ b jumps spec E (ℓ + 1)] ({ω | z ∈ (stageChart κ b jumps spec Δ E ℓ ω).dom}.indicator
      fun ω => (stageChart κ b jumps spec Δ E ℓ ω).1 z) :=
  measurable_indicator_fwd_catChartN (fun j => (Δ j).toNNReal) spec.1 (fun j ω => continuous_stageDrv ℓ ω j)
    (fun j ω => stageDrv_zero ℓ ω j) (fun j s => measurable_stageDrv_apply ℓ j s) ℓ z

theorem measurable_indicator_lift_stageChart (Δ : ℕ → ℝ≥0∞) (ℓ : ℕ) (z : ℂ) :
    Measurable[pastSigma κ b jumps spec E (ℓ + 1)] ({ω | z ∈ (stageChart κ b jumps spec Δ E ℓ ω).dom}.indicator
      fun ω => (stageChart κ b jumps spec Δ E ℓ ω).2.2 z) :=
  measurable_indicator_lift_catChartN (fun j => (Δ j).toNNReal) spec.1 (fun j ω => continuous_stageDrv ℓ ω j)
    (fun j ω => stageDrv_zero ℓ ω j) (fun j s => measurable_stageDrv_apply ℓ j s) ℓ z

theorem measurableSet_closedBall_subset_stageChart (Δ : ℕ → ℝ≥0∞) (ℓ : ℕ) (z : ℂ) (ε : ℝ) :
    MeasurableSet[pastSigma κ b jumps spec E (ℓ + 1)]
      {ω | Metric.closedBall z ε ⊆ (stageChart κ b jumps spec Δ E ℓ ω).dom} :=
  measurableSet_closedBall_subset_dom_catChartN (fun j => (Δ j).toNNReal) spec.1
    (fun j ω => continuous_stageDrv ℓ ω j) (fun j ω => stageDrv_zero ℓ ω j)
    (fun j s => measurable_stageDrv_apply ℓ j s) ℓ z ε

variable {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}

/-- **The success event is an event of the retained past.** -/
theorem measurableSet_stageGood (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) :
    MeasurableSet[pastSigma κ b jumps spec E (ℓ + 1)] (stageGood κ b jumps spec Δ E ℓ) := by
  refine (measurableSet_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ E hℓ).inter ?_
  rw [pastSigma_eq_comap]
  refine ⟨_, ?_, rfl⟩
  have e : {u : PastData (ℓ + 1) | ∀ i, LocalExt.IsDrvGood (recHist (u i))} =
      ⋂ i : Fin (ℓ + 1), (fun u : PastData (ℓ + 1) => recHist (u i)) ⁻¹' {y | LocalExt.IsDrvGood y} := by
    ext u
    simp
  rw [e]
  exact MeasurableSet.iInter fun i =>
    (measurable_recHist.comp (measurable_pi_apply i)) LocalExt.measurableSet_isDrvGood

/-- On the success event, the record drivers are the records of the stopped pieces. -/
theorem stageDrv_eq_of_mem (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) {ω : Ω} (hω : ω ∈ stageGood κ b jumps spec Δ E ℓ) {j : ℕ}
    (hj : j < ℓ + 1) :
    stageDrv κ b jumps spec E ℓ ω j = recW (recOf (Δ j) (E j ω)) ∧
      LocalExt.IsDrvGood (recHist (recOf (Δ j) (E j ω))) := by
  have hpm := pastMap_of_allSucc (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ E hℓ hω.1
  have hgood := hω.2 ⟨j, hj⟩
  have e : pastMap κ b jumps spec E (ℓ + 1) ω ⟨j, hj⟩ = recOf (Δ j) (E j ω) := by rw [hpm]
  refine ⟨?_, ?_⟩
  · simp only [stageDrv, hj, ↓reduceDIte, e]
  · rw [← e]
    exact hgood

end Records

/-! ### The staged law after the stopped pieces, in the original coordinate -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℕ → ℝ} {Δ : ℕ → ℝ≥0∞}

/-- **The staged law after the stopped pieces `0, …, ℓ`, in the chart read off the records**: a word `β` read off the
past before the last piece and the field `Y` read in the chart after the pieces such that, on the success event, `Y`
is `h` read in `stageChart` and, given the records of all the pieces, `Y` has the Gaussian characteristic functional of
the stop word `stopWord κ (β, θ_ℓ, record_ℓ)`. (The landed `stageLaw` and `post_stage`, with the run's chart identified
with the chart of the concatenated record drivers.) -/
theorem exists_stageChartLaw (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → DistOn upperHalfPlaneOpens),
      Measurable[pastSigma κ b jumps spec E ℓ] β ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
        IsChartTransport (stageChart κ b jumps spec Δ E ℓ ω) 1 0 (chiC κ) (h ω) (Y ω)) ∧
      ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
        P[fun ω' => Complex.exp (Complex.I * (Y ω' ψ : ℂ)) | pastSigma κ b jumps spec E (ℓ + 1)] ω =
          gaussCF (stopWord κ (β ω, θ ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))) ψ := by
  have hβA := isStopLaw_stopWord.{u} hκ
  obtain ⟨β, Y, hβ, hY, hpath, hker⟩ := stageLaw (spec := spec) (E := E) hβA runMeasStatement hκ hb hh ℓ
    (fun j _ => hS.1 j) (fun j _ => hreg j) (fun j _ => hS.2.2.2 j)
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
  refine ⟨β, _, hβ, hY', ?_, fun ψ => ?_⟩
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
    exact h2

/-- **The field given the records of all the stopped pieces, in the original coordinate** (any number of pieces of a
flow program; the multi-piece form of `Sec7.StripSideHeightProb.ae_condExp_cexp_stopChart`). On the success event,
for every test function `φ` supported in the domain `D` left after the pieces `0, …, ℓ`, conditionally on their
records, `(h, φ)` is Gaussian with mean `∫ (𝔤 ∘ F − χ ℓ) φ` and variance `‖φ‖²_{H⁻¹(D)}`: `F` the chart after the
pieces, `ℓ` its lift, `𝔤` the bounded harmonic mean of the stop word `stopWord κ (β, θ_ℓ, record_ℓ)`. -/
theorem ae_condExp_cexp_stageChart (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (hgw : spec.2.1 = true) (hprog : IsFlowProg spec.2.2 θ Δ)
    (hΔ : ∀ j, Δ j ≠ ⊤) {ℓ : ℕ} (hℓ : ℓ < spec.2.2.length) :
    ∃ β : Ω → BoundaryWord, Measurable[pastSigma κ b jumps spec E ℓ] β ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
        tsupport φ ⊆ (stageChart κ b jumps spec Δ E ℓ ω).dom →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | pastSigma κ b jumps spec E (ℓ + 1)] ω =
          Complex.exp (Complex.I * ((∫ z, ((stopWord κ (β ω, θ ℓ,
              pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))).mean ((stageChart κ b jumps spec Δ E ℓ ω).1 z) -
              chiC κ * (stageChart κ b jumps spec Δ E ℓ ω).2.2 z) * φ z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((stageChart κ b jumps spec Δ E ℓ ω).dom : Set ℂ) φ φ : ℝ) :
              ℂ)) := by
  obtain ⟨β, Y, hβ, hY, htr, hlaw⟩ := exists_stageChartLaw hκ hb hh hS hreg hgw hprog hΔ hℓ
  exact ⟨β, hβ, fun φ => ae_condExp_cexp_of_chartLaw (hS.2.1 (ℓ + 1)) (isConformal_stageChart Δ ℓ)
    (measurableSet_dom_stageChart Δ ℓ) (measurable_indicator_fwd_stageChart Δ ℓ)
    (measurableSet_closedBall_subset_stageChart Δ ℓ) (measurable_indicator_lift_stageChart Δ ℓ)
    (continuousOn_lift_stageChart Δ ℓ) hh.1 hY (measurableSet_stageGood hgw hprog hΔ hℓ) htr hlaw φ⟩

/-- **The staged prefix's own mean** (PROVE-CROSSCOND-STAGED §5.1 (ii), any number of pieces): every version `g` of the
local-set mean of a set `A` retained with the records of the pieces `0, …, ℓ` (a local set of `h − 𝔥₀`,
history-avoidance local for `𝓟_{ℓ+1}`, whose complement contains the domain `D` after the pieces as a clopen part)
satisfies, on the success event, `g(φ) = ∫ (𝔤 ∘ F − χ ℓ) φ − ∫ 𝔥₀ φ` for every `φ` supported in `D`, with `𝔤` the
bounded harmonic mean of the stop word. -/
theorem ae_apply_eq_stageChartMean (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
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
    ∃ β : Ω → BoundaryWord, Measurable[pastSigma κ b jumps spec E ℓ] β ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ stageGood κ b jumps spec Δ E ℓ →
        tsupport φ ⊆ (stageChart κ b jumps spec Δ E ℓ ω).dom →
        g ω φ = (∫ z, ((stopWord κ (β ω, θ ℓ, pastMap κ b jumps spec E (ℓ + 1) ω (Fin.last ℓ))).mean
            ((stageChart κ b jumps spec Δ E ℓ ω).1 z) -
            chiC κ * (stageChart κ b jumps spec Δ E ℓ ω).2.2 z) * φ z) - ∫ z, u₀ z * φ z := by
  obtain ⟨β, Y, hβ, hY, htr, hlaw⟩ := exists_stageChartLaw hκ hb hh hS hreg hgw hprog hΔ hℓ
  exact ⟨β, hβ, fun φ => ae_apply_eq_chartMean_of_chartLaw (hS.2.1 (ℓ + 1)) (isConformal_stageChart Δ ℓ)
    (measurableSet_dom_stageChart Δ ℓ) (measurable_indicator_fwd_stageChart Δ ℓ)
    (measurableSet_closedBall_subset_stageChart Δ ℓ) (measurable_indicator_lift_stageChart Δ ℓ)
    (continuousOn_lift_stageChart Δ ℓ) hh hu₀ hY (measurableSet_stageGood hgw hprog hΔ hℓ) htr hlaw hA hloc hmark
    hAD hg φ⟩

end Main

end InteractingSLE.Sec5.CrossCond.Staged

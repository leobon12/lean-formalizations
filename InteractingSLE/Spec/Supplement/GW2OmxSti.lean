/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxRun
import InteractingSLE.Spec.Supplement.GW2GmBack
import InteractingSLE.Spec.Supplement.BRLeafGB6Aux
import InteractingSLE.Spec.Supplement.GW2aForceFlow
import InteractingSLE.Spec.Supplement.AbsMergeFlow
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Supplement.GW2LaterInt
import InteractingSLE.Spec.Sec5.Lemma56Stages

/-!
# GW2's open lines: the switching tips of a staged GW2 history are interior, almost surely

Packet PROVE-GW2-STAGEMEAN, R120 round (the kernel chain's premise). GB6's staged datum is given only at samples whose
earlier switching tips are interior (`GW2Later.SwitchTipsInterior`); the consumers of the chain carried
`∀ᵐ ω, AllSucc k → SwitchTipsInterior k` as a hypothesis (`hint` in `GW2LaterChain`, `GW2ConeQFixed`). It holds for
every staged flow history with positive durations and angles in `[−π/2, π/2]`:

* **`isInteriorStop_iff_traceAt`** (deterministic): for a regular piece that survives its duration `Δ` and is
  continuous with a trace up to `Δ`, the stop at `Δ` is interior iff the trace READER of the stopped record driver at
  `Δ` lies in `ℍ` (`LP.traceAt`, measurable);
* **`ae_switchTipsInterior`**: under the conditional law given the earlier pieces, piece `j` is a flow line of the
  launch field (`IsStagedHistory`), so its tip at the deterministic time `Δ_j > 0` is interior almost surely
  (`GW2aForce.flowFixedTimeInteriorStatement_of_thm13`, Theorem 1.3); the measurable reader moves this to `P`
  (`Sec5.Lemma56Stages.ae_of_ae_condExpKernel`); samples where an earlier piece failed are excluded by run equality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open GW2TipSystem GW2Schedule GW2Tip Exist Exist.Staged Exist.StagedLaw

/-- **An interior stop is read off the stopped record driver's trace** (deterministic). -/
theorem isInteriorStop_iff_traceAt {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {Δ : ℝ≥0}
    (hΔζ : (Δ : ℝ≥0∞) < e.2) (hc : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ min (Δ : ℝ≥0∞) e.2})
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace e.1 (min (Δ : ℝ≥0∞) e.2) η) :
    GW2Later.IsInteriorStop e.1 (Δ : ℝ≥0∞) ↔ LP.traceAt Δ (fun x : ℝ≥0 => rdrv (recOf (Δ : ℝ≥0∞) e) x) ∈ H := by
  have hmin : min (Δ : ℝ≥0∞) e.2 = Δ := min_eq_left hΔζ.le
  have hfin : min (Δ : ℝ≥0∞) e.2 ≠ ⊤ := by
    rw [hmin]
    exact ENNReal.coe_ne_top
  obtain ⟨η', hη', -⟩ := Gm.exists_isGeneratingTrace_rdrv_recOf he hfin hc hη
  set w' : ℝ≥0 → ℝ := fun x => rdrv (recOf (Δ : ℝ≥0∞) e) x with hw'
  have hw'eq : ∀ x, w' x = e.1 (min x Δ) := fun x => by
    show rdrv (recOf (Δ : ℝ≥0∞) e) (x : ℝ) = _
    rw [Gm.rdrv_recOf_eq he hfin hc x, hmin, ENNReal.toNNReal_coe]
  have hcI : ContinuousOn e.1 (Iic Δ) := hc.mono fun s hs => by
    rw [hmin]
    exact ENNReal.coe_le_coe.2 hs
  have hw'c : Continuous w' := by
    have e' : w' = fun x => e.1 (min x Δ) := funext hw'eq
    rw [e']
    exact hcI.comp_continuous (continuous_id.min continuous_const) fun x => min_le_right x Δ
  have hw'0 : w' 0 = 0 := by
    rw [hw'eq, min_eq_left zero_le]
    exact he.2.1
  have hstop : (fun r : ℝ≥0 => e.1 (min (r : ℝ≥0∞) (Δ : ℝ≥0∞)).toNNReal) =
      fun r : ℝ≥0 => w' (min (r : ℝ≥0∞) (Δ : ℝ≥0∞)).toNNReal := by
    funext r
    rw [hw'eq, ← ENNReal.coe_min, ENNReal.toNNReal_coe, min_eq_left (min_le_right r Δ)]
  have hiff : GW2Later.IsInteriorStop e.1 (Δ : ℝ≥0∞) ↔ GW2Later.IsInteriorStop w' (Δ : ℝ≥0∞) := by
    unfold GW2Later.IsInteriorStop
    rw [hstop]
  rw [hiff, LP.traceAt_eq_of_isGeneratingTrace hη' hw'c.continuousOn hw'0 ENNReal.coe_lt_top]
  constructor
  · intro h
    simpa using BRLeaf.mem_H_of_isInteriorStop hη' hw'c.continuousOn hw'0 ENNReal.coe_lt_top h
  · intro h
    exact GW2aForce.isInteriorStop_of_mem_H hη' hw'c.continuousOn hw'0 ENNReal.coe_lt_top h

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The switching tips of a staged GW2 flow history are interior almost surely.** -/
theorem ae_switchTipsInterior (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b : ℝ → ℝ} {jumps : Finset ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec} (hgw : spec.2.1 = true) {θ : ℕ → ℝ}
    {Δ : ℕ → ℝ≥0∞} (hprog : IsFlowProg spec.2.2 θ Δ) (hΔ : ∀ j, Δ j ≠ ⊤)
    (hΔpos : ∀ j < spec.2.2.length, 0 < Δ j)
    (hθ : ∀ j < spec.2.2.length, θ j ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h spec E)
    (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    {k : ℕ} (hk : k ≤ spec.2.2.length) :
    ∀ᵐ ω ∂P, AllSucc Δ (fun j => E j ω) k → GW2Later.SwitchTipsInterior spec (fun j => E j ω) k := by
  have hFix := GW2aForce.flowFixedTimeInteriorStatement_of_thm13 h13
  set M : ℕ → Set Ω := fun j => {ω | AllSucc Δ (fun i => E i ω) (j + 1) →
    LP.traceAt (Δ j).toNNReal (fun x : ℝ≥0 => rdrv (recOf (Δ j) (E j ω)) x) ∈ H} with hMdef
  have hAm : ∀ n, MeasurableSet {ω | AllSucc Δ (fun i => E i ω) n} := by
    intro n
    have e : {ω | AllSucc Δ (fun i => E i ω) n} = ⋂ i : ℕ, {ω | i < n → Δ i < (E i ω).2} := by
      ext ω
      simp only [AllSucc, mem_ofPred_eq, mem_iInter]
    rw [e]
    refine MeasurableSet.iInter fun i => ?_
    by_cases hi : i < n
    · have e2 : {ω | i < n → Δ i < (E i ω).2} = {ω | Δ i < (E i ω).2} := by
        ext ω
        simp only [mem_ofPred_eq, hi, true_implies]
      rw [e2]
      exact measurableSet_lt measurable_const (measurable_snd.comp (hS.1 i))
    · have e2 : {ω | i < n → Δ i < (E i ω).2} = univ := by
        ext ω
        simp only [mem_ofPred_eq, hi, false_implies, mem_univ]
      rw [e2]
      exact MeasurableSet.univ
  have hMm : ∀ j, MeasurableSet (M j) := by
    intro j
    have htr : Measurable fun ω => LP.traceAt (Δ j).toNNReal (fun x : ℝ≥0 => rdrv (recOf (Δ j) (E j ω)) x) :=
      (LP.measurable_traceAt _).comp (measurable_pi_iff.2 fun x =>
        (measurable_rdrv_apply (x : ℝ)).comp (measurable_recOf (hS.1 j) (hreg j) (Δ j)))
    have e : M j = {ω | AllSucc Δ (fun i => E i ω) (j + 1)}ᶜ ∪
        (fun ω => LP.traceAt (Δ j).toNNReal (fun x : ℝ≥0 => rdrv (recOf (Δ j) (E j ω)) x)) ⁻¹' H := by
      ext ω
      simp only [hMdef, mem_ofPred_eq, mem_union, mem_compl_iff, mem_preimage]
      tauto
    rw [e]
    exact (hAm (j + 1)).compl.union (htr QuantumZipper.isOpen_H.measurableSet)
  have hMae : ∀ j < spec.2.2.length, ∀ᵐ ω ∂P, ω ∈ M j := by
    intro j hj
    refine Sec5.Lemma56Stages.ae_of_ae_condExpKernel (hS.2.1 j) (hMm j) ?_
    filter_upwards [hS.2.2.2 j, CondDriverBridge.ae_ae_run_eq_of_le (P := P) (κ := κ) (b := b) (jumps := jumps)
      spec (fun i _ ω => hreg i ω) (hS.2.1 j) le_rfl,
      Sec7.Aux122Disint.ae_ae_condExpKernel (hS.2.1 j) hR] with ω₀ hst hrun hregν
    by_cases hs₀ : AllSucc Δ (fun i => E i ω₀) j
    · have hl₀ := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω₀) hj).1 hs₀
      obtain ⟨b', J', h', hb', -, hfl'⟩ := hst _ _ hl₀
      have hG' := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl'
      have htpos : 0 < (Δ j).toNNReal := ENNReal.toNNReal_pos (hΔpos j hj).ne' (hΔ j)
      have hfix := hFix κ hκ hκ4 (θ j) (hθ j hj) b' J' hb' _ h' hG' _ _ hfl' (Δ j).toNNReal htpos
      filter_upwards [hfix, hrun, hregν] with ω hfω hrω hRω hsω
      have hΔeq : (((Δ j).toNNReal : ℝ≥0) : ℝ≥0∞) = Δ j := ENNReal.coe_toNNReal (hΔ j)
      have hsj : Δ j < (E j ω).2 := hsω j (Nat.lt_succ_self j)
      have hint := hfω (by rw [hΔeq]; exact hsj)
      have hsjω : AllSucc Δ (fun i => E i ω) j := fun i hi => hsω i (Nat.lt_succ_of_lt hi)
      have hlω := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) hj).1 hsjω
      obtain ⟨-, hc, η, hη, -⟩ := hRω j (θ j) (Δ j) _ (hprog j hj) hlω
      rw [← hΔeq] at hc hη hsj
      have h2 := (isInteriorStop_iff_traceAt (hreg j ω) hsj hc hη).1 hint
      rw [hΔeq] at h2
      exact h2
    · filter_upwards [hrun] with ω hrω hsω
      exfalso
      apply hs₀
      by_contra hn
      have hst := (run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω₀) j hj.le).2 hn
      have hlive := ((run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) j hj.le).1
        (fun i hi => hsω i (Nat.lt_succ_of_lt hi))).1
      rw [hrω] at hlive
      rcases hlive with h1 | h1 <;> rcases hst with h' | ⟨o, h'⟩ <;> rw [h1] at h' <;> cases h'
  have hall : ∀ᵐ ω ∂P, ∀ j, j < spec.2.2.length → ω ∈ M j := ae_all_iff.2 fun j => by
    by_cases hj : j < spec.2.2.length
    · exact (hMae j hj).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => absurd h hj
  filter_upwards [hall, hR] with ω hMω hRω hs j hj
  have hjl : j < spec.2.2.length := lt_of_lt_of_le hj hk
  have hsj : Δ j < (E j ω).2 := hs j hj
  have hinstr : instrTime spec j = Δ j := by
    unfold instrTime
    rw [hprog j hjl]
  have hstop : GW2aMulti.pieceStop spec (fun i => E i ω) j = Δ j := by
    unfold GW2aMulti.pieceStop
    rw [hinstr]
    exact min_eq_left hsj.le
  have hsjω : AllSucc Δ (fun i => E i ω) j := fun i hi => hs i (lt_trans hi hj)
  have hlω := (launches_run_gw2 (κ := κ) (b := b) (jumps := jumps) hgw hprog hΔ (fun i => E i ω) hjl).1 hsjω
  obtain ⟨-, hc, η, hη, -⟩ := hRω j (θ j) (Δ j) _ (hprog j hjl) hlω
  have hΔeq : (((Δ j).toNNReal : ℝ≥0) : ℝ≥0∞) = Δ j := ENNReal.coe_toNNReal (hΔ j)
  have htr := hMω j hjl (fun i hi => hs i (lt_of_lt_of_le hi hj))
  show GW2Later.IsInteriorStop (E j ω).1 (GW2aMulti.pieceStop spec (fun i => E i ω) j)
  rw [hstop, ← hΔeq]
  rw [← hΔeq] at hc hη hsj
  refine (isInteriorStop_iff_traceAt (hreg j ω) hsj hc hη).2 ?_
  rw [hΔeq]
  exact htr

end InteractingSLE.Theorem14.GW2Omx

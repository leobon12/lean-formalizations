/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JReg
import InteractingSLE.Spec.Supplement.SB2CondState
import InteractingSLE.Spec.Supplement.WalkInfChart

/-!
# K2's chart and word inputs in the recentred launch chart, for families regular at every sample

Packet PROVE-T14-SB2FIN4. K2 (`SB.Cond.isCondFlowLineDriverOn_of_markedKernel`) reads the field in a random chart `c`
whose data are measurable in the conditioning σ-algebra `𝒢` (`hdom`, `hfwd`, `hliftm`, conformal with a continuous
harmonic lift: `hc`, `hlc`, `hlift`), with a `𝒢`-measurable word `cw` (`hcw`) such that the field read in `c ω₀` is,
under `condExpKernel P 𝒢 ω₀`, the GFF of `cw ω₀` (`hG`), and `c` is kernel-almost surely constant (`hcc`). For
SB2(1) the chart is the launch chart recentred at the entry point. This file supplies all of these for
`𝒢 = pastSigma k` (the retained past at the launch) and the chart `(verChart k).recenter m'`, for any
`pastSigma k`-measurable real `m'` (a version of the entry point), when the drivers are regular at every sample
(`SB2RelDriverLRegStatement`'s setting; the general case reduces to it, `sb2RelDriverLStatement_of_reg`):

* `ae_verChart_eq_runChart`: the version chart `WalkInf.verChart k` (measurable in the retained past) is almost
  surely the run chart after `k` instructions (the launch chart of instruction `k`);
* **`exists_k2ChartInputs`**: a `pastSigma k`-measurable word `cw = shiftW m' β` (`β` from
  `Cond.exists_condChartField_of_isStagedHistory`), `IsMeasChart (pastSigma k)` for the recentred version chart, and,
  almost surely at living states, the conditional field read in the recentred chart is the GFF of `cw` (the recentred
  field is `flowField m' 0` of the field in the run chart: `eq_flowField_of_recenter`,
  `IsGFFWithBoundaryData.recenter`),
  and the recentred chart is kernel-almost surely constant (`Cond.ae_ae_runChart_eq`, `ae_ae_condExpKernel_eq`).

What it leaves for K2's application: a `pastSigma k`-measurable version `m'` of the entry point `launchEntry`, the
launch at the root state (`k = 0`, where `GW2aConn.IsLive` fails and `𝒢` is trivial), the force-word reading
(`xL xR ρL ρR`, `hword`, `hseed`: constant word shape on each piece of a countable partition of the launch event), the
adapted relative driver, and the probabilistic core `hcond`, `hmean`, `hloc`, `hAK`, `hint`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist.Staged Exist.StagedLaw WalkInf

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {spec : ExplSpec}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **The version chart is almost surely the run chart** after `k` instructions (the launched pieces are almost surely
continuous up to their stops, `StagedPiecesRegular`, so their records are good). -/
theorem ae_verChart_eq_runChart (hR : StagedPiecesRegular κ b jumps P spec E) (hreg : ∀ j ω, IsRegularDriver (E j ω))
    (k : ℕ) : ∀ᵐ ω ∂P, verChart κ b jumps spec E k ω = Cond.runChart κ b jumps spec E k ω := by
  filter_upwards [hR.ae_pieceRegular] with ω hω
  refine verChart_eq_run (fun j => hreg j ω) (N := k) (fun j _ hlj hfin => ?_) k le_rfl
  obtain ⟨⟨c', θ''⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hlj
  have hpr := hω j c' θ'' hl'
  exact isDrvGood_of_continuousOn_retOf (hreg j ω) hfin (CounterflowRange.continuous_stopped hpr.2.1).continuousOn

/-- **K2's chart and word inputs in the recentred version chart** (`𝒢 = pastSigma k`, drivers regular at every sample,
a program rooted at `0` without the GW2 flag — e.g. the lower walk): for every `pastSigma k`-measurable real `m'`
there is a `pastSigma k`-measurable word `cw` such that the recentred version chart `(verChart k).recenter m'` is a
measurable random chart for `pastSigma k` (K2's `hc`, `hlc`, `hlift`, `hdom`, `hfwd`, `hliftm`); the version chart is
almost surely the run chart; almost surely at a living state the field read in the recentred chart is, under the
regular conditional law, the GFF of `cw` (K2's `hG`); and the recentred chart is kernel-almost surely constant (K2's
`hcc`). -/
theorem exists_k2ChartInputs (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hgw : spec.2.1 = false) (hx₀ : spec.1 = 0)
    (hE : IsStagedHistory κ b jumps P h spec E) (hR : StagedPiecesRegular κ b jumps P spec E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) {m' : Ω → ℝ}
    (hm' : Measurable[pastSigma κ b jumps spec E k] m') :
    ∃ cw : Ω → Restart.BoundaryWord, Measurable[pastSigma κ b jumps spec E k] cw ∧
      IsMeasChart (pastSigma κ b jumps spec E k) (fun ω => (verChart κ b jumps spec E k ω).recenter (m' ω)) ∧
      (∀ᵐ ω₀ ∂P, verChart κ b jumps spec E k ω₀ = Cond.runChart κ b jumps spec E k ω₀) ∧
      (∀ᵐ ω₀ ∂P, GW2aConn.IsLive (ExplState.run κ b jumps spec (fun j => E j ω₀) k) →
        IsPiecewiseConstantBoundaryData (cw ω₀).fn (cw ω₀).jumps ∧
        ∃ h' : Ω → DistOn upperHalfPlaneOpens,
          (∀ ω, IsChartTransport ((verChart κ b jumps spec E k ω₀).recenter (m' ω₀)) 1 0 (chiC κ) (h ω) (h' ω)) ∧
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps spec E k) ω₀) h' (cw ω₀).fn
            (cw ω₀).jumps) ∧
      ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀),
        (verChart κ b jumps spec E k ω).recenter (m' ω) = (verChart κ b jumps spec E k ω₀).recenter (m' ω₀) := by
  obtain ⟨β, hβm, hβ⟩ := Cond.exists_condChartField_of_isStagedHistory hκ hb hh hgw hx₀ hE hreg k
  have h𝒢 : pastSigma κ b jumps spec E k ≤ mΩ := hE.2.1 k
  have hver := ae_verChart_eq_runChart hR hreg k
  refine ⟨fun ω => Exist.StagedLaw.BoundaryWord.shiftW (m' ω) (β ω),
    Exist.StagedLaw.BoundaryWord.measurable_shiftW.comp (hm'.prodMk hβm),
    (isMeasChart_verChart hb hE.1 hreg k).recenter hm', hver, ?_, ?_⟩
  · filter_upwards [hβ, hver, hR.ae_pieceRegular] with ω₀ hβ₀ hv₀ hp₀ hl₀
    obtain ⟨-, h', hT', hG'⟩ := hβ₀ hl₀
    obtain ⟨hcf, hℓ⟩ := GW2aCont.isConformal_runChart (κ := κ) (b := b) (jumps := jumps) spec (fun j => E j ω₀) k
      fun j _ c θ hl => hp₀ j c θ hl
    set m₀ := m' ω₀
    have hT'' : ∀ ω, IsChartTransport ((Cond.runChart κ b jumps spec E k ω₀).recenter m₀) 1 0 (chiC κ) (h ω)
        (Chart.chartTransport (hcf.recenter m₀) 1 0 (chiC κ) (h ω)) := fun ω =>
      Chart.isChartTransport_chartTransport (hcf.recenter m₀)
        (Chart.locallyIntegrableOn_of_continuousOn (Chart.continuousOn_recenter_lift hℓ)) 1 0 (chiC κ) (h ω)
    have he : (fun ω => Chart.chartTransport (hcf.recenter m₀) 1 0 (chiC κ) (h ω)) =
        fun ω => Exist.flowField m₀ 0 (h' ω) :=
      funext fun ω => eq_flowField_of_recenter hcf hℓ (hT' ω) (hT'' ω)
    have hG'' := Supp9.IsGFFWithBoundaryData.recenter (β ω₀).isPiecewiseConstantBoundaryData m₀ hG'
    refine ⟨(Exist.StagedLaw.BoundaryWord.shiftW m₀ (β ω₀)).isPiecewiseConstantBoundaryData,
      fun ω => Chart.chartTransport (hcf.recenter m₀) 1 0 (chiC κ) (h ω), ?_, ?_⟩
    · rw [hv₀]
      exact hT''
    · rw [he, Exist.StagedLaw.BoundaryWord.jumps_shiftW,
        show (Exist.StagedLaw.BoundaryWord.shiftW m₀ (β ω₀)).fn = fun y => (β ω₀).fn (y + m₀) from
          funext (Exist.StagedLaw.BoundaryWord.fn_shiftW m₀ (β ω₀))]
      exact hG''
  · filter_upwards [Cond.ae_ae_runChart_eq (P := P) k (fun j _ => hreg j) h𝒢,
      Sec7.Aux122Disint.ae_ae_condExpKernel h𝒢 hver, hver, Sec7.Aux122Disint.ae_ae_condExpKernel_eq h𝒢 hm']
      with ω₀ h1 h2 h3 h4
    filter_upwards [h1, h2, h4] with ω e1 e2 e4
    rw [e2, e1, ← h3, e4]

omit [IsProbabilityMeasure P] in
/-- **K2's `hF` for a launch** (drivers measurable and regular at every sample): the event that instruction `k` launches
is measurable in the retained past `pastSigma k` — it is determined by the state after `k` instructions
(`launches_run_succ_of_run_eq`), hence saturated for the past map (`measurableSet_pastSigma_of_runs`). For the lower
walk it is `launchSet` (`launchSet κ b jumps E k = {ω | … (E w) …}` with `w = boundaryWalkSpec b jumps (−π/2) true`). -/
theorem measurableSet_launch_pastSigma (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (k : ℕ) :
    MeasurableSet[pastSigma κ b jumps spec E k]
      {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} :=
  measurableSet_pastSigma_of_runs runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j)
    (measurableSet_launch_self runMeasStatement hb (fun j _ => hEm j) (fun j _ => hreg j)) fun ω ω' h hω => by
      show _ ≠ none
      rw [← launches_run_succ_of_run_eq spec (h k le_rfl)]
      exact hω

end InteractingSLE.Theorem14.SB.Lv

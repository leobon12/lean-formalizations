/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2QxFlow
import InteractingSLE.Spec.Supplement.SB2QxRec
import InteractingSLE.Spec.Supplement.SB2JvEnd
import InteractingSLE.Spec.Supplement.GW2ScheduleIdent
import InteractingSLE.Spec.Sec7.StripSysPath
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# The canonical driver is continuous up to its lifetime (Theorem 1.3)

Packet PROVE-SB2-CANON, round 5 ((P4): the last clause of `Qx.ChainFacts`). **`ae_continuousOn_driverOf`**: if the
field `Z` is, under the conditional law given `𝓜` at almost every point of an event `L ∈ 𝓜`, a GFF with the boundary
data of an `𝓜`-measurable word `c`, then almost surely on `L` the canonical driver `driverOf (c, Z)` is continuous on
`{s ≤ its lifetime}`.

Proof: under the kernel the canonical driver is the flow-line driver (`Qx.ae_isFlowLineDriver_driverOf`), so it has a
trace (Theorem 1.3, `IsFlowLineDriver.ae_hasTrace`), hence is continuous up to its lifetime
(**`continuousOn_le_of_hasTrace`**, from `Lk.continuousOn_driver_of_gen`), hence its record is good
(`isDrvGood_of_continuousOn_le`), a measurable event; the event passes from the kernels to `P` on `L`
(`GW2Schedule.ae_of_ae_condExpKernel_on`), and a good record gives the continuity back (`Qx.continuousOn_of_good`).

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cz

open Restart Exist Exist.Staged Exist.StagedLaw

/-- **A regular driver with a trace is continuous up to its lifetime.** -/
theorem continuousOn_le_of_hasTrace {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver e)
    (htr : Sec7.StripSysPath.HasTrace e.1 e.2) : ContinuousOn e.1 {s | (s : ℝ≥0∞) ≤ e.2} := by
  by_cases htop : e.2 = ⊤
  · refine hreg.1.mono fun s _ => ?_
    show (s : ℝ≥0∞) < e.2
    rw [htop]; exact ENNReal.coe_lt_top
  by_cases h0 : e.2 = 0
  · refine Set.Subsingleton.continuousOn (fun s hs t ht => ?_) _
    have hs' : (s : ℝ≥0∞) ≤ 0 := h0 ▸ hs
    have ht' : (t : ℝ≥0∞) ≤ 0 := h0 ▸ ht
    rw [nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hs' ht'
    rw [hs', ht']
  obtain ⟨η, hη, -⟩ := htr
  exact Lk.continuousOn_driver_of_gen hreg htop (pos_iff_ne_zero.2 h0) hη

/-- **The canonical driver is continuous up to its lifetime**, almost surely on an event where the field has the word's
conditional law (Theorem 1.3). -/
theorem ae_continuousOn_driverOf (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (θ : ℝ) {Ω : Type u} {𝓜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (h𝓜 : 𝓜 ≤ mΩ) {c : Ω → BoundaryWord}
    (hc : Measurable[𝓜] c) {Z : Ω → DistOn upperHalfPlaneOpens} (hZ : Measurable Z) {L : Set Ω}
    (hL : MeasurableSet[𝓜] L)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → IsGFFWithBoundaryData (condExpKernel P 𝓜 ω₀) Z (c ω₀).fn (c ω₀).jumps) :
    ∀ᵐ ω ∂P, ω ∈ L → ContinuousOn (driverOf h12p hκ θ (c ω, Z ω)).1
      {s | (s : ℝ≥0∞) ≤ (driverOf h12p hκ θ (c ω, Z ω)).2} := by
  set e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => driverOf h12p hκ θ (c ω, Z ω) with hedef
  have hcm : Measurable c := hc.mono h𝓜 le_rfl
  have hem : Measurable e := (measurable_driverOf h12p hκ θ).comp (hcm.prodMk hZ)
  have hreg : ∀ ω, IsRegularDriver (e ω) := fun ω => Mz.isRegularDriver_driverOf h12p hκ _ _
  set A : Set Ω := {ω | (e ω).2 = ⊤} ∪ {ω | LocalExt.IsDrvGood (recHist (recOf ⊤ (e ω)))} with hAdef
  have hA : MeasurableSet A :=
    (measurableSet_eq_fun (measurable_snd.comp hem) measurable_const).union
      ((measurable_recHist.comp (measurable_recOf hem hreg ⊤)) LocalExt.measurableSet_isDrvGood)
  have hflow := Qx.ae_isFlowLineDriver_driverOf h12p h13 hκ θ h𝓜 hc hZ hlaw
  have hk : ∀ᵐ ω₀ ∂P, ω₀ ∈ L → ∀ᵐ ω ∂(condExpKernel P 𝓜 ω₀), ω ∈ A := by
    filter_upwards [hflow] with ω₀ hf hω₀
    filter_upwards [Sec7.StripSysPath.IsFlowLineDriver.ae_hasTrace
      (Sec7.StripSysPath.theorem13LowStatement_of_theorem13 h13) hκ hκ4 (hf hω₀)] with ω htr
    by_cases htop : (e ω).2 = ⊤
    · exact Or.inl htop
    · refine Or.inr (isDrvGood_of_continuousOn_le (hreg ω) (by rwa [min_eq_right le_top]) ?_)
      rw [min_eq_right le_top]
      exact continuousOn_le_of_hasTrace (hreg ω) htr
  filter_upwards [GW2Schedule.ae_of_ae_condExpKernel_on h𝓜 hL hA hk] with ω hω hωL
  exact Qx.continuousOn_of_good (hreg ω) fun hfin => (hω hωL).resolve_left hfin

end InteractingSLE.Theorem14.SB.Cz

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafSurvEPositive

/-!
# The reciprocal survival gap is a history clock

A continuous optional reader gives a strictly positive gap before the cutoff,
vanishing at each finite cutoff. Its reciprocal is the scalar blowup clock
used by the already proved WFS announcing-rule construction.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

/-- A positive continuous gap which vanishes at a positive endpoint has an
unbounded reciprocal on the interval before that endpoint. -/
theorem exists_lt_reciprocal_of_continuous_zero {g : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hg : Continuous g) (hT : 0 < T) (hzero : g T = 0)
    (hpos : ∀ t < T, 0 < g t) (M : ℝ) :
    ∃ t : ℝ≥0, t < T ∧ M < (g t)⁻¹ := by
  have : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hlim : Tendsto g (𝓝[<] T) (𝓝 (0 : ℝ)) := by
    simpa only [hzero] using (hg.continuousAt (x := T)).tendsto.mono_left
      (show 𝓝[<] T ≤ 𝓝 T from nhdsWithin_le_nhds)
  have hlt : ∀ᶠ t in 𝓝[<] T, t < T := self_mem_nhdsWithin
  have hlim' : Tendsto g (𝓝[<] T) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, hlt.mono fun t ht => hpos t ht⟩
  exact (hlt.and
    (hlim'.inv_tendsto_nhdsGT_zero.eventually (eventually_gt_atTop M))).exists

/-- The reader of the closed survival martingale supplies the previous clock
input. The strict-gap and terminal conditions are proved, not extra premises. -/
theorem hasHistoryBlowupClock_of_optionalSurvivalReader
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hpos : ∀ᵐ ω ∂P, 0 < V ω)
    {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hm : ∀ p, Measurable fun γ => M γ (dyadicTime p)) (hM : IsNonAnticipating M)
    (hcont : ∀ᵐ ω ∂P, Continuous (M (killedHistory W VL VR V ω)))
    (hread : IsOptionalSurvivalReader P (drivingFiltration P hX) V (killedHistory W VL VR V) M) :
    HasHistoryBlowupClock P (killedHistory W VL VR V) := by
  let Y := killedHistory W VL VR V
  let ψ : HistorySpace nL nR → ℝ≥0 → ℝ := fun γ t => (survivalGap M γ t)⁻¹
  refine ⟨ψ, fun p => (measurable_survivalGap hm p).inv, ?_, ?_⟩
  · intro γ δ p h
    exact congrArg Inv.inv (isNonAnticipating_survivalGap hM γ δ p h)
  · have hgap := ae_survivalGap_pos hX hc hpos hm hM hcont hread
    have hterminal := ae_survival_reader_terminal
      (Restart.Aux54.isStoppingTime_lifetime_driving (P := P) hX) hread
    filter_upwards [hpos, hcont, hgap, hterminal] with ω hVpos hcont hgap hterminal
    have hg : Continuous (survivalGap M (Y ω)) := continuous_survivalDiscount_time.sub hcont
    refine ⟨hg.continuousOn.inv₀ (fun t ht => (hgap t ht).ne'), fun hfin L => ?_⟩
    let T : ℝ≥0 := (V ω).toNNReal
    have hTV : (T : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hfin
    have hTpos : 0 < T := ENNReal.coe_pos.1 (hTV.symm ▸ hVpos)
    have hzero : survivalGap M (Y ω) T = 0 := by
      change survivalDiscount (T : ℝ≥0∞) - M (Y ω) (V ω).toNNReal = 0
      rw [hTV, hterminal hfin, sub_self]
    obtain ⟨t, ht, hL⟩ := exists_lt_reciprocal_of_continuous_zero hg hTpos hzero
      (fun t ht => hgap t (by rw [← hTV]; exact ENNReal.coe_lt_coe.2 ht)) L
    exact ⟨t, by change (t : ℝ≥0∞) < V ω; rw [← hTV]; exact ENNReal.coe_lt_coe.2 ht, hL⟩

end InteractingSLE.WFS

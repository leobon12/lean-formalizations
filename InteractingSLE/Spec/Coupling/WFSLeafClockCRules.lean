/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafClockCPath
import InteractingSLE.Spec.Restart.Aux54Ref

/-!
# Stopping rules constructed from a history blowup clock

Galmarino's stopped-time test applies to each level rule clipped at the
lifetime. Almost sure strictness removes that clipping in the completed
driving filtration. The sequence itself is explicit and common to all samples.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.FlowStopIdentG LQGMetric

/-- A Borel Galmarino rule almost surely bounded by the lifetime is a stopping
time itself. This is Aux. 54's rule test followed by its null-set adapter. -/
theorem isStoppingTime_rule_of_ae_le_lifetime
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR V) {Q : HistorySpace nL nR → ℝ≥0∞}
    (hm : Measurable Q) (hgal : IsHistGalmarino Q)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω})
    (hle : ∀ᵐ ω ∂P, Q (killedHistory W VL VR V ω) ≤ V ω) :
    IsStoppingTime (drivingFiltration P hX)
      fun ω => (Q (killedHistory W VL VR V ω) : WithTop ℝ≥0) := by
  have hs := Restart.Aux54.isStoppingTime_ruleStop hX hm hgal hc
  have hqm := hm.comp (measurable_killedHistory hX)
  intro t
  apply Restart.Aux54.measurableSet_usualAugmentation_of_ae_eq
    (measurableSet_le hqm measurable_const)
    ((drivingFiltration P hX).le t _ (hs t)) (hs t)
  filter_upwards [hle] with ω hω
  change (Q (killedHistory W VL VR V ω) ≤ (t : ℝ≥0∞)) =
    (min (Q (killedHistory W VL VR V ω)) (V ω) ≤ (t : ℝ≥0∞))
  rw [min_eq_left hω]

/-- A Borel non-anticipating scalar reader, continuous before the recorded
lifetime and unbounded before each finite lifetime. Its initial value is unrestricted. -/
def HasHistoryBlowupClock {nL nR : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Y : Ω → HistorySpace nL nR) : Prop :=
  ∃ ψ : HistorySpace nL nR → ℝ≥0 → ℝ,
    (∀ p, Measurable fun γ => ψ γ (dyadicTime p)) ∧ IsNonAnticipating ψ ∧
    ∀ᵐ ω ∂P, ContinuousOn (ψ (Y ω)) {t | (t : ℝ≥0∞) < (Y ω).1} ∧
      ((Y ω).1 ≠ ⊤ → ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < (Y ω).1 ∧ M < ψ (Y ω) t)

/-- All the strict cofinal Galmarino stopping rules are constructed from the
single continuous history clock, with no rule or reference model as input. -/
theorem exists_strictRules_of_historyBlowupClock
    {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ V : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h)
    (hclock : HasHistoryBlowupClock P (killedHistory W VL VR V)) :
    ∃ Q : ℕ → HistorySpace nL nR → ℝ≥0∞,
      (∀ n, Measurable (Q n) ∧ IsHistGalmarino (Q n)) ∧
      (∀ n, IsStoppingTime (drivingFiltration P hC.2.2.2.2.choose)
        fun ω => (Q n (killedHistory W VL VR V ω) : WithTop ℝ≥0)) ∧
      (∀ n, ∀ᵐ ω ∂P, Q n (killedHistory W VL VR V ω) < V ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => Q n (killedHistory W VL VR V ω)) atTop (𝓝 (V ω))) := by
  obtain ⟨ψ₀, hm₀, hψ₀, hg₀⟩ := hclock
  let ψ : HistorySpace nL nR → ℝ≥0 → ℝ := fun γ t => ψ₀ γ t - ψ₀ γ 0
  have hm0 : Measurable fun γ => ψ₀ γ 0 := by simpa [dyadicTime] using hm₀ (0, 0)
  have hm : ∀ p, Measurable fun γ => ψ γ (dyadicTime p) := fun p => (hm₀ p).sub hm0
  have hψ : IsNonAnticipating ψ := by
    intro γ δ p h
    apply congrArg₂ (· - ·) (hψ₀ γ δ p h)
    have he := hψ₀ γ δ (0, 0) (fun q hq => h q (hq.trans (by simp [dyadicTime])))
    simpa [dyadicTime] using he
  have hg : ∀ᵐ ω ∂P, ContinuousOn (ψ (killedHistory W VL VR V ω))
      {t | (t : ℝ≥0∞) < V ω} ∧ ψ (killedHistory W VL VR V ω) 0 = 0 ∧
      (V ω ≠ ⊤ → ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < V ω ∧
        M < ψ (killedHistory W VL VR V ω) t) := by
    filter_upwards [hg₀] with ω hω
    refine ⟨hω.1.sub continuousOn_const, sub_self _, fun htop M => ?_⟩
    obtain ⟨t, ht, hM⟩ := hω.2 htop (M + ψ₀ (killedHistory W VL VR V ω) 0)
    exact ⟨t, ht, (lt_sub_iff_add_lt).2 hM⟩
  have hc : ∀ᵐ ω ∂P, ContinuousOn (Restart.Aux54.dState W VL VR ω) {t | (t : ℝ≥0∞) < V ω} := by
    filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path] with ω hp
    exact (continuousOn_state_of_isSLEPathUpTo hp).mono (fun t ht => ht.trans_le (hC.2.1 ω))
  have hcont : ∀ᵐ ω ∂P, IsKilledContHist (killedHistory W VL VR V ω) :=
    hc.mono fun _ h => isKilledContHist_killedHistory h
  have hQ : ∀ n, Measurable (levelPrefixRule ψ n) ∧ IsHistGalmarino (levelPrefixRule ψ n) :=
    fun n => ⟨measurable_levelPrefixRule hm n, (isStrongGalmarino_levelPrefixRule hψ n).isHistGalmarino⟩
  have hlt : ∀ n, ∀ᵐ ω ∂P, levelPrefixRule ψ n (killedHistory W VL VR V ω) < V ω := by
    intro n
    filter_upwards [hcont, hg] with ω hγ hg
    exact levelPrefixRule_lt hψ hγ hg.1 hg.2.1 hg.2.2 n
  refine ⟨levelPrefixRule ψ, hQ, fun n => ?_, hlt, ?_⟩
  · exact isStoppingTime_rule_of_ae_le_lifetime hC.2.2.2.2.choose (hQ n).1 (hQ n).2 hc
      ((hlt n).mono fun _ h => h.le)
  · filter_upwards [hcont, hg] with ω hγ hg
    exact tendsto_levelPrefixRule hψ hγ hg.1 hg.2.1 hg.2.2

end InteractingSLE.WFS

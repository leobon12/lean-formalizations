/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofResidualObserved

/-!
# On-event clock transport for the (S) and (L) arguments

Packet PROVE-RETPLUMB. Run the generic deterministic-line arguments with the
supported clock and lifetime. Their line identities only concern the initial
event, where both versions agree with the original retained processes.
-/
set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
namespace InteractingSLE.Restart.RetAux79
open DomainMarkov DomainMarkov.Aux79 DomainMarkov.K2
open LQGMetric (TestOn DistOn)
open Coupling Ito LocalSets LQGMetric.MarkovZB
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

omit mΩ in
/-- A zero lifetime makes every safe event empty off the initial event. -/
theorem lineSafe_indicator (F : Set Ω) (Q : ℝ≥0 → Ω → ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (C : Set ℂ) (t : ℝ≥0) :
    lineSafe (fun s => F.indicator (Q s)) W (F.indicator V) C t = F ∩ lineSafe Q W V C t := by
  classical
  ext ω
  by_cases hω : ω ∈ F <;> simp [lineSafe, hω]

omit mΩ in
/-- Supporting a clock preserves its pathwise continuity, monotonicity and
normalization, regardless of the behavior of its regularization branch. -/
theorem indicator_clock_properties {F : Set Ω} {Q : ℝ≥0 → Ω → ℝ≥0}
    (hc : ∀ ω, Continuous fun t => Q t ω) (hm : ∀ ω, Monotone fun t => Q t ω)
    (h0 : ∀ ω, Q 0 ω = 0) :
    (∀ ω, Continuous fun t => F.indicator (Q t) ω) ∧
      (∀ ω, Monotone fun t => F.indicator (Q t) ω) ∧
      ∀ ω, F.indicator (Q 0) ω = 0 := by
  classical
  refine ⟨fun ω => ?_, fun ω => ?_, fun ω => ?_⟩
  · by_cases hω : ω ∈ F
    · simpa only [indicator_of_mem hω] using hc ω
    · simpa only [indicator_of_notMem hω] using (continuous_const : Continuous fun _ : ℝ≥0 => (0 : ℝ≥0))
  · intro s t hst
    by_cases hω : ω ∈ F
    · simpa only [indicator_of_mem hω] using hm ω hst
    · simp only [indicator_of_notMem hω, le_refl]
  · by_cases hω : ω ∈ F <;> simp [hω, h0 ω]

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    {F : Set Ω} {Q : ℝ≥0 → Ω → ℝ≥0} {W : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens}

/-- (S) with the supported clock. The line law remains the landed original
line law; only its version on the initial event is used. -/
theorem hasSafeLaw_of_lineLaw_indicator
    (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Q t ω) (hm : ∀ ω, Monotone fun t => Q t ω)
    (h0 : ∀ ω, Q 0 ω = 0) (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (Q t)))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, q ≤ Q t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω)
    (hS : ∀ (ψ : TestOn upperHalfPlaneOpens) t,
      MeasurableSet[𝓖 t] (F ∩ lineSafe Q W V (tsupport ψ) t))
    (𝒢L : ℝ≥0 → MeasurableSpace Ω) (h𝒢L : ∀ t, 𝓖 t ≤ 𝒢L t) (h𝒢Lm : ∀ t, 𝒢L t ≤ mΩ)
    (hline : ∀ (ψ : TestOn upperHalfPlaneOpens) (t : ℝ≥0), ∀ᵐ ω ∂P, ω ∈ F →
      ω ∈ lineSafe Q W V (tsupport ψ) t →
      P[fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) | 𝒢L t] ω =
        Coupling.cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (Q t) ω) :
    HasSafeLaw κ ρL ρR P (timeChange 𝓖 (fun t => F.indicator (Q t)) hQa)
      F (F.indicator V) W VL VR X := by
  classical
  obtain ⟨hc', hm', h0'⟩ := indicator_clock_properties hc hm h0 (F := F)
  apply hasSafeLaw_of_lineLaw hX hc' hm' h0' hQa
    (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) ?_ ?_ ?_ 𝒢L h𝒢L h𝒢Lm ?_
  · intro q
    filter_upwards [hreach q] with ω hr hω hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := hr hω hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · filter_upwards [hreg] with ω hr hω
    simpa only [IsForceReg, indicator_of_mem hω] using hr hω
  · intro ψ t
    rw [lineSafe_indicator]
    exact hS ψ t
  · intro ψ t
    filter_upwards [hline ψ t] with ω hl hω hs
    rw [lineSafe_indicator] at hs
    simpa only [Coupling.cfAt, indicator_of_mem hω] using hl hω hs.2

/-- (L) with the supported clock. Protected line-set identities and integrals
are unchanged on the initial event. -/
theorem hasSafeMembers_of_lineMembers_indicator
    (hX : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ)
    (hc : ∀ ω, Continuous fun t => Q t ω) (hm : ∀ ω, Monotone fun t => Q t ω)
    (h0 : ∀ ω, Q 0 ω = 0) (hQa : ∀ t, Measurable[𝓖 t] (F.indicator (Q t)))
    (hreach : ∀ q : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ F → (q : ℝ≥0∞) < V ω → ∃ t, q ≤ Q t ω)
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → IsForceReg W VL VR V ω)
    (hS : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t,
      MeasurableSet[𝓖 t] (F ∩ lineSafe Q W V (ballsK Fb) t))
    (hline : ∀ (t : ℝ≥0) (Fb : Finset (ℚ × ℚ × ℚ)), ballsK Fb ⊆ QuantumZipper.H →
      ∀ E : Set Ω, MeasurableSet[𝓖 t] E →
      (∀ᵐ ω ∂P, ω ∈ E → ω ∈ F ∧ ω ∈ lineSafe Q W V (ballsK Fb) t) →
      ∀ (f : zsSub (ballsU Fb)) (Ξ : TestOn upperHalfPlaneOpens),
        ∫ ω in E, Complex.exp (Complex.I * (X ω (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P =
          projFactor (ballsOpen Fb) f Ξ *
            ∫ ω in E, Complex.exp (Complex.I * (X ω Ξ : ℂ)) ∂P) :
    HasSafeMembers P (timeChange 𝓖 (fun t => F.indicator (Q t)) hQa) F (F.indicator V) W X := by
  classical
  obtain ⟨hc', hm', h0'⟩ := indicator_clock_properties hc hm h0 (F := F)
  apply hasSafeMembers_of_lineMembers (VL := VL) (VR := VR) hX hc' hm' h0' hQa
    (fun _ _ hD t => measurableSet_inter_of_timeChange hD t) ?_ ?_ ?_ ?_
  · intro q
    filter_upwards [hreach q] with ω hr hω hq
    rw [indicator_of_mem hω] at hq
    obtain ⟨t, ht⟩ := hr hω hq
    exact ⟨t, by simpa only [indicator_of_mem hω] using ht⟩
  · filter_upwards [hreg] with ω hr hω
    simpa only [IsForceReg, indicator_of_mem hω] using hr hω
  · intro Fb t
    rw [lineSafe_indicator]
    exact hS Fb t
  · intro t Fb hFb E hE hs
    apply hline t Fb hFb E hE
    filter_upwards [hs] with ω he hω
    obtain ⟨hF, hsafe⟩ := he hω
    rw [lineSafe_indicator] at hsafe
    exact ⟨hF, hsafe.2⟩

end InteractingSLE.Restart.RetAux79

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofInputsWord

/-!
# Lifetime and trace inputs from observable physical prefixes

Packet PROVE-RETPLUMB. The landed inverse-clock measurability theorem supplies
the canonical trace and capacity lifetime once physical prefix observations
are available. The supported trace is continuous for every sample, including
the exceptional samples outside the initial event.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open Supp7

/-- A clock with a positive physical lifetime has a positive capacity lifetime. -/
theorem capLife_pos_of_clock {C : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    (hC : IsClockOn C L) (hL : 0 < L) : 0 < capLife C L := by
  by_cases htop : L = ⊤
  · simp only [capLife, ite_eq_left htop, ENNReal.zero_lt_top]
  · have he : (L.toNNReal : ℝ≥0∞) = L := ENNReal.coe_toNNReal htop
    have hp : 0 < L.toNNReal := by
      exact ENNReal.coe_pos.1 (he.symm ▸ hL)
    have hpos := hC.strictMonoOn (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ L by simp) he.le hp
    rw [hC.zero] at hpos
    simpa only [capLife, ite_eq_right htop] using ENNReal.ofReal_pos.2 hpos

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- Positivity of the two retained lifetimes is a consequence of the landed
boundary-stopped retained-continuation geometry. -/
theorem retLife_pos_of_good_pair {G : ℝ≥0 → Set Ω}
    {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0}
    {x₂ : ℝ} {ω : Ω} (hd : (retFam G η₁' η₂' u r).IsMeasGood)
    (hG : ω ∈ G r) (hp₂ : IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    0 < retLifeP η₁' η₂' ζ₂ u r ω ∧ 0 < retLife G η₁' η₂' ζ₂ u r ω := by
  obtain ⟨hR, -, hL⟩ := isRetCont_retFam hd hG hp₂ hpair
  have hp : 0 < retLifeP η₁' η₂' ζ₂ u r ω := by
    rw [hL]
    exact hR.pos_contLife
  refine ⟨hp, ?_⟩
  rw [retLife_eq]
  exact capLife_pos_of_clock (retChartPath_clock hd hG hp₂ hpair).1 hp

variable {𝓖 : Filtration ℝ≥0 mΩ} {F : Set Ω} {G : ℝ≥0 → Set Ω}
  {η₁' η₂' : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {u r : ℝ≥0} {x₂ : ℝ}

/-- Physical survival at all deterministic lines determines the measurable
supported physical lifetime. No earlier line observes its full future value. -/
theorem RetPrefixObservations.measurable_lifeP
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r) :
    Measurable (F.indicator (retLifeP η₁' η₂' ζ₂ u r)) := by
  classical
  refine measurable_of_Ioi fun a => ?_
  induction a using ENNReal.recTopCoe with
  | top => simp only [Ioi_top, preimage_empty, MeasurableSet.empty]
  | coe t =>
    convert 𝓖.le t _ (ho.survival t) using 1
    ext ω
    by_cases hω : ω ∈ F <;> simp [hω]

/-- Prefix observations give the supported canonical capacity-time trace and
lifetime as measurable random variables, with all-sample trace continuity. -/
theorem RetPrefixObservations.trace_data
    (ho : RetPrefixObservations 𝓖 F G η₁' η₂' ζ₂ u r)
    (hd : (retFam G η₁' η₂' u r).IsMeasGood) (hG : F ⊆ G r)
    (hp₂ : ∀ ω ∈ F, IsPathGood (η₂' ω) (ζ₂ ω) x₂)
    (hpair : ∀ ω ∈ F,
      Sec7.Lemma76Exit.IsDisjointPair (η₁' ω) (ζ₁ ω) u (η₂' ω) (ζ₂ ω) r) :
    (∀ q, Measurable (F.indicator fun ω => retPath G η₁' η₂' ζ₂ u r ω q)) ∧
      Measurable (F.indicator (retLife G η₁' η₂' ζ₂ u r)) ∧
      ∀ ω, ContinuousOn (fun q => F.indicator (fun ω => retPath G η₁' η₂' ζ₂ u r ω q) ω)
        {q | (q : ℝ≥0∞) ≤ F.indicator (retLife G η₁' η₂' ζ₂ u r) ω} := by
  classical
  let Γ : Ω → ℝ≥0 → ℂ := fun ω q => F.indicator (fun ω => retChartPath G η₁' η₂' ζ₂ u r ω q) ω
  have he : ∀ ω ∈ F, Γ ω = retChartPath G η₁' η₂' ζ₂ u r ω :=
    fun ω hω => funext fun _ => indicator_of_mem hω _
  have hc : ∀ ω, Continuous (Γ ω) := by
    intro ω
    by_cases hω : ω ∈ F
    · rw [he ω hω]
      exact (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1
    · have hz : Γ ω = fun _ => 0 := funext fun _ => indicator_of_notMem hω _
      rw [hz]
      exact continuous_const
  have h0 : ∀ ω ∈ F, Γ ω 0 = 0 := fun ω hω => by
    rw [he ω hω]
    exact (retChartPath_continuous_zero hd (hG hω) (hp₂ ω hω) (hpair ω hω)).2
  have hpath : ∀ ω, retPath G η₁' η₂' ζ₂ u r ω = fun q =>
      retChartPath G η₁' η₂' ζ₂ u r ω
        (invClock (chartClock (retChartPath G η₁' η₂' ζ₂ u r ω))
          (retLifeP η₁' η₂' ζ₂ u r ω) q) := fun _ => canonRetPath_zero ..
  have hdata := clockData_of_measurable (𝓖.le 0 _ ho.initial) hc
    (fun q => (ho.coordinates q q le_rfl).mono (𝓖.le q) le_rfl) h0 ho.measurable_lifeP
    (fun ω hω => by
      rw [he ω hω, indicator_of_mem hω]
      exact (retChartPath_clock hd (hG hω) (hp₂ ω hω) (hpair ω hω)).1)
    (fun ω hω => by
      rw [he ω hω]
      exact (retChartPath_clock hd (hG hω) (hp₂ ω hω) (hpair ω hω)).2.2)
  refine ⟨fun q => ?_, ?_, fun ω => ?_⟩
  · convert hdata.1 q using 1
    funext ω
    by_cases hω : ω ∈ F
    · simp only [indicator_of_mem hω, ite_eq_left hω, he ω hω, hpath ω]
    · simp only [indicator_of_notMem hω, ite_eq_right hω]
  · convert hdata.2.1 using 1
    funext ω
    by_cases hω : ω ∈ F
    · simp only [indicator_of_mem hω, ite_eq_left hω, he ω hω, retLife_eq]
    · simp only [indicator_of_notMem hω, ite_eq_right hω]
  · by_cases hω : ω ∈ F
    · simpa only [indicator_of_mem hω, he ω hω, hpath ω, retLife_eq] using hdata.2.2 ω hω
    · have hz : (fun q => F.indicator (fun ω => retPath G η₁' η₂' ζ₂ u r ω q) ω) = fun _ => 0 :=
        funext fun _ => indicator_of_notMem hω _
      rw [hz]
      exact continuous_const.continuousOn

/-- Replace the lifetime and trace of a model transfer by versions agreeing on
the conditioning event. This keeps its actual model, measurable reader and law. -/
def StoppedModelTransfer.congr_life_trace {P : Measure Ω} {κ θ : ℝ}
    {c : Ω → BoundaryWord} {Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {V V' : Ω → ℝ≥0∞} {γ γ' : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransfer κ θ P F c Hc V γ)
    (he : ∀ᵐ ω ∂P, ω ∈ F → V ω = V' ω ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V' ω → γ ω t = γ' ω t) :
    StoppedModelTransfer κ θ P F c Hc V' γ' where
  model := T.model
  read := T.read
  readMeas := T.readMeas
  mapLaw := T.mapLaw
  agrees := by
    filter_upwards [T.agrees, he] with ω hω e hF
    obtain ⟨hc, hH, hV, hγ⟩ := hω hF
    obtain ⟨eV, eγ⟩ := e hF
    refine ⟨hc, hH, hV.trans eV, fun t ht => ?_⟩
    exact (hγ t (eV.symm ▸ ht)).trans (eγ t ht)

/-- The supported versions constructed above give a transfer for the original
retained lifetime and trace. Their off-event values create no extra hypothesis. -/
def StoppedModelTransfer.of_indicator {P : Measure Ω} {κ θ : ℝ}
    {c : Ω → BoundaryWord} {Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {V : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (T : StoppedModelTransfer κ θ P F c Hc (F.indicator V)
      (fun ω t => F.indicator (fun ω => γ ω t) ω)) :
    StoppedModelTransfer κ θ P F c Hc V γ :=
  T.congr_life_trace (Eventually.of_forall fun _ hω =>
    ⟨indicator_of_mem hω _, fun _ _ => indicator_of_mem hω _⟩)

end InteractingSLE.Restart.RetAux79

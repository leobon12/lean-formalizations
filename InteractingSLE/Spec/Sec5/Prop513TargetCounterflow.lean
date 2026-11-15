/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetLaw
import InteractingSLE.Spec.Sec5.Prop513FieldAssembly

/-! # The Figure 5.1 counterflow, in its original angle-zero frame

Adding `πχ/2` to the strip datum and using frame `-π/2` leaves the
counterflow datum unchanged. The existing Prop. 4.11 admissibility theorem
therefore applies to exactly the source's Figure 5.1 bounds.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal
universe u

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper Sec4

/-- The Figure 5.1 bounds, shifted into the frame of Prop. 4.11. -/
theorem shifted_fig51_isProp411Data {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b') :
    IsProp411Data κ x₀
      (fun x => fig51Lower a b x + π / 2 * chiC κ)
      (fun x => fig51Upper x₀ a' b' x + π / 2 * chiC κ) {0} {x₀} := by
  have he := sleLambda_sixteen_div_eq_sub hκ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [sub_neg_eq_add] using isPiecewiseConstantBoundaryData_sub_const
      (isPiecewiseConstantBoundaryData_fig51Lower a b) (-(π / 2 * chiC κ))
  · simpa only [sub_neg_eq_add] using isPiecewiseConstantBoundaryData_sub_const
      (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b') (-(π / 2 * chiC κ))
  · intro x hx
    dsimp only
    rw [fig51Lower_of_neg hx]
    linarith only [hb.1, he]
  · intro x hx
    dsimp only
    rw [fig51Lower_of_pos hx]
    linarith only [hb.2.1, he]
  · intro x hx
    dsimp only
    rw [fig51Upper_of_lt hx]
    linarith only [hb.2.2.1, he]
  · intro x hx
    dsimp only
    rw [fig51Upper_of_gt hx]
    linarith only [hb.2.2.2, he]

theorem counterflowData_shift (κ q : ℝ) (bL bU : ℝ → ℝ) :
    stripCounterflowData κ 0 q bL bU = stripCounterflowData κ (-(π / 2)) q
      (fun x => bL x + π / 2 * chiC κ) (fun x => bU x + π / 2 * chiC κ) := by
  funext x
  unfold stripCounterflowData stripHData
  split_ifs <;> ring

/-- The actual angle-zero counterflow driver carries an admissible force word. -/
theorem exists_admissible_fig51_counterflow {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∃ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsPiecewiseConstantBoundaryData b' J' ∧ IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ ∧
      HasAdmissiblePartialSums (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0)
        (flowLineRhoR (16 / κ) b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0) := by
  obtain ⟨b₀, J₀, h₀, hb₀, hT, hfl⟩ := hcf
  have hq : 0 < Real.exp (π * x₀) := Real.exp_pos _
  have hpc := isPiecewiseConstantBoundaryData_stripHData κ
    (isPiecewiseConstantBoundaryData_fig51Lower a b)
    (isPiecewiseConstantBoundaryData_fig51Upper x₀ a' b')
  have hg := Prop513Field.gff hq _ _ hpc hG hT
  have hc := Prop513Field.isPiecewiseConstant_data hq
    (-((0 + π) * chiC κ)) (chiC (16 / κ)) hpc
  rw [Prop513Field.data_eq hκ hq 0] at hg hc
  have he := Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb₀ hc
    (Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
      (div_pos (by norm_num) hκ) hb₀ hfl) hg
  refine ⟨b₀, J₀, h₀, hb₀, hfl, admissible_stripCounterflow_of_eq hκ
    (shifted_fig51_isProp411Data (x₀ := x₀) hκ hb) hb₀
    (J₀ ∪ Prop513Field.jumps (Real.exp (π * x₀)) (stripHJumps {0} {x₀})) ?_⟩
  intro x hx
  rw [← counterflowData_shift]
  exact he x hx

/-- Infinite lifetime for the source's angle-zero counterflow. -/
theorem fig51_counterflow_lifetime {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ)
    (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ := by
  obtain ⟨b', J', _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  exact (aux6Statement (div_pos (by norm_num) hκ) _ _ _ _ P 𝓕 W VL VR B ζ
    (Theorem15.isOrderedForceWord_flowLine b' J' 0) hadm hC.1).mono fun _ hω => hω.1

/-- The source's counterflow stays in the open half-plane at positive times. -/
theorem fig51_counterflow_trace_mem_H
    (hN : Theorem14.GW4Ident.CounterflowNoReturnStatement.{u})
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  have hζ := fig51_counterflow_lifetime hκ hb hG hcf
  have hzero := stripCounterflow_noReturn_of_centered hN hκ hκ4 hcf hζ
  obtain ⟨b', J', _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  exact ae_lifetime_eq_top_and_trace_mem_H_of_noReturn (div_pos (by norm_num) hκ)
    (Theorem15.isOrderedForceWord_flowLine b' J' 0) hadm
    ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ hC.1 hzero

end InteractingSLE.Sec5.Prop513Target

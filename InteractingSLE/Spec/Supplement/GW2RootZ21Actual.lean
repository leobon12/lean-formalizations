/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootZ21Clock
import InteractingSLE.Spec.Supplement.GW2RootM17Capacity
import InteractingSLE.Spec.Supplement.GW2aSingle

/-!
# The initial canonical capacity is read in its actual retained stage

Packet PROVE-T14-GW2ROOT2. The source staged law supplies the first
piece's full generating trace. The two-record reader then equals the
literal normalized root capacity on the actual live pre-contact event.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootZ21

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)

/-- The initial normalized reader is measurable in the literal initial
root record at every sample, without an ambient regularity assumption. -/
theorem measurable_initialCapacity {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r []]
      (fun ω => 4 ^ r.2 * forwardCapacity s (rootEntry r.1).2
        (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω)) :=
  measurable_const.mul (measurable_rootSigma_forwardCapacity hκ h12p βA c₀ h s W ζ
    r [] ⟨0, by simp only [entryList, List.map_nil, List.length_nil]; omega⟩ (rootEntry r.1).2)

/-- The initial reader is the literal root capacity before contact.
All relative chart, hull and clock identifications are proved internally. -/
theorem capR_nil_eq_forwardCapacity_from_traces {α : ℝ≥0 → ℂ} (ω : Ω)
    (hα : IsGeneratingTrace (W · ω) (ζ ω) α) (hW : Continuous (W · ω))
    (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤) (hsH : α s ∈ H)
    {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) :
    let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [rootEntry r.1]) 0 ω
    ∀ {γ : ℝ≥0 → ℂ}, IsGeneratingTrace E.1 E.2 γ →
      ((rootEntry r.1).2 : ℝ≥0∞) < min
        (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
          ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) E.2 →
      capR hκ h12p βA b jumps c₀ h W ζ s r [] ω =
        4 ^ r.2 * forwardCapacity s (rootEntry r.1).2
          (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω) := by
  dsimp only
  intro γ hγ ht
  let θ := (rootEntry r.1).1
  let v := (rootEntry r.1).2
  let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [(θ, v)]) 0 ω
  have he : IsRegularDriver E := isRegularDriver_canonDrive hκ h12p βA c₀ 0 _ _ (h ω) 0
  have hspec : schedSpecOf r.1 [] = schedSpec 0 [(θ, v)] := by
    simp only [schedSpecOf, entryList, List.map_nil, schedOf_nil, hroot]
    rfl
  have hδ : specDelta (schedSpec 0 [(θ, v)]) 0 = (v : ℝ≥0∞) := by
    have hs : schedSpec 0 [(θ, v)] = (0, true, [Sum.inl (θ, (v : ℝ≥0∞))]) := by
      simp only [schedSpec, scheduleProgram, tsub_zero]
    rw [hs]
    simp only [specDelta, instrTime, List.getElem?_cons_zero, ENNReal.coe_ne_top, ↓reduceIte]
  have hstop : stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω = recOf (v : ℝ≥0∞) E := by
    rw [hspec]
    change recOf (specDelta (schedSpec 0 [(θ, v)]) 0) E = _
    rw [hδ]
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hc := forwardCapacity_eq_relClock_before_contact W ζ ω hα hW.continuousOn hW0 hs hsH
    he hγ ht
  have hcap := RootM17.capR_nil_eq_relClock_from_canonical_trace hκ h12p βA b jumps c₀ h
    θ v ω W ζ hα hW hW0 hζ s hsH r hroot rfl hγ he.1 he.2.1 ht
  rw [hstop, hc]
  exact hcap

variable [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The original source data supply the full first generating trace and
the exact capacity reader on one conull event. No relative experiment or
capacity-measurability premise is added. -/
theorem ae_capR_nil_eq_forwardCapacity (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (α : Ω → ℝ≥0 → ℂ)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) ⊤ (α ω))
    {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) :
    let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (E ω).2 (γ ω) ∧
      (α ω s ∈ H → ((rootEntry r.1).2 : ℝ≥0∞) < min
        (firstContactTime (fun q => sphereInv (γ ω q : OnePoint ℂ))
          ((fun q => (α ω q : OnePoint ℂ)) '' Icc 0 s)) (E ω).2 →
        capR hκ h12p βA b jumps c₀ h W ζ s r [] ω =
          4 ^ r.2 * forwardCapacity s (rootEntry r.1).2
            (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω)) := by
  let spec := schedSpec 0 [rootEntry r.1]
  have hS := isStagedHistory_canonFam hκ h12p βA c₀ (specAngle spec) (specDelta spec)
    h13 hβA hb hc₀J hc₀ hh (spec := spec) rfl
    (isFlowProg_spec 0 true _) (specDelta_ne_top _)
  have hp : spec.2.2 = [Sum.inl ((rootEntry r.1).1, ((rootEntry r.1).2 : ℝ≥0∞))] := by
    simp only [spec, schedSpec, scheduleProgram, tsub_zero]
  have hfl := hS.isFlowLineDriver_first hκ hb hh rfl hp
  have hgen := GW2aSingle.ae_chosenTrace h13 hκ hfl
  dsimp only
  filter_upwards [hgen, hα, GW2Later.ae_counterflow_regular h13 hκ hcf hζ, hζ]
    with ω hgenω hαω hreg hζω
  refine ⟨hgenω.1, ?_⟩
  intro hsH ht
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  have hαζ : IsGeneratingTrace (W · ω) (ζ ω) (α ω) := by rwa [hζω]
  exact capR_nil_eq_forwardCapacity_from_traces hκ h12p βA b jumps c₀ h W ζ s ω
    hαζ hW hW0 hζω hsH r hroot hgenω.1 ht

end InteractingSLE.Theorem14.GW2TipSystem.RootZ21

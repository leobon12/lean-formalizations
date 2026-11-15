/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Trace

/-!
# Source regularity of the initial observable relative experiment

Packet PROVE-T14-GW2ROOT2. The actual first canonical piece supplies the
original generating trace by the source staged law and Theorem 1.3.
Its boundary-extended inverse-clock reader is therefore continuous and
has zero boundary occupation in the actual relative capacity time.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)

/-- The exact initial physical record, for a zero physical root. -/
theorem initial_stopRec_eq {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q)
    (hroot : rootPt r.1 = 0) (ω : Ω) :
    stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω =
      recOf ((rootEntry r.1).2 : ℝ≥0∞)
        (canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [rootEntry r.1]) 0 ω) := by
  have hspec : schedSpecOf r.1 [] = schedSpec 0 [rootEntry r.1] := by
    simp only [schedSpecOf, entryList, List.map_nil, schedOf_nil, hroot]
  have hp : schedSpec 0 [rootEntry r.1] =
      (0, true, [Sum.inl ((rootEntry r.1).1, ((rootEntry r.1).2 : ℝ≥0∞))]) := by
    simp only [schedSpec, scheduleProgram, tsub_zero]
  rw [hspec]
  change recOf (specDelta (schedSpec 0 [rootEntry r.1]) 0) _ = _
  congr 1
  rw [hp]
  simp only [specDelta, instrTime, List.getElem?_cons_zero, ENNReal.coe_ne_top, ↓reduceIte]

variable [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- Source-level relative trace regularity for the actual initial records.
The curve and its parametrization are the Borel readers already proved
measurable in `rootSigma`; no relative regularity is assumed. -/
theorem ae_initial_relativeTip_regular (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (α : Ω → ℝ≥0 → ℂ)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) ⊤ (α ω))
    {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) :
    let v := (rootEntry r.1).2
    let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂P, α ω s ∈ H → (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ ω q : OnePoint ℂ))
        ((fun q => (α ω q : OnePoint ℂ)) '' Icc 0 s)) (E ω).2 →
      let p := (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω)
      let C := (RootZ21.forwardCapacity s v p).toNNReal
      relativeTipRead s v 0 p = 0 ∧
        ContinuousOn (fun t : ℝ => relativeTipRead s v t.toNNReal p) (Icc 0 (C : ℝ)) ∧
        volume {t : ℝ | t ∈ Ioo 0 (C : ℝ) ∧ relativeTipRead s v t.toNNReal p ∉ H} = 0 ∧
        ∃ V : ℝ≥0 → ℝ, V 0 = 0 ∧
          ContinuousOn V {t | (t : ℝ≥0∞) ≤ (C : ℝ≥0∞)} ∧
          IsGeneratingTrace V (C : ℝ≥0∞) (fun u => relativeTipRead s v u p) := by
  have hfirst := RootZ21.ae_capR_nil_eq_forwardCapacity hκ h12p βA b jumps c₀ h W ζ s P
    h13 hβA hb hc₀J hc₀ hh hcf hζ α hα r hroot
  dsimp only
  filter_upwards [hfirst, GW2Later.ae_counterflow_regular h13 hκ hcf hζ, hζ, hα]
    with ω hf hr hζω hαω
  intro hsH hv
  obtain ⟨_, _, hW, hW0, _⟩ := hr
  have hαζ : IsGeneratingTrace (W · ω) (ζ ω) (α ω) := by rwa [hζω]
  let e := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [rootEntry r.1]) 0 ω
  have he : IsRegularDriver e := isRegularDriver_canonDrive hκ h12p βA c₀ 0 _ _ (h ω) 0
  obtain ⟨V, hV0, hVc, hgen, hvol⟩ :=
    exists_relativeTipRead_generatingTrace_before_contact
      W ζ ω hαζ hW hW0 hζω hsH he hf.1 hv
  rw [← initial_stopRec_eq hκ h12p βA c₀ h r hroot ω] at hgen hvol hVc
  refine ⟨hgen.1, hgen.2.1.comp continuous_real_toNNReal.continuousOn ?_, ?_, V, hV0, hVc, hgen⟩
  · intro t ht
    exact ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr ht.2)
  · apply measure_mono_null ?_ hvol
    intro t ht
    refine ⟨ht.1.1.le, ?_, ht.2⟩
    apply ENNReal.coe_lt_coe.mpr
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht.1.1.le]
    exact ht.1.2

end InteractingSLE.Theorem14.GW2TipSystem.RootA22

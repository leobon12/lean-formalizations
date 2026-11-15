/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Observe

/-!
# Source regularity of the observable initial driver and trace

Packet PROVE-T14-GW2ROOT2. The source first-piece law supplies the relative
trace. Its explicit Borel driver reader generates that trace and is
continuous at every live capacity time. No relative driver is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootB23

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric Supp8.GB6

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (b : ℝ → ℝ)
  (jumps : Finset ℝ) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The actual first-piece record has a measurable relative driver which
generates the actual relative curve, with its source regularity proved. -/
theorem ae_initial_relative_readers_regular (h13 : Theorem13Statement.{u})
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
      relativeDriverRead s v 0 p = 0 ∧ RootA22.relativeTipRead s v 0 p = 0 ∧
        IsGeneratingTrace (fun u => relativeDriverRead s v u p) (C : ℝ≥0∞)
          (fun u => RootA22.relativeTipRead s v u p) ∧
        (∀ t : ℝ, t.toNNReal < C →
          ContinuousAt (fun u : ℝ => relativeDriverRead s v u.toNNReal p) t) ∧
        ContinuousOn (fun t : ℝ => RootA22.relativeTipRead s v t.toNNReal p)
          (Icc 0 (C : ℝ)) ∧
        volume {t : ℝ | t ∈ Ioo 0 (C : ℝ) ∧
          RootA22.relativeTipRead s v t.toNNReal p ∉ H} = 0 := by
  have hfirst := RootA22.ae_initial_relativeTip_regular
    hκ h12p βA b jumps c₀ h W ζ s P h13 hβA hb hc₀J hc₀ hh hcf hζ α hα r hroot
  dsimp only at hfirst ⊢
  filter_upwards [hfirst] with ω hf
  intro hsH hv
  obtain ⟨hΓ0, hΓc, hvol, V, hV0, hVc, hgen⟩ := hf hsH hv
  have hc := hVc.mono fun t (ht : (t : ℝ≥0∞) <
    ((RootZ21.forwardCapacity s (rootEntry r.1).2
      (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω)).toNNReal :
        ℝ≥0∞)) => ht.le
  refine ⟨relativeDriverRead_zero _ _ _, hΓ0,
    isGeneratingTrace_traceDriverRead hgen hc hV0, ?_, hΓc, hvol⟩
  intro t ht
  exact (continuousAt_traceDriverRead hgen hc hV0
    (ENNReal.coe_lt_coe.mpr ht)).comp continuous_real_toNNReal.continuousAt

end InteractingSLE.Theorem14.GW2TipSystem.RootB23

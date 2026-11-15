/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootB23Scale

/-!
# The actual initial experiment in the root's normalized chart

Packet PROVE-T14-GW2ROOT2. Scaling the actual initial relative readers by
`2^k` gives their literal `capR` lifetime, with source trace regularity
and zero boundary occupation. The scaled observations are measurable
in the exact retained root sigma algebra at every sample.
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
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : ℝ≥0)

theorem measurable_rootSigma_scaledRelativeObservationRead {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q))
    (j : Fin ((entryList l).length + 1)) (a v u : ℝ≥0) :
    Measurable[rootSigma hκ h12p βA c₀ h W ζ s r l]
      (fun ω => scaledRelativeObservationRead a s v u (cfRec s W ζ ω,
        stopRec hκ h12p βA c₀ h (schedSpecOf r.1 l) j ω)) := by
  have hm := measurable_rootSigma_relativeObservationRead
    hκ h12p βA c₀ h s W ζ r l j v (u / a ^ 2)
  exact (measurable_const.mul (measurable_fst.comp hm)).prodMk
    (measurable_const.mul (measurable_snd.comp hm))

variable (b : ℝ → ℝ) (jumps : Finset ℝ)
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  (P : Measure Ω) [IsProbabilityMeasure P]

/-- The source first-piece experiment in the normalized root chart has
the literal initial root capacity as lifetime, with its actual observable
driver and trace regularity proved from the original source hypotheses. -/
theorem ae_initial_normalized_readers_regular (h13 : Theorem13Statement.{u})
    (hβA : IsStopLaw.{u} κ βA) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hc₀J : c₀.jumps = jumps) (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y)
    (hh : IsGFFWithBoundaryData P h b jumps) (hcf : IsCenteredCounterflowDriver κ P h W ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) (α : Ω → ℝ≥0 → ℂ)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) ⊤ (α ω))
    {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q) (hroot : rootPt r.1 = 0) :
    let a : ℝ≥0 := 2 ^ r.2
    let v := (rootEntry r.1).2
    let E := canonSpecFam hκ h12p βA c₀ h (schedSpec 0 [rootEntry r.1]) 0
    let γ := GW2aSingle.chosenTrace (fun t ω => (E ω).1 t) (fun ω => (E ω).2)
    ∀ᵐ ω ∂P, α ω s ∈ H → (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ ω q : OnePoint ℂ))
        ((fun q => (α ω q : OnePoint ℂ)) '' Icc 0 s)) (E ω).2 →
      let p := (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω)
      let C := a ^ 2 * (RootZ21.forwardCapacity s v p).toNNReal
      capR hκ h12p βA b jumps c₀ h W ζ s r [] ω = (C : ℝ) ∧
        scaledRelativeDriverRead a s v 0 p = 0 ∧ scaledRelativeTipRead a s v 0 p = 0 ∧
        IsGeneratingTrace (fun u => scaledRelativeDriverRead a s v u p) (C : ℝ≥0∞)
          (fun u => scaledRelativeTipRead a s v u p) ∧
        (∀ t : ℝ, t.toNNReal < C →
          ContinuousAt (fun u : ℝ => scaledRelativeDriverRead a s v u.toNNReal p) t) ∧
        ContinuousOn (fun t : ℝ => scaledRelativeTipRead a s v t.toNNReal p)
          (Icc 0 (C : ℝ)) ∧
        volume {t : ℝ | t ∈ Ioo 0 (C : ℝ) ∧
          scaledRelativeTipRead a s v t.toNNReal p ∉ H} = 0 := by
  have hfirst := ae_initial_relative_readers_regular
    hκ h12p βA b jumps c₀ h W ζ s P h13 hβA hb hc₀J hc₀ hh hcf hζ α hα r hroot
  have hcap := RootZ21.ae_capR_nil_eq_forwardCapacity
    hκ h12p βA b jumps c₀ h W ζ s P h13 hβA hb hc₀J hc₀ hh hcf hζ α hα r hroot
  dsimp only at hfirst hcap ⊢
  filter_upwards [hfirst, hcap] with ω hf hcapω
  intro hsH hv
  obtain ⟨_, _, hgen, hAt, _, _⟩ := hf hsH hv
  let a : ℝ≥0 := 2 ^ r.2
  let v := (rootEntry r.1).2
  let p := (cfRec s W ζ ω, stopRec hκ h12p βA c₀ h (schedSpecOf r.1 []) 0 ω)
  let D := (RootZ21.forwardCapacity s v p).toNNReal
  let C := a ^ 2 * D
  have ha : 0 < a := by dsimp only [a]; positivity
  have hc : ContinuousOn (fun u => relativeDriverRead s v u p)
      {u | (u : ℝ≥0∞) < (D : ℝ≥0∞)} := by
    intro u hu
    have hAtu := hAt u (by simpa only [Real.toNNReal_coe] using ENNReal.coe_lt_coe.mp hu)
    simpa only [Function.comp_def, Real.toNNReal_coe] using
      (hAtu.comp NNReal.continuous_coe.continuousAt).continuousWithinAt
  have hscaled : IsGeneratingTrace (fun u => scaledRelativeDriverRead a s v u p)
      (C : ℝ≥0∞) (fun u => scaledRelativeTipRead a s v u p) := by
    simpa only [C, D, v, p, scaledRelativeDriverRead, scaledRelativeTipRead,
      ENNReal.coe_mul] using
      isGeneratingTrace_scale hgen ha
  have hcont : ContinuousOn (fun u => scaledRelativeDriverRead a s v u p)
      {u | (u : ℝ≥0∞) < (C : ℝ≥0∞)} := by
    simpa only [C, scaledRelativeDriverRead, ENNReal.coe_mul] using
      Sec5.Prop59NodeTree.continuousOn_scale ha hc
  have hCeq : (C : ℝ) = 4 ^ r.2 * RootZ21.forwardCapacity s v p := by
    change ((2 : ℝ) ^ r.2) ^ 2 * (D : ℝ) = _
    rw [Real.coe_toNNReal _ (RootZ21.forwardCapacity_nonneg s v p)]
    congr 1
    rw [pow_two, ← mul_pow]
    norm_num
  refine ⟨(hcapω.2 hsH hv).trans hCeq.symm, scaledRelativeDriverRead_zero _ _ _ _,
    hscaled.1, hscaled, ?_, ?_, ?_⟩
  · intro t ht
    exact (hcont.continuousAt
      ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds
        (ENNReal.coe_lt_coe.mpr ht))).comp continuous_real_toNNReal.continuousAt
  · refine hscaled.2.1.comp continuous_real_toNNReal.continuousOn ?_
    intro t ht
    exact ENNReal.coe_le_coe.mpr (Real.toNNReal_le_iff_le_coe.mpr ht.2)
  · apply measure_mono_null ?_
      (hscaled.volume_setOf_notMem_H hcont (scaledRelativeDriverRead_zero _ _ _ _))
    intro t ht
    refine ⟨ht.1.1.le, ?_, ht.2⟩
    apply ENNReal.coe_lt_coe.mpr
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal t ht.1.1.le]
    exact ht.1.2

end InteractingSLE.Theorem14.GW2TipSystem.RootB23

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A5ClearanceWire
import InteractingSLE.Spec.Wire.PartAClearanceRegularity
import InteractingSLE.Spec.Sec5.CrossRestartLawReduce
import InteractingSLE.Spec.Sec5.CrossRestartLawMeas
import InteractingSLE.Spec.Sec5.CrossRestartMeasPathVersion
import InteractingSLE.Spec.Sec5.Prop411
import InteractingSLE.Spec.Sec5.Prop55
import InteractingSLE.Spec.Sec5.Prop513WireCounterflow
import InteractingSLE.Spec.Sec5.Prop513WireAssembly
import InteractingSLE.Spec.Sec5.Prop513WirePieceLaw

/-! # Part A clearance variants: restart

Packet PROVE-WIRE-PARTA. The source proofs use only Aux. lemma 7 from Part A.
These variants replace the two-crosscut input by protected-ray clearance, using
the existing clearance and inverse-boundary API. All other hypotheses and conclusions
are those of the original consumers; the original declarations are unchanged.
-/

set_option autoImplicit false

section

/- Clearance variants of `Sec5/CrossRestartLawReduce`. -/

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory

open scoped Real NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther Sec2.Assembly

/-- Clearance variant of `counterflowSegmentRestartStatement_of_kernel`; only Aux. lemma 7 is used from Part A. -/
theorem counterflowSegmentRestartStatement_of_kernel_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hK : CounterflowRestartKernelStatement.{u}) (hV : RestartVarMeasurableStatement.{u}) :
    CounterflowSegmentRestartStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨w, η₀, γ₀, ζ₀, hver, hXm⟩ :=
    hV κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨M, β, K, hM, hβ, hKm, hlaw, hdat, hMev⟩ :=
    hK κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w η₀ γ₀ ζ₀ hver hXm
  set X := fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω) with hXdef
  have hγm : ∀ t, Measurable fun s : (PCode × PCode) × ℝ≥0∞ => decPath s t := measurable_decPath
  have hUm : Measurable fun s : (PCode × PCode) × ℝ≥0∞ => s.2 := measurable_snd
  have hγc : ∀ s : (PCode × PCode) × ℝ≥0∞, ContinuousOn (decPath s) {u | (u : ℝ≥0∞) ≤ s.2} :=
    continuousOn_decPath
  refine ⟨(PCode × PCode) × ℝ≥0∞, inferInstance, decPath, fun s => s.2, M, β, X, K, hγm, hUm, hγc, hM, hβ,
    hXm, hKm, hlaw, hdat, ?_⟩
  have hκ' : 0 < 16 / κ := by positivity
  have h7 : Aux7Statement.{0} (16 / κ) := aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  -- Lemma 4.5 under the kernel, integrated back (as in `counterflowSegmentRestartStatement_of_restartLaw`)
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 < r → X ω ∈ restartEvent decPath (fun s => s.2) r := by
    intro r
    set E : Set ((ℝ × BoundaryWord) × ((PCode × PCode) × ℝ≥0∞)) :=
      {p | (r : ℝ) ≤ p.1.1} ∪ univ ×ˢ restartEvent decPath (fun s => s.2) r
    have hE : MeasurableSet E :=
      (measurableSet_le measurable_const (measurable_fst.comp measurable_fst)).union
        (MeasurableSet.univ.prod (measurableSet_restartEvent hγm hUm hγc r))
    have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂(K d), (d, s) ∈ E := by
      filter_upwards [hdat] with d ⟨hd, hfl⟩
      have hd' := isRestartTargetDatum_of_isFig55RestartDatum hκ hκ4 hbd hθ₁ hθ₂ hd
      by_cases hdr : (r : ℝ) ≤ d.1
      · exact Eventually.of_forall fun s => Or.inl hdr
      · push Not at hdr
        filter_upwards [ae_restartEvent_of_isFlowLineTraceLaw hκ' h7 hd' hfl] with s hs
        obtain ⟨hU, hav, him, htr⟩ := hs
        refine Or.inr ⟨mem_univ _, hU, fun t ht => hav t ?_, him, htr⟩
        obtain ⟨x, hx, hxt⟩ := ht
        refine ⟨x, ?_, hxt⟩
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (show d.1 ≤ x from hdr.le.trans hx)
    filter_upwards [ae_mem_of_compProd_eq_prod hM hβ hXm hlaw hE hKE] with ω hω hωM hlt
    rcases hω hωM with h | ⟨-, h⟩
    · exact absurd h (not_le.2 hlt)
    · exact h
  rw [← ae_all_iff] at hr
  filter_upwards [hr, hver, htr', ae_continuousOn_of_isStripCounterflowDriver hcf, hMev]
    with ω hrω ⟨hwη, hwc, hw0, hη₀, hγ₀, hζ₀⟩ htrω hcfω hMω hσζ hηH
  have hωM := hMω hσζ hηH
  refine ⟨hωM, ?_⟩
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (β ω).1
  obtain ⟨hUX, -, -, -⟩ := hrω r₀ hωM hr₀
  have hXω : X ω = restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η ω) σ (ζ' ω) (γ' ω) := by
    rw [hXdef]
    simp only [hη₀, hγ₀, hζ₀]
  rw [hXω] at hUX ⊢
  exact isCounterflowChartContinuation_restartVar (Real.exp_pos _) hwη hwc hw0 hσζ hηH htrω hcfω.1 hcfω.2 hUX

end CrossRestart

end Sec5

end InteractingSLE

end

end

section

/- Clearance variants of `Sec5/CrossRestartLawMeas`. -/

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory

open scoped Real NNReal ENNReal

open QuantumZipper (H)

universe u

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther Sec2.Assembly

section Tools

variable {Ω : Type*} [MeasurableSpace Ω]

end Tools

section Var

variable {Ω : Type*} [MeasurableSpace Ω] {q : ℝ} {U : Ω → ℝ → ℝ} {σ : ℝ} {x₁ : Ω → ℝ}
  {η : Ω → ℝ≥0 → ℂ} {s : ℝ≥0} {ζ' : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
  (hpath : ∀ t, Measurable fun ω => restartPath q (U ω) σ (x₁ ω) (γ ω) t)
  (hηm : ∀ t, Measurable fun ω => η ω t) (hγm : ∀ t, Measurable fun ω => γ ω t) (hζm : Measurable ζ')

end Var

/-- Clearance variant of `counterflowSegmentRestartStatement_of_kernel_of_path`; only Aux. lemma 7 is used from Part A. -/
theorem counterflowSegmentRestartStatement_of_kernel_of_path_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hK : CounterflowRestartKernelStatement.{u}) (hP : RestartPathMeasurableStatement.{u}) :
    CounterflowSegmentRestartStatement.{u} :=
  counterflowSegmentRestartStatement_of_kernel_of_clearance hA hK (restartVarMeasurableStatement_of_path hP)

end CrossRestart

end Sec5

end InteractingSLE

end

end

section

/- Clearance variants of `Sec5/CrossRestartMeasPathVersion`. -/

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory

open scoped Real NNReal ENNReal

open QuantumZipper (H fwdHull extIccPath)

universe u

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open ConformalImage ConformalImageFull Sec4 Restart MarkovOther Sec2.Assembly

section Versions

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

end Versions

section Main

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

end Main

/-- Clearance variant of `counterflowSegmentRestartStatement_of_kernelOn`; only Aux. lemma 7 is used from Part A. -/
theorem counterflowSegmentRestartStatement_of_kernelOn_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hK : CounterflowRestartKernelOnStatement.{u}) : CounterflowSegmentRestartStatement.{u} := by
  intro κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ Ω _ _ P _ h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ
  obtain ⟨w, η₀, γ₀, ζ₀, hver, hXm⟩ :=
    exists_measurable_restartVar (Real.exp_pos (π * x₀)) hη hcf htr' σ
  obtain ⟨M, β, K, hM, hβ, hKm, hlaw, hdat, hMev⟩ :=
    hK κ hκ hκ4 α x₀ a b a' b' θ hbd hθ₁ hθ₂ P h hhm hh η ζ hη W' ζ' γ' hcf htr' hci σ w η₀ γ₀ ζ₀ hver hXm
  set X := fun ω => restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η₀ ω) σ (ζ₀ ω) (γ₀ ω) with hXdef
  have hγm : ∀ t, Measurable fun s : (PCode × PCode) × ℝ≥0∞ => decPath s t := measurable_decPath
  have hUm : Measurable fun s : (PCode × PCode) × ℝ≥0∞ => s.2 := measurable_snd
  have hγc : ∀ s : (PCode × PCode) × ℝ≥0∞, ContinuousOn (decPath s) {u | (u : ℝ≥0∞) ≤ s.2} :=
    continuousOn_decPath
  refine ⟨(PCode × PCode) × ℝ≥0∞, inferInstance, decPath, fun s => s.2, M, β, X, K, hγm, hUm, hγc, hM, hβ,
    hXm, hKm, hlaw, hdat, ?_⟩
  have hκ' : 0 < 16 / κ := by positivity
  have h7 : Aux7Statement.{0} (16 / κ) := aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4
  -- Lemma 4.5 under the kernel, integrated back (as in `counterflowSegmentRestartStatement_of_kernel_of_clearance`)
  have hr : ∀ r : ℚ, ∀ᵐ ω ∂P, ω ∈ M → (β ω).1 < r → X ω ∈ restartEvent decPath (fun s => s.2) r := by
    intro r
    set E : Set ((ℝ × BoundaryWord) × ((PCode × PCode) × ℝ≥0∞)) :=
      {p | (r : ℝ) ≤ p.1.1} ∪ univ ×ˢ restartEvent decPath (fun s => s.2) r
    have hE : MeasurableSet E :=
      (measurableSet_le measurable_const (measurable_fst.comp measurable_fst)).union
        (MeasurableSet.univ.prod (measurableSet_restartEvent hγm hUm hγc r))
    have hKE : ∀ᵐ d ∂(P.restrict M).map β, ∀ᵐ s ∂(K d), (d, s) ∈ E := by
      filter_upwards [hdat] with d ⟨hd, hfl⟩
      have hd' := isRestartTargetDatum_of_isFig55RestartDatum hκ hκ4 hbd hθ₁ hθ₂ hd
      by_cases hdr : (r : ℝ) ≤ d.1
      · exact Eventually.of_forall fun s => Or.inl hdr
      · push Not at hdr
        filter_upwards [ae_restartEvent_of_isFlowLineTraceLaw hκ' h7 hd' hfl] with s hs
        obtain ⟨hU, hav, him, htr⟩ := hs
        refine Or.inr ⟨mem_univ _, hU, fun t ht => hav t ?_, him, htr⟩
        obtain ⟨x, hx, hxt⟩ := ht
        refine ⟨x, ?_, hxt⟩
        rcases hx with hx | hx
        · exact Or.inl hx
        · exact Or.inr (show d.1 ≤ x from hdr.le.trans hx)
    filter_upwards [ae_mem_of_compProd_eq_prod hM hβ hXm hlaw hE hKE] with ω hω hωM hlt
    rcases hω hωM with h | ⟨-, h⟩
    · exact absurd h (not_le.2 hlt)
    · exact h
  rw [← ae_all_iff] at hr
  filter_upwards [hr, hver, htr', ae_continuousOn_of_isStripCounterflowDriver hcf, hMev]
    with ω hrω ⟨hwη, hwc, hw0, hη₀, hγ₀, hζ₀⟩ htrω hcfω hMω hσζ hηH
  have hωM := hMω hσζ hηH
  refine ⟨hωM, ?_⟩
  obtain ⟨r₀, hr₀⟩ := exists_rat_gt (β ω).1
  obtain ⟨hUX, -, -, -⟩ := hrω r₀ hωM hr₀
  have hXω : X ω = restartVar (Real.exp (π * x₀)) (fun t => w t ω) (ζ ω) (η ω) σ (ζ' ω) (γ' ω) := by
    rw [hXdef]
    simp only
    rw [hζ₀]
    exact restartVar_congr (fun t ht => hη₀ t (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht) hσζ))
      fun t ht => hγ₀ t ht.le
  rw [hXω] at hUX ⊢
  exact isCounterflowChartContinuation_restartVar (Real.exp_pos _) hwη hwc hw0 hσζ hηH htrω hcfω.1 hcfω.2 hUX

end CrossRestart

end Sec5

end InteractingSLE

end

end

section

/- Clearance variants of `Sec5/Prop411`. -/

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory

open scoped Real NNReal ENNReal

open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec5

open Sec4 (stripCounterflowChart stripCounterflowPath IsStripCounterflowDriver)

variable {κ α x₀ a b a' b' : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}

/-- Clearance variant of `ae_image_inter_H_subset_stripCounterflowRange`; only Aux. lemma 7 is used from Part A. -/
theorem ae_image_inter_H_subset_stripCounterflowRange_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hK : CrossRestart.CounterflowRestartKernelOnStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α (π / 2) (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h
      η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H) :
    ∀ᵐ ω ∂P, (fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω) ∩ H ⊆
      stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) ⊤ := by
  have hR := CrossRestart.counterflowSegmentRestartStatement_of_kernelOn_of_clearance hA hK
  have h57 := lemma57_of_counterflowSegmentRestart' hR (aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4) hκ hκ4
    hbd (by linarith [Real.pi_pos]) le_rfl hhm hh hη hcf htr' hci hγ hT0 hT
  filter_upwards [h57] with ω ⟨_, hsub, _⟩
  exact (inter_subset_inter_left H hsub).trans (stripCounterflowPath_image_inter_H_subset _ _)

/-- Clearance variant of `ae_liesRightOf_image_of_liesRightOf_counterflow`; only Aux. lemma 7 is used from Part A. -/
theorem ae_liesRightOf_image_of_liesRightOf_counterflow_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    (hK : CrossRestart.CounterflowRestartKernelOnStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hbd : IsFig51Bounds κ a b a' b') (hhm : Measurable h) (hh : IsFig51Field κ α x₀ a b a' b' P h)
    (hη : IsStripFlowLineAt κ α (π / 2) (fig51LowerFrame κ α a b) (fig51UpperFrame κ α x₀ a' b') {0} {x₀} P h
      η ζ)
    (hcf : IsStripCounterflowDriver κ α (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧ Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T ω)
    (hT : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T ω → (t : ℝ≥0∞) < ζ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T ω → η ω t ∈ H)
    {A : Ω → Set ℂ}
    (hcfA : ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) ⊤) (A ω)) :
    ∀ᵐ ω ∂P, LiesRightOf ((fun s : ℝ => η ω s.toNNReal) '' Icc 0 (T ω)) (A ω) := by
  filter_upwards [ae_image_inter_H_subset_stripCounterflowRange_of_clearance hA hK hκ hκ4 hbd hhm hh hη hcf htr' hci hγ
    hT0 hT, hcfA] with ω hsub hω
  exact LiesRightOf.of_inter_H (hω.mono hsub)

end Sec5

end InteractingSLE

end

end

section

/- Clearance variants of `Sec5/Prop55`. -/

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory

open scoped Real NNReal ENNReal

open QuantumZipper (H chiC)

universe u

namespace InteractingSLE

namespace Sec5

open Sec4 (IsStripCounterflowDriver)

/-- Clearance variant of `prop55_of_prop51CondIndep`; only Aux. lemma 7 is used from Part A. -/
theorem prop55_of_prop51CondIndep_of_clearance (h51 : Prop51CondIndepStatement.{u}) (hA : PartAInputsSixteenDivOfClearance)
    (hK : CrossRestart.CounterflowRestartKernelOnStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {x₀ a b a' b' θ₁ θ₂ : ℝ} (h1 : (sleLambda κ - b) / chiC κ ≤ θ₁) (h12 : θ₁ < θ₂)
    (h2 : θ₂ ≤ (a + π * chiC κ - sleLambda κ) / chiC κ)
    (ha' : sleLambda (16 / κ) + (θ₁ + π / 2) * chiC κ ≤ a')
    (hb' : sleLambda (16 / κ) + (3 * π / 2 - θ₁) * chiC κ ≤ b')
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hhm : Measurable h) (hh : IsFig51Field κ 0 x₀ a b a' b' P h)
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}
    (hη₁ : IsStripFlowLineAt κ 0 θ₁ (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} P h η₁ ζ₁)
    (hη₂ : IsStripFlowLineAt κ 0 θ₂ (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀} P h η₂ ζ₂)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {γ' : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ (θ₁ - π / 2) (Real.exp (π * x₀)) P h W' ζ')
    (htr' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) (γ' ω))
    (hci₁ : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η₁ ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hci₂ : CondIndep (MeasurableSpace.comap h inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun ω => η₂ ω t) inferInstance)
      (⨆ t : ℝ≥0, MeasurableSpace.comap (W' t) inferInstance) hhm.comap_le P)
    (hγ : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (γ' ω) ∧ (∀ t, γ' ω t ≠ -1) ∧
      Tendsto (fun t => ‖γ' ω t‖) atTop atTop)
    {T₁ : Ω → ℝ} (hT0 : ∀ᵐ ω ∂P, 0 < T₁ ω)
    (hT₁ : ∀ᵐ ω ∂P, (∀ t : ℝ≥0, (t : ℝ) < T₁ ω → (t : ℝ≥0∞) < ζ₁ ω) ∧
      ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T₁ ω → η₁ ω t ∈ H) :
    ∀ᵐ ω ∂P, LiesRightOf ((fun s : ℝ => η₁ ω s.toNNReal) '' Icc 0 (T₁ ω)) (pathRange (η₂ ω) (ζ₂ ω)) := by
  set α : ℝ := θ₁ - π / 2 with hα
  have hχ := Sec4.chiC_pos hκ hκ4
  obtain ⟨⟨hA', hB', hA0, hB0⟩, hθ', hlo, hhi⟩ := prop55_reduction hκ hκ4 h1 h12 h2 ha' hb'
  -- the field `h + αχ` has the data of Figure 5.1 with the shifted parameters
  have hh' : IsFig51Field κ α x₀ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ)
      P h := by
    unfold IsFig51Field
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsFig51Field at hh
    rwa [fig51LowerFrame_zero, fig51UpperFrame_zero] at hh
  have hbounds : IsFig51Bounds κ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ) :=
    ⟨hA0, hB0, hA', hB'⟩
  -- `η₂` is the flow line of `h + αχ` with the relative angle `θ₂ − α`
  have hη₂' : IsStripFlowLineAt κ α (θ₂ - α) (fig51LowerFrame κ α (a - α * chiC κ) (b + α * chiC κ))
      (fig51UpperFrame κ α x₀ (a' - α * chiC κ) (b' + α * chiC κ)) {0} {x₀} P h η₂ ζ₂ := by
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsStripFlowLineAt at hη₂ ⊢
    rwa [show α + (θ₂ - α) = 0 + θ₂ by ring]
  -- `η₁` is the flow line of `h + αχ` with the relative angle `π/2`
  have hη₁' : IsStripFlowLineAt κ α (π / 2) (fig51LowerFrame κ α (a - α * chiC κ) (b + α * chiC κ))
      (fig51UpperFrame κ α x₀ (a' - α * chiC κ) (b' + α * chiC κ)) {0} {x₀} P h η₁ ζ₁ := by
    rw [fig51LowerFrame_shift, fig51UpperFrame_shift]
    unfold IsStripFlowLineAt at hη₁ ⊢
    rwa [show α + π / 2 = 0 + θ₁ by rw [hα]; ring]
  have hrel : θ₂ - α = θ₂ - θ₁ + π / 2 := by rw [hα]; ring
  have heq51 : Eq51 κ (a - α * chiC κ) (b + α * chiC κ) (θ₂ - α) := by
    rw [hrel]
    exact ⟨(div_le_iff₀ hχ).1 hlo, (le_div_iff₀ hχ).1 hhi⟩
  have hgt : π / 2 < θ₂ - α := by rw [hrel]; exact hθ'
  -- Proposition 5.1: the counterflow lies to the right of `η₂`
  have h5 := (h51 hκ hκ4 α x₀ (a - α * chiC κ) (b + α * chiC κ) (a' - α * chiC κ) (b' + α * chiC κ)
    (θ₂ - α) hbounds heq51 P h hhm η₂ ζ₂ W' ζ' γ' hh' hη₂' hcf htr' hci₂).1 hgt
  have h5' : ∀ᵐ ω ∂P, LiesRightOf (stripCounterflowRange (Real.exp (π * x₀)) (γ' ω) ⊤)
      (pathRange (η₂ ω) (ζ₂ ω)) := by
    filter_upwards [h5, hγ] with ω h5ω hγω
    rwa [hγω.1] at h5ω
  -- Proposition 4.11's containment: `η₁([0, T₁])` is in the counterflow
  exact ae_liesRightOf_image_of_liesRightOf_counterflow_of_clearance hA hK hκ hκ4 hbounds hhm hh' hη₁' hcf htr' hci₁
    (hγ.mono fun ω hω => hω.2) hT0 hT₁ h5'

end Sec5

end InteractingSLE

end

end

section

/- Clearance variants of `Sec5/Prop513WireCounterflow`. -/

noncomputable section

open MeasureTheory Filter Set Topology

open scoped Real NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Wire

open QuantumZipper Sec4 Prop513Target

/-- Clearance variant of `fig51_noReturn_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem fig51_noReturn_of_partA_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ →
      ∀ t : ℝ≥0, 0 < t → γ t ≠ 0 := by
  obtain ⟨_, _, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  exact CfNoReturn.Route.ae_trace_ne_zero_of_isFlowLineDriver hk
    (aux7Statement_sixteen_div_of_partA_of_clearance hA hκ hκ4) hfl hadm

/-- Clearance variant of `fig51_trace_mem_H_of_partA`; only Aux. lemma 7 is used from Part A. -/
theorem fig51_trace_mem_H_of_partA_of_clearance (hA : PartAInputsSixteenDivOfClearance)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  obtain ⟨b₀, J₀, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  exact ae_lifetime_eq_top_and_trace_mem_H_of_noReturn (div_pos (by norm_num) hκ)
    (Theorem15.isOrderedForceWord_flowLine b₀ J₀ 0) hadm
    ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ hC.1
    (fig51_noReturn_of_partA_of_clearance hA hκ hκ4 hb hG hcf)

end InteractingSLE.Sec5.Prop513Wire

end

end

section

/- Clearance variants of `Sec5/Prop513WireAssembly`. -/

noncomputable section

open MeasureTheory Filter Set Topology

open scoped Real NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop513Wire

open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Restart

open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- Clearance variant of `prop513_path_of_partA_reverseVisit`; only Aux. lemma 7 is used from Part A. -/
theorem prop513_path_of_partA_reverseVisit_of_clearance
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{u})
    (hA : PartAInputsSixteenDivOfClearance)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type u} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (htip : ∀ n, Prop59Tips.TipUnboundedStatement P W γ
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n)
      (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
    (htip0 : Prop59Tips.Tip0UnboundedStatement P W
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  let c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hmQ := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hh𝒢
  obtain ⟨ξ, hξm, hξc, hroot, he⟩ := exists_measurable_extreme_tree_of_stagedPiecesRegular
    h44 hκ hκ4 c hc hhQ hE hR hmQ
  have hreg := fig51_trace_mem_H_of_partA_of_clearance hA hκ hκ4 hb hG hcf
  have hζ := hreg.mono fun _ hω => hω.1
  have htrTop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [htr, hζ] with ω hω hζω
    rwa [hζω] at hω
  have hH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H := by
    filter_upwards [hreg, htrTop] with ω hω hγω
    exact hω.2 _ hγω
  have heRaw := ae_driverTree_eq
    (prefixTraceRegularity_of_stagedPiecesRegular h44 hκ hκ4 c hc hhQ hE hR) he
  have h57 := targetLemma57_of_stripReverseVisit (Real.exp_pos _)
    (htrTop.mono fun _ hω => hω.1) hH
    (ae_driverTree_interior h44 hκ hκ4 c hc hhQ hE hR) hVisit
  have hgeom := geometry_of_targetLemma57 h57 hH heRaw hroot
  obtain ⟨L, hLm, hLe⟩ := @exists_measurable_capacity_cones Ω mΩ P 𝒢 ξ hξm hξc
    treeTime descendantIndex treeTime_pos treeTime_mono hroot (hgeom.mono fun _ hω => hω.1)
  obtain ⟨b₀, J₀, _, _, hfl, _⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hdriver : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hC.1.ae_isIntegratedSLEPath, hζ, htrTop] with ω hp hζω hγω
    have hw := hp.2.2.2.1
    rw [hζω] at hw
    exact ⟨continuousOn_univ.1 (by simpa only [ENNReal.coe_lt_top, ofPred_true] using hw), hp.1, hγω⟩
  have hTip := fun n => Prop59Tips.ae_tip_of_unbounded hdriver
    (fun _ => rfl : ∀ ω, extremeAngleTreeCone (capacityTree (driverTree E)) treeTime descendantIndex n ω =
      closure (insert (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω)
        (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n ω))) (htip n)
  have hTip0 := Prop59Tips.ae_tip0_of_unbounded hdriver htip0
  have hk : 4 < 16 / κ := (lt_div_iff₀ hκ).2 (by linarith only [hκ4])
  refine @path_of_tips_ae_cones (16 / κ) _ _ _ _ _ _ Ω mΩ P _ 𝓕 W VL VR B ζ
    hk hC.1 hζ 𝒢 γ (extremeAngleTreeNode (capacityTree ξ) treeTime)
    (extremeAngleTreeDescendants (capacityTree ξ) treeTime descendantIndex) L
    (measurable_extremeAngleTreeNode (measurable_capacityTree hξm) treeTime) hLm
    hLe htrTop hH (hgeom.mono fun _ hω => hω.2.1) (hgeom.mono fun _ hω => hω.2.2) ?_ ?_
  · intro n q hq
    filter_upwards [hTip n q hq, heRaw, hLe] with ω ht heω hlω hqT
    have hn := node_cone_eq heω
    rw [hlω n, hn.2 n]
    apply ht
    rwa [← hn.1 n]
  · intro q hq
    filter_upwards [hTip0 q hq, heRaw] with ω ht heω
    have hn := (node_cone_eq heω).1
    have hr : (fun n => extremeAngleTreeNode (capacityTree ξ) treeTime n ω) =
        fun n => extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω := funext hn
    rwa [hr]

end InteractingSLE.Sec5.Prop513Wire

end

end

section

/- Clearance variants of `Sec5/Prop513WirePieceLaw`. -/

noncomputable section

open MeasureTheory Filter Set Topology

open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Wire

open QuantumZipper Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Restart

open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- Clearance variant of `prop513_path_of_partA_reverseVisit_pieceLaw`; only Aux. lemma 7 is used from Part A. -/
theorem prop513_path_of_partA_reverseVisit_pieceLaw_of_clearance
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDivOfClearance)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    (hTips : TipPieceInputs κ P W γ
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime)
      (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  exact prop513_path_of_partA_reverseVisit_of_clearance h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit
    (fun n => hTips.tip hκ hκ4 n) (hTips.tip0 hκ hκ4)

end InteractingSLE.Sec5.Prop513Wire

end

end

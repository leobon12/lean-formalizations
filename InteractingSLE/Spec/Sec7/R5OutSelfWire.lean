import InteractingSLE.Spec.Sec7.R5OutSelf

/-! # The old deterministic-relative-cover interface follows from the source phase word -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec7.R5Out
open LocalSets WholeField PocketTraversal Lemma71C PocketStop PocketStopSide PocketStopField PocketUnionPt
  PocketCoord PocketJordan PocketWordAssembly PocketSeedOpen R5Phase R5Enl PhaseCont PocketCoupling PocketAdapt
open PocketWordPerQ R5Ref
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ rL rR : ℝ} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {W' : ℝ≥0 → Ω → ℝ}
  {G : Set Ω} {h₀ : Ω → DistOn upperHalfPlaneOpens} {u : ℂ → ℝ}

/-- The bounded outer phase word supplies the deterministic relative cover. -/
theorem twoSeedRelativeCoverInput_of_phaseWord_outer
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hηm : ∀ t, 0 ≤ t → Measurable fun ω => η ω t)
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedPhaseWordInput κ rL rR (wallsSigma P R L) P R L r η G h₀ u) :
    TwoSeedR5RelativeCoverInputOn κ rL rR P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, hWord⟩ := hin A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAll R L r η ψ ω) :=
    fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H :=
    fun ω hω => (hψ ω hω).2.2.2.1
  have hcd := shiftChart_dom_facts hCo hCH hψc n
  have hFixed := R5OLaw.r7_fixed_inputs_outer hRc hLc hRm hLm hGm hG hA hAG
    (fun ω hω => hcfg ω (hAG hω)) hψ hψm hηm
    (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1) (fun ω hω => (hcd ω hω).2.2)
  refine ⟨n, hn, a, δ, fun q => ⟨(fun _ => q), (fun _ => ∅), fun _ => le_rfl,
    fun _ => finite_empty, (hWord q).1, ?_, ?_⟩⟩
  · intro i z
    exact ((measurable_indicator_fwd_relChart_fixed hγ (fun ω hω => (hcd ω hω).1)
      hFixed.2.2.2.1 q (hFixed.2.2.2.2 q) z).2).mono le_sup_right le_rfl
  · exact r5Cover_self_of_phaseWord hγ (fun ω hω => (hcd ω hω).1)
      (relativeReference_facts hγ hCo hCH hψc hcd q).2.1 (hWord q)

/-- The Inf outer phase word supplies the deterministic relative cover. -/
theorem twoSeedRelativeCoverInputInf_of_phaseWord_outer
    (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    (hηm : ∀ t, 0 ≤ t → Measurable fun ω => η ω t)
    (hGm : MeasurableSet[wallsSigma P R L] G)
    (hcfg : ∀ ω ∈ G, HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hin : TwoSeedPhaseWordInputInf κ rL rR (wallsSigma P R L) P R L r η G h₀ u) :
    TwoSeedR5RelativeCoverInputInfOn κ rL rR P R L r η G h₀ u := by
  intro A hA hAG hPA ψ hψ hψm
  obtain ⟨n, hn, a, δ, hWord⟩ := hin A hA hAG hPA ψ hψ hψm
  have hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hγ : ∀ ω ∈ A, IsDrivenCurve (travAllInf R L r η ψ ω) :=
    fun ω hω => ((hcfg ω (hAG hω)).props (hψ ω hω)).1
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω (hAG hω)).isOpen_changePocket (hG ω (hAG hω)).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω (hAG hω)).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H :=
    fun ω hω => (hψ ω hω).2.2.2.1
  have hcd := shiftChart_dom_facts hCo hCH hψc n
  have hFixed := R5OLaw.r7_fixed_inputs_outerInf hRc hLc hRm hLm hGm hG hA hAG
    (fun ω hω => hcfg ω (hAG hω)) hψ hψm hηm
    (fun ω hω => (hcd ω hω).1) (fun ω hω => (hcd ω hω).2.1) (fun ω hω => (hcd ω hω).2.2)
  refine ⟨n, hn, a, δ, fun q => ⟨(fun _ => q), (fun _ => ∅), fun _ => le_rfl,
    fun _ => finite_empty, (hWord q).1, ?_, ?_⟩⟩
  · intro i z
    exact ((measurable_indicator_fwd_relChart_fixed hγ (fun ω hω => (hcd ω hω).1)
      hFixed.2.2.2.1 q (hFixed.2.2.2.2 q) z).2).mono le_sup_right le_rfl
  · exact r5Cover_self_of_phaseWord hγ (fun ω hω => (hcd ω hω).1)
      (relativeReference_facts hγ hCo hCH hψc hcd q).2.1 (hWord q)

end InteractingSLE.Sec7.R5Out

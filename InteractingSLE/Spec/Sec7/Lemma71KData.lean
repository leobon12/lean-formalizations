/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71KSpace
import InteractingSLE.Spec.Sec7.Lemma71DTop

/-!
# `IsPocketChartData` from the pocket construction and the fixed-time coupling clause

Packet PROVE-LEMMA71K. The pocket construction of `Lemma71KSpace` supplies every clause of `Lemma72B.IsPocketChartData`
except the chart coupling clause, including the three structure clauses (S1)–(S3). This file assembles them:

* the filtration is the usual augmentation of the **prefix filtration** `prefixFiltrationOf σ(β, α) γ'` (the outer
  curves and the filled prefixes of the mapped segment up to capacity time `t`), the driver is the capacity driver
  `segDriver` of the mapped segment and the terminal time its capacity lifetime `capLife`;
* the chart may carry the **inherited branch**: its lift is shifted by `2πn` for a `σ(β, α)`-measurable integer `n`
  (`Lemma71E.shiftLift`; the normalization (2) of the supplement, Aux. 119, determines `n`);
* (S3) holds because the prefix events of `γ'` are events of `σ(β) ∨ σ(α) ∨ σ(γ) ∨ 𝒩`.

**`isPocketChartData_of_isPocketConstruction`**: `IsPocketChartData` from `IsPocketConstruction` and the chart coupling
clause **at fixed times** (`Lemma71D.IsChartCouplingCharFunConst`) for that filtration (passed to all stopping times of
its usual augmentation by `Lemma71D.isChartCouplingCharFun_usualAugmentation`). Conditional helper: the fixed-time
coupling clause is the remaining content of Lemma 7.1 (see the handoff).

`chartField`, `isChartTransport_chartField`: the pulled-back field `h_ψ = h ∘ ψ⁻¹ + a + k · lift ∘ ψ⁻¹` of
`Lemma72B.PocketJointStatement`, as an explicit function of the chart and the field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71K

open QuantumZipper (H Hbar)
open MartChar Coupling Lemma71C Lemma71D Lemma71E

/-! ### The pulled-back field -/

/-- **The pulled-back field of Lemma 7.1**: the chart transport `h ∘ ψ⁻¹ + a + k · lift ∘ ψ⁻¹` of `h` for a conformal
chart (`Chart.chartTransport` with `σ = 1`), and `0` for a non-conformal chart. -/
def chartField (c : Chart) (a k : ℝ) (h : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  open Classical in if hc : c.IsConformal then Chart.chartTransport hc 1 a k h else 0

/-- **The pulled-back field is the chart transport** (`IsChartTransport` with `σ = 1`) for a conformal chart with a
continuous lift. -/
theorem isChartTransport_chartField {c : Chart} (hc : c.IsConformal) (hl : ContinuousOn c.2.2 c.dom) (a k : ℝ)
    (h : DistOn upperHalfPlaneOpens) : IsChartTransport c 1 a k h (chartField c a k h) := by
  classical
  have hcont : ContinuousOn (fun w => c.2.2 (c.2.1 w)) H := by
    refine hl.comp hc.1.continuousOn fun w hw => ?_
    show c.2.1 w ∈ (c.dom : Set ℂ)
    rw [hc.coe_dom]
    exact mem_image_of_mem _ hw
  have e : chartField c a k h = Chart.chartTransport hc 1 a k h := by
    simp only [chartField, hc, ↓reduceDIte]
  rw [e]
  exact Chart.isChartTransport_chartTransport hc
    (hcont.locallyIntegrableOn QuantumZipper.isOpen_H.measurableSet) 1 a k h

/-! ### The assembly -/

/-- **(S3) for a prefix filtration**: if `𝓐₀ ≤ 𝓑` and the coordinates of a segment curve `γ'` are `𝓑`-measurable, the
usual augmentation of `prefixFiltrationOf 𝓐₀ γ'` lies in `𝓑 ∨ 𝒩` at every time. -/
theorem usualAugmentation_prefixFiltrationOf_le {Ω : Type*} {𝓐₀ 𝓑 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} (h𝓐 : 𝓐₀ ≤ 𝓑) {γ' : Ω → ℝ → ℂ}
    (hseg : ∀ ω, IsSegCurve (γ' ω)) (hm : ∀ u, Measurable[𝓑] fun ω => γ' ω u) (t : ℝ≥0) :
    usualAugmentation (prefixFiltrationOf (mΩ := mΩ) 𝓐₀ γ') P t ≤ 𝓑 ⊔ Ito.nullSets P := by
  rw [Ito.usualAugmentation_apply]
  refine (iInf₂_le (t + 1) (lt_add_one t)).trans ?_
  rw [Ito.nullAugmented_apply]
  refine sup_le (inf_le_left.trans (sup_le (h𝓐.trans le_sup_left) ?_)) le_sup_right
  refine MeasurableSpace.generateFrom_le ?_
  rintro s ⟨r, -, n, k, rfl⟩
  exact (le_sup_left : 𝓑 ≤ 𝓑 ⊔ Ito.nullSets P) _
    (@measurableSet_prefixEvent Ω 𝓑 γ' hseg (fun u _ => hm u) r n k)


section Assembly

variable {κ θ₁ θ₂ a b : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

/-- **`IsPocketChartData` from the pocket construction and the fixed-time chart coupling clause.** On a three-curve
space, for a pocket construction `(C, c, γ')` (`IsPocketConstruction`) and a `σ(β, α)`-measurable branch shift `n`, if
the chart coupling clause holds at fixed times for the prefix filtration of `σ(β, α)` and `γ'`, with the chart lift
shifted by `2πn`, then `IsPocketChartData` holds for the usual augmentation of that filtration, the capacity driver of
`γ'` and its capacity lifetime, including (S1)–(S3). Conditional helper. -/
theorem isPocketChartData_of_isPocketConstruction [IsProbabilityMeasure P]
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ) {C : Ω → Set ℂ} {c : Ω → Chart}
    {γ' : Ω → ℝ → ℂ} (hpc : IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' k : ℝ}
    (hcf : IsChartCouplingCharFunConst κ (fun _ : Fin 1 => cpf2RhoL κ θ₂) (fun _ : Fin 1 => cpf2RhoR κ θ₁) P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' k h) :
    Lemma72B.IsPocketChartData κ θ₁ θ₂ P β α γ h
      (usualAugmentation (prefixFiltrationOf (mΩ := mΩ)
        (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ') P)
      γ' (fun s ω => segDriver (γ' ω) s) (fun ω => capLife (γ' ω)) (fun ω => shiftLift (c ω) (n ω)) a' k := by
  obtain ⟨hC, hCm, hconf, hdom, hfm, hlm, hlc, -, -, hfr, hseg, hγ'm, -⟩ := hpc
  have hh : Measurable h := hS.1.1
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, -⟩ := hS
  have hβm : Measurable β := measurable_pi_iff.2 hβ62.2.2.2.1
  have hαm : Measurable α := measurable_pi_iff.2 hα62.2.2.2.1
  have hγm : Measurable γ := measurable_pi_iff.2 hγ62.2.2.2.1
  have h₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := (hβm.prodMk hαm).comap_le
  have h𝓑 : MeasurableSpace.comap β MeasurableSpace.pi ⊔ MeasurableSpace.comap α MeasurableSpace.pi ⊔
      MeasurableSpace.comap γ MeasurableSpace.pi ⊔ Ito.nullSets P ≤ mΩ :=
    sup_le (sup_le (sup_le hβm.comap_le hαm.comap_le) hγm.comap_le) (Ito.nullSets_le P)
  have hγ'mΩ : ∀ u, Measurable fun ω => γ' ω u := fun u => (hγ'm u).mono h𝓑 le_rfl
  have hpm : ∀ r n k, MeasurableSet (prefixEvent γ' r n k) := fun r n k =>
    measurableSet_prefixEvent hseg (fun u _ => hγ'mΩ u) r n k
  set 𝓐 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' with h𝓐def
  have hpre : IsPrefixAdapted 𝓐 γ' := isPrefixAdapted_prefixFiltrationOf _ γ' hpm
  have hle := Ito.le_usualAugmentation 𝓐 P
  have h𝓐₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ usualAugmentation 𝓐 P 0 :=
    (le_prefixFiltrationOf h₀ γ' 0).trans (hle 0)
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (hC ω).1
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c ω).dom} := fun z => by
    have e : {ω | z ∈ (c ω).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C hCo hCm z
  have hlm' : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator fun ω => (shiftLift (c ω) (n ω)).2.2 z) := fun z =>
    @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn z
      (hdomm z) (hlm z)
  have hcc : ∀ ω, (shiftLift (c ω) (n ω)).IsConformal := fun ω => isConformal_shiftLift (hconf ω) (n ω)
  have hlc' : ∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (shiftLift (c ω) (n ω)).dom := fun ω =>
    continuousOn_shiftLift (hlc ω) (n ω)
  have hc : ∀ ω, ContinuousOn (fun s => segDriver (γ' ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ' ω)} :=
    fun ω => (hseg ω).segDriver_spec.2.1
  refine ⟨Ito.isRightContinuous_usualAugmentation 𝓐 P,
    fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0, Eventually.of_forall fun ω => hseg ω,
    fun ω => (hseg ω).segDriver_spec.1, hc, adaptedBefore_segDriver hseg fun r n j => hle r _ (hpre r n j),
    Eventually.of_forall fun ω => (hseg ω).segDriver_spec.2.2, hh, hcc, fun z => h𝓐₀ _ (hdomm z),
    fun z => (hfm z).mono h𝓐₀ le_rfl, fun z => (hlm' z).mono h𝓐₀ le_rfl, hlc', ?_, fun z r => ?_, hfm, hlm', ?_,
    ?_⟩
  · exact isChartCouplingCharFun_usualAugmentation hh hcc hlc' hc
      (fun i ω => continuousOn_geomL hc LP.twoSeedXL i ω) (fun i ω => continuousOn_geomR hc LP.twoSeedXR i ω)
      (fun ω t ht => geomL_le_le_geomR hc LP.twoSeedXL LP.twoSeedXR ht) hcf
  · have e : {ω | closedBall z r ⊆ ((shiftLift (c ω) (n ω)).dom : Set ℂ)} = {ω | closedBall z r ⊆ C ω} := by
      ext ω
      show closedBall z r ⊆ ((c ω).dom : Set ℂ) ↔ _
      rw [hdom ω]
      exact Iff.rfl
    rw [e]
    exact hCm z r
  · filter_upwards [hfr] with ω hω
    show frontier ((c ω).dom : Set ℂ) ∩ H ⊆ _
    rw [hdom ω]
    exact hω
  · intro t
    exact (usualAugmentation_prefixFiltrationOf_le (P := P) ((comap_pair_le β α γ).trans le_sup_left) hseg hγ'm
      t).trans (sup_le le_rfl le_sup_right)

end Assembly

end InteractingSLE.Sec7.Lemma71K

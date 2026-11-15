/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS4

/-!
# GB6's relative safe law, part 5: the reduction to the line data

Packet PROVE-GB6-RELSAFE2. `RelSafeS3.hasRelSafe_of_lines` proves `HasRelSafe` for one version and one word type from
the data of K2's lines step at deterministic physical times. This file names that data and proves
`Q3Stop.GB6RelSafeRStatement` from it:

* **`HasGB6LineData`**: the line kernels and means (`hker`, `hmean`: Aux. 77/79 at the physical lines) and the
  history-marked locality of the physical union (`hloc`, `hBK`, …), for one measurable version `W` of the counterflow
  driver, a good set `GT`, a version `(R, V)` and a type `w`;
* **`HasGB6SafeMeas`**: the safe events `{a(t) < V, C ∩ K̃_{a(t)} = ∅}` are physical events at `t`;
* **`GB6LineDataStatement`**: both, in GB6's setting (binders of `GB6RelSafeRStatement`), for every measurable
  version of the counterflow driver, good set, R-form version and type;
* the wiring proves everything else: a measurable version of the counterflow driver (`cfKW`, equal to the driver on
  `{ζ = ⊤}`), the transfer of the version to it (`isGB6RelVersionR_congr`), the good set (`RelSafe.exists_goodSet`),
  the counterflow's admissibility in data form (`GB6.gb6_admL`, `gb6_admR`), the cut chart field and its
  integrability (`RelSafeS4`), and the passage back to the original chart field (`hasRelSafe_of_eqOn`):
  **`gb6RelSafeRStatement_of_lineData`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Supp8.RelSafeS

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.RelSafe Restart Restart.DomainMarkov.K2
  Restart.FCDet Sec7.PocketTraversal Sec7.StripSysField

/-! ### The line data -/

section Data

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **GB6's line data** (the inputs of `hasRelSafe_of_lines` that are not proved there): for a measurable counterflow
driver `W`, a good set `GT`, a version `(R, V)` and a type `w`, with the relative clock
`a(t) = min(physClock t, V)` and the live event of the type: the conditioning σ-algebras `𝒢L t ⊇ 𝓖_t`, the line means
`M t` with the Gaussian line kernels (Aux. 77 at the physical lines) and the chart transport of `M t` equal to the
canonical relative mean (Aux. 79), and the history-marked locality of the physical union `B t` for the centred field
with marks `ℋ t ⊇ 𝓖_t`, whose complement is the inverse relative chart image of the complement of the relative
hull. -/
def HasGB6LineData (κ θ : ℝ) (c : BoundaryWord) (P : Measure Ω) (h' Hc : Ω → DistOn upperHalfPlaneOpens)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r)) (w : WordType) : Prop :=
  ∃ (𝒢L : ℝ≥0 → MeasurableSpace Ω) (M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (B : ℝ≥0 → Ω → Set ℂ),
    (∀ t, physFilt hrec hWm P t ≤ 𝒢L t) ∧ (∀ t, 𝒢L t ≤ mΩ) ∧
    (∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
      min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      tsupport φ ⊆ (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) →
      P[fun ω => Complex.exp (Complex.I * (h' ω φ : ℂ)) | 𝒢L t] ω =
        Complex.exp (Complex.I * (M t ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((relChart (gb6Rec s Wα ζα ω)).2.1 '' (H \ fwdHull
            (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)) φ φ : ℝ) : ℂ))) ∧
    (∀ (t : ℝ≥0) (ψ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w →
      min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      Disjoint (tsupport ψ) (fwdHull (fun r : ℝ => R r.toNNReal ω)
        (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) →
      Chart.chartTransport (isConformal_relChart (gb6Rec s Wα ζα ω)) 1 (2 * Real.pi * chiC (16 / κ))
          (chiC (16 / κ)) (M t ω) ψ =
        ∫ z, couplingMean (16 / κ) (fun r : ℝ => R r.toNNReal ω)
          (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal
          (DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
            (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (gb6Rec s Wα ζα ω, relVar Hc R V ω))
            (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (gb6Rec s Wα ζα ω, relVar Hc R V ω)) ω
            (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal) z * ψ z) ∧
    InnerProductSpace.HarmonicOnNhd u₀ H ∧
    LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h' u₀) P ∧
    (∀ t, physFilt hrec hWm P t ≤ ℋ t) ∧ (∀ t, ℋ t ≤ mΩ) ∧
    (∀ t, Measurable[mΩ, hittingSigma] (B t)) ∧ (∀ t ω, B t ω ⊆ H ∧ IsOpen (H \ B t ω)) ∧
    (∀ t, WholeField.IsHistoryAvoidanceLocal (ℋ t) (B t) (WholeField.centredField h' u₀) P) ∧
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ω ∈ liveEv κ θ c s Wα ζα w → min (physClock s W Wα ζα GT t ω) (V ω) < V ω →
      H \ B t ω = (relChart (gb6Rec s Wα ζα ω)).2.1 ''
        (H \ fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)

/-- **GB6's safe events are physical**: for every compact test support and every finite family of rational closed
balls, `{a(t) < V, C ∩ K̃_{a(t)} = ∅}` is an event of the physical σ-algebra at `t`. -/
def HasGB6SafeMeas (P : Measure Ω) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (s : ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (hrec : Measurable (gb6Rec s Wα ζα)) (hWm : ∀ r, Measurable (W r)) :
    Prop :=
  (∀ (ψ : TestOn upperHalfPlaneOpens) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω ∧ Disjoint (tsupport ψ)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)}) ∧
    ∀ (Fb : Finset (ℚ × ℚ × ℚ)) t, MeasurableSet[physFilt hrec hWm P t]
      {ω | min (physClock s W Wα ζα GT t ω) (V ω) < V ω ∧ Disjoint (Coupling.ballsK Fb)
        (fwdHull (fun r : ℝ => R r.toNNReal ω) (min (physClock s W Wα ζα GT t ω) (V ω)).toNNReal)}

end Data

/-! ### The modified counterflow driver and the version -/

section Version

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {s : ℝ≥0} {W W' Wα : ℝ≥0 → Ω → ℝ}
  {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **A version for the counterflow driver is a version for every pathwise almost surely equal driver.** -/
theorem isGB6RelVersionR_congr (hWW : ∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω)
    (hv : HullId.IsGB6RelVersionR s P W Wα ζα γ α R V) : HullId.IsGB6RelVersionR s P W' Wα ζα γ α R V := by
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, hρ⟩ := hv
  refine ⟨⟨h1, h2, h3, h4, h5, h6, ?_⟩, hρ⟩
  filter_upwards [h7, hWW] with ω hω hW hs hsH
  have e : (fun r : ℝ => W' r.toNNReal ω) = fun r : ℝ => W r.toNNReal ω := funext fun r => hW _
  have ec : ∀ t, gb6Clock s W' Wα ω t = gb6Clock s W Wα ω t := fun t => by
    unfold gb6Clock
    rw [e]
  obtain ⟨hV0, hlt, hhull⟩ := hω hs hsH
  refine ⟨hV0, fun u hu => ?_, fun t ht hle => ?_⟩
  · obtain ⟨t, ht, hut⟩ := hlt u hu
    exact ⟨t, ht, by rw [ec]; exact hut⟩
  · rw [ec] at hle ⊢
    rw [hhull t ht hle, e]

end Version

/-! ### The named input and the wiring -/

/-- **Named input: GB6's line data** (binders of `Q3Stop.GB6RelSafeRStatement`; for every measurable version `W'` of
the counterflow driver, every good set, every R-form version for `W'` and every type): `HasGB6LineData` and
`HasGB6SafeMeas`. -/
def GB6LineDataStatement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    ∀ (hfl : IsFlowLineDriver κ b J θ P h Wα ζα),
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc ω)) →
    ∀ c : BoundaryWord, c.jumps = J → (∀ y ∉ J, c.fn y = b y) →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (hW'm : ∀ r, Measurable (W' r)), (∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω) →
    ∀ GT : Set Ω, (∀ ω ∈ GT, PhysGood s W' Wα ζα γ α ω) → MeasurableSet GT →
      (∀ᵐ ω ∂P, ω ∈ GT ↔ gb6Rec s Wα ζα ω ∈ gb6TS s) →
    ∀ (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), HullId.IsGB6RelVersionR s P W' Wα ζα γ α R V →
    ∀ w : WordType,
      HasGB6LineData κ θ c P h' Hc W' Wα ζα GT s R V (measurable_recOf_cfE hfl s).2 hW'm w ∧
        HasGB6SafeMeas P W' Wα ζα GT s R V (measurable_recOf_cfE hfl s).2 hW'm

/-- The chart field cut to the record event. -/
def cutField {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (Hc : Ω → DistOn upperHalfPlaneOpens)
    (ω : Ω) : DistOn upperHalfPlaneOpens :=
  open Classical in if gb6Rec s Wα ζα ω ∈ gb6TS s then Hc ω else 0

theorem cutField_apply {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞)
    (Hc : Ω → DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    (fun ω => cutField s Wα ζα Hc ω φ) = (gb6Rec s Wα ζα ⁻¹' gb6TS s).indicator fun ω => Hc ω φ := by
  classical
  funext ω
  unfold cutField
  rw [Set.indicator_apply]
  by_cases hω : gb6Rec s Wα ζα ω ∈ gb6TS s
  · simp only [mem_preimage, hω, ↓reduceIte]
  · simp only [mem_preimage, hω, ↓reduceIte]
    rfl

theorem measurable_cutField {Ω : Type*} [MeasurableSpace Ω] {s : ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    (hrec : Measurable (gb6Rec s Wα ζα)) {Hc : Ω → DistOn upperHalfPlaneOpens} (hHc : Measurable Hc) :
    Measurable (cutField s Wα ζα Hc) := by
  classical
  exact Measurable.ite (hrec (measurableSet_gb6TS s)) hHc measurable_const

/-- **`GB6RelSafeRStatement` from GB6's line data.** -/
theorem gb6RelSafeRStatement_of_lineData (hL : GB6LineDataStatement.{u}) : GB6RelSafeRStatement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR hcomp hfl hα s Hc
    hHcm hHc c hcJ hcb R V hver w
  have hrec : Measurable (gb6Rec s Wα ζα) := (measurable_recOf_cfE hfl s).2
  have hβ := measurable_gb6WordOfRec κ θ c
  -- a measurable version of the counterflow driver
  obtain ⟨h''c, 𝓕c, VLc, VRc, Bc, -, hCc⟩ := id hcf
  have hX := hCc.2.2.2.1
  set W' : ℝ≥0 → Ω → ℝ := Theorem14.GW2JointKernel.cfKW W ζ with hW'def
  have hW'm : ∀ r, Measurable (W' r) := by
    intro r
    have hlive : MeasurableSet {ω | (r : ℝ≥0∞) < ζ ω} := by
      have := hX r univ MeasurableSet.univ
      simpa only [mem_univ, and_true] using this
    refine measurable_of_isOpen fun O hO => ?_
    have e : W' r ⁻¹' O = ({ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VLc i r ω, fun i => VRc i r ω) ∈
        O ×ˢ univ}) ∪ ({ω | (r : ℝ≥0∞) < ζ ω}ᶜ ∩ {_ω | (0 : ℝ) ∈ O}) := by
      ext ω
      simp only [hW'def, Theorem14.GW2JointKernel.cfKW, mem_preimage, mem_union, mem_ofPred_eq, mem_prod,
        mem_univ, and_true, mem_inter_iff, mem_compl_iff]
      by_cases hω : (r : ℝ≥0∞) < ζ ω
      · simp [hω]
      · simp [hω]
    rw [e]
    exact (hX r _ (hO.measurableSet.prod MeasurableSet.univ)).union
      (hlive.compl.inter (MeasurableSet.const _))
  have hWW : ∀ᵐ ω ∂P, ∀ t, W' t ω = W t ω := by
    filter_upwards [hcomp] with ω hω t
    simp only [hW'def, Theorem14.GW2JointKernel.cfKW, hω.1, ENNReal.coe_lt_top, ↓reduceIte]
  -- the good set for the modified driver
  have hW'good : ∀ᵐ ω ∂P, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      IsGeneratingTrace (fun t => W' t ω) ⊤ (γ ω) := by
    filter_upwards [hcomp, hWW, ae_driver_zero_continuousOn hcf] with ω hω hW hd
    have e : (fun t => W' t ω) = fun t => W t ω := funext hW
    refine ⟨?_, (hW 0).trans hd.1, ?_⟩
    · rw [e, ← continuousOn_univ]
      refine hd.2.mono fun t _ => ?_
      simp only [mem_ofPred_eq, hω.1, ENNReal.coe_lt_top]
    · rw [e]
      exact hω.2.1
  obtain ⟨GT, hGT, hGTm, hGTae⟩ := exists_goodSet (θ := θ) hκ hκ4 hfl hα hW'good s
  have hver' := isGB6RelVersionR_congr hWW hver
  -- the cut chart field
  set Hc' := cutField s Wα ζα Hc with hHc'def
  have hHc'm : Measurable Hc' := measurable_cutField hrec hHcm
  have hHc' : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) (Hc' ω) := by
    filter_upwards [hHc, ae_gb6RecGood hfl hα s] with ω hω hg hs hsH
    have hm : gb6Rec s Wα ζα ω ∈ gb6TS s := (mem_gb6TS_iff hg).1 ⟨hs, hsH⟩
    simp only [hHc'def, cutField, hm, ↓reduceIte]
    exact hω hs hsH
  -- admissibility in data form
  obtain ⟨cw, hcwJ, hcwb⟩ := BoundaryWord.exists_fn_eq hb
  have hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα :=
    (isFlowLineDriver_congr_of_eqOn hb c.isPiecewiseConstantBoundaryData J hcb).2 (hcJ ▸ hfl)
  have hk : 0 < 16 / κ := by positivity
  have hG' : IsGFFWithBoundaryData P h' b' J' :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk hb' hcf
  have hcL := gb6_admL hκ hb hG hb' hG' hT hadmR hcJ hcb
  have hcR := gb6_admR hκ hb hG hb' hG' hT hadmL hcJ hcb
  have hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => Hc' ω φ) P := fun φ => by
    rw [hHc'def, cutField_apply]
    exact integrable_indicator_chartField (θ := θ) hκ hG hflc hα s hHcm hHc φ
  -- the line data
  obtain ⟨hD, hS⟩ := hL κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hG hb' hT hcf hadmL hadmR
    hcomp hfl hα s Hc' hHc'm hHc' c hcJ hcb W' hW'm hWW GT hGT hGTm hGTae R V hver' w
  obtain ⟨𝒢L, M, u₀, ℋ, B, h𝒢L, h𝒢Lm, hker, hmean, hu₀, hh0, h𝓖ℋ, hℋ, hBm, hBc, hloc, hBK⟩ := hD
  have hh'm : Measurable h' := by
    have e : h' = fun ω => Chart.chartTransport Chart.isConformal_infinitySourceChart (-1)
        (-(Real.pi * QuantumZipper.chiC κ)) (QuantumZipper.chiC (16 / κ)) (h ω) := funext fun ω =>
      (hT ω).eq_chartTransport Chart.isConformal_infinitySourceChart
        (Chart.locallyIntegrableOn_of_continuousOn Chart.continuousOn_infinitySourceChart_lift)
    rw [e]
    exact (Chart.measurable_chartTransport _ _ _ _).comp hG.1
  have hmain := hasRelSafe_of_lines (c := c) hκ hκ4 hθ₁ hθ₂ hfl hα hT hh'm hHc'm hHc' (J'.image fun w => -w⁻¹)
    hcL hcR hver' hW'm hGT hGTm hGTae w 𝒢L h𝒢L h𝒢Lm M hker hmean hu₀ hh0 ℋ h𝓖ℋ hℋ B hBm hBc hloc hBK hS.1 hS.2
    hint
  refine hasRelSafe_of_eqOn hβ (measurableSet_gb6TS s) (hrec.prodMk (measurable_relVar hHcm hver.1.1
    hver.1.2.2.2.2.1)) (hrec.prodMk (measurable_relVar hHc'm hver.1.1 hver.1.2.2.2.2.1)) (fun _ => rfl)
    (fun ω hω => ?_) hmain
  have hω' : gb6Rec s Wα ζα ω ∈ gb6TS s := hω
  simp only [relVar, hHc'def, cutField, hω', ↓reduceIte]

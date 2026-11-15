/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCPlumbAssembly
import InteractingSLE.Spec.Restart.FCAux79Mean

/-!
# First-contact boxes and the active component at later lines

The physical domain corresponding to a chart hull is `H \ fillH (lineK d t ω)`.
It is one component of the complement of the shifted union. The entire complement
of the union can also contain bounded pockets.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open FCAux79 Sec7.PocketTraversal DomainMarkov

variable {Ω : Type*}

/-- The active physical domain at the later first-contact line. -/
def lineDomain (d : PairData Ω) (t : ℝ≥0) (ω : Ω) : Set ℂ :=
  H \ fillH (lineK d t ω)

/-- Boxes also bounding the later physical time; their union still covers the meeting branch. -/
def lineBox (d : PairData Ω) (t : ℝ≥0) (m : ℕ) : Set Ω :=
  meetBox d m ∩ {ω | d.s₀ ω + t < m}

theorem lineBox_subset_meetBox (d : PairData Ω) (t : ℝ≥0) (m : ℕ) :
    lineBox d t m ⊆ meetBox d m := inter_subset_left

theorem exists_mem_lineBox {d : PairData Ω} {ω : Ω} (hω : ω ∈ meetSet d) (t : ℝ≥0) :
    ∃ m : ℕ, ω ∈ lineBox d t m := by
  obtain ⟨hE, hζ₁, hζ₂⟩ := mem_meetSet_iff.1 hω
  obtain ⟨m, hm⟩ := exists_nat_gt (max (d.s₀ ω + t) (d.t₀ ω))
  have hs : d.s₀ ω + t < m := (le_max_left _ _).trans_lt hm
  have ht : d.t₀ ω < m := (le_max_right _ _).trans_lt hm
  exact ⟨m, mem_meetBox_iff.2 ⟨hE, le_self_add.trans_lt hs, ht, hζ₁, hζ₂⟩, hs⟩

theorem iUnion_lineBox (d : PairData Ω) (t : ℝ≥0) :
    ⋃ m : ℕ, lineBox d t m = meetSet d := by
  ext ω
  constructor
  · intro hω
    obtain ⟨m, hm⟩ := mem_iUnion.1 hω
    exact mem_iUnion.2 ⟨m, hm.1⟩
  · intro hω
    exact mem_iUnion.2 (exists_mem_lineBox hω t)

section Meas

variable [mΩ : MeasurableSpace Ω] {d : PairData Ω}

theorem measurableSet_lineBox (hd : d.IsMeasGood) (P : Measure Ω) (t : ℝ≥0) (m : ℕ) :
    MeasurableSet (lineBox d t m) :=
  ((retSigma_le P) _ (hd.measurableSet_meetBox P m)).inter
    (measurableSet_lt (hd.measurable_s₀.add measurable_const) measurable_const)

/-- The later active domain is the component of any one of its points. -/
theorem lineDomain_eq_connectedComponentIn (hd : d.IsMeasGood) {ω : Ω} (hω : ω ∈ d.E)
    {t : ℝ≥0} (hlife : ((d.s₀ ω + t : ℝ≥0) : ℝ≥0∞) ≤ d.ζ₁ ω)
    {z : ℂ} (hz : z ∈ lineDomain d t ω) :
    lineDomain d t ω = connectedComponentIn (H \ lineK d t ω) z := by
  have hc₁ : ContinuousOn (d.η₁ ω) (Icc 0 (d.s₀ ω + t)) :=
    (hd.good ω hω.1).1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hlife
  have hc₂ : ContinuousOn (d.η₂ ω) (Icc 0 (d.t₀ ω)) :=
    (hd.continuousOn₂ hω).mono (Icc_subset_Iic_self)
  have hK : IsCompact (lineK d t ω) := isCompact_prefixSet hc₁ hc₂
  obtain ⟨R, -, -, he⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hK.isClosed hK.isBounded
  change H \ fillH (lineK d t ω) = _
  change z ∈ H \ fillH (lineK d t ω) at hz
  rw [he] at hz ⊢
  exact connectedComponentIn_eq hz

/-- The inverse first-contact chart sends the chart-hull complement onto the active physical domain. -/
theorem image_inv_compl_eq_lineDomain (hd : d.IsMeasGood) {ω : Ω} {x₁ x₂ : ℝ}
    {t : ℝ≥0} {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}
    (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) :
    d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) = lineDomain d t ω := by
  refine Subset.antisymm ?_ ?_
  · rintro z ⟨v, hv, rfl⟩
    have hch := hl.isDomChart hd
    rw [hl.fwdHull_eq] at hv
    exact hch.inv_image_subset (hl.isCompact_lineK hd) hl.lineK_subset hl.continuousOn_γ ⟨v, hv, rfl⟩
  · intro z hz
    exact ⟨d.fwd ω z, hl.fwd_mem hd hz,
      (hl.isDomChart hd).inv_fwd ⟨hz.1, fun h => hz.2 (hl.fillH_K_subset h)⟩⟩

/-- At a pathwise reading, any point swallowed off the raw union obstructs the whole-complement equality. -/
theorem not_complement_eq_chartImage_of_swallowed (hd : d.IsMeasGood) {ω : Ω} {x₁ x₂ : ℝ}
    {t : ℝ≥0} {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}
    (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) {z : ℂ}
    (hz : z ∈ fillH (lineK d t ω)) (hzK : z ∉ lineK d t ω) :
    H \ lineK d t ω ≠ d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) := by
  intro he
  have hmem : z ∈ H \ lineK d t ω := ⟨fillH_subset_H _ hz, hzK⟩
  rw [he, image_inv_compl_eq_lineDomain hd hl] at hmem
  exact hmem.2 hz

/-- The whole-complement equality required by the raw-union adapter is equivalent to having no pockets. -/
theorem complement_eq_chartImage_iff_no_pockets (hd : d.IsMeasGood) {ω : Ω} {x₁ x₂ : ℝ}
    {t : ℝ≥0} {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {ζc : ℝ≥0∞} {Q : ℝ≥0}
    (hl : IsFCLine d ω x₁ x₂ t W γ ζc Q) :
    H \ lineK d t ω = d.inv ω '' (H \ fwdHull (fun s : ℝ => W s.toNNReal) Q) ↔
      fillH (lineK d t ω) ⊆ lineK d t ω := by
  rw [image_inv_compl_eq_lineDomain hd hl]
  constructor
  · intro he z hz
    by_contra hzK
    have hmem : z ∈ H \ lineK d t ω := ⟨fillH_subset_H _ hz, hzK⟩
    rw [he] at hmem
    exact hmem.2 hz
  · intro hfill
    apply Subset.antisymm
    · exact fun z hz => ⟨hz.1, fun h => hz.2 (hfill h)⟩
    · exact HalfPlaneSep.H_diff_fillH_subset_H_diff (hl.isCompact_lineK hd).isClosed

end Meas

section Force

variable {nL nR : ℕ}

/-- The flowed left positions in Aux. 79 are the centred geometric force coordinates. -/
theorem flowL_eq_geomLW (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (ω : Ω) (Q : ℝ≥0) :
    flowL (fun s => W s ω) Q (xL ω) = fun i => geomLW W xL i Q ω - W Q ω := rfl

/-- The corresponding identification for right force coordinates. -/
theorem flowR_eq_geomRW (W : ℝ≥0 → Ω → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) (Q : ℝ≥0) :
    flowR (fun s => W s ω) Q (xR ω) = fun j => geomRW W xR j Q ω - W Q ω := rfl

/-- The bounded harmonic mean used by Aux. 79 is exactly the mean used by K2. -/
theorem bheAt_flow_eq_bheProc (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ)
    (ω : Ω) (Q : ℝ≥0) :
    LocalExt.bheAt κ ρL ρR (flowL (fun s => W s ω) Q (xL ω))
      (flowR (fun s => W s ω) Q (xR ω)) =
      bheProc κ ρL ρR W (geomLW W xL) (geomRW W xR) ω Q := rfl

/-- Regularity of all geometric coordinates of the assembled segment driver. -/
theorem isForceReg_fcSegmentProcess [MeasurableSpace Ω]
    {E : Set Ω} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (hseg : ∀ ω ∈ E, Sec7.Lemma71C.IsSegCurve (realPath (Γ ω)))
    (hcont : FCStoppedDriverContinuous E Γ U)
    (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) :
    Aux79.IsForceReg (fcSegmentProcess E Γ U) (geomLW (fcSegmentProcess E Γ U) xL)
      (geomRW (fcSegmentProcess E Γ U) xR) ζ ω :=
  FCDet.isForceReg_thr (fcSegmentDriver_zero hseg) (continuous_fcSegmentDriver hcont) xL xR ζ ω

end Force

section Driver

variable [mΩ : MeasurableSpace Ω]

/-- The lifetime used by the assembly is measurable in the initial word and the adapted segment driver. -/
theorem measurable_fcSegmentThreshold {κ θ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {E : Set Ω} {Γ : Ω → ℝ≥0 → ℂ} {U : Ω → ℝ≥0∞}
    (β : Ω → BoundaryWord) (hβ : Measurable β) (hE : MeasurableSet E)
    (hsegMeas : ∀ q : ℝ≥0, Measurable fun ω =>
      Sec7.Lemma71C.segDriver (realPath (Γ ω)) (fcDriverStopTime U q ω))
    (hcont : FCStoppedDriverContinuous E Γ U) :
    Measurable (fcSegmentThreshold κ θ nL nR ρL ρR E Γ U β) := by
  have hWm := fcSegmentDriverMeasurable hE hsegMeas
  have hnat := fcDriverFiltration_adapted β (fcSegmentProcess E Γ U) hβ hWm
  exact FCDet.measurable_thr (continuous_fcSegmentDriver hcont) hnat.2
    ((FCDet.measurable_typeXL κ θ nL nR ρL ρR).comp hnat.1)
    ((FCDet.measurable_typeXR κ θ nL nR ρL ρR).comp hnat.1)

omit mΩ in
/-- The force positions extracted from any word are ordered, including on the off-type branch. -/
theorem isOrderedForceWord_fcWordPositions (κ θ : ℝ) (nL nR : ℕ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (β : Ω → BoundaryWord) (ω : Ω) :
    IsOrderedForceWord (fcWordLeftPositions κ θ nL nR ρL ρR β ω)
      (fcWordRightPositions κ θ nL nR ρL ρR β ω) :=
  FCDet.isOrderedForceWord_typeXL (β ω)

end Driver

end InteractingSLE.Restart.FCPlumb

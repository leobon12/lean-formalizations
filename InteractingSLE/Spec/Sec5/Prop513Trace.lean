/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.CounterflowHeights
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Sec5.CfAvoidLeftQHit
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Exist.StagedLawData

/-!
# Proposition 5.13: lifetime and boundary avoidance

Packet PROVE-PROP513C. The canonical strip heights give admissible partial sums even
when the actual transported datum agrees with them only off a finite set. Aux. 6
then gives infinite lifetime; the real-contact lemmas exclude all nonzero real
points. No return to the seed is an explicit separate input.

The chart-transport identification is kept explicit: this file does not claim
that the canonical GFF transport has already been constructed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5

open QuantumZipper Sec4

/-- The force word of a transported datum has admissible partial sums if that
datum agrees off finitely many points with the canonical strip-counterflow data. -/
theorem admissible_stripCounterflow_of_eq {κ x₀ : ℝ} (hκ : 0 < κ)
    {bL bU b' : ℝ → ℝ} {JL JU J' : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    (hb' : IsPiecewiseConstantBoundaryData b' J') (E : Finset ℝ)
    (heq : ∀ x ∉ E, b' x =
      stripCounterflowData κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) bL bU x) :
    HasAdmissiblePartialSums (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0)
      (flowLineRhoR (16 / κ) b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0) := by
  have hk : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hbd := stripCounterflowData_bounds_of_isProp411Data hκ hdata
  let F := insert 0 (insert (-1) (insert (Real.exp (Real.pi * x₀)) (E ∪ J')))
  have hF : ∀ x, x ∉ F → x ≠ 0 ∧ x ≠ -1 ∧ x ≠ Real.exp (Real.pi * x₀) ∧
      x ∉ E ∧ x ∉ J' := by
    intro x hx
    simpa only [F, Finset.mem_insert, Finset.mem_union, not_or] using hx
  refine hasAdmissiblePartialSums_of_forall_not_mem hk F ?_ ?_
  · intro x hx hxF _
    obtain ⟨hx0, hx1, _, hxE, hxJ⟩ := hF x hxF
    rw [forceBoundaryData_flowLine hk hb' hx0 hxJ, heq x hxE]
    exact hbd.1 x hx hx1
  · intro x hx hxF _
    obtain ⟨hx0, _, hxq, hxE, hxJ⟩ := hF x hxF
    rw [forceBoundaryData_flowLine hk hb' hx0 hxJ, heq x hxE]
    exact hbd.2 x (lt_of_le_of_ne hx (Ne.symm hx0)) hxq

/-- A canonical transported GFF identifies the datum stored by the flow-line
driver. This is a small adapter to uniqueness of GFF boundary data. -/
theorem stripCounterflowData_eq_of_canonicalGFF {κ x₀ : ℝ} (hκ : 0 < κ)
    {bL bU b' : ℝ → ℝ} {Jc J' : Finset ℝ}
    (hc : IsPiecewiseConstantBoundaryData
      (stripCounterflowData κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) bL bU) Jc)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hG : IsGFFWithBoundaryData P h'
      (stripCounterflowData κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) bL bU) Jc)
    (hfl : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ) :
    ∀ x ∉ J' ∪ Jc, b' x =
      stripCounterflowData κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) bL bU x := by
  exact Exist.StagedLaw.eq_of_isGFFWithBoundaryData hb' hc
    (Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver
      (div_pos (by norm_num) hκ) hb' hfl) hG

/-- An admissible word with a mark at each side of the seed has infinite
lifetime and all its generating traces lie in the open half-plane at positive
times, provided that they do not return to zero. -/
theorem ae_lifetime_eq_top_and_trace_mem_H_of_noReturn {k : ℝ} (hk : 0 < k)
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hword : IsOrderedForceWord xL xR)
    (hadm : HasAdmissiblePartialSums k ρL ρR xL xR)
    (hL : ∃ i, xL i = 0) (hR : ∃ i, xR i = 0)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hzero : ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  obtain ⟨iL, hiL⟩ := hL
  obtain ⟨iR, hiR⟩ := hR
  filter_upwards [aux6Statement hk xL xR ρL ρR P 𝓕 W VL VR B ζ hword hadm hE,
    hE.ae_isIntegratedSLEPath, CfAvoidLeftQ.ae_trace_ne_neg hk hword hadm hE,
    CfAvoidLeftQ.ae_trace_ne_pos hk hword hadm hE, hzero]
    with ω ⟨hζ, _⟩ hp hn hp' hz
  refine ⟨hζ, fun γ hγ t ht => ?_⟩
  have hw : Continuous (fun t => W t ω) := by
    have hc := hp.2.2.2.1
    rw [hζ] at hc
    exact continuousOn_univ.1 (by simpa only [ENNReal.coe_lt_top, ofPred_true] using hc)
  have hbar := Theorem14.GW2aPiece.trace_mem_Hbar hγ hw hp.1 t
  change 0 < (γ t).im
  refine lt_of_le_of_ne hbar ?_
  intro he
  have heq : γ t = ((γ t).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using he.symm
  rcases lt_trichotomy (γ t).re 0 with hneg | h0 | hpos
  · exact hn γ hγ t iL _ hneg (by rw [hiL]; exact hneg.le) heq
  · exact hz γ hγ t ht (by simpa only [h0, Complex.ofReal_zero] using heq)
  · exact hp' γ hγ t iR _ hpos (by rw [hiR]; exact hpos.le) heq

/-- The remaining canonical-field transport input, stated independently of any
driver: every `M_q` transport of the original field has the canonical boundary
data. The piecewise-constant realization and its finite exceptional set are part
of this input. It is not proved here. -/
def StripCounterflowCanonicalFieldStatement (κ x₀ : ℝ) (bL bU : ℝ → ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) : Prop :=
  ∃ Jc : Finset ℝ,
    IsPiecewiseConstantBoundaryData
      (stripCounterflowData κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) bL bU) Jc ∧
    ∀ h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens,
      (∀ ω, IsChartTransport (stripCounterflowChart (Real.exp (Real.pi * x₀))) (-1)
        (-((-(Real.pi / 2) + Real.pi) * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω)) →
      IsGFFWithBoundaryData P h'
        (stripCounterflowData κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) bL bU) Jc

/-- The existential transported driver datum is admissible, using the canonical
field transport input and uniqueness of GFF boundary data. -/
theorem exists_admissible_stripCounterflowDriver {κ x₀ : ℝ} (hκ : 0 < κ)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ)
    (hcanon : StripCounterflowCanonicalFieldStatement κ x₀ bL bU P h) :
    ∃ (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsPiecewiseConstantBoundaryData b' J' ∧ IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ ∧
      HasAdmissiblePartialSums (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0)
        (flowLineRhoR (16 / κ) b' J' 0 0) (flowLineXL b' J' 0) (flowLineXR b' J' 0) := by
  obtain ⟨b', J', h', hb', htrans, hfl⟩ := hcf
  obtain ⟨Jc, hc, hG⟩ := hcanon
  have heq := stripCounterflowData_eq_of_canonicalGFF hκ hc hb' (hG h' htrans) hfl
  exact ⟨b', J', h', hb', hfl,
    admissible_stripCounterflow_of_eq hκ hdata hb' (J' ∪ Jc) heq⟩

/-- Lifetime and strict half-plane membership for the strip counterflow, with
canonical field transport and the strip no-return assertion as explicit inputs. -/
theorem ae_stripCounterflow_lifetime_eq_top_and_trace_mem_H {κ x₀ : ℝ} (hκ : 0 < κ)
    {bL bU : ℝ → ℝ} {JL JU : Finset ℝ}
    (hdata : IsProp411Data κ x₀ bL bU JL JU)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hcf : IsStripCounterflowDriver κ (-(Real.pi / 2)) (Real.exp (Real.pi * x₀)) P h W ζ)
    (hcanon : StripCounterflowCanonicalFieldStatement κ x₀ bL bU P h)
    (hzero : ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ≠ 0) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ γ : ℝ≥0 → ℂ,
      IsGeneratingTrace (fun t => W t ω) ⊤ γ → ∀ t : ℝ≥0, 0 < t → γ t ∈ H := by
  obtain ⟨b', J', h', _, hfl, hadm⟩ :=
    exists_admissible_stripCounterflowDriver hκ hdata hcf hcanon
  obtain ⟨h'', 𝓕, VL, VR, B, _, hC⟩ := hfl
  exact ae_lifetime_eq_top_and_trace_mem_H_of_noReturn (div_pos (by norm_num) hκ)
    (Theorem15.isOrderedForceWord_flowLine b' J' 0) hadm
    ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩
    ⟨⟨0, Nat.zero_lt_succ _⟩, rfl⟩ hC.1 hzero

end InteractingSLE.Sec5

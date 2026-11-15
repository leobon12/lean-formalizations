/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetNHGap
import InteractingSLE.Spec.Supplement.GB7aCmp

/-!
# G8's positivity with the nonhitting premise supplied almost surely

Packet PROVE-G8-DET, R63. GB7a's simultaneous boundary-avoidance theorem gives
absence of all negative-real contacts for the chosen left weight. The dyadic
frame and positivity arguments then use `G8DetFrameNHStatement`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.RLC

open Supp7 Supp9D Restart

/-- A flow line with the two-height boundary datum and a nonhitting left
cumulative weight has no negative-real contact, simultaneously at every time
through its original lifetime. -/
theorem ae_nonneg_real_of_left_height {κ a C θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : κ / 2 - 2 ≤ (a - θ * QuantumZipper.chiC κ) / sleLambda κ - 1)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h (Sec7.prop74Data a C) (↑({0} : Finset ℝ)))
    {α : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hα : IsFlowLine κ (Sec7.prop74Data a C) {0} 0 θ P h α ζ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω →
      (α ω t).im = 0 → 0 ≤ (α ω t).re := by
  have havoid := Supp8.GB7aFlowStatement.ae_forall Supp8.gb7aFlowStatement
    hκ hκ4 (Sec7.isPiecewiseConstant_prop74Data a C) hh hα
  filter_upwards [havoid] with ω hω t ht him
  by_contra hneg
  have hre : (α ω t).re < 0 := lt_of_not_ge hneg
  have heq : α ω t = ((α ω t).re : ℂ) := Complex.ext rfl
    (by simpa only [ofReal_im] using him)
  have hnot : (α ω t).re ∉ ({0} : Finset ℝ) := by
    simpa only [Finset.mem_singleton] using hre.ne
  have hcum : κ / 2 - 2 ≤ Sec4.cumWeightLeft κ
      (Sec7.prop74Data a C (α ω t).re + θ * QuantumZipper.chiC κ) := by
    rw [Sec7.prop74Data, ite_eq_left hre, Sec4.cumWeightLeft]
    convert hL using 1
    ring
  exact (hω t ht (α ω t).re hnot).2 hre hcum heq

/-- G8's selected left weight is in the nonhitting sector. -/
theorem reference_left_weight_nonhitting {κ θ₁ θ₂ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) :
    κ / 2 - 2 ≤
      (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ - θ₁ * QuantumZipper.chiC κ) /
        sleLambda κ - 1 := by
  have hlam := Sec4.sleLambda_pos hκ
  have hchi := Sec4.chiC_pos hκ hκ4
  have hnum : 2 * sleLambda κ ≤
      2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ - θ₁ * QuantumZipper.chiC κ := by
    nlinarith only [hθ, hchi]
  have hdiv := (le_div_iff₀ hlam).2 hnum
  linarith only [hdiv, hκ4]

/-- The pathwise positivity argument with the R63 deterministic successor.
The additional premise is discharged by GB7a, not retained as an event or an
assumption on the source-facing positivity statement. -/
theorem g8PathFrameStatement_of_detNH (hW0b : Supp9.W0bStatement.{u})
    (hD : G8DetFrameNHStatement) : G8PathFrameStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ C hθ hr₁ hr₂ Ω mΩ P hP h hh α β ζα ζβ hα hβ hord ε hε
  have hLnh := reference_left_weight_nonhitting hκ hκ4 hθ
  have hNH := ae_nonneg_real_of_left_height hκ hκ4 hLnh hh hα
  obtain ⟨h', 𝓕, W, VL, VR, B, _, hc, htrace⟩ := Sec7.isFlowLine_prop74Data_iff.1 hα
  have hL : -2 < (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ -
      θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 := by
    linarith only [hLnh, hκ]
  have hR : -2 < (C + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 := hr₁
  have hRc : (C + θ₁ * QuantumZipper.chiC κ) / sleLambda κ - 1 < κ / 2 - 2 := hr₂
  have hηα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζα ω) (α ω) := by
    filter_upwards [htrace] with ω hω
    simpa using hω
  have hland := RLCJ.ae_swallow_landing hκ hκ4 hL hR hRc hc.1 hηα one_pos
  have hgα := LP.ae_good hκ hL hR hc.1
  have hpα := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hα
  have hpβ := ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hβ
  have hw0b := hW0b κ hκ hκ4 _ _ (Sec7.isPiecewiseConstant_prop74Data
    (2 * sleLambda κ + θ₂ * QuantumZipper.chiC κ) C) 0 0 θ₁ θ₂ le_rfl hθ P h hh α β ζα ζβ hα hβ
  refine Filter.Eventually.frequently ?_
  filter_upwards [hland, hgα, hpα, hpβ, hw0b, hord, hηα, hNH] with
    ω ⟨σ, _, hsw, q, hq1, hασ, _⟩ ⟨_, hw, hw0⟩ hpαω hpβω hw0bω ⟨hζα, hζβ, hcop⟩ hηω hNHω
  have hα0 : α ω 0 = 0 := by simpa using Sec7.IsPathGood.zero hpαω
  have hβ0 : β ω 0 = 0 := by simpa using Sec7.IsPathGood.zero hpβω
  rw [hζα] at hηω hNHω
  obtain ⟨_, wβ, hwβ, hwβ0, hgβ⟩ := hpβω
  have hH : ∀ x y : ℝ≥0, x < y → ∃ z ∈ Ioo x y, β ω z ∈ H := by
    intro x y hxy
    obtain ⟨z, hz, hzH⟩ := exists_mem_H_of_isGeneratingTrace hgβ hwβ hwβ0 hxy
      (by rw [hζβ]; exact ENNReal.coe_lt_top)
    exact ⟨z, hz, by simpa using hzH⟩
  have hno : ∀ c : ℝ≥0, ¬ Supp9.HasCommonOpenSubarc (α ω) σ (β ω) c := fun c =>
    hw0bω σ c (by rw [hζα]; exact ENNReal.coe_lt_top) (by rw [hζβ]; exact ENNReal.coe_lt_top)
      (hcop.hasOrderedProperCompletions σ c)
  obtain ⟨r, hr, hβrH, hβrα, hβsmall⟩ :=
    exists_dyad_cut hcop.1 hcop.2.1 hcop.2.2.2.2.1 hcop.2.2.2.2.2.1 hβ0 hno hH
  obtain ⟨t₀, ht₀σ, hfr⟩ := hD (α ω) (β ω) (fun t => W t ω) σ r q ε hε hcop hα0 hβ0
    hw hw0 hηω hsw hq1 hασ hβrH hβrα hβsmall (fun t _ => hNHω t le_top)
  obtain ⟨u, hu, ht₀u, huσ⟩ := exists_dyadSet_btwn ht₀σ
  obtain ⟨h1, h2, h3, h4, hgap⟩ := hfr u ht₀u huσ
  refine ⟨u, hu, r, hr, ⟨by rw [hζα]; exact ENNReal.coe_lt_top,
    by rw [hζβ]; exact ENNReal.coe_lt_top, h1, hβrH,
    fun h => hβrα (image_mono (Icc_subset_Icc_right huσ.le) h), h2, h3, h4,
    hcop.hasOrderedProperCompletions _ _⟩, hgap⟩

/-- G8's original positivity statement from the source-faithful deterministic
successor, with its extra path premise supplied almost surely. -/
theorem g8PositivityStatement_of_detNH (hW0b : Supp9.W0bStatement.{u})
    (hD : G8DetFrameNHStatement) : G8PositivityStatement.{u} :=
  g8PositivityStatement_of_pathFrame (g8PathFrameStatement_of_detNH hW0b hD)

/-- R63's replacement of the G8 input wiring. The old wrapper is kept for
reference in its owner's file; this wrapper takes the successor statement. -/
theorem g8FrameStatement_of_nh_inputs (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetHistStatement.{0})
    (hDet : G8DetFrameNHStatement) : G8FrameStatement.{0} :=
  g8FrameStatement_of_cond_pos h75 href (retainedPairRestartCondStatement_of_param h12p h13 hD)
    (g8PositivityStatement_of_detNH (Supp9.w0bStatement_of_lemma75 h75) hDet)

/-- All G8 wiring from the one remaining relative-chart construction and the
existing conditional-restart inputs, with no old deterministic statement. -/
theorem g8FrameStatement_of_relative_nh_inputs (h75 : Theorem15.Lemma75Statement.{0})
    (href : Sec7.Prop74Order.Prop74RefStatement.{0}) (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) (hD : RetainedCanonCondDetHistStatement.{0})
    (hRel : G8RelativeChartNHStatement) : G8FrameStatement.{0} :=
  g8FrameStatement_of_nh_inputs h75 href h12p h13 hD (g8DetFrameNHStatement_of_relative hRel)

end InteractingSLE.RLC

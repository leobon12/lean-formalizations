/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J5ChartClauseFour
import InteractingSLE.Spec.Sec7.Lemma71QProb
import InteractingSLE.Spec.Sec7.Lemma71QCurve

/-!
# Wang–Wu Proposition 4.20 along the middle line (κ = 4): the side heights of the three-line mean

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.20
(text dump L1701–1745): "The local-set union boundary lemma identifies the mean on the relative interior of every
exposed
arc. […] For three ordered lines, each complementary component is bounded by two adjacent exposed arcs." On the middle
line `γ` (height `0`) the exposed sides carry the values `−λ` (left) and `+λ` (right) of the field `h`, i.e. the mean of
the three complete lines tends to `∓λ − u₀` from the two sides of `γ`, away from the facing wall.

This is the input (CS-prob) of the chamber chart's side limits along the middle line, in the form
`Sec7.Lemma71Q.MiddleSideHeight β α γ W AL vL u₀ 0 λ` (the side of approach read off the centred forward map of a middle
prefix: `g_q(z) → y < 0` from the left, `y > 0` from the right). The specification's version for flow lines
(`Sec7.Lemma71Q.ae_middleSideHeight`, `κ < 4`) compares each pair with the middle **prefixes** and uses the flow-line
single-path heights in forward-map coordinates. At `κ = 4` this file compares each pair with the **complete** middle
line
(Proposition 3.8, `SideHeightBox.ae_tendsto_sub_of_locals`) and uses the plane-form side limits of the complete seed
line
(PROVE-WW-B8, through `seedWall_facts` with `c = 0`) together with the side-of-approach lemmas
`Sec7.Lemma71Q.leftSideOf_mem_of_tendsto_neg` / `rightSideOf_mem_of_tendsto_pos`; the deterministic core is the landed
`Sec7.Lemma71Q.middleSideHeight_of_pairs`, fed with the complete-line mean in place of the prefix means.

## Main results

* `midStops`, `explored_midStops`: the complete middle line as an explored set;
* **`IsSeedThreeSpace.ae_middleSideHeight`**: on a seed three-line space, for every version of the mean of the three
  complete lines, almost surely, for every generating driver `W` of the middle line and every harmonic representative
  `vL`, `MiddleSideHeight β α γ W AL vL u₀ 0 λ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.WangWu.SeedThree

open QuantumZipper (H Hbar chiC)
open Sec7 Sec7.Lemma71I Sec7.Lemma71N Sec7.Lemma71Q Sec7.Lemma71G Sec6 LocalSets

section Stops

variable {Ω : Type*}

/-- The stops of the complete middle line alone (curves ordered `β, α, γ`). -/
abbrev midStops : Fin 3 → ℝ≥0∞ := ![0, 0, ⊤]

theorem explored_midStops (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (hβ0 : (β ω 0).im = 0) (hα0 : (α ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => midStops i) ω = range (γ ω) ∩ H := by
  rw [explored_three_const]
  simp only [midStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Three.setOf_le_top, image_univ]
  rw [union_inter_distrib_right, union_inter_distrib_right, image_setOf_le_zero_inter_H hβ0,
    image_setOf_le_zero_inter_H hα0, empty_union, empty_union]

end Stops

section Middle

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}

/-- **The side heights of the three-line mean along the middle line** (Proposition 4.20 on the middle line, `κ = 4`).
On a seed three-line space, for every version `gL` of the local-set mean of the three complete lines: almost surely,
for every generating driver `W` of the middle line `γ` and every harmonic representative `vL` of `gL`, the full mean
has the side heights `∓λ` along `γ` (`MiddleSideHeight`, lift coefficient `0`): at `γ(s)`, from the left side of `γ`
(the centred map `g_q` tends to a negative real) when `γ(s)` is off the left wall `β`, and from the right side when
`γ(s)` is off the right wall `α`. -/
theorem IsSeedThreeSpace.ae_middleSideHeight {rL rR u₁ u₂ : ℝ}
    (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ) {gL : Ω → DistOn upperHalfPlaneOpens}
    (hgL : IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL) :
    ∀ᵐ ω ∂P, ∀ W : ℝ≥0 → ℝ, IsGeneratingTrace W ⊤ (γ ω) → ∀ vL : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
      MiddleSideHeight (β ω) (α ω) (γ ω) W (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
        0 wwLambda := by
  classical
  obtain ⟨hu₁, hu₂, hL, hR, hh, hu₀, hT, hcoup⟩ := hS
  have hT' := hT
  obtain ⟨-, -, hh0, hβ62, hα62, hγ62, hae⟩ := hT'
  have hl : 0 < wwLambda := wwLambda_pos
  have hL0 : 0 ≤ rL - 0 / wwLambda := by
    have := div_pos hu₂ hl
    rw [zero_div, sub_zero]; linarith
  have hR0 : 0 ≤ rR + 0 / wwLambda := by
    have := div_neg_of_neg_of_pos hu₁ hl
    rw [zero_div, add_zero]; linarith
  obtain ⟨𝓕γ, Wγ, VLγ, VRγ, Bγ, ζγ, hCγ, hsγ⟩ := hcoup 0 γ (by simp)
  obtain ⟨-, -, -, hγside⟩ := seedWall_facts hL0 hR0 hu₀ hh0 hγ62 hCγ hsγ
  obtain ⟨hc3, h03, him3, hηm3, hdet3, hloc3, htr3⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  set hc' := WholeField.centredField h u₀ with hc'def
  have hloc : ∀ s : Fin 3 → ℝ≥0∞, IsLocalSet (explored (Three.threeCurves β α γ) fun i _ => s i) hc' P :=
    fun s => isLocalSet_explored_of_tendsto (τ := fun i _ => s i) (S := fun j _ _ => s j) hh0 hc3 h03 hηm3 hdet3
      hloc3 htr3 (fun _ => measurable_const) (fun j => isGalmarino_const (s j)) (fun _ _ => rfl)
  have hm : ∀ s : Fin 3 → ℝ≥0∞, Measurable[_, hittingSigma] (explored (Three.threeCurves β α γ) fun i _ => s i) :=
    measurable_explored_const hc3 hηm3
  have hdet := comap_explored_const_le_aeSigma hc3 hdet3
  have hunb : ∀ s : Fin 3 → ℝ≥0∞, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (explored (Three.threeCurves β α γ) (fun i _ => s i) ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (explored (Three.threeCurves β α γ)
        (fun i _ => s i) ω)) z) := fun s => Eventually.of_forall fun ω =>
    not_isBounded_lowerUnion_explored (fun i => hc3 i ω) (fun i => by rw [h03 i ω]; simp) (fun i t => him3 i ω t)
  have hβ00 : ∀ ω, (β ω 0).im = 0 := fun ω => by rw [show β ω 0 = 0 from h03 0 ω]; simp
  have hα00 : ∀ ω, (α ω 0).im = 0 := fun ω => by rw [show α ω 0 = 0 from h03 1 ω]; simp
  have hγ00 : ∀ ω, (γ ω 0).im = 0 := fun ω => by rw [show γ ω 0 = 0 from h03 2 ω]; simp
  -- the explored sets
  set EL : Ω → Set ℂ := explored (Three.threeCurves β α γ) fun i _ => Three.leftPairStops i with hELdef
  set ER : Ω → Set ℂ := explored (Three.threeCurves β α γ) fun i _ => Three.rightPairStops i with hERdef
  have hELeq : ∀ ω, EL ω = (range (β ω) ∪ range (γ ω)) ∩ H := fun ω => explored_leftPair β α γ ω (hα00 ω)
  have hEReq : ∀ ω, ER ω = (range (α ω) ∪ range (γ ω)) ∩ H := fun ω => explored_rightPair β α γ ω (hβ00 ω)
  have hEM : ∀ ω, explored (Three.threeCurves β α γ) (fun i _ => midStops i) ω = range (γ ω) ∩ H :=
    fun ω => explored_midStops β α γ ω (hβ00 ω) (hα00 ω)
  -- the means of the pairs and of the complete middle line
  obtain ⟨gEL, hgEL⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hm Three.leftPairStops) (hloc Three.leftPairStops)
  obtain ⟨gER, hgER⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hm Three.rightPairStops) (hloc Three.rightPairStops)
  obtain ⟨gM, hgM⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hm midStops) (hloc midStops)
  have hgM' : IsLocalSetMean (fun ω => arcRange (realPath (γ ω))) hc' P gM := by
    rw [← isLocalSetMean_inter_H_iff]
    have e : explored (Three.threeCurves β α γ) (fun i _ => midStops i) =
        fun ω => arcRange (realPath (γ ω)) ∩ H := funext fun ω => by rw [hEM, arcRange_realPath]
    rw [← e]; exact hgM
  obtain ⟨hγL, hγR⟩ := hγside gM hgM'
  -- Proposition 3.9 on the far components
  set CL : Ω → Set ℂ := fun ω => H \ closureSide (Ioi 0) (EL ω) with hCLdef
  set CR : Ω → Set ℂ := fun ω => H \ closureSide (Iio 0) (ER ω) with hCRdef
  have hCLm : Measurable[MeasurableSpace.comap EL hittingSigma, hittingSigma] fun ω => H \ CL ω := by
    have e : (fun ω => H \ CL ω) = closureSide (Ioi 0) ∘ EL :=
      funext fun ω => sdiff_sdiff_cancel_left (closureSide_subset_H _ _)
    rw [e]
    exact measurable_closureRightSide.comp (comap_measurable EL)
  have hCRm : Measurable[MeasurableSpace.comap ER hittingSigma, hittingSigma] fun ω => H \ CR ω := by
    have e : (fun ω => H \ CR ω) = closureSide (Iio 0) ∘ ER :=
      funext fun ω => sdiff_sdiff_cancel_left (closureSide_subset_H _ _)
    rw [e]
    exact measurable_closureLeftSide.comp (comap_measurable ER)
  have hCL : ∀ᵐ ω ∂P, CL ω ⊆ H \ EL ω ∧ ∀ z ∈ CL ω, connectedComponentIn (H \ EL ω) z ⊆ CL ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, hsβ, -, hsγ, -⟩ := hω
    exact compl_closureSide_components (I := Ioi 0) (A := EL ω) (by rw [hELeq]; exact inter_subset_right)
      (by rw [hELeq]; exact isOpen_H_diff_pair hsβ hsγ)
  have hCR : ∀ᵐ ω ∂P, CR ω ⊆ H \ ER ω ∧ ∀ z ∈ CR ω, connectedComponentIn (H \ ER ω) z ⊆ CR ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, hsα, hsγ, -⟩ := hω
    exact compl_closureSide_components (I := Iio 0) (A := ER ω) (by rw [hEReq]; exact inter_subset_right)
      (by rw [hEReq]; exact isOpen_H_diff_pair hsα hsγ)
  have hCLα : ∀ᵐ ω ∂P, Disjoint (CL ω) (explored (Three.threeCurves β α γ) (fun i _ => Three.rightFlankStops i) ω) := by
    filter_upwards [hae, hT.ae_closedLeftSide] with ω hω hcl
    obtain ⟨-, hsβ, hsα, hsγ, -⟩ := hω
    obtain ⟨hβγ, hγα, -⟩ := hcl
    rw [explored_rightFlank β α γ ω (hβ00 ω) (hγ00 ω), hCLdef]
    dsimp only
    rw [hELeq]
    exact disjoint_sdiff_left.mono_right (range_inter_H_subset_closureRightSide hsβ hsγ
      (disjoint_rightSideOf_of_subset_closedLeftSide hsγ.isProperCurve hsγ.2.2.1 hβγ)
      (disjoint_range_leftSideOf_of_subset_closedLeftSide hsγ hsα hγα))
  have hCRβ : ∀ᵐ ω ∂P, Disjoint (CR ω) (explored (Three.threeCurves β α γ) (fun i _ => Three.leftFlankStops i) ω) := by
    filter_upwards [hae, hT.ae_closedLeftSide] with ω hω hcl
    obtain ⟨-, hsβ, hsα, hsγ, -⟩ := hω
    obtain ⟨hβγ, hγα, -⟩ := hcl
    rw [explored_leftFlank β α γ ω (hα00 ω) (hγ00 ω), hCRdef]
    dsimp only
    rw [hEReq]
    exact disjoint_sdiff_left.mono_right (range_inter_H_subset_closureLeftSide hsα hsγ
      (disjoint_rightSideOf_of_subset_closedLeftSide hsγ.isProperCurve hsγ.2.2.1 hβγ)
      (disjoint_range_leftSideOf_of_subset_closedLeftSide hsγ hsα hγα))
  have hP39L := Three.ae_eq_on_three_full_of_avoid_left hh0 hc3 h03 hηm3 hdet3 hloc3 htr3 hCLm hCL hCLα hgL hgEL
  have hP39L := Three.ae_eq_on_three_full_of_avoid_left hh0 hc3 h03 hηm3 hdet3 hloc3 htr3 hCLm hCL hCLα hgL hgEL
  have hP39R := Three.ae_eq_on_three_full_of_avoid hh0 hc3 h03 hηm3 hdet3 hloc3 htr3 hCRm hCR hCRβ hgL hgER
  -- Proposition 3.8 for each pair against the complete middle line
  have hPL := SideHeightBox.ae_tendsto_sub_of_locals hh0 (hm _) (hm midStops) (hloc _) (hloc _)
    (hdet _) (hdet _) (hunb _) (hunb _) hgEL hgM
  have hPR := SideHeightBox.ae_tendsto_sub_of_locals hh0 (hm _) (hm midStops) (hloc _) (hloc _)
    (hdet _) (hdet _) (hunb _) (hunb _) hgER hgM
  -- the middle line's own driver
  have hmc := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL0 hR0) hCγ.1
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  -- the probability-one event
  filter_upwards [hae, hmc, hsγ, hCγ.1.2.2.2.2, hP39L, hP39R, hPL, hPR, hgEL.2.1, hgER.2.1, hγL, hγR, hCL, hCR,
    hCLα, hCRβ] with ω hω hmω hsω hpγ hP39Lω hP39Rω hcmpL hcmpR hrEL hrER hγLω hγRω hCLω hCRω hCLαω hCRβω
    W hW vL hvL hvLr
  obtain ⟨-, hsβ, hsα, hsγ', -⟩ := hω
  obtain ⟨hζγ, ⟨η, hη, heq⟩, -⟩ := hmω
  obtain ⟨hwγ0, -, -, hcwγ, -⟩ := hpγ
  rw [hζγ] at hcwγ
  have hWγc : Continuous fun t => Wγ t ω :=
    continuousOn_univ.1 (hcwγ.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hγη : γ ω = η := funext fun t => by
    have h1 := congrFun hsω.2 (t : ℝ)
    rw [Lemma71I.realPath_coe, heq] at h1
    simpa only [Real.toNNReal_coe] using h1
  have htrγ' : IsGeneratingTrace (fun t => Wγ t ω) ⊤ (γ ω) := by rw [hγη]; exact hη
  obtain ⟨vEL, hvEL, hvELr⟩ := hrEL
  obtain ⟨vER, hvER, hvERr⟩ := hrER
  obtain ⟨v, hv, hvr, hvlim⟩ := hγLω
  obtain ⟨v', hv', hvr', hvlim'⟩ := hγRω
  have hAL : explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω =
      (range (β ω) ∪ range (α ω) ∪ range (γ ω)) ∩ H := Three.explored_threeTop β α γ ω
  rw [explored_rightFlank β α γ ω (hβ00 ω) (hγ00 ω)] at hCLαω
  rw [explored_leftFlank β α γ ω (hα00 ω) (hγ00 ω)] at hCRβω
  -- the far components avoid the full union and are open
  have hCLAL : CL ω ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω := by
    intro z hz
    refine ⟨hz.1, fun hzA => ?_⟩
    rw [hAL] at hzA
    obtain ⟨(hzβ | hzα) | hzγ, hzH⟩ := hzA
    · exact (hCLω.1 hz).2 (by rw [hELeq]; exact ⟨Or.inl hzβ, hzH⟩)
    · exact Set.disjoint_left.1 hCLαω hz ⟨hzα, hzH⟩
    · exact (hCLω.1 hz).2 (by rw [hELeq]; exact ⟨Or.inr hzγ, hzH⟩)
  have hCRAL : CR ω ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω := by
    intro z hz
    refine ⟨hz.1, fun hzA => ?_⟩
    rw [hAL] at hzA
    obtain ⟨(hzβ | hzα) | hzγ, hzH⟩ := hzA
    · exact Set.disjoint_left.1 hCRβω hz ⟨hzβ, hzH⟩
    · exact (hCRω.1 hz).2 (by rw [hEReq]; exact ⟨Or.inl hzα, hzH⟩)
    · exact (hCRω.1 hz).2 (by rw [hEReq]; exact ⟨Or.inr hzγ, hzH⟩)
  have hELo : IsOpen (H \ EL ω) := by rw [hELeq]; exact isOpen_H_diff_pair hsβ hsγ'
  have hERo : IsOpen (H \ ER ω) := by rw [hEReq]; exact isOpen_H_diff_pair hsα hsγ'
  have hCLo : IsOpen (CL ω) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨connectedComponentIn (H \ EL ω) z, hCLω.2 z hz, hELo.connectedComponentIn,
      mem_connectedComponentIn (hCLω.1 hz)⟩
  have hCRo : IsOpen (CR ω) := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨connectedComponentIn (H \ ER ω) z, hCRω.2 z hz, hERo.connectedComponentIn,
      mem_connectedComponentIn (hCRω.1 hz)⟩
  -- Proposition 3.9, pointwise
  have hEqL : EqOn vL vEL (CL ω) := Sec6.eqOn_of_integral_mul_eq hCLo (fun z hz => hz.1) (hvL.mono hCLAL)
    (hvEL.mono hCLω.1) fun φ hφ => by
      rw [← hvLr φ (hφ.trans hCLAL), ← hvELr φ (hφ.trans hCLω.1)]
      exact hP39Lω φ hφ
  have hEqR : EqOn vL vER (CR ω) := Sec6.eqOn_of_integral_mul_eq hCRo (fun z hz => hz.1) (hvL.mono hCRAL)
    (hvER.mono hCRω.1) fun φ hφ => by
      rw [← hvLr φ (hφ.trans hCRAL), ← hvERr φ (hφ.trans hCRω.1)]
      exact hP39Rω φ hφ
  -- the two representatives of the middle-line mean agree off the middle line
  have hγo : IsOpen (H \ arcRange (realPath (γ ω))) := by
    rw [arcRange_realPath]
    exact QuantumZipper.isOpen_H.sdiff (Lemma71Pin.IsSimpleProper.isClosed_range hsγ')
  have hvv' : EqOn v' v (H \ arcRange (realPath (γ ω))) :=
    Sec6.eqOn_of_integral_mul_eq hγo sdiff_subset hv' hv fun φ hφ => by rw [← hvr' φ hφ, hvr φ hφ]
  have hHγ : H \ explored (Three.threeCurves β α γ) (fun i _ => midStops i) ω =
      H \ arcRange (realPath (γ ω)) := by
    rw [hEM ω, H_diff_inter_H, arcRange_realPath]
  have hsubγ : range (γ ω) ∩ H ⊆ (range (β ω) ∪ range (γ ω)) ∩ H := fun z hz => ⟨Or.inr hz.1, hz.2⟩
  have hsubγ' : range (γ ω) ∩ H ⊆ (range (α ω) ∪ range (γ ω)) ∩ H := fun z hz => ⟨Or.inr hz.1, hz.2⟩
  have hpre : ∀ q : ℚ≥0, wallPrefix (γ ω) q ⊆ range (γ ω) ∩ H := fun q z hz => by
    obtain ⟨⟨t, -, ht⟩, hzH⟩ := hz
    exact ⟨⟨t, ht⟩, hzH⟩
  refine MiddleSideHeight.congr_driver htrγ' hW (middleSideHeight_of_pairs hsβ hsα hsγ' hWγc hwγ0 htrγ' hAL
    (fun _ => v) (by rw [← hELeq ω]; exact hEqL) (by rw [← hEReq ω]; exact hEqR) ?_ ?_ ?_)
  · intro q p hp1 hp2 hp3 hp4
    have := hcmpL vEL v hvEL hvELr (by rw [hHγ]; exact hv) (fun φ hφ => hvr φ (by rw [← hHγ]; exact hφ)) p
    rw [hEM ω, explored_leftPair β α γ ω (hα00 ω), union_eq_left.2 hsubγ] at this
    rw [union_eq_left.2 ((hpre q).trans hsubγ)]
    obtain ⟨r, hr, hsr⟩ := hp4
    refine this hp1 ?_ ⟨1, one_pos, fun z hz => hsubγ hz.1⟩ ⟨r, hr, fun z hz => hpre q (hsr hz)⟩
    rcases hp2 with hp2 | hp2
    · exact Or.inl (hpre q hp2)
    · exact Or.inr hp2
  · intro q p hp1 hp2 hp3 hp4
    have := hcmpR vER v hvER hvERr (by rw [hHγ]; exact hv) (fun φ hφ => hvr φ (by rw [← hHγ]; exact hφ)) p
    rw [hEM ω, explored_rightPair β α γ ω (hβ00 ω), union_eq_left.2 hsubγ'] at this
    rw [union_eq_left.2 ((hpre q).trans hsubγ')]
    obtain ⟨r, hr, hsr⟩ := hp4
    refine this hp1 ?_ ⟨1, one_pos, fun z hz => hsubγ' hz.1⟩ ⟨r, hr, fun z hz => hpre q (hsr hz)⟩
    rcases hp2 with hp2 | hp2
    · exact Or.inl (hpre q hp2)
    · exact Or.inr hp2
  · intro q t₀ ht₀ hH F hFne hFle y hy
    have ht0 : 0 < t₀ := by
      rcases eq_or_ne t₀ 0 with h0 | h0
      · rw [h0, hsγ'.2.2.1] at hH
        exact absurd hH (by simp [H])
      · exact pos_iff_ne_zero.2 h0
    have ht0' : (0 : ℝ) < (t₀ : ℝ) := ht0
    obtain ⟨ρ, hρ, hρt⟩ := Lemma71N.exists_ball_tail hsγ' ht₀
    have hF1 : F ≤ 𝓝 (γ ω t₀) := hFle.trans nhdsWithin_le_nhds
    have hFs : H \ fillH (γ ω '' Icc 0 (q : ℝ≥0)) ∈ F := hFle self_mem_nhdsWithin
    have hFb : ball (γ ω t₀) ρ ∈ F := hF1 (ball_mem_nhds _ hρ)
    have hFγ : F ≤ 𝓝[H \ range (γ ω)] (γ ω t₀) := by
      refine le_inf hF1 (le_principal_iff.2 (Filter.mem_of_superset (Filter.inter_mem hFs hFb) ?_))
      rintro z ⟨⟨hzH, hzf⟩, hzb⟩
      refine ⟨hzH, ?_⟩
      rintro ⟨t, rfl⟩
      rcases le_or_gt t (q : ℝ≥0) with htq | htq
      · exact hzf ⟨hzH, Or.inl (subset_closure ⟨t, ⟨zero_le (a := t), htq⟩, rfl⟩)⟩
      · exact hρt t htq.le hzb
    have hFH : F ≤ 𝓝[H] (γ ω t₀) :=
      le_inf hF1 (le_principal_iff.2 (Filter.mem_of_superset hFs fun z hz => hz.1))
    have hu₀t : Tendsto u₀ F (𝓝 (u₀ (γ ω t₀))) := (hu₀c _ hH).tendsto.mono_left hFH
    have hvv'F : ∀ᶠ z in F, v' z = v z := Filter.mem_of_superset (hFγ self_mem_nhdsWithin) fun z hz =>
      hvv' (by rw [arcRange_realPath]; exact hz)
    constructor
    · intro hy0
      have hRs := rightSideOf_mem_of_tendsto_pos hsγ' hWγc hwγ0 htrγ' ht0 ht₀ hFγ hy0 hy
      have hFR : F ≤ 𝓝[rightSideOf (range (γ ω))] (γ ω t₀) := le_inf hF1 (le_principal_iff.2 hRs)
      have hlim := hvlim' (t₀ : ℝ) ht0'
      rw [Lemma71I.realPath_coe, arcRange_realPath] at hlim
      have hvF : Tendsto v F (𝓝 (wwLambda - (u₀ (γ ω t₀) + 0))) := (hlim.mono_left hFR).congr' hvv'F
      have hsum := hvF.add hu₀t
      have e : wwLambda - (u₀ (γ ω t₀) + 0) + u₀ (γ ω t₀) = wwLambda := by ring
      rw [e] at hsum
      refine hsum.congr fun z => ?_
      simp only [zero_mul, add_zero]
    · intro hy0
      have hLs := leftSideOf_mem_of_tendsto_neg hsγ' hWγc hwγ0 htrγ' ht0 ht₀ hFγ hy0 hy
      have hFL : F ≤ 𝓝[leftSideOf (range (γ ω))] (γ ω t₀) := le_inf hF1 (le_principal_iff.2 hLs)
      have hlim := hvlim (t₀ : ℝ) ht0'
      rw [Lemma71I.realPath_coe, arcRange_realPath] at hlim
      have hvF : Tendsto v F (𝓝 (-wwLambda - (u₀ (γ ω t₀) + 0))) := hlim.mono_left hFL
      have hsum := hvF.add hu₀t
      have e : -wwLambda - (u₀ (γ ω t₀) + 0) + u₀ (γ ω t₀) = -wwLambda := by ring
      rw [e] at hsum
      refine hsum.congr fun z => ?_
      simp only [zero_mul, add_zero]

end Middle

end InteractingSLE.WangWu.SeedThree

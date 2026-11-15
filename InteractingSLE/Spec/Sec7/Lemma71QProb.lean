/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71QSide

/-!
# Lemma 7.1's side limits along the middle curve: the probabilistic half (CS-prob)

Packet PROVE-LEMMA71Q (specification Remark 6.7, `source/spec/p145-192.md` L566–L590). On a three-curve space
(`Lemma72B.IsThreeCurveSpace`: the walls `β = η_{θ₂}`, `α = η_{θ₁}` and the middle curve `γ = η_0`), almost surely, for
every harmonic representative `vL` of the mean of the complete three curves and every driver of `γ`, the full mean has
the single-curve side heights `∓λ` of the middle curve at every point `γ(s)` approached from its left (right) side, as
long as `γ(s)` is off the left (right) wall (`MiddleSideHeight`):

* `explored_three_const` and its specializations: the explored sets of the three curves at constant stops (the left
  pair `β ∪ γ`, the right pair `α ∪ γ`, each wall alone, the middle prefixes `γ([0, q])`);
* `ae_eqOn_leftPair`, `ae_eqOn_rightPair` (**Proposition 3.9**, Remark 6.7: "Contacts with the other outer curve cause
  no extra exception, since that curve avoids the relevant component and Proposition 3.9 removes it"): on the union of
  the components of `ℍ ∖ (β ∪ γ)` not facing the positive half-line — measurable from the pair's explored set
  (`Lemma71Q.measurable_closureRightSide`) and avoided by `α` — the full mean is the left pair mean; likewise on the
  right;
* **`ae_middleSideHeight`**: Proposition 3.8 for each pair against `γ([0, q])` at every rational `q`
  (`SideHeightBox.ae_tendsto_sub_of_locals`), the single-curve heights of the angle-`0` curve
  (`Lemma613.sideHeight_of_map`, with the determination map of the §4.2 reference), and the pathwise assembly
  `middleSideHeight_of_pairs`. The driver is any generating driver of `γ` (drivers are unique).

Conditional helper (on the §4.2 reference `Lemma71H.Cond44ReferenceStatement`, an input of the three-curve space
itself; ruling R43/R48: no Theorem 1.2/1.3); it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71Q

open QuantumZipper (H Hbar chiC)
open LocalSets Sec6 Lemma71I Lemma71N

/-! ### Explored sets at constant stops -/

section Stops

variable {Ω : Type*}

/-- The stops of the middle prefix alone (curves ordered `β, α, γ`). -/
abbrev stopsγ (q : ℚ≥0) : Fin 3 → ℝ≥0∞ := ![0, 0, ((q : ℝ≥0) : ℝ≥0∞)]

theorem explored_three_const (β α γ : Ω → ℝ≥0 → ℂ) (s : Fin 3 → ℝ≥0∞) (ω : Ω) :
    explored (Three.threeCurves β α γ) (fun i _ => s i) ω =
      (β ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s 0} ∪ α ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s 1} ∪
        γ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ s 2}) ∩ H := by
  unfold explored
  rw [Three.iUnion_fin_three]
  simp only [Three.threeCurves, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem image_setOf_le_zero_inter_H {η : ℝ≥0 → ℂ} (h0 : (η 0).im = 0) :
    η '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} ∩ H = ∅ := by
  rw [setOf_le_zero, image_singleton]
  ext z
  simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
  rintro rfl hz
  have : (0 : ℝ) < (η 0).im := hz
  rw [h0] at this
  exact lt_irrefl 0 this

theorem explored_leftPair (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (hα0 : (α ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => Three.leftPairStops i) ω = (range (β ω) ∪ range (γ ω)) ∩ H := by
  rw [explored_three_const]
  simp only [Three.leftPairStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Three.setOf_le_top, image_univ]
  rw [union_inter_distrib_right, union_inter_distrib_right, image_setOf_le_zero_inter_H hα0, union_empty,
    ← union_inter_distrib_right]

theorem explored_rightPair (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (hβ0 : (β ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => Three.rightPairStops i) ω =
      (range (α ω) ∪ range (γ ω)) ∩ H := by
  rw [explored_three_const]
  simp only [Three.rightPairStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Three.setOf_le_top, image_univ]
  rw [union_inter_distrib_right, union_inter_distrib_right, image_setOf_le_zero_inter_H hβ0, empty_union,
    ← union_inter_distrib_right]

theorem explored_rightFlank (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (hβ0 : (β ω 0).im = 0) (hγ0 : (γ ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => Three.rightFlankStops i) ω = range (α ω) ∩ H := by
  rw [explored_three_const]
  simp only [Three.rightFlankStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Three.setOf_le_top, image_univ]
  rw [union_inter_distrib_right, union_inter_distrib_right, image_setOf_le_zero_inter_H hβ0,
    image_setOf_le_zero_inter_H hγ0, empty_union, union_empty]

theorem explored_leftFlank (β α γ : Ω → ℝ≥0 → ℂ) (ω : Ω) (hα0 : (α ω 0).im = 0) (hγ0 : (γ ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => Three.leftFlankStops i) ω = range (β ω) ∩ H := by
  rw [explored_three_const]
  simp only [Three.leftFlankStops, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Three.setOf_le_top, image_univ]
  rw [union_inter_distrib_right, union_inter_distrib_right, image_setOf_le_zero_inter_H hα0,
    image_setOf_le_zero_inter_H hγ0, union_empty, union_empty]

theorem explored_stopsγ (β α γ : Ω → ℝ≥0 → ℂ) (q : ℚ≥0) (ω : Ω) (hβ0 : (β ω 0).im = 0)
    (hα0 : (α ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => stopsγ q i) ω = wallPrefix (γ ω) q := by
  rw [explored_three_const]
  simp only [stopsγ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [union_inter_distrib_right, union_inter_distrib_right, image_setOf_le_zero_inter_H hβ0,
    image_setOf_le_zero_inter_H hα0, empty_union, empty_union, wallPrefix]

end Stops

/-! ### Proposition 3.9: the full mean is a pair mean on the far components -/

section Prob

variable {κ θ₁ θ₂ a b : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}

/-- **The single-curve side heights along the middle curve, almost surely** (Remark 6.7, CS-prob of Lemma 7.1's side
limits along the middle curve). On a three-curve space, for every version `gL` of the local-set mean of the complete
three curves: almost surely, for every generating driver `W` of the middle curve `γ` and every harmonic representative
`vL` of `gL`, the full mean has the side heights `∓λ` along `γ` (`MiddleSideHeight`, `k = χ`, `lam = λ`): at `γ(s)`,
from the left side of `γ` (the centred map `g_q` tends to a negative real) when `γ(s)` is off `β`, and from the right
side when `γ(s)` is off `α`. Proposition 3.9 identifies the full mean with the left (right) pair mean on the far
components; Proposition 3.8 compares each pair with the prefix `γ([0, q])` at every rational `q`; the single-curve
heights are `Lemma613.sideHeight_of_map` for the angle-`0` flow line. Conditional helper (on the §4.2 reference). -/
theorem ae_middleSideHeight (href : Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    {gL : Ω → DistOn upperHalfPlaneOpens}
    (hgL : IsLocalSetMean (explored (Three.threeCurves β α γ) fun _ _ => ⊤) (WholeField.centredField h u₀) P gL) :
    ∀ᵐ ω ∂P, ∀ W : ℝ≥0 → ℝ, IsGeneratingTrace W ⊤ (γ ω) → ∀ vL : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vL (H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω → gL ω ψ = ∫ x, vL x * ψ x) →
      MiddleSideHeight (β ω) (α ω) (γ ω) W (explored (Three.threeCurves β α γ) (fun _ _ => ⊤) ω) vL u₀
        (chiC κ) (sleLambda κ) := by
  classical
  set χ := chiC κ with hχdef
  have hχ : 0 < χ := Sec4.chiC_pos hκ hκ4
  have hS' := hS
  obtain ⟨hh, hu₀, hh0, -, -, hγfl, hβ62, hα62, hγ62, hae⟩ := hS'
  have hbpc := isPiecewiseConstant_prop74Data a b
  have hθχ₂ : 0 < θ₂ * χ := mul_pos hθ₂ hχ
  have hθχ₁ : θ₁ * χ < 0 := mul_neg_of_neg_of_pos hθ₁ hχ
  have ha0 : sleLambda κ - π * χ + 0 * χ ≤ a := by linarith
  have hb0 : sleLambda κ - 0 * χ ≤ b := by linarith
  have hΦγ := Lemma613.exists_map_of_cond44 href hκ hκ4 ha0 hb0 hh hγfl
  obtain ⟨_, _, Wγ, _, _, _, -, hcγ, htrγ⟩ := id hγfl
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
  have hEγ : ∀ q ω, explored (Three.threeCurves β α γ) (fun i _ => stopsγ q i) ω = wallPrefix (γ ω) q :=
    fun q ω => explored_stopsγ β α γ q ω (hβ00 ω) (hα00 ω)
  -- the means of the pairs and of the middle prefixes
  obtain ⟨gEL, hgEL⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hm Three.leftPairStops) (hloc Three.leftPairStops)
  obtain ⟨gER, hgER⟩ := IsLocalSet.exists_isLocalSetMean hh0 (hm Three.rightPairStops) (hloc Three.rightPairStops)
  choose gq hgq using fun q : ℚ≥0 => IsLocalSet.exists_isLocalSetMean hh0 (hm (stopsγ q)) (hloc (stopsγ q))
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
    obtain ⟨-, -, -, -, -, -, -, hsβ, -, hsγ, -⟩ := hω
    exact compl_closureSide_components (I := Ioi 0) (A := EL ω) (by rw [hELeq]; exact inter_subset_right)
      (by rw [hELeq]; exact isOpen_H_diff_pair hsβ hsγ)
  have hCR : ∀ᵐ ω ∂P, CR ω ⊆ H \ ER ω ∧ ∀ z ∈ CR ω, connectedComponentIn (H \ ER ω) z ⊆ CR ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, -, -, -, -, -, -, hsα, hsγ, -⟩ := hω
    exact compl_closureSide_components (I := Iio 0) (A := ER ω) (by rw [hEReq]; exact inter_subset_right)
      (by rw [hEReq]; exact isOpen_H_diff_pair hsα hsγ)
  have hCLα : ∀ᵐ ω ∂P, Disjoint (CL ω) (explored (Three.threeCurves β α γ) (fun i _ => Three.rightFlankStops i) ω) := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, -, -, hβγ, hγα, -, hsβ, hsα, hsγ, -⟩ := hω
    rw [explored_rightFlank β α γ ω (hβ00 ω) (hγ00 ω), hCLdef]
    dsimp only
    rw [hELeq]
    exact disjoint_sdiff_left.mono_right (range_inter_H_subset_closureRightSide hsβ hsγ
      (disjoint_rightSideOf_of_subset_closedLeftSide hsγ.isProperCurve hsγ.2.2.1 hβγ)
      (disjoint_range_leftSideOf_of_subset_closedLeftSide hsγ hsα hγα))
  have hCRβ : ∀ᵐ ω ∂P, Disjoint (CR ω) (explored (Three.threeCurves β α γ) (fun i _ => Three.leftFlankStops i) ω) := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, -, -, -, hβγ, hγα, -, hsβ, hsα, hsγ, -⟩ := hω
    rw [explored_leftFlank β α γ ω (hα00 ω) (hγ00 ω), hCRdef]
    dsimp only
    rw [hEReq]
    exact disjoint_sdiff_left.mono_right (range_inter_H_subset_closureLeftSide hsα hsγ
      (disjoint_rightSideOf_of_subset_closedLeftSide hsγ.isProperCurve hsγ.2.2.1 hβγ)
      (disjoint_range_leftSideOf_of_subset_closedLeftSide hsγ hsα hγα))
  have hP39L := Three.ae_eq_on_three_full_of_avoid_left hh0 hc3 h03 hηm3 hdet3 hloc3 htr3 hCLm hCL hCLα hgL hgEL
  have hP39R := Three.ae_eq_on_three_full_of_avoid hh0 hc3 h03 hηm3 hdet3 hloc3 htr3 hCRm hCR hCRβ hgL hgER
  -- Proposition 3.8 for each pair against the middle prefixes
  have hPL := fun q : ℚ≥0 => SideHeightBox.ae_tendsto_sub_of_locals hh0 (hm _) (hm (stopsγ q)) (hloc _) (hloc _)
    (hdet _) (hdet _) (hunb _) (hunb _) hgEL (hgq q)
  have hPR := fun q : ℚ≥0 => SideHeightBox.ae_tendsto_sub_of_locals hh0 (hm _) (hm (stopsγ q)) (hloc _) (hloc _)
    (hdet _) (hdet _) (hunb _) (hunb _) hgER (hgq q)
  -- the single-curve heights of the capped middle curve
  have hγc : ∀ ω, Continuous (γ ω) := fun ω => hc3 2 ω
  have hgq' : ∀ q : ℚ≥0, IsLocalSetMean (fun ω => (fun t => γ ω (min t (q : ℝ≥0))) ''
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0)} ∩ H) hc' P (gq q) := fun q => by
    have e : (fun ω => (fun t => γ ω (min t (q : ℝ≥0))) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0)} ∩ H) =
        explored (Three.threeCurves β α γ) (fun i _ => stopsγ q i) := funext fun ω => by
      rw [hEγ, wallPrefix, Lemma71N.image_capped_eq]
    rw [e]; exact hgq q
  have hcapγ : ∀ q : ℚ≥0, ∀ᵐ ω ∂P, ∀ t, γ ω (min t (q : ℝ≥0)) = γ ω (Restart.capTime (q : ℝ≥0) (ζγ ω) t) :=
    fun q => by
      filter_upwards [hae] with ω hω t
      rw [Restart.capTime, hω.2.2.1]
      simp
  have hSγ := fun q : ℚ≥0 => Lemma613.sideHeight_of_map hκ hκ4 hbpc hh hγfl hΦγ Wγ htrγ hu₀ (q : ℝ≥0) (q : ℝ≥0)
    le_rfl (fun ω t => γ ω (min t (q : ℝ≥0))) (fun ω => (hγc ω).comp (continuous_id.min continuous_const))
    (fun t => hηm3 2 (min t q)) (hcapγ q) (gq q) (hgq' q)
  -- the probability-one event
  filter_upwards [hae, htrγ, hcγ.1.2.2.2.2, hP39L, hP39R, ae_all_iff.2 hPL, ae_all_iff.2 hPR, ae_all_iff.2 hSγ,
    hgEL.2.1, hgER.2.1, ae_all_iff.2 fun q => (hgq q).2.1, hCL, hCR, hCLα, hCRβ] with ω hω htγ hpγ hP39Lω hP39Rω
    hcmpL hcmpR hshγ hrEL hrER hrq hCLω hCRω hCLαω hCRβω W hW vL hvL hvLr
  obtain ⟨-, -, hζγ, -, -, -, -, hsβ, hsα, hsγ, -⟩ := hω
  obtain ⟨hwγ0, -, -, hcwγ, -⟩ := hpγ
  rw [hζγ] at hcwγ htγ
  have hWγc : Continuous fun t => Wγ t ω :=
    continuousOn_univ.1 (hcwγ.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have htrγ' : IsGeneratingTrace (fun t => Wγ t ω) ⊤ (γ ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htγ
  obtain ⟨vEL, hvEL, hvELr⟩ := hrEL
  obtain ⟨vER, hvER, hvERr⟩ := hrER
  choose vq hvq hvqr using hrq
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
  have hELo : IsOpen (H \ EL ω) := by rw [hELeq]; exact isOpen_H_diff_pair hsβ hsγ
  have hERo : IsOpen (H \ ER ω) := by rw [hEReq]; exact isOpen_H_diff_pair hsα hsγ
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
  refine MiddleSideHeight.congr_driver htrγ' hW (middleSideHeight_of_pairs hsβ hsα hsγ hWγc hwγ0 htrγ' hAL vq
    (by rw [← hELeq ω]; exact hEqL) (by rw [← hEReq ω]; exact hEqR) ?_ ?_ ?_)
  · intro q p hp1 hp2 hp3 hp4
    have := hcmpL q vEL (vq q) hvEL hvELr (hvq q) (hvqr q) p
    rw [hEγ q ω, explored_leftPair β α γ ω (hα00 ω)] at this
    exact this hp1 hp2 hp3 hp4
  · intro q p hp1 hp2 hp3 hp4
    have := hcmpR q vER (vq q) hvER hvERr (hvq q) (hvqr q) p
    rw [hEγ q ω, explored_rightPair β α γ ω (hβ00 ω)] at this
    exact this hp1 hp2 hp3 hp4
  · intro q t₀ ht₀ hH F hF hFle y hy
    have hv := hvq q
    have hvr := hvqr q
    rw [hEγ q ω, wallPrefix, ← Lemma71N.image_capped_eq] at hv hvr
    have := hshγ q (by rw [hζγ]; exact ENNReal.coe_lt_top) (vq q) hv hvr t₀ ht₀ hH F hF hFle y
      (by simpa only [Complex.ofReal_zero, sub_zero] using hy)
    simpa only [Complex.ofReal_zero, sub_zero, zero_mul] using this

end Prob

end InteractingSLE.Sec7.Lemma71Q

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux2728Pocket
import InteractingSLE.Spec.Sec7.Aux119Own
import InteractingSLE.Impl.PiecewiseConstant

/-!
# Aux. lemma 119's conditional mean in the change pocket: (PW13.1) and Aux. lemmas 27–28

Packet PROVE-STRIPSYS25. Specification §7.4, the proof of Aux. lemma 119 (`source/spec/p385-432.md` L50–L52,
p. 387): "Now retain the complete marked incoming union `A`. On every compact selected open side, nested local-set
boundary comparison makes the mean `h_A` agree at the boundary with its single-path own mean. […] In the `φ` coordinate
they are (PW13.1). The only exceptions are `x₀`, `y₀` and the finitely many angle-change points on the selected arcs.
Apply the retained local-set subpower estimate of Aux. 27 and the conformal finite-exception uniqueness argument of
Aux. 28. […] The mean is therefore the bounded finite-piece Poisson extension of (PW13.1)".

For the change pocket's flow chart `c` (`Aux119Bdry.IsFlowChart`) with the common lift's integer `n`
(`Lemma71N.IsPocketBranch`), the **transported heights** are `chartData L R hL hR c ξ = hL(s)` for `ξ < 0` landing at
`L s`, `hR(s)` for `ξ > 0` landing at `R s`: the boundary data (PW13.1) of the chart, with the actual height functions
`hL`, `hR` of the wall pieces. The own heights may fail at finitely many exceptional own times `SL`, `SR` (the angle
changes, where the own mean has no boundary limit); their chart images, with `0`, form the finite exceptional set
`exSet`. Then:

* `IsFlowChart.tendsto_chartMean_neg_of_notMem`, `…_pos_of_notMem`: `Aux119Own`'s (PW13.1) on `ℝ₋`, `ℝ₊` with the
  exceptional own times removed;
* `finite_exSet`, `tendsto_chartMean_of_notMem_exSet`: (PW13.1) at every real chart point off `exSet`;
* `isPiecewiseConstant_chartData`, **`exists_isBoundedHarmonicExtension_chartData`**: for height functions locally
  constant off the exceptional times, the transported heights are piecewise constant, so their bounded Poisson
  extension exists;
* **`ae_eqOn_changePocket`**: almost surely, for the local-set mean of a set `A` with `ℍ ∖ A = ℍ ∖ (R ∪ L)`, given the
  nested comparisons and own heights of the two walls off the exceptional times, the mean in the change pocket is the
  bounded Poisson extension `G` of the transported heights, pulled back and corrected by the shifted lift:
  `v + u₀ = G ∘ c.1 − χ (c.2.2 + 2πn)`.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Aux2728Pocket

open QuantumZipper (H Hbar logDerivFwd)
open Lemma71O (land)
open Lemma71N (IsPocketBranch)
open PocketCoord PocketJordan PocketMarks Aux119Bdry LocalSets

/-! ### (PW13.1) off the exceptional own times -/

section Side

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

/-- **(PW13.1) on `ℝ₋` off the exceptional own times**: `Aux119Own.IsFlowChart.tendsto_chartMean_neg` with the own
heights required only at own times outside `SL`, and the conclusion at the chart points landing there. -/
theorem IsFlowChart.tendsto_chartMean_neg_of_notMem (hF : IsFlowChart R L r Ψ c) {n : ℤ}
    (hn : IsPocketBranch L R c n) {WL WR : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L)
    (htrR : IsGeneratingTrace WR ⊤ R) {v u₀ : ℂ → ℝ} {vL : ℝ≥0 → ℂ → ℝ} {χ : ℝ} {hL : ℝ≥0 → ℝ} {SL : Set ℝ≥0}
    (hown : ∀ s : ℝ≥0, L s ∉ range R → s ∉ SL → ∃ q : ℝ≥0, s < q ∧
      Tendsto (fun z => v z - vL q z) (𝓝[changePocket R L r] (L s)) (𝓝 0) ∧
      Tendsto (fun z => vL q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WL t.toNNReal) q z).im)
        (𝓝[changePocket R L r] (L s)) (𝓝 (hL s))) {ξ : ℝ} (hξ : ξ < 0) {s : ℝ≥0} (hs : land c ξ = L s)
    (hsS : s ∉ SL) :
    Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ))
      (𝓝 (hL s)) := by
  have hT := hF.isTwoArcFrame
  obtain ⟨s', hs'R, hs'⟩ := hT.neg ξ hξ
  have hss' : s' = s := hF.config.left.2.1 (hs'.symm.trans hs)
  subst hss'
  have hl : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (L s')) :=
    hs ▸ hT.tendsto_land (mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨q, hsq, hcmp, hown⟩ := hown s' hs'R hsS
  have hbr := (hn WL WR htrL htrR ξ s' q hsq).1 hξ hl
  exact Aux119Own.tendsto_chartMean_of_own hbr (Aux119Own.tendsto_comp_land hF.conf hF.dom hl) hcmp hown

/-- **(PW13.1) on `ℝ₊` off the exceptional own times** (the right wall). -/
theorem IsFlowChart.tendsto_chartMean_pos_of_notMem (hF : IsFlowChart R L r Ψ c) {n : ℤ}
    (hn : IsPocketBranch L R c n) {WL WR : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L)
    (htrR : IsGeneratingTrace WR ⊤ R) {v u₀ : ℂ → ℝ} {vR : ℝ≥0 → ℂ → ℝ} {χ : ℝ} {hR : ℝ≥0 → ℝ} {SR : Set ℝ≥0}
    (hown : ∀ s : ℝ≥0, R s ∉ range L → s ∉ SR → ∃ q : ℝ≥0, s < q ∧
      Tendsto (fun z => v z - vR q z) (𝓝[changePocket R L r] (R s)) (𝓝 0) ∧
      Tendsto (fun z => vR q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WR t.toNNReal) q z).im)
        (𝓝[changePocket R L r] (R s)) (𝓝 (hR s))) {ξ : ℝ} (hξ : 0 < ξ) {s : ℝ≥0} (hs : land c ξ = R s)
    (hsS : s ∉ SR) :
    Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ))
      (𝓝 (hR s)) := by
  have hT := hF.isTwoArcFrame
  obtain ⟨s', hs'L, hs'⟩ := hT.pos ξ hξ
  have hss' : s' = s := hF.config.right.2.1 (hs'.symm.trans hs)
  subst hss'
  have hl : Tendsto c.2.1 (𝓝[H] (ξ : ℂ)) (𝓝 (R s')) :=
    hs ▸ hT.tendsto_land (mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨q, hsq, hcmp, hown⟩ := hown s' hs'L hsS
  have hbr := (hn WL WR htrL htrR ξ s' q hsq).2 hξ hl
  exact Aux119Own.tendsto_chartMean_of_own hbr (Aux119Own.tendsto_comp_land hF.conf hF.dom hl) hcmp hown

end Side

/-! ### The transported heights and the exceptional set -/

section Data

/-- **The transported heights** (the boundary data (PW13.1) of the chart): `hL(s)` at a chart point `ξ < 0` landing
at `L s`, `hR(s)` at `ξ > 0` landing at `R s`, and `0` at `0`. -/
def chartData (L R : ℝ≥0 → ℂ) (hL hR : ℝ≥0 → ℝ) (c : Chart) (ξ : ℝ) : ℝ :=
  if ξ < 0 then hL (Function.invFun L (land c ξ)) else if 0 < ξ then hR (Function.invFun R (land c ξ)) else 0

/-- **The exceptional chart points**: `0` and the chart points landing at the exceptional own times. -/
def exSet (L R : ℝ≥0 → ℂ) (SL SR : Set ℝ≥0) (c : Chart) : Set ℝ :=
  insert 0 ({ξ : ℝ | ξ < 0 ∧ Function.invFun L (land c ξ) ∈ SL} ∪
    {ξ : ℝ | 0 < ξ ∧ Function.invFun R (land c ξ) ∈ SR})

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

/-- At a negative chart point the landing point is `L` at the curve time `invFun L`. -/
theorem IsFlowChart.land_neg_eq (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : ξ < 0) :
    L (Function.invFun L (land c ξ)) = land c ξ ∧ L (Function.invFun L (land c ξ)) ∉ range R := by
  obtain ⟨s, hsR, hs⟩ := hF.isTwoArcFrame.neg ξ hξ
  have he : L (Function.invFun L (land c ξ)) = land c ξ := Function.invFun_eq ⟨s, hs.symm⟩
  exact ⟨he, by rw [he, hs]; exact hsR⟩

/-- At a positive chart point the landing point is `R` at the curve time `invFun R`. -/
theorem IsFlowChart.land_pos_eq (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : 0 < ξ) :
    R (Function.invFun R (land c ξ)) = land c ξ ∧ R (Function.invFun R (land c ξ)) ∉ range L := by
  obtain ⟨s, hsL, hs⟩ := hF.isTwoArcFrame.pos ξ hξ
  have he : R (Function.invFun R (land c ξ)) = land c ξ := Function.invFun_eq ⟨s, hs.symm⟩
  exact ⟨he, by rw [he, hs]; exact hsL⟩

/-- **The exceptional set is finite** when the exceptional own times are (the chart's boundary map is injective). -/
theorem IsFlowChart.finite_exSet (hF : IsFlowChart R L r Ψ c) {SL SR : Set ℝ≥0} (hSL : SL.Finite)
    (hSR : SR.Finite) : (exSet L R SL SR c).Finite := by
  have hinj := hF.injective_land
  refine Set.Finite.insert 0 (Set.Finite.union ?_ ?_)
  · refine ((hSL.image L).preimage hinj.injOn).subset fun ξ hξ => ?_
    exact ⟨_, hξ.2, (IsFlowChart.land_neg_eq hF hξ.1).1⟩
  · refine ((hSR.image R).preimage hinj.injOn).subset fun ξ hξ => ?_
    exact ⟨_, hξ.2, (IsFlowChart.land_pos_eq hF hξ.1).1⟩

/-- **(PW13.1) at every real chart point off the exceptional set.** -/
theorem IsFlowChart.tendsto_chartMean_of_notMem_exSet (hF : IsFlowChart R L r Ψ c) {n : ℤ}
    (hn : IsPocketBranch L R c n) {WL WR : ℝ≥0 → ℝ} (htrL : IsGeneratingTrace WL ⊤ L)
    (htrR : IsGeneratingTrace WR ⊤ R) {v u₀ : ℂ → ℝ} {vL vR : ℝ≥0 → ℂ → ℝ} {χ : ℝ} {hL hR : ℝ≥0 → ℝ}
    {SL SR : Set ℝ≥0}
    (hownL : ∀ s : ℝ≥0, L s ∉ range R → s ∉ SL → ∃ q : ℝ≥0, s < q ∧
      Tendsto (fun z => v z - vL q z) (𝓝[changePocket R L r] (L s)) (𝓝 0) ∧
      Tendsto (fun z => vL q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WL t.toNNReal) q z).im)
        (𝓝[changePocket R L r] (L s)) (𝓝 (hL s)))
    (hownR : ∀ s : ℝ≥0, R s ∉ range L → s ∉ SR → ∃ q : ℝ≥0, s < q ∧
      Tendsto (fun z => v z - vR q z) (𝓝[changePocket R L r] (R s)) (𝓝 0) ∧
      Tendsto (fun z => vR q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WR t.toNNReal) q z).im)
        (𝓝[changePocket R L r] (R s)) (𝓝 (hR s)))
    {ξ : ℝ} (hξ : ξ ∉ exSet L R SL SR c) :
    Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + χ * (c.2.2 (c.2.1 y) + 2 * π * n)) (𝓝[H] (ξ : ℂ))
      (𝓝 (chartData L R hL hR c ξ)) := by
  have hξ0 : ξ ≠ 0 := fun h => hξ (Set.mem_insert_iff.2 (Or.inl h))
  rcases lt_or_gt_of_ne hξ0 with hneg | hpos
  · have hS : Function.invFun L (land c ξ) ∉ SL := fun h => hξ (mem_insert_of_mem _ (Or.inl ⟨hneg, h⟩))
    simp only [chartData, hneg, ↓reduceIte]
    exact IsFlowChart.tendsto_chartMean_neg_of_notMem hF hn htrL htrR hownL hneg
      (IsFlowChart.land_neg_eq hF hneg).1.symm hS
  · have hS : Function.invFun R (land c ξ) ∉ SR := fun h => hξ (mem_insert_of_mem _ (Or.inr ⟨hpos, h⟩))
    have h1 : ¬ ξ < 0 := not_lt.2 hpos.le
    simp only [chartData, h1, hpos, ↓reduceIte]
    exact IsFlowChart.tendsto_chartMean_pos_of_notMem hF hn htrL htrR hownR hpos
      (IsFlowChart.land_pos_eq hF hpos).1.symm hS

end Data

/-! ### The bounded Poisson extension of the transported heights -/

section Extension

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {Ψ : ℂ → ℂ} {c : Chart}

/-- The curve time of the landing point is continuous at every negative chart point. -/
theorem IsFlowChart.continuousAt_invFun_neg (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : ξ < 0) :
    ContinuousAt (fun t : ℝ => Function.invFun L (land c t)) ξ := by
  have hI : Icc (ξ - -ξ / 2) (ξ + -ξ / 2) ∈ 𝓝 ξ := Icc_mem_nhds (by linarith) (by linarith)
  refine (Lemma71O.continuousOn_invFun_comp hF.config.left
    hF.isTwoArcFrame.continuous_land_ofReal.continuousOn (fun w hw => ?_)).continuousAt hI
  have hw0 : w < 0 := by linarith [hw.2]
  exact ⟨_, (IsFlowChart.land_neg_eq hF hw0).1⟩

/-- The curve time of the landing point is continuous at every positive chart point. -/
theorem IsFlowChart.continuousAt_invFun_pos (hF : IsFlowChart R L r Ψ c) {ξ : ℝ} (hξ : 0 < ξ) :
    ContinuousAt (fun t : ℝ => Function.invFun R (land c t)) ξ := by
  have hI : Icc (ξ - ξ / 2) (ξ + ξ / 2) ∈ 𝓝 ξ := Icc_mem_nhds (by linarith) (by linarith)
  refine (Lemma71O.continuousOn_invFun_comp hF.config.right
    hF.isTwoArcFrame.continuous_land_ofReal.continuousOn (fun w hw => ?_)).continuousAt hI
  have hw0 : 0 < w := by linarith [hw.1]
  exact ⟨_, (IsFlowChart.land_pos_eq hF hw0).1⟩

/-- **The transported heights are piecewise constant** off the exceptional set, when the height functions are locally
constant off the exceptional own times. -/
theorem IsFlowChart.isPiecewiseConstant_chartData (hF : IsFlowChart R L r Ψ c) {SL SR : Set ℝ≥0}
    (hSL : SL.Finite) (hSR : SR.Finite) {hL hR : ℝ≥0 → ℝ} (hLc : ∀ s ∉ SL, ∀ᶠ s' in 𝓝 s, hL s' = hL s)
    (hRc : ∀ s ∉ SR, ∀ᶠ s' in 𝓝 s, hR s' = hR s) :
    IsPiecewiseConstantBoundaryData (chartData L R hL hR c) (IsFlowChart.finite_exSet hF hSL hSR).toFinset := by
  intro y hy
  rw [Set.Finite.mem_toFinset] at hy
  have hy0 : y ≠ 0 := fun h => hy (Set.mem_insert_iff.2 (Or.inl h))
  rcases lt_or_gt_of_ne hy0 with hneg | hpos
  · have hS : Function.invFun L (land c y) ∉ SL := fun h => hy (mem_insert_of_mem _ (Or.inl ⟨hneg, h⟩))
    have h1 := (IsFlowChart.continuousAt_invFun_neg hF hneg).eventually (hLc _ hS)
    filter_upwards [h1, eventually_lt_nhds hneg] with z hz hz0
    simp only [chartData, hz0, hneg, ↓reduceIte]
    exact hz
  · have hS : Function.invFun R (land c y) ∉ SR := fun h => hy (mem_insert_of_mem _ (Or.inr ⟨hpos, h⟩))
    have h1 := (IsFlowChart.continuousAt_invFun_pos hF hpos).eventually (hRc _ hS)
    filter_upwards [h1, eventually_gt_nhds hpos] with z hz hz0
    have h1 : ¬ z < 0 := not_lt.2 hz0.le
    have h2 : ¬ y < 0 := not_lt.2 hpos.le
    simp only [chartData, h1, h2, hz0, hpos, ↓reduceIte]
    exact hz

/-- **The bounded Poisson extension of the transported heights exists** (the frozen companion's statement,
`PiecewiseConstant.existsUnique_isBoundedHarmonicExtension`), and it is unique on `ℍ`. -/
theorem IsFlowChart.exists_isBoundedHarmonicExtension_chartData (hF : IsFlowChart R L r Ψ c) {SL SR : Set ℝ≥0}
    (hSL : SL.Finite) (hSR : SR.Finite) {hL hR : ℝ≥0 → ℝ} (hLc : ∀ s ∉ SL, ∀ᶠ s' in 𝓝 s, hL s' = hL s)
    (hRc : ∀ s ∉ SR, ∀ᶠ s' in 𝓝 s, hR s' = hR s) :
    ∃ G : ℂ → ℝ, IsBoundedHarmonicExtension (chartData L R hL hR c) (exSet L R SL SR c) G ∧
      ∀ G' : ℂ → ℝ, IsBoundedHarmonicExtension (chartData L R hL hR c) (exSet L R SL SR c) G' → EqOn G' G H := by
  obtain ⟨G, hG, huniq⟩ :=
    PiecewiseConstant.existsUnique_isBoundedHarmonicExtension
      (IsFlowChart.isPiecewiseConstant_chartData hF hSL hSR hLc hRc)
  rw [Set.Finite.coe_toFinset] at hG huniq
  exact ⟨G, hG, huniq⟩

end Extension

/-! ### The conditional mean in the change pocket -/

section Prob

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens} {A : Ω → Set ℂ} {g : Ω → DistOn upperHalfPlaneOpens}

/-- **The conditional mean in the change pocket is the bounded Poisson extension of (PW13.1)** (proof of Aux.
lemma 119, p. 387). Let `A` be a local set of the zero-boundary GFF `X` on `ℍ` with local-set mean `g` and `u₀` a
bounded harmonic function on `ℍ`. Almost surely, for every harmonic representative `v` of `g`, every pair of walls
`R`, `L` with `ℍ ∖ A = ℍ ∖ (R ∪ L)` (the complete marked incoming union), every flow chart `c` of their change pocket
with a lift `c.2.2 = Im ℓ` and the common lift's integer `n`, generating traces of both walls, finite exceptional own
times `SL`, `SR`, height functions `hL`, `hR` such that off the exceptional times every wall point of the pocket has
an own time `q > s` with the nested comparison and the own height, and every bounded harmonic extension `G` of the
transported heights off the exceptional chart points: `v + u₀ = G ∘ c.1 − χ (c.2.2 + 2πn)` on the change pocket. -/
theorem ae_eqOn_changePocket (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens X P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A X P) (hg : IsLocalSetMean A X P g)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (hu₀b : ∃ M : ℝ, ∀ z ∈ H, |u₀ z| ≤ M) (χ : ℝ) :
    ∀ᵐ ω ∂P, ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (Ψ : ℂ → ℂ) (c : Chart) (ℓ : ℂ → ℂ) (n : ℤ) (WL WR : ℝ≥0 → ℝ)
        (vL vR : ℝ≥0 → ℂ → ℝ) (hL hR : ℝ≥0 → ℝ) (SL SR : Set ℝ≥0) (G : ℂ → ℝ),
      H \ A ω = H \ (range R ∪ range L) → IsFlowChart R L r Ψ c →
      IsDerivLog c.1 ℓ (changePocket R L r) → (∀ z ∈ changePocket R L r, c.2.2 z = (ℓ z).im) →
      IsPocketBranch L R c n → IsGeneratingTrace WL ⊤ L → IsGeneratingTrace WR ⊤ R → SL.Finite → SR.Finite →
      (∀ s : ℝ≥0, L s ∉ range R → s ∉ SL → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z - vL q z) (𝓝[changePocket R L r] (L s)) (𝓝 0) ∧
        Tendsto (fun z => vL q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WL t.toNNReal) q z).im)
          (𝓝[changePocket R L r] (L s)) (𝓝 (hL s))) →
      (∀ s : ℝ≥0, R s ∉ range L → s ∉ SR → ∃ q : ℝ≥0, s < q ∧
        Tendsto (fun z => v z - vR q z) (𝓝[changePocket R L r] (R s)) (𝓝 0) ∧
        Tendsto (fun z => vR q z + u₀ z + χ * (logDerivFwd (fun t : ℝ => WR t.toNNReal) q z).im)
          (𝓝[changePocket R L r] (R s)) (𝓝 (hR s))) →
      IsBoundedHarmonicExtension (chartData L R hL hR c) (exSet L R SL SR c) G →
      ∀ z ∈ changePocket R L r, v z + u₀ z = G (c.1 z) - χ * (c.2.2 z + 2 * π * n) := by
  filter_upwards [ae_eqOn_of_sideLimit hh hA hloc hg hu₀ hu₀b χ] with ω hω v hv hgv R L r Ψ c ℓ n WL WR vL vR
    hL hR SL SR G hAω hF hℓ hlift hn htrL htrR hSL hSR hownL hownR hG
  obtain ⟨z₀, hz₀, hCeq, -⟩ := hF.config.changePocket_eq
  have hdom : (c.dom : Set ℂ) = changePocket R L r := hF.dom
  have hcomp : ∃ z₀ ∈ H \ A ω, (c.dom : Set ℂ) = connectedComponentIn (H \ A ω) z₀ :=
    ⟨z₀, hAω ▸ hz₀, by rw [hdom, hCeq, hAω]⟩
  have key := hω v hv hgv c ℓ n (chartData L R hL hR c) (exSet L R SL SR c) G hF.conf hcomp
    (by rw [hdom]; exact hℓ) (fun z hz => hlift z (by rw [← hdom]; exact hz)) (IsFlowChart.finite_exSet hF hSL hSR) hG
    (fun ξ hξ => IsFlowChart.tendsto_chartMean_of_notMem_exSet hF hn htrL htrR hownL hownR hξ)
  intro z hz
  exact key z (by rw [SetLike.mem_coe.symm, hdom]; exact hz)

end Prob

end InteractingSLE.Sec7.Aux2728Pocket

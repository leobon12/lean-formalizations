/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J5ChartClause
import InteractingSLE.Spec.Sec7.Lemma71NProb
import InteractingSLE.Spec.Sec5.Prop55HalfSide

/-!
# Corollary 4.8 in the chamber: the wall side limits of the two-wall mean in the chamber chart (deterministic part)

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.20
(text dump L1701–1745): "The local-set union boundary lemma identifies the mean on the relative interior of every
exposed arc. […] At points on the other line not belonging to the stopped line, compactness gives positive distance
from the stopped set and the same boundary lemma applies directly. Only the tip prime ends remain; Corollary 4.8
applies again." In the chamber chart these are the side limits of the remaining chamber along the two walls: at a real
point `ξ < 0` of the chart the inverse chart lands on the left wall `β` (off the right wall), at `ξ > 0` on the right
wall `α` (off `β`), and there the two-wall mean plus `u₀` tends to the wall heights `λ − u₂`, `−λ − u₁` (D2).

The specification's Lemma 7.1 proves this through the single-path heights in forward-map coordinates and the
inherited argument branch (`Sec7.Lemma71N.outerSideLimit_of_heights`, needed for `χ ≠ 0`). At `κ = 4` the lift
coefficient is `χ = 0`, and the wall values of the two-wall mean **from the region between the walls** are already
proved (PROVE-WW-B5/B8: `WangWu.ae_tendsto_unionMean_between_inter`). This file supplies the deterministic glue:

* `range_subset_closedLeftSide_of_disjoint_rightSideOf`: Wang–Wu's order of two simple proper arcs (`β` avoids the right
  side of `α`) gives the frozen closed-side order `range β ⊆ closedLeftSide α` (the order clause of the pocket frame);
* `IsThreeLineSpace.ae_closedLeftSide`, **`ae_exists_isPocketFrame_three`**: on every three-line space with the chamber
  construction, almost surely the chamber chart is a pocket frame (`Sec7.Lemma71N.IsPocketFrame`);
* **`outerSideLimit_of_between`**: in a pocket frame, a harmonic function on the chamber which agrees with a function
  having the wall limits from between the walls (`hL − u₀` along `β`, `hR − u₀` along `α`, at the points off the
  other wall) has the outer side limits `Sec7.Lemma71N.OuterSideLimit c' v u₀ 0 hL hR` of every chart `c'` with the
  same inverse map (e.g. a lift shift `shiftLift c n`; lift coefficient `0`), using the landing lemmas
  `IsPocketFrame.land_neg`, `IsPocketFrame.land_pos` and `C ⊆` between;
* `seedWall_facts` (one seed wall): hitting measurability, field determination, locality, and **the single-line side
  limits** `−λ − (u₀ + c)` (left side) and `λ − (u₀ + c)` (right side) of every version of its mean (PROVE-WW-B8's
  `IsFullLevelLineCoupling.ae_hasSideLimits_line` for the coupling of `h + c`, transported to the common centred
  field `h − u₀`);
* **`IsSeedThreeSpace.ae_outerSideLimit`**: on a seed three-line space with the chamber construction, for every version
  of the two-wall mean, almost surely every harmonic representative has the outer side limits of the (lift-shifted)
  chamber chart with the (D2) heights `λ − u₂` (left wall) and `−λ − u₁` (right wall) — the `κ = 4` counterpart of
  `Sec7.Lemma71N.ae_outerSideLimit`, without a branch hypothesis (`χ(4) = 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.WangWu.SeedThree

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Sec7 Sec7.Lemma71I Sec7.Lemma71K Sec7.Lemma71L Sec7.Lemma71N Sec7.Lemma71G Sec6 LocalSets

/-! ### The closed-side order -/

section Order

/-- **Wang–Wu's order gives the frozen closed-side order.** For simple proper curves `β`, `α` from `0`, if `β` avoids
the right side of `α`, then `β` lies in the closed left side of `α`. (The right side of `α` is avoided by `β` iff the
left side of `β` is avoided by `α`, `IsDiscCrosscut.disjoint_crossRange_crossSide_swap`; then
`Sec5.Prop55Half.range_subset_closedLeftSide_of_disjoint`.) -/
theorem range_subset_closedLeftSide_of_disjoint_rightSideOf {β α : ℝ≥0 → ℂ} (hβ : IsSimpleProper β)
    (hα : IsSimpleProper α) (h : Disjoint (arcRange (realPath β)) (rightSideOf (arcRange (realPath α)))) :
    range β ⊆ closedLeftSide α := by
  have hβ' := hβ.isProperArc
  have hα' := hα.isProperArc
  have h2 := WangWu.IsDiscCrosscut.disjoint_crossRange_crossSide_swap hα'.isDiscCrosscut_toDisc
    hβ'.isDiscCrosscut_toDisc ((WangWu.disjoint_rightSideOf_iff hα' hβ').1 h)
  have hd : Disjoint (range α) (leftSideOf (range β)) := by
    rw [Set.disjoint_left]
    intro z hzα hzL
    have hzH : z ∈ H := hzL.1.1
    have hzα' : z ∈ arcRange (realPath α) := by rw [arcRange_realPath]; exact hzα
    have hzL' : z ∈ leftSideOf (arcRange (realPath β)) := by rw [arcRange_realPath]; exact hzL
    exact Set.disjoint_left.1 h2
      ((hα'.cayley_mem_crossRange_iff (le_of_lt (show (0 : ℝ) < z.im from hzH))).2 hzα')
      ((hβ'.mem_leftSideOf_iff hzH).1 hzL')
  exact Sec5.Prop55Half.range_subset_closedLeftSide_of_disjoint hα hβ hd

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **The closed-side order of a three-line space** (the frozen W0 form of the order clause). -/
theorem IsThreeLineSpace.ae_closedLeftSide (hS : IsThreeLineSpace P h u₀ β α γ) :
    ∀ᵐ ω ∂P, range (β ω) ⊆ closedLeftSide (γ ω) ∧ range (γ ω) ⊆ closedLeftSide (α ω) ∧
      range (β ω) ⊆ closedLeftSide (α ω) := by
  obtain ⟨-, -, -, -, -, -, hae⟩ := hS
  filter_upwards [hae] with ω hω
  obtain ⟨-, hβs, hαs, hγs, hord, -, -⟩ := hω
  exact ⟨range_subset_closedLeftSide_of_disjoint_rightSideOf hβs hγs hord.middle_left,
    range_subset_closedLeftSide_of_disjoint_rightSideOf hγs hαs hord.right_middle,
    range_subset_closedLeftSide_of_disjoint_rightSideOf hβs hαs hord.right_left⟩

/-- **The chamber chart is almost surely a pocket frame** (mirrored from `Sec7.Lemma71N.ae_exists_isPocketFrame`, with
the order clause from `IsThreeLineSpace.ae_closedLeftSide`). -/
theorem ae_exists_isPocketFrame_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') :
    ∀ᵐ ω ∂P, ∃ (Ψ : ℂ → ℂ) (a' b' : ℝ), IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hae⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, hconf, hdom, -⟩ := hpc'
  filter_upwards [hae, hS.ae_closedLeftSide, ae_pocketGood_three hS hpc] with ω hω hcl hg
  obtain ⟨-, hsβ, hsα, -⟩ := hω
  obtain ⟨-, -, -, hb, hfr, a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, -⟩ := hg
  exact ⟨Ψ, a', b', hsβ, hsα, hcl.2.2, hb, hM, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hfr⟩

end Order

/-! ### The wall side limits in the chart (deterministic) -/

section Wall

variable {β α : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ}

/-- **The outer side limits of the chamber chart from the wall limits between the walls** (`χ = 0`). In a pocket
frame, let `v` agree on the chamber with a function `w` which tends, from the region between the walls, to `hL − u₀`
at every point `β s` (`s > 0`) of the left wall off the right wall and to `hR − u₀` at every point `α s` of the right
wall off the left wall, and let `u₀` be continuous on `ℍ`. Then `v + u₀` composed with the inverse chart tends to `hL`
at every real `ξ < 0` and to `hR` at every real `ξ > 0`. -/
theorem outerSideLimit_of_between (hF : IsPocketFrame β α C c Ψ a b) {c' : Chart} (hc' : c'.2.1 = c.2.1)
    {v u₀ w : ℂ → ℝ} {hL hR : ℝ} (hu₀ : ContinuousOn u₀ H) (hvw : EqOn v w C)
    (hwL : ∀ s : ℝ≥0, 0 < s → β s ∉ range α →
      Tendsto w (𝓝[leftSideOf (range α) ∩ rightSideOf (range β)] (β s)) (𝓝 (hL - u₀ (β s))))
    (hwR : ∀ s : ℝ≥0, 0 < s → α s ∉ range β →
      Tendsto w (𝓝[leftSideOf (range α) ∩ rightSideOf (range β)] (α s)) (𝓝 (hR - u₀ (α s)))) :
    OuterSideLimit c' v u₀ 0 hL hR := by
  intro ξ hξ
  rw [hc']
  have hmemC : ∀ᶠ y in 𝓝[H] ((ξ : ℝ) : ℂ), c.2.1 y ∈ C := eventually_nhdsWithin_of_forall fun y hy => by
    rw [← hF.hdom]; exact hF.hc.inv_mem_dom hy
  -- the common argument: landing at a point `p ∈ ℍ` from inside the chamber
  have key : ∀ (p : ℂ) (val : ℝ), p ∈ H → Tendsto c.2.1 (𝓝[H] ((ξ : ℝ) : ℂ)) (𝓝 p) →
      Tendsto w (𝓝[leftSideOf (range α) ∩ rightSideOf (range β)] p) (𝓝 (val - u₀ p)) →
      Tendsto (fun y => v (c.2.1 y) + u₀ (c.2.1 y) + 0 * c'.2.2 (c.2.1 y)) (𝓝[H] ((ξ : ℝ) : ℂ)) (𝓝 val) := by
    intro p val hpH hcp hwp
    have hcw : Tendsto c.2.1 (𝓝[H] ((ξ : ℝ) : ℂ)) (𝓝[leftSideOf (range α) ∩ rightSideOf (range β)] p) :=
      tendsto_nhdsWithin_iff.2 ⟨hcp, hmemC.mono fun y hy => hF.subset_sides hy⟩
    have hcH : Tendsto c.2.1 (𝓝[H] ((ξ : ℝ) : ℂ)) (𝓝[H] p) :=
      tendsto_nhdsWithin_iff.2 ⟨hcp, hmemC.mono fun y hy => hF.subset_H hy⟩
    have h1 : Tendsto (fun y => w (c.2.1 y)) (𝓝[H] ((ξ : ℝ) : ℂ)) (𝓝 (val - u₀ p)) := hwp.comp hcw
    have h2 : Tendsto (fun y => u₀ (c.2.1 y)) (𝓝[H] ((ξ : ℝ) : ℂ)) (𝓝 (u₀ p)) :=
      (hu₀ p hpH).tendsto.comp hcH
    have h3 : Tendsto (fun y => w (c.2.1 y) + u₀ (c.2.1 y) + 0 * c'.2.2 (c.2.1 y)) (𝓝[H] ((ξ : ℝ) : ℂ))
        (𝓝 val) := by
      have := h1.add h2
      simp only [zero_mul, add_zero, sub_add_cancel] at this ⊢
      exact this
    refine h3.congr' (hmemC.mono fun y hy => ?_)
    simp only [hvw hy]
  rcases lt_or_gt_of_ne hξ with hneg | hpos
  · obtain ⟨s, hs, hsα, hcs⟩ := hF.land_neg hneg
    simp only [hneg, ↓reduceIte]
    exact key (β s) hL (hF.hβ.2.2.2.1 s hs) hcs (hwL s hs hsα)
  · obtain ⟨s, hs, hsβ, hcs⟩ := hF.land_pos hpos
    simp only [not_lt.2 hpos.le, ↓reduceIte]
    exact key (α s) hR (hF.hα.2.2.2.1 s hs) hcs (hwR s hs hsβ)

end Wall

/-! ### One seed wall: measurability, determination, locality, side limits -/

section SeedWall

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens}

/-- **One seed wall.** Let `η` be a curve with Lemma 6.2's hypotheses for the centred field `h − u₀` (`u₀` the bounded
harmonic extension of the two-seed data of `(ρL; ρR)`), which is almost surely the seed line of an optional hull
coupling of the nonnegative word `(ρL − c/λ; ρR + c/λ)` with the field `h + c`. Then its range is hitting-measurable,
field-determined and local (with `∩ ℍ`), and every version of its local-set mean has almost surely the left-side limits
`−λ − (u₀ + c)` and the right-side limits `λ − (u₀ + c)` (single-line determinism and side values of the seed line,
PROVE-WW-B8). -/
theorem seedWall_facts {rL rR c : ℝ} (hL : 0 ≤ rL - c / wwLambda) (hR : 0 ≤ rR + c / wwLambda)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR)
      LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) u₀)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (WholeField.centredField h u₀) P)
    {η : Ω → ℝ≥0 → ℂ} (hη : IsLemma62Curve η (WholeField.centredField h u₀) P)
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - c / wwLambda)
      (fun _ => rR + c / wwLambda) P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 c (h ω)))
    (hseed : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ realPath (η ω) = seedLine ζ W ω) :
    Measurable[mΩ, hittingSigma] (fun ω => arcRange (realPath (η ω))) ∧
      LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (realPath (η ω))) hittingSigma)
        (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P ∧
      IsLocalSet (fun ω => arcRange (realPath (η ω)) ∩ H) (WholeField.centredField h u₀) P ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens,
        IsLocalSetMean (fun ω => arcRange (realPath (η ω))) (WholeField.centredField h u₀) P g →
        (∀ᵐ ω ∂P, HasLeftSideLimit (g ω) (realPath (η ω)) fun z => -wwLambda - (u₀ z + c)) ∧
          ∀ᵐ ω ∂P, HasRightSideLimit (g ω) (realPath (η ω)) fun z => wwLambda - (u₀ z + c) := by
  obtain ⟨hc, h0, -, hm, hdet, hloc, htr⟩ := hη
  have hrc : ∀ ω, ContinuousOn (realPath (η ω)) (Ici 0) := fun ω =>
    ((hc ω).comp continuous_real_toNNReal).continuousOn
  have hrm : ∀ s, Measurable fun ω => realPath (η ω) s := fun s => hm s.toNNReal
  have hRm : Measurable[mΩ, hittingSigma] (fun ω => arcRange (realPath (η ω))) := measurable_arcRange hrc hrm
  -- the single curve as an explored set
  have hE : ∀ ω, explored (fun _ : Fin 1 => η) (fun _ _ => ⊤) ω = arcRange (realPath (η ω)) ∩ H := fun ω => by
    simp only [explored, Three.setOf_le_top, image_univ, iUnion_const, arcRange_realPath]
  have hEf : explored (fun _ : Fin 1 => η) (fun _ _ => ⊤) = fun ω => arcRange (realPath (η ω)) ∩ H :=
    funext hE
  have hdetE := Sec7.comap_explored_const_le_aeSigma (η := fun _ : Fin 1 => η) (P := P)
    (h := WholeField.centredField h u₀) (fun _ => hc) (fun _ => hdet) (fun _ => ⊤)
  have hdet' : LQGMetric.AEDeterminedSigma
      (MeasurableSpace.comap (fun ω => arcRange (realPath (η ω))) hittingSigma)
      (MeasurableSpace.comap (WholeField.centredField h u₀) inferInstance) P := by
    intro s hs
    rw [← comap_inter_H] at hs
    have hs' : MeasurableSet[MeasurableSpace.comap (explored (fun _ : Fin 1 => η) fun i _ => (fun _ => ⊤) i)
        hittingSigma] s := by
      rw [show (explored (fun _ : Fin 1 => η) fun i _ => (fun _ : Fin 1 => (⊤ : ℝ≥0∞)) i) =
        fun ω => arcRange (realPath (η ω)) ∩ H from hEf]
      exact hs
    exact hdetE s hs'
  have hlocE := isLocalSet_explored_of_tendsto (η := fun _ : Fin 1 => η) (x := fun _ => 0)
    (τ := fun _ _ => ⊤) (S := fun _ _ _ => ⊤) hh0 (fun _ => hc) (fun _ => h0) (fun _ => hm) (fun _ => hdet)
    (fun _ => hloc) (htr.mono fun ω hω _ => hω) (fun _ => measurable_const) (fun _ => isGalmarino_const ⊤)
    (fun _ _ => rfl)
  rw [hEf] at hlocE
  refine ⟨hRm, hdet', hlocE, fun g hg => ?_⟩
  -- the side limits from the coupling of `h + c`
  have hF := isFullLevelLineCoupling_twoSeed hL hR hC
  have hmc := IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1
  have htrW : ∀ᵐ ω ∂P, ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η' := by
    filter_upwards [hmc] with ω hω
    obtain ⟨hζ, ⟨η', hη', -⟩, -⟩ := hω
    exact ⟨η', hζ ▸ hη'⟩
  have hthr : ¬ ForceWord.ThresholdCondition (fun _ : Fin 1 => rL - c / wwLambda)
      (fun _ : Fin 1 => rR + c / wwLambda) 0 LP.twoSeedXL LP.twoSeedXR :=
    Sec2.TwoSeed.not_thresholdCondition_fin_one (fun _ => by linarith) (fun _ => by linarith) 0 _ _
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hmc.mono fun ω hω => hω.1
  have hγ : ∀ᵐ ω ∂P, IsLoewnerTrace (Ito.rpath (W · ω)) (realPath (η ω)) ∧ IsProperArc (realPath (η ω)) := by
    filter_upwards [hmc, hseed] with ω hω hsω
    rw [hsω.2]
    exact ⟨hω.2.2.1, hω.2.2.2.1⟩
  have hpm : ∀ n : ℕ, Measurable[mΩ, hittingSigma] fun ω => arcPrefix (realPath (η ω)) (n + 1) := fun n =>
    measurable_arcPrefix hrc hrm _
  have hu' := Sec5.GlueCond.isBoundedHarmonicExtension_add_const hu₀ c
  have hdata : (fun x => forceBoundaryData 4 (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) LP.twoSeedXL
      LP.twoSeedXR x + c) = forceBoundaryData 4 (fun _ : Fin 1 => rL - c / wwLambda)
        (fun _ : Fin 1 => rR + c / wwLambda) LP.twoSeedXL LP.twoSeedXR :=
    funext fun x => SeedField.forceBoundaryData_twoSeed_four_add rL rR c x
  rw [hdata] at hu'
  have hcent := SeedField.centredField_flowField_eq h hu₀.1 c
  have hdet'' : LQGMetric.AEDeterminedSigma
      (MeasurableSpace.comap (fun ω => arcRange (realPath (η ω))) hittingSigma)
      (MeasurableSpace.comap (WholeField.centredField (fun ω => Exist.flowField 0 c (h ω)) fun z => u₀ z + c)
        inferInstance) P := by
    rw [hcent]; exact hdet'
  have hg' : IsLocalSetMean (fun ω => arcRange (realPath (η ω)))
      (WholeField.centredField (fun ω => Exist.flowField 0 c (h ω)) fun z => u₀ z + c) P g := by
    rw [hcent]; exact hg
  exact hF.ae_hasSideLimits_line htrW hthr hζ hγ hRm hpm hu' hdet'' hg'

end SeedWall

/-! ### The outer side limits of the chamber chart, almost surely -/

section Outer

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart}
  {γ' : Ω → ℝ → ℂ}

/-- **The wall side limits of the chamber chart, almost surely** (Proposition 4.20 on the two walls, with Corollary
4.8's
boundary identification; `κ = 4` counterpart of `Sec7.Lemma71N.ae_outerSideLimit`). On a seed three-line space with
the chamber construction, for every version `gT` of the local-set mean of the two complete walls: almost surely, for
every harmonic representative `vT` of `gT` and every lift shift `n`, the chamber chart has the outer side limits
`vT + u₀ → λ − u₂` at the real points `ξ < 0` (left wall `β`, its right side) and `→ −λ − u₁` at `ξ > 0` (right wall
`α`, its left side). -/
theorem IsSeedThreeSpace.ae_outerSideLimit {rL rR u₁ u₂ : ℝ}
    (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ) (hpc : IsPocketConstruction P β α γ C c γ')
    {gT : Ω → DistOn upperHalfPlaneOpens}
    (hgT : IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
      (WholeField.centredField h u₀) P gT) :
    ∀ᵐ ω ∂P, ∀ vT : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vT (H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω →
          gT ω ψ = ∫ x, vT x * ψ x) →
      ∀ n : ℤ, OuterSideLimit (Sec7.Lemma71E.shiftLift (c ω) n) vT u₀ 0 (wwLambda - u₂) (-wwLambda - u₁) := by
  obtain ⟨hu₁, hu₂, hL, hR, hh, hu₀, hT, hcoup⟩ := hS
  have hT' := hT
  obtain ⟨-, -, hh0, hβ62, hα62, hγ62, hae⟩ := hT'
  have hl : 0 < wwLambda := wwLambda_pos
  have hdiv₁ : u₁ / wwLambda < 0 := div_neg_of_neg_of_pos hu₁ hl
  have hdiv₂ : 0 < u₂ / wwLambda := div_pos hu₂ hl
  have hLα : 0 ≤ rL - u₁ / wwLambda := by linarith
  have hRβ : 0 ≤ rR + u₂ / wwLambda := by linarith
  obtain ⟨𝓕β, Wβ, VLβ, VRβ, Bβ, ζβ, hCβ, hsβ⟩ := hcoup u₂ β (by simp)
  obtain ⟨𝓕α, Wα, VLα, VRα, Bα, ζα, hCα, hsα⟩ := hcoup u₁ α (by simp)
  obtain ⟨hβm, hβdet, hβloc, hβside⟩ := seedWall_facts hL hRβ hu₀ hh0 hβ62 hCβ hsβ
  obtain ⟨hαm, hαdet, hαloc, hαside⟩ := seedWall_facts hLα hR hu₀ hh0 hα62 hCα hsα
  obtain ⟨gβ, hgβ⟩ := IsLocalSet.exists_isLocalSetMean hh0 (measurable_inter_H hβm) hβloc
  obtain ⟨gα, hgα⟩ := IsLocalSet.exists_isLocalSetMean hh0 (measurable_inter_H hαm) hαloc
  rw [isLocalSetMean_inter_H_iff] at hgβ hgα
  have harc : ∀ᵐ ω ∂P, IsProperArc (realPath (α ω)) ∧ IsProperArc (realPath (β ω)) := by
    filter_upwards [hae] with ω hω
    exact ⟨hω.2.2.1.isProperArc, hω.2.1.isProperArc⟩
  obtain ⟨-, hwall⟩ := ae_tendsto_unionMean_between_inter hh0 hαm hβm hαdet hβdet hαloc hβloc harc hgα hgβ
    (hαside gα hgα).1 (hβside gβ hgβ).2
  -- the wall mean is the mean of the two complete walls
  have hAT : ∀ ω, explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω =
      (arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω))) ∩ H := fun ω => by
    rw [Three.explored_threeOuter β α γ ω (by rw [hγ62.2.1 ω]; simp), arcRange_realPath, arcRange_realPath,
      union_comm]
  have hgT' : IsLocalSetMean (fun ω => arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω)))
      (WholeField.centredField h u₀) P gT := by
    rw [← isLocalSetMean_inter_H_iff]
    have e : explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) =
        fun ω => (arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω))) ∩ H := funext hAT
    rw [← e]
    exact hgT
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  filter_upwards [hwall gT hgT', ae_exists_isPocketFrame_three hT hpc, hae] with ω hw hFω hω vT hvT hgvT n
  obtain ⟨w, hwh, hgw, hwα, hwβ⟩ := hw
  obtain ⟨Ψ, a', b', hF⟩ := hFω
  obtain ⟨-, hβs, hαs, -⟩ := hω
  have hpc' := hpc
  obtain ⟨-, -, -, hdom, -⟩ := hpc'
  -- the two representatives agree off the walls
  have hO : IsOpen (H \ (arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω)))) := by
    refine QuantumZipper.isOpen_H.sdiff (IsClosed.union ?_ ?_)
    · rw [arcRange_realPath]; exact Sec7.Lemma71Pin.IsSimpleProper.isClosed_range hαs
    · rw [arcRange_realPath]; exact Sec7.Lemma71Pin.IsSimpleProper.isClosed_range hβs
  have hHAT : H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω =
      H \ (arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω))) := by
    rw [hAT ω, H_diff_inter_H]
  rw [hHAT] at hvT hgvT
  have heq : EqOn vT w (H \ (arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω)))) :=
    Sec6.eqOn_of_integral_mul_eq hO sdiff_subset hvT hwh fun φ hφ => by rw [← hgvT φ hφ, hgw φ hφ]
  have hCsub : C ω ⊆ H \ (arcRange (realPath (α ω)) ∪ arcRange (realPath (β ω))) := by
    intro z hz
    have hz' := hF.subset_sides hz
    refine ⟨hF.subset_H hz, ?_⟩
    rintro (hzα | hzβ)
    · rw [arcRange_realPath] at hzα; exact hz'.1.1.2 hzα
    · rw [arcRange_realPath] at hzβ; exact hz'.2.1.2 hzβ
  refine outerSideLimit_of_between hF (c' := Sec7.Lemma71E.shiftLift (c ω) n) rfl hu₀c (heq.mono hCsub) ?_ ?_
  · intro s hs hsα'
    have hs' : (0 : ℝ) < (s : ℝ) := hs
    have hpt : realPath (β ω) (s : ℝ) = β ω s := realPath_coe _ _
    have := hwβ s hs' (by rw [hpt, arcRange_realPath]; exact hsα')
    rw [hpt, arcRange_realPath, arcRange_realPath] at this
    convert this using 2
    ring
  · intro s hs hsβ'
    have hs' : (0 : ℝ) < (s : ℝ) := hs
    have hpt : realPath (α ω) (s : ℝ) = α ω s := realPath_coe _ _
    have := hwα s hs' (by rw [hpt, arcRange_realPath]; exact hsβ')
    rw [hpt, arcRange_realPath, arcRange_realPath] at this
    convert this using 2
    ring

end Outer

end InteractingSLE.WangWu.SeedThree

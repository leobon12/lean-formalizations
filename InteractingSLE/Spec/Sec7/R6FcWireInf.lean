/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcMixedInf
import InteractingSLE.Spec.Sec7.R6FcWire

/-!
# R.6's face of shape `MixedInf` from the non-corner landing of the shared force point

Packet PROVE-R6-FACE2. The port of `R6FcWire` to the outer pocket opening at the flow seed:
`R6NonCornerMixedInfRemaining` (**named, unproved**; the same non-corner landing statement as
`R6NonCornerMixedRemaining`, with `IsOuterCfgInf`, `nestRelEventInf` and the traversal `travAllInf`),
`pocketSetInf_eq`, **`r6FaceSMixedInfRemaining_of_nonCorner`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Fc

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen
  PocketStopWallsFin PocketStopSide

universe u

/-- **Named, unproved: the shared seed coordinate of the outer chart lands at a non-corner point of `U`'s boundary**
(mixed shapes, outer pocket opening at the flow seed): the binders of `R6Safe.R6FaceSMixedInfRemaining`; almost
surely on the nested event,
the landing of the outer current chart at the shared seed coordinate (right seed if `d < r_L`, left seed otherwise) is
a point of `∂U`, off `closure (∂U ∩ C)`, other than `U`'s outgoing corner. -/
def R6NonCornerMixedInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordanInf (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEventInf R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        IsNonCornerLanding (curChartInf A R L r η ψ n (StripSys.rt q) ω)
          (if k / 2 - 4 < rL then seedRInf R L r η ψ (StripSys.rt q) ω else seedLInf R L r η ψ (StripSys.rt q) ω)
          (cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) (cfPocket (R ω) (L ω) r)
          (cfPt (openPt (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)))

/-- The active complement of a current pocket chart opening at the flow seed is the complement of its domain. -/
theorem pocketSetInf_eq {Ω : Type*} {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ}
    {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {q : ℝ≥0} {ω : Ω} (hω : ω ∈ A) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hγ : IsDrivenCurve (travAllInf R L r η ψ ω))
    (hc : (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).IsConformal) :
    R6Fin.pocketSetInf A R L r η ψ n q ω = H \ ((curChartInf A R L r η ψ n q ω).dom : Set ℂ) := by
  show H \ activeDom A (travAllInf R L r η ψ) (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω)
    (n ω)) q ω = _
  rw [activeDom_eq_relChart_dom (γ := travAllInf R L r η ψ)
    (c := fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)) hω hq hγ hc]

/-- **R.6's face of shape `MixedInf` from the non-corner landing of the shared seed coordinate.** -/
theorem r6FaceSMixedInfRemaining_of_nonCorner {k rL rR c c' : ℝ} (hNC : R6NonCornerMixedInfRemaining.{u} k rL rR c c') :
    R6FaceSMixedInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hNC hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n s q
    hA hA'] with ω hgen hωA hωA' hωN
  have hgen' := hgen hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hcfO := (hA ω hωA).1
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcfO.props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAllInf R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by
    unfold outerFibreEndInf
    rw [hinv]
    exact hrel
  have hT0 : 0 ≤ outerFibreEndInf R L r η ψ (StripSys.rt q) ω :=
    outerFibreEndInf_nonneg (fun ω hω => (hA ω hω).1) hωA
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  -- the base charts are conformal
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hA ω hω).1.conf
  have hcO := (R5Phase.shiftChart_dom_facts (n := n)
    (fun ω hω => isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H)
    (fun ω hω => (hA ω hω).2.2.2.2.1) ω hωA).1
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) :=
    fun ω hω => (hA' ω hω).1.conf
  obtain ⟨hcI, hdomI, hfwdI⟩ := R5Phase.shiftChart_dom_facts (n := n')
    (fun ω hω => isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H)
    (fun ω hω => PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H)
    (fun ω hω => (hA' ω hω).2.2.2.2.1) ω hωA'
  have hγ' : IsDrivenCurve (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) :=
    ((hA' ω hωA').1.isDrivenCurve (hA' ω hωA').2).1
  rcases hmix with ⟨hdL, hdR⟩ | ⟨hdL, hdR⟩
  · -- the shared wall is `L`: the right side
    simp only [hdL, ↓reduceIte] at hgen'
    obtain ⟨εW, hεW, hpkg⟩ := face_packageInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA hωA' hq0' hqlive hsub
      hT0 htip hgen'
    refine ⟨εW, hεW, fun q' hlo hhi hlive hLS hincl => ?_⟩
    have hc0 : 0 ≤ innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
        (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω :=
      (R5Phase.visitCap_spec (W := fun ω t => W' t.toNNReal ω) (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket
        (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω)) hωA' (hA' ω hωA').1
        (hA' ω hωA').2 hcI hdomI hfwdI hT0 htip).1.le
    have hrt' : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ (hc0.trans hlo.le)
    obtain ⟨hOc, hIc, EO, EI, hEO, hEOc, hEI, hEIc, hvL, hvR, hwL, hwR, ε, hε, hloc, ⟨M, hbdd⟩, hdead,
      halive⟩ := hpkg (StripSys.rt q') (by rw [hrt']; exact hlo) (by rw [hrt']; exact hhi) hincl
    obtain ⟨δc, hδc, hδcE⟩ := Metric.continuousWithinAt_iff.1 (hEOc _ (real_mem_Hbar
      (seedRInf R L r η ψ (StripSys.rt q) ω))) (ε / 2) (half_pos hε)
    rw [pocketSetInf_eq hωA hqlive hγ hcO, pocketSet_eq hωA' hlive hγ' hcI]
    have hδ₁ : 0 < min δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω) :=
      lt_min hδc (by linarith)
    have hball : ∀ t : ℝ, |t - seedRInf R L r η ψ (StripSys.rt q) ω| < δc →
        EO t ∈ ball (EO (seedRInf R L r η ψ (StripSys.rt q) ω)) (ε / 2) := fun t ht => by
      refine mem_ball.2 (hδcE (real_mem_Hbar t) ?_)
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact ht
    refine r6FaceR_right hOc hIc hincl hEO hEOc hEI hEIc hvR hwR
      (by simp only [innerLeft, not_lt.2 hdR, ↓reduceIte]) hε hloc hbdd hδ₁
      (fun ξ hξ1 hξ2 x hx => ?_) (fun y hy1 hy2 x hx => ?_)
    · have hm := min_le_right δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω)
      have hm' := min_le_left δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω)
      exact hdead ξ ⟨by linarith, hξ2⟩ (hball ξ (by rw [abs_sub_lt_iff]; constructor <;> linarith)) x hx
    · have hm' := min_le_left δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω)
      have h := halive y (fun hy => by linarith [hy.2])
        (hball y (by rw [abs_sub_lt_iff]; constructor <;> linarith)) x hx
      simp only [mem_Icc, not_and_or, not_le] at h
      exact h
  · -- the shared wall is `R`: the left side
    simp only [not_lt.2 hdL, ↓reduceIte] at hgen'
    obtain ⟨εW, hεW, hpkg⟩ := face_packageInf (n := n) (n' := n') (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA hωA' hq0' hqlive hsub
      hT0 htip hgen'
    refine ⟨εW, hεW, fun q' hlo hhi hlive hLS hincl => ?_⟩
    have hc0 : 0 ≤ innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
        (outerFibreEndInf R L r η ψ (StripSys.rt q) ω) ω :=
      (R5Phase.visitCap_spec (W := fun ω t => W' t.toNNReal ω) (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket
        (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω)) hωA' (hA' ω hωA').1
        (hA' ω hωA').2 hcI hdomI hfwdI hT0 htip).1.le
    have hrt' : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ (hc0.trans hlo.le)
    obtain ⟨hOc, hIc, EO, EI, hEO, hEOc, hEI, hEIc, hvL, hvR, hwL, hwR, ε, hε, hloc, ⟨M, hbdd⟩, hdead,
      halive⟩ := hpkg (StripSys.rt q') (by rw [hrt']; exact hlo) (by rw [hrt']; exact hhi) hincl
    obtain ⟨δc, hδc, hδcE⟩ := Metric.continuousWithinAt_iff.1 (hEOc _ (real_mem_Hbar
      (seedLInf R L r η ψ (StripSys.rt q) ω))) (ε / 2) (half_pos hε)
    rw [pocketSetInf_eq hωA hqlive hγ hcO, pocketSet_eq hωA' hlive hγ' hcI]
    have hδ₁ : 0 < min δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω) :=
      lt_min hδc (by linarith)
    have hball : ∀ t : ℝ, |t - seedLInf R L r η ψ (StripSys.rt q) ω| < δc →
        EO t ∈ ball (EO (seedLInf R L r η ψ (StripSys.rt q) ω)) (ε / 2) := fun t ht => by
      refine mem_ball.2 (hδcE (real_mem_Hbar t) ?_)
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact ht
    refine r6FaceR_left hOc hIc hincl hEO hEOc hEI hEIc hvL hwL
      (by simp only [innerRight, not_lt.2 hdL, ↓reduceIte]) hε hloc hbdd hδ₁
      (fun ξ hξ1 hξ2 x hx => ?_) (fun y hy1 hy2 x hx => ?_)
    · have hm := min_le_right δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω)
      have hm' := min_le_left δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω)
      exact hdead ξ ⟨hξ1, by linarith⟩ (hball ξ (by rw [abs_sub_lt_iff]; constructor <;> linarith)) x hx
    · have hm' := min_le_left δc (seedRInf R L r η ψ (StripSys.rt q) ω - seedLInf R L r η ψ (StripSys.rt q) ω)
      have h := halive y (fun hy => by linarith [hy.1])
        (hball y (by rw [abs_sub_lt_iff]; constructor <;> linarith)) x hx
      simp only [mem_Icc, not_and_or, not_le] at h
      exact h

end InteractingSLE.Sec7.R6Fc

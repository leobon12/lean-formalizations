/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux119Bdry
import InteractingSLE.Spec.Sec7.Aux119LiftMeas
import InteractingSLE.Spec.Sec7.PocketCoordMeas

/-!
# Aux. lemma 119 for the random change pocket: a measurably selected chart and common lift

Packet PROVE-STRIPSYS22. Specification §7.4, Aux. lemma 119 (`source/spec/p385-432.md` L5, L52, pp. 385, 387):

> There is a measurably selected derivative-logarithm lift for a conformal chart `φ : C → ℍ` taking `x₀` to zero and
> `y₀` to infinity […] No independent integer offset is allowed on the two sides. […] Finally, the component, its
> endpoints, the geometric prefixes, and their normalized maps are measurable from the incoming labels. […] These
> choices give a measurable lift.

For random walls `R`, `L` with measurable coordinates and a measurable event `G` on which they form an oriented change
configuration (Aux. lemma 130's event, PROVE-STRIPSYS8/17/18), this file assembles:

* the random change pocket observed through closed balls (`PocketCoord.exists_measurable_changePocketInc`);
* a measurable chart of it normalized at the marked prime ends (`Lemma71K.exists_markedPocketChart`, applied to the
  right wall, of which the change pocket is a marked pocket: `PocketCoord.IsChangeConfigInc.isMarkedPocket`), with a
  logarithm of the chart derivative whose imaginary part is the chart lift;
* on `G`, this chart is a flow chart (`Aux119Bdry.IsFlowChart`, for a positive multiple of a two-point uniformizer:
  the normalization is unique up to positive scaling), hence a two-arc frame;
* a measurable integer `n` making the lift the inherited branch of both walls
  (`Aux119Lift.exists_measurable_isPocketBranch`).

Off `G` the walls are replaced by the imaginary axis (`wallOn`) where a continuous curve from `0` is needed; on `G`
nothing changes.

## Main results

* `PocketJordan.IsBdryUniformizer.const_mul`: positive multiples of a two-point uniformizer;
* **`exists_measurable_flowChart_branch`**: Aux. lemma 119's measurably selected chart and common lift for the random
  change pocket.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal

namespace InteractingSLE.Sec7

namespace PocketJordan.IsBdryUniformizer

variable {D : Set ℂ} {p q : ℂ} {Ψ : ℂ → ℂ}

/-- **Positive multiples of a two-point uniformizer** are two-point uniformizers. -/
theorem const_mul (hU : IsBdryUniformizer D p q Ψ) {a : ℝ} (ha : 0 < a) :
    IsBdryUniformizer D p q (fun w => (a : ℂ) * Ψ w) := by
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.2 ha.ne'
  refine ⟨⟨hU.conf.1.const_mul _, fun w hw => ?_, fun w₁ hw₁ w₂ hw₂ h => ?_, fun y hy => ?_⟩, continuousOn_const.mul
    hU.cont, fun w₁ hw₁ w₂ hw₂ h => hU.inj hw₁ hw₂ (mul_left_cancel₀ ha' h), fun w hw => ?_, by simp [hU.zero], ?_⟩
  · show 0 < ((a : ℂ) * Ψ w).im
    rw [im_ofReal_mul]; exact mul_pos ha (hU.conf.2.mapsTo hw)
  · exact hU.conf.2.injOn hw₁ hw₂ (mul_left_cancel₀ ha' h)
  · have hy' : y / a ∈ H := by
      show 0 < (y / (a : ℂ)).im
      rw [div_ofReal_im]; exact div_pos hy ha
    obtain ⟨w, hw, hwe⟩ := hU.conf.2.surjOn hy'
    refine ⟨w, hw, ?_⟩
    show (a : ℂ) * Ψ w = y
    rw [hwe]; field_simp
  · show 0 ≤ ((a : ℂ) * Ψ w).im
    rw [im_ofReal_mul]; exact mul_nonneg ha.le (hU.mapsTo hw)
  · have h := hU.tendsto.const_mul_atTop ha
    refine h.congr fun w => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]

end PocketJordan.IsBdryUniformizer

namespace Aux119Lift

open WangWu PocketCoord Lemma71I PocketJordan PocketMarks Aux119Bdry
open Lemma71K (wallPt)

variable {Ω : Type*}

/-- A random wall, replaced off `G` by the imaginary axis (a continuous curve from `0`). -/
def wallOn (G : Set Ω) (R : Ω → ℝ≥0 → ℂ) (ω : Ω) : ℝ≥0 → ℂ :=
  open scoped Classical in if ω ∈ G then R ω else fun t => ((t : ℝ) : ℂ) * I

theorem wallOn_of_mem {G : Set Ω} {R : Ω → ℝ≥0 → ℂ} {ω : Ω} (hω : ω ∈ G) : wallOn G R ω = R ω := by
  simp [wallOn, hω]

theorem continuous_wallOn {G : Set Ω} {R : Ω → ℝ≥0 → ℂ} (hR : ∀ ω ∈ G, Continuous (R ω)) (ω : Ω) :
    Continuous (wallOn G R ω) := by
  by_cases hω : ω ∈ G
  · rw [wallOn_of_mem hω]; exact hR ω hω
  · simp only [wallOn, hω, ↓reduceIte]; fun_prop

theorem wallOn_zero {G : Set Ω} {R : Ω → ℝ≥0 → ℂ} (hR : ∀ ω ∈ G, R ω 0 = 0) (ω : Ω) : wallOn G R ω 0 = 0 := by
  by_cases hω : ω ∈ G
  · rw [wallOn_of_mem hω]; exact hR ω hω
  · simp [wallOn, hω]

variable [MeasurableSpace Ω]

theorem measurable_wallOn {G : Set Ω} (hG : MeasurableSet G) {R : Ω → ℝ≥0 → ℂ}
    (hRm : ∀ t, Measurable fun ω => R ω t) (t : ℝ≥0) : Measurable fun ω => wallOn G R ω t := by
  classical
  have : (fun ω => wallOn G R ω t) = fun ω => if ω ∈ G then R ω t else ((t : ℝ) : ℂ) * I := by
    funext ω; by_cases hω : ω ∈ G <;> simp [wallOn, hω]
  rw [this]
  exact Measurable.ite hG (hRm t) measurable_const

/-- **Aux. lemma 119's measurably selected chart and common lift for the random change pocket.** For random walls with
measurable coordinates and a measurable event `G` on which they form an oriented change configuration, there are a
random domain `C` (the change pocket on `G`), a random chart `c` of `C` with measurable domain events, chart values
and lift, a logarithm of the chart derivative with imaginary part the lift, and a measurable integer `n`, such that on
`G` the chart is a flow chart (`x₀ ↦ 0`, `y₀ ↦ ∞`, oriented) and the shifted lift `Im ℓ + 2πn` is the inherited
branch of both walls: it has the boundary value of every own prefix's canonical derivative argument, on `ℝ₋` along
the left wall and on `ℝ₊` along the right wall. -/
theorem exists_measurable_flowChart_branch {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hor : ∀ ω ∈ G, IsFlowChartOriented (R ω) (L ω) r) :
    ∃ (C : Ω → Set ℂ) (c : Ω → Chart) (n : Ω → ℤ),
      (∀ ω ∈ G, C ω = changePocket (R ω) (L ω) r) ∧ (∀ ω, (c ω).IsConformal) ∧
      (∀ ω, ((c ω).dom : Set ℂ) = C ω) ∧ (∀ z, MeasurableSet {ω | z ∈ (c ω).dom}) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) ∧
      (∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z)) ∧
      (∀ ω, ∃ ℓ : ℂ → ℂ, IsDerivLog (c ω).1 ℓ (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (ℓ z).im) ∧
      (∀ ω ∈ G, ∃ Ψ : ℂ → ℂ, IsFlowChart (R ω) (L ω) r Ψ (c ω)) ∧
      Measurable n ∧ ∀ ω ∈ G, Lemma71N.IsPocketBranch (L ω) (R ω) (c ω) (n ω) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨C, Np, hNp, hC, hCm, hNpC, hCG, -⟩ := exists_measurable_changePocketInc hRm hLm hGm hG he
  set R' := wallOn G R with hR'
  set L' := wallOn G L with hL'
  have hR'c : ∀ ω, Continuous (R' ω) := continuous_wallOn fun ω hω => (hG ω hω).right.1
  have hL'c : ∀ ω, Continuous (L' ω) := continuous_wallOn fun ω hω => (hG ω hω).left.1
  have hL'0 : ∀ ω, L' ω 0 = 0 := wallOn_zero fun ω hω => (hG ω hω).left.2.2.1
  obtain ⟨Nx, Ny, c, -, -, -, -, hconf, hdom, -, hdm, hfm, hlm, -, hL, -, huniq, hmark⟩ :=
    Lemma71K.exists_markedPocketChart hC hCm he hNp hNpC hR'c (measurable_wallOn hGm hRm)
  -- on `G` the chart is a flow chart
  have hflow : ∀ ω ∈ G, ∃ Ψ : ℂ → ℂ, IsFlowChart (R ω) (L ω) r Ψ (c ω) := by
    intro ω hω
    have h := hG ω hω
    obtain ⟨Ψ, hU⟩ := h.exists_isBdryUniformizer
    have hCω : C ω = changePocket (R ω) (L ω) r := hCG ω hω
    have hCH : C ω ⊆ H := hCω ▸ h.changePocket_subset_H
    have hψ : IsConformalBijection (Ψ ∘ cayley) (C ω) H := by
      rw [hCω]
      exact isConformalBijection_comp hU.conf (Lemma71F.isConformalBijection_cayley_image h.changePocket_subset_H)
    have hM : Lemma71K.IsMarkedPocket (R' ω) (C ω) (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) := by
      rw [hR', wallOn_of_mem hω, hCω]; exact h.isMarkedPocket
    obtain ⟨hx, hy⟩ := hmark ω _ _ hM
    have hwx : wallPt (R' ω) (rightLo (R ω) (L ω) r) = openPt (R ω) (L ω) r := by
      rw [hR', wallOn_of_mem hω]; rfl
    have hwy : wallPt (R' ω) (rightHi (R ω) (L ω) r) = closePt (R ω) (L ω) r := by
      rw [hR', wallOn_of_mem hω]; rfl
    rw [hwx, hCω] at hx
    rw [hwy, hCω] at hy
    set D := cayley '' changePocket (R ω) (L ω) r with hD
    have hDK : D ⊆ closure D \ {closePt (R ω) (L ω) r} := fun w hw =>
      ⟨subset_closure hw, fun he' => closePt_notMem h (mem_singleton_iff.1 he' ▸ hw)⟩
    have hpK : openPt (R ω) (L ω) r ∈ closure D \ {closePt (R ω) (L ω) r} :=
      ⟨frontier_subset_closure h.openPt_mem_frontier, h.openPt_ne_closePt⟩
    have h0 : Tendsto (fun m => (Ψ ∘ cayley) (e (Nx m ω))) atTop (𝓝 0) := by
      rw [← hU.zero]
      exact ((hU.cont _ hpK).tendsto.comp (tendsto_nhdsWithin_mono_right hDK hx))
    have hinf : Tendsto (fun m => ‖(Ψ ∘ cayley) (e (Ny m ω))‖) atTop atTop :=
      hU.tendsto.comp (tendsto_nhdsWithin_mono_right hDK hy)
    obtain ⟨a, ha, haeq⟩ := huniq ω (Ψ ∘ cayley) hψ h0 hinf
    exact ⟨fun w => (a : ℂ) * Ψ w, ⟨h, hor ω hω, hU.const_mul ha, hconf ω, (hdom ω).trans hCω,
      fun x hx' => haeq (hCω ▸ hx')⟩⟩
  -- the measurable integer
  have hCm' : ∀ z, MeasurableSet {ω | z ∈ C ω} :=
    Lemma71E.measurableSet_mem_of_closedBall (fun ω => (hC ω).1) hCm
  have hG' : ∀ ω ∈ G, (∃ sa ta q₁ q₂ : ℝ≥0, IsTwoArcFrame (L' ω) (R ω) (C ω) (c ω) sa ta q₁ q₂) ∧
      ∃ ℓ : ℂ → ℂ, IsDerivLog (c ω).1 ℓ (C ω) ∧ ∀ z ∈ C ω, (c ω).2.2 z = (ℓ z).im := by
    intro ω hω
    obtain ⟨Ψ, hF⟩ := hflow ω hω
    refine ⟨⟨openL (R ω) (L ω) r, openR (R ω) (L ω) r, cornerL (R ω) (L ω) r, cornerR (R ω) (L ω) r, ?_⟩, hL ω⟩
    rw [hL', wallOn_of_mem hω, hCG ω hω]
    exact hF.isTwoArcFrame
  obtain ⟨n, hnm, hn⟩ := exists_measurable_isPocketBranch hL'c hL'0 (measurable_wallOn hGm hLm) hconf hdom hCm'
    hfm hlm hG'
  refine ⟨C, c, n, hCG, hconf, hdom, hdm, hfm, hlm, hL, hflow, hnm, fun ω hω => ?_⟩
  have := hn ω hω
  rwa [hL', wallOn_of_mem hω] at this

end Aux119Lift

end InteractingSLE.Sec7

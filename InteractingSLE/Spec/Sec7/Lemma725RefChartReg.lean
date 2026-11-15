/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopFieldChart
import InteractingSLE.Spec.Coupling.WholeField2Hull
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# The canonical pocket chart is regular on the whole sample space; the field `h₀ + u`

Packet PROVE-LEMMA725REF4, item 1 (c)–(d). Specification §7.4, Aux. lemma 119 (`source/spec/p385-432.md` L52,
p. 387: "There is a measurably selected derivative-logarithm lift for a conformal chart `φ : C → ℍ`") and Lemma 7.25's
proof (pp. 413–414).

PROVE-LEMMA725REF3's named input `Lemma725RefSafe.PocketChartFieldStatement` asks for a pocket chart `c` that is
conformal at **every** sample, whose domain events, forward values and lift values at fixed points are measurable for
the walls' σ-algebra on the domain events (on all of `Ω`, not only on the pocket event `A`), and whose lift is
continuous and **harmonic** on the chart domain at every sample. Here this is proved for the canonical pocket chart
`PocketStopField.pChart A C ψ` (PROVE-STRIPSYS35) with its branch shifted by a walls-measurable integer `n`
(`shiftChart`), the chart used by the strip system's remaining field-level inputs (`PocketStopWallsField`):

* on `A` the lift is `Im ℓ − 2πn` with `ℓ = pLog` an analytic logarithm of `ψ′` on the pocket (`isDerivLog_pLog`), so
  it is harmonic (`AnalyticAt.harmonicAt_im`);
* off `A` the chart is the identity chart of `ℍ` with the lift `−Im canonLogH id − 2πn`, again the imaginary part of
  an analytic function on `ℍ` minus a constant.

Also: for a harmonic `u`, the field `h = h₀ + smoothDist u` has centred field `h₀` (`centredField_add_smoothDist`), and
the deterministic mean `smoothDist u` is `φ ↦ ∫ u φ` (`smoothDist_eq_integral`).

## Main results

* `differentiableOn_pLog`, **`harmonicOnNhd_lift_shiftChart`**, `continuousOn_lift_shiftChart`;
* `isConformal_shiftChart`, `measurableSet_mem_dom_shiftChart`, `measurable_fwd_shiftChart`,
  **`measurable_lift_shiftChart`** (lift values at fixed points on all of `Ω`);
* `centredField_add_smoothDist`, `smoothDist_eq_integral`, `measurable_add_smoothDist`.

Ruling R48: nothing here uses Theorem 1.2/1.3 or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped Real NNReal

namespace InteractingSLE.Sec7.Lemma725RefChart

open QuantumZipper (H isOpen_H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)
open PocketStopField

/-! ### The lift of the shifted canonical pocket chart -/

section Lift

variable {Ω : Type*} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}

/-- The domain of the shifted chart is the domain of the chart. -/
theorem dom_shiftChart (c : Chart) (n : ℤ) : (shiftChart c n).dom = c.dom := rfl

/-- The shifted chart is conformal when the chart is. -/
theorem isConformal_shiftChart {c : Chart} (hc : c.IsConformal) (n : ℤ) : (shiftChart c n).IsConformal := hc

/-- **The derivative logarithm of the canonical pocket chart is holomorphic on the chart domain at every sample**:
on `A` it is an analytic logarithm of `ψ′` on the pocket (`isDerivLog_pLog`); off `A` it is `−canonLogH id`, an
analytic logarithm of `id′ = 1` on `ℍ` with a sign change. -/
theorem differentiableOn_pLog (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (ω : Ω) :
    DifferentiableOn ℂ (pLog A C ψ ω) (pChart A C ψ ω).dom := by
  have hdom := (pChart_props hCo hCH hψ ω).2.2.2
  by_cases hω : ω ∈ A
  · have e : ((pChart A C ψ ω).dom : Set ℂ) = C ω := by
      rw [hdom]
      ext z
      simp only [mem_ofPred_eq, hω, true_and, not_true_eq_false, false_and, or_false]
    rw [e]
    exact (isDerivLog_pLog hCo hψ hω).1
  · have e : ((pChart A C ψ ω).dom : Set ℂ) = H := by
      rw [hdom]
      ext z
      simp only [mem_ofPred_eq, hω, false_and, not_false_eq_true, true_and, false_or]
    rw [e]
    have hid := (isDerivLog_canonLogH (g := id) differentiableOn_id fun w _ => by
      rw [deriv_id]; exact one_ne_zero).1.1
    have e2 : pLog A C ψ ω = fun z => -canonLogH id z := by
      funext z
      simp only [pLog, pInv_of_notMem hω, pFwd_of_notMem hω, id_eq]
    rw [e2]
    exact hid.neg

/-- The chart domain is open. -/
theorem isOpen_dom (c : Chart) : IsOpen (c.dom : Set ℂ) := c.dom.isOpen

/-- **The lift of the shifted canonical pocket chart is harmonic on the chart domain at every sample**
(`Im ℓ − 2πn` with `ℓ` holomorphic on the open chart domain). -/
theorem harmonicOnNhd_lift_shiftChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (n : Ω → ℤ) (ω : Ω) :
    InnerProductSpace.HarmonicOnNhd (shiftChart (pChart A C ψ ω) (n ω)).2.2
      (shiftChart (pChart A C ψ ω) (n ω)).dom := by
  intro z hz
  have hd := differentiableOn_pLog hCo hCH hψ ω
  have ha : AnalyticAt ℂ (pLog A C ψ ω) z :=
    hd.analyticAt ((isOpen_dom (pChart A C ψ ω)).mem_nhds hz)
  exact ha.harmonicAt_im.sub (InnerProductSpace.harmonicAt_const _)

/-- The lift of the shifted canonical pocket chart is continuous on the chart domain at every sample. -/
theorem continuousOn_lift_shiftChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (n : Ω → ℤ) (ω : Ω) :
    ContinuousOn (shiftChart (pChart A C ψ ω) (n ω)).2.2 (shiftChart (pChart A C ψ ω) (n ω)).dom :=
  (Complex.continuous_im.comp_continuousOn (differentiableOn_pLog hCo hCH hψ ω).continuousOn).sub
    continuousOn_const

end Lift

/-! ### Measurability on the whole sample space -/

section Meas

variable {Ω : Type*} {𝓦 : MeasurableSpace Ω} {A : Set Ω} {C : Ω → Set ℂ} {ψ : Ω → ℂ → ℂ}

/-- The domain events of the shifted canonical pocket chart are walls-measurable. -/
theorem measurableSet_mem_dom_shiftChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hA : MeasurableSet[𝓦] A)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω}) (n : Ω → ℤ) (z : ℂ) :
    MeasurableSet[𝓦] {ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom} :=
  measurableSet_mem_dom_pChart (mΩ := 𝓦) hCo hCH hψ hA hCm z

/-- The forward values of the shifted canonical pocket chart at fixed points are walls-measurable on the domain
events. -/
theorem measurable_fwd_shiftChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hA : MeasurableSet[𝓦] A)
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) (n : Ω → ℤ) (z : ℂ) :
    Measurable[𝓦] ({ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}.indicator
      fun ω => (shiftChart (pChart A C ψ ω) (n ω)).1 z) :=
  measurable_fwd_pChart (mΩ := 𝓦) hCo hCH hψ hA hψm z

/-- **The lift values of the shifted canonical pocket chart at fixed points are walls-measurable on the domain
events, on all of `Ω`**: on `{ω ∈ A, z ∈ C ω}` by the measurable canonical logarithm (`isPocketChartOn_pChart`,
`isPocketChartOn_shift`); on `{ω ∉ A, z ∈ ℍ}` the lift is the constant `−Im canonLogH id z` minus `2πn`. -/
theorem measurable_lift_shiftChart (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H)
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hA : MeasurableSet[𝓦] A)
    (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) (z : ℂ) :
    Measurable[𝓦] ({ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom}.indicator
      fun ω => (shiftChart (pChart A C ψ ω) (n ω)).2.2 z) := by
  have hon := isPocketChartOn_shift (isPocketChartOn_pChart (mΩ := 𝓦) hA hCo hCH hψ hCm hψm).1 hCm hn
  set S₁ := {ω | ω ∈ A ∧ z ∈ C ω} with hS₁
  set S₂ := Aᶜ ∩ {_ω : Ω | z ∈ H} with hS₂
  have hS : {ω | z ∈ (shiftChart (pChart A C ψ ω) (n ω)).dom} = S₁ ∪ S₂ := by
    ext ω
    change z ∈ (pChart A C ψ ω).dom ↔ _
    rw [mem_dom_pChart_iff hCo hCH hψ]
    rfl
  have hdisj : Disjoint S₁ S₂ := Set.disjoint_left.2 fun ω h1 h2 => h2.1 h1.1
  rw [hS, indicator_union_of_disjoint hdisj]
  refine (hon.2 z).add ?_
  have hnm : Measurable[𝓦] fun ω => 2 * π * (n ω : ℝ) :=
    measurable_const.mul ((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp hn)
  have e : S₂.indicator (fun ω => (shiftChart (pChart A C ψ ω) (n ω)).2.2 z) =
      S₂.indicator fun ω => (-canonLogH id z).im - 2 * π * (n ω : ℝ) := by
    refine indicator_congr fun ω hω => ?_
    change (pLog A C ψ ω z).im - 2 * π * (n ω : ℝ) = _
    simp only [pLog, pInv_of_notMem hω.1, pFwd_of_notMem hω.1, id_eq]
  rw [e]
  exact (measurable_const.sub hnm).indicator (hA.compl.inter (MeasurableSet.const _))

end Meas

/-! ### The field `h₀ + u` -/

section Field

variable {Ω : Type*}

/-- A deterministic harmonic mean `u` as a distribution is `φ ↦ ∫ u φ`. -/
theorem smoothDist_eq_integral {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    (φ : TestOn upperHalfPlaneOpens) : smoothDist upperHalfPlaneOpens u φ = ∫ z, u z * φ z := by
  have hc : ContinuousOn u (upperHalfPlaneOpens : Set ℂ) := fun z hz =>
    (hu z hz).1.continuousAt.continuousWithinAt
  rw [smoothDist_apply hc]
  congr 1
  funext z
  ring

/-- **The centred field of `h₀ + smoothDist u` is `h₀`.** -/
theorem centredField_add_smoothDist (h₀ : Ω → DistOn upperHalfPlaneOpens) (u : ℂ → ℝ) :
    WholeField.centredField (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) u = h₀ := by
  funext ω
  exact add_sub_cancel_right _ _

/-- `h₀ + smoothDist u` is measurable when `h₀` is. -/
theorem measurable_add_smoothDist {h₀ : Ω → DistOn upperHalfPlaneOpens} [MeasurableSpace Ω] (hh₀ : Measurable h₀)
    (u : ℂ → ℝ) : Measurable fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u :=
  PocketCoupling.measurable_add_const hh₀ _ fun _ => rfl

end Field

end InteractingSLE.Sec7.Lemma725RefChart

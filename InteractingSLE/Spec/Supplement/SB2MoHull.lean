/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasLift
import InteractingSLE.Spec.Restart.ChartMeasRandom
import InteractingSLE.Spec.Jordan.Chart

/-!
# The canonical chart of a hull: the mapping-out function, shifted, with the canonical lift

Packet PROVE-SB2-LCMEAN, round 11 (item F2 of §R10.2: canonical relative charts, needed under every option of D5).
LCOND's transfer to the retained kernel (`Lcd.ae_isCondFlowLineDriverOn_glue_condExpKernel`) needs one chart on all
of `Ω`, independent of the retained sample. The relative chart of an actual lower stage maps out the retained union
`fill(A ∪ B_{<ℓ})`; its canonical form is the mapping-out function `g_A` of that hull (hydrodynamic normalization)
shifted by a real constant, with the canonical logarithm of `g_A′` (`Restart.canonDerivLog`, zero argument high up)
as its lift. This file builds that chart deterministically:

* `hullChart A x₀`: forward map `g_A − x₀`, inverse `y ↦ g_A⁻¹(y + x₀)` (`invFunOn` on `ℍ \ A`), lift
  `Im canonDerivLog A`;
* **`isDomainChart_hullChart`**: for a compact `ℍ`-hull `A`, `hullChart A x₀` is a domain chart of `ℍ \ A`
  (conformal, image of `ℍ` exactly `ℍ \ A`, lift a branch of `arg` of the derivative);
* `coe_dom_hullChart`, `continuousOn_lift_hullChart`, `hullChart_fwd`, `hullChart_lift`;
* **`measurableSet_mem_dom_hullChart`, `measurable_indicator_fwd_hullChart`,
  `measurable_indicator_lift_hullChart`**: for a random compact set `K` observed through its dyadic hits, connected
  to the real line, and a measurable shift, the chart of `fill(K ω)` has measurable domain events, forward map and
  lift (the measurability inputs of K2 and of `Lv.isCondFlowLineDriverOn_of_hasSafeLaw_onI`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Function MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Theorem14.SB.Mo

/-- **The canonical chart of a hull** `A`, shifted by `x₀`: forward map `g_A − x₀`, inverse `y ↦ g_A⁻¹(y + x₀)` on
`ℍ`, lift the imaginary part of the canonical logarithm of `g_A′`. -/
def hullChart (A : Set ℂ) (x₀ : ℝ) : Chart :=
  (fun z => ConformalImage.mapOut A z - (x₀ : ℂ),
    fun y => invFunOn (ConformalImage.mapOut A) (H \ A) (y + (x₀ : ℂ)),
    fun z => (Restart.canonDerivLog A z).im)

@[simp] theorem hullChart_fwd (A : Set ℂ) (x₀ : ℝ) (z : ℂ) :
    (hullChart A x₀).1 z = ConformalImage.mapOut A z - (x₀ : ℂ) := rfl

@[simp] theorem hullChart_inv (A : Set ℂ) (x₀ : ℝ) (y : ℂ) :
    (hullChart A x₀).2.1 y = invFunOn (ConformalImage.mapOut A) (H \ A) (y + (x₀ : ℂ)) := rfl

@[simp] theorem hullChart_lift (A : Set ℂ) (x₀ : ℝ) (z : ℂ) :
    (hullChart A x₀).2.2 z = (Restart.canonDerivLog A z).im := rfl

theorem add_ofReal_mem_H {y : ℂ} (hy : y ∈ H) (x₀ : ℝ) : y + (x₀ : ℂ) ∈ H := by
  show 0 < (y + (x₀ : ℂ)).im
  rw [add_im, ofReal_im, add_zero]
  exact hy

theorem sub_ofReal_mem_H {y : ℂ} (hy : y ∈ H) (x₀ : ℝ) : y - (x₀ : ℂ) ∈ H := by
  show 0 < (y - (x₀ : ℂ)).im
  rw [sub_im, ofReal_im, sub_zero]
  exact hy

variable {A : Set ℂ}

/-- **The canonical chart of a compact `ℍ`-hull is a domain chart of its complement.** -/
theorem isDomainChart_hullChart (hA : IsHPHull A) (x₀ : ℝ) : IsDomainChart (H \ A) (hullChart A x₀) := by
  have hg := ConformalImage.isMapOut_mapOut hA
  have hbij := hg.1
  have hDo : IsOpen (H \ A) := hA.2.2.1
  have hinv := isConformalBijection_invFunOn hDo hbij
  have hL := Restart.isCanonicalDerivLog_canonDerivLog hA
  refine ⟨⟨?_, ?_, ?_⟩, ?_, Restart.canonDerivLog A, ⟨hL.1.1, fun z hz => ?_⟩, fun z _ => rfl⟩
  · -- the inverse is holomorphic on `ℍ`
    refine (hinv.1.comp (differentiableOn_id.add_const (x₀ : ℂ)) fun y hy => add_ofReal_mem_H hy x₀).congr
      fun y _ => rfl
  · -- the inverse maps `ℍ` into `ℍ`
    intro y hy
    exact (hinv.2.mapsTo (add_ofReal_mem_H hy x₀)).1
  · -- forward after inverse is the identity on `ℍ`
    intro y hy
    show ConformalImage.mapOut A (invFunOn (ConformalImage.mapOut A) (H \ A) (y + (x₀ : ℂ))) - (x₀ : ℂ) = y
    rw [invFunOn_eq (hbij.2.surjOn (add_ofReal_mem_H hy x₀))]
    ring
  · -- the image of `ℍ` is exactly `ℍ \ A`
    refine Subset.antisymm ?_ fun z hz => ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hinv.2.mapsTo (add_ofReal_mem_H hy x₀)
    · refine ⟨ConformalImage.mapOut A z - (x₀ : ℂ), sub_ofReal_mem_H (hbij.2.mapsTo hz) x₀, ?_⟩
      show invFunOn (ConformalImage.mapOut A) (H \ A) (ConformalImage.mapOut A z - (x₀ : ℂ) + (x₀ : ℂ)) = z
      rw [sub_add_cancel]
      exact hbij.2.injOn.leftInvOn_invFunOn hz
  · -- the canonical logarithm is a logarithm of the shifted derivative
    have h1 := hL.1.2 z hz
    rw [h1]
    show deriv (ConformalImage.mapOut A) z = deriv (fun z => ConformalImage.mapOut A z - (x₀ : ℂ)) z
    rw [deriv_sub_const]

theorem coe_dom_hullChart (hA : IsHPHull A) (x₀ : ℝ) : ((hullChart A x₀).dom : Set ℂ) = H \ A :=
  (isDomainChart_hullChart hA x₀).coe_dom

theorem isConformal_hullChart (hA : IsHPHull A) (x₀ : ℝ) : (hullChart A x₀).IsConformal :=
  (isDomainChart_hullChart hA x₀).1

theorem continuousOn_lift_hullChart (hA : IsHPHull A) (x₀ : ℝ) :
    ContinuousOn (hullChart A x₀).2.2 (hullChart A x₀).dom := by
  rw [coe_dom_hullChart hA x₀]
  exact (isDomainChart_hullChart hA x₀).continuousOn_lift

/-! ### Random hulls -/

section Random

variable {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ} {x₀ : Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem isHPHull_fillH (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (ω : Ω) : IsHPHull (fillH (K ω)) :=
  Restart.isHPHull_fillH_of_compact (hKc ω) (hKp ω)

/-- **The domain events of the random hull chart are measurable.** -/
theorem measurableSet_mem_dom_hullChart (hK : Restart.IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (z : ℂ) :
    MeasurableSet {ω | z ∈ (hullChart (fillH (K ω)) (x₀ ω)).dom} := by
  have e : {ω | z ∈ (hullChart (fillH (K ω)) (x₀ ω)).dom} = {ω | z ∈ H \ fillH (K ω)} := by
    ext ω
    show z ∈ ((hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) ↔ _
    rw [coe_dom_hullChart (isHPHull_fillH hKc hKp ω)]
    rfl
  rw [e]
  exact Restart.measurableSet_mem_H_diff_fillH hK hKc z

/-- **The forward map of the random hull chart is measurable** on its domain events. -/
theorem measurable_indicator_fwd_hullChart (hK : Restart.IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hx₀ : Measurable x₀) (z : ℂ) :
    Measurable ({ω | z ∈ (hullChart (fillH (K ω)) (x₀ ω)).dom}.indicator
      fun ω => (hullChart (fillH (K ω)) (x₀ ω)).1 z) := by
  have e : {ω | z ∈ (hullChart (fillH (K ω)) (x₀ ω)).dom} = {ω | z ∈ H \ fillH (K ω)} := by
    ext ω
    show z ∈ ((hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) ↔ _
    rw [coe_dom_hullChart (isHPHull_fillH hKc hKp ω)]
    rfl
  rw [e]
  have h1 := Restart.measurable_indicator_mapOut hK hKc hKp z
  have h2 : Measurable ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => ((x₀ ω : ℝ) : ℂ)) :=
    (Complex.measurable_ofReal.comp hx₀).indicator (Restart.measurableSet_mem_H_diff_fillH hK hKc z)
  have e2 : ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => (hullChart (fillH (K ω)) (x₀ ω)).1 z) =
      ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => ConformalImage.mapOut (fillH (K ω)) z) -
        ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => ((x₀ ω : ℝ) : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ {ω | z ∈ H \ fillH (K ω)}
    · simp only [indicator_of_mem hω, Pi.sub_apply, hullChart_fwd]
    · simp only [indicator_of_notMem hω, Pi.sub_apply, sub_zero]
  rw [e2]
  exact h1.sub h2

/-- **The lift of the random hull chart is measurable** on its domain events. -/
theorem measurable_indicator_lift_hullChart (hK : Restart.IsDyadicHitMeasurable K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (z : ℂ) :
    Measurable ({ω | z ∈ (hullChart (fillH (K ω)) (x₀ ω)).dom}.indicator
      fun ω => (hullChart (fillH (K ω)) (x₀ ω)).2.2 z) := by
  have e : {ω | z ∈ (hullChart (fillH (K ω)) (x₀ ω)).dom} = {ω | z ∈ H \ fillH (K ω)} := by
    ext ω
    show z ∈ ((hullChart (fillH (K ω)) (x₀ ω)).dom : Set ℂ) ↔ _
    rw [coe_dom_hullChart (isHPHull_fillH hKc hKp ω)]
    rfl
  rw [e]
  have h1 := Restart.measurable_indicator_canonDerivLog hK hKc hKp z
  have e2 : ({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => (hullChart (fillH (K ω)) (x₀ ω)).2.2 z) =
      fun ω => (({ω | z ∈ H \ fillH (K ω)}.indicator fun ω => Restart.canonDerivLog (fillH (K ω)) z) ω).im := by
    funext ω
    by_cases hω : ω ∈ {ω | z ∈ H \ fillH (K ω)}
    · simp only [indicator_of_mem hω, hullChart_lift]
    · simp only [indicator_of_notMem hω, zero_im]
  rw [e2]
  exact Complex.measurable_im.comp h1

end Random

end InteractingSLE.Theorem14.SB.Mo

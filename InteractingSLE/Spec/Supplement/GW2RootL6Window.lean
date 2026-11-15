/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootL6Life
import InteractingSLE.Spec.Supplement.GW2RootL6Drift
import InteractingSLE.Spec.Supplement.GW2RootS5Window

/-!
# Constructing GW2 slow-comparison windows from varying-angle evolutions

Continuation of PROVE-T14-GW2ROOT2. The lifetime and remaining-drift fields
are proved for the explicit varying-angle word. The inputs are the actual
integrated evolution, the separated starting configuration, a stopping time
and its first-zero identification. No lifetime or drift estimate is assumed.
Identification of these evolutions with the retained root law remains open.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootL6

open RootN4 Sec5

/-- The actual first passage through zero has driver value zero, almost
surely on an event where that passage precedes the continuation threshold.
This reuses the existing deterministic first-passage lemma. -/
theorem ae_zero_of_first_passage {κ : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (e : EvolutionData.{u} nL nR) (hE : e.IsEvolution κ xL ρL xR ρR)
    {a : ℝ} (ha : a < 0) {τ : e.Ω → WithTop ℝ≥0} {A : Set e.Ω}
    (hAζ : ∀ ω ∈ A, (τ ω : ℝ≥0∞) < e.lifetime ω)
    (hhit : ∀ᵐ ω ∂e.P, ω ∈ A → τ ω =
      Coupling.hitBelow (fun t => -(a + e.W t ω)) (e.lifetime ω) 0) :
    ∀ᵐ ω ∂e.P, ω ∈ A → a + e.W (τ ω).untopA ω = 0 := by
  filter_upwards [hE.2.2.2.2, hhit] with ω hp hω hωA
  have hfin : Coupling.hitBelow (fun t => -(a + e.W t ω)) (e.lifetime ω) 0 =
      (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) :=
    (hω hωA).symm.trans (coe_untopA_of_ne_top (ne_top_of_lt (hAζ ω hωA))).symm
  exact Prop59Stage.eq_zero_of_hitBelow_eq hp.isForcePath.continuousOn_w
    hp.isForcePath.w_zero ha hfin

variable {κ : ℝ} {nL₀ nR₀ : ℕ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (mL mR : ℕ)
  (φ : ℕ → ℝ) (hφ : ∀ i, φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
  (xL : Fin (mL + nL₀) → ℝ) (xR : Fin (mR + nR₀ + 1) → ℝ)
  (a : ℝ) (hy : (a, xL, xR) ∈ Prop59Stage.startsU)
  (e : EvolutionData.{u} (mL + nL₀) (mR + nR₀ + 1))
  (hE : e.IsEvolution κ xL (angleWordL κ φ mL ρL₀)
    xR (angleWordR κ φ mR ρR₀))
  (τ : e.Ω → WithTop ℝ≥0) (hτ : IsStoppingTime e.filtration τ)
  (A : Set e.Ω) (hA : MeasurableSet[hτ.measurableSpace] A)
  (hAζ : ∀ ω ∈ A, (τ ω : ℝ≥0∞) < e.lifetime ω)
  (hhit : ∀ᵐ ω ∂e.P, ω ∈ A → τ ω =
    Coupling.hitBelow (fun t => -(a + e.W t ω)) (e.lifetime ω) 0)

/-- A concrete varying-angle evolution supplies all fields of the slow
window, with the constant determined by the inherited word alone. The
first-zero stopping data are explicit; both quantitative fields are proved. -/
def restartWindowOfAngleWord :
    RootS5.RestartWindow κ (Prop59Stage.stageDriftBound κ ρL₀ ρR₀)
      (Icc (-angleWeightBound κ) (angleWeightBound κ)) := by
  let : MeasurableSpace e.Ω := e.mΩ
  have : IsProbabilityMeasure e.P := hE.1.1.isGaussianProcess.isProbabilityMeasure
  have hseed := angleChangeWeight_mem hκ hκ4 hφ 0
  have hρ : -2 < angleWordR κ φ mR ρR₀ 0 := by
    simpa only [angleWordR, Fin.cons_zero] using hseed.2
  have ha : a < 0 := by linarith only [hy.2.1]
  have hzero := ae_zero_of_first_passage e hE ha hAζ hhit
  have hcontrol : ∀ᵐ ω ∂e.P, ω ∈ A → ∀ t : ℝ≥0,
      (∀ s < t, |e.W ((τ ω).untopA + s) ω - e.W (τ ω).untopA ω| < 1) →
      (((τ ω).untopA + t : ℝ≥0) : ℝ≥0∞) < e.lifetime ω ∧
        (∀ i, 3 / 4 ≤ e.W ((τ ω).untopA + t) ω -
          e.VL i ((τ ω).untopA + t) ω) ∧
        ∀ i : Fin (mR + nR₀), 3 / 4 ≤ e.VR i.succ ((τ ω).untopA + t) ω -
          e.W ((τ ω).untopA + t) ω := by
    filter_upwards [hE.2.2.2.2, hE.ae_tendsto_threshold hκ, hzero]
      with ω hp hlim hz hωA t hnear
    have hτζ : (((τ ω).untopA : ℝ≥0) : ℝ≥0∞) < e.lifetime ω := by
      change (((τ ω).untopA : ℝ≥0) : WithTop ℝ≥0) < e.lifetime ω
      rw [coe_untopA_of_ne_top (ne_top_of_lt (hAζ ω hωA))]
      exact hAζ ω hωA
    exact lifetime_and_gaps_of_near_zero hp.isForcePath hy hρ hlim
      (hz hωA) hτζ hnear
  refine
    { nL := mL + nL₀
      nR := mR + nR₀
      xL := xL
      xR := xR
      ρL := angleWordL κ φ mL ρL₀
      ρR := angleWordR κ φ mR ρR₀
      e := e
      hE := hE
      hseed := by simpa only [angleWordR, Fin.cons_zero] using hseed.1
      τ := τ
      hτ := hτ
      A := A
      hA := hA
      hAζ := hAζ
      hlife := ?_
      hdrift := ?_ }
  · filter_upwards [hcontrol] with ω hc hωA t _ hnear
    exact (hc hωA t hnear).1
  · filter_upwards [hE.2.2.2.2, hcontrol] with ω hp hc hωA
    exact Eventually.of_forall fun r _ _ hnear => by
      obtain ⟨htζ, hL, hR⟩ := hc hωA r.toNNReal hnear
      exact otherDrift_angleWord_le hκ hκ4 hφ ρL₀ ρR₀ mL mR
        (hp.isForcePath.antitone_vL htζ) (hp.isForcePath.monotone_vR htζ) hL hR

/-- The constructed window uses exactly the given evolution. -/
theorem restartWindowOfAngleWord_e :
    (restartWindowOfAngleWord hκ hκ4 ρL₀ ρR₀ mL mR φ hφ xL xR a hy e hE
      τ hτ A hA hAζ hhit).e = e := rfl

/-- The window's event is the literal first-zero complement/small-increment
event of the original processes, without a version or law substitution. -/
theorem restartWindowOfAngleWord_slowEvent :
    (restartWindowOfAngleWord hκ hκ4 ρL₀ ρR₀ mL mR φ hφ xL xR a hy e hE
      τ hτ A hA hAζ hhit).slowEvent =
      Aᶜ ∪ {ω | ∀ t : ℝ≥0, t < 1 →
        |e.W ((τ ω).untopA + t) ω - e.W (τ ω).untopA ω| < 1} := rfl

end InteractingSLE.Theorem14.GW2TipSystem.RootL6

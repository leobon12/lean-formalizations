/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripExt
import InteractingSLE.Spec.Sec7.ContinuityProb10Seed

/-!
# Aux. lemma 22 in the strip, step 2: the retargeted evolution, continued to an integrated one

Packet PROVE-SEC5-L (specification §4.1, Aux. lemma 22, pp. 113–115). Let `(W, V, B)` be an integrated `SLE_κ(ρ)`
evolution of a distinct-position word whose right list has length `j + 1 + m`, `j ≥ 1`, with an admissible start.
PROVE-SEC7-C9/C10/TRACECLOSE's process-level target change (`Zhan.Retarget.exists_retarget_evolution_of_seed_stop`)
sends the right mark `x_k`, `k = LP.retargetIdx j m`, to `∞` by `ψ(z) = z/(x_k − z)`; the transformed driver
`newW`, time-changed by the new capacity clock, is a local evolution (on `P ⊗ P`) of LP9's transformed word before the
new horizon `newHorizon (sepTime …)`, with a localizing sequence of stopping times.

* **`Aux22Strip.exists_retarget_integrated`**: on `P ⊗ P` there is an **integrated** evolution of the transformed word
  that lives at least until the new horizon and agrees there with the transformed processes `newW`, `newVL`, `newVR`
  of the first coordinate. Proof: the first positive localizing time is a positive good stop
  (`Sec7.firstPos`, `Sec7.goodWord_of_isSLEPathUpTo`, as in `Sec7.lp9SeedTraceStatement`), and
  `Aux22Strip.exists_integrated_of_stop` continues the local evolution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Zhan.Retarget Sec2 Sec2.Assembly2 Sec2.Assembly3 Sec7

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The horizon of the retargeted evolution along one path: the new clock at the separation time. -/
abbrev retargetHorizon (xR : Fin (j + 1 + m) → ℝ) (w : ℝ≥0 → ℝ) (vR : Fin (j + 1 + m) → ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : ℝ≥0∞ :=
  newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (sepTime w (vR (LP.retargetIdx j m)) ζ)

/-- **The retargeted evolution continues to an integrated one.** On `P ⊗ P` there is an integrated evolution of LP9's
transformed word (filtration `𝓖`, Brownian motion `B'`) that lives at least until the new horizon of the first
coordinate and agrees, before that horizon, with the transformed driver and marks of the first coordinate. -/
theorem exists_retarget_integrated (hκ : 0 < κ) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω))) (B' gW : ℝ≥0 → Ω × Ω → ℝ)
      (gL : Fin (nL + (m + 1)) → ℝ≥0 → Ω × Ω → ℝ) (gR : Fin j → ℝ≥0 → Ω × Ω → ℝ) (ζG : Ω × Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR)
        (LP.retargetρR ρR) (P.prod P) 𝓖 gW gL gR B' ζG ∧
      ∀ᵐ p ∂(P.prod P), retargetHorizon xR (fun t => W t p.1) (fun i t => VR i t p.1) (ζ p.1) ≤ ζG p ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) < retargetHorizon xR (fun t => W t p.1) (fun i t => VR i t p.1) (ζ p.1) →
          newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u = gW u p ∧
          (∀ i, newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u = gL i u p) ∧
          ∀ i, newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u = gR i u p := by
  obtain ⟨𝓘, β, τ, -, hτ, hloc, S, hSst, hSae⟩ := exists_retarget_evolution_of_seed_stop hκ hD hj hE hseed
  have hF := (LP.isDistinctForceWord_retarget hD hj).1
  have hTst : IsStoppingTime (usualAugmentation 𝓘 (P.prod P))
      fun p : Ω × Ω => (firstPos (fun n (q : Ω × Ω) => S n q.1) p : WithTop ℝ≥0) :=
    fun t => Ito.le_usualAugmentation 𝓘 (P.prod P) t _ (isStoppingTime_firstPos hSst t)
  have hT0 : ∀ p : Ω × Ω, 0 < firstPos (fun n (q : Ω × Ω) => S n q.1) p := fun p => firstPos_pos _ p
  have hTτ : ∀ᵐ p ∂(P.prod P), (firstPos (fun n (q : Ω × Ω) => S n q.1) p : ℝ≥0∞) < τ p.1 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hSae] with p hp
    exact firstPos_lt (S := fun n (q : Ω × Ω) => S n q.1) (τ := fun q => τ q.1) hp.1 hp.2
  have hgood : ∀ᵐ p ∂(P.prod P), GoodWord (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR)
      (contWord (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u)
        (firstPos (fun n (q : Ω × Ω) => S n q.1)) p) := by
    filter_upwards [hloc.ae_path, hTτ] with p hp hpτ
    exact goodWord_of_isSLEPathUpTo hp hF (hT0 p) hpτ
  obtain ⟨B', gW, gL, gR, ζG, hG, hag⟩ := exists_integrated_of_stop hκ hloc hTst hT0 hTτ hgood
  refine ⟨usualAugmentation 𝓘 (P.prod P), B', gW, gL, gR, ζG, hG, ?_⟩
  have hτ' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hτ
  filter_upwards [hag, hτ'] with p hp hτp
  simp only [retargetHorizon]
  rw [← hτp]
  exact ⟨hp.2.1, hp.2.2⟩

end Aux22Strip

end Sec5

end InteractingSLE

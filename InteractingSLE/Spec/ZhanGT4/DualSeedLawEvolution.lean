/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawPath
import InteractingSLE.Spec.ZhanGT4.DualSeedLawLog

/-!
# Continuing the seeded image evolution

Packet PROVE-ZHAN-GT4-A22. Use the landed continuation theorem, which
already handles seed entrances. The exact remaining stochastic input is
Brownianity of the compensated image driver in capacity time. It is not
replaced by an assumption asserting an integrated evolution or its law.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Sec2 Sec2.Assembly2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The precise (D10) and capacity-clock Brownian input, expressed using
the actual image driver and image forces. The measure in the application
is `seedMeasure P d S`. Only agreement before the capacity horizon is
required; the Brownian coordinate continues after that horizon. -/
def SeedCapacityBrownian {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (Q : Measure Ω) (𝓗 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → ℝ≥0) (Bh : ℝ≥0 → Ω → ℝ) : Prop :=
  IsFilteredBrownianReal 𝓗 Bh Q ∧
    ∀ ω t, t ≤ T ω → Bh t ω =
      seedCapacityNoise κ ρL ρR (W · ω) (fun i u => VL i u ω) (fun j u => VR j u ω) t

/-- The deterministic image equations and the capacity Brownian input
produce a full integrated seeded evolution. Its maximal continuation
agrees with the actual image path before the stopped capacity horizon. -/
theorem exists_seeded_image_evolution_of_capacityBrownian
    {nL nR : ℕ} {κ : ℝ} (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Q : Measure Ω}
    {𝓗 : Filtration ℝ≥0 mΩ} [𝓗.IsRightContinuous]
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {T : Ω → ℝ≥0} {Bh : ℝ≥0 → Ω → ℝ}
    (hgeom : ∀ ω, SeedImageGeometry xL xR ρL ρR (W · ω) (fun i u => VL i u ω) (fun j u => VR j u ω) (T ω))
    (hB : SeedCapacityBrownian κ ρL ρR Q 𝓗 W VL VR T Bh)
    (hBc : ∀ ω, Continuous (Bh · ω))
    (hWa : ∀ t, Measurable[𝓗 t] (W t)) (hVLa : ∀ i t, Measurable[𝓗 t] (VL i t))
    (hVRa : ∀ j t, Measurable[𝓗 t] (VR j t))
    (hT : IsStoppingTime 𝓗 fun ω => (T ω : WithTop ℝ≥0)) (hT0 : ∀ ω, 0 < T ω) :
    ∃ (Wc : ℝ≥0 → Ω → ℝ) (VLc : Fin nL → ℝ≥0 → Ω → ℝ)
        (VRc : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓗 Wc VLc VRc Bh ζ ∧
      (∀ ω, (T ω : ℝ≥0∞) ≤ ζ ω) ∧
      ∀ ω t, t < T ω → Wc t ω = W t ω ∧ (∀ i, VLc i t ω = VL i t ω) ∧
        ∀ j, VRc j t ω = VR j t ω := by
  let B := Bh
  have hBQ : IsFilteredBrownianReal 𝓗 B Q := hB.1
  have : IsProbabilityMeasure Q := hBQ.isProbabilityMeasure'
  have hpath : ∀ᵐ ω ∂Q, IsSLEPathUpTo κ xL xR ρL ρR (W · ω)
      (fun i u => VL i u ω) (fun j u => VR j u ω) (B · ω) (T ω) :=
    Eventually.of_forall fun ω => Assembly2.isSLEPathUpTo_congr
      ((hgeom ω).isSLEPathUpTo hκ) rfl (fun _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
      (fun t ht => hB.2 ω t (le_of_lt (by exact_mod_cast ht)))
  have hgood : ∀ᵐ ω ∂Q, GoodWord ρL ρR (contWord W VL VR T ω) :=
    Eventually.of_forall fun ω => (hgeom ω).goodWord (hT0 ω)
  have hE := Sec2.Assembly3.isIntegratedSLEEvolution_contClosed hκ hBQ hBc hWa hVLa hVRa
    (fun ω => (hgeom ω).continuous_w) (fun i ω => (hgeom ω).continuous_left i)
    (fun j ω => (hgeom ω).continuous_right j) hpath hT hT0 hgood
  refine ⟨(fun t ω => (contState κ ρL ρR W VL VR B T t ω).1),
    (fun i t ω => (contState κ ρL ρR W VL VR B T t ω).2.1 i),
    (fun j t ω => (contState κ ρL ρR W VL VR B T t ω).2.2 j),
    (fun ω => (T ω : ℝ≥0∞) + contLife κ ρL ρR W VL VR B T ω), hE, (fun _ => le_self_add), ?_⟩
  intro ω t ht
  simp only [contState, concatAt_of_lt ht, and_self, implies_true]

end InteractingSLE.ZhanGT4

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Path
import InteractingSLE.Spec.Sec2.Assembly2Strong

/-!
# The precise noise inputs for first-mark local retargeting

The transformed path equations are proved in `TwoMarkLocal2Path`. Thus the
remaining stochastic inputs are a filtered Brownian continuation of the
canonical noise, adaptedness of the canonical coordinates, and an almost
sure version of the new horizon. No transformed SDE is a hypothesis here.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Local2

open Zhan.Retarget

/-- The local first-mark evolution from its explicitly named noise inputs.
Neither maximality of the original evolution nor a transformed-path premise
is required. This lemma does not prove the Brownian or adaptedness inputs. -/
theorem isSLEEvolutionUpTo_first_of_noise {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 𝓘 : Filtration ℝ≥0 mΩ} {κ a b r : ℝ}
    {xL ρL : Fin 0 → ℝ} {W B β : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e τ : Ω → ℝ≥0∞} (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ![r, -r] P 𝓕 W VL VR B e)
    (hτ : ∀ᵐ ω ∂P, τ ω = newHorizon a (W · ω) (VR 0 · ω)
      (sepTime (W · ω) (VR 0 · ω) (e ω)))
    (hβ : IsFilteredBrownianReal 𝓘 β P)
    (hW : AdaptedBefore 𝓘 τ (fun s ω =>
      newW (j := 0) (m := 1) ![a, b] (W · ω) (fun i t => VR i t ω) s))
    (hVL : ∀ i, AdaptedBefore 𝓘 τ (fun s ω =>
      newVL (j := 0) (m := 1) ![a, b] (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) i s))
    (hnoise : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) < τ ω →
      newB (j := 0) (m := 1) κ xL ![a, b] ρL ![r, -r]
        (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) s = β s ω) :
    Sec2.IsSLEEvolutionUpTo κ ![-1, Sec7.targetChangeReal a b]
      (LP.retargetXR (j := 0) (m := 1) ![a, b]) ![κ - 6, -r]
      (LP.retargetρR (j := 0) (m := 1) ![r, -r]) P 𝓘
      (fun s ω => newW (j := 0) (m := 1) ![a, b] (W · ω) (fun i t => VR i t ω) s)
      (fun i s ω => newVL (j := 0) (m := 1) ![a, b] (W · ω)
        (fun i t => VL i t ω) (fun i t => VR i t ω) i s)
      (fun i s ω => newVR (j := 0) (m := 1) ![a, b] (W · ω) (fun i t => VR i t ω) i s)
      β τ := by
  refine ⟨hβ, hW, hVL, (fun i => i.elim0), ?_⟩
  filter_upwards [hE.ae_path, hτ, hnoise] with ω hp hτω hn
  have h := isSLEPathUpTo_first_sep hκ ha hab hp
  rw [← hτω] at h
  exact h.congr_b (fun s hs => (hn s hs).symm)

end InteractingSLE.Sec5.TwoMark.Local2

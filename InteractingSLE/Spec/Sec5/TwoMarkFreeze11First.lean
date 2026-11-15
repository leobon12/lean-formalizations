/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkFreeze11Mart
import InteractingSLE.Spec.Sec5.TwoMarkLocal2Process

/-!
# An announced local image evolution at the first mark

The canonical first-mark driver and force images form a local SLE evolution on
the product space, with a Brownian noise continued after the image lifetime.
No frozen-version hypothesis remains.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Freeze11

open Zhan.Retarget

/-- The first-mark target change of any announced local two-mark evolution. -/
theorem exists_first_retarget_evolution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ a b r : ℝ}
    {xL ρL : Fin 0 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}
    (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ![r, -r] P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) :
    ∃ (𝓙 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω)))
      (β : ℝ≥0 → Ω × Ω → ℝ) (τ : Ω → ℝ≥0∞) (Q : ℕ → Ω → ℝ≥0),
      (∀ p, Continuous (β · p)) ∧
      (∀ᵐ ω ∂P, τ ω = newHorizon a (W · ω) (VR 0 · ω)
        (sepTime (W · ω) (VR 0 · ω) (e ω))) ∧
      Coupling.IsAnnouncingSeq 𝓙 (P.prod P) (fun p : Ω × Ω => τ p.1)
        (fun n p => Q n p.1) ∧
      Sec2.IsSLEEvolutionUpTo κ ![-1, Sec7.targetChangeReal a b]
        (LP.retargetXR (j := 0) (m := 1) ![a, b]) ![κ - 6, -r]
        (LP.retargetρR (j := 0) (m := 1) ![r, -r]) (P.prod P) 𝓙
        (fun u p => newW (j := 0) (m := 1) ![a, b] (W · p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL (j := 0) (m := 1) ![a, b] (W · p.1)
          (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR (j := 0) (m := 1) ![a, b] (W · p.1) (fun i t => VR i t p.1) i u)
        β (fun p => τ p.1) := by
  have := hE.brownian.isProbabilityMeasure'
  obtain ⟨G, S, 𝓘, τ, -, -, -, -, hτ, hW, hVL, -, hQ, -, -, hExp, h0, hc, -, hEq, hlim, -⟩ :=
    Noise10.exists_announced_noise_and_endpoint hκ ha hab hE hA
  let Q := Noise10.imageStops a G S W B VL VR e
  obtain ⟨𝓚, M, ℓ, hIK, hTC, hℓ, hMN⟩ := exists_frozen_version hQ hExp h0 hc hlim
  have hMB : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω →
      M u ω = newB (j := 0) (m := 1) κ xL ![a, b] ρL ![r, -r]
        (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u := by
    filter_upwards [hMN, hEq] with ω hm he u hu
    exact (hm u hu).trans (he u hu)
  obtain ⟨𝓙, β, hKJ, hβ, hβc, hnoise⟩ :=
    Noise10.exists_brownian_extension_of_frozen_noise hE hTC hℓ hMB
  have hIJ : ∀ u, MeasurableSpace.comap (Prod.fst : Ω × Ω → Ω) (𝓘 u) ≤ 𝓙 u := fun u =>
    (MeasurableSpace.comap_mono (hIK u)).trans (hKJ u)
  have hlift : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓘 τ X →
      AdaptedBefore 𝓙 (fun p : Ω × Ω => τ p.1) (fun u p => X u p.1) := by
    intro X hX u D hD
    exact hIJ u _ ⟨_, hX u D hD, rfl⟩
  have hAnn : Coupling.IsAnnouncingSeq 𝓙 (P.prod P) (fun p : Ω × Ω => τ p.1)
      (fun n p => Q n p.1) := by
    refine ⟨fun n u => hIJ u _ ⟨_, hQ.1 n u, rfl⟩, fun p => hQ.2.1 p.1, ?_, ?_⟩
    · intro n
      exact (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae (hQ.2.2.1 n)
    · exact (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hQ.2.2.2
  refine ⟨𝓙, β, τ, Q, hβc, hτ, hAnn, hβ, hlift hW, fun i => hlift (hVL i), fun i => i.elim0, ?_⟩
  have hLift := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae (hE.ae_path.and hτ)
  filter_upwards [hLift, hnoise] with p hp hn
  have hpath := Local2.isSLEPathUpTo_first_sep hκ ha hab hp.1
  rw [← hp.2] at hpath
  exact hpath.congr_b (fun u hu => (hn u hu).symm)

end InteractingSLE.Sec5.TwoMark.Freeze11

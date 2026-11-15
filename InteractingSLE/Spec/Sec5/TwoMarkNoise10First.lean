/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkNoise10Limit

/-!
# Canonical first-mark noise martingales and finite endpoints

An announced local source supplies the actual image filtration and announced
stops, all normalized noise martingales, and the finite-horizon endpoint limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Noise10

open Zhan.Retarget

/-- An announced local two-mark evolution has localized image noise with a finite endpoint. -/
theorem exists_announced_noise_and_endpoint {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ a b : ℝ}
    {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {A : ℕ → Ω → ℝ≥0}
    (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) :
    ∃ (G : Set Ω) (S : ℕ → Ω → ℝ≥0) (𝓘 : Filtration ℝ≥0 mΩ) (τ : Ω → ℝ≥0∞),
      MeasurableSet G ∧ P Gᶜ = 0 ∧
      (∀ ω ∈ G, Mart9.IsGood κ a b xL ρL ρR W B VL VR e S ω) ∧
      Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
        (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) S ∧
      (∀ᵐ ω ∂P, τ ω = newHorizon a (W · ω) (VR 0 · ω)
        (sepTime (W · ω) (VR 0 · ω) (e ω))) ∧
      AdaptedBefore 𝓘 τ (fun u ω =>
        newW (j := 0) (m := 1) ![a, b] (W · ω) (fun i t => VR i t ω) u) ∧
      (∀ i, AdaptedBefore 𝓘 τ (fun u ω =>
        newVL (j := 0) (m := 1) ![a, b] (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) i u)) ∧
      AdaptedBefore 𝓘 τ (fun u ω =>
        newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR (W · ω)
          (fun i t => VL i t ω) (fun i t => VR i t ω) u) ∧
      let N := localNoise κ a b xL ρL ρR G W B VL VR
      let Q := imageStops a G S W B VL VR e
      Coupling.IsAnnouncingSeq 𝓘 P τ Q ∧
      (∀ n, Martingale (fun u ω => N (min u (Q n ω)) ω) 𝓘 P) ∧
      (∀ n, Martingale (fun u ω => N (min u (Q n ω)) ω ^ 2 - ((min u (Q n ω) : ℝ≥0) : ℝ)) 𝓘 P) ∧
      (∀ θ n, Martingale (fun u ω => Real.exp (θ * N (min u (Q n ω)) ω -
        θ ^ 2 * ((min u (Q n ω) : ℝ≥0) : ℝ) / 2)) 𝓘 P) ∧
      (∀ ω, N 0 ω = 0) ∧
      (∀ n ω, Continuous fun u => N (min u (Q n ω)) ω) ∧
      (∀ n, ∃ C, ∀ u ω, |N (min u (Q n ω)) ω| ≤ C) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < τ ω →
        N u ω = newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR
          (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u) ∧
      (∀ᵐ ω ∂P, τ ω ≠ ⊤ → ∃ L : ℝ,
        Tendsto (N · ω) (𝓝[<] (τ ω).toNNReal) (𝓝 L)) ∧
      ∀ᵐ ω ∂P, ω ∈ G →
        newHorizon a (W · ω) (VR 0 · ω) (sepTime (W · ω) (VR 0 · ω) (e ω)) ≠ ⊤ →
        ∃ L : ℝ, Tendsto
          (fun u : ℝ≥0 => newB (j := 0) (m := 1) κ xL ![a, b] ρL ρR
            (W · ω) (fun i t => VL i t ω) (fun i t => VR i t ω) u)
          (𝓝[<] (newHorizon a (W · ω) (VR 0 · ω)
            (sepTime (W · ω) (VR 0 · ω) (e ω))).toNNReal) (𝓝 L) := by
  have := hE.brownian.isProbabilityMeasure'
  obtain ⟨G, S, 𝓘, τ, hGm, hGc, hgood, hS, hτ, hQ, hW, hVL, hNad, hRead⟩ :=
    Mart9.exists_announced_image_observables ha hab hE hA
  let N := localNoise κ a b xL ρL ρR G W B VL VR
  let Q := imageStops a G S W B VL VR e
  have hObs := hRead (obs κ xL ![a, b] ρL ρR 0) (contDiffOn_obs κ xL ![a, b] ρL ρR 0)
    (fun _ hp hL hR => itoGen_obs_eq_zero hκ.le hp hL hR)
  have hObs2 := fun c => hRead (obs2 κ xL ![a, b] ρL ρR 0 c) (contDiffOn_obs2 κ xL ![a, b] ρL ρR 0 c)
    (fun _ hp hL hR => itoGen_obs2_eq_zero hκ.le c hp hL hR)
  have hExp := fun θ => hRead (expObs κ xL ![a, b] ρL ρR 0 θ)
    (contDiffOn_expObs (κ := κ) (xL := xL) (xR := ![a, b]) (ρL := ρL) (ρR := ρR) (k := 0) θ)
    (fun _ hp hL hR => itoGen_expObs_eq_zero hκ θ hp hL hR)
  have hM := martingale_localNoise_stopped hκ ha hab hgood hObs
  have hM2 := martingale_localNoise_sq_stopped hκ ha hab hgood hObs2
  have hME := martingale_exp_localNoise_stopped hκ ha hab hgood hExp
  have h0 := localNoise_zero hgood
  have hZc := fun n => (Mart9.stopped_coords_regular ha hab hE hGm hGc hgood hS.1 n).2
  have hc := continuous_localNoise_stopped hκ ha hab hgood hZc
  have hb := exists_bound_localNoise_stopped hκ ha hab hgood
  have hlim := ae_tendsto_of_announced_noise hQ hM hM2 h0 hc hb
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  refine ⟨G, S, 𝓘, τ, hGm, hGc, hgood, hS, hτ, hW, hVL, hNad,
    hQ, hM, hM2, hME, h0, hc, hb, ?_, hlim, ?_⟩
  · filter_upwards [hGa, hτ] with ω hω heq u hu
    rw [heq] at hu
    exact localNoise_eq_newB hκ ha hab hgood hω hu
  · filter_upwards [hlim, hτ] with ω hl heq hω hfin
    have htfin : τ ω ≠ ⊤ := heq ▸ hfin
    obtain ⟨L, hL⟩ := hl htfin
    refine ⟨L, ?_⟩
    rw [heq] at hL
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hcoe := ENNReal.coe_toNNReal hfin
    exact localNoise_eq_newB hκ ha hab hgood hω (by
      rw [← hcoe, ENNReal.coe_lt_coe]
      exact hu)

end InteractingSLE.Sec5.TwoMark.Noise10

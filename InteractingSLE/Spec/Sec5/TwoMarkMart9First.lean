/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkMart9Exhaust

/-!
# Announced local first-mark martingale localization

An announced local two-mark evolution supplies the good event and the spatial
refinement on which the three canonical observable martingales are valid.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec5.TwoMark.Mart9

open Zhan.Retarget

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {κ a b : ℝ} {xL ρL : Fin 0 → ℝ} {ρR : Fin 2 → ℝ}
  {W B : ℝ≥0 → Ω → ℝ} {VL : Fin 0 → ℝ≥0 → Ω → ℝ} {VR : Fin 2 → ℝ≥0 → Ω → ℝ}
  {e : Ω → ℝ≥0∞} {S : ℕ → Ω → ℝ≥0} {G : Set Ω}

/-- The spatial/Brownian refinement announces the raw first-mark separation horizon. -/
theorem isAnnouncingSeq_localizer (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hGm : MeasurableSet G) (hGc : P Gᶜ = 0)
    (hgood : ∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω)
    (hS : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
      (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) S) :
    Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
      (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) (rLoc 0 G S W VL VR B e) := by
  have hGa : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hGc
  refine ⟨isStoppingTime_rLoc hE hGm hGc hgood hS.1,
    localizer_mono hgood hS.2.1, ?_, ?_⟩
  · intro n
    filter_upwards [hGa] with ω hω
    exact (hgood ω hω).loc_lt n
  · filter_upwards [hGa] with ω hω t ht
    obtain ⟨n, hn⟩ := exists_forall_le_localizer ha hab hgood (hgood ω hω) hω (hS.2.1 ω) ht
    exact ⟨n, hn n le_rfl⟩

/-- An announced local source evolution supplies an exhaustive canonical Itô martingale localization. -/
theorem exists_announced_local_martingales {A : ℕ → Ω → ℝ≥0}
    (hκ : 0 < κ) (ha : 0 < a) (hab : a < b)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL ![a, b] ρL ρR P 𝓕 W VL VR B e)
    (hA : Coupling.IsAnnouncingSeq 𝓕 P e A) :
    ∃ (G : Set Ω) (S : ℕ → Ω → ℝ≥0),
      MeasurableSet G ∧ P Gᶜ = 0 ∧
      (∀ ω ∈ G, IsGood κ a b xL ρL ρR W B VL VR e S ω) ∧
      Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
        (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) S ∧
      Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P
        (fun ω => sepTime (W · ω) (VR 0 · ω) (e ω)) (rLoc 0 G S W VL VR B e) ∧
      (∀ n, Martingale (fun t ω => obs κ xL ![a, b] ρL ρR 0
        (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
        (usualAugmentation 𝓕 P) P) ∧
      (∀ c n, Martingale (fun t ω => obs2 κ xL ![a, b] ρL ρR 0 c
        (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
        (usualAugmentation 𝓕 P) P) ∧
      ∀ θ n, Martingale (fun t ω => expObs κ xL ![a, b] ρL ρR 0 θ
        (rCoord xL ![a, b] a 0 G W VL VR (min t (rLoc 0 G S W VL VR B e n ω)) ω,
          Sec2.TwoSeed.brownG G B (min t (rLoc 0 G S W VL VR B e n ω)) ω))
        (usualAugmentation 𝓕 P) P := by
  obtain ⟨S, hS⟩ := Version6.exists_isAnnouncingSeq_sepTime hE hA (k := 0) ha
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good hE hS
  exact ⟨G, S, hGm, hGc, hgood, hS,
    isAnnouncingSeq_localizer ha hab hE hGm hGc hgood hS,
    martingale_obs_stopped ha hab hE hGm hGc hgood hS.1 hκ.le,
    fun c => martingale_obs2_stopped ha hab hE hGm hGc hgood hS.1 hκ.le c,
    fun θ => martingale_expObs_stopped ha hab hE hGm hGc hgood hS.1 hκ θ⟩

end InteractingSLE.Sec5.TwoMark.Mart9

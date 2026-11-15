/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalPassage

/-!
# Constructing every actual seed gap-band map field

Packet PROVE-ZHAN-GT4-A22. The actual gap exits supply the scale bounds
for the map field. Localization is on the original band event and keeps
the original density horizon in the Girsanov Brownian coordinate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The protected source data construct the regular map field on every
actual gap band, with zero field and restart horizon on its complement. -/
theorem exists_seedMap_gap_band_fields {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (rr : Fin n → ℝ) {d : Ω → SeedData n} {B D : ℝ≥0 → Ω → ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {ε : ℝ≥0} (hε : 0 < ε) {T : Ω → ℝ≥0} {Tm M C : ℝ}
    (hTm : ∀ ω, (T ω : ℝ) ≤ Tm) (hM : 0 ≤ M) (hC : 0 ≤ C)
    {A : Set ℂ} {r a₀ ρm : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, ε ≤ T ω → OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hclr : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).W t : ℂ) r) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω), a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA0 : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω), |(d ω).A 0 t| ≤ M)
    (hV₀ : ∀ ω, ε ≤ T ω → ∀ t ∈ Ioc (0 : ℝ) (T ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hV : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Ioc (0 : ℝ) (T ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hD : ∀ ω, ε ≤ T ω → ∀ t ∈ Ioc (0 : ℝ) (T ω), HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hnc : ∀ ω, ContinuousOn (fun u : ℝ => seedNoise κ d T u.toNNReal ω) (Ioc 0 (T ω)))
    {Y : SeedGap n → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYv : ∀ ω i (u : ℝ≥0), ε ≤ u → u ≤ T ω → Y i u ω = (d ω).gapVal i u)
    (k : ℕ) (R : ℝ≥0) : ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      let E := bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
      let S := bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T
      IsSeedDriftField (Real.sqrt κ) ρ K
        (Girsanov.girsanovProcess B (seedNoise κ d T))
        (seedImageOffset (Real.sqrt κ) D (seedNoise κ d T))
        (onEvB E (seedMappedDrift κ d T)) ε (onEvS E ε S)
        (onEv E (fun ω => (d ω).F 0)) (onEv E (fun ω => (d ω).F 1))
        (onEv E (fun ω => (d ω).F 2)) (onEv E (fun ω => (d ω).F 3))
        (onEv E (fun ω => (d ω).mapTime)) := by
  set γ : ℝ := 1 / ((k : ℝ) + 1) with hγ
  set Γ : ℝ := (k : ℝ) + 1 with hΓ
  set E := bandEv Y γ Γ ε T with hEdef
  set S := bandExit Y γ Γ ε R T with hSdef
  have hεS : ∀ ω, ε ≤ S ω := le_bandExit
  have hεT : ∀ ω ∈ E, ε ≤ T ω := fun ω hω => hω.1
  have hSr : ∀ ω ∈ E, (S ω : ℝ) ≤ T ω := fun ω hω => NNReal.coe_le_coe.2 (bandExit_le hω.1)
  have hSpos : ∀ ω, (0 : ℝ) < S ω := fun ω => (NNReal.coe_pos.2 hε).trans_le (NNReal.coe_le_coe.2 (hεS ω))
  have hγ0 : (0 : ℝ) < γ := by positivity
  obtain ⟨L, hL⟩ := exists_seedScaleOK hr ha₀ hγ0 Γ (Real.log Γ) Tm
  -- the band on `[ε, S]` and the constants
  have hband : ∀ ω ∈ E, ∀ t ∈ Icc (ε : ℝ) (S ω), (d ω).SeedBand γ Γ t := fun ω hω t ht =>
    (d ω).seedBand_of_gapVal fun i => by
      have hb := bounds_of_mem_Icc_bandExit (R := R) hYc hω ht i
      have ht0 : 0 ≤ t := ε.coe_nonneg.trans ht.1
      have h1 : ε ≤ t.toNNReal := by rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact ht.1
      have h2 : t.toNNReal ≤ T ω := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]; exact ht.2.trans (hSr ω hω)
      rw [hYv ω i t.toNNReal h1 h2, Real.coe_toNNReal _ ht0] at hb
      exact hb
  have sub : ∀ ω ∈ E, Icc (0 : ℝ) (S ω) ⊆ Icc 0 (T ω) := fun ω hω => Icc_subset_Icc_right (hSr ω hω)
  have subε : ∀ ω ∈ E, Icc (ε : ℝ) (S ω) ⊆ Icc ε (T ω) := fun ω hω => Icc_subset_Icc_right (hSr ω hω)
  have hc : ∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ γ Γ (Real.log Γ) ρm := fun ω hω =>
    (d ω).seedConst_of_band k hr ha₀ hρm (fun t ht => hclr ω (hεT ω hω) t (sub ω hω ht))
      (fun t ht => hA1 ω (hεT ω hω) t (sub ω hω ht)) (fun m t ht => hmclr ω (hεT ω hω) m t (sub ω hω ht))
      (hband ω hω)
  have hown : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W' := fun ω hω =>
    (h ω (hεT ω hω)).restrict (hSpos ω) (hSr ω hω)
  let ρ := 3 * cutRad r a₀ γ / 4
  let K := Real.exp L + Γ + M + (|κ| * (coefTot κ rr * scaleBound L) + Real.sqrt κ * C)
  have hcoef : 0 ≤ coefTot κ rr * scaleBound L :=
    mul_nonneg (coefTot_ge (κ := κ) (r := rr)).2.2.2
      (hL.base.L0.trans (le_scaleBound hL.base.L0).1)
  have hΓ0 : 0 ≤ Γ := by positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hρ : 0 < ρ := by
    have hh := cutRad_pos hr ha₀ hγ0
    dsimp only [ρ]
    positivity
  refine ⟨ρ, K, hρ, hK, seedMap_localized_field hκ hε hΓ0 hM hC hεS
    (fun ω hω => bandExit_le (hεT ω hω)) (fun ω hω => (hSr ω hω).trans (hTm ω))
    hdW hdκ hdr hown hc hL ?_ ?_ ?_ hp hb hnc (fun ω hω => hD ω (hεT ω hω))⟩
  · intro ω hω t ht
    exact hA0 ω (hεT ω hω) t (sub ω hω ⟨ε.coe_nonneg.trans ht.1, ht.2⟩)
  · intro ω hω t ht
    have hsub : Icc (ε : ℝ) (S ω) ⊆ Ioc (0 : ℝ) (T ω) := fun u hu =>
      ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2.trans (hSr ω hω)⟩
    exact (hV₀ ω (hεT ω hω) t (hsub ht)).mono hsub
  · intro ω hω m t ht
    have hsub : Icc (ε : ℝ) (S ω) ⊆ Ioc (0 : ℝ) (T ω) := fun u hu =>
      ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2.trans (hSr ω hω)⟩
    exact (hV ω (hεT ω hω) m t (hsub ht)).mono hsub

end InteractingSLE.ZhanGT4

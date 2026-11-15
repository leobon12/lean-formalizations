/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Energy
import InteractingSLE.Spec.ZhanGT4.DualSeedPathBand

/-!
# Actual adapted fields on each seeded gap band

Packet PROVE-ZHAN-GT4-A22. Build the event-localized drifted field from
actual protected geometry, coordinate rates and alive measurability.
This exports the analytic construction needed by original-clock Itô.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Every actual seed gap band supplies an adapted drifted log-field,
with the zero field and the restart horizon on its complement. -/
theorem exists_seedBand_localized_fields (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (rr : Fin n → ℝ) {B D : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    {d : Ω → SeedData n} (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ)
    (hdr : ∀ ω, (d ω).r = rr) {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ} (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) {ε : ℝ≥0} (hε : 0 < ε) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {Tm : ℝ} (hTm : ∀ ω, (T ω : ℝ) ≤ Tm) {r a₀ ρm : ℝ}
    (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, ε ≤ T ω → OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ε ≤ T ω → ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).W t : ℂ) r) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω), a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hV₀ : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (ε : ℝ) (T ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (T ω)) t)
    (hG₀ : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (ε : ℝ) (T ω),
      HasDerivWithinAt (d ω).G₀ (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Icc (ε : ℝ) (T ω)) t)
    (hV : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Icc (ε : ℝ) (T ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (T ω)) t)
    (hVc : ∀ ω, ε ≤ T ω → ∀ m, ContinuousOn ((d ω).V m) (Icc 0 (T ω)))
    (hD : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (ε : ℝ) (T ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) ((d ω).drift t) (Icc (ε : ℝ) (T ω)) t)
    (hVm : ∀ (q : ℝ≥0) m, ε ≤ q → Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0, ε ≤ q → Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).G₀ q))
    {Y : SeedGap n → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω)) (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hYv : ∀ ω i (u : ℝ≥0), ε ≤ u → u ≤ T ω → Y i u ω = (d ω).gapVal i u) (k : ℕ) (R : ℝ≥0)
    : ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      IsDriftLogField 𝓕 (Real.sqrt κ) ρ K B D
        (onEvB (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) (fun ω => (d ω).drift)) ε
        (onEvS (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) ε
          (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T))
        (onEv (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) (fun ω => (d ω).ell))
        (onEv (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) (fun ω => (d ω).ellX))
        (onEv (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) (fun ω => (d ω).ellXX))
        (onEv (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) (fun ω => (d ω).ellXXX))
        (onEv (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T) (fun ω => (d ω).ellT)) := by
  set γ : ℝ := 1 / ((k : ℝ) + 1) with hγ
  set Γ : ℝ := (k : ℝ) + 1 with hΓ
  set E := bandEv Y γ Γ ε T with hEdef
  set S := bandExit Y γ Γ ε R T with hSdef
  have hE : MeasurableSet[𝓕 ε] E := measurableSet_bandEv hYm hT
  have hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0) := isStoppingTime_bandExit hYc hYm hT
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
  have hv : ∀ ω ∈ E, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀ := fun ω hω => by
    obtain ⟨v, hv⟩ := hv₀ ω (hεT ω hω)
    have hT0 : (0 : ℝ) ≤ T ω := T ω |>.coe_nonneg
    have hmono := (h ω (hεT ω hω)).mono.monotoneOn ⟨(hSpos ω).le, hSr ω hω⟩ ⟨hT0, le_rfl⟩ (hSr ω hω)
    exact ⟨v, isForwardSol_restrict hv hmono⟩
  -- the measurability on `E ∩ {q ≤ S}`
  have hGq : ∀ q : ℝ≥0, ε ≤ q → MeasurableSet[𝓕 q] (E ∩ {ω | q ≤ S ω}) := fun q hq =>
    (𝓕.mono hq _ hE).inter (measurableSet_ge_of_isStoppingTime hS q)
  have hmeasT : ∀ (f : Ω → ℝ) (q : ℝ≥0), ε ≤ q → Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator f) →
      Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator f) := fun f q hq hf => by
    have e : (E ∩ {ω | q ≤ S ω}).indicator f = (E ∩ {ω | q ≤ S ω}).indicator ({ω | q ≤ T ω}.indicator f) := by
      have hsub : E ∩ {ω | q ≤ S ω} ⊆ {ω | q ≤ T ω} := fun ω hω =>
        (show q ≤ S ω from hω.2).trans (bandExit_le hω.1.1)
      rw [indicator_indicator, inter_eq_left.2 hsub]
    rw [e]
    exact Measurable.indicator (m := 𝓕 q) hf (hGq q hq)
  obtain ⟨hm0, hm1, hm2⟩ := seed_meas_inputs_on (fun u => hB.2.1 u) hBc hDm hDc
    hdW hdκ hdr hdφ hdζ hE hS hown hv hc
    (fun q m hq => hmeasT _ q hq (hVm q m hq))
    (fun q hq => hmeasT _ q hq (hV₀m q hq))
    (fun q hq => hmeasT _ q hq (hG₀m q hq))
  let ρ := 3 * cutRad r a₀ γ / 4
  let K := 4 * (coefTot κ rr * scaleBound L) + |κ| * (coefTot κ rr * scaleBound L)
  have hρ : 0 < ρ := by
    have hh := cutRad_pos hr ha₀ hγ0
    dsimp only [ρ]
    positivity
  have hK : 0 ≤ K := by
    have hh : 0 ≤ coefTot κ rr * scaleBound L :=
      mul_nonneg (coefTot_ge (κ := κ) (r := rr)).2.2.2
        (hL.base.L0.trans (le_scaleBound hL.base.L0).1)
    dsimp only [K]
    positivity
  refine ⟨ρ, K, hρ, hK, isDriftLogField_localize 𝓕 hK ?_ hm0 hm1 hm2⟩
  intro ω hω
  exact isDriftLogField_seed_path hκ rr ω (hdW ω) (hdκ ω) (hdr ω) (hεS ω)
    ((hSr ω hω).trans (hTm ω)) (hown ω hω) (hv ω hω) (hc ω hω) hL
    (fun t ht => (hV₀ ω (hεT ω hω) t (subε ω hω ht)).mono (subε ω hω))
    (fun t ht => (hG₀ ω (hεT ω hω) t (subε ω hω ht)).mono (subε ω hω))
    (fun m t ht => (hV ω (hεT ω hω) m t (subε ω hω ht)).mono (subε ω hω))
    (fun m => (hVc ω (hεT ω hω) m).mono (sub ω hω))
    (fun t ht => (hD ω (hεT ω hω) t (subε ω hω ht)).mono (subε ω hω))

end InteractingSLE.ZhanGT4

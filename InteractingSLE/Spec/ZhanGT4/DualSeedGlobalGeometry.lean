/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalOrigin

/-!
# Actual geometry and measurability on every seed gap band

Packet PROVE-ZHAN-GT4-A22. Restrict the protected geometry and the
forward seed-tip solution to the actual band exit; the adapted source
coordinates then give every coefficient needed for map Itô.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory Metric
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open QuantumZipper (fwdMap IsForwardSol)
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Protected source enclosures construct the geometry and adapted
actual map values on each event-localized gap band. -/
theorem seedMap_gap_band_inputs {𝓕 : Filtration ℝ≥0 mΩ} {n : ℕ}
    {d : Ω → SeedData n} {X : ℝ≥0 → Ω → ℝ} {κ : ℝ} {rr : Fin n → ℝ}
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ}
    (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hdW : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hdφ : ∀ ω, (d ω).φ = φ)
    (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {ε : ℝ≥0} (hε : 0 < ε) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0)) {r a₀ ρm : ℝ}
    (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, ε ≤ T ω → OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ε ≤ T ω → ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).W t : ℂ) r) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω, ε ≤ T ω → ∀ t ∈ Icc (0 : ℝ) (T ω), a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω, ε ≤ T ω → ∀ m, ∀ t ∈ Icc (0 : ℝ) (T ω),
      Disjoint (ball ((d ω).V m t : ℂ) ρm) ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hVm : ∀ (q : ℝ≥0) m, ε ≤ q → Measurable[𝓕 q]
      ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    {Y : SeedGap n → ℝ≥0 → Ω → ℝ} (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hYv : ∀ ω i (u : ℝ≥0), ε ≤ u → u ≤ T ω → Y i u ω = (d ω).gapVal i u)
    (k : ℕ) (R : ℝ≥0) :
    let E := bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
    let S := bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T
    (∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W') ∧
    (∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ (1 / ((k : ℝ) + 1))
      ((k : ℝ) + 1) (Real.log ((k : ℝ) + 1)) ρm) ∧
    (∀ q : ℝ≥0, ε ≤ q →
      (∀ j, Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).A j q)) ∧
        Measurable[𝓕 q] ((E ∩ {ω | q ≤ S ω}).indicator fun ω => (d ω).d10Rate q)) := by
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
  refine ⟨hown, hc, seedMap_measurable_on_event hXm hXc hdW hdφ hdζ hdκ hdr hE hS
    (fun ω hω => bandExit_le (hεT ω hω)) hown hv ?_ hVm⟩
  intro ω hω q hq hqS m
  refine ⟨ρm, hρm, ?_⟩
  exact hmclr ω (hεT ω hω) m q ⟨q.coe_nonneg,
    (NNReal.coe_le_coe.2 hqS).trans (hSr ω hω)⟩

end InteractingSLE.ZhanGT4

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedPathCut
import InteractingSLE.Spec.ZhanGT4.DualSeedPath
import InteractingSLE.Spec.ZhanGT4.DualColsFrozen

/-!
# Zhan's A.1.6, the seeded field XII: the martingale up to the cut-off `τ_k`

Packet PROVE-ZHAN-GT4-A21. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L507, R38), with A19's localization: on `[ε, τ_k]` every seed gap and scale factor of
the seeded density lies in `[1/k, k]`.

* `SeedData.SeedBand`: all gaps and scale factors of `SeedConst` in the band `γ ≤ |·| ≤ Γ` at one time;
  **`SeedData.seedConst_of_band`**: the clearances on `[0, S]` and the band on `[ε, S]` with `γ = 1/(k+1)`,
  `Γ = k + 1` give `SeedConst` with `λ = log (k+1)`;
* `SeedGap n`, `SeedData.gapVal`: the finite family of these quantities; `SeedData.seedBand_of_gapVal`;
* **`integral_indicator_mul_seed_band_eq_zero`**: for continuous adapted versions `Y` of the gap family on `[ε, T]`,
  the seeded density stopped at `τ_k = bandExit` is a martingale after `ε` on the good event `bandEv`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

/-! ### The band of the seeded constants -/

namespace SeedData

variable {n : ℕ} (d : SeedData n)

/-- **All gaps and scale factors of `SeedConst` in the band `γ ≤ |·| ≤ Γ` at time `t`.** -/
structure SeedBand (γ Γ t : ℝ) : Prop where
  E0 : γ ≤ |d.A20 t - d.A 0 t| ∧ |d.A20 t - d.A 0 t| ≤ Γ
  Em : ∀ m, γ ≤ |d.B0 t m - d.A 0 t| ∧ |d.B0 t m - d.A 0 t| ≤ Γ
  E2m : ∀ m, γ ≤ |d.A20 t - d.B0 t m| ∧ |d.A20 t - d.B0 t m| ≤ Γ
  Cmk : ∀ m k, m ≠ k → γ ≤ |d.B0 t m - d.B0 t k| ∧ |d.B0 t m - d.B0 t k| ≤ Γ
  A21 : γ ≤ |d.A21 t| ∧ |d.A21 t| ≤ Γ
  B1 : ∀ m, γ ≤ |d.B1 t m| ∧ |d.B1 t m| ≤ Γ
  O0 : γ ≤ |d.V₀ t - d.W t| ∧ |d.V₀ t - d.W t| ≤ Γ
  Om : ∀ m, γ ≤ |d.V m t - d.W t| ∧ |d.V m t - d.W t| ≤ Γ
  O0m : ∀ m, γ ≤ |d.V₀ t - d.V m t| ∧ |d.V₀ t - d.V m t| ≤ Γ
  Omk : ∀ m k, m ≠ k → γ ≤ |d.V m t - d.V k t| ∧ |d.V m t - d.V k t| ≤ Γ

theorem inScale_log_of_band {c u : ℝ} (hc : 0 < c) (h : 1 / c ≤ |u| ∧ |u| ≤ c) : InScale (Real.log c) u := by
  refine ⟨?_, ?_⟩
  · rw [Real.exp_neg, Real.exp_log hc, ← one_div]; exact h.1
  · rw [Real.exp_log hc]; exact h.2

/-- **`SeedConst` from the band**: with `γ = 1/(k+1)`, `Γ = k + 1`, `λ = log (k+1)`. -/
theorem seedConst_of_band {A : Set ℂ} {ε S r a₀ ρm : ℝ} (k : ℕ) (hr : 0 < r) (ha : 0 < a₀) (hρ : 0 < ρm)
    (hclr : ∀ t ∈ Icc (0 : ℝ) S, Disjoint (ball (d.W t : ℂ) r) ((fun z => fwdMap d.W t z + d.W t) '' A))
    (hA1 : ∀ t ∈ Icc (0 : ℝ) S, a₀ ≤ d.A 1 t)
    (hmclr : ∀ m, ∀ t ∈ Icc (0 : ℝ) S, Disjoint (ball (d.V m t : ℂ) ρm) ((fun z => fwdMap d.W t z + d.W t) '' A))
    (hb : ∀ t ∈ Icc ε S, d.SeedBand (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) t) :
    d.SeedConst A ε S r a₀ (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) (Real.log ((k : ℝ) + 1)) ρm where
  r0 := hr
  a0 := ha
  g0 := by positivity
  m0 := hρ
  clr := hclr
  A1 := hA1
  mclr := hmclr
  E0 := fun t ht => (hb t ht).E0
  Em := fun t ht => (hb t ht).Em
  E2m := fun t ht => (hb t ht).E2m
  Cmk := fun t ht => (hb t ht).Cmk
  A21 := fun t ht => inScale_log_of_band (by positivity) (hb t ht).A21
  B1 := fun t ht m => inScale_log_of_band (by positivity) ((hb t ht).B1 m)
  O0 := fun t ht => (hb t ht).O0
  Om := fun t ht => (hb t ht).Om
  O0m := fun t ht => (hb t ht).O0m
  Omk := fun t ht => (hb t ht).Omk

end SeedData

/-- The index set of the gaps and scale factors of `SeedConst`: three single quantities, five per mark, two per pair
of marks. -/
abbrev SeedGap (n : ℕ) : Type := Fin 3 ⊕ (Fin 5 × Fin n) ⊕ (Fin 2 × Fin n × Fin n)

namespace SeedData

variable {n : ℕ} (d : SeedData n)

open Classical in
/-- **The gaps and scale factors of `SeedConst`** (a pair `m = k` contributes the constant `1`). -/
def gapVal : SeedGap n → ℝ → ℝ
  | Sum.inl i, t => ![d.A20 t - d.A 0 t, d.A21 t, d.V₀ t - d.W t] i
  | Sum.inr (Sum.inl (i, m)), t =>
      ![d.B0 t m - d.A 0 t, d.A20 t - d.B0 t m, d.B1 t m, d.V m t - d.W t, d.V₀ t - d.V m t] i
  | Sum.inr (Sum.inr (i, m, k)), t => if m = k then 1 else ![d.B0 t m - d.B0 t k, d.V m t - d.V k t] i

/-- The band of `SeedConst` from the band of every gap. -/
theorem seedBand_of_gapVal {γ Γ t : ℝ} (h : ∀ i, γ ≤ |d.gapVal i t| ∧ |d.gapVal i t| ≤ Γ) :
    d.SeedBand γ Γ t where
  E0 := by simpa [gapVal] using h (Sum.inl 0)
  A21 := by simpa [gapVal] using h (Sum.inl 1)
  O0 := by simpa [gapVal] using h (Sum.inl 2)
  Em := fun m => by simpa [gapVal] using h (Sum.inr (Sum.inl (0, m)))
  E2m := fun m => by simpa [gapVal] using h (Sum.inr (Sum.inl (1, m)))
  B1 := fun m => by simpa [gapVal] using h (Sum.inr (Sum.inl (2, m)))
  Om := fun m => by simpa [gapVal] using h (Sum.inr (Sum.inl (3, m)))
  O0m := fun m => by simpa [gapVal] using h (Sum.inr (Sum.inl (4, m)))
  Cmk := fun m k hmk => by simpa [gapVal, hmk] using h (Sum.inr (Sum.inr (0, m, k)))
  Omk := fun m k hmk => by simpa [gapVal, hmk] using h (Sum.inr (Sum.inr (1, m, k)))

end SeedData

/-- A forward solution up to `T` is one up to every `T' ≤ T`. -/
theorem isForwardSol_restrict {W : ℝ → ℝ} {z : ℂ} {T T' : ℝ} {u : ℝ → ℂ} (h : IsForwardSol W z T u)
    (hT : T' ≤ T) : IsForwardSol W z T' u :=
  ⟨h.1.mono (Icc_subset_Icc_right hT), fun t ht => h.2 t ⟨ht.1, ht.2.trans hT⟩⟩

/-! ### The martingale up to the cut-off -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The seeded density stopped at the cut-off `τ_k` is a martingale after `ε` on the good event.** The data along
the paths are given up to a horizon `T` (a stopping time, `T ≤ Tm`): `OwnData`, the tip alive for the image chain,
the clearances `r`, `a₀`, `ρm` on `[0, T]`, the force ODE, the rate of `G⁰` and of the drift on `[ε, T]`, the
adaptedness of the own-chart coordinates on `{q ≤ T}`, and continuous adapted versions `Y` of the gap family
(`SeedData.gapVal`) on `[ε, T]`. With `γ_k = 1/(k+1)`, `Γ_k = k + 1`, the cut-off `τ_k = bandExit` and the good event
`E_k = bandEv`: for `ε ≤ s ≤ t` and bounded `𝓕_s`-measurable `ξ`,
`E[1_{E_k} ξ (e^{ℓ(t∧τ_k, W_{t∧τ_k})} − e^{ℓ(s∧τ_k, W_{s∧τ_k})})] = 0`. -/
theorem integral_indicator_mul_seed_band_eq_zero (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} {κ : ℝ} (hκ : 0 < κ)
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
    {s t : ℝ≥0} (hεs : ε ≤ s) (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T).indicator ξ ω *
      (Real.exp ((d ω).ell (min t (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω))
          (driftDriver (Real.sqrt κ) B D ω (min t (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω))))
        - Real.exp ((d ω).ell (min s (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω))
          (driftDriver (Real.sqrt κ) B D ω (min s (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω)))))
      ∂P = 0 := by
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
  exact integral_indicator_mul_seed_stopped_sub_eq_zero 𝓕 hκ rr hB hBc hDm hDc hS hεS hdW hdκ hdr hdφ hdζ hE
    (fun ω hω => (hSr ω hω).trans (hTm ω)) hown hv hc hL
    (fun ω hω t ht => (hV₀ ω (hεT ω hω) t (subε ω hω ht)).mono (subε ω hω))
    (fun ω hω t ht => (hG₀ ω (hεT ω hω) t (subε ω hω ht)).mono (subε ω hω))
    (fun ω hω m t ht => (hV ω (hεT ω hω) m t (subε ω hω ht)).mono (subε ω hω))
    (fun ω hω m => (hVc ω (hεT ω hω) m).mono (sub ω hω))
    (fun ω hω t ht => (hD ω (hεT ω hω) t (subε ω hω ht)).mono (subε ω hω))
    (fun q m hq => hmeasT _ q hq (hVm q m hq)) (fun q hq => hmeasT _ q hq (hV₀m q hq))
    (fun q hq => hmeasT _ q hq (hG₀m q hq)) hεs hst hξ hξb

end InteractingSLE.ZhanGT4

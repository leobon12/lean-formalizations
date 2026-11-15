/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3RRField
import InteractingSLE.Spec.ZhanGT4.D9Const

/-!
# Zhan's A.1 (G3): the frozen-curve logarithm `log M̃` as a tube field along a drifted driver

Packet PROVE-A1-G3RECTROW. Source: Astra, *Follow-up proofs*, §A.1.2–A.1.4 (`ig1_followup_proofs.txt` L268–L407:
(D9) bounds `M̃` on the protected rectangle; "with the other curve frozen" the generator of `M̃` vanishes).

A7–A8 (`MTildeBoundField`, `MTildeMartFrozen`) proved that the logarithm `ℓ = FrzData.ell` of the frozen-curve
density is a regular log-field on driver pieces with (D9) constants, and that its driftless generator vanishes. A22
(`DualSeedFusedMeas`) proved its adaptedness along any adapted continuous driver. Here these facts are packaged as an
`IsTubeLogField` along a **drifted** driver `W = σB + D` (the frozen-curve data only see the driver path, so the drift
plays no role):

* `scaleOK_of_le`: the scale conditions on a shorter horizon;
* **`isTubeLogField_frz`**: for a family of frozen data with common chart, parameter, charges and marks, whose drivers
  are an adapted continuous process and equal `σB + D` up to a stopping time `S ≤ Tm`, with image data and (D9)
  constants (`TwoCurveD9`) uniform in the sample, `ℓ` is a tube field of radius `3 · cutRad / 4` and bound
  `2 · coefTot · scaleBound L`;
* **`FrzData.gen_eq_zero_of_twoCurveD9`**: its driftless generator vanishes at the driver.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3RR

open QuantumZipper (IsForwardSol fwdMap)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The scale conditions on `[0, Tm]` give those on any shorter horizon. -/
theorem scaleOK_of_le {r a₀ γ Γ lam Tm L T : ℝ} (hr : 0 < r) (ha : 0 < a₀) (hL : ScaleOK r a₀ γ Γ lam Tm L)
    (hT : T ≤ Tm) : ScaleOK r a₀ γ Γ lam T L := by
  have hrate : 0 ≤ rateBound r a₀ := by unfold rateBound; positivity
  exact { hL with logF := (mul_le_mul_of_nonneg_right hT hrate).trans hL.logF }

/-- **The driftless generator of `log M̃` vanishes at the driver** under the (D9) facts `TwoCurveD9`, for a parameter
`d.κ = σ²`. -/
theorem FrzData.gen_eq_zero_of_twoCurveD9 {n : ℕ} (d : FrzData n) {A : Set ℂ} {T r a₀ γ Γ lam : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (hD : TwoCurveD9 d A T r a₀ γ Γ lam) {σ : ℝ} (hσ : d.κ = σ ^ 2)
    (hσ0 : σ ≠ 0) {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (hx : d.W t = x) :
    d.ellT t x + σ ^ 2 / 2 * (d.LSXX t x + d.LSX t x ^ 2) = 0 := by
  have hκ : d.κ ≠ 0 := by rw [hσ]; exact pow_ne_zero 2 hσ0
  have hg := d.gen_eq_zero_of_accesses h hκ hD.alive₀.choose_spec (q := fun m => (hD.alive m).choose)
    (fun m => (hD.alive m).choose_spec) hD.ne hD.inj ht
  rw [hx, hσ] at hg
  exact hg

/-- **`log M̃` is a tube field along a drifted driver.** Let `d ω` be frozen data with common chart `φ`, parameter
`κ`, charges `rr`, other source `ζ₀` and marks `ζ`, whose driver is the path of an adapted continuous process `X` and
equals `σB + D` on `[0, S ω]` (`S` a stopping time, `S ≤ Tm`), with image data up to `S ω` and the (D9) facts
`TwoCurveD9` with constants `r, a₀, γ, Γ, λ` independent of the sample, and a scale `L` for `Tm`. Then
`(ℓ, ℓ_x, ℓ_xx, ℓ_xxx, ℓ_t) = (d.ell, d.LSX, d.LSXX, d.LSXXX, d.ellT)` is an `IsTubeLogField` of radius
`3 · cutRad r a₀ γ / 4` and bound `2 · coefTot κ rr · scaleBound L`. -/
theorem isTubeLogField_frz {n : ℕ} {𝓕 : Filtration ℝ≥0 mΩ} {σ : ℝ} {B D : ℝ≥0 → Ω → ℝ} {S : Ω → ℝ≥0}
    (d : Ω → FrzData n) {A : Set ℂ} {φ : ℂ → ℂ} {κ ζ₀ : ℝ} {rr ζ : Fin n → ℝ}
    (hdφ : ∀ ω, (d ω).φ = φ) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    (hdζ₀ : ∀ ω, (d ω).ζ₀ = ζ₀) (hdζ : ∀ ω, (d ω).ζ = ζ)
    (hW : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S ω), (d ω).W t = driftDriver σ B D ω t)
    {X : ℝ≥0 → Ω → ℝ} (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    (hWX : ∀ ω, (d ω).W = Ito.rpath (X · ω)) (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {r a₀ γ Γ lam L Tm : ℝ} (hL : ScaleOK r a₀ γ Γ lam Tm L) (hST : ∀ ω, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hD : ∀ ω, TwoCurveD9 (d ω) A (S ω) r a₀ γ Γ lam) :
    IsTubeLogField 𝓕 σ (3 * cutRad r a₀ γ / 4) (2 * coefTot κ rr * scaleBound L) B D 0 S
      (fun ω => (d ω).ell) (fun ω => (d ω).LSX) (fun ω => (d ω).LSXX) (fun ω => (d ω).LSXXX)
      (fun ω => (d ω).ellT) := by
  set ρ := cutRad r a₀ γ with hρdef
  set K := 2 * coefTot κ rr * scaleBound L with hKdef
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) (coefTot_ge (κ := κ) (r := rr)).2.2.2)
    (hL.L0.trans (le_scaleBound hL.L0).1)
  -- the tube is the box tube around the frozen data's own driver
  have he4 : 4 * (3 * ρ / 4) = 3 * ρ := by ring
  have htube (ω : Ω) : driftTube σ B D ((0 : ℝ≥0) : ℝ) (S ω) (4 * (3 * ρ / 4)) ω =
      {p : ℝ × ℝ | p.1 ∈ Icc (0 : ℝ) (S ω) ∧ |p.2 - (d ω).W p.1| < 3 * ρ} := by
    rw [he4, NNReal.coe_zero]
    ext p
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [hW ω p.1 h1]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [← hW ω p.1 h1]; exact h2⟩
  -- the local log-fields on boxes
  have hfacts (ω : Ω) := tube_of_isLogField (ℓ := (d ω).ell) (ℓx := (d ω).LSX) (ℓxx := (d ω).LSXX)
    (ℓxxx := (d ω).LSXXX) (ℓt := (d ω).ellT) (W := (d ω).W) (ε := 0) (S := (S ω : ℝ)) (ρ := ρ) (K := K)
    (R₀ := 3 * ρ) le_rfl (fun t ht => by
      have hρ : 0 < ρ := cutRad_pos (hD ω).d9.r0 (hD ω).d9.a0 (hD ω).d9.g0
      obtain ⟨δ, hδ, hδW⟩ := Metric.continuous_iff.1 (h ω).cont t ρ hρ
      refine ⟨max 0 (t - δ / 2), min (S ω : ℝ) (t + δ / 2), box_mem_nhdsWithin_Icc (by positivity),
        ⟨max_le ht.1 (by linarith), le_min ht.2 (by linarith)⟩, ?_⟩
      have hJ : Icc (max 0 (t - δ / 2)) (min (S ω : ℝ) (t + δ / 2)) ⊆ Icc 0 (S ω) := fun u hu =>
        ⟨(le_max_left _ _).trans hu.1, hu.2.trans (min_le_left _ _)⟩
      have hsc := scaleOK_of_le (hD ω).d9.r0 (hD ω).d9.a0 hL (hST ω)
      have hLF := (d ω).isLogField_of_D9 (h ω) (hD ω).alive₀.choose_spec
        (v := fun m => ((hD ω).alive m).choose) (fun m => ((hD ω).alive m).choose_spec) (hD ω).ne (hD ω).inj hJ
        (hD ω).d9 hsc (y := (d ω).W t) fun u hu => by
          have h1 := (le_max_right (0 : ℝ) (t - δ / 2)).trans hu.1
          have h2 := hu.2.trans (min_le_right (S ω : ℝ) (t + δ / 2))
          have hh := hδW u (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith only [h1, h2, hδ])
          rwa [Real.dist_eq] at hh
      rw [hdκ ω, hdr ω] at hLF
      exact hLF)
  refine ⟨hK, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω z hz; rw [htube ω] at hz; exact ((hfacts ω).1 z hz).1
  · intro ω z hz; rw [htube ω] at hz; exact ((hfacts ω).1 z hz).2.1
  · intro ω z hz; rw [htube ω] at hz; exact ((hfacts ω).1 z hz).2.2.1
  · intro ω z hz
    rw [htube ω] at hz
    simpa only [NNReal.coe_zero] using ((hfacts ω).1 z hz).2.2.2.1
  · intro ω; rw [htube ω]; exact (hfacts ω).2.1
  · intro ω; rw [htube ω]; exact (hfacts ω).2.2.1
  · intro ω; rw [htube ω]; exact (hfacts ω).2.2.2.1
  · intro ω; rw [htube ω]; exact (hfacts ω).2.2.2.2
  · intro ω z hz; rw [htube ω] at hz; exact ((hfacts ω).1 z hz).2.2.2.2
  all_goals
    intro t _
    have hG : MeasurableSet[𝓕 t] {ω | t ≤ S ω} := measurableSet_ge_of_isStoppingTime hS t
    have hFM : ∀ u ∈ Icc (0 : ℝ) t, @FrzMeas Ω (𝓕 t) (fun ω => (d ω).W) (fun ω => (d ω).W')
        (fun ω => (d ω).a) A φ (fun ω => (S ω : ℝ)) {ω | t ≤ S ω} u := fun u hu =>
      frzMeas_of_adaptedX hXm hXc hWX hG (fun ω _ => by rw [← hdφ ω]; exact h ω) hu
        (fun ω hω => ⟨hu.1, hu.2.trans (NNReal.coe_le_coe.2 hω)⟩)
    obtain ⟨j0, j1, j2⟩ := @measurable_frzAccess_log_jet Ω (𝓕 t) n d A φ (fun ω => (S ω : ℝ)) {ω | t ≤ S ω}
      t κ ζ₀ rr ζ hdφ hdκ hdr hdζ₀ hdζ t.coe_nonneg hFM
      (fun ω _ => by simpa only [hdζ₀ ω] using (hD ω).alive₀)
      (fun m ω _ => by simpa only [hdζ ω] using (hD ω).alive m)
    have hcongr : ∀ f : Ω → ℝ → ℝ → ℝ, ({ω | t ≤ S ω}.indicator fun ω => f ω t (driftDriver σ B D ω t)) =
        {ω | t ≤ S ω}.indicator fun ω => f ω t ((d ω).W t) := fun f => by
      funext ω
      by_cases hω : ω ∈ {ω | t ≤ S ω}
      · simp only [indicator_of_mem hω, hW ω t ⟨t.coe_nonneg, NNReal.coe_le_coe.2 hω⟩]
      · simp only [indicator_of_notMem hω]
  · rw [hcongr fun ω => (d ω).ell]; exact j0
  · rw [hcongr fun ω => (d ω).LSX]; exact j1
  · rw [hcongr fun ω => (d ω).LSXX]; exact j2

end InteractingSLE.ZhanGT4.A1G3RR

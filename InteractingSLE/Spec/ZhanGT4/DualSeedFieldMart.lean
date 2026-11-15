/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFieldTube
import InteractingSLE.Spec.ZhanGT4.DualSeedDrift

/-!
# Zhan's A.1.6, the seeded field VII: the seeded density is a martingale after a positive time

Packet PROVE-ZHAN-GT4-A20. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38): "At positive own time, differentiating (D13)–(D15) by Itô and the force ODE
is the same cancelled calculation leading to (D8)."

The growing curve's driver is `W = √κ B + D` (its force-point law: `D` has the rate `b = κ ∂_xℓ_0`, the force-point
drift, `SeedData.drift`). For a family of seeded data along the paths whose driver is `W`, on cut-off pieces
`[ε, S]` with uniform constants (`SeedConst`, `SeedScaleOK`), the seeded log-density is A19's log-field along the
drifted driver:

* `SeedScaleOK.mono`: the scale conditions pass to shorter horizons;
* **`isDriftLogField_seed`**: `IsDriftLogField` for `ℓ = SeedData.ell` with tube radius `3 · cutRad r a₀ γ`, given the
  rate of `D` and the adaptedness of `ℓ, ℓ_x, ℓ_xx` along the driver (the measurability inputs, here hypotheses);
* **`integral_mul_seed_stopped_sub_eq_zero`**: hence for `ε ≤ s ≤ t` and bounded `𝓕_s`-measurable `ξ`,
  `E[ξ(e^{ℓ(t∧S, W_{t∧S})} − e^{ℓ(s∧S, W_{s∧S})})] = 0` (A19's
  `IsDriftLogField.integral_mul_stopped_sub_eq_zero`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

/-- The scale conditions pass to a shorter horizon. -/
theorem SeedScaleOK.mono {r a₀ γ Γ lam T T' L : ℝ} (hL : SeedScaleOK r a₀ γ Γ lam T L) (hr : 0 < r) (ha : 0 < a₀)
    (hT' : T' ≤ T) : SeedScaleOK r a₀ γ Γ lam T' L := by
  have hR : 0 ≤ rateBound r a₀ := by unfold rateBound; positivity
  exact ⟨{ hL.base with logF := (mul_le_mul_of_nonneg_right hT' hR).trans hL.base.logF }, hL.e4, hL.g4⟩

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The seeded log-density is a log-field along the drifted driver** on the cut-off pieces `[ε, S]`. -/
theorem isDriftLogField_seed (𝓕 : Filtration ℝ≥0 mΩ) {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (rr : Fin n → ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (S : Ω → ℝ≥0) (d : Ω → SeedData n)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Ω → Set ℂ} {r a₀ γ Γ lam ρm L Tm : ℝ} (hεS : ∀ ω, ε ≤ S ω) (hSTm : ∀ ω, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    (hc : ∀ ω, (d ω).SeedConst (A ω) ε (S ω) r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam Tm L)
    (hV₀ : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hG₀ : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).G₀ (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Icc (ε : ℝ) (S ω)) t)
    (hV : ∀ ω m, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (S ω)))
    (hD : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) ((d ω).drift t) (Icc (ε : ℝ) (S ω)) t)
    (hm0 : ∀ q : ℝ≥0, ε ≤ q →
      Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).ell q (driftDriver (Real.sqrt κ) B D ω q)))
    (hm1 : ∀ q : ℝ≥0, ε ≤ q →
      Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).ellX q (driftDriver (Real.sqrt κ) B D ω q)))
    (hm2 : ∀ q : ℝ≥0, ε ≤ q →
      Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).ellXX q (driftDriver (Real.sqrt κ) B D ω q))) :
    IsDriftLogField 𝓕 (Real.sqrt κ) (3 * cutRad r a₀ γ / 4)
      (4 * (coefTot κ rr * scaleBound L) + |κ| * (coefTot κ rr * scaleBound L)) B D (fun ω => (d ω).drift) ε S
      (fun ω => (d ω).ell) (fun ω => (d ω).ellX) (fun ω => (d ω).ellXX) (fun ω => (d ω).ellXXX)
      (fun ω => (d ω).ellT) := by
  have hL0 := hL.base.L0
  set C := coefTot κ rr * scaleBound L with hC
  have hC0 : 0 ≤ C := mul_nonneg (coefTot_ge (κ := κ) (r := rr)).2.2.2 (hL0.trans (le_scaleBound hL0).1)
  have hK : 4 * C ≤ 4 * C + |κ| * C := le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) hC0)
  have hKb : |κ| * C ≤ 4 * C + |κ| * C := le_add_of_nonneg_left (by positivity)
  have e4 : 4 * (3 * cutRad r a₀ γ / 4) = 3 * cutRad r a₀ γ := by ring
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  -- the per-path facts
  have hLω : ∀ ω, SeedScaleOK r a₀ γ Γ lam (S ω) L := fun ω => hL.mono (hc ω).r0 (hc ω).a0 (hSTm ω)
  have hCω : ∀ ω, coefTot (d ω).κ (d ω).r * scaleBound L = C := fun ω => by rw [hdκ ω, hdr ω]
  have htube : ∀ ω, driftTube (Real.sqrt κ) B D ε (S ω) (4 * (3 * cutRad r a₀ γ / 4)) ω =
      {p : ℝ × ℝ | p.1 ∈ Icc (ε : ℝ) (S ω) ∧ |p.2 - (d ω).W p.1| < 3 * cutRad r a₀ γ} := fun ω => by
    rw [e4, hdW ω]; rfl
  have hfacts := fun ω => (d ω).tube_facts (h ω) (hv₀ ω).choose_spec (hc ω) (hLω ω) ε.2 (hV₀ ω) (hG₀ ω)
    (hV ω) (hVc ω)
  refine ⟨hεS, by positivity, hD, fun ω => (d ω).continuousOn_drift (h ω) (hc ω) (hV₀ ω) (hV ω),
    fun ω t ht => ?_, fun ω p hp => ?_, fun ω p hp => ?_, fun ω p hp => ?_, fun ω p hp => ?_, fun ω => ?_,
    fun ω => ?_, fun ω => ?_, fun ω => ?_, fun ω p hp => ?_, fun ω t ht => ?_, hm0, hm1, hm2⟩
  · have := (d ω).abs_drift_le (hc ω) (hLω ω) ht
    rw [hCω ω, hdκ ω] at this
    exact this.trans hKb
  · rw [htube ω] at hp; exact ((hfacts ω).1 p hp).1
  · rw [htube ω] at hp; exact ((hfacts ω).1 p hp).2.1
  · rw [htube ω] at hp; exact ((hfacts ω).1 p hp).2.2.1
  · rw [htube ω] at hp; exact ((hfacts ω).1 p hp).2.2.2.1
  · rw [htube ω]; exact (hfacts ω).2.1
  · rw [htube ω]; exact (hfacts ω).2.2.1
  · rw [htube ω]; exact (hfacts ω).2.2.2.1
  · rw [htube ω]; exact (hfacts ω).2.2.2.2
  · rw [htube ω] at hp
    obtain ⟨b0, b1, b2, b3, bT⟩ := ((hfacts ω).1 p hp).2.2.2.2
    rw [hCω ω] at b0 b1 b2 b3 bT
    exact ⟨b0.trans hK, b1.trans hK, b2.trans hK, b3.trans hK, bT.trans hK⟩
  · have hg := (d ω).gen_eq_zero_of_const (h ω) (hc ω) ε.2 (by rw [hdκ ω]; exact hκ.ne') ht
    rw [hdκ ω, hdW ω] at hg
    rw [hsq]
    exact hg

/-- **The seeded density is a martingale after `ε`** (up to the cut-off `S`): for `ε ≤ s ≤ t` and bounded
`𝓕_s`-measurable `ξ`, `E[ξ(e^{ℓ(t∧S, W_{t∧S})} − e^{ℓ(s∧S, W_{s∧S})})] = 0` under any measure for which `B` is an
`𝓕`-Brownian motion. -/
theorem integral_mul_seed_stopped_sub_eq_zero (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} {κ : ℝ} (hκ : 0 < κ)
    {n : ℕ} (rr : Fin n → ℝ) (B D : ℝ≥0 → Ω → ℝ) (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (ε : ℝ≥0) (S : Ω → ℝ≥0)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (d : Ω → SeedData n)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Ω → Set ℂ} {r a₀ γ Γ lam ρm L Tm : ℝ} (hεS : ∀ ω, ε ≤ S ω) (hSTm : ∀ ω, (S ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (d ω).W (A ω) (d ω).φ (S ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ, IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (S ω)) v₀)
    (hc : ∀ ω, (d ω).SeedConst (A ω) ε (S ω) r a₀ γ Γ lam ρm) (hL : SeedScaleOK r a₀ γ Γ lam Tm L)
    (hV₀ : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hG₀ : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (d ω).G₀ (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Icc (ε : ℝ) (S ω)) t)
    (hV : ∀ ω m, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Icc (ε : ℝ) (S ω)) t)
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (S ω)))
    (hD : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) ((d ω).drift t) (Icc (ε : ℝ) (S ω)) t)
    (hm0 : ∀ q : ℝ≥0, ε ≤ q →
      Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).ell q (driftDriver (Real.sqrt κ) B D ω q)))
    (hm1 : ∀ q : ℝ≥0, ε ≤ q →
      Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).ellX q (driftDriver (Real.sqrt κ) B D ω q)))
    (hm2 : ∀ q : ℝ≥0, ε ≤ q →
      Measurable[𝓕 q] ({ω | q ≤ S ω}.indicator fun ω => (d ω).ellXX q (driftDriver (Real.sqrt κ) B D ω q)))
    {s t : ℝ≥0} (hεs : ε ≤ s) (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Real.exp ((d ω).ell (min t (S ω)) (driftDriver (Real.sqrt κ) B D ω (min t (S ω))))
      - Real.exp ((d ω).ell (min s (S ω)) (driftDriver (Real.sqrt κ) B D ω (min s (S ω))))) ∂P = 0 := by
  have hL' := isDriftLogField_seed 𝓕 hκ rr B D ε S d hdW hdκ hdr hεS hSTm h hv₀ hc hL hV₀ hG₀ hV hVc hD hm0 hm1
    hm2
  rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω₀⟩⟩
  · rw [Measure.eq_zero_of_isEmpty P, integral_zero_measure]
  have hρ : 0 < 3 * cutRad r a₀ γ / 4 := by
    have := cutRad_pos (hc ω₀).r0 (hc ω₀).a0 (hc ω₀).g0
    positivity
  exact hL'.integral_mul_stopped_sub_eq_zero hB hBc (Real.sqrt_nonneg _) hρ hS hεs hst hξ hξb

end InteractingSLE.ZhanGT4

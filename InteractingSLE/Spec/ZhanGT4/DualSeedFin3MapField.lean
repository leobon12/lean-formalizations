/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Map

/-!
# Protected geometry constructs the mapped-driver field

Packet PROVE-ZHAN-GT4-A22. Build the unrestricted-generator field from
actual protected enclosures. The finite-variation coordinate can be the
Girsanov offset, whose rate is supplied by the landed seeded calculation.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The reflected map and its actual derivatives form a regular drifted
field, uniformly in path and time on a protected seed band. -/
theorem seedMap_isSeedDriftField {n : ℕ} {d : Ω → SeedData n}
    {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {σ : ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    {A : Set ℂ} {r a₀ γ Γ lam ρm L M Cb : ℝ}
    (hle : ∀ ω, ε ≤ S ω) (hΓ : 0 ≤ Γ) (hM : 0 ≤ M) (hCb : 0 ≤ Cb)
    (hdW : ∀ ω, (d ω).W = driftDriver σ B D ω)
    (hown : ∀ ω, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hc : ∀ ω, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (hL : ∀ ω, SeedScaleOK r a₀ γ Γ lam (S ω) L)
    (hA0 : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) → |(d ω).A 0 t| ≤ M)
    (hD : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) → HasDerivWithinAt
      (fun u : ℝ => D u.toNNReal ω) (b ω t) (Icc (ε : ℝ) (S ω)) t)
    (hbc : ∀ ω, ContinuousOn (b ω) (Icc (ε : ℝ) (S ω)))
    (hbb : ∀ ω t, t ∈ Icc (ε : ℝ) (S ω) → |b ω t| ≤ Cb) :
    IsSeedDriftField σ (3 * cutRad r a₀ γ / 4) (Real.exp L + Γ + M + Cb) B D b ε S
      (fun ω => (d ω).F 0) (fun ω => (d ω).F 1) (fun ω => (d ω).F 2)
      (fun ω => (d ω).F 3) (fun ω => (d ω).mapTime) := by
  have hf (ω : Ω) := (d ω).map_tube_facts (hown ω) (hc ω) (hL ω) ε.coe_nonneg hΓ hM (hA0 ω)
  have he (ω : Ω) : driftTube σ B D ε (S ω) (4 * (3 * cutRad r a₀ γ / 4)) ω =
      {p : ℝ × ℝ | p.1 ∈ Icc (ε : ℝ) (S ω) ∧ |p.2 - (d ω).W p.1| < 3 * cutRad r a₀ γ} := by
    simp only [driftTube, hdW ω, show 4 * (3 * cutRad r a₀ γ / 4) = 3 * cutRad r a₀ γ by ring]
  have hK : Real.exp L + Γ + M ≤ Real.exp L + Γ + M + Cb := le_add_of_nonneg_right hCb
  refine ⟨hle, by positivity, hD, hbc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω t ht
    exact (hbb ω t ht).trans (by linarith [Real.exp_pos L])
  · intro ω p hp
    exact ((hf ω).1 p ((he ω) ▸ hp)).1
  · intro ω p hp
    exact ((hf ω).1 p ((he ω) ▸ hp)).2.1
  · intro ω p hp
    exact ((hf ω).1 p ((he ω) ▸ hp)).2.2.1
  · intro ω p hp
    exact ((hf ω).1 p ((he ω) ▸ hp)).2.2.2.1
  · intro ω
    rw [he ω]
    exact (hf ω).2.1
  · intro ω
    rw [he ω]
    exact (hf ω).2.2.1
  · intro ω
    rw [he ω]
    exact (hf ω).2.2.2.1
  · intro ω
    rw [he ω]
    exact (hf ω).2.2.2.2
  · intro ω p hp
    obtain ⟨b0, b1, b2, b3, bt⟩ := ((hf ω).1 p ((he ω) ▸ hp)).2.2.2.2
    exact ⟨b0.trans hK, b1.trans hK, b2.trans hK, b3.trans hK, bt.trans hK⟩

namespace SeedData

/-- D2 at the driver, obtained from the protected hull clearance. -/
theorem mapTime_driver_of_const {n : ℕ} (d : SeedData n) {A : Set ℂ} {ε T r a₀ γ Γ lam ρm : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hε : 0 ≤ ε) {t : ℝ} (ht : t ∈ Icc ε T) : d.mapTime t (d.W t) = -3 * d.A 2 t := by
  have hJ : Icc t t ⊆ Icc 0 T := fun s hs => by
    rw [Icc_self, mem_singleton_iff] at hs
    rw [hs]
    exact ⟨hε.trans ht.1, ht.2⟩
  have hWy : ∀ s ∈ Icc t t, |d.W s - d.W t| < clrRad r a₀ / 24 := fun s hs => by
    rw [Icc_self, mem_singleton_iff] at hs
    rw [hs, sub_self, abs_zero]
    exact div_pos (clrRad_pos hc.r0 hc.a0) (by norm_num)
  obtain ⟨hdisj, hWm, hq0, -⟩ := h.box_of_clearance hc.r0 hc.a0 hc.clr hc.A1 hJ hWy
  exact (h.re_dHat_drive hJ hdisj hWm hq0 (left_mem_Icc.2 le_rfl)).1

/-- The actual map generator after the seeded Brownian change is D10.
Its own seed gaps cancel before the image law is identified. -/
theorem map_generator_d10_of_const {n : ℕ} (d : SeedData n)
    {A : Set ℂ} {ε T r a₀ γ Γ lam ρm : ℝ}
    (h : OwnData d.W A d.φ T d.a d.W') (hc : d.SeedConst A ε T r a₀ γ Γ lam ρm)
    (hε : 0 ≤ ε) (hκ : d.κ ≠ 0) {t : ℝ} (ht : t ∈ Icc ε T) :
    d.mapTime t (d.W t) + (d.drift t + d.κ * d.ellX t (d.W t)) * d.F 1 t (d.W t) +
      d.κ / 2 * d.F 2 t (d.W t) = d.d10Rate t := by
  rw [d.mapTime_driver_of_const h hc hε ht, d.F_driver, d.F_driver]
  have hA : d.A 1 t ≠ 0 := (h.frzA_one_pos ⟨hε.trans ht.1, ht.2⟩).ne'
  linarith only [d.d10_drift hκ hA]

end SeedData

end InteractingSLE.ZhanGT4

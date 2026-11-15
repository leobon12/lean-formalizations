/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFusedMart

/-!
# Zhan's A.1 (G3): a drifted log-field plus a driftless one

Packet PROVE-A1-G3RECTROW. Source: Astra, *Follow-up proofs*, §A.1.4 (`ig1_followup_proofs.txt` L363–L407: "with the
first path fixed, `t ↦ M(s, t)` is a martingale in the second filtration").

The row of the (G3) seeded field is a product of two factors along the large curve `W = √κ B + D`: the frozen-curve
density `M̃` (whose logarithm `f` has vanishing **driftless** generator `f_t + (σ²/2)(f_xx + f_x²) = 0`: `M̃` is a local
martingale of ordinary `SLE_κ`) and the inverse force-point martingale `1/M` (whose logarithm `ℓ` is a **drifted**
log-field, `ℓ_t + b ℓ_x + (σ²/2)(ℓ_xx + ℓ_x²) = 0`, with the force drift `b = −σ² ℓ_x` at the driver). The sum `f + ℓ`
is again a drifted log-field: its drifted generator is `[f_t + (σ²/2)(f_xx + f_x²)] + [ℓ_t + b ℓ_x + (σ²/2)(ℓ_xx +
ℓ_x²)] + f_x (b + σ² ℓ_x) = 0`. This file records it:

* `driftTube_mono`, `IsDriftLogField.mono_radius`: shrinking the tube;
* `IsTubeLogField`: the tube regularity, bounds and adaptedness of `IsDriftLogField`, without a drift or generator;
  `IsTubeLogField.mono_radius`;
* **`isDriftLogField_add`**: a drifted log-field plus a tube field with vanishing driftless generator, when the drift
  is `−σ² ℓ_x` at the driver, is a drifted log-field (bound `K + K'`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3RR

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A thinner tube around the drifted driver is contained in a thicker one. -/
theorem driftTube_mono {σ : ℝ} {B D : ℝ≥0 → Ω → ℝ} {ε S R R' : ℝ} {ω : Ω} (h : R' ≤ R) :
    driftTube σ B D ε S R' ω ⊆ driftTube σ B D ε S R ω := fun _ hp => ⟨hp.1, lt_of_lt_of_le hp.2 h⟩

/-- **A drifted log-field restricts to a thinner tube.** -/
theorem IsDriftLogField.mono_radius {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ ρ' K : ℝ} {B D : ℝ≥0 → Ω → ℝ}
    {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
    (h : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt) (hρ : ρ' ≤ ρ) :
    IsDriftLogField 𝓕 σ ρ' K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt := by
  have hs : ∀ ω, driftTube σ B D ε (S ω) (4 * ρ') ω ⊆ driftTube σ B D ε (S ω) (4 * ρ) ω := fun _ =>
    driftTube_mono (by linarith)
  exact ⟨h.le, h.Knonneg, h.dD, h.contb, h.bound_b, fun ω p hp => h.dx ω p (hs ω hp),
    fun ω p hp => h.dxx ω p (hs ω hp), fun ω p hp => h.dxxx ω p (hs ω hp), fun ω p hp => h.dt ω p (hs ω hp),
    fun ω => (h.cont ω).mono (hs ω), fun ω => (h.contX ω).mono (hs ω), fun ω => (h.contXX ω).mono (hs ω),
    fun ω => (h.contT ω).mono (hs ω), fun ω p hp => h.bound ω p (hs ω hp), h.gen, h.meas0, h.meas1, h.meas2⟩

/-- **A log-field on the tube around the drifted driver** `W = σB + D` over `[ε, S]` (radius `4ρ`): the tube
regularity, the bounds and the adaptedness of `IsDriftLogField`, with no drift and no generator identity. -/
structure IsTubeLogField (𝓕 : Filtration ℝ≥0 mΩ) (σ ρ K : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (S : Ω → ℝ≥0)
    (ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ) : Prop where
  Knonneg : 0 ≤ K
  dx : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, HasDerivAt (ℓ ω p.1) (ℓx ω p.1 p.2) p.2
  dxx : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, HasDerivAt (ℓx ω p.1) (ℓxx ω p.1 p.2) p.2
  dxxx : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, HasDerivAt (ℓxx ω p.1) (ℓxxx ω p.1 p.2) p.2
  dt : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω,
    HasDerivWithinAt (fun s => ℓ ω s p.2) (ℓt ω p.1 p.2) (Icc (ε : ℝ) (S ω)) p.1
  cont : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓ ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  contX : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓx ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  contXX : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓxx ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  contT : ∀ ω, ContinuousOn (fun p : ℝ × ℝ => ℓt ω p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)
  bound : ∀ ω, ∀ p ∈ driftTube σ B D ε (S ω) (4 * ρ) ω, |ℓ ω p.1 p.2| ≤ K ∧ |ℓx ω p.1 p.2| ≤ K ∧
    |ℓxx ω p.1 p.2| ≤ K ∧ |ℓxxx ω p.1 p.2| ≤ K ∧ |ℓt ω p.1 p.2| ≤ K
  meas0 : ∀ r : ℝ≥0, ε ≤ r →
    Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓ ω r (driftDriver σ B D ω r))
  meas1 : ∀ r : ℝ≥0, ε ≤ r →
    Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓx ω r (driftDriver σ B D ω r))
  meas2 : ∀ r : ℝ≥0, ε ≤ r →
    Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓxx ω r (driftDriver σ B D ω r))

/-- **A tube field restricts to a thinner tube.** -/
theorem IsTubeLogField.mono_radius {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ ρ' K : ℝ} {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0}
    {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ} (h : IsTubeLogField 𝓕 σ ρ K B D ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hρ : ρ' ≤ ρ) : IsTubeLogField 𝓕 σ ρ' K B D ε S ℓ ℓx ℓxx ℓxxx ℓt := by
  have hs : ∀ ω, driftTube σ B D ε (S ω) (4 * ρ') ω ⊆ driftTube σ B D ε (S ω) (4 * ρ) ω := fun _ =>
    driftTube_mono (by linarith)
  exact ⟨h.Knonneg, fun ω p hp => h.dx ω p (hs ω hp), fun ω p hp => h.dxx ω p (hs ω hp),
    fun ω p hp => h.dxxx ω p (hs ω hp), fun ω p hp => h.dt ω p (hs ω hp), fun ω => (h.cont ω).mono (hs ω),
    fun ω => (h.contX ω).mono (hs ω), fun ω => (h.contXX ω).mono (hs ω), fun ω => (h.contT ω).mono (hs ω),
    fun ω p hp => h.bound ω p (hs ω hp), h.meas0, h.meas1, h.meas2⟩

/-- The indicator of a sum is the sum of the indicators. -/
theorem measurable_indicator_add {m : MeasurableSpace Ω} {G : Set Ω} {f g : Ω → ℝ}
    (hf : Measurable (G.indicator f)) (hg : Measurable (G.indicator g)) :
    Measurable (G.indicator fun ω => f ω + g ω) := by
  convert hf.add hg using 1
  funext ω
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Pi.add_apply]
  · simp only [indicator_of_notMem hω, Pi.add_apply, add_zero]

/-- **A drifted log-field plus a driftless one.** If `ℓ` is a drifted log-field along `W = σB + D` with drift `b`,
`f` is a tube field on the same tube whose driftless generator `f_t + (σ²/2)(f_xx + f_x²)` vanishes at the driver,
and the drift is `b = −σ² ℓ_x` at the driver, then `f + ℓ` is a drifted log-field with drift `b` (bound `K + K'`). -/
theorem isDriftLogField_add {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K K' : ℝ} {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ}
    {ε : ℝ≥0} {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt f fx fxx fxxx ft : Ω → ℝ → ℝ → ℝ}
    (hG : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hF : IsTubeLogField 𝓕 σ ρ K' B D ε S f fx fxx fxxx ft)
    (hgen : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω), ft ω t (driftDriver σ B D ω t) +
      σ ^ 2 / 2 * (fxx ω t (driftDriver σ B D ω t) + fx ω t (driftDriver σ B D ω t) ^ 2) = 0)
    (hb : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω), b ω t = -σ ^ 2 * ℓx ω t (driftDriver σ B D ω t)) :
    IsDriftLogField 𝓕 σ ρ (K + K') B D b ε S (fun ω t x => f ω t x + ℓ ω t x)
      (fun ω t x => fx ω t x + ℓx ω t x) (fun ω t x => fxx ω t x + ℓxx ω t x)
      (fun ω t x => fxxx ω t x + ℓxxx ω t x) (fun ω t x => ft ω t x + ℓt ω t x) := by
  have hK' := hF.Knonneg
  refine ⟨hG.le, add_nonneg hG.Knonneg hK', hG.dD, hG.contb,
    fun ω t ht => (hG.bound_b ω t ht).trans (le_add_of_nonneg_right hK'),
    fun ω p hp => (hF.dx ω p hp).add (hG.dx ω p hp), fun ω p hp => (hF.dxx ω p hp).add (hG.dxx ω p hp),
    fun ω p hp => (hF.dxxx ω p hp).add (hG.dxxx ω p hp), fun ω p hp => (hF.dt ω p hp).add (hG.dt ω p hp),
    fun ω => (hF.cont ω).add (hG.cont ω), fun ω => (hF.contX ω).add (hG.contX ω),
    fun ω => (hF.contXX ω).add (hG.contXX ω), fun ω => (hF.contT ω).add (hG.contT ω), ?_, ?_,
    fun r hr => measurable_indicator_add (hF.meas0 r hr) (hG.meas0 r hr),
    fun r hr => measurable_indicator_add (hF.meas1 r hr) (hG.meas1 r hr),
    fun r hr => measurable_indicator_add (hF.meas2 r hr) (hG.meas2 r hr)⟩
  · intro ω p hp
    obtain ⟨f0, f1, f2, f3, fT⟩ := hF.bound ω p hp
    obtain ⟨g0, g1, g2, g3, gT⟩ := hG.bound ω p hp
    refine ⟨(abs_add_le _ _).trans (by linarith), (abs_add_le _ _).trans (by linarith),
      (abs_add_le _ _).trans (by linarith), (abs_add_le _ _).trans (by linarith),
      (abs_add_le _ _).trans (by linarith)⟩
  · intro ω t ht
    have h1 := hgen ω t ht
    have h2 := hG.gen ω t ht
    have h3 := hb ω t ht
    linear_combination h1 + h2 + fx ω t (driftDriver σ B D ω t) * h3

end InteractingSLE.ZhanGT4.A1G3RR

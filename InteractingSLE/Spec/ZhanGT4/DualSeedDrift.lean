/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.MTildeMart
import InteractingSLE.Spec.ZhanGT4.DualSeedChain
import InteractingSLE.Spec.Supplement.LP4HalfBallFuture

/-!
# Zhan's A.1.6, the stochastic part II: log-fields along a drifted driver after a positive time

Packet PROVE-ZHAN-GT4-A19. Source: Astra, *Follow-up proofs*, §A.1.6 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L426–L500, R38): "At positive own time, differentiating (D13)–(D15) by Itô and the force ODE is
the same cancelled calculation leading to (D8)."

With seed marks the base law of the seeded curve is its own force-point law, not ordinary `SLE_κ`, so its driver is
`W = σB + D` with a drift `D_t = ∫ b` (the force drift), which is singular at time `0` but continuous with a bounded
rate after any positive time `ε` (as long as the force gaps stay away from zero). A8's martingale identity
(`IsDriverLogField.integral_mul_logField_stopped_sub_eq_zero`) is for a driftless driver `σB`. We reduce to it:

* **time shift**: `B'_u = B_{ε+u} − B_ε` is a Brownian motion of `u ↦ 𝓕_{ε+u}` (`isFilteredBrownianReal_shift`,
  PROVE-LP17);
* **drift absorption**: the field `ψ(u, x) = ℓ(ε + u, x + σB_ε + D_{ε+u})` along `σB'` is `ℓ` along `W` after `ε`; its
  time derivative at a fixed `x` is `ℓ_t + b ℓ_x` (chain rule along the moving point, `DualSeedChain`), so its driftless
  generator `ψ_t + (σ²/2)(ψ_xx + ψ_x²)` is the drifted generator `ℓ_t + b ℓ_x + (σ²/2)(ℓ_xx + ℓ_x²)` of `ℓ`.

## Main results

* `driftDriver`, `driftTube`; `IsDriftLogField` (a log-field on the tube of radius `4ρ` around `W` over `[ε, S]`, with a
  bounded continuous drift rate, the drifted generator identity, adaptedness);
* `IsDriftLogField.isDriverLogField_shift`: the shifted field is A8's `IsDriverLogField`;
* **`IsDriftLogField.integral_mul_stopped_sub_eq_zero`**: for `ε ≤ s ≤ t` and bounded `𝓕_s`-measurable `ξ`,
  `E[ξ (e^{ℓ(t∧S, W_{t∧S})} − e^{ℓ(s∧S, W_{s∧S})})] = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open LP.LP4HB (shiftFiltration isFilteredBrownianReal_shift)

section Drift

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The drifted driver** `W_t = σB_t + D_t` at a real time. -/
def driftDriver (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ := σ * B t.toNNReal ω + D t.toNNReal ω

/-- The tube of radius `R` around the drifted driver over `[ε, S]`. -/
def driftTube (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε S R : ℝ) (ω : Ω) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc ε S ∧ |p.2 - driftDriver σ B D ω p.1| < R}

/-- **A log-field along the drifted driver `W = σB + D` over `[ε, S]`**: on the tube of radius `4ρ` around `W`, three
space derivatives and a one-sided time derivative, continuous and bounded by `K`; the drift `D` has the continuous rate
`b`, `|b| ≤ K`; the drifted generator of `e^ℓ` vanishes at the driver; `ℓ`, `ℓ_x`, `ℓ_xx` along the driver are adapted
after `ε`. -/
structure IsDriftLogField (𝓕 : Filtration ℝ≥0 mΩ) (σ ρ K : ℝ) (B D : ℝ≥0 → Ω → ℝ) (b : Ω → ℝ → ℝ)
    (ε : ℝ≥0) (S : Ω → ℝ≥0) (ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ) : Prop where
  le : ∀ ω, ε ≤ S ω
  Knonneg : 0 ≤ K
  dD : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω),
    HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω) (b ω t) (Icc (ε : ℝ) (S ω)) t
  contb : ∀ ω, ContinuousOn (b ω) (Icc (ε : ℝ) (S ω))
  bound_b : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω), |b ω t| ≤ K
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
  gen : ∀ ω, ∀ t ∈ Icc (ε : ℝ) (S ω), ℓt ω t (driftDriver σ B D ω t) + b ω t * ℓx ω t (driftDriver σ B D ω t)
    + σ ^ 2 / 2 * (ℓxx ω t (driftDriver σ B D ω t) + ℓx ω t (driftDriver σ B D ω t) ^ 2) = 0
  meas0 : ∀ r : ℝ≥0, ε ≤ r →
    Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓ ω r (driftDriver σ B D ω r))
  meas1 : ∀ r : ℝ≥0, ε ≤ r →
    Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓx ω r (driftDriver σ B D ω r))
  meas2 : ∀ r : ℝ≥0, ε ≤ r →
    Measurable[𝓕 r] ({ω | r ≤ S ω}.indicator fun ω => ℓxx ω r (driftDriver σ B D ω r))

/-! ### The shifted objects -/

/-- The restarted Brownian motion `B'_u = B_{ε+u} − B_ε`. -/
def shiftBM (B : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) : ℝ≥0 → Ω → ℝ := fun s ω => B (ε + s) ω - B ε ω

/-- The offset `σB_ε + D_{ε+u}` of the shifted field. -/
def shiftOff (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (ω : Ω) (u : ℝ) : ℝ :=
  σ * B ε ω + D ((ε : ℝ) + u).toNNReal ω

/-- The shifted field `ψ(u, x) = ℓ(ε + u, x + σB_ε + D_{ε+u})` (also used for `ℓ_x`, `ℓ_xx`, `ℓ_xxx`). -/
def shiftField (ℓ : Ω → ℝ → ℝ → ℝ) (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) : Ω → ℝ → ℝ → ℝ :=
  fun ω u x => ℓ ω (ε + u) (x + shiftOff σ B D ε ω u)

/-- The time derivative of the shifted field, `ψ_t = ℓ_t + b ℓ_x`. -/
def shiftFieldT (ℓx ℓt : Ω → ℝ → ℝ → ℝ) (b : Ω → ℝ → ℝ) (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) :
    Ω → ℝ → ℝ → ℝ :=
  fun ω u x => ℓt ω (ε + u) (x + shiftOff σ B D ε ω u) + b ω (ε + u) * ℓx ω (ε + u) (x + shiftOff σ B D ε ω u)

theorem toNNReal_coe_add {ε : ℝ≥0} {u : ℝ} (hu : 0 ≤ u) : ((ε : ℝ) + u).toNNReal = ε + u.toNNReal := by
  rw [Real.toNNReal_add ε.coe_nonneg hu, Real.toNNReal_coe]

/-- The shifted driver plus the offset is the drifted driver after `ε`. -/
theorem shiftBM_add_shiftOff (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (ω : Ω) {u : ℝ} (hu : 0 ≤ u) :
    σ * shiftBM B ε u.toNNReal ω + shiftOff σ B D ε ω u = driftDriver σ B D ω (ε + u) := by
  simp only [shiftBM, shiftOff, driftDriver, toNNReal_coe_add hu]
  ring

theorem shiftBM_add_shiftOff' (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (ω : Ω) (r : ℝ≥0) :
    σ * shiftBM B ε r ω + shiftOff σ B D ε ω r = driftDriver σ B D ω ((ε + r : ℝ≥0) : ℝ) := by
  have h := shiftBM_add_shiftOff σ B D ε ω r.coe_nonneg
  rw [Real.toNNReal_coe] at h
  rw [h, NNReal.coe_add]

/-! ### The shifted field is a log-field along the restarted Brownian motion -/

namespace IsDriftLogField

variable {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {ε : ℝ≥0}
  {S : Ω → ℝ≥0} {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
  (hL : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
include hL

/-- `D` along the path is continuous on `[ε, S]`. -/
theorem continuousOn_D (ω : Ω) : ContinuousOn (fun s : ℝ => D s.toNNReal ω) (Icc (ε : ℝ) (S ω)) :=
  fun t ht => (hL.dD ω t ht).continuousWithinAt

omit hL in
theorem continuous_B_real (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) : Continuous fun s : ℝ => B s.toNNReal ω :=
  (hBc ω).comp continuous_real_toNNReal

/-- The drifted driver is continuous on `[ε, S]`. -/
theorem continuousOn_driftDriver (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    ContinuousOn (driftDriver σ B D ω) (Icc (ε : ℝ) (S ω)) :=
  ((continuous_const.mul (continuous_B_real hBc ω)).continuousOn).add (hL.continuousOn_D ω)

/-- `u ↦ ε + u` maps `[0, S − ε]` into `[ε, S]`. -/
theorem mapsTo_add (ω : Ω) :
    MapsTo (fun u : ℝ => (ε : ℝ) + u) (Icc 0 ((S ω - ε : ℝ≥0) : ℝ)) (Icc (ε : ℝ) (S ω)) := by
  intro u hu
  rw [NNReal.coe_sub (hL.le ω)] at hu
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- The offset is continuous on `[0, S − ε]`. -/
theorem continuousOn_shiftOff (ω : Ω) :
    ContinuousOn (shiftOff σ B D ε ω) (Icc 0 ((S ω - ε : ℝ≥0) : ℝ)) :=
  continuousOn_const.add ((hL.continuousOn_D ω).comp (continuousOn_const.add continuousOn_id) (hL.mapsTo_add ω))

/-- The shifted driver is continuous on `[0, S − ε]`. -/
theorem continuousOn_driftDriver_add (hBc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    ContinuousOn (fun u : ℝ => driftDriver σ B D ω (ε + u)) (Icc 0 ((S ω - ε : ℝ≥0) : ℝ)) :=
  (hL.continuousOn_driftDriver hBc ω).comp (continuousOn_const.add continuousOn_id) (hL.mapsTo_add ω)

/-- A point within `4ρ` of the shifted driver at a time of `[0, S − ε]` lies (after the offset) in the tube. -/
theorem mem_tube {ω : Ω} {u z : ℝ} (hu : u ∈ Icc 0 ((S ω - ε : ℝ≥0) : ℝ))
    (hz : |z - σ * shiftBM B ε u.toNNReal ω| < 4 * ρ) :
    ((ε : ℝ) + u, z + shiftOff σ B D ε ω u) ∈ driftTube σ B D ε (S ω) (4 * ρ) ω := by
  refine ⟨hL.mapsTo_add ω hu, ?_⟩
  rw [← shiftBM_add_shiftOff σ B D ε ω hu.1]
  simpa only [add_sub_add_right_eq_sub] using hz

/-- Eventually near `(t, z)`, `(ε + p₁, p₂)` lies in the tube (one-sided in time). -/
theorem eventually_mem_tube (hBc : ∀ ω, Continuous (B · ω)) {ω : Ω} {bb c t z : ℝ}
    (hsub : Icc bb c ⊆ Icc 0 ((S ω - ε : ℝ≥0) : ℝ)) (ht : t ∈ Icc bb c)
    (hz : |z - driftDriver σ B D ω (ε + t)| < 4 * ρ) :
    ∀ᶠ p in 𝓝[Icc bb c] t ×ˢ 𝓝 z, ((ε : ℝ) + p.1, p.2) ∈ driftTube σ B D ε (S ω) (4 * ρ) ω := by
  have hcw : ContinuousWithinAt (fun p : ℝ × ℝ => |p.2 - driftDriver σ B D ω (ε + p.1)|) (Icc bb c ×ˢ univ)
      (t, z) := by
    have h1 : ContinuousWithinAt (fun u : ℝ => driftDriver σ B D ω (ε + u)) (Icc bb c) t :=
      ((hL.continuousOn_driftDriver_add hBc ω).mono hsub) t ht
    have h2 : ContinuousWithinAt (fun p : ℝ × ℝ => driftDriver σ B D ω (ε + p.1)) (Icc bb c ×ˢ univ) (t, z) :=
      ContinuousWithinAt.comp (g := fun u : ℝ => driftDriver σ B D ω (ε + u)) (f := Prod.fst) (x := (t, z))
        h1 continuousWithinAt_fst fun p (hp : p ∈ Icc bb c ×ˢ univ) => hp.1
    exact (continuousWithinAt_snd.sub h2).abs
  have hev := hcw.eventually_lt continuousWithinAt_const hz
  rw [nhdsWithin_prod_eq, nhdsWithin_univ] at hev
  have hmem : ∀ᶠ p in 𝓝[Icc bb c] t ×ˢ 𝓝 z, p.1 ∈ Icc bb c :=
    tendsto_fst.eventually (self_mem_nhdsWithin (s := Icc bb c) (a := t))
  filter_upwards [hev, hmem] with p hp hp1
  exact ⟨hL.mapsTo_add ω (hsub hp1), hp⟩

/-- Continuity of a tube field after the shift `(u, x) ↦ (ε + u, x)`, along `𝓝[Icc b c] t ×ˢ 𝓝 z`. -/
theorem tendsto_shift (hBc : ∀ ω, Continuous (B · ω)) {f : ℝ → ℝ → ℝ} {ω : Ω}
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (driftTube σ B D ε (S ω) (4 * ρ) ω)) {bb c t z : ℝ}
    (hsub : Icc bb c ⊆ Icc 0 ((S ω - ε : ℝ≥0) : ℝ)) (ht : t ∈ Icc bb c)
    (hz : |z - driftDriver σ B D ω (ε + t)| < 4 * ρ) :
    Tendsto (fun p : ℝ × ℝ => f (ε + p.1) p.2) (𝓝[Icc bb c] t ×ˢ 𝓝 z) (𝓝 (f (ε + t) z)) := by
  have hmem : ((ε : ℝ) + t, z) ∈ driftTube σ B D ε (S ω) (4 * ρ) ω := ⟨hL.mapsTo_add ω (hsub ht), hz⟩
  have hm : Tendsto (fun p : ℝ × ℝ => ((ε : ℝ) + p.1, p.2)) (𝓝[Icc bb c] t ×ˢ 𝓝 z)
      (𝓝[driftTube σ B D ε (S ω) (4 * ρ) ω] ((ε : ℝ) + t, z)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, hL.eventually_mem_tube hBc hsub ht hz⟩
    have hc : Continuous fun p : ℝ × ℝ => ((ε : ℝ) + p.1, p.2) :=
      (continuous_const.add continuous_fst).prodMk continuous_snd
    exact (hc.tendsto (t, z)).mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl |>.trans (nhds_prod_eq).ge)
  exact ((hf _ hmem).tendsto).comp hm

/-- The map `(u, x) ↦ (ε + u, x + σB_ε + D_{ε+u})` is continuous on `[b, c] × ℝ` for `[b, c] ⊆ [0, S − ε]`. -/
theorem continuousOn_shiftMap {ω : Ω} {bb c : ℝ} (hsub : Icc bb c ⊆ Icc 0 ((S ω - ε : ℝ≥0) : ℝ)) (X : Set ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => ((ε : ℝ) + p.1, p.2 + shiftOff σ B D ε ω p.1)) (Icc bb c ×ˢ X) :=
  (continuousOn_const.add continuousOn_fst).prodMk (continuousOn_snd.add
    (((hL.continuousOn_shiftOff ω).mono hsub).comp continuousOn_fst fun _ hp => hp.1))

/-- **The shifted field is a regular log-field on every piece where the restarted driver stays near a centre.** -/
theorem isLogField_shift (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) (ω : Ω) {bb c y : ℝ} (hb : 0 ≤ bb)
    (hc : c ≤ ((S ω - ε : ℝ≥0) : ℝ)) (hy : ∀ r ∈ Icc bb c, |σ * shiftBM B ε r.toNNReal ω - y| < ρ) :
    IsLogField (shiftField ℓ σ B D ε ω) (shiftField ℓx σ B D ε ω) (shiftField ℓxx σ B D ε ω)
      (shiftField ℓxxx σ B D ε ω) (shiftFieldT ℓx ℓt b σ B D ε ω) bb c y ρ (K + K * K) := by
  have hK := hL.Knonneg
  have hsub : Icc bb c ⊆ Icc 0 ((S ω - ε : ℝ≥0) : ℝ) := Icc_subset_Icc hb hc
  -- points of the box are near the shifted driver
  have hnear : ∀ t ∈ Icc bb c, ∀ x, |x - y| < 3 * ρ → |x - σ * shiftBM B ε t.toNNReal ω| < 4 * ρ :=
    fun t ht x hx => by
      have h1 := hy t ht
      calc |x - σ * shiftBM B ε t.toNNReal ω| ≤ |x - y| + |y - σ * shiftBM B ε t.toNNReal ω| := abs_sub_le _ _ _
        _ < 3 * ρ + ρ := by rw [abs_sub_comm y]; exact add_lt_add hx h1
        _ = 4 * ρ := by ring
  have hmem : ∀ t ∈ Icc bb c, ∀ x, |x - y| < 3 * ρ →
      ((ε : ℝ) + t, x + shiftOff σ B D ε ω t) ∈ driftTube σ B D ε (S ω) (4 * ρ) ω :=
    fun t ht x hx => hL.mem_tube (hsub ht) (hnear t ht x hx)
  have hmaps : MapsTo (fun p : ℝ × ℝ => ((ε : ℝ) + p.1, p.2 + shiftOff σ B D ε ω p.1))
      (Icc bb c ×ˢ {x | |x - y| < 3 * ρ}) (driftTube σ B D ε (S ω) (4 * ρ) ω) :=
    fun p hp => hmem p.1 hp.1 p.2 hp.2
  have hcm := hL.continuousOn_shiftMap (σ := σ) hsub {x | |x - y| < 3 * ρ}
  -- the drifted driver at the shifted point
  have hdrv : ∀ t ∈ Icc bb c, ∀ x, |x - y| < 3 * ρ →
      |x + shiftOff σ B D ε ω t - driftDriver σ B D ω (ε + t)| < 4 * ρ := fun t ht x hx => (hmem t ht x hx).2
  refine ⟨hρ, by positivity, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_,
    ?_, ?_, ?_, ?_, fun t ht x hx => ?_⟩
  · exact HasDerivAt.comp_add_const x _ (hL.dx ω _ (hmem t ht x hx))
  · exact HasDerivAt.comp_add_const x _ (hL.dxx ω _ (hmem t ht x hx))
  · exact HasDerivAt.comp_add_const x _ (hL.dxxx ω _ (hmem t ht x hx))
  · -- the chain rule along the moving point `x + σB_ε + D_{ε+u}`
    set v : ℝ → ℝ := fun u => x + shiftOff σ B D ε ω u with hv
    have hmt := hmem t ht x hx
    have hft : HasDerivWithinAt (fun τ => ℓ ω (ε + τ) (v t)) (ℓt ω (ε + t) (v t)) (Icc bb c) t := by
      have h1 := hL.dt ω _ hmt
      have h2 : HasDerivWithinAt (fun τ : ℝ => (ε : ℝ) + τ) 1 (Icc bb c) t :=
        (hasDerivWithinAt_id t _).const_add _
      exact (h1.comp t h2 ((hL.mapsTo_add ω).mono_left hsub)).congr_deriv (mul_one _)
    have hvd : HasDerivWithinAt v (b ω (ε + t)) (Icc bb c) t := by
      have h1 := hL.dD ω _ (hL.mapsTo_add ω (hsub ht))
      have h2 : HasDerivWithinAt (fun τ : ℝ => (ε : ℝ) + τ) 1 (Icc bb c) t :=
        (hasDerivWithinAt_id t _).const_add _
      have h3 := (h1.comp t h2 ((hL.mapsTo_add ω).mono_left hsub)).congr_deriv (mul_one _)
      exact (h3.const_add (σ * B ε ω)).const_add x
    have hz : |v t - driftDriver σ B D ω (ε + t)| < 4 * ρ := hdrv t ht x hx
    have hfx : ∀ᶠ p in 𝓝[Icc bb c] t ×ˢ 𝓝 (v t), HasDerivAt (fun z => ℓ ω (ε + p.1) z) (ℓx ω (ε + p.1) p.2) p.2 :=
      (hL.eventually_mem_tube hBc hsub ht hz).mono fun p hp => hL.dx ω _ hp
    have hcx := hL.tendsto_shift hBc (f := ℓx ω) (hL.contX ω) hsub ht hz
    have hch := hasDerivWithinAt_comp_of_partial (f := fun τ z => ℓ ω (ε + τ) z) (fx := fun τ z => ℓx ω (ε + τ) z)
      hft hvd hfx hcx
    refine hch.congr_deriv ?_
    simp only [shiftFieldT, hv]
    ring
  · exact (hL.cont ω).comp hcm hmaps
  · exact (hL.contX ω).comp hcm hmaps
  · exact (hL.contXX ω).comp hcm hmaps
  · refine ((hL.contT ω).comp hcm hmaps).add (ContinuousOn.mul ?_ ((hL.contX ω).comp hcm hmaps))
    exact (hL.contb ω).comp (continuousOn_const.add continuousOn_fst) fun p hp => hL.mapsTo_add ω (hsub hp.1)
  · obtain ⟨b0, b1, b2, b3, b4⟩ := hL.bound ω _ (hmem t ht x hx)
    have hbb := hL.bound_b ω _ (hL.mapsTo_add ω (hsub ht))
    have hKK : K ≤ K + K * K := le_add_of_nonneg_right (mul_nonneg hK hK)
    refine ⟨b0.trans hKK, b1.trans hKK, b2.trans hKK, b3.trans hKK, ?_⟩
    simp only [shiftFieldT]
    calc _ ≤ |ℓt ω (ε + t) (x + shiftOff σ B D ε ω t)|
          + |b ω (ε + t) * ℓx ω (ε + t) (x + shiftOff σ B D ε ω t)| := abs_add_le _ _
      _ ≤ K + K * K := by
          rw [abs_mul]
          exact add_le_add b4 (mul_le_mul hbb b1 (abs_nonneg _) hK)

/-- **The shifted field is A8's driver log-field** along the restarted Brownian motion, up to `S − ε`. -/
theorem isDriverLogField_shift (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ) :
    IsDriverLogField (shiftFiltration 𝓕 ε) σ ρ (K + K * K) (shiftBM B ε) (fun ω => S ω - ε)
      (shiftField ℓ σ B D ε) (shiftField ℓx σ B D ε) (shiftField ℓxx σ B D ε) (shiftField ℓxxx σ B D ε)
      (shiftFieldT ℓx ℓt b σ B D ε) where
  loc ω bb c y hb _ hc hy := hL.isLogField_shift hBc hρ ω hb hc hy
  gen ω r hr hrS := by
    simp only [shiftFieldT, shiftField]
    rw [shiftBM_add_shiftOff σ B D ε ω hr]
    exact hL.gen ω _ (hL.mapsTo_add ω ⟨hr, hrS⟩)
  meas0 r := by
    have e : ({ω | r ≤ S ω - ε}.indicator fun ω => shiftField ℓ σ B D ε ω r (σ * shiftBM B ε r ω)) =
        {ω | ε + r ≤ S ω}.indicator fun ω => ℓ ω ((ε + r : ℝ≥0) : ℝ)
          (driftDriver σ B D ω ((ε + r : ℝ≥0) : ℝ)) := by
      funext ω
      have hset : (ω ∈ {ω | r ≤ S ω - ε}) ↔ (ω ∈ {ω | ε + r ≤ S ω}) := le_tsub_iff_left (hL.le ω)
      by_cases hω : ω ∈ {ω | ε + r ≤ S ω}
      · rw [indicator_of_mem (hset.2 hω), indicator_of_mem hω]
        simp only [shiftField]
        rw [shiftBM_add_shiftOff', NNReal.coe_add]
      · rw [indicator_of_notMem (fun h => hω (hset.1 h)), indicator_of_notMem hω]
    rw [e]
    exact hL.meas0 (ε + r) le_self_add
  meas1 r := by
    have e : ({ω | r ≤ S ω - ε}.indicator fun ω => shiftField ℓx σ B D ε ω r (σ * shiftBM B ε r ω)) =
        {ω | ε + r ≤ S ω}.indicator fun ω => ℓx ω ((ε + r : ℝ≥0) : ℝ)
          (driftDriver σ B D ω ((ε + r : ℝ≥0) : ℝ)) := by
      funext ω
      have hset : (ω ∈ {ω | r ≤ S ω - ε}) ↔ (ω ∈ {ω | ε + r ≤ S ω}) := le_tsub_iff_left (hL.le ω)
      by_cases hω : ω ∈ {ω | ε + r ≤ S ω}
      · rw [indicator_of_mem (hset.2 hω), indicator_of_mem hω]
        simp only [shiftField]
        rw [shiftBM_add_shiftOff', NNReal.coe_add]
      · rw [indicator_of_notMem (fun h => hω (hset.1 h)), indicator_of_notMem hω]
    rw [e]
    exact hL.meas1 (ε + r) le_self_add
  meas2 r := by
    have e : ({ω | r ≤ S ω - ε}.indicator fun ω => shiftField ℓxx σ B D ε ω r (σ * shiftBM B ε r ω)) =
        {ω | ε + r ≤ S ω}.indicator fun ω => ℓxx ω ((ε + r : ℝ≥0) : ℝ)
          (driftDriver σ B D ω ((ε + r : ℝ≥0) : ℝ)) := by
      funext ω
      have hset : (ω ∈ {ω | r ≤ S ω - ε}) ↔ (ω ∈ {ω | ε + r ≤ S ω}) := le_tsub_iff_left (hL.le ω)
      by_cases hω : ω ∈ {ω | ε + r ≤ S ω}
      · rw [indicator_of_mem (hset.2 hω), indicator_of_mem hω]
        simp only [shiftField]
        rw [shiftBM_add_shiftOff', NNReal.coe_add]
      · rw [indicator_of_notMem (fun h => hω (hset.1 h)), indicator_of_notMem hω]
    rw [e]
    exact hL.meas2 (ε + r) le_self_add

omit hL in
/-- `ε + min (r − ε) (S − ε) = min r S` for `ε ≤ r`, `ε ≤ S`. -/
theorem add_min_tsub {ε r S' : ℝ≥0} (hr : ε ≤ r) (hS : ε ≤ S') : ε + min (r - ε) (S' - ε) = min r S' := by
  rcases le_total r S' with h | h
  · rw [min_eq_left (tsub_le_tsub_right h ε), min_eq_left h, add_tsub_cancel_of_le hr]
  · rw [min_eq_right (tsub_le_tsub_right h ε), min_eq_right h, add_tsub_cancel_of_le hS]

/-- The stopped exponential of the shifted field is that of `ℓ` along the drifted driver. -/
theorem logFieldExp_shift {r : ℝ≥0} (hr : ε ≤ r) (ω : Ω) :
    logFieldExp σ (shiftBM B ε) (shiftField ℓ σ B D ε) (min (r - ε) (S ω - ε)) ω =
      Real.exp (ℓ ω (min r (S ω)) (driftDriver σ B D ω (min r (S ω)))) := by
  simp only [logFieldExp, shiftField]
  rw [shiftBM_add_shiftOff', ← NNReal.coe_add, add_min_tsub hr (hL.le ω), NNReal.coe_min]

/-- **The martingale identity along the drifted driver after `ε`** (A8's identity for the shifted field): for
`ε ≤ s ≤ t` and bounded `𝓕_s`-measurable `ξ`,
`E[ξ (e^{ℓ(t∧S, W_{t∧S})} − e^{ℓ(s∧S, W_{s∧S})})] = 0`. -/
theorem integral_mul_stopped_sub_eq_zero {P : Measure Ω} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) (hσ : 0 ≤ σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) {s t : ℝ≥0} (hεs : ε ≤ s) (hst : s ≤ t)
    {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Real.exp (ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))))
      - Real.exp (ℓ ω (min s (S ω)) (driftDriver σ B D ω (min s (S ω))))) ∂P = 0 := by
  have hB' : IsFilteredBrownianReal (shiftFiltration 𝓕 ε) (shiftBM B ε) P := isFilteredBrownianReal_shift hB ε
  have hB'c : ∀ ω, Continuous (shiftBM B ε · ω) := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hS' : IsStoppingTime (shiftFiltration 𝓕 ε) fun ω => ((S ω - ε : ℝ≥0) : WithTop ℝ≥0) := by
    intro i
    have e : {ω | ((S ω - ε : ℝ≥0) : WithTop ℝ≥0) ≤ i} = {ω | (S ω : WithTop ℝ≥0) ≤ ((ε + i : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, tsub_le_iff_left]
    rw [e]
    exact hS (ε + i)
  have hξ' : Measurable[shiftFiltration 𝓕 ε (s - ε)] ξ := by
    show Measurable[𝓕 (ε + (s - ε))] ξ
    rw [add_tsub_cancel_of_le hεs]
    exact hξ
  have h := (hL.isDriverLogField_shift hBc hρ).integral_mul_logField_stopped_sub_eq_zero hB' hB'c hσ hρ hS'
    (tsub_le_tsub_right hst ε) hξ' hξb
  refine Eq.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_)) h
  simp only
  rw [hL.logFieldExp_shift (hεs.trans hst), hL.logFieldExp_shift hεs]

end IsDriftLogField

end Drift

end InteractingSLE.ZhanGT4

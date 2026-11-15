/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6CoordBCurve
import InteractingSLE.Spec.Restart.ClockInv
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# Before contact, the relative trace is `relBdry` of the physical trace, on the closed interval (D12 item 2)

Packet PROVE-GW2-BUF (round 9). Before the physical curve reaches the counterflow, its prefix lies in `relSafe`. There
the boundary extension `relBdry` of GB6's relative map is continuous (`GB6.CoordB.continuousOn_relBdry`). If the
relative driver `R` has the hulls of the `relBdry`-image of the physical prefix at the relative clock `a`, then
`relBdry ∘ γ ∘ a⁻¹` is a Loewner trace of `R`. It is continuous on the CLOSED interval up to `a τ`, and ends at
`relBdry (γ τ)`.

* `relTrace U s γ a τ u := relBdry U s (γ (invClock a τ u))`;
* **`isLoewnerTraceLT_relTrace`**, **`continuousOn_relTrace`**, **`relTrace_end`** (the hypotheses of NOJUMP's
  collision lemma `SB.Vo.rightImg_eq_iff_real_tip` at `σ = a τ`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open Supp8.GB6.CoordB Restart

/-- **The relative trace before contact**: `relBdry` of the physical trace, read at the inverse relative clock. -/
def relTrace (U : ℝ → ℝ) (s : ℝ) (γ : ℝ≥0 → ℂ) (a : ℝ≥0 → ℝ) (τ : ℝ≥0) (u : ℝ) : ℂ :=
  relBdry U s (γ (invClock a τ u.toNNReal))

variable {U : ℝ → ℝ} {s : ℝ} {γ : ℝ≥0 → ℂ} {a : ℝ≥0 → ℝ} {τ : ℝ≥0}

theorem capLife_eq (τ : ℝ≥0) : capLife a τ = ENNReal.ofReal (a τ) := by
  simp only [capLife, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.toNNReal_coe]

/-- The inverse clock reads every relative time up to `a τ`. -/
theorem invClock_mem (ha : IsClockOn a τ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (a τ)) :
    invClock a τ u.toNNReal ≤ τ ∧ a (invClock a τ u.toNNReal) = u := by
  have hle : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ capLife a τ := by
    rw [capLife_eq, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hu.1]
    exact ENNReal.ofReal_le_ofReal hu.2
  obtain ⟨h1, h2⟩ := ha.invClock_spec hle
  exact ⟨ENNReal.coe_le_coe.1 h1, by rw [h2, Real.coe_toNNReal _ hu.1]⟩

theorem relTrace_zero (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ) (hγ0 : γ 0 = 0) :
    relTrace U s γ a τ 0 = 0 := by
  unfold relTrace
  have h0 : invClock a τ (0 : ℝ).toNNReal = 0 := by
    have h := ha.invClock_apply (r := 0) (by simp)
    rw [ha.zero] at h
    exact h
  rw [h0, hγ0, relBdry_zero hU hU0 hs]

theorem relTrace_end (ha : IsClockOn a τ) : relTrace U s γ a τ (a τ) = relBdry U s (γ τ) := by
  unfold relTrace
  rw [ha.invClock_apply le_rfl]

/-- **The relative trace is continuous on the closed interval.** -/
theorem continuousOn_relTrace (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hγc : ContinuousOn γ (Iic τ)) (hsafe : MapsTo γ (Iic τ) (relSafe U s)) :
    ContinuousOn (relTrace U s γ a τ) (Icc 0 (a τ)) := by
  have hinv : ContinuousOn (fun u : ℝ => invClock a τ u.toNNReal) (Icc 0 (a τ)) := by
    refine ha.continuousOn_invClock.comp continuous_real_toNNReal.continuousOn fun u hu => ?_
    show ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ capLife a τ
    rw [capLife_eq, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hu.1]
    exact ENNReal.ofReal_le_ofReal hu.2
  have hmap : MapsTo (fun u : ℝ => invClock a τ u.toNNReal) (Icc 0 (a τ)) (Iic τ) :=
    fun u hu => (invClock_mem ha hu).1
  have hγ' : ContinuousOn (fun u : ℝ => γ (invClock a τ u.toNNReal)) (Icc 0 (a τ)) := hγc.comp hinv hmap
  exact (continuousOn_relBdry hU hU0 hs).comp hγ' fun u hu => hsafe (hmap hu)

/-- The image of a relative prefix is the `relBdry`-image of the physical prefix up to the inverse clock. -/
theorem relTrace_image (ha : IsClockOn a τ) {u : ℝ} (hu : u ∈ Icc (0 : ℝ) (a τ)) :
    relTrace U s γ a τ '' Icc 0 u = relBdry U s '' (γ '' Icc 0 (invClock a τ u.toNNReal)) := by
  obtain ⟨hr, hru⟩ := invClock_mem ha hu
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hvI : v ∈ Icc (0 : ℝ) (a τ) := ⟨hv.1, hv.2.trans hu.2⟩
    obtain ⟨hvr, hva⟩ := invClock_mem ha hvI
    refine ⟨γ (invClock a τ v.toNNReal), ⟨invClock a τ v.toNNReal, ⟨zero_le, ?_⟩, rfl⟩, rfl⟩
    by_contra hlt
    have h1 := ha.strictMonoOn (show ((invClock a τ u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ τ from ENNReal.coe_le_coe.2 hr)
      (show ((invClock a τ v.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ τ from ENNReal.coe_le_coe.2 hvr) (not_le.1 hlt)
    rw [hru, hva] at h1
    linarith [hv.2]
  · rintro ⟨_, ⟨r', hr', rfl⟩, rfl⟩
    have hr'τ : r' ≤ τ := hr'.2.trans hr
    have hmono := ha.strictMonoOn.monotoneOn (show ((r' : ℝ≥0) : ℝ≥0∞) ≤ τ from ENNReal.coe_le_coe.2 hr'τ)
      (show ((invClock a τ u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ τ from ENNReal.coe_le_coe.2 hr) hr'.2
    rw [hru] at hmono
    have h0 : 0 ≤ a r' := ha.nonneg (ENNReal.coe_le_coe.2 hr'τ)
    refine ⟨a r', ⟨h0, hmono⟩, ?_⟩
    unfold relTrace
    rw [show ((a r').toNNReal : ℝ≥0) = (a r').toNNReal from rfl, ha.invClock_apply (ENNReal.coe_le_coe.2 hr'τ)]

/-- **The relative trace is a Loewner trace of the relative driver before `a τ`**, given the hull identity in the
`relBdry` form on `[0, τ]`. -/
theorem isLoewnerTraceLT_relTrace (hU : Continuous U) (hU0 : U 0 = 0) (hs : 0 ≤ s) (ha : IsClockOn a τ)
    (hγc : ContinuousOn γ (Iic τ)) (hγ0 : γ 0 = 0) (hsafe : MapsTo γ (Iic τ) (relSafe U s)) {R : ℝ → ℝ}
    (hK : ∀ t ≤ τ, fwdHull R (a t) = fillH (relBdry U s '' (γ '' Icc 0 t))) :
    IsLoewnerTraceLT R (a τ) (relTrace U s γ a τ) := by
  refine ⟨relTrace_zero hU hU0 hs ha hγ0,
    (continuousOn_relTrace hU hU0 hs ha hγc hsafe).mono Ico_subset_Icc_self, fun u hu0 huτ => ?_⟩
  have hu : u ∈ Icc (0 : ℝ) (a τ) := ⟨hu0, huτ.le⟩
  obtain ⟨hr, hru⟩ := invClock_mem ha hu
  rw [relTrace_image ha hu, ← hK _ hr, hru]

end InteractingSLE.Theorem14.GW2Bh

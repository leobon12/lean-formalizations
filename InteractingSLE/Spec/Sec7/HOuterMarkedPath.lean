/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedLaw
import InteractingSLE.Spec.Sec7.HOuterUnion

/-!
# The outer pocket's stop `T⁰(q)` through the relative capacity in ambient time (pathwise part)

Packet PROVE-HOUTER. The port of PROVE-STRIPSYS43's pathwise part (`PocketStopMarked`, file
`PocketStopMarkedPath.lean`, section "The bounded pocket") from a reverse-contained pocket (`Sec6.IsReversePocket` with
Aux. lemma 37's attachment constancy) to a mixed or outer pocket: one realization `IsOuterPocket` bundles the erasure
facts (`R7StopIn.IsErasurePocket`), the counterflow's Loewner trace, `C ⊆ ℍ`, a Jordan coordinate and the driven
relative traversal (the relative Loewner conclusion of §5.4). The proofs are those of STRIPSYS43 with the erasure API in
place of the reverse-pocket API; the only pocket facts they use are clock and erasure facts, (GC2), the absence of
visits
inside a clock fibre (`HOuter.notMem_of_mem_Ioc_fibre'`) and the driven traversal.

The declarations live in the sub-namespace `PocketStopMarked.Outer`, so that the unported definitions (`trav`,
`relTime`, `relCap`, `stopTimeM`, `adTrace`, `ratCap`, `visPt`) and generic lemmas of `PocketStopMarked` are reused as
they are, and the ported lemmas keep their names.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked.Outer

open QuantumZipper (H Hbar)
open PocketTraversal Lemma71C

/-- **One realization of a mixed or outer pocket for the marked stop**: the erasure facts, the counterflow's Loewner
trace, `C ⊆ ℍ`, a Jordan coordinate `ψ` (`m(x₀) ↦ ∞`, `m(y₀) ↦ 0`) and the driven relative traversal. -/
structure IsOuterPocket (W : ℝ → ℝ) (η : ℝ → ℂ) (C : Set ℂ) (x₀ y₀ : ℂ) (τ σ : ℝ) (ψ : ℂ → ℂ) : Prop where
  erase : R7StopIn.IsErasurePocket η C x₀ y₀ τ σ
  trace : IsLoewnerTrace W η
  subset_H : C ⊆ H
  jordan : Sec6.IsJordanCoord C x₀ y₀ ψ
  driven : IsDrivenCurve (trav η C τ σ ψ)

section Helpers

open Sec6 PocketStopWallsFin

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

theorem pocketFibreLeft_mem' (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) (v : ℝ) :
    pocketFibreLeft η C τ σ v ∈ Icc τ σ :=
  fibreLeft_mem hP.erase.continuous_clock hP.erase.lt.le v

theorem clock_pocketFibreLeft' (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {v : ℝ}
    (hv : v ∈ Icc 0 (pocketClock η C τ σ σ)) : pocketClock η C τ σ (pocketFibreLeft η C τ σ v) = v :=
  clock_fibreLeft hP.erase.continuous_clock hP.erase.monotone_clock hP.erase.lt.le
    (by rw [R7StopIn.IsErasurePocket.clock_τ]; exact hv)

end Helpers

/-! ### The bounded pocket: relative capacity in ambient time -/

section Pocket

open Sec6 PocketUnionPt PocketStopWallsFin

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {x₀ y₀ : ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

theorem relTime_nonneg (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    {t : ℝ} (ht : t ∈ Ico τ σ) : 0 ≤ relTime η C τ σ t :=
  div_nonneg (hP.erase.clock_nonneg ht.1) (sub_pos.2 (hP.erase.clock_lt_clock_σ ht)).le

theorem clockOf_relTime (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    {t : ℝ} (ht : t ∈ Ico τ σ) : clockOf (pocketClock η C τ σ σ) (relTime η C τ σ t) = pocketClock η C τ σ t :=
  PocketLife.clockOf_div_sub (hP.erase.clock_σ_pos) (hP.erase.clock_lt_clock_σ ht)

/-- The relative time of the right fibre end of the erased time `clockOf L u` is `u`. -/
theorem relTime_fibre_clockOf (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    {u : ℝ} (hu : 0 ≤ u) :
    pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) u) ∈ Ico τ σ ∧
      relTime η C τ σ (pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) u)) = u := by
  have hL := hP.erase.clock_σ_pos
  have hv := clockOf_mem_Ico hL hu
  set t := pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) u) with htdef
  have hct : pocketClock η C τ σ t = clockOf (pocketClock η C τ σ σ) u := hP.erase.clock_fibre ⟨hv.1, hv.2.le⟩
  have htm : t ∈ Ico τ σ := ⟨(hP.erase.fibre_mem _).1, hP.erase.fibre_lt_σ hv⟩
  refine ⟨htm, (strictMonoOn_clockOf hL).injOn (relTime_nonneg hP htm) hu ?_⟩
  rw [clockOf_relTime hP htm, hct]

/-- For `z ∈ C̄ ∖ {x₀}`, the Jordan coordinate is in `ℍ` iff `z ∈ C`. -/
theorem jordan_mem_H_iff (hψ : IsJordanCoord C x₀ y₀ ψ) {z : ℂ} (hz : z ∈ closure C \ {x₀})
    (hC : IsOpen C) : ψ z ∈ H ↔ z ∈ C := by
  constructor
  · intro hH
    by_contra hzC
    have hfr : z ∈ frontier C \ {x₀} := ⟨⟨hz.1, by rwa [hC.interior_eq]⟩, hz.2⟩
    have := hψ.2.2.2.2.1 z hfr
    exact (ne_of_gt (show (0 : ℝ) < (ψ z).im from hH)) this
  · exact fun hzC => hψ.2.2.2.1.2.mapsTo hzC

/-- **The non-real part of the traversal up to the relative time of `t`** is the Jordan image of the pocket visits
up to `t`: `γ([0, relTime t]) ∩ ℍ = ψ(η([0, t]) ∩ C)` (Aux. lemma 41's (GC2) and no visit inside a clock fibre). -/
theorem image_trav_inter_H (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    trav η C τ σ ψ '' Icc 0 (relTime η C τ σ t) ∩ H = ψ '' (η '' Icc 0 t ∩ C) := by
  have hL := hP.erase.clock_σ_pos
  have hℓt := hP.erase.clock_lt_clock_σ ht
  have hℓ0 := hP.erase.clock_nonneg ht.1
  rw [image_relCurve_Icc _ hL (relTime_nonneg hP ht), clockOf_relTime hP ht]
  -- the erased image lies in `C̄ ∖ {x₀}`
  have hE : ∀ v ∈ Icc 0 (pocketClock η C τ σ t), erasedPath η C τ σ v ∈ closure C \ {x₀} := fun v hv =>
    hP.erase.erasedPath_mem ⟨hv.1, hv.2.trans_lt hℓt⟩
  -- `η([0, fR(ℓ t)]) ∩ C = η([0, t]) ∩ C`
  have hfib : η '' Icc 0 (pocketFibre η C τ σ (pocketClock η C τ σ t)) ∩ C = η '' Icc 0 t ∩ C := by
    have htle : t ≤ pocketFibre η C τ σ (pocketClock η C τ σ t) := fibreRight_clock ⟨ht.1, ht.2.le⟩
    refine Subset.antisymm ?_ (inter_subset_inter_left _ (image_mono (Icc_subset_Icc_right htle)))
    rintro _ ⟨⟨t', ht', rfl⟩, hC'⟩
    refine ⟨⟨t', ⟨ht'.1, ?_⟩, rfl⟩, hC'⟩
    by_contra hlt
    rw [not_le] at hlt
    have hleft : pocketFibreLeft η C τ σ (pocketClock η C τ σ t) ≤ t :=
      fibreLeft_le ⟨ht.1, ht.2.le⟩ (min_le_left _ _)
    exact HOuter.notMem_of_mem_Ioc_fibre' hP.erase ⟨hℓ0, hℓt⟩ ⟨hleft.trans_lt hlt, ht'.2⟩ hC'
  have himg : erasedPath η C τ σ '' Icc 0 (pocketClock η C τ σ t) ∩ C = η '' Icc 0 t ∩ C := by
    rw [hP.erase.erasedPath_image_inter ⟨hℓ0, hℓt.le⟩, hfib]
  rw [← himg]
  ext w
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hwH⟩
    exact ⟨erasedPath η C τ σ v, ⟨⟨v, hv, rfl⟩, (jordan_mem_H_iff hP.jordan (hE v hv) hP.erase.isOpen).1 hwH⟩, rfl⟩
  · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hvC⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hP.jordan.2.2.2.1.2.mapsTo hvC⟩

/-- **The relative capacity reached at ambient time `t ∈ [τ, σ)`** is half the hitting capacity of the Jordan image
of the pocket visits up to `t`. -/
theorem relCap_eq_hcapHit (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    relCap η C τ σ ψ t = (WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C))).toReal / 2 := by
  have hγ := hP.driven
  have h0 := relTime_nonneg hP ht
  have hh : WholeField.hcapHit (trav η C τ σ ψ '' Icc 0 (relTime η C τ σ t)) =
      WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C)) := by
    refine hcapHit_congr_closure ?_
    have hsub : ψ '' (η '' Icc 0 t ∩ C) ⊆ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact hP.jordan.2.2.2.1.2.mapsTo hz.2
    rw [image_trav_inter_H hP ht, inter_eq_left.2 hsub]
  rw [relCap, PocketMeas.capClock_eq_hcapHit hγ h0, PocketMeas.image_nnPath _ h0, hh]

/-- The Jordan coordinate is continuous on the pocket. -/
theorem continuousOn_jordan (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) :
    ContinuousOn ψ C :=
  hP.jordan.1.mono fun _ hz => ⟨subset_closure hz, fun h => hP.erase.notMem_x (mem_singleton_iff.1 h ▸ hz)⟩

/-- **`T⁰(q)` through the relative capacity in ambient time** (live event): for `t ∈ [τ, σ)`,
`T⁰(q) ≤ t ↔ q ≤ c(t)`. -/
theorem ambTime0_le_iff (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) {t : ℝ} (ht : t ∈ Ico τ σ) :
    ambTime0 η C τ σ ψ q ≤ t ↔ q ≤ relCap η C τ σ ψ t := by
  have hγ := hP.driven
  have hL := hP.erase.clock_σ_pos
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec hq0 hq
  have hv := clockOf_mem_Ico hL hc0
  have h0 := relTime_nonneg hP ht
  have e1 : ambTime0 η C τ σ ψ q ≤ t ↔
      clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q) ≤ pocketClock η C τ σ t := by
    constructor
    · intro h
      rw [← clock_pocketFibreLeft' hP ⟨hv.1, hv.2.le⟩]
      exact hP.erase.monotone_clock h
    · exact fun h => fibreLeft_le ⟨ht.1, ht.2.le⟩ ((min_le_left _ _).trans h)
  rw [e1, ← clockOf_relTime hP ht, (strictMonoOn_clockOf hL).le_iff_le hc0 h0, relCap,
    ← (hγ.strictMonoOn_capClock).le_iff_le hc0 h0, hcq]

/-- On the live event the stop `T⁰(q)` lies in `[τ, σ)`. -/
theorem ambTime0_mem_Ico (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) : ambTime0 η C τ σ ψ q ∈ Ico τ σ := by
  have hγ := hP.driven
  have hL := hP.erase.clock_σ_pos
  obtain ⟨hc0, -⟩ := hγ.capInv_spec hq0 hq
  have hv := clockOf_mem_Ico hL hc0
  have hm := pocketFibreLeft_mem' hP (clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q))
  refine ⟨hm.1, lt_of_le_of_ne hm.2 fun h => ?_⟩
  have hc := clock_pocketFibreLeft' hP ⟨hv.1, hv.2.le⟩
  rw [show pocketFibreLeft η C τ σ (clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q)) = σ from h] at hc
  exact hv.2.ne hc.symm

theorem relCap_lt_capLife (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    ENNReal.ofReal (relCap η C τ σ ψ t) < capLife (trav η C τ σ ψ) :=
  (hP.driven).ofReal_capClock_lt (relTime_nonneg hP ht)

/-- Below the terminal capacity time some ambient time of `[τ, σ)` has relative capacity above `q`. -/
theorem exists_relCap_gt (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ)
    {q : ℝ} (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) :
    ∃ t ∈ Ico τ σ, q < relCap η C τ σ ψ t := by
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hq
  obtain ⟨htm, hrel⟩ := relTime_fibre_clockOf hP (u := (n : ℝ)) (Nat.cast_nonneg n)
  exact ⟨_, htm, by rw [relCap, hrel]; exact hn⟩

/-- **The live stop before an ambient time `s`** is decided by the relative capacity before `s`:
`q < capLife γ ∧ T⁰(q) ≤ s` iff `τ ≤ s < σ ∧ q ≤ c(s)`, or `σ ≤ s` and `q < c(t)` for some `t ∈ [τ, σ)`. -/
theorem live_and_ambTime0_le_iff (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (s : ℝ) :
    (ENNReal.ofReal q < capLife (trav η C τ σ ψ) ∧ ambTime0 η C τ σ ψ q ≤ s) ↔
      (τ ≤ s ∧ s < σ ∧ q ≤ relCap η C τ σ ψ s) ∨ (σ ≤ s ∧ ∃ t ∈ Ico τ σ, q < relCap η C τ σ ψ t) := by
  constructor
  · rintro ⟨hq, ha⟩
    have hm := ambTime0_mem_Ico hP hq0 hq
    rcases lt_or_ge s σ with hs | hs
    · exact Or.inl ⟨hm.1.trans ha, hs, (ambTime0_le_iff hP hq0 hq ⟨hm.1.trans ha, hs⟩).1 ha⟩
    · exact Or.inr ⟨hs, exists_relCap_gt hP hq⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨hs, t, ht, hlt⟩)
    · have hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ) :=
        (ENNReal.ofReal_le_ofReal h3).trans_lt (relCap_lt_capLife hP ⟨h1, h2⟩)
      exact ⟨hq, (ambTime0_le_iff hP hq0 hq ⟨h1, h2⟩).2 h3⟩
    · have hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ) :=
        (ENNReal.ofReal_le_ofReal hlt.le).trans_lt (relCap_lt_capLife hP ht)
      exact ⟨hq, (pocketFibreLeft_mem' hP _).2.trans hs⟩

/-! ### Regularity of the relative capacity in ambient time -/

theorem continuousOn_relTime (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) :
    ContinuousOn (relTime η C τ σ) (Ico τ σ) :=
  hP.erase.continuous_clock.continuousOn.div (continuousOn_const.sub hP.erase.continuous_clock.continuousOn)
    fun _ ht => (sub_pos.2 (hP.erase.clock_lt_clock_σ ht)).ne'

theorem monotoneOn_relTime (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) :
    MonotoneOn (relTime η C τ σ) (Ico τ σ) := fun _ _ _ hb hab =>
  div_le_div₀ (hP.erase.clock_nonneg hb.1) (hP.erase.monotone_clock hab) (sub_pos.2 (hP.erase.clock_lt_clock_σ hb))
    (sub_le_sub_left (hP.erase.monotone_clock hab) _)

theorem continuousOn_relCap (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) : ContinuousOn (relCap η C τ σ ψ) (Ico τ σ) :=
  (hP.driven).continuousOn_capClock.comp
    (continuousOn_relTime hP) fun _ ht => relTime_nonneg hP ht

theorem monotoneOn_relCap (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) : MonotoneOn (relCap η C τ σ ψ) (Ico τ σ) :=
    fun _ ha _ hb hab =>
  (hP.driven).strictMonoOn_capClock.monotoneOn
    (relTime_nonneg hP ha) (relTime_nonneg hP hb) (monotoneOn_relTime hP ha hb hab)

theorem relCap_τ (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) : relCap η C τ σ ψ τ = 0 := by
  rw [relCap, relTime, R7StopIn.IsErasurePocket.clock_τ, zero_div]
  exact (hP.driven).capClock_zero

/-- **The relative capacity at `s ∈ (τ, σ)` from rational earlier times**: `q ≤ c(s)` iff at every scale some
rational `p ∈ (τ, s)` has `c(p) > q − 1/(n+1)`. -/
theorem le_relCap_iff_rat (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q s : ℝ} (hs : s ∈ Ioo τ σ) :
    q ≤ relCap η C τ σ ψ s ↔
      ∀ n : ℕ, ∃ p : ℚ, τ < p ∧ (p : ℝ) < s ∧ q - 1 / ((n : ℝ) + 1) < relCap η C τ σ ψ p := by
  have hsI : s ∈ Ico τ σ := ⟨hs.1.le, hs.2⟩
  constructor
  · intro h n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hc := (continuousOn_relCap hP s hsI)
    have hev : ∀ᶠ t in 𝓝[Ico τ σ] s, relCap η C τ σ ψ s - 1 / ((n : ℝ) + 1) < relCap η C τ σ ψ t :=
      hc.eventually (lt_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show max τ (s - δ) < s from max_lt hs.1 (by linarith))
    have hpτ : τ < p := (le_max_left _ _).trans_lt hp1
    have hpm : (p : ℝ) ∈ ball s δ ∩ Ico τ σ := by
      refine ⟨?_, hpτ.le, hp2.trans hs.2⟩
      rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_right τ (s - δ)
      linarith
    exact ⟨p, hpτ, hp2, lt_of_le_of_lt (sub_le_sub_right h _) (hball hpm)⟩
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨p, hpτ, hps, hp⟩ := h n
    have := monotoneOn_relCap hP ⟨hpτ.le, hps.trans hs.2⟩ hsI hps.le
    linarith

/-- Some ambient time of `[τ, σ)` has relative capacity above `q` iff some rational one has. -/
theorem exists_relCap_gt_iff_rat (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {q : ℝ} :
    (∃ t ∈ Ico τ σ, q < relCap η C τ σ ψ t) ↔ ∃ p : ℚ, τ < p ∧ (p : ℝ) < σ ∧ q < relCap η C τ σ ψ p := by
  constructor
  · rintro ⟨t, ht, hlt⟩
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn ht.2
    exact ⟨p, ht.1.trans_lt hp1, hp2,
      hlt.trans_le (monotoneOn_relCap hP ht ⟨ht.1.trans hp1.le, hp2⟩ hp1.le)⟩
  · rintro ⟨p, hp1, hp2, hlt⟩
    exact ⟨p, ⟨hp1.le, hp2⟩, hlt⟩

/-! ### Prefix events through pocket visits -/

/-- **A prefix of the traversal up to a positive capacity time meets a closed set** iff at every scale the Jordan
coordinate of some pocket visit `η t ∈ C` of relative capacity `c(t) < r` is close to it. -/
theorem prefix_nonempty_iff_visit (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < capLife (trav η C τ σ ψ)) {Q : Set ℂ} (hQ : IsClosed Q) :
    (Q ∩ trav η C τ σ ψ '' Icc 0 (capInv (trav η C τ σ ψ) r)).Nonempty ↔
      ∀ m : ℕ, ∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCap η C τ σ ψ t < r ∧ ψ (η t) ∈ thickening (1 / ((m : ℝ) + 1)) Q := by
  have hγ := hP.driven
  have hL := hP.erase.clock_σ_pos
  rw [prefix_nonempty_iff_mem_H hγ hr0 hr hQ]
  refine forall_congr' fun m => ⟨?_, ?_⟩
  · rintro ⟨u, hu0, hur, huH, hut⟩
    obtain ⟨htm, hrel⟩ := relTime_fibre_clockOf hP hu0
    have hv := clockOf_mem_Ico hL hu0
    have hE := hP.erase.erasedPath_mem hv
    have hC : erasedPath η C τ σ (clockOf (pocketClock η C τ σ σ) u) ∈ C :=
      (jordan_mem_H_iff hP.jordan hE hP.erase.isOpen).1 huH
    exact ⟨_, hP.erase.nonneg.trans htm.1, hC, by rw [relCap, hrel]; exact hur, hut⟩
  · rintro ⟨t, ht0, htC, htr, htt⟩
    have htI := hP.erase.mem_visitSet ht0 htC
    obtain ⟨hu0, he⟩ := hP.erase.relTrav_of_mem_visitSet (ψ := ψ) htI
    have he' : trav η C τ σ ψ (relTime η C τ σ t) =
        ψ (η t) := he
    refine ⟨relTime η C τ σ t, hu0, htr, ?_, ?_⟩
    · rw [he']
      exact hP.jordan.2.2.2.1.2.mapsTo htC
    · rw [he']
      exact htt

/-- **The visit condition at rational times**: for an open set `O`, a pocket visit with relative capacity below
`r` and Jordan image in `O` exists iff a rational one does (the visit set is open). -/
theorem exists_visit_iff_rat (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {r : ℝ} {O : Set ℂ} (hO : IsOpen O) :
    (∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCap η C τ σ ψ t < r ∧ ψ (η t) ∈ O) ↔
      ∃ p : ℚ, 0 ≤ (p : ℝ) ∧ η p ∈ C ∧ relCap η C τ σ ψ p < r ∧ ψ (η p) ∈ O := by
  refine ⟨?_, fun ⟨p, h⟩ => ⟨p, h⟩⟩
  rintro ⟨t, ht0, htC, htr, htO⟩
  set I := visitSet η C τ σ with hI
  have hIo : IsOpen I := hP.erase.isOpen_visitSet
  have hIsub : I ⊆ Ico τ σ := fun t ht => ⟨ht.1.1.le, ht.1.2⟩
  have hηc : ContinuousOn η I := hP.trace.2.1.mono fun t ht => hP.erase.nonneg.trans ht.1.1.le
  have hψη : ContinuousOn (fun t => ψ (η t)) I :=
    (continuousOn_jordan hP).comp hηc fun t ht => ht.2
  have hU : IsOpen (I ∩ relCap η C τ σ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O) := by
    have h1 := ((continuousOn_relCap hP).mono hIsub).isOpen_inter_preimage hIo (isOpen_Iio (a := r))
    exact (hψη.mono inter_subset_left).isOpen_inter_preimage h1 hO
  have htU : t ∈ I ∩ relCap η C τ σ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O :=
    ⟨⟨hP.erase.mem_visitSet ht0 htC, htr⟩, htO⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htU
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show t - ε < t from by linarith)
  have hpU := hball (show (p : ℝ) ∈ ball t ε by
    rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    linarith)
  exact ⟨p, hP.erase.nonneg.trans (hIsub hpU.1.1).1, hpU.1.1.2, hpU.1.2, hpU.2⟩

open scoped Classical in
/-- **The relative capacity at `t ∈ [τ, σ)` from the rational pocket visits up to `t`** (junk value `0 ∉ ℍ`). -/
theorem relCap_eq_hcapHit_rat (hP : IsOuterPocket W η C x₀ y₀ τ σ ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    relCap η C τ σ ψ t = (WholeField.hcapHit (range fun p : ℚ =>
      if 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C then ψ (η p) else 0)).toReal / 2 := by
  rw [relCap_eq_hcapHit hP ht]
  congr 2
  refine hcapHit_congr_closure ?_
  have hCH := hP.subset_H
  have hA : ψ '' (η '' Icc 0 t ∩ C) ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hP.jordan.2.2.2.1.2.mapsTo hz.2
  have hB : (range fun p : ℚ => if 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C then ψ (η p) else 0) ∩ H ⊆
      ψ '' (η '' Icc 0 t ∩ C) := by
    rintro _ ⟨⟨p, rfl⟩, hpH⟩
    by_cases hp : 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C
    · simp only [hp, and_self, ↓reduceIte] at hpH ⊢
      exact ⟨η p, ⟨⟨p, ⟨hp.1, hp.2.1⟩, rfl⟩, hp.2.2⟩, rfl⟩
    · simp only [hp, ↓reduceIte] at hpH
      exact absurd hpH (by simp [QuantumZipper.H])
  rw [inter_eq_left.2 hA]
  refine Subset.antisymm ?_ (closure_mono hB)
  refine closure_minimal ?_ isClosed_closure
  rintro _ ⟨_, ⟨⟨t', ht', rfl⟩, htC⟩, rfl⟩
  -- `ψ ∘ η` is continuous at the visit time `t' > 0`, approached by rational visit times from the left
  have htI := hP.erase.mem_visitSet ht'.1 htC
  have ht'0 : 0 < t' := hP.erase.nonneg.trans_lt htI.1.1
  have hIo : IsOpen (visitSet η C τ σ) := hP.erase.isOpen_visitSet
  have hηc : ContinuousAt η t' :=
    (hP.trace.2.1 t' ht'0.le).continuousAt (Ici_mem_nhds ht'0)
  have hψc : ContinuousAt ψ (η t') := (continuousOn_jordan hP).continuousAt (hP.erase.isOpen.mem_nhds htC)
  rw [mem_closure_iff_nhds]
  intro N hN
  have hev : ∀ᶠ s in 𝓝 t', ψ (η s) ∈ N ∧ s ∈ visitSet η C τ σ :=
    ((hψc.comp hηc).eventually hN).and (hIo.mem_nhds htI)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show max (t' - δ) 0 < t' from max_lt (by linarith) ht'0)
  have hpd : dist (p : ℝ) t' < δ := by
    rw [Real.dist_eq, abs_of_neg (by linarith)]
    have := le_max_left (t' - δ) 0
    linarith
  obtain ⟨hpN, hpI⟩ := hball hpd
  have hp : 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C :=
    ⟨(le_max_right _ _).trans hp1.le, hp2.le.trans ht'.2, hpI.2⟩
  refine ⟨ψ (η p), hpN, ⟨⟨p, ?_⟩, hP.jordan.2.2.2.1.2.mapsTo hp.2.2⟩⟩
  simp only [hp, and_self, ↓reduceIte]

end Pocket

end InteractingSLE.Sec7.PocketStopMarked.Outer

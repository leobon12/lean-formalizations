/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedInf
import InteractingSLE.Spec.Sec7.HOuterMarkedStop

/-!
# The outer pocket opening at the flow seed: `T⁰(q)` through the relative capacity (pathwise part)

Packet PROVE-HOUTER. The port of PROVE-STRIPSYS43's `PocketStopMarkedPathInf.lean` from the reverse pocket at infinity
(`Sec6.IsReversePocketInf` with Aux. lemma 37's attachment constancy at infinity) to a mixed or outer pocket opening at
the flow seed: one realization `IsOuterPocketInf` bundles the erasure facts at infinity (`R7StopIn.IsErasurePocketInf`),
the counterflow's Loewner trace, `C ⊆ ℍ`, a Jordan coordinate at infinity and the driven relative traversal. Proofs are
STRIPSYS43's with the erasure API. Declarations in the sub-namespace `PocketStopMarked.Outer` (see `HOuterMarkedPath`).

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked.Outer

open QuantumZipper (H Hbar)
open PocketTraversal Lemma71C Sec6 PocketUnionPt PocketStopWallsFin

/-- **One realization of a mixed or outer pocket opening at the flow seed for the marked stop**: the erasure facts at
infinity, the counterflow's Loewner trace, `C ⊆ ℍ`, a Jordan coordinate at infinity and the driven relative
traversal. -/
structure IsOuterPocketInf (W : ℝ → ℝ) (η : ℝ → ℂ) (C : Set ℂ) (y₀ : ℂ) (τ : ℝ) (ψ : ℂ → ℂ) : Prop where
  erase : R7StopIn.IsErasurePocketInf η C y₀ τ
  trace : IsLoewnerTrace W η
  subset_H : C ⊆ H
  jordan : Sec6.IsJordanCoordInf C y₀ ψ
  driven : IsDrivenCurve (travInf η C τ ψ)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

theorem clock_pocketFibreLeftInf' (hP : IsOuterPocketInf W η C y₀ τ ψ) {v : ℝ}
    (hv : v ∈ Ico 0 (clockEnd η C τ)) : pocketClockInf η C τ (pocketFibreLeftInf η C τ v) = v := by
  obtain ⟨-, hva, hab⟩ := HOuter.pocketFibreLeftInf_props hP.erase hv
  refine le_antisymm ?_ hva
  calc pocketClockInf η C τ (pocketFibreLeftInf η C τ v) ≤ pocketClockInf η C τ (pocketFibreInf η C τ v) :=
        hP.erase.monotone_clock hab
    _ = v := hP.erase.clock_fibre hv

theorem le_ambTime0Inf' (hP : IsOuterPocketInf W η C y₀ τ ψ) (ψ' : ℂ → ℂ) (q : ℝ) :
    τ ≤ ambTime0Inf η C τ ψ' q :=
  (HOuter.pocketFibreLeftInf_props hP.erase (clockOf_mem_Ico hP.erase.clockEnd_pos (capInv_nonneg _ _))).1

theorem relTimeInf_nonneg (hP : IsOuterPocketInf W η C y₀ τ ψ)
    {t : ℝ} (ht : τ ≤ t) : 0 ≤ relTimeInf η C τ t :=
  div_nonneg (hP.erase.clock_nonneg ht) (sub_pos.2 (hP.erase.clock_lt_clockEnd ht)).le

theorem clockOf_relTimeInf (hP : IsOuterPocketInf W η C y₀ τ ψ)
    {t : ℝ} (ht : τ ≤ t) : clockOf (clockEnd η C τ) (relTimeInf η C τ t) = pocketClockInf η C τ t :=
  PocketLife.clockOf_div_sub (hP.erase.clockEnd_pos) (hP.erase.clock_lt_clockEnd ht)

theorem relTimeInf_fibre_clockOf (hP : IsOuterPocketInf W η C y₀ τ ψ) {u : ℝ} (hu : 0 ≤ u) :
    τ ≤ pocketFibreInf η C τ (clockOf (clockEnd η C τ) u) ∧
      relTimeInf η C τ (pocketFibreInf η C τ (clockOf (clockEnd η C τ) u)) = u := by
  have hL := hP.erase.clockEnd_pos
  have hv := clockOf_mem_Ico hL hu
  have hct := hP.erase.clock_fibre hv
  have htm := hP.erase.fibre_mem hv
  refine ⟨htm, (strictMonoOn_clockOf hL).injOn (relTimeInf_nonneg hP htm) hu ?_⟩
  rw [clockOf_relTimeInf hP htm, hct]

theorem jordanInf_mem_H_iff (hψ : IsJordanCoordInf C y₀ ψ) {z : ℂ} (hz : z ∈ closure C) (hC : IsOpen C) :
    ψ z ∈ H ↔ z ∈ C := by
  constructor
  · intro hH
    by_contra hzC
    have hfr : z ∈ frontier C := ⟨hz, by rwa [hC.interior_eq]⟩
    have := hψ.2.2.2.2.1 z hfr
    exact (ne_of_gt (show (0 : ℝ) < (ψ z).im from hH)) this
  · exact fun hzC => hψ.2.2.2.1.2.mapsTo hzC

/-- `t ≤ fR(ℓ t)` for `t ≥ τ` (junction at infinity). -/
theorem le_fibreInf_clock (hP : IsOuterPocketInf W η C y₀ τ ψ)
    {t : ℝ} (ht : τ ≤ t) : t ≤ pocketFibreInf η C τ (pocketClockInf η C τ t) := by
  obtain ⟨T, hτT, hvT⟩ := hP.erase.exists_clock_gt (hP.erase.clock_lt_clockEnd ht)
  have htT : t ≤ T := by
    by_contra h
    exact absurd (hP.erase.monotone_clock (not_le.1 h).le) (not_le.2 hvT)
  rw [hP.erase.fibre_eq_fibreRight_of_lt (hP.erase.clock_nonneg ht) hvT]
  exact fibreRight_clock ⟨ht, htT⟩

theorem image_travInf_inter_H (hP : IsOuterPocketInf W η C y₀ τ ψ) {t : ℝ} (ht : τ ≤ t) :
    travInf η C τ ψ '' Icc 0 (relTimeInf η C τ t) ∩ H = ψ '' (η '' Icc 0 t ∩ C) := by
  have hL := hP.erase.clockEnd_pos
  have hℓt := hP.erase.clock_lt_clockEnd ht
  have hℓ0 := hP.erase.clock_nonneg ht
  rw [image_relCurve_Icc _ hL (relTimeInf_nonneg hP ht), clockOf_relTimeInf hP ht]
  have hE : ∀ v ∈ Icc 0 (pocketClockInf η C τ t), erasedPathInf η C τ v ∈ closure C := fun v hv =>
    hP.erase.erasedPath_mem ⟨hv.1, hv.2.trans_lt hℓt⟩
  have hfib : η '' Icc 0 (pocketFibreInf η C τ (pocketClockInf η C τ t)) ∩ C = η '' Icc 0 t ∩ C := by
    have htle := le_fibreInf_clock hP ht
    refine Subset.antisymm ?_ (inter_subset_inter_left _ (image_mono (Icc_subset_Icc_right htle)))
    rintro _ ⟨⟨t', ht', rfl⟩, hC'⟩
    refine ⟨⟨t', ⟨ht'.1, ?_⟩, rfl⟩, hC'⟩
    by_contra hlt
    rw [not_le] at hlt
    have hleft : pocketFibreLeftInf η C τ (pocketClockInf η C τ t) ≤ t :=
      csInf_le ⟨τ, fun _ h => h.1⟩ ⟨ht, le_rfl⟩
    exact HOuter.notMem_of_mem_Ioc_fibreInf' hP.erase ⟨hℓ0, hℓt⟩ ⟨hleft.trans_lt hlt, ht'.2⟩ hC'
  have himg : erasedPathInf η C τ '' Icc 0 (pocketClockInf η C τ t) ∩ C = η '' Icc 0 t ∩ C := by
    rw [hP.erase.erasedPath_image_inter ⟨hℓ0, hℓt⟩, hfib]
  rw [← himg]
  ext w
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hwH⟩
    exact ⟨erasedPathInf η C τ v, ⟨⟨v, hv, rfl⟩, (jordanInf_mem_H_iff hP.jordan (hE v hv) hP.erase.isOpen).1 hwH⟩, rfl⟩
  · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hvC⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hP.jordan.2.2.2.1.2.mapsTo hvC⟩

theorem relCapInf_eq_hcapHit (hP : IsOuterPocketInf W η C y₀ τ ψ) {t : ℝ} (ht : τ ≤ t) :
    relCapInf η C τ ψ t = (WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C))).toReal / 2 := by
  have hγ := hP.driven
  have h0 := relTimeInf_nonneg hP ht
  have hh : WholeField.hcapHit (travInf η C τ ψ '' Icc 0 (relTimeInf η C τ t)) =
      WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C)) := by
    refine hcapHit_congr_closure ?_
    have hsub : ψ '' (η '' Icc 0 t ∩ C) ⊆ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact hP.jordan.2.2.2.1.2.mapsTo hz.2
    rw [image_travInf_inter_H hP ht, inter_eq_left.2 hsub]
  rw [relCapInf, PocketMeas.capClock_eq_hcapHit hγ h0, PocketMeas.image_nnPath _ h0, hh]

/-- **`T⁰(q)` through the relative capacity in ambient time** (junction at infinity, live event). -/
theorem ambTime0Inf_le_iff (hP : IsOuterPocketInf W η C y₀ τ ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ))
    {t : ℝ} (ht : τ ≤ t) : ambTime0Inf η C τ ψ q ≤ t ↔ q ≤ relCapInf η C τ ψ t := by
  have hγ := hP.driven
  have hL := hP.erase.clockEnd_pos
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec hq0 hq
  have hv := clockOf_mem_Ico hL hc0
  have h0 := relTimeInf_nonneg hP ht
  have e1 : ambTime0Inf η C τ ψ q ≤ t ↔
      clockOf (clockEnd η C τ) (capInv (travInf η C τ ψ) q) ≤ pocketClockInf η C τ t := by
    constructor
    · intro h
      rw [← clock_pocketFibreLeftInf' hP hv]
      exact hP.erase.monotone_clock h
    · exact fun h => csInf_le ⟨τ, fun _ h' => h'.1⟩ ⟨ht, h⟩
  rw [e1, ← clockOf_relTimeInf hP ht, (strictMonoOn_clockOf hL).le_iff_le hc0 h0, relCapInf,
    ← (hγ.strictMonoOn_capClock).le_iff_le hc0 h0, hcq]

theorem relCapInf_lt_capLife (hP : IsOuterPocketInf W η C y₀ τ ψ) {t : ℝ} (ht : τ ≤ t) :
    ENNReal.ofReal (relCapInf η C τ ψ t) < capLife (travInf η C τ ψ) :=
  (hP.driven).ofReal_capClock_lt (relTimeInf_nonneg hP ht)

/-- **The live stop before `s`** (junction at infinity): `q < capLife γ ∧ T⁰(q) ≤ s ↔ τ ≤ s ∧ q ≤ c(s)`. -/
theorem live_and_ambTime0Inf_le_iff (hP : IsOuterPocketInf W η C y₀ τ ψ) {q : ℝ} (hq0 : 0 ≤ q) (s : ℝ) :
    (ENNReal.ofReal q < capLife (travInf η C τ ψ) ∧ ambTime0Inf η C τ ψ q ≤ s) ↔
      τ ≤ s ∧ q ≤ relCapInf η C τ ψ s := by
  constructor
  · rintro ⟨hq, ha⟩
    have hτ := le_ambTime0Inf' hP ψ q
    exact ⟨hτ.trans ha, (ambTime0Inf_le_iff hP hq0 hq (hτ.trans ha)).1 ha⟩
  · rintro ⟨h1, h2⟩
    have hq : ENNReal.ofReal q < capLife (travInf η C τ ψ) :=
      (ENNReal.ofReal_le_ofReal h2).trans_lt (relCapInf_lt_capLife hP h1)
    exact ⟨hq, (ambTime0Inf_le_iff hP hq0 hq h1).2 h2⟩

theorem continuousOn_relTimeInf (hP : IsOuterPocketInf W η C y₀ τ ψ) : ContinuousOn (relTimeInf η C τ) (Ici τ) :=
  hP.erase.continuous_clock.continuousOn.div (continuousOn_const.sub hP.erase.continuous_clock.continuousOn)
    fun _ ht => (sub_pos.2 (hP.erase.clock_lt_clockEnd ht)).ne'

theorem monotoneOn_relTimeInf (hP : IsOuterPocketInf W η C y₀ τ ψ) : MonotoneOn (relTimeInf η C τ) (Ici τ) :=
    fun _ _ _ hb hab =>
  div_le_div₀ (hP.erase.clock_nonneg hb) (hP.erase.monotone_clock hab) (sub_pos.2 (hP.erase.clock_lt_clockEnd hb))
    (sub_le_sub_left (hP.erase.monotone_clock hab) _)

theorem continuousOn_relCapInf (hP : IsOuterPocketInf W η C y₀ τ ψ) : ContinuousOn (relCapInf η C τ ψ) (Ici τ) :=
  (hP.driven).continuousOn_capClock.comp
    (continuousOn_relTimeInf hP) fun _ ht => relTimeInf_nonneg hP ht

theorem monotoneOn_relCapInf (hP : IsOuterPocketInf W η C y₀ τ ψ) : MonotoneOn (relCapInf η C τ ψ) (Ici τ) :=
    fun _ ha _ hb hab =>
  (hP.driven).strictMonoOn_capClock.monotoneOn
    (relTimeInf_nonneg hP ha) (relTimeInf_nonneg hP hb) (monotoneOn_relTimeInf hP ha hb hab)

theorem relCapInf_τ (hP : IsOuterPocketInf W η C y₀ τ ψ) : relCapInf η C τ ψ τ = 0 := by
  rw [relCapInf, relTimeInf, R7StopIn.IsErasurePocketInf.clock_τ, zero_div]
  exact (hP.driven).capClock_zero

theorem le_relCapInf_iff_rat (hP : IsOuterPocketInf W η C y₀ τ ψ) {q s : ℝ} (hs : τ < s) :
    q ≤ relCapInf η C τ ψ s ↔
      ∀ n : ℕ, ∃ p : ℚ, τ < p ∧ (p : ℝ) < s ∧ q - 1 / ((n : ℝ) + 1) < relCapInf η C τ ψ p := by
  have hsI : s ∈ Ici τ := hs.le
  constructor
  · intro h n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hc := (continuousOn_relCapInf hP s hsI)
    have hev : ∀ᶠ t in 𝓝[Ici τ] s, relCapInf η C τ ψ s - 1 / ((n : ℝ) + 1) < relCapInf η C τ ψ t :=
      hc.eventually (lt_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hev
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show max τ (s - δ) < s from max_lt hs (by linarith))
    have hpτ : τ < p := (le_max_left _ _).trans_lt hp1
    have hpm : (p : ℝ) ∈ ball s δ ∩ Ici τ := by
      refine ⟨?_, hpτ.le⟩
      rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
      have := le_max_right τ (s - δ)
      linarith
    exact ⟨p, hpτ, hp2, lt_of_le_of_lt (sub_le_sub_right h _) (hball hpm)⟩
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨p, hpτ, hps, hp⟩ := h n
    have := monotoneOn_relCapInf hP (show (p : ℝ) ∈ Ici τ from hpτ.le) hsI hps.le
    linarith

theorem prefix_nonempty_iff_visitInf (hP : IsOuterPocketInf W η C y₀ τ ψ) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < capLife (travInf η C τ ψ)) {Q : Set ℂ} (hQ : IsClosed Q) :
    (Q ∩ travInf η C τ ψ '' Icc 0 (capInv (travInf η C τ ψ) r)).Nonempty ↔
      ∀ m : ℕ, ∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCapInf η C τ ψ t < r ∧ ψ (η t) ∈ thickening (1 / ((m : ℝ) + 1)) Q := by
  have hγ := hP.driven
  have hL := hP.erase.clockEnd_pos
  rw [prefix_nonempty_iff_mem_H hγ hr0 hr hQ]
  refine forall_congr' fun m => ⟨?_, ?_⟩
  · rintro ⟨u, hu0, hur, huH, hut⟩
    obtain ⟨htm, hrel⟩ := relTimeInf_fibre_clockOf hP hu0
    have hv := clockOf_mem_Ico hL hu0
    have hE := hP.erase.erasedPath_mem hv
    have hC : erasedPathInf η C τ (clockOf (clockEnd η C τ) u) ∈ C :=
      (jordanInf_mem_H_iff hP.jordan hE hP.erase.isOpen).1 huH
    exact ⟨_, hP.erase.nonneg.trans htm, hC, by rw [relCapInf, hrel]; exact hur, hut⟩
  · rintro ⟨t, ht0, htC, htr, htt⟩
    have htI := hP.erase.mem_visitSet ht0 htC
    obtain ⟨hu0, he⟩ := hP.erase.relTravInf_of_mem_visitSet (ψ := ψ) htI
    have he' : travInf η C τ ψ (relTimeInf η C τ t) = ψ (η t) := he
    refine ⟨relTimeInf η C τ t, hu0, htr, ?_, ?_⟩
    · rw [he']
      exact hP.jordan.2.2.2.1.2.mapsTo htC
    · rw [he']
      exact htt

theorem exists_visitInf_iff_rat (hP : IsOuterPocketInf W η C y₀ τ ψ) {r : ℝ} {O : Set ℂ} (hO : IsOpen O) :
    (∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCapInf η C τ ψ t < r ∧ ψ (η t) ∈ O) ↔
      ∃ p : ℚ, 0 ≤ (p : ℝ) ∧ η p ∈ C ∧ relCapInf η C τ ψ p < r ∧ ψ (η p) ∈ O := by
  refine ⟨?_, fun ⟨p, h⟩ => ⟨p, h⟩⟩
  rintro ⟨t, ht0, htC, htr, htO⟩
  set I := visitSetInf η C τ with hI
  have hIo : IsOpen I := hP.erase.isOpen_visitSet
  have hIsub : I ⊆ Ici τ := fun t ht => (show τ < t from ht.1).le
  have hηc : ContinuousOn η I := hP.trace.2.1.mono fun t ht => hP.erase.nonneg.trans (show τ < t from ht.1).le
  have hψη : ContinuousOn (fun t => ψ (η t)) I :=
    (hP.jordan.1.mono subset_closure).comp hηc fun t ht => ht.2
  have hU : IsOpen (I ∩ relCapInf η C τ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O) := by
    have h1 := ((continuousOn_relCapInf hP).mono hIsub).isOpen_inter_preimage hIo (isOpen_Iio (a := r))
    exact (hψη.mono inter_subset_left).isOpen_inter_preimage h1 hO
  have htU : t ∈ I ∩ relCapInf η C τ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O :=
    ⟨⟨hP.erase.mem_visitSet ht0 htC, htr⟩, htO⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htU
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show t - ε < t from by linarith)
  have hpU := hball (show (p : ℝ) ∈ ball t ε by
    rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    linarith)
  exact ⟨p, hP.erase.nonneg.trans (hIsub hpU.1.1), hpU.1.1.2, hpU.1.2, hpU.2⟩

open scoped Classical in
theorem relCapInf_eq_hcapHit_rat (hP : IsOuterPocketInf W η C y₀ τ ψ) {t : ℝ} (ht : τ ≤ t) :
    relCapInf η C τ ψ t = (WholeField.hcapHit (range fun p : ℚ =>
      if 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C then ψ (η p) else 0)).toReal / 2 := by
  rw [relCapInf_eq_hcapHit hP ht]
  congr 2
  refine hcapHit_congr_closure ?_
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
  have htI := hP.erase.mem_visitSet ht'.1 htC
  have ht'0 : 0 < t' := hP.erase.nonneg.trans_lt htI.1
  have hIo : IsOpen (visitSetInf η C τ) := hP.erase.isOpen_visitSet
  have hηc : ContinuousAt η t' := (hP.trace.2.1 t' ht'0.le).continuousAt (Ici_mem_nhds ht'0)
  have hψc : ContinuousAt ψ (η t') :=
    ((hP.jordan.1.mono subset_closure) (η t') htC).continuousAt (hP.erase.isOpen.mem_nhds htC)
  rw [mem_closure_iff_nhds]
  intro N hN
  have hev : ∀ᶠ s in 𝓝 t', ψ (η s) ∈ N ∧ s ∈ visitSetInf η C τ :=
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


end InteractingSLE.Sec7.PocketStopMarked.Outer

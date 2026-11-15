/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopMarkedPath

/-!
# The pocket's stop `T⁰(q)` through the relative capacity in ambient time — pocket opening at the flow seed

Packet PROVE-STRIPSYS43. The analogue of `PocketStopMarkedPath.lean` for the change pocket opening at the flow seed
(the junction at infinity, `IsReversePocketInf`): there is no closing time, every time `t ≥ τ` has pocket visits ahead
(`clock_lt_clockEnd`), and the relative capacity reached at ambient time `t ≥ τ` is
`c(t) = capClock γ (ℓ t / (L − ℓ t))`, `L = ℓ(∞)` (`relCapInf`).

* **`relCapInf_eq_hcapHit_rat`**: `2 c(t)` is the hitting capacity of the Jordan images of the rational pocket visits
  up to `t`;
* **`live_and_ambTime0Inf_le_iff`**: `q < capLife γ ∧ T⁰(q) ≤ s ↔ τ ≤ s ∧ q ≤ c(s)`;
* **`le_relCapInf_iff_rat`**, **`prefix_nonempty_iff_visitInf`**, **`exists_visitInf_iff_rat`**: the rational forms.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked

open QuantumZipper (H Hbar)
open PocketTraversal Lemma71C Sec6 PocketUnionPt PocketStopWallsFin

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ} {ψ : ℂ → ℂ}

/-- The erased traversal of the pocket opening at the flow seed in the coordinate `ψ`. -/
abbrev travInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (ψ : ℂ → ℂ) : ℝ → ℂ :=
  relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ)

/-- The relative parameter `ℓ t / (L − ℓ t)` reached at ambient time `t` (junction at infinity). -/
def relTimeInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (t : ℝ) : ℝ :=
  pocketClockInf η C τ t / (clockEnd η C τ - pocketClockInf η C τ t)

/-- **The relative capacity reached at ambient time `t`** (junction at infinity). -/
def relCapInf (η : ℝ → ℂ) (C : Set ℂ) (τ : ℝ) (ψ : ℂ → ℂ) (t : ℝ) : ℝ :=
  capClock (travInf η C τ ψ) (relTimeInf η C τ t)

theorem relTimeInf_nonneg (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    {t : ℝ} (ht : τ ≤ t) : 0 ≤ relTimeInf η C τ t :=
  div_nonneg (hP.clock_nonneg ht) (sub_pos.2 (hP.clock_lt_clockEnd hAC ht)).le

theorem clockOf_relTimeInf (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    {t : ℝ} (ht : τ ≤ t) : clockOf (clockEnd η C τ) (relTimeInf η C τ t) = pocketClockInf η C τ t :=
  PocketLife.clockOf_div_sub (hP.clockEnd_pos hAC) (hP.clock_lt_clockEnd hAC ht)

theorem relTimeInf_fibre_clockOf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) {u : ℝ} (hu : 0 ≤ u) :
    τ ≤ pocketFibreInf η C τ (clockOf (clockEnd η C τ) u) ∧
      relTimeInf η C τ (pocketFibreInf η C τ (clockOf (clockEnd η C τ) u)) = u := by
  have hL := hP.clockEnd_pos hAC
  have hv := clockOf_mem_Ico hL hu
  have hct := hP.clock_fibre hv
  have htm := hP.fibre_mem hv
  refine ⟨htm, (strictMonoOn_clockOf hL).injOn (relTimeInf_nonneg hP hAC htm) hu ?_⟩
  rw [clockOf_relTimeInf hP hAC htm, hct]

theorem jordanInf_mem_H_iff (hψ : IsJordanCoordInf C (α₁ 0) ψ) {z : ℂ} (hz : z ∈ closure C) (hC : IsOpen C) :
    ψ z ∈ H ↔ z ∈ C := by
  constructor
  · intro hH
    by_contra hzC
    have hfr : z ∈ frontier C := ⟨hz, by rwa [hC.interior_eq]⟩
    have := hψ.2.2.2.2.1 z hfr
    exact (ne_of_gt (show (0 : ℝ) < (ψ z).im from hH)) this
  · exact fun hzC => hψ.2.2.2.1.2.mapsTo hzC

/-- `t ≤ fR(ℓ t)` for `t ≥ τ` (junction at infinity). -/
theorem le_fibreInf_clock (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    {t : ℝ} (ht : τ ≤ t) : t ≤ pocketFibreInf η C τ (pocketClockInf η C τ t) := by
  obtain ⟨T, hτT, hvT⟩ := hP.exists_clock_gt (hP.clock_lt_clockEnd hAC ht)
  have htT : t ≤ T := by
    by_contra h
    exact absurd (hP.monotone_clock (not_le.1 h).le) (not_le.2 hvT)
  rw [hP.fibre_eq_fibreRight_of_lt (hP.clock_nonneg ht) hvT]
  exact fibreRight_clock ⟨ht, htT⟩

theorem image_travInf_inter_H (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {t : ℝ} (ht : τ ≤ t) :
    travInf η C τ ψ '' Icc 0 (relTimeInf η C τ t) ∩ H = ψ '' (η '' Icc 0 t ∩ C) := by
  have hL := hP.clockEnd_pos hAC
  have hℓt := hP.clock_lt_clockEnd hAC ht
  have hℓ0 := hP.clock_nonneg ht
  rw [image_relCurve_Icc _ hL (relTimeInf_nonneg hP hAC ht), clockOf_relTimeInf hP hAC ht]
  have hE : ∀ v ∈ Icc 0 (pocketClockInf η C τ t), erasedPathInf η C τ v ∈ closure C := fun v hv =>
    hP.erasedPath_mem ⟨hv.1, hv.2.trans_lt hℓt⟩
  have hfib : η '' Icc 0 (pocketFibreInf η C τ (pocketClockInf η C τ t)) ∩ C = η '' Icc 0 t ∩ C := by
    have htle := le_fibreInf_clock hP hAC ht
    refine Subset.antisymm ?_ (inter_subset_inter_left _ (image_mono (Icc_subset_Icc_right htle)))
    rintro _ ⟨⟨t', ht', rfl⟩, hC'⟩
    refine ⟨⟨t', ⟨ht'.1, ?_⟩, rfl⟩, hC'⟩
    by_contra hlt
    rw [not_le] at hlt
    have hleft : pocketFibreLeftInf η C τ (pocketClockInf η C τ t) ≤ t :=
      csInf_le ⟨τ, fun _ h => h.1⟩ ⟨ht, le_rfl⟩
    exact notMem_of_mem_Ioc_fibreInf hP ⟨hℓ0, hℓt⟩ ⟨hleft.trans_lt hlt, ht'.2⟩ hC'
  have himg : erasedPathInf η C τ '' Icc 0 (pocketClockInf η C τ t) ∩ C = η '' Icc 0 t ∩ C := by
    rw [hP.erasedPath_image_inter ⟨hℓ0, hℓt⟩, hfib]
  rw [← himg]
  ext w
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hwH⟩
    exact ⟨erasedPathInf η C τ v, ⟨⟨v, hv, rfl⟩, (jordanInf_mem_H_iff hψ (hE v hv) hP.isOpen).1 hwH⟩, rfl⟩
  · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hvC⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hψ.2.2.2.1.2.mapsTo hvC⟩

theorem relCapInf_eq_hcapHit (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {t : ℝ} (ht : τ ≤ t) :
    relCapInf η C τ ψ t = (WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C))).toReal / 2 := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  have h0 := relTimeInf_nonneg hP hAC ht
  have hh : WholeField.hcapHit (travInf η C τ ψ '' Icc 0 (relTimeInf η C τ t)) =
      WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C)) := by
    refine hcapHit_congr_closure ?_
    have hsub : ψ '' (η '' Icc 0 t ∩ C) ⊆ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact hψ.2.2.2.1.2.mapsTo hz.2
    rw [image_travInf_inter_H hP hAC hψ ht, inter_eq_left.2 hsub]
  rw [relCapInf, PocketMeas.capClock_eq_hcapHit hγ h0, PocketMeas.image_nnPath _ h0, hh]

/-- **`T⁰(q)` through the relative capacity in ambient time** (junction at infinity, live event). -/
theorem ambTime0Inf_le_iff (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {q : ℝ} (hq0 : 0 ≤ q) (hq : ENNReal.ofReal q < capLife (travInf η C τ ψ))
    {t : ℝ} (ht : τ ≤ t) : ambTime0Inf η C τ ψ q ≤ t ↔ q ≤ relCapInf η C τ ψ t := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  have hL := hP.clockEnd_pos hAC
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec hq0 hq
  have hv := clockOf_mem_Ico hL hc0
  have h0 := relTimeInf_nonneg hP hAC ht
  have e1 : ambTime0Inf η C τ ψ q ≤ t ↔
      clockOf (clockEnd η C τ) (capInv (travInf η C τ ψ) q) ≤ pocketClockInf η C τ t := by
    constructor
    · intro h
      rw [← clock_pocketFibreLeftInf hP hv]
      exact hP.monotone_clock h
    · exact fun h => csInf_le ⟨τ, fun _ h' => h'.1⟩ ⟨ht, h⟩
  rw [e1, ← clockOf_relTimeInf hP hAC ht, (strictMonoOn_clockOf hL).le_iff_le hc0 h0, relCapInf,
    ← (hγ.strictMonoOn_capClock).le_iff_le hc0 h0, hcq]

theorem relCapInf_lt_capLife (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {t : ℝ} (ht : τ ≤ t) :
    ENNReal.ofReal (relCapInf η C τ ψ t) < capLife (travInf η C τ ψ) :=
  (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ).ofReal_capClock_lt (relTimeInf_nonneg hP hAC ht)

/-- **The live stop before `s`** (junction at infinity): `q < capLife γ ∧ T⁰(q) ≤ s ↔ τ ≤ s ∧ q ≤ c(s)`. -/
theorem live_and_ambTime0Inf_le_iff (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {q : ℝ} (hq0 : 0 ≤ q) (s : ℝ) :
    (ENNReal.ofReal q < capLife (travInf η C τ ψ) ∧ ambTime0Inf η C τ ψ q ≤ s) ↔
      τ ≤ s ∧ q ≤ relCapInf η C τ ψ s := by
  constructor
  · rintro ⟨hq, ha⟩
    have hτ := le_ambTime0Inf hP hAC ψ q
    exact ⟨hτ.trans ha, (ambTime0Inf_le_iff hP hAC hψ hq0 hq (hτ.trans ha)).1 ha⟩
  · rintro ⟨h1, h2⟩
    have hq : ENNReal.ofReal q < capLife (travInf η C τ ψ) :=
      (ENNReal.ofReal_le_ofReal h2).trans_lt (relCapInf_lt_capLife hP hAC hψ h1)
    exact ⟨hq, (ambTime0Inf_le_iff hP hAC hψ hq0 hq h1).2 h2⟩

theorem continuousOn_relTimeInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) : ContinuousOn (relTimeInf η C τ) (Ici τ) :=
  hP.continuous_clock.continuousOn.div (continuousOn_const.sub hP.continuous_clock.continuousOn)
    fun _ ht => (sub_pos.2 (hP.clock_lt_clockEnd hAC ht)).ne'

theorem monotoneOn_relTimeInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) : MonotoneOn (relTimeInf η C τ) (Ici τ) := fun _ _ _ hb hab =>
  div_le_div₀ (hP.clock_nonneg hb) (hP.monotone_clock hab) (sub_pos.2 (hP.clock_lt_clockEnd hAC hb))
    (sub_le_sub_left (hP.monotone_clock hab) _)

theorem continuousOn_relCapInf (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) : ContinuousOn (relCapInf η C τ ψ) (Ici τ) :=
  (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ).continuousOn_capClock.comp
    (continuousOn_relTimeInf hP hAC) fun _ ht => relTimeInf_nonneg hP hAC ht

theorem monotoneOn_relCapInf (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) : MonotoneOn (relCapInf η C τ ψ) (Ici τ) := fun _ ha _ hb hab =>
  (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ).strictMonoOn_capClock.monotoneOn
    (relTimeInf_nonneg hP hAC ha) (relTimeInf_nonneg hP hAC hb) (monotoneOn_relTimeInf hP hAC ha hb hab)

theorem relCapInf_τ (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) : relCapInf η C τ ψ τ = 0 := by
  rw [relCapInf, relTimeInf, IsReversePocketInf.clock_τ, zero_div]
  exact (isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ).capClock_zero

theorem le_relCapInf_iff_rat (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {q s : ℝ} (hs : τ < s) :
    q ≤ relCapInf η C τ ψ s ↔
      ∀ n : ℕ, ∃ p : ℚ, τ < p ∧ (p : ℝ) < s ∧ q - 1 / ((n : ℝ) + 1) < relCapInf η C τ ψ p := by
  have hsI : s ∈ Ici τ := hs.le
  constructor
  · intro h n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hc := (continuousOn_relCapInf hP hAC hψ s hsI)
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
    have := monotoneOn_relCapInf hP hAC hψ (show (p : ℝ) ∈ Ici τ from hpτ.le) hsI hps.le
    linarith

theorem prefix_nonempty_iff_visitInf (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < capLife (travInf η C τ ψ)) {Q : Set ℂ} (hQ : IsClosed Q) :
    (Q ∩ travInf η C τ ψ '' Icc 0 (capInv (travInf η C τ ψ) r)).Nonempty ↔
      ∀ m : ℕ, ∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCapInf η C τ ψ t < r ∧ ψ (η t) ∈ thickening (1 / ((m : ℝ) + 1)) Q := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ
  have hL := hP.clockEnd_pos hAC
  rw [prefix_nonempty_iff_mem_H hγ hr0 hr hQ]
  refine forall_congr' fun m => ⟨?_, ?_⟩
  · rintro ⟨u, hu0, hur, huH, hut⟩
    obtain ⟨htm, hrel⟩ := relTimeInf_fibre_clockOf hP hAC hu0
    have hv := clockOf_mem_Ico hL hu0
    have hE := hP.erasedPath_mem hv
    have hC : erasedPathInf η C τ (clockOf (clockEnd η C τ) u) ∈ C :=
      (jordanInf_mem_H_iff hψ hE hP.isOpen).1 huH
    exact ⟨_, hP.nonneg.trans htm, hC, by rw [relCapInf, hrel]; exact hur, hut⟩
  · rintro ⟨t, ht0, htC, htr, htt⟩
    have htI := hP.mem_visitSet ht0 htC
    obtain ⟨hu0, he⟩ := PocketLife.relCurve_of_mem_visitSetInf (ψ := ψ) hP hAC htI
    have he' : relCurve (fun v => ψ (erasedPathInf η C τ v)) (clockEnd η C τ) (relTimeInf η C τ t) = ψ (η t) := he
    refine ⟨relTimeInf η C τ t, hu0, htr, ?_, ?_⟩
    · rw [he']
      exact hψ.2.2.2.1.2.mapsTo htC
    · rw [he']
      exact htt

theorem exists_visitInf_iff_rat (hP : IsReversePocketInf W η C α₁ α₂ τ) (hAC : AttachmentConstancyInf η C α₁ α₂ τ)
    (hψ : IsJordanCoordInf C (α₁ 0) ψ) {r : ℝ} {O : Set ℂ} (hO : IsOpen O) :
    (∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCapInf η C τ ψ t < r ∧ ψ (η t) ∈ O) ↔
      ∃ p : ℚ, 0 ≤ (p : ℝ) ∧ η p ∈ C ∧ relCapInf η C τ ψ p < r ∧ ψ (η p) ∈ O := by
  refine ⟨?_, fun ⟨p, h⟩ => ⟨p, h⟩⟩
  rintro ⟨t, ht0, htC, htr, htO⟩
  set I := visitSetInf η C τ with hI
  have hIo : IsOpen I := hP.isOpen_visitSet
  have hIsub : I ⊆ Ici τ := fun t ht => (show τ < t from ht.1).le
  have hηc : ContinuousOn η I := hP.trace.2.1.mono fun t ht => hP.nonneg.trans (show τ < t from ht.1).le
  have hψη : ContinuousOn (fun t => ψ (η t)) I :=
    (hψ.1.mono subset_closure).comp hηc fun t ht => ht.2
  have hU : IsOpen (I ∩ relCapInf η C τ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O) := by
    have h1 := ((continuousOn_relCapInf hP hAC hψ).mono hIsub).isOpen_inter_preimage hIo (isOpen_Iio (a := r))
    exact (hψη.mono inter_subset_left).isOpen_inter_preimage h1 hO
  have htU : t ∈ I ∩ relCapInf η C τ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O :=
    ⟨⟨hP.mem_visitSet ht0 htC, htr⟩, htO⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htU
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show t - ε < t from by linarith)
  have hpU := hball (show (p : ℝ) ∈ ball t ε by
    rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    linarith)
  exact ⟨p, hP.nonneg.trans (hIsub hpU.1.1), hpU.1.1.2, hpU.1.2, hpU.2⟩

open scoped Classical in
theorem relCapInf_eq_hcapHit_rat (hP : IsReversePocketInf W η C α₁ α₂ τ)
    (hAC : AttachmentConstancyInf η C α₁ α₂ τ) (hψ : IsJordanCoordInf C (α₁ 0) ψ) {t : ℝ} (ht : τ ≤ t) :
    relCapInf η C τ ψ t = (WholeField.hcapHit (range fun p : ℚ =>
      if 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C then ψ (η p) else 0)).toReal / 2 := by
  rw [relCapInf_eq_hcapHit hP hAC hψ ht]
  congr 2
  refine hcapHit_congr_closure ?_
  have hA : ψ '' (η '' Icc 0 t ∩ C) ⊆ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact hψ.2.2.2.1.2.mapsTo hz.2
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
  have htI := hP.mem_visitSet ht'.1 htC
  have ht'0 : 0 < t' := hP.nonneg.trans_lt htI.1
  have hIo : IsOpen (visitSetInf η C τ) := hP.isOpen_visitSet
  have hηc : ContinuousAt η t' := (hP.trace.2.1 t' ht'0.le).continuousAt (Ici_mem_nhds ht'0)
  have hψc : ContinuousAt ψ (η t') :=
    ((hψ.1.mono subset_closure) (η t') htC).continuousAt (hP.isOpen.mem_nhds htC)
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
  refine ⟨ψ (η p), hpN, ⟨⟨p, ?_⟩, hψ.2.2.2.1.2.mapsTo hp.2.2⟩⟩
  simp only [hp, and_self, ↓reduceIte]

end InteractingSLE.Sec7.PocketStopMarked

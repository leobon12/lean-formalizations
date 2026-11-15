/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsFinLeft
import InteractingSLE.Spec.Sec7.PocketLife
import InteractingSLE.Spec.Sec7.PocketMeas

/-!
# The pocket's stop `T⁰(q)` through the relative capacity in ambient time (pathwise part)

Packet PROVE-STRIPSYS43 (PROVE-STRIPSYS41 §5.1, ruling R67). Specification §7.4, proof of Aux. lemma 125
(`source/spec/p385-432.md` L213–L224, p. 396): `T⁰(q) = inf {t ≥ τ : Q(t) ≥ q}` with `Q(t)` the relative capacity of
the pocket's part of the counterflow hull at ambient time `t`.

For one realization of the bounded change pocket traversed by the counterflow (`IsCfPocketConfig`) with a Jordan
coordinate `ψ`, write `ℓ` for the erasure clock on `[τ, S]` (`τ`, `S` the first visits of `m(y₀)`, `m(x₀)`), `L = ℓ S`,
`γ` for the erased traversal (`cfTraversal`), and `c(t) = capClock γ (ℓ t / (L − ℓ t))` for the relative capacity
reached at ambient time `t ∈ [τ, S)` (`relCap`). This file proves, deterministically:

* `fillH_union_eq_of_inter_H_empty`, **`exists_mem_H_of_lt`**: a driven curve is not real-valued on any
  nondegenerate interval (its capacity clock would be constant there);
* **`prefix_nonempty_iff_mem_H`**: a prefix up to a positive capacity time meets a closed set iff, at every scale,
  some non-real point of the curve before that capacity time is close to it;
* **`relCap_eq_hcapHit`**: `2 c(t) = hcap(ψ(η([0, t]) ∩ C))` (through Aux. lemma 41's (GC2), `erasedPath_image_inter`,
  and the absence of pocket visits inside a clock fibre);
* **`ambTime0_le_iff`**: on the live event `q < capLife γ`, `T⁰(q) ≤ t ↔ q ≤ c(t)` for `t ∈ [τ, S)`;
* **`live_and_ambTime0_le_iff`**: `q < capLife γ ∧ T⁰(q) ≤ s` iff `τ ≤ s < S ∧ q ≤ c(s)` or `S ≤ s` and `q < c(t)`
  for some `t ∈ [τ, S)` — every ambient time before `S` still has pocket visits ahead (`clock_lt_clock_σ`), so the
  liveness at the stop is decided by the past;
* **`prefix_nonempty_iff_visit`**: a prefix of the traversal up to a positive capacity time `r'` meets a closed set
  iff, at every scale, the Jordan coordinate of some pocket visit `η t ∈ C` with `c(t) < r'` is close to it.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopMarked

open QuantumZipper (H Hbar)
open PocketTraversal Lemma71C

/-! ### Driven curves are nowhere real -/

section Driven

/-- Adding a closed set disjoint from `ℍ` does not change the filled hull. -/
theorem fillH_union_eq_of_inter_H_empty {A B : Set ℂ} (hB : IsClosed B) (hBH : B ∩ H = ∅) :
    fillH (A ∪ B) = fillH A := by
  have hcl : closure (A ∪ B) ∩ H = closure A ∩ H := by
    rw [closure_union, hB.closure_eq, union_inter_distrib_right, hBH, union_empty]
  have hdiff : H \ closure (A ∪ B) = H \ closure A := by
    ext z
    constructor
    · rintro ⟨hz, hzc⟩
      exact ⟨hz, fun h => hzc (closure_mono subset_union_left h)⟩
    · rintro ⟨hz, hzc⟩
      refine ⟨hz, fun h => hzc ?_⟩
      have : z ∈ closure (A ∪ B) ∩ H := ⟨h, hz⟩
      rw [hcl] at this
      exact this.1
  ext z
  simp only [fillH, mem_ofPred_eq, hdiff]
  constructor
  · rintro ⟨hz, h | h⟩
    · have : z ∈ closure (A ∪ B) ∩ H := ⟨h, hz⟩
      rw [hcl] at this
      exact ⟨hz, Or.inl this.1⟩
    · exact ⟨hz, Or.inr h⟩
  · rintro ⟨hz, h | h⟩
    · exact ⟨hz, Or.inl (closure_mono subset_union_left h)⟩
    · exact ⟨hz, Or.inr h⟩

variable {γ : ℝ → ℂ}

/-- **A driven curve has non-real points in every nondegenerate time interval** (its capacity clock is strictly
increasing, and a real piece does not change the filled hull). -/
theorem exists_mem_H_of_lt (hγ : IsDrivenCurve γ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ u ∈ Ioo a b, γ u ∈ H := by
  set a' := (2 * a + b) / 3 with ha'
  set b' := (a + 2 * b) / 3 with hb'
  have h1 : a < a' := by rw [ha']; linarith
  have h2 : a' < b' := by rw [ha', hb']; linarith
  have h3 : b' < b := by rw [hb']; linarith
  have ha'0 : 0 ≤ a' := ha.trans h1.le
  by_contra hno
  push Not at hno
  have hB : γ '' Icc a' b' ∩ H = ∅ := by
    refine eq_empty_iff_forall_notMem.2 ?_
    rintro _ ⟨⟨u, hu, rfl⟩, huH⟩
    exact hno u ⟨h1.trans_le hu.1, hu.2.trans_lt h3⟩ huH
  have hBc : IsClosed (γ '' Icc a' b') :=
    (isCompact_Icc.image_of_continuousOn (hγ.continuousOn.mono fun u hu => ha'0.trans hu.1)).isClosed
  have hsplit : γ '' Icc 0 b' = γ '' Icc 0 a' ∪ γ '' Icc a' b' := by
    rw [← image_union, Icc_union_Icc_eq_Icc ha'0 h2.le]
  have heq : capClock γ b' = capClock γ a' := by
    rw [capClock, capClock, hsplit, fillH_union_eq_of_inter_H_empty hBc hB]
  exact (hγ.strictMonoOn_capClock ha'0 (ha'0.trans h2.le) h2).ne heq.symm

/-- **A prefix up to a positive capacity time meets a closed set** iff at every scale some non-real point of the
curve at an earlier capacity time is close to it. -/
theorem prefix_nonempty_iff_mem_H (hγ : IsDrivenCurve γ) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < capLife γ) {Q : Set ℂ} (hQ : IsClosed Q) :
    (Q ∩ γ '' Icc 0 (capInv γ r)).Nonempty ↔ ∀ m : ℕ, ∃ u, 0 ≤ u ∧ capClock γ u < r ∧ γ u ∈ H ∧
      γ u ∈ thickening (1 / ((m : ℝ) + 1)) Q := by
  obtain ⟨hc0, hcr⟩ := hγ.capInv_spec hr0.le hr
  set c := capInv γ r with hcdef
  have hcpos : 0 < c := by
    refine lt_of_le_of_ne hc0 fun h => ?_
    rw [← h, hγ.capClock_zero] at hcr
    exact hr0.ne hcr
  constructor
  · rintro ⟨z, hzQ, u₀, hu₀, rfl⟩ m
    have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hmem : γ u₀ ∈ thickening (1 / ((m : ℝ) + 1)) Q := self_subset_thickening hε Q hzQ
    have hpre : γ ⁻¹' thickening (1 / ((m : ℝ) + 1)) Q ∈ 𝓝[Ici 0] u₀ :=
      (hγ.continuousOn u₀ hu₀.1).preimage_mem_nhdsWithin (isOpen_thickening.mem_nhds hmem)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1 hpre
    -- an interval `(a, b)` of times below `c` within `δ` of `u₀`
    obtain ⟨a, b, ha0, hab, hbc, hclose⟩ : ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ c ∧
        ∀ u ∈ Ioo a b, dist u u₀ < δ := by
      rcases hu₀.1.lt_or_eq with hpos | hzero
      · refine ⟨max (u₀ - δ / 2) 0, u₀, le_max_right _ _, max_lt (by linarith) hpos, hu₀.2, fun u hu => ?_⟩
        rw [Real.dist_eq, abs_of_neg (by linarith [hu.2])]
        have := le_max_left (u₀ - δ / 2) 0
        linarith [hu.1]
      · refine ⟨0, min (δ / 2) c, le_rfl, lt_min (by linarith) hcpos, min_le_right _ _, fun u hu => ?_⟩
        rw [← hzero, Real.dist_eq, sub_zero, abs_of_pos hu.1]
        have := min_le_left (δ / 2) c
        linarith [hu.2]
    obtain ⟨u, hu, huH⟩ := exists_mem_H_of_lt hγ ha0 hab
    have hu0 : 0 ≤ u := ha0.trans hu.1.le
    refine ⟨u, hu0, ?_, huH, hball ⟨mem_ball.2 (hclose u hu), hu0⟩⟩
    rw [← hcr]
    exact hγ.strictMonoOn_capClock hu0 hc0 (hu.2.trans_le hbc)
  · intro h
    -- the curve on `[0, c]` is compact; distances to `Q` along it tend to `0`
    have hK : IsCompact (γ '' Icc 0 c) :=
      isCompact_Icc.image_of_continuousOn (hγ.continuousOn.mono fun u hu => hu.1)
    have hd : ∀ m : ℕ, ∃ z ∈ γ '' Icc 0 c, infDist z Q < 1 / ((m : ℝ) + 1) := fun m => by
      obtain ⟨u, hu0, hur, -, hut⟩ := h m
      have huc : u ≤ c := by
        by_contra hlt
        rw [not_le] at hlt
        have := hγ.strictMonoOn_capClock hc0 hu0 hlt
        rw [hcr] at this
        linarith
      obtain ⟨w, hwQ, hw⟩ := mem_thickening_iff.1 hut
      exact ⟨γ u, ⟨u, ⟨hu0, huc⟩, rfl⟩, (infDist_le_dist_of_mem hwQ).trans_lt hw⟩
    have hKne : (γ '' Icc 0 c).Nonempty := by
      obtain ⟨z, hz, -⟩ := hd 0
      exact ⟨z, hz⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn (f := fun z => infDist z Q) hKne
      (continuous_infDist_pt Q).continuousOn
    have hzero : infDist z₀ Q = 0 := by
      refine le_antisymm (le_of_forall_pos_lt_add fun ε hε => ?_) infDist_nonneg
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
      obtain ⟨z, hz, hzd⟩ := hd m
      have := hmin hz
      simp only [mem_ofPred_eq] at this
      linarith
    have hQne : Q.Nonempty := by
      by_contra hQe
      rw [not_nonempty_iff_eq_empty] at hQe
      obtain ⟨u, -, -, -, hut⟩ := h 0
      rw [hQe, thickening_empty] at hut
      exact hut
    exact ⟨z₀, (hQ.mem_iff_infDist_zero hQne).2 hzero, hz₀⟩

end Driven

/-! ### Capacity through the hitting criterion -/

section Hit

/-- `hcapHit` only sees the part of a set in `ℍ`, up to closure. -/
theorem hcapHit_congr_closure {A B : Set ℂ} (h : closure (A ∩ H) = closure (B ∩ H)) :
    WholeField.hcapHit A = WholeField.hcapHit B := by
  have key : ∀ (S : Set ℂ) (O : Set ℂ), IsOpen O → O ⊆ H → (Disjoint S O ↔ Disjoint (closure (S ∩ H)) O) :=
    fun S O hO hOH => by
      constructor
      · exact fun hd => (hd.mono_left inter_subset_left).closure_left hO
      · intro hd
        rw [Set.disjoint_left] at hd ⊢
        exact fun z hzS hzO => hd (subset_closure ⟨hzS, hOH hzO⟩) hzO
  unfold WholeField.hcapHit
  have hO : ∀ n s, IsOpen (H \ WholeField.gridUnion n s) := fun n s =>
    QuantumZipper.isOpen_H.sdiff (WholeField.isClosed_gridUnion n s)
  congr 1
  ext1 n
  congr 1
  ext1 s
  have e : Disjoint A (H \ WholeField.gridUnion n s) ↔ Disjoint B (H \ WholeField.gridUnion n s) := by
    rw [key A _ (hO n s) sdiff_subset, key B _ (hO n s) sdiff_subset, h]
  by_cases hA : Disjoint A (H \ WholeField.gridUnion n s)
  · rw [ite_eq_left hA, ite_eq_left (e.1 hA)]
  · rw [ite_eq_right hA, ite_eq_right (fun h' => hA (e.2 h'))]

end Hit

/-! ### The bounded pocket: relative capacity in ambient time -/

section Pocket

open Sec6 PocketUnionPt PocketStopWallsFin

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- The erased traversal of the pocket in the coordinate `ψ`. -/
abbrev trav (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (ψ : ℂ → ℂ) : ℝ → ℂ :=
  relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ)

/-- The relative parameter `ℓ t / (L − ℓ t)` reached at ambient time `t`. -/
def relTime (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (t : ℝ) : ℝ :=
  pocketClock η C τ σ t / (pocketClock η C τ σ σ - pocketClock η C τ σ t)

/-- **The relative capacity reached at ambient time `t`**: `c(t) = capClock γ (ℓ t / (L − ℓ t))`. -/
def relCap (η : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) (ψ : ℂ → ℂ) (t : ℝ) : ℝ :=
  capClock (trav η C τ σ ψ) (relTime η C τ σ t)

theorem relTime_nonneg (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {t : ℝ} (ht : t ∈ Ico τ σ) : 0 ≤ relTime η C τ σ t :=
  div_nonneg (hP.clock_nonneg ht.1) (sub_pos.2 (hP.clock_lt_clock_σ hAC ht)).le

theorem clockOf_relTime (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {t : ℝ} (ht : t ∈ Ico τ σ) : clockOf (pocketClock η C τ σ σ) (relTime η C τ σ t) = pocketClock η C τ σ t :=
  PocketLife.clockOf_div_sub (hP.clock_σ_pos hAC) (hP.clock_lt_clock_σ hAC ht)

/-- The relative time of the right fibre end of the erased time `clockOf L u` is `u`. -/
theorem relTime_fibre_clockOf (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {u : ℝ} (hu : 0 ≤ u) :
    pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) u) ∈ Ico τ σ ∧
      relTime η C τ σ (pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) u)) = u := by
  have hL := hP.clock_σ_pos hAC
  have hv := clockOf_mem_Ico hL hu
  set t := pocketFibre η C τ σ (clockOf (pocketClock η C τ σ σ) u) with htdef
  have hct : pocketClock η C τ σ t = clockOf (pocketClock η C τ σ σ) u := hP.clock_fibre ⟨hv.1, hv.2.le⟩
  have htm : t ∈ Ico τ σ := ⟨(hP.fibre_mem _).1, hP.fibre_lt_σ hv⟩
  refine ⟨htm, (strictMonoOn_clockOf hL).injOn (relTime_nonneg hP hAC htm) hu ?_⟩
  rw [clockOf_relTime hP hAC htm, hct]

/-- For `z ∈ C̄ ∖ {x₀}`, the Jordan coordinate is in `ℍ` iff `z ∈ C`. -/
theorem jordan_mem_H_iff (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {z : ℂ} (hz : z ∈ closure C \ {α₁ 0})
    (hC : IsOpen C) : ψ z ∈ H ↔ z ∈ C := by
  constructor
  · intro hH
    by_contra hzC
    have hfr : z ∈ frontier C \ {α₁ 0} := ⟨⟨hz.1, by rwa [hC.interior_eq]⟩, hz.2⟩
    have := hψ.2.2.2.2.1 z hfr
    exact (ne_of_gt (show (0 : ℝ) < (ψ z).im from hH)) this
  · exact fun hzC => hψ.2.2.2.1.2.mapsTo hzC

/-- **The non-real part of the traversal up to the relative time of `t`** is the Jordan image of the pocket visits
up to `t`: `γ([0, relTime t]) ∩ ℍ = ψ(η([0, t]) ∩ C)` (Aux. lemma 41's (GC2) and no visit inside a clock fibre). -/
theorem image_trav_inter_H (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    trav η C τ σ ψ '' Icc 0 (relTime η C τ σ t) ∩ H = ψ '' (η '' Icc 0 t ∩ C) := by
  have hL := hP.clock_σ_pos hAC
  have hℓt := hP.clock_lt_clock_σ hAC ht
  have hℓ0 := hP.clock_nonneg ht.1
  rw [image_relCurve_Icc _ hL (relTime_nonneg hP hAC ht), clockOf_relTime hP hAC ht]
  -- the erased image lies in `C̄ ∖ {x₀}`
  have hE : ∀ v ∈ Icc 0 (pocketClock η C τ σ t), erasedPath η C τ σ v ∈ closure C \ {α₁ 0} := fun v hv =>
    hP.erasedPath_mem ⟨hv.1, hv.2.trans_lt hℓt⟩
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
    exact notMem_of_mem_Ioc_fibre hP ⟨hℓ0, hℓt⟩ ⟨hleft.trans_lt hlt, ht'.2⟩ hC'
  have himg : erasedPath η C τ σ '' Icc 0 (pocketClock η C τ σ t) ∩ C = η '' Icc 0 t ∩ C := by
    rw [hP.erasedPath_image_inter ⟨hℓ0, hℓt.le⟩, hfib]
  rw [← himg]
  ext w
  constructor
  · rintro ⟨⟨v, hv, rfl⟩, hwH⟩
    exact ⟨erasedPath η C τ σ v, ⟨⟨v, hv, rfl⟩, (jordan_mem_H_iff hψ (hE v hv) hP.isOpen).1 hwH⟩, rfl⟩
  · rintro ⟨_, ⟨⟨v, hv, rfl⟩, hvC⟩, rfl⟩
    exact ⟨⟨v, hv, rfl⟩, hψ.2.2.2.1.2.mapsTo hvC⟩

/-- **The relative capacity reached at ambient time `t ∈ [τ, σ)`** is half the hitting capacity of the Jordan image
of the pocket visits up to `t`. -/
theorem relCap_eq_hcapHit (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    relCap η C τ σ ψ t = (WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C))).toReal / 2 := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have h0 := relTime_nonneg hP hAC ht
  have hh : WholeField.hcapHit (trav η C τ σ ψ '' Icc 0 (relTime η C τ σ t)) =
      WholeField.hcapHit (ψ '' (η '' Icc 0 t ∩ C)) := by
    refine hcapHit_congr_closure ?_
    have hsub : ψ '' (η '' Icc 0 t ∩ C) ⊆ H := by
      rintro _ ⟨z, hz, rfl⟩
      exact hψ.2.2.2.1.2.mapsTo hz.2
    rw [image_trav_inter_H hP hAC hψ ht, inter_eq_left.2 hsub]
  rw [relCap, PocketMeas.capClock_eq_hcapHit hγ h0, PocketMeas.image_nnPath _ h0, hh]

/-- The Jordan coordinate is continuous on the pocket. -/
theorem continuousOn_jordan (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) :
    ContinuousOn ψ C := by
  refine hψ.1.mono fun z hz => ⟨subset_closure hz, fun h => ?_⟩
  have hfr : α₁ 0 ∈ frontier C := by
    rw [hP.frontier_eq]
    exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have := hP.isOpen.inter_frontier_eq
  exact (eq_empty_iff_forall_notMem.1 this) (α₁ 0) ⟨h ▸ hz, hfr⟩

/-- **`T⁰(q)` through the relative capacity in ambient time** (live event): for `t ∈ [τ, σ)`,
`T⁰(q) ≤ t ↔ q ≤ c(t)`. -/
theorem ambTime0_le_iff (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) {t : ℝ} (ht : t ∈ Ico τ σ) :
    ambTime0 η C τ σ ψ q ≤ t ↔ q ≤ relCap η C τ σ ψ t := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have hL := hP.clock_σ_pos hAC
  obtain ⟨hc0, hcq⟩ := hγ.capInv_spec hq0 hq
  have hv := clockOf_mem_Ico hL hc0
  have h0 := relTime_nonneg hP hAC ht
  have e1 : ambTime0 η C τ σ ψ q ≤ t ↔
      clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q) ≤ pocketClock η C τ σ t := by
    constructor
    · intro h
      rw [← clock_pocketFibreLeft hP ⟨hv.1, hv.2.le⟩]
      exact hP.monotone_clock h
    · exact fun h => fibreLeft_le ⟨ht.1, ht.2.le⟩ ((min_le_left _ _).trans h)
  rw [e1, ← clockOf_relTime hP hAC ht, (strictMonoOn_clockOf hL).le_iff_le hc0 h0, relCap,
    ← (hγ.strictMonoOn_capClock).le_iff_le hc0 h0, hcq]

/-- On the live event the stop `T⁰(q)` lies in `[τ, σ)`. -/
theorem ambTime0_mem_Ico (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) : ambTime0 η C τ σ ψ q ∈ Ico τ σ := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have hL := hP.clock_σ_pos hAC
  obtain ⟨hc0, -⟩ := hγ.capInv_spec hq0 hq
  have hv := clockOf_mem_Ico hL hc0
  have hm := pocketFibreLeft_mem hP (clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q))
  refine ⟨hm.1, lt_of_le_of_ne hm.2 fun h => ?_⟩
  have hc := clock_pocketFibreLeft hP ⟨hv.1, hv.2.le⟩
  rw [show pocketFibreLeft η C τ σ (clockOf (pocketClock η C τ σ σ) (capInv (trav η C τ σ ψ) q)) = σ from h] at hc
  exact hv.2.ne hc.symm

theorem relCap_lt_capLife (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    ENNReal.ofReal (relCap η C τ σ ψ t) < capLife (trav η C τ σ ψ) :=
  (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ).ofReal_capClock_lt (relTime_nonneg hP hAC ht)

/-- Below the terminal capacity time some ambient time of `[τ, σ)` has relative capacity above `q`. -/
theorem exists_relCap_gt (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    {q : ℝ} (hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ)) :
    ∃ t ∈ Ico τ σ, q < relCap η C τ σ ψ t := by
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hq
  obtain ⟨htm, hrel⟩ := relTime_fibre_clockOf hP hAC (u := (n : ℝ)) (Nat.cast_nonneg n)
  exact ⟨_, htm, by rw [relCap, hrel]; exact hn⟩

/-- **The live stop before an ambient time `s`** is decided by the relative capacity before `s`:
`q < capLife γ ∧ T⁰(q) ≤ s` iff `τ ≤ s < σ ∧ q ≤ c(s)`, or `σ ≤ s` and `q < c(t)` for some `t ∈ [τ, σ)`. -/
theorem live_and_ambTime0_le_iff (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} (hq0 : 0 ≤ q)
    (s : ℝ) :
    (ENNReal.ofReal q < capLife (trav η C τ σ ψ) ∧ ambTime0 η C τ σ ψ q ≤ s) ↔
      (τ ≤ s ∧ s < σ ∧ q ≤ relCap η C τ σ ψ s) ∨ (σ ≤ s ∧ ∃ t ∈ Ico τ σ, q < relCap η C τ σ ψ t) := by
  constructor
  · rintro ⟨hq, ha⟩
    have hm := ambTime0_mem_Ico hP hAC hψ hq0 hq
    rcases lt_or_ge s σ with hs | hs
    · exact Or.inl ⟨hm.1.trans ha, hs, (ambTime0_le_iff hP hAC hψ hq0 hq ⟨hm.1.trans ha, hs⟩).1 ha⟩
    · exact Or.inr ⟨hs, exists_relCap_gt hP hAC hq⟩
  · rintro (⟨h1, h2, h3⟩ | ⟨hs, t, ht, hlt⟩)
    · have hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ) :=
        (ENNReal.ofReal_le_ofReal h3).trans_lt (relCap_lt_capLife hP hAC hψ ⟨h1, h2⟩)
      exact ⟨hq, (ambTime0_le_iff hP hAC hψ hq0 hq ⟨h1, h2⟩).2 h3⟩
    · have hq : ENNReal.ofReal q < capLife (trav η C τ σ ψ) :=
        (ENNReal.ofReal_le_ofReal hlt.le).trans_lt (relCap_lt_capLife hP hAC hψ ht)
      exact ⟨hq, (pocketFibreLeft_mem hP _).2.trans hs⟩

/-! ### Regularity of the relative capacity in ambient time -/

theorem continuousOn_relTime (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    ContinuousOn (relTime η C τ σ) (Ico τ σ) :=
  hP.continuous_clock.continuousOn.div (continuousOn_const.sub hP.continuous_clock.continuousOn)
    fun _ ht => (sub_pos.2 (hP.clock_lt_clock_σ hAC ht)).ne'

theorem monotoneOn_relTime (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ) :
    MonotoneOn (relTime η C τ σ) (Ico τ σ) := fun _ _ _ hb hab =>
  div_le_div₀ (hP.clock_nonneg hb.1) (hP.monotone_clock hab) (sub_pos.2 (hP.clock_lt_clock_σ hAC hb))
    (sub_le_sub_left (hP.monotone_clock hab) _)

theorem continuousOn_relCap (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) : ContinuousOn (relCap η C τ σ ψ) (Ico τ σ) :=
  (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ).continuousOn_capClock.comp
    (continuousOn_relTime hP hAC) fun _ ht => relTime_nonneg hP hAC ht

theorem monotoneOn_relCap (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) : MonotoneOn (relCap η C τ σ ψ) (Ico τ σ) := fun _ ha _ hb hab =>
  (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ).strictMonoOn_capClock.monotoneOn
    (relTime_nonneg hP hAC ha) (relTime_nonneg hP hAC hb) (monotoneOn_relTime hP hAC ha hb hab)

theorem relCap_τ (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) : relCap η C τ σ ψ τ = 0 := by
  rw [relCap, relTime, IsReversePocket.clock_τ, zero_div]
  exact (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ).capClock_zero

/-- **The relative capacity at `s ∈ (τ, σ)` from rational earlier times**: `q ≤ c(s)` iff at every scale some
rational `p ∈ (τ, s)` has `c(p) > q − 1/(n+1)`. -/
theorem le_relCap_iff_rat (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q s : ℝ} (hs : s ∈ Ioo τ σ) :
    q ≤ relCap η C τ σ ψ s ↔
      ∀ n : ℕ, ∃ p : ℚ, τ < p ∧ (p : ℝ) < s ∧ q - 1 / ((n : ℝ) + 1) < relCap η C τ σ ψ p := by
  have hsI : s ∈ Ico τ σ := ⟨hs.1.le, hs.2⟩
  constructor
  · intro h n
    have hε : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hc := (continuousOn_relCap hP hAC hψ s hsI)
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
    have := monotoneOn_relCap hP hAC hψ ⟨hpτ.le, hps.trans hs.2⟩ hsI hps.le
    linarith

/-- Some ambient time of `[τ, σ)` has relative capacity above `q` iff some rational one has. -/
theorem exists_relCap_gt_iff_rat (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {q : ℝ} :
    (∃ t ∈ Ico τ σ, q < relCap η C τ σ ψ t) ↔ ∃ p : ℚ, τ < p ∧ (p : ℝ) < σ ∧ q < relCap η C τ σ ψ p := by
  constructor
  · rintro ⟨t, ht, hlt⟩
    obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn ht.2
    exact ⟨p, ht.1.trans_lt hp1, hp2,
      hlt.trans_le (monotoneOn_relCap hP hAC hψ ht ⟨ht.1.trans hp1.le, hp2⟩ hp1.le)⟩
  · rintro ⟨p, hp1, hp2, hlt⟩
    exact ⟨p, ⟨hp1.le, hp2⟩, hlt⟩

/-! ### Prefix events through pocket visits -/

/-- **A prefix of the traversal up to a positive capacity time meets a closed set** iff at every scale the Jordan
coordinate of some pocket visit `η t ∈ C` of relative capacity `c(t) < r` is close to it. -/
theorem prefix_nonempty_iff_visit (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {r : ℝ} (hr0 : 0 < r)
    (hr : ENNReal.ofReal r < capLife (trav η C τ σ ψ)) {Q : Set ℂ} (hQ : IsClosed Q) :
    (Q ∩ trav η C τ σ ψ '' Icc 0 (capInv (trav η C τ σ ψ) r)).Nonempty ↔
      ∀ m : ℕ, ∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCap η C τ σ ψ t < r ∧ ψ (η t) ∈ thickening (1 / ((m : ℝ) + 1)) Q := by
  have hγ := isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ
  have hL := hP.clock_σ_pos hAC
  rw [prefix_nonempty_iff_mem_H hγ hr0 hr hQ]
  refine forall_congr' fun m => ⟨?_, ?_⟩
  · rintro ⟨u, hu0, hur, huH, hut⟩
    obtain ⟨htm, hrel⟩ := relTime_fibre_clockOf hP hAC hu0
    have hv := clockOf_mem_Ico hL hu0
    have hE := hP.erasedPath_mem hv
    have hC : erasedPath η C τ σ (clockOf (pocketClock η C τ σ σ) u) ∈ C :=
      (jordan_mem_H_iff hψ hE hP.isOpen).1 huH
    exact ⟨_, hP.nonneg.trans htm.1, hC, by rw [relCap, hrel]; exact hur, hut⟩
  · rintro ⟨t, ht0, htC, htr, htt⟩
    have htI := hP.mem_visitSet ht0 htC
    obtain ⟨hu0, he⟩ := PocketLife.relCurve_of_mem_visitSet (ψ := ψ) hP hAC htI
    have he' : relCurve (fun v => ψ (erasedPath η C τ σ v)) (pocketClock η C τ σ σ) (relTime η C τ σ t) =
        ψ (η t) := he
    refine ⟨relTime η C τ σ t, hu0, htr, ?_, ?_⟩
    · rw [he']
      exact hψ.2.2.2.1.2.mapsTo htC
    · rw [he']
      exact htt

/-- **The visit condition at rational times**: for an open set `O`, a pocket visit with relative capacity below
`r` and Jordan image in `O` exists iff a rational one does (the visit set is open). -/
theorem exists_visit_iff_rat (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {r : ℝ} {O : Set ℂ} (hO : IsOpen O) :
    (∃ t, 0 ≤ t ∧ η t ∈ C ∧ relCap η C τ σ ψ t < r ∧ ψ (η t) ∈ O) ↔
      ∃ p : ℚ, 0 ≤ (p : ℝ) ∧ η p ∈ C ∧ relCap η C τ σ ψ p < r ∧ ψ (η p) ∈ O := by
  refine ⟨?_, fun ⟨p, h⟩ => ⟨p, h⟩⟩
  rintro ⟨t, ht0, htC, htr, htO⟩
  set I := visitSet η C τ σ with hI
  have hIo : IsOpen I := hP.isOpen_visitSet
  have hIsub : I ⊆ Ico τ σ := fun t ht => ⟨ht.1.1.le, ht.1.2⟩
  have hηc : ContinuousOn η I := hP.trace.2.1.mono fun t ht => hP.nonneg.trans ht.1.1.le
  have hψη : ContinuousOn (fun t => ψ (η t)) I :=
    (continuousOn_jordan hP hψ).comp hηc fun t ht => ht.2
  have hU : IsOpen (I ∩ relCap η C τ σ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O) := by
    have h1 := ((continuousOn_relCap hP hAC hψ).mono hIsub).isOpen_inter_preimage hIo (isOpen_Iio (a := r))
    exact (hψη.mono inter_subset_left).isOpen_inter_preimage h1 hO
  have htU : t ∈ I ∩ relCap η C τ σ ψ ⁻¹' Iio r ∩ (fun t => ψ (η t)) ⁻¹' O :=
    ⟨⟨hP.mem_visitSet ht0 htC, htr⟩, htO⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU t htU
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show t - ε < t from by linarith)
  have hpU := hball (show (p : ℝ) ∈ ball t ε by
    rw [mem_ball, Real.dist_eq, abs_of_neg (by linarith)]
    linarith)
  exact ⟨p, hP.nonneg.trans (hIsub hpU.1.1).1, hpU.1.1.2, hpU.1.2, hpU.2⟩

open scoped Classical in
/-- **The relative capacity at `t ∈ [τ, σ)` from the rational pocket visits up to `t`** (junk value `0 ∉ ℍ`). -/
theorem relCap_eq_hcapHit_rat (hP : IsReversePocket W η C α₁ α₂ β τ σ) (hAC : AttachmentConstancy η C α₁ α₂ τ σ)
    (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {t : ℝ} (ht : t ∈ Ico τ σ) :
    relCap η C τ σ ψ t = (WholeField.hcapHit (range fun p : ℚ =>
      if 0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ t ∧ η p ∈ C then ψ (η p) else 0)).toReal / 2 := by
  rw [relCap_eq_hcapHit hP hAC hψ ht]
  congr 2
  refine hcapHit_congr_closure ?_
  have hCH := hP.subset_H
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
  -- `ψ ∘ η` is continuous at the visit time `t' > 0`, approached by rational visit times from the left
  have htI := hP.mem_visitSet ht'.1 htC
  have ht'0 : 0 < t' := hP.nonneg.trans_lt htI.1.1
  have hIo : IsOpen (visitSet η C τ σ) := hP.isOpen_visitSet
  have hηc : ContinuousAt η t' :=
    (hP.trace.2.1 t' ht'0.le).continuousAt (Ici_mem_nhds ht'0)
  have hψc : ContinuousAt ψ (η t') := (continuousOn_jordan hP hψ).continuousAt (hP.isOpen.mem_nhds htC)
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
  refine ⟨ψ (η p), hpN, ⟨⟨p, ?_⟩, hψ.2.2.2.1.2.mapsTo hp.2.2⟩⟩
  simp only [hp, and_self, ↓reduceIte]

end Pocket

end InteractingSLE.Sec7.PocketStopMarked

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71OLocal

/-!
# Lemma 7.1's inherited branch: one wall

Packet PROVE-LEMMA71O (supplement §2.3, "Deterministic normalization lemma", `source/spec/p433-480.md` L472–L520).
Let `c` be a conformal chart of a domain `C` off the hull `K_t` of a Loewner trace `η` (driver `W`), and read the
transition `T = f_t ∘ c.2.1` (`f_t` the centred Loewner map).

* `exists_tendsto_fwdMap_comp`: at every point `x ∈ ℍ̄` at which the chart inverse lands (`c.2.1 → p`), `T` has a limit
  `v ∈ ℍ̄` with `F̄_t(v) = p` (the cluster-set lemma `exists_tendsto_of_tendsto_comp` of [Yua22] §2.1 for the boundary
  extension `F̄_t` of the inverse map); the limit is real when `p ∉ ℍ ∖ K_t` (`im_eq_zero_of_land`);
* **`exists_int_wall`**: if the chart inverse lands outside `ℍ ∖ K_t` at every real point of `B(x, r)`, then
  `Im (log f_t′ − L) ∘ c.2.1 → 2πn` at the real points near `x` for one integer `n`
  (`exists_int_tendsto_of_realLimits`);
* `tendsto_lift_sub_of_agree_chart`: Aux. lemma 57 (`Lemma613.tendsto_lift_sub_of_agree`) read along the chart: if a
  compact `Γ` agrees with a wall prefix `η([0, q])` near the landing point, the canonical logarithm of `fill Γ` and
  `log f_q′` have the same imaginary boundary value along the chart.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71O

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

/-! ### The transition of one wall -/

section Wall

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ} {c : Chart}

/-- **The transition `f_t ∘ c.2.1` has a limit wherever the chart inverse lands** (cluster-set lemma for the boundary
extension `F̄_t` of the inverse Loewner map). -/
theorem exists_tendsto_fwdMap_comp (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hc : c.IsConformal) (hCt : (c.dom : Set ℂ) ⊆ H \ fwdHull W t) {x p : ℂ} (hx : x ∈ Hbar)
    (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 p)) :
    ∃ v ∈ Hbar, extendFrom H (fwdMapInv W t) v = p ∧
      Tendsto (fun y => fwdMap W t (c.2.1 y)) (𝓝[H] x) (𝓝 v) := by
  obtain ⟨hFd, hFc, hFi, hFR⟩ := hη.fiber_hyps hW hW0 ht
  have hinv : ∀ y ∈ H, c.2.1 y ∈ H \ fwdHull W t := fun y hy => hCt (hc.inv_mem_dom hy)
  have hGc : ContinuousOn (fun y => fwdMap W t (c.2.1 y)) H :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht).continuousOn.comp hc.1.continuousOn hinv
  have hGH : MapsTo (fun y => fwdMap W t (c.2.1 y)) H Hbar := fun y hy =>
    H_subset_Hbar (QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht (hinv y hy))
  obtain ⟨K, hK, -⟩ := WangWu.exists_norm_extendFrom_sub_le hη hW hW0 ht
  have hbd : ∀ᶠ y in 𝓝[H] x, ‖fwdMap W t (c.2.1 y)‖ ≤ ‖p‖ + 1 + K := by
    have hb : ∀ᶠ y in 𝓝[H] x, c.2.1 y ∈ ball p 1 := hland (ball_mem_nhds p one_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with y hyb hy
    have hz := hinv y hy
    have hw := QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz
    have h1 := hK _ hw
    rw [QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 ht hz] at h1
    have h2 : ‖c.2.1 y‖ ≤ ‖p‖ + 1 := by
      have := norm_le_norm_add_norm_sub' (c.2.1 y) p
      rw [mem_ball, dist_eq_norm] at hyb
      linarith
    calc ‖fwdMap W t (c.2.1 y)‖ ≤ ‖c.2.1 y‖ + ‖fwdMap W t (c.2.1 y) - c.2.1 y‖ := norm_le_norm_add_norm_sub' _ _
      _ = ‖c.2.1 y‖ + ‖c.2.1 y - fwdMap W t (c.2.1 y)‖ := by rw [norm_sub_rev]
      _ ≤ ‖p‖ + 1 + K := by linarith
  have hFG : Tendsto (fun y => extendFrom H (fwdMapInv W t) (fwdMap W t (c.2.1 y))) (𝓝[H] x) (𝓝 p) :=
    hland.congr' (eventually_nhdsWithin_of_forall fun y hy =>
      (WangWu.extendFrom_fwdMap hW hW0 ht (hinv y hy)).symm)
  obtain ⟨v, hv, hFv, hT⟩ := exists_tendsto_of_tendsto_comp hFd hFc hFi hFR hx hGc hGH hbd hFG
  exact ⟨v, hv, hFv, hT⟩

/-- **The limit is real when the landing point is not a point of `ℍ ∖ K_t`.** -/
theorem im_eq_zero_of_land (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t) {v p : ℂ} (hv : v ∈ Hbar)
    (hFv : extendFrom H (fwdMapInv W t) v = p) (hp : p ∉ H \ fwdHull W t) : v.im = 0 := by
  refine le_antisymm (not_lt.1 fun hpos => hp ?_) hv
  rw [← hFv, WangWu.extendFrom_fwdMapInv_eq hW hW0 ht hpos]
  exact (isConformalBijection_fwdMapInv hW hW0 ht).2.mapsTo hpos

/-- **The integer of one wall** (supplement §2.3: the transition from the chart to the wall's Loewner map reflects
across the real interval with positive derivative). If the chart inverse lands outside `ℍ ∖ K_t` at every real point
of `B(x, r)`, then `Im (log f_t′ − L) ∘ c.2.1 → 2πn` at the real points of `B(x, ε)` for one integer `n`. -/
theorem exists_int_wall (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (ht : 0 ≤ t)
    (hc : c.IsConformal) {C : Set ℂ} (hdom : (c.dom : Set ℂ) = C) {L : ℂ → ℂ} (hL : IsDerivLog c.1 L C)
    (hCt : C ⊆ H \ fwdHull W t) {x r : ℝ} (hr : 0 < r)
    (hland : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull W t ∧ Tendsto c.2.1 (𝓝[H] z) (𝓝 p)) :
    ∃ n : ℤ, ∃ ε > 0, ε ≤ r ∧ ∀ z ∈ ball (x : ℂ) ε, z.im = 0 →
      Tendsto (fun y => (logDerivFwd W t (c.2.1 y) - L (c.2.1 y)).im) (𝓝[H] z) (𝓝 (2 * π * n)) := by
  have hCt' : (c.dom : Set ℂ) ⊆ H \ fwdHull W t := hdom ▸ hCt
  refine exists_int_tendsto_of_realLimits hc hdom hL (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW ht) hCt
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW ht) (QuantumZipper.FwdHolo.injOn_fwdMap hW ht)
    (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW ht hz) (isDerivLog_fwdMap hW ht) hr fun z hz hz0 => ?_
  obtain ⟨p, hp, hpl⟩ := hland z hz hz0
  obtain ⟨v, hv, hFv, hT⟩ := exists_tendsto_fwdMap_comp hη hW hW0 ht hc hCt'
    (show (0 : ℝ) ≤ z.im from hz0.ge) hpl
  exact ⟨v, im_eq_zero_of_land hW hW0 ht hv hFv hp, hT⟩

end Wall

/-! ### Aux. lemma 57 along the chart -/

section Agree

variable {c : Chart}

/-- **Aux. lemma 57 along the chart** (`Lemma613.tendsto_lift_sub_of_agree`): if a compact `Γ` contains the wall
prefix `η([0, q])` and agrees with it near the landing point `p`, and the transition `f_q ∘ c.2.1` has a real limit,
then the canonical logarithm of `fill Γ` and `log f_q′` have the same imaginary boundary value along the chart. -/
theorem tendsto_lift_sub_of_agree_chart {Γ : Set ℂ} (hΓc : IsCompact Γ) (hKΓ : IsHPHull (fillH Γ)) {gK LK : ℂ → ℂ}
    (hgK : IsMapOut (fillH Γ) gK) (hLK : Restart.IsCanonicalDerivLog (fillH Γ) gK LK) (hc : c.IsConformal)
    (hCΓ : (c.dom : Set ℂ) ⊆ H \ fillH Γ) {x p : ℂ} (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 p)) {ρ : ℝ} (hρ : 0 < ρ)
    {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ} (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηi : Function.Injective η) {q : ℝ≥0} (hq0 : 0 < q) (hsub : η '' Icc 0 q ⊆ Γ)
    (hloc : Γ ∩ ball p ρ ⊆ η '' Icc 0 q) {v : ℂ} (hv : v.im = 0)
    (hT : Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal) q (c.2.1 y)) (𝓝[H] x) (𝓝 v)) :
    Tendsto (fun y => (LK (c.2.1 y)).im - (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im) (𝓝[H] x)
      (𝓝 0) := by
  have hg : IsGeneratingTrace W ⊤ (fun t => η t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  have hWc : ContinuousOn W {s : ℝ≥0 | (s : ℝ≥0∞) < ⊤} := hW.continuousOn
  have hi : InjOn η {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} := hηi.injOn
  have hvr : v = ((v.re : ℝ) : ℂ) := eq_ofReal_re_of_im_eq_zero hv
  rw [tendsto_iff_ultrafilter]
  intro U hU
  set V : Ultrafilter ℂ := U.map c.2.1 with hVdef
  have hVle : (V : Filter ℂ) ≤ 𝓝[H \ fillH Γ] p := by
    rw [hVdef, Ultrafilter.coe_map]
    refine tendsto_nhdsWithin_iff.2 ⟨hland.mono_left hU, ?_⟩
    have hH : ∀ᶠ y in (U : Filter ℂ), y ∈ H := hU self_mem_nhdsWithin
    exact hH.mono fun y hy => hCΓ (hc.inv_mem_dom hy)
  have hfy : Tendsto (fun z => fwdMap (fun r : ℝ => W r.toNNReal) q (z - ((0 : ℝ) : ℂ))) (V : Filter ℂ)
      (𝓝 ((v.re : ℝ) : ℂ)) := by
    rw [hVdef, Ultrafilter.coe_map, ← hvr]
    simp only [Complex.ofReal_zero, sub_zero]
    exact tendsto_map'_iff.2 (hT.mono_left hU)
  have h := Lemma613.tendsto_lift_sub_of_agree hΓc hKΓ hgK hLK hρ V hVle hg hWc hW0 hi (WithTop.coe_lt_top q) hq0
    hsub hloc hfy
  simp only [Complex.ofReal_zero, sub_zero] at h
  rw [hVdef, Ultrafilter.coe_map] at h
  exact tendsto_map'_iff.1 h

end Agree

/-! ### One wall at two times -/

section Times

variable {c : Chart} {η : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- A point of the prefix `η([0, q])` is not a point of `ℍ ∖ K_q`. -/
theorem notMem_H_diff_fwdHull (htr : IsGeneratingTrace W ⊤ η) {s q : ℝ≥0} (hsq : s ≤ q) :
    η s ∉ H \ fwdHull (fun r : ℝ => W r.toNNReal) q := by
  rintro ⟨hH, hK⟩
  rw [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr (WithTop.coe_lt_top q)] at hK
  exact hK ⟨hH, Or.inl (subset_closure ⟨s, ⟨zero_le (a := s), hsq⟩, rfl⟩)⟩

/-- **The wall transition has a real limit wherever the chart inverse lands on the stopped prefix.** -/
theorem exists_real_tendsto_wall (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hc : c.IsConformal) {q : ℝ≥0} (hCq : (c.dom : Set ℂ) ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q)
    {x : ℂ} (hx : x ∈ Hbar) {s : ℝ≥0} (hsq : s ≤ q) (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 (η s))) :
    ∃ v : ℂ, v.im = 0 ∧ Tendsto (fun y => fwdMap (fun r : ℝ => W r.toNNReal) q (c.2.1 y)) (𝓝[H] x) (𝓝 v) := by
  have hW'c : Continuous fun r : ℝ => W r.toNNReal := hW.comp continuous_real_toNNReal
  have hW'0 : (fun r : ℝ => W r.toNNReal) 0 = 0 := by simp [hW0]
  obtain ⟨v, hv, hFv, hT⟩ := exists_tendsto_fwdMap_comp (isLoewnerTrace_of_isGeneratingTrace htr) hW'c hW'0
    q.2 hc hCq hx hland
  exact ⟨v, im_eq_zero_of_land hW'c hW'0 q.2 hv hFv (notMem_H_diff_fwdHull htr hsq), hT⟩

/-- **The inherited lift does not depend on the stopping time of the wall** (the untouched-interval identity, Aux.
lemma 57): if the chart inverse lands at `η s`, `s < q ≤ q'`, the derivative arguments of `f_q` and `f_{q'}` have the
same boundary value along the chart. -/
theorem tendsto_logDerivFwd_sub_of_le (htr : IsGeneratingTrace W ⊤ η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hη : Lemma71I.IsSimpleProper η) (hc : c.IsConformal)
    (hCη : ∀ q : ℝ≥0, (c.dom : Set ℂ) ⊆ H \ fillH (η '' Icc 0 q)) {x : ℂ} (hx : x ∈ Hbar) {s q q' : ℝ≥0}
    (hsq : s < q) (hqq' : q ≤ q') (hland : Tendsto c.2.1 (𝓝[H] x) (𝓝 (η s))) :
    Tendsto (fun y => (logDerivFwd (fun r : ℝ => W r.toNNReal) q' (c.2.1 y)).im -
      (logDerivFwd (fun r : ℝ => W r.toNNReal) q (c.2.1 y)).im) (𝓝[H] x) (𝓝 0) := by
  rcases eq_or_lt_of_le hqq' with rfl | hlt
  · simp only [sub_self]; exact tendsto_const_nhds
  have hq0 : 0 < q := lt_of_le_of_lt (zero_le (a := s)) hsq
  have hg : IsGeneratingTrace W ⊤ (fun t => η t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htr
  obtain ⟨κ, hKΓ, hgK, hLK⟩ := ReverseArc.exists_physChart hg hW.continuousOn hW0 (WithTop.coe_lt_top q')
  simp only [Complex.ofReal_zero, sub_zero] at hgK hLK
  have hCq : (c.dom : Set ℂ) ⊆ H \ fwdHull (fun r : ℝ => W r.toNNReal) q := by
    rw [SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace htr (WithTop.coe_lt_top q)]; exact hCη q
  obtain ⟨v, hv0, hT⟩ := exists_real_tendsto_wall htr hW hW0 hc hCq hx hsq.le hland
  obtain ⟨ρ, hρ, hball⟩ := Lemma71N.exists_ball_tail hη hsq
  have hloc : η '' Icc 0 q' ∩ ball (η s) ρ ⊆ η '' Icc 0 q := by
    rintro _ ⟨⟨t, ht, rfl⟩, htb⟩
    refine ⟨t, ⟨ht.1, ?_⟩, rfl⟩
    by_contra hqt
    exact hball t (le_of_lt (not_le.1 hqt)) htb
  exact tendsto_lift_sub_of_agree_chart (isCompact_Icc.image hη.1) hKΓ hgK hLK hc (hCη q') hland hρ htr hW hW0
    hη.2.1 hq0 (image_mono (Icc_subset_Icc_right hqq')) hloc hv0 hT

end Times

end InteractingSLE.Sec7.Lemma71O

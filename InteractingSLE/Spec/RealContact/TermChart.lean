/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermField
import InteractingSLE.Spec.Supplement.SB2WfTip
import InteractingSLE.Spec.Supplement.SB2WfSwal
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Supplement.CollarActivity

/-!
# The terminal retained pair: the Loewner chart at a freshly reached real tip (deterministic)

Packet PROVE-RC-TERM (ruling R124), step P1.2 of `planning/handoffs/PROVE-RC-POCKET.md`: "the terminal point has one
prime end in `D_T`, with chart value `W_T`". Let `γ` be a continuous Loewner trace of a continuous driver `U` on
`[0, T]`, `T > 0`, whose tip `γ(T) = q` is a nonzero real point off every earlier closed hull (`IsFreshRealTip`).
Then the centred Loewner map `f_T = fwdMap U T` of the hull at the horizon is an active chart of the complement
`ℍ ∖ K_T` at the tip:

* **`IsFreshRealTip.eq_zero_of_extendFrom_eq`**: the boundary extension of the inverse map takes the value `q` on `ℍ̄`
  only at `0` (the landed `Theorem14.SB.Wf.eq_zero_of_extendFrom_eq_tip` on `ℝ`; an interior point is mapped into
  `ℍ`);
* **`IsFreshRealTip.tendsto_fwdMap`**: `f_T(z) → 0` as `z → q` in `ℍ ∖ K_T`. Proof: `f_T − id` is bounded, so along a
  sequence `z_n → q` the images have a cluster point `a ∈ ℍ̄`; the inverse extends continuously to `ℍ̄`
  (`TraceClose.hasBdryLimits_of_isLoewnerTraceLT`), so its extension maps `a` to `q`, and `a = 0`;
* **`IsFreshRealTip.isActiveChart`**: the frozen `IsActiveChart (ℍ ∖ K_T) q f_T`.

No prime-end theory is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)

namespace InteractingSLE.RealContact

namespace Term

/-- **A real tip freshly reached at the horizon**: a continuous driver `U` from `0`, a horizon `T > 0`, a Loewner
trace `γ` before `T` which is continuous on `[0, T]`, whose endpoint `γ(T) = q` is a nonzero real point off every
earlier closed hull. -/
structure IsFreshRealTip (U : ℝ → ℝ) (T : ℝ) (γ : ℝ → ℂ) (q : ℝ) : Prop where
  cont : Continuous U
  zero : U 0 = 0
  pos : 0 < T
  trace : IsLoewnerTraceLT U T γ
  traceCont : ContinuousOn γ (Icc 0 T)
  tip : γ T = q
  ne : q ≠ 0
  fresh : ∀ t, 0 ≤ t → t < T → (q : ℂ) ∉ closure (fwdHull U t)

variable {U : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} {q : ℝ}

/-- The centred Loewner map differs from the identity by a bounded amount off the hull. -/
theorem exists_norm_fwdMap_sub_le (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 ≤ T) :
    ∃ C : ℝ, ∀ z ∈ H \ fwdHull U T, ‖fwdMap U T z - z‖ ≤ C := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hU.continuousOn
  refine ⟨24 * M + 8 * Real.sqrt T, fun z hz => ?_⟩
  have hw := QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT hz
  have h1 := norm_fwdMapInv_sub_le hU hU0 hT (M := M)
    (fun r hr => by rw [← Real.norm_eq_abs]; exact hM r hr) hw
  rw [QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hT hz] at h1
  rwa [norm_sub_rev]

/-- On `ℍ` the boundary extension of the inverse Loewner map is the inverse Loewner map. -/
theorem extendFrom_fwdMapInv_of_mem (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 ≤ T) {y : ℂ} (hy : y ∈ H) :
    extendFrom H (fwdMapInv U T) y = fwdMapInv U T y := by
  have hcont : ContinuousOn (fwdMapInv U T) H :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hU hU0 hT).continuousOn
  exact extendFrom_eq (subset_closure hy) (hcont y hy)

/-- **One boundary preimage.** At a freshly reached real tip, the boundary extension of the inverse Loewner map takes
the value `q` on `ℍ̄` only at `0`. -/
theorem IsFreshRealTip.eq_zero_of_extendFrom_eq (h : IsFreshRealTip U T γ q) {y : ℂ} (hy : y ∈ Hbar)
    (hyq : extendFrom H (fwdMapInv U T) y = q) : y = 0 := by
  have hy0 : 0 ≤ y.im := hy
  rcases hy0.eq_or_lt with h0 | hpos
  · have hyr : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← h0])
    have hx : y.re = 0 := Theorem14.SB.Wf.eq_zero_of_extendFrom_eq_tip h.cont h.zero h.pos h.trace h.traceCont
      h.tip h.ne h.fresh (x := y.re) (by rw [← hyr, hyq, h.tip])
    rw [hyr, hx, Complex.ofReal_zero]
  · have hyH : y ∈ H := hpos
    rw [extendFrom_fwdMapInv_of_mem h.cont h.zero h.pos.le hyH] at hyq
    have hmem : 0 < (fwdMapInv U T y).im :=
      (QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull h.cont h.zero h.pos.le hyH).1
    rw [hyq, Complex.ofReal_im] at hmem
    exact absurd hmem (lt_irrefl 0)

/-- **The chart is centred at the tip**: the centred Loewner map at the horizon tends to `0` at a freshly reached real
tip, within the complement of the hull. -/
theorem IsFreshRealTip.tendsto_fwdMap (h : IsFreshRealTip U T γ q) :
    Tendsto (fwdMap U T) (𝓝[H \ fwdHull U T] (q : ℂ)) (𝓝 0) := by
  have hU := h.cont
  have hU0 := h.zero
  have hT := h.pos.le
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  by_contra hcon
  have hseq : ∀ n : ℕ, ∃ z ∈ H \ fwdHull U T, dist z (q : ℂ) < 1 / ((n : ℝ) + 1) ∧
      ε ≤ dist (fwdMap U T z) 0 := by
    intro n
    by_contra hn
    refine hcon ⟨1 / ((n : ℝ) + 1), by positivity, fun z hz hd => ?_⟩
    by_contra hlt
    exact hn ⟨z, hz, hd, not_lt.1 hlt⟩
  choose z hzD hzq hzε using hseq
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 hT
  set y : ℕ → ℂ := fun n => fwdMap U T (z n) with hy
  have hyH : ∀ n, y n ∈ H := fun n => QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT (hzD n)
  -- the images stay in a compact part of the closed half-plane
  have hzn : ∀ n, ‖z n‖ ≤ ‖(q : ℂ)‖ + 1 := fun n => by
    have h1 : dist (z n) (q : ℂ) ≤ 1 := (hzq n).le.trans (by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n])
    have h2 : ‖z n‖ ≤ ‖z n - (q : ℂ)‖ + ‖(q : ℂ)‖ := by
      have := norm_add_le (z n - (q : ℂ)) (q : ℂ)
      rwa [sub_add_cancel] at this
    rw [dist_eq_norm] at h1
    linarith
  have hyn : ∀ n, ‖y n‖ ≤ ‖(q : ℂ)‖ + 1 + C := fun n => by
    have h1 : ‖y n‖ ≤ ‖y n - z n‖ + ‖z n‖ := by
      have := norm_add_le (y n - z n) (z n)
      rwa [sub_add_cancel] at this
    have h2 := hC (z n) (hzD n)
    have h3 := hzn n
    linarith
  have hScomp : IsCompact (Hbar ∩ closedBall (0 : ℂ) (‖(q : ℂ)‖ + 1 + C)) := by
    have hcl : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    exact (isCompact_closedBall _ _).inter_left hcl
  have hyS : ∀ n, y n ∈ Hbar ∩ closedBall (0 : ℂ) (‖(q : ℂ)‖ + 1 + C) := fun n =>
    ⟨show 0 ≤ (y n).im from le_of_lt (hyH n), mem_closedBall_zero_iff.2 (hyn n)⟩
  obtain ⟨a, haS, φ, hφ, hlim⟩ := hScomp.tendsto_subseq hyS
  -- the inverse extension maps the cluster point to the tip
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT h.trace hU hU0 h.pos h.traceCont
  have hFz : ∀ n, extendFrom H (fwdMapInv U T) (y n) = z n := fun n => by
    rw [extendFrom_fwdMapInv_of_mem hU hU0 hT (hyH n)]
    exact QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hT (hzD n)
  have hl1 : Tendsto (fun n => extendFrom H (fwdMapInv U T) (y (φ n))) atTop
      (𝓝 (extendFrom H (fwdMapInv U T) a)) := by
    have hw : Tendsto (y ∘ φ) atTop (𝓝[Hbar] a) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n =>
        show 0 ≤ (y (φ n)).im from le_of_lt (hyH (φ n))⟩
    exact (hB.continuousOn a haS.1).tendsto.comp hw
  have hl2 : Tendsto (fun n => extendFrom H (fwdMapInv U T) (y (φ n))) atTop (𝓝 (q : ℂ)) := by
    have e : (fun n => extendFrom H (fwdMapInv U T) (y (φ n))) = fun n => z (φ n) := funext fun n => hFz (φ n)
    rw [e, tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    refine (hzq (φ n)).le.trans ?_
    have hn : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have ha0 : a = 0 := h.eq_zero_of_extendFrom_eq haS.1 (tendsto_nhds_unique hl1 hl2)
  -- but the images stay away from `0`
  have hnorm : Tendsto (fun n => ‖y (φ n)‖) atTop (𝓝 ‖a‖) := hlim.norm
  have hge : ε ≤ ‖a‖ := ge_of_tendsto' hnorm fun n => by
    have := hzε (φ n)
    rwa [dist_zero_right] at this
  rw [ha0, norm_zero] at hge
  exact absurd hε (not_lt.2 hge)

/-- **The Loewner chart at a freshly reached real tip is an active chart**: `f_T` is a holomorphic bijection of
`ℍ ∖ K_T` onto `ℍ`, tends to `0` at the tip and to `∞` at `∞`. -/
theorem IsFreshRealTip.isActiveChart (h : IsFreshRealTip U T γ q) :
    IsActiveChart (H \ fwdHull U T) (q : ℂ) (fwdMap U T) := by
  have hU := h.cont
  have hU0 := h.zero
  have hT := h.pos.le
  refine ⟨⟨QuantumZipper.FwdHolo.mapsTo_fwdMap hU hT, fun z hz z' hz' e => ?_, fun w hw => ?_⟩,
    QuantumZipper.FwdHolo.differentiableOn_fwdMap hU hT, h.tendsto_fwdMap, ?_⟩
  · rw [← QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hT hz, e, QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hT hz']
  · exact ⟨fwdMapInv U T w, QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hU hU0 hT hw,
      QuantumZipper.RS.fwdMap_fwdMapInv hU hU0 hT hw⟩
  · obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 hT
    rw [← tendsto_norm_atTop_iff_cobounded]
    have h1 : Tendsto (fun z : ℂ => ‖z‖ - C) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fwdHull U T)) atTop :=
      tendsto_atTop_add_const_right _ (-C) (tendsto_norm_cobounded_atTop.mono_left inf_le_left)
    refine tendsto_atTop_mono' _ ?_ h1
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    have h2 := hC z hz
    have h3 : ‖z‖ ≤ ‖z - fwdMap U T z‖ + ‖fwdMap U T z‖ := by
      have := norm_add_le (z - fwdMap U T z) (fwdMap U T z)
      rwa [sub_add_cancel] at this
    rw [norm_sub_rev] at h3
    linarith

end Term

end InteractingSLE.RealContact

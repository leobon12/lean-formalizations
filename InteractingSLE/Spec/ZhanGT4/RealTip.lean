/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.RealTipSep
import InteractingSLE.Spec.ZhanGT4.CrosscutRestart

/-!
# §A.4.3: a real tip sits at an end of the inverse interval

Packet PROVE-ZHAN-GT4-A3. Source: Astra, *Follow-up proofs and dependency audit*, Part A.4.3
(`source/external/AstraIG1/ig1_followup_proofs.txt` L798–L831, ruling R38); the additional note's Theorem 2.12
(`ig1_additional_proofs.txt` L1240–L1281, ruling R39) is the same argument. "Suppose instead that `z = η(T) ∈ ℝ`
and `c < W < d` … This contradiction excludes the event … Consequently a real tip must have `W = c` or `W = d`."

## Main results

* `hasInteriorTip_of_openSides` (deterministic): for a continuous Loewner trace `η` of `W` and `T > 0`, if the open
  driver sides are interior at `T` and at every rational time in `(0, T)` (A.4.2) and `K_T` contains a half-ball
  around `0` (the source collar), then the inverse map has an interior boundary value at the driver coordinate
  whenever that coordinate is strictly inside the inverse interval (`HasInteriorTip W T`).
* `stoppingRealTipStatement_of_openSides`: for `κ > 4`, A.4.2 at stopping times (`StoppingOpenSidesStatement κ`)
  gives A.4.3 (`StoppingRealTipStatement κ`).
* `stoppingCollarStatement_of_firstSwallowCrosscut`: hence **(G7), the stopping-time collar, follows from A.3
  alone** (`FirstSwallowCrosscutStatement κ`, `κ > 4`).

## Proof

Write `F = F̄_T` for the continuous extension of `f_T = g_T⁻¹(W_T + ·)` and suppose `p = F(0)` is real while
`c < 0 < d`. The source collar puts `0` at positive distance from `ℍ \ K_T`, so `p ≠ 0`; by the reflection
`z ↦ −z̄` it suffices to treat `p > 0`. A coordinate `u ∈ (0, d)` has `w = F(u) ∈ ℍ` (A.4.2 at `T`); `w` is a boundary
point of `ℍ \ K_T` in `K_T = fill(η[0, T])`, hence a point `η(t₀)` of the trace. The abstract core
`false_of_real_tip_core` (`RealTipSep.lean`) then runs the source's argument with the access curve `y ↦ F(iy)`: at a
rational time `r` just before `t₀`, the tip `η(r) = F̄_r(0)` lies on the right of the access curve, while the left
boundary arc `F̄_r([u_r, 0])` of `K_r` (interior by A.4.2 at `r`, with nonpositive real points) joins it to a negative
real point without meeting the access curve or `[p, ∞)` — impossible. This replaces the source's hull decomposition
(G6) and its "no real cut point" lemma by the separation of `ℍ̄` along the access curve; it uses no injectivity.
The stopping times are `T` itself and the deterministic rational times.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped ComplexConjugate NNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper QuantumZipper.RS

variable {W : ℝ → ℝ}

/-! ### The boundary extension of a Loewner inverse map -/

theorem extendFrom_eq_fwdMapInv (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {w : ℂ}
    (hw : w ∈ H) : extendFrom H (fwdMapInv W t) w = fwdMapInv W t w :=
  extendFrom_H_eq (continuousOn_fwdMapInv hW hW0 ht) hw

theorem isBoundaryMap_extendFrom {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) : IsBoundaryMap (extendFrom H (fwdMapInv W t)) := by
  obtain ⟨-, hc, hi, -⟩ := hη.fiber_hyps hW hW0 ht
  refine ⟨hc, hi, fun w hw => ?_, ?_⟩
  · rw [extendFrom_eq_fwdMapInv hW hW0 ht hw]
    exact fwdMapInv_mem_H hW hW0 ht hw
  · obtain ⟨C, hC⟩ := InteractingSLE.exists_norm_fwdMapInv_sub_le hW hW0 ht
    exact ⟨C, fun w hw => by rw [extendFrom_eq_fwdMapInv hW hW0 ht hw]; exact hC w hw⟩

theorem extendFrom_image_H (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    extendFrom H (fwdMapInv W t) '' H = H \ fwdHull W t := by
  have heq : EqOn (extendFrom H (fwdMapInv W t)) (fwdMapInv W t) H := fun w hw =>
    extendFrom_eq_fwdMapInv hW hW0 ht hw
  rw [heq.image_eq]
  exact (isConformalBijection_fwdMapInv hW hW0 ht).2.image_eq

/-- Real boundary values of `F̄_r` avoid `F̄_T(ℍ) = ℍ \ K_T` for `r ≤ T`. -/
theorem extendFrom_not_mem_image {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r T : ℝ} (hr : 0 ≤ r) (hrT : r ≤ T) (v : ℝ) :
    extendFrom H (fwdMapInv W r) v ∉ extendFrom H (fwdMapInv W T) '' H := by
  rw [extendFrom_image_H hW hW0 (hr.trans hrT)]
  intro h
  exact hη.extendFrom_not_mem hW hW0 hr (x := (v : ℂ)) (by simp) ⟨h.1, fun hK => h.2 (fwdHull_mono' hrT hK)⟩

theorem extendFrom_tendsto {t : ℝ} {x : ℂ} {p : ℂ} (hx : x.im = 0)
    (h : Tendsto (fwdMapInv W t) (𝓝[H] x) (𝓝 p)) : extendFrom H (fwdMapInv W t) x = p :=
  extendFrom_eq (by rw [closure_H]; exact mem_Hbar_of_im_eq_zero hx) h

/-- **The tip.** `F̄_t(0) = η(t)`. -/
theorem extendFrom_zero_eq {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) : extendFrom H (fwdMapInv W t) 0 = η t :=
  extendFrom_tendsto (by simp) (hη.tendsto_fwdMapInv_tip hW hW0 ht)

/-- On the open driver sides (A.4.2), the boundary value is interior. -/
theorem extendFrom_mem_H_of_openSides {t : ℝ}
    (h : HasInteriorOpenSides W t) {v : ℝ} (hv : v ∉ exteriorCoords W t) (hv0 : v ≠ 0) :
    extendFrom H (fwdMapInv W t) v ∈ H := by
  obtain ⟨q, hq, hlim⟩ := h v hv hv0
  rw [extendFrom_tendsto (by simp) hlim]
  exact hq

/-- **Exterior coordinates have real boundary values, with the sign of the coordinate.** -/
theorem extendFrom_of_mem_exteriorCoords {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {v : ℝ} (hv : v ∈ exteriorCoords W t) :
    (extendFrom H (fwdMapInv W t) v).im = 0 ∧ (v < 0 → (extendFrom H (fwdMapInv W t) v).re ≤ 0) ∧
      (0 < v → 0 ≤ (extendFrom H (fwdMapInv W t) v).re) := by
  set F := extendFrom H (fwdMapInv W t) with hFdef
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 ht).continuousOn
  have hFeq : EqOn F (fwdMapInv W t) H := fun w hw => extendFrom_eq_fwdMapInv hW hW0 ht hw
  obtain ⟨s, hsX, hslim⟩ := mem_closure_iff_seq_limit.1 hv
  choose x hxalive hxs using hsX
  have hFs : ∀ n, F (s n) = x n := by
    intro n
    obtain ⟨w, hw⟩ := hxalive n
    have h1 := extension_fwdMap_eq_of_isForwardSol hW hW0 ht hFeq hFc hw
    rwa [fwdMap_eq_ofReal_re hW hw ⟨ht, le_rfl⟩, hxs n] at h1
  have hlim : Tendsto (fun n => F (s n)) atTop (𝓝 (F v)) := by
    refine (hFc _ (ofReal_mem_Hbar v)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · exact (continuous_ofReal.tendsto v).comp hslim
    · exact Eventually.of_forall fun n => ofReal_mem_Hbar (s n)
  -- the sign of an alive real point is the sign of its coordinate
  have hsign : ∀ n, (s n < 0 → x n < 0) ∧ (0 < s n → 0 < x n) := by
    intro n
    obtain ⟨w, hw⟩ := hxalive n
    have hx0 : x n ≠ 0 := fun h => by
      rw [h] at hw; exact not_isForwardSol_zero hW0 ht hw
    constructor
    · intro hs
      by_contra hpos
      have := re_fwdMap_pos hW hW0 (lt_of_le_of_ne (not_lt.1 hpos) (Ne.symm hx0)) hw ⟨ht, le_rfl⟩
      rw [hxs n] at this; linarith
    · intro hs
      by_contra hneg
      have := re_fwdMap_neg hW hW0 (lt_of_le_of_ne (not_lt.1 hneg) hx0) hw ⟨ht, le_rfl⟩
      rw [hxs n] at this; linarith
  refine ⟨?_, fun hv0 => ?_, fun hv0 => ?_⟩
  · exact (isClosed_eq continuous_im continuous_const).mem_of_tendsto hlim
      (Eventually.of_forall fun n => by rw [hFs n]; simp)
  · refine (isClosed_le continuous_re continuous_const).mem_of_tendsto hlim ?_
    filter_upwards [hslim.eventually (gt_mem_nhds hv0)] with n hn
    show (F (s n)).re ≤ 0
    rw [hFs n, ofReal_re]
    exact ((hsign n).1 hn).le
  · refine (isClosed_le continuous_const continuous_re).mem_of_tendsto hlim ?_
    filter_upwards [hslim.eventually (lt_mem_nhds hv0)] with n hn
    show 0 ≤ (F (s n)).re
    rw [hFs n, ofReal_re]
    exact ((hsign n).2 hn).le

/-- **Far real points** on either side: alive real points beyond any bound, with real coordinates of the right sign
and `F̄_t(coordinate) = point`. -/
theorem exists_coord_far (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) {t : ℝ}
    (ht : 0 < t) (B : ℝ) :
    (∃ v : ℝ, v < 0 ∧ (extendFrom H (fwdMapInv W t) v).im = 0 ∧ (extendFrom H (fwdMapInv W t) v).re < B) ∧
      ∃ v : ℝ, 0 < v ∧ (extendFrom H (fwdMapInv W t) v).im = 0 ∧ B < (extendFrom H (fwdMapInv W t) v).re := by
  set F := extendFrom H (fwdMapInv W t) with hFdef
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 ht.le).continuousOn
  have hFeq : EqOn F (fwdMapInv W t) H := fun w hw => extendFrom_eq_fwdMapInv hW hW0 ht.le hw
  obtain ⟨M, hM⟩ := exists_abs_le_of_continuous hW t
  have hK := CaraR.fwdHull_subset_closedBall hW ht hM
  set ρ : ℝ := M + 3 * Real.sqrt t with hρ
  have hρ0 : 0 ≤ ρ := by
    have := hM 0 ⟨le_rfl, ht.le⟩
    have : 0 ≤ M := (abs_nonneg _).trans this
    positivity
  have hdisj : ∀ x : ℝ, ρ + 1 ≤ |x| → Disjoint (ball (x : ℂ) 1) (fwdHull W t) := by
    intro x hx
    refine Set.disjoint_left.2 fun z hz hzK => ?_
    have h1 := hK hzK
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball] at hz
    have h2 : ‖(x : ℂ)‖ ≤ ‖z‖ + dist z x := by
      rw [dist_eq_norm]; linarith [norm_sub_norm_le (x : ℂ) z, norm_sub_rev (x : ℂ) z]
    rw [Complex.norm_real, Real.norm_eq_abs] at h2
    linarith
  have hcoord : ∀ x : ℝ, ρ + 1 ≤ |x| → ∃ w, IsForwardSol W (x : ℂ) t w := fun x hx =>
    exists_isForwardSol_of_disjoint_ball hW hW0 (fun h => by rw [h, abs_zero] at hx; linarith) ht.le one_pos
      (hdisj x hx)
  have hFx : ∀ x : ℝ, ∀ w, IsForwardSol W (x : ℂ) t w → F ((fwdMap W t x).re : ℝ) = x := by
    intro x w hw
    have h1 := extension_fwdMap_eq_of_isForwardSol hW hW0 ht.le hFeq hFc hw
    rwa [fwdMap_eq_ofReal_re hW hw ⟨ht.le, le_rfl⟩] at h1
  constructor
  · set x : ℝ := -(ρ + 1 + |B|) with hx
    have hxa : ρ + 1 ≤ |x| := by rw [hx, abs_neg, abs_of_nonneg (by positivity)]; linarith [abs_nonneg B]
    obtain ⟨w, hw⟩ := hcoord x hxa
    have hx0 : x < 0 := by rw [hx]; linarith [abs_nonneg B]
    refine ⟨(fwdMap W t x).re, re_fwdMap_neg hW hW0 hx0 hw ⟨ht.le, le_rfl⟩, ?_, ?_⟩
    · rw [hFx x w hw]; simp
    · rw [hFx x w hw, ofReal_re, hx]; linarith [neg_abs_le B]
  · set x : ℝ := ρ + 1 + |B| with hx
    have hxa : ρ + 1 ≤ |x| := by rw [hx, abs_of_nonneg (by positivity)]; linarith [abs_nonneg B]
    obtain ⟨w, hw⟩ := hcoord x hxa
    have hx0 : 0 < x := by rw [hx]; positivity
    refine ⟨(fwdMap W t x).re, re_fwdMap_pos hW hW0 hx0 hw ⟨ht.le, le_rfl⟩, ?_, ?_⟩
    · rw [hFx x w hw]; simp
    · rw [hFx x w hw, ofReal_re, hx]; linarith [le_abs_self B]

/-- **A boundary point of the active domain inside the hull is on the trace.** If `z ∈ K_t` is a limit of points of
`ℍ \ K_t`, then `z ∈ η([0, t])`: otherwise a disc around `z` misses `η([0, t])`, lies in the bounded component of
`ℍ \ η([0, t])` containing `z`, hence in `K_t = fill(η[0, t])` (as in `mem_image_or_notMem_closure_of_mem_fwdHull`). -/
theorem mem_image_of_mem_fwdHull_of_mem_closure {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ fwdHull W t) (hzc : z ∈ closure (H \ fwdHull W t)) : z ∈ η '' Icc 0 t := by
  by_contra hzA
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := hη.isCompact_image t
  have hzK := hz
  rw [hη.2.2 t ht] at hzK
  obtain ⟨hzH, hzF⟩ := hzK
  rw [hAc.isClosed.closure_eq] at hzF
  have hbdd : Bornology.IsBounded (connectedComponentIn (H \ A) z) := hzF.resolve_left hzA
  have hAne : A.Nonempty := ⟨η 0, mem_image_of_mem _ ⟨le_rfl, ht⟩⟩
  have hd : 0 < infDist z A := (hAc.isClosed.notMem_iff_infDist_pos hAne).1 hzA
  set r : ℝ := min (infDist z A) z.im with hr
  have hr0 : 0 < r := lt_min hd hzH
  have hball : ball z r ⊆ H \ A := by
    intro w hw
    rw [mem_ball] at hw
    refine ⟨?_, fun hwA => ?_⟩
    · show 0 < w.im
      have := Complex.abs_im_le_norm (w - z)
      rw [Complex.sub_im, ← dist_eq_norm] at this
      have h2 : dist w z < z.im := hw.trans_le (min_le_right _ _)
      linarith [(abs_le.1 this).1]
    · have := infDist_le_dist_of_mem hwA (x := z)
      rw [dist_comm] at this
      linarith [min_le_left (infDist z A) z.im]
  have hballK : ball z r ⊆ fwdHull W t := by
    intro w hw
    have hsub : ball z r ⊆ connectedComponentIn (H \ A) z :=
      (convex_ball z r).isPreconnected.subset_connectedComponentIn (mem_ball_self hr0) hball
    have hwC := hsub hw
    rw [hη.2.2 t ht, ← hA]
    refine ⟨(hball hw).1, Or.inr ?_⟩
    rw [hAc.isClosed.closure_eq, ← connectedComponentIn_eq hwC]
    exact hbdd
  obtain ⟨w, hw, hwb⟩ := Metric.mem_closure_iff.1 hzc r hr0
  exact hw.2 (hballK (by rw [mem_ball, dist_comm]; exact hwb))

/-- A real boundary value in `ℍ` lies in `K_t` and in the closure of `ℍ \ K_t`. -/
theorem extendFrom_mem_fwdHull {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) {v : ℝ} (hvH : extendFrom H (fwdMapInv W t) v ∈ H) :
    extendFrom H (fwdMapInv W t) v ∈ fwdHull W t ∧
      extendFrom H (fwdMapInv W t) v ∈ closure (H \ fwdHull W t) := by
  have hnot := hη.extendFrom_not_mem hW hW0 ht (x := (v : ℂ)) (by simp)
  refine ⟨by_contra fun h => hnot ⟨hvH, h⟩, ?_⟩
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto (ofReal_mem_Hbar v)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (v : ℂ)) (by simp)
  exact mem_closure_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun w hw => fwdMapInv_mem_compl_fwdHull hW hW0 ht hw)

/-- **The source collar keeps the tip away from `0`**: if `K_t ⊇ ℍ ∩ B(0, ε)`, then `‖F̄_t(0)‖ ≥ ε`. -/
theorem le_norm_extendFrom_zero (hW : Continuous W) (hW0 : W 0 = 0) {η : ℝ → ℂ} (hη : IsLoewnerTrace W η)
    {t ε : ℝ} (ht : 0 ≤ t) (hcol : ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull W t) :
    ε ≤ ‖extendFrom H (fwdMapInv W t) 0‖ := by
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto (ofReal_mem_Hbar 0)
  rw [ofReal_zero] at hlim
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (0 : ℂ)) (by simp)
  refine (isClosed_le continuous_const continuous_norm).mem_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun w hw => ?_)
  have h := fwdMapInv_mem_compl_fwdHull hW hW0 ht hw
  by_contra hlt
  exact h.2 (hcol _ h.1 (not_le.1 hlt))

/-- **Real boundary values at a time with an interior tip** (A.4.2 at that time): a real value of `F̄_r` at a
coordinate `v` forces `v ≠ 0` and gives `F̄_r(v)` the sign of `v`. -/
theorem sign_of_extendFrom_real {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {r : ℝ} (hr : 0 ≤ r) (hs : HasInteriorOpenSides W r) (htip : η r ∈ H) {v : ℝ}
    (him : (extendFrom H (fwdMapInv W r) v).im = 0) :
    (v < 0 ∧ (extendFrom H (fwdMapInv W r) v).re ≤ 0) ∨ (0 < v ∧ 0 ≤ (extendFrom H (fwdMapInv W r) v).re) := by
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [ofReal_zero, extendFrom_zero_eq hη hW hW0 hr] at him
    exact not_mem_H_of_im_eq_zero him htip
  by_cases hv : v ∈ exteriorCoords W r
  · obtain ⟨-, hneg, hpos⟩ := extendFrom_of_mem_exteriorCoords hη hW hW0 hr hv
    rcases lt_or_gt_of_ne hv0 with h | h
    · exact Or.inl ⟨h, hneg h⟩
    · exact Or.inr ⟨h, hpos h⟩
  · exact absurd (extendFrom_mem_H_of_openSides hs hv hv0) (not_mem_H_of_im_eq_zero him)

/-! ### Reflection -/

theorem negConj_ofReal (x : ℝ) : -conj (x : ℂ) = ((-x : ℝ) : ℂ) := by simp

theorem negConj_mem_H {z : ℂ} : -conj z ∈ H ↔ z ∈ H := by
  show 0 < (-conj z).im ↔ 0 < z.im
  simp

theorem negConj_mem_Hbar {z : ℂ} : -conj z ∈ Hbar ↔ z ∈ Hbar := by
  show 0 ≤ (-conj z).im ↔ 0 ≤ z.im
  simp

theorem negConj_injective : Function.Injective (fun z : ℂ => -conj z) := fun z w h => by
  have := congrArg (fun x => -conj x) h
  simpa using this

theorem IsBoundaryMap.reflect {F : ℂ → ℂ} (hF : IsBoundaryMap F) :
    IsBoundaryMap (fun z => -conj (F (-conj z))) := by
  have hr : Continuous (fun z : ℂ => -conj z) := continuous_conj.neg
  have hHbar : MapsTo (fun z : ℂ => -conj z) Hbar Hbar := fun z hz => by
    have h : 0 ≤ z.im := hz
    show 0 ≤ (-conj z).im; simpa using h
  have hH : MapsTo (fun z : ℂ => -conj z) H H := fun z hz => by
    have h : 0 < z.im := hz
    show 0 < (-conj z).im; simpa using h
  refine ⟨hr.comp_continuousOn (hF.cont.comp hr.continuousOn hHbar), fun z hz w hw hzw => ?_,
    fun z hz => hH (hF.mapsTo (hH hz)), ?_⟩
  · have h1 : F (-conj z) = F (-conj w) := by
      have := congrArg (fun x => -conj x) hzw
      simpa using this
    have h2 := hF.inj (hH hz) (hH hw) h1
    have := congrArg (fun x => -conj x) h2
    simpa using this
  · obtain ⟨C, hC⟩ := hF.bdd
    refine ⟨C, fun w hw => ?_⟩
    have h := hC _ (hH hw)
    have : -conj (F (-conj w)) - w = -conj (F (-conj w) - -conj w) := by simp; ring
    rw [this, norm_neg, Complex.norm_conj]
    exact h

/-! ### The deterministic theorem -/

/-- **A.4.3, deterministic form.** Let `η` be a continuous Loewner trace of `W` (continuous, `W 0 = 0`) and `T > 0`.
If the open driver sides are interior at `T` and at every rational time in `(0, T)` (A.4.2), and `K_T` contains a
half-ball around `0` (the source collar), then a driver coordinate strictly inside the inverse interval has an
interior boundary value: a real tip sits at an end of the inverse interval. -/
theorem hasInteriorTip_of_openSides {η : ℝ → ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    {T : ℝ} (hT : 0 < T) (hs : HasInteriorOpenSides W T)
    (hrat : ∀ r : ℚ, 0 < (r : ℝ) → (r : ℝ) < T → HasInteriorOpenSides W r)
    (hcol : ∃ ε > (0 : ℝ), ∀ z ∈ H, ‖z‖ < ε → z ∈ fwdHull W T) :
    HasInteriorTip W T := by
  intro h0
  set F := extendFrom H (fwdMapInv W T) with hFdef
  have hlim : Tendsto (fwdMapInv W T) (𝓝[H] 0) (𝓝 (F 0)) := by
    have := (hη.hasBdryLimits hW hW0 hT.le).tendsto (ofReal_mem_Hbar 0)
    rwa [ofReal_zero] at this
  by_cases hF0 : F 0 ∈ H
  · exact ⟨F 0, hF0, hlim⟩
  exfalso
  have hFb := isBoundaryMap_extendFrom hη hW hW0 hT.le
  have hF0bar : F 0 ∈ Hbar := by
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := (0 : ℂ)) (by simp)
    exact QuantumZipper.isClosed_Hbar.mem_of_tendsto hlim
      (eventually_nhdsWithin_of_forall fun w hw => H_subset_Hbar (fwdMapInv_mem_H hW hW0 hT.le hw))
  have hp : (F 0).im = 0 := le_antisymm (not_lt.1 hF0) hF0bar
  -- the tip is not `0`
  have hp0 : (F 0).re ≠ 0 := by
    obtain ⟨ε, hε, hK⟩ := hcol
    have h1 := le_norm_extendFrom_zero hW hW0 hη hT.le hK
    intro h
    have : F 0 = 0 := Complex.ext h hp
    rw [← hFdef, this, norm_zero] at h1
    linarith
  -- a small coordinate on each side off the exterior coordinates
  obtain ⟨δ, hδ, hδext⟩ : ∃ δ > (0 : ℝ), ∀ v : ℝ, |v| < δ → v ∉ exteriorCoords W T := by
    obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl 0 h0
    exact ⟨δ, hδ, fun v hv => hsub (by rw [mem_ball, Real.dist_eq, sub_zero]; exact hv)⟩
  obtain ⟨u, hu, huδ⟩ : ∃ u : ℝ, 0 < u ∧ u < δ := ⟨δ / 2, half_pos hδ, by linarith⟩
  have huext : u ∉ exteriorCoords W T := hδext u (by rw [abs_of_pos hu]; exact huδ)
  have huext' : -u ∉ exteriorCoords W T := hδext (-u) (by rw [abs_neg, abs_of_pos hu]; exact huδ)
  -- the trace point at a boundary value in `ℍ`
  have htrace : ∀ v : ℝ, F v ∈ H → ∃ t₀ ∈ Ioc 0 T, η t₀ = F v := by
    intro v hv
    obtain ⟨hK, hcl⟩ := extendFrom_mem_fwdHull hη hW hW0 hT.le hv
    obtain ⟨t₀, ht₀, he⟩ := mem_image_of_mem_fwdHull_of_mem_closure hη hT.le hK hcl
    refine ⟨t₀, ⟨lt_of_le_of_ne ht₀.1 fun h => ?_, ht₀.2⟩, he⟩
    rw [← h, hη.1] at he
    exact not_mem_H_of_im_eq_zero (by rw [hFdef, ← he]; simp) hv
  have hnotimg : ∀ v : ℝ, F v ∉ F '' H := fun v =>
    extendFrom_not_mem_image hη hW hW0 hT.le le_rfl v
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · -- `p < 0`: reflect by `z ↦ −z̄`
    obtain ⟨⟨x₁, hx₁, hx₁r, hx₁p⟩, -⟩ := exists_coord_far hW hW0 hη hT (F 0).re
    have huH : F ((-u : ℝ) : ℂ) ∈ H := extendFrom_mem_H_of_openSides hs huext' (by linarith)
    obtain ⟨t₀, ht₀, hηt₀⟩ := htrace _ huH
    refine false_of_real_tip_core (F := fun z => -conj (F (-conj z))) (η := fun t => -conj (η t))
      (G := fun r z => -conj (extendFrom H (fwdMapInv W r) (-conj z))) (T := T) (x₁ := -x₁) (u := u)
      hFb.reflect ?_ ?_ (by linarith) ?_ ?_ hu ?_ ?_ (continuous_conj.neg.comp_continuousOn hη.2.1) ht₀ ?_ ?_
    · show (-conj (F (-conj 0))).im = 0
      simpa using hp
    · show 0 < (-conj (F (-conj 0))).re
      simp only [map_zero, neg_zero, neg_re, conj_re]
      linarith
    · show (-conj (F (-conj ((-x₁ : ℝ) : ℂ)))).im = 0
      rw [negConj_ofReal, neg_neg]
      simpa using hx₁r
    · show (-conj (F (-conj 0))).re < (-conj (F (-conj ((-x₁ : ℝ) : ℂ)))).re
      rw [negConj_ofReal, neg_neg]
      simp only [map_zero, neg_zero, neg_re, conj_re]
      linarith
    · show -conj (F (-conj (u : ℂ))) ∈ H
      rw [negConj_ofReal, negConj_mem_H]
      exact huH
    · rintro ⟨w, hw, hwe⟩
      have h1 : F (-conj w) = F (-conj (u : ℂ)) := negConj_injective hwe
      rw [negConj_ofReal] at h1
      exact hnotimg (-u) ⟨-conj w, negConj_mem_H.2 hw, h1⟩
    · show -conj (η t₀) = -conj (F (-conj (u : ℂ)))
      rw [hηt₀, negConj_ofReal]
    · intro r hr0 hrT hηr
      have hηr' : η r ∈ H := negConj_mem_H.1 hηr
      have hr : (0 : ℝ) ≤ r := hr0.le
      set G := extendFrom H (fwdMapInv W r) with hGdef
      obtain ⟨-, ⟨ur, hur, hurr, -⟩⟩ := exists_coord_far hW hW0 hη hr0 0
      refine ⟨?_, ?_, fun v => ?_, -ur, by linarith, ?_, fun v hv him => ?_⟩
      · have hrc : Continuous (fun z : ℂ => -conj z) := continuous_conj.neg
        refine hrc.comp_continuousOn ((hη.hasBdryLimits hW hW0 hr).continuousOn.comp hrc.continuousOn ?_)
        intro z hz
        exact negConj_mem_Hbar.2 hz
      · show -conj (G (-conj 0)) = -conj (η r)
        rw [map_zero, neg_zero, hGdef, extendFrom_zero_eq hη hW hW0 hr]
      · rintro ⟨w, hw, hwe⟩
        have h1 : F (-conj w) = G (-conj (v : ℂ)) := negConj_injective hwe
        rw [negConj_ofReal] at h1
        exact extendFrom_not_mem_image hη hW hW0 hr hrT.le (-v) ⟨-conj w, negConj_mem_H.2 hw, h1⟩
      · show (-conj (G (-conj ((-ur : ℝ) : ℂ)))).im = 0
        rw [negConj_ofReal, neg_neg]
        simpa using hurr
      · have him' : (G ((-v : ℝ) : ℂ)).im = 0 := by
          have h2 : (-conj (G (-conj (v : ℂ)))).im = 0 := him
          rw [negConj_ofReal] at h2
          simpa using h2
        rcases sign_of_extendFrom_real hη hW hW0 hr (hrat r hr0 hrT) hηr' him' with h | h
        · linarith [hv.2, h.1]
        · show (-conj (G (-conj (v : ℂ)))).re ≤ 0
          rw [negConj_ofReal]
          simp only [neg_re, conj_re]
          linarith [h.2]
  · -- `p > 0`
    obtain ⟨-, ⟨x₁, hx₁, hx₁r, hx₁p⟩⟩ := exists_coord_far hW hW0 hη hT (F 0).re
    have huH : F (u : ℂ) ∈ H := extendFrom_mem_H_of_openSides hs huext hu.ne'
    obtain ⟨t₀, ht₀, hηt₀⟩ := htrace _ huH
    refine false_of_real_tip_core (G := fun r => extendFrom H (fwdMapInv W r)) hFb hp hpos hx₁ hx₁r hx₁p
      hu huH (hnotimg _) hη.2.1 ht₀ hηt₀ ?_
    intro r hr0 hrT hηr
    have hr : (0 : ℝ) ≤ r := hr0.le
    obtain ⟨⟨ur, hur, hurr, -⟩, -⟩ := exists_coord_far hW hW0 hη hr0 0
    refine ⟨(hη.hasBdryLimits hW hW0 hr).continuousOn, extendFrom_zero_eq hη hW hW0 hr,
      fun v => extendFrom_not_mem_image hη hW hW0 hr hrT.le v, ur, hur, hurr, fun v hv him => ?_⟩
    rcases sign_of_extendFrom_real hη hW hW0 hr (hrat r hr0 hrT) hηr him with h | h
    · exact h.2
    · linarith [hv.2, h.1]

/-! ### At stopping times -/

/-- **A.4.3 at stopping times, from A.4.2** (`κ > 4`): if almost surely the open driver sides are interior at every
positive finite stopping time, then almost surely a real tip sits at an end of the inverse interval. A.4.2 is applied
at `T` and at the deterministic rational times; the trace and the source collar are almost sure for ordinary
`SLE_κ`. -/
theorem stoppingRealTipStatement_of_openSides {κ : ℝ} (hκ : 4 < κ) (h : StoppingOpenSidesStatement.{u} κ) :
    StoppingRealTipStatement.{u} κ := by
  intro Ω mΩ P hP 𝓕 B hB T hT hTpos
  obtain ⟨B', -, hB'c, hB'0, hB'BM, hae⟩ := exists_continuous_version_zero hB
  have hT' := h P 𝓕 B hB T hT hTpos
  have hrat : ∀ᵐ ω ∂P, ∀ r : ℚ, 0 < (r : ℝ) → HasInteriorOpenSides (drive κ B ω) r := by
    rw [ae_all_iff]
    intro r
    by_cases hr : 0 < (r : ℝ)
    · have hc := h P 𝓕 B hB (fun _ => (r : ℝ).toNNReal) (isStoppingTime_const 𝓕 _)
        (fun _ => Real.toNNReal_pos.2 hr)
      filter_upwards [hc] with ω hω _
      rwa [Real.coe_toNNReal _ hr.le] at hω
    · exact Eventually.of_forall fun _ h' => absurd h' hr
  have hBM := hB'BM.1
  filter_upwards [hT', hrat, hae, ae_isLoewnerTrace_sleTrace hBM (by linarith : (0 : ℝ) < κ),
    ae_forall_sleHull_halfBall_of_four_lt hBM hκ] with ω hTω hratω haeω htr hcol
  have hdr : drive κ B ω = drive κ B' ω := funext fun r => by simp only [drive, haeω]
  rw [hdr] at hTω hratω ⊢
  have hWc : Continuous (drive κ B' ω) := drive_continuous (hB'c ω)
  have hW0 : drive κ B' ω 0 = 0 := by simp [drive, hB'0]
  have hT0 : (0 : ℝ) < T ω := by exact_mod_cast hTpos ω
  exact hasInteriorTip_of_openSides htr hWc hW0 hT0 hTω (fun r hr _ => hratω r hr) (hcol (T ω) hT0)

/-- **A.4.3 at stopping times from A.3** (`κ > 4`). -/
theorem stoppingRealTipStatement_of_firstSwallowCrosscut {κ : ℝ} (hκ : 4 < κ)
    (hA3 : FirstSwallowCrosscutStatement.{u} κ) : StoppingRealTipStatement.{u} κ :=
  stoppingRealTipStatement_of_openSides hκ (stoppingOpenSidesStatement_of_firstSwallowCrosscut hκ hA3)

/-- **(G5) at stopping times from A.3** (`κ > 4`). -/
theorem stoppingInverseBoundaryStatement_of_firstSwallowCrosscut {κ : ℝ} (hκ : 4 < κ)
    (hA3 : FirstSwallowCrosscutStatement.{u} κ) : StoppingInverseBoundaryStatement.{u} κ :=
  stoppingInverseBoundaryStatement_of_openSides_of_tip
    (stoppingOpenSidesStatement_of_firstSwallowCrosscut hκ hA3)
    (stoppingRealTipStatement_of_firstSwallowCrosscut hκ hA3)

/-- **(G7), the stopping-time collar, from A.3 alone** (`κ > 4`; the LP4 input, specification p. 483): with A.4.2
(`stoppingOpenSidesStatement_of_firstSwallowCrosscut`) and A.4.3 (`stoppingRealTipStatement_of_openSides`), the
first-swallow crosscut theorem is the only remaining input of the collar. -/
theorem stoppingCollarStatement_of_firstSwallowCrosscut {κ : ℝ} (hκ : 4 < κ)
    (hA3 : FirstSwallowCrosscutStatement.{u} κ) : StoppingCollarStatement.{u} κ :=
  stoppingCollarStatement_of_openSides_of_tip (by linarith)
    (stoppingOpenSidesStatement_of_firstSwallowCrosscut hκ hA3)
    (stoppingRealTipStatement_of_firstSwallowCrosscut hκ hA3)

end InteractingSLE.ZhanGT4

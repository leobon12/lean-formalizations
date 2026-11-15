/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeIncl
import InteractingSLE.Spec.Sec7.PocketSideInReachExtension
import InteractingSLE.Spec.Supplement.R6RefPhase

/-!
# R.6's face from a local inclusion at the outer landing of the shared force point

Packet PROVE-R6-FACE2 (continuing PROVE-R6-SAFE round 5). Supplement §5.6, Lemma R.6 and its application to a mixed
pocket (`source/spec/p433-480.md` L1024–L1040): "the selected active `U` face shares precisely the required connected
real interval through the driver and a surviving `γ` collar".

This file is deterministic. For an outer chart `O` (current chart of `C`), an inner chart `I` (current chart of
`U ⊆ C`) with `I.dom ⊆ O.dom`, continuous inverse extensions `E_O`, `E_I` on `ℍ̄`, and the outer force coordinate
`v = v_R > 0` on the shared side, the face `R6FaceR` follows from:

* the **local inclusion** `D_C ∩ B(p_F, ε) ⊆ D_U` at the physical landing `p_F = E_O(v)` of the force point;
* a bound for the inner coordinate on `D_U ∩ B(p_F, ε)`;
* the **dichotomy** of the outer prime ends near `v` in the inner chart: the landing of an outer coordinate at or just
  left of `v` (a hull point) has its inner real coordinates in `[w_L, w_R]`, that of an outer coordinate just right of
  `v` (an alive shared-wall point) has none there; and `w_R > 0`.

The interval is `J = (v − δ, v + δ)`: the collars are pulled back from the local inclusion by continuity of `E_O` at
`v`; the reflection lemma `PocketStopSide.exists_transition_extension_of_inverse_and_bounds` gives the extended
transition `G` (real on `J`, real-boundary conformal, hence strictly increasing on a real diameter by its positive
boundary derivative, `strictMonoOn_re_of_isRealBoundaryConformal`). Monotonicity and the dichotomy force `G(v) = w_R`,
`G > w_R` just right of `v` and `0 < G < w_R` just left of `v` (no orientation of the inner pocket is used). The local
agreement of the two active complements at the outer landings is the local inclusion again.

* **`r6FaceR_right`** (shared side on the right), **`r6FaceR_left`** (its mirror).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Fc

open PocketStopSide R6Safe

variable {O I : Chart}

theorem real_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)

theorem neBot_nhdsWithin_H_real (x : ℝ) : (𝓝[H] (x : ℂ)).NeBot :=
  mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact real_mem_Hbar x)

theorem schwarzReflect_ofReal (G : ℂ → ℂ) (t : ℝ) : QuantumZipper.CA.schwarzReflect G (t : ℂ) = G t := by
  simp [QuantumZipper.CA.schwarzReflect]

/-- The landings of a continuous inverse extension. -/
theorem tendsto_of_extension {E : ℂ → ℂ} {c : Chart} (hE : EqOn E c.2.1 H) (hEc : ContinuousOn E Hbar) (x : ℝ) :
    Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (E x)) :=
  ((hEc _ (real_mem_Hbar x)).mono QuantumZipper.H_subset_Hbar).tendsto.congr'
    (eventually_nhdsWithin_of_forall fun _ hz => hE hz)

/-- A real-boundary-conformal map is **strictly increasing on its real diameter** (positive boundary derivative,
`R16.IsRealBoundaryConformal.deriv_schwarzReflect_pos`). -/
theorem strictMonoOn_re_of_isRealBoundaryConformal {G : ℂ → ℂ} {x r : ℝ} (h : R16.IsRealBoundaryConformal G x r) :
    StrictMonoOn (fun t : ℝ => (G t).re) (Ioo (x - r) (x + r)) := by
  have hd := h.differentiableOn_schwarzReflect
  have hball : ∀ t ∈ Ioo (x - r) (x + r), (t : ℂ) ∈ ball (x : ℂ) r := fun t ht => by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_lt_iff]
    constructor <;> linarith [ht.1, ht.2]
  have hderiv : ∀ t ∈ Ioo (x - r) (x + r), HasDerivAt (fun t : ℝ => (QuantumZipper.CA.schwarzReflect G t).re)
      (deriv (QuantumZipper.CA.schwarzReflect G) t).re t := fun t ht =>
    ((hd.differentiableAt (isOpen_ball.mem_nhds (hball t ht))).hasDerivAt).real_of_complex
  have hmono : StrictMonoOn (fun t : ℝ => (QuantumZipper.CA.schwarzReflect G t).re) (Ioo (x - r) (x + r)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      fun t ht => ?_
    rw [interior_Ioo] at ht
    rw [(hderiv t ht).deriv]
    exact (h.deriv_schwarzReflect_pos (hball t ht)).2
  intro s hs t ht hst
  have := hmono hs ht hst
  simpa only [schwarzReflect_ofReal] using this

/-- **The shared interval data around the force point** (common part of `r6FaceR_right` and `r6FaceR_left`): with
`J = (v − δ, v + δ)` the collars, the local bounds, the extended transition `G` (continuous on `J`, real there, with
`E_I(G t) = E_O(t)`), its limits, the real-boundary conformality at `v`, and the local agreement of the active
complements at the outer landings. -/
theorem shared_interval_data (hO : O.IsConformal) (hI : I.IsConformal) (hIncl : (I.dom : Set ℂ) ⊆ O.dom)
    {EO EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI : EqOn EI I.2.1 H) (hEIc : ContinuousOn EI Hbar) (v : ℝ)
    {ε : ℝ} (hε : 0 < ε) (hloc : (O.dom : Set ℂ) ∩ ball (EO v) ε ⊆ I.dom)
    {M : ℝ} (hbdd : ∀ w ∈ (I.dom : Set ℂ) ∩ ball (EO v) ε, ‖I.1 w‖ ≤ M) :
    ∃ δ > 0, ∃ g : ℝ → ℝ,
      (∀ x ∈ Ioo (v - δ) (v + δ), ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
        ((pocketTransitionChart O I).dom : Set ℂ)) ∧
      (∀ x ∈ Ioo (v - δ) (v + δ), ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
        ‖(pocketTransitionChart O I).1 z‖ ≤ M) ∧
      (∀ t ∈ Ioo (v - δ) (v + δ), Tendsto (pocketTransitionChart O I).1
        (𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (t : ℂ)) (𝓝 ((g t : ℝ) : ℂ))) ∧
      (∀ t ∈ Ioo (v - δ) (v + δ), EI (g t) = EO t) ∧
      ContinuousOn g (Ioo (v - δ) (v + δ)) ∧
      (∃ r > 0, StrictMonoOn g (Ioo (v - r) (v + r))) ∧
      (∀ t ∈ Ioo (v - δ) (v + δ), ∀ p : ℂ, Tendsto O.2.1 (𝓝[H] (t : ℂ)) (𝓝 p) →
        ∃ ε' > 0, (H \ (I.dom : Set ℂ)) ∩ ball p ε' ⊆ H \ (O.dom : Set ℂ)) := by
  obtain ⟨δ₀, hδ₀, hδ₀E⟩ := Metric.continuousWithinAt_iff.1 (hEOc _ (real_mem_Hbar v)) (ε / 2) (half_pos hε)
  have hnear : ∀ z ∈ Hbar, dist z (v : ℂ) < δ₀ → EO z ∈ ball (EO v) (ε / 2) := fun z hz hd => hδ₀E hz hd
  have hTdom : ((pocketTransitionChart O I).dom : Set ℂ) = O.1 '' (I.dom : Set ℂ) :=
    dom_pocketTransitionChart hO hI hIncl
  set δ := δ₀ / 2 with hδ
  have hδpos : 0 < δ := half_pos hδ₀
  set J : Set ℝ := Ioo (v - δ) (v + δ) with hJ
  have hdist : ∀ x ∈ J, ∀ z : ℂ, dist z (x : ℂ) < δ → dist z (v : ℂ) < δ₀ := by
    intro x hx z hz
    have hxv : dist (x : ℂ) (v : ℂ) < δ := by
      rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_lt_iff]
      constructor <;> linarith [hx.1, hx.2]
    calc dist z (v : ℂ) ≤ dist z (x : ℂ) + dist (x : ℂ) (v : ℂ) := dist_triangle _ _ _
      _ < δ + δ := add_lt_add hz hxv
      _ = δ₀ := by rw [hδ]; ring
  have hball_half : ball (EO v) (ε / 2) ⊆ ball (EO v) ε := ball_subset_ball (half_le_self hε.le)
  -- collars
  have hcollar : ∀ x ∈ J, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((pocketTransitionChart O I).dom : Set ℂ) := by
    intro x hx
    refine ⟨δ, hδpos, fun z hz => ?_⟩
    have hw := hnear z (QuantumZipper.H_subset_Hbar hz.1) (hdist x hx z hz.2)
    rw [hEO hz.1] at hw
    have hwI : O.2.1 z ∈ (I.dom : Set ℂ) := hloc ⟨hO.inv_mem_dom hz.1, hball_half hw⟩
    rw [hTdom]
    exact ⟨_, hwI, hO.2.2 z hz.1⟩
  -- bounds
  have hbound : ∀ x ∈ J, ∃ M : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O I).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O I).1 z‖ ≤ M := by
    intro x hx
    refine ⟨M, ?_⟩
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hδpos), self_mem_nhdsWithin] with z hzb hzT
    rw [hTdom] at hzT
    obtain ⟨w, hwI, rfl⟩ := hzT
    have hwO : w ∈ (O.dom : Set ℂ) := hIncl hwI
    show ‖I.1 (O.2.1 (O.1 w))‖ ≤ M
    rw [hO.inv_fwd hwO]
    refine hbdd w ⟨hwI, hball_half ?_⟩
    have hzH : O.1 w ∈ H := hO.fwd_mem hwO
    have h := hnear (O.1 w) (QuantumZipper.H_subset_Hbar hzH) (hdist x hx _ hzb)
    rwa [hEO hzH, hO.inv_fwd hwO] at h
  have hland : ∀ x ∈ J, Tendsto O.2.1 (𝓝[H] (x : ℂ)) (𝓝 (EO x)) := fun x _ => tendsto_of_extension hEO hEOc x
  obtain ⟨G, hGeq, hGc, hGrb, hGE⟩ := exists_transition_extension_of_inverse_and_bounds hO hI hIncl hEI hEIc
    isOpen_Ioo hcollar hland hbound
  have hGreal : ∀ t ∈ J, (G t).im = 0 := fun t ht => by
    obtain ⟨r, hr, hrb⟩ := hGrb t ht
    exact hrb.2.2.1 t (mem_ball_self hr) (by simp)
  set g : ℝ → ℝ := fun t => (G t).re with hg
  have hGg : ∀ t ∈ J, G t = ((g t : ℝ) : ℂ) := fun t ht =>
    Complex.ext (by simp [hg]) (by simp [hGreal t ht])
  have hvJ : v ∈ J := ⟨by linarith, by linarith⟩
  refine ⟨δ, hδpos, g, hcollar, hbound, fun t ht => ?_, fun t ht => ?_, ?_, ?_, fun t ht p hp => ?_⟩
  · have h1 : ContinuousWithinAt G (((pocketTransitionChart O I).dom : Set ℂ) ∪ Complex.ofReal '' J) t :=
      hGc _ (Or.inr ⟨t, ht, rfl⟩)
    have h2 := (h1.mono subset_union_left).tendsto
    rw [hGg t ht] at h2
    exact h2.congr' (eventually_nhdsWithin_of_forall fun z hz => hGeq hz)
  · rw [← hGg t ht]
    exact hGE t ht
  · have hc : ContinuousOn (fun t : ℝ => G t) J :=
      hGc.comp Complex.continuous_ofReal.continuousOn fun t ht => Or.inr ⟨t, ht, rfl⟩
    exact Complex.continuous_re.comp_continuousOn hc
  · obtain ⟨r₀, hr₀, hrb⟩ := hGrb v hvJ
    exact ⟨r₀, hr₀, strictMonoOn_re_of_isRealBoundaryConformal hrb⟩
  · have := neBot_nhdsWithin_H_real t
    have hpE : p = EO t := tendsto_nhds_unique hp (hland t ht)
    have hpF : EO t ∈ ball (EO v) (ε / 2) := hnear t (real_mem_Hbar t) (hdist t ht t (by simpa using hδpos))
    refine ⟨ε / 2, half_pos hε, fun z hz => ⟨hz.1.1, fun hzO => hz.1.2 (hloc ⟨hzO, ?_⟩)⟩⟩
    rw [hpE] at hz
    have h1 := mem_ball.1 hz.2
    have h2 := mem_ball.1 hpF
    exact mem_ball.2 (by linarith [dist_triangle z (EO t) (EO v)])

/-- **R.6's face, shared side on the right**, from the local inclusion at the outer landing `p_F = E_O(v_R)` of the
right force point, a bound of the inner coordinate there, and the dichotomy of the outer prime ends near `v_R` in the
inner chart: the landing of an outer coordinate at or just left of `v_R` (on the hull) has inner coordinates in
`[w_L, w_R]`, that of an outer coordinate just right of `v_R` (an alive shared-wall point) has none there. -/
theorem r6FaceR_right {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ}
    (hO : O.IsConformal) (hI : I.IsConformal) (hIncl : (I.dom : Set ℂ) ⊆ O.dom)
    {EO EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI : EqOn EI I.2.1 H) (hEIc : ContinuousOn EI Hbar)
    (hvR : 0 < vR 0) (hwR : 0 < wR 0) (hρ : ρR 0 = σR 0)
    {ε : ℝ} (hε : 0 < ε) (hloc : (O.dom : Set ℂ) ∩ ball (EO (vR 0)) ε ⊆ I.dom)
    {M : ℝ} (hbdd : ∀ w ∈ (I.dom : Set ℂ) ∩ ball (EO (vR 0)) ε, ‖I.1 w‖ ≤ M)
    {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hdead : ∀ ξ : ℝ, vR 0 - δ₁ < ξ → ξ ≤ vR 0 → ∀ x : ℝ, EI x = EO ξ → wL 0 ≤ x ∧ x ≤ wR 0)
    (halive : ∀ y : ℝ, vR 0 < y → y < vR 0 + δ₁ → ∀ x : ℝ, EI x = EO y → x < wL 0 ∨ wR 0 < x) :
    R6FaceR ρL ρR σL σR vL vR wL wR O I (H \ (O.dom : Set ℂ)) (H \ (I.dom : Set ℂ)) := by
  set v := vR 0 with hv
  obtain ⟨δ, hδ, g, hcollar, hbound, hlim, hgE, hgc, ⟨r₀, hr₀, hmono⟩, hagree⟩ :=
    shared_interval_data hO hI hIncl hEO hEOc hEI hEIc v hε hloc hbdd
  set J : Set ℝ := Ioo (v - δ) (v + δ) with hJ
  have hvJ : v ∈ J := ⟨by linarith, by linarith⟩
  have hgca : ContinuousAt g v := hgc.continuousAt (isOpen_Ioo.mem_nhds hvJ)
  have hv0 : v ∈ Ioo (v - r₀) (v + r₀) := ⟨by linarith, by linarith⟩
  set m := min (min δ δ₁) r₀ with hm
  have hm0 : 0 < m := lt_min (lt_min hδ hδ₁) hr₀
  have hm1 : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m ≤ r₀ := min_le_right _ _
  obtain ⟨hgvL, hgvR⟩ := hdead v (by linarith) le_rfl _ (hgE v hvJ)
  -- just right of `v` the inner coordinate exceeds `w_R`
  have hright : ∀ y : ℝ, v < y → y < v + m → wR 0 < g y := by
    intro y hy1 hy2
    have hyJ : y ∈ J := ⟨by linarith, by linarith⟩
    have hgy : g v < g y := hmono hv0 ⟨by linarith, by linarith⟩ hy1
    rcases halive y hy1 (by linarith) _ (hgE y hyJ) with h | h
    · linarith
    · exact h
  have hgv_ge : wR 0 ≤ g v := by
    have hev : ∀ᶠ y in 𝓝[>] v, wR 0 ≤ g y := by
      filter_upwards [Ioo_mem_nhdsGT (show v < v + m by linarith)] with y hy
      exact (hright y hy.1 hy.2).le
    exact ge_of_tendsto (hgca.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hgv : g v = wR 0 := le_antisymm hgvR hgv_ge
  obtain ⟨ρ₁, hρ₁, hρ₁g⟩ := Metric.continuousAt_iff.1 hgca (wR 0) hwR
  set θ := min m (min ρ₁ v) / 2 with hθ
  have hθm : θ < min m (min ρ₁ v) := half_lt_self (lt_min hm0 (lt_min hρ₁ hvR))
  have hθpos : 0 < θ := half_pos (lt_min hm0 (lt_min hρ₁ hvR))
  have h1 : θ < m := hθm.trans_le (min_le_left _ _)
  have h4 : θ < ρ₁ := hθm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h5 : θ < v := hθm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set ξ := v - θ with hξ
  have hξJ : ξ ∈ J := ⟨by linarith, by linarith⟩
  have hgξpos : 0 < g ξ := by
    have h := hρ₁g (show dist ξ v < ρ₁ by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    rw [hgv, Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.2]
  have hgξlt : g ξ < wR 0 := hgv ▸ hmono ⟨by linarith, by linarith⟩ hv0 (by linarith)
  set y := v + θ with hy
  have hyJ : y ∈ J := ⟨by linarith, by linarith⟩
  have hgy : wR 0 < g y := hright y (by linarith) (by linarith)
  exact ⟨J, y, g y, ξ, g ξ, isOpen_Ioo, isPreconnected_Ioo, hcollar, hbound, hyJ, hξJ, hlim y hyJ, hlim ξ hξJ,
    Or.inl ⟨by linarith, hgy, hρ⟩, Or.inl ⟨by linarith, by linarith, hgξpos, hgξlt⟩, hagree y hyJ, hagree ξ hξJ⟩

/-- **R.6's face, shared side on the left** (mirror of `r6FaceR_right`). -/
theorem r6FaceR_left {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ}
    (hO : O.IsConformal) (hI : I.IsConformal) (hIncl : (I.dom : Set ℂ) ⊆ O.dom)
    {EO EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI : EqOn EI I.2.1 H) (hEIc : ContinuousOn EI Hbar)
    (hvL : vL 0 < 0) (hwL : wL 0 < 0) (hρ : ρL 0 = σL 0)
    {ε : ℝ} (hε : 0 < ε) (hloc : (O.dom : Set ℂ) ∩ ball (EO (vL 0)) ε ⊆ I.dom)
    {M : ℝ} (hbdd : ∀ w ∈ (I.dom : Set ℂ) ∩ ball (EO (vL 0)) ε, ‖I.1 w‖ ≤ M)
    {δ₁ : ℝ} (hδ₁ : 0 < δ₁)
    (hdead : ∀ ξ : ℝ, vL 0 ≤ ξ → ξ < vL 0 + δ₁ → ∀ x : ℝ, EI x = EO ξ → wL 0 ≤ x ∧ x ≤ wR 0)
    (halive : ∀ y : ℝ, vL 0 - δ₁ < y → y < vL 0 → ∀ x : ℝ, EI x = EO y → x < wL 0 ∨ wR 0 < x) :
    R6FaceR ρL ρR σL σR vL vR wL wR O I (H \ (O.dom : Set ℂ)) (H \ (I.dom : Set ℂ)) := by
  set v := vL 0 with hv
  obtain ⟨δ, hδ, g, hcollar, hbound, hlim, hgE, hgc, ⟨r₀, hr₀, hmono⟩, hagree⟩ :=
    shared_interval_data hO hI hIncl hEO hEOc hEI hEIc v hε hloc hbdd
  set J : Set ℝ := Ioo (v - δ) (v + δ) with hJ
  have hvJ : v ∈ J := ⟨by linarith, by linarith⟩
  have hgca : ContinuousAt g v := hgc.continuousAt (isOpen_Ioo.mem_nhds hvJ)
  have hv0 : v ∈ Ioo (v - r₀) (v + r₀) := ⟨by linarith, by linarith⟩
  set m := min (min δ δ₁) r₀ with hm
  have hm0 : 0 < m := lt_min (lt_min hδ hδ₁) hr₀
  have hm1 : m ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m ≤ δ₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m ≤ r₀ := min_le_right _ _
  obtain ⟨hgvL, hgvR⟩ := hdead v le_rfl (by linarith) _ (hgE v hvJ)
  have hleft : ∀ y : ℝ, v - m < y → y < v → g y < wL 0 := by
    intro y hy1 hy2
    have hyJ : y ∈ J := ⟨by linarith, by linarith⟩
    have hgy : g y < g v := hmono ⟨by linarith, by linarith⟩ hv0 hy2
    rcases halive y (by linarith) hy2 _ (hgE y hyJ) with h | h
    · exact h
    · linarith
  have hgv_le : g v ≤ wL 0 := by
    have hev : ∀ᶠ y in 𝓝[<] v, g y ≤ wL 0 := by
      filter_upwards [Ioo_mem_nhdsLT (show v - m < v by linarith)] with y hy
      exact (hleft y hy.1 hy.2).le
    exact le_of_tendsto (hgca.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hgv : g v = wL 0 := le_antisymm hgv_le hgvL
  have hwL' : 0 < -wL 0 := by linarith
  obtain ⟨ρ₁, hρ₁, hρ₁g⟩ := Metric.continuousAt_iff.1 hgca (-wL 0) hwL'
  have hvpos : 0 < -v := by linarith
  set θ := min m (min ρ₁ (-v)) / 2 with hθ
  have hθm : θ < min m (min ρ₁ (-v)) := half_lt_self (lt_min hm0 (lt_min hρ₁ hvpos))
  have hθpos : 0 < θ := half_pos (lt_min hm0 (lt_min hρ₁ hvpos))
  have h1 : θ < m := hθm.trans_le (min_le_left _ _)
  have h4 : θ < ρ₁ := hθm.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h5 : θ < -v := hθm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set ξ := v + θ with hξ
  have hξJ : ξ ∈ J := ⟨by linarith, by linarith⟩
  have hgξneg : g ξ < 0 := by
    have h := hρ₁g (show dist ξ v < ρ₁ by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith)
    rw [hgv, Real.dist_eq, abs_sub_lt_iff] at h
    linarith [h.1]
  have hgξgt : wL 0 < g ξ := hgv ▸ hmono hv0 ⟨by linarith, by linarith⟩ (by linarith)
  set y := v - θ with hy
  have hyJ : y ∈ J := ⟨by linarith, by linarith⟩
  have hgy : g y < wL 0 := hleft y (by linarith) (by linarith)
  exact ⟨J, y, g y, ξ, g ξ, isOpen_Ioo, isPreconnected_Ioo, hcollar, hbound, hyJ, hξJ, hlim y hyJ, hlim ξ hξJ,
    Or.inr ⟨by linarith, hgy, hρ⟩, Or.inr ⟨by linarith, by linarith, hgξgt, hgξneg⟩, hagree y hyJ, hagree ξ hξJ⟩

end InteractingSLE.Sec7.R6Fc

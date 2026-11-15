/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior

/-!
# §A.4.2, deterministic part: the open driver sides through a restart

Packet PROVE-ZHAN-GT4-A2. Source: Astra, *Follow-up proofs and dependency audit*, §A.4.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L743–L777, ruling R38):

> Restart at `T`. The fresh ordinary SLE has positive conditional probability of swallowing the negative point
> `g_T(−n) − W` before the positive point `q` … On that event every point of `[q, d − W]` is still unswallowed by
> the fresh chain, so its map `h` extends analytically across a neighborhood of that interval and is strictly
> increasing there. The original continued process stopped when the deterministic point `−n` is first swallowed
> has a simple crosscut boundary, by §A.3. Its inverse map is `f ∘ (W + h⁻¹)`. On the retained interval one
> therefore has the exact relation `f(W + u) = f_{T+σ}(W + h_σ(u))` … the displayed coordinates for
> `q ≤ u < d − W` lie strictly inside the new hull interval.

This file proves that paragraph for a fixed driver. With `V = W_{T+·} − W_T` the fresh driver:

* `realSwallowAt_add_of_shift`: if `x` is alive at `T` and the fresh chain swallows `g_T(x) − W_T` at `σ`, the
  original chain swallows `x` at `T + σ`;
* `tendsto_fwdMapInv_of_isForwardSol_shift`: if `u` is alive for the fresh chain at time `σ` (solution `w`),
  `f_T(u) = F_{T+σ}(w σ)` as a boundary value, where `F_{T+σ}` is any continuous extension of `f_{T+σ}` to `ℍ̄`;
* `not_mem_exteriorCoords_add_of_pos` / `…_of_neg`: if moreover `u` is off the exterior coordinates at `T`, its
  fresh image `w σ` is off the exterior coordinates at `T + σ` (the fresh real flow is strictly increasing on each
  side of the driver);
* `exists_tendsto_fwdMapInv_of_restart_pos` / `…_neg`: **the deterministic §A.4.2** — if `−n` is alive at `T`,
  the fresh chain swallows `g_T(−n) − W_T` while `q > 0` is alive, the hull at the first swallowing of `−n` is
  bounded by a crosscut with ends on both sides of `0`, and `f_{T+σ}` extends continuously to `ℍ̄`, then for every
  `u ≥ q` off the exterior coordinates at `T`, `f_T` has a boundary value at `u` and it lies in `ℍ` (and the
  reflected statement on the left).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Bornology

namespace InteractingSLE.ZhanGT4

open QuantumZipper

variable {W : ℝ → ℝ}

/-! ### Swallowing through a restart -/

/-- **Swallowing times add along a restart.** -/
theorem realSwallowAt_add_of_shift (hW : Continuous W) {x T σ : ℝ} (hT : 0 ≤ T) {u₀ : ℝ → ℂ}
    (hu₀ : IsForwardSol W (x : ℂ) T u₀) {p : ℝ} (hp : u₀ T = (p : ℂ))
    (hsw : RealSwallowAt (fun r => W (T + r) - W T) p σ) : RealSwallowAt W x (T + σ) := by
  obtain ⟨hσ, halive, hdead⟩ := hsw
  refine ⟨by linarith, fun s hs => ?_, ?_⟩
  · rcases le_or_gt s T with hsT | hsT
    · exact ⟨u₀, isForwardSol_restrict hu₀ hs.1 hsT⟩
    · obtain ⟨v, hv⟩ := halive (s - T) ⟨by linarith, by linarith [hs.2]⟩
      rw [← hp] at hv
      have := isForwardSol_glue hT (by linarith) hu₀ hv
      rw [add_sub_cancel] at this
      exact ⟨_, this⟩
  · rintro ⟨w, hw⟩
    have hsh := isForwardSol_shift hw hT hσ.le
    have hwT : w T = u₀ T :=
      eqOn_of_isForwardSol hW (isForwardSol_restrict hw hT (by linarith)) hu₀ ⟨hT, le_rfl⟩
    rw [hwT, hp] at hsh
    exact hdead ⟨_, hsh⟩

/-- The real flow at `T + σ` is the fresh flow at `σ` of the real flow at `T`. -/
theorem exists_isForwardSol_shift_of_add (hW : Continuous W) {x T σ : ℝ} (hT : 0 ≤ T) (hσ : 0 ≤ σ)
    {w : ℝ → ℂ} (hw : IsForwardSol W (x : ℂ) (T + σ) w) :
    ∃ v, IsForwardSol (fun r => W (T + r) - W T) (fwdMap W T x) σ v ∧ fwdMap W (T + σ) x = v σ := by
  refine ⟨fun r => w (T + r), ?_, ?_⟩
  · rw [fwdMap_eq_of_isForwardSol hW hw ⟨hT, by linarith⟩]
    exact isForwardSol_shift hw hT hσ
  · exact fwdMap_eq_of_isForwardSol hW hw ⟨by linarith, le_rfl⟩

/-! ### The boundary value through the fresh chain -/

/-- **`f_T(u) = F_{T+σ}(h_σ(u))`** for a real `u` alive for the fresh chain at time `σ`. -/
theorem tendsto_fwdMapInv_of_isForwardSol_shift (hW : Continuous W) (hW0 : W 0 = 0) {T σ : ℝ} (hT : 0 ≤ T)
    (hσ : 0 ≤ σ) {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W (T + σ)) H) (hFc : ContinuousOn F Hbar) {u : ℝ}
    {w : ℝ → ℂ} (hw : IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w) :
    Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 (F (w σ))) := by
  set V : ℝ → ℝ := fun r => W (T + r) - W T with hV
  have hVc : Continuous V := by fun_prop
  have hV0 : V 0 = 0 := by simp [hV]
  have hnear := eventually_not_mem_fwdHull hVc hσ hw
  have hcomp : ∀ᶠ z in 𝓝[H] (u : ℂ), fwdMapInv W T z = F (fwdMap V σ z) := by
    filter_upwards [hnear] with z hz
    have hfz : fwdMap V σ z ∈ H := FwdHolo.mapsTo_fwdMap hVc hσ hz
    rw [hFeq hfz, RS.fwdMapInv_add_shift hW hW0 hT hσ hfz]
    congr 1
    exact (RS.fwdMapInv_fwdMap hVc hV0 hσ hz).symm
  have hlim := tendsto_fwdMap_of_isForwardSol hVc hσ hw
  have hmem : w σ ∈ Hbar := by
    have : closure H = Hbar := closure_H
    rw [← this]
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := (u : ℂ)) (by simp)
    exact mem_closure_of_tendsto hlim (by filter_upwards [hnear] with z hz using FwdHolo.mapsTo_fwdMap hVc hσ hz)
  have hlim' : Tendsto (fwdMap V σ) (𝓝[H] (u : ℂ)) (𝓝[Hbar] (w σ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, by
      filter_upwards [hnear] with z hz using (le_of_lt (FwdHolo.mapsTo_fwdMap hVc hσ hz) : (0 : ℝ) ≤ _)⟩
  exact ((hFc (w σ) hmem).tendsto.comp hlim').congr' (hcomp.mono fun z hz => hz.symm)

/-! ### Exterior coordinates through a restart -/

/-- Membership in the generating set of the exterior coordinates. -/
theorem mem_exteriorCoords_of_isForwardSol {x T : ℝ} {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) :
    (fwdMap W T x).re ∈ exteriorCoords W T :=
  subset_closure ⟨x, ⟨u, hu⟩, rfl⟩

/-- The centered real flow of a negative point stays negative. -/
theorem re_fwdMap_neg (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hx : x < 0) {v : ℝ → ℂ}
    (hv : IsForwardSol W (x : ℂ) T v) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : (fwdMap W t x).re < 0 := by
  obtain ⟨m, hm, hle⟩ := exists_pos_re_le_neg_of_isForwardSol hW hW0 hx (ht.1.trans ht.2) hv
  rw [fwdMap_eq_of_isForwardSol hW hv ht]
  linarith [hle t ht]

/-- **The positive retained side stays off the exterior coordinates.** If `u > 0` is off the exterior coordinates
at `T` and alive for the fresh chain at `σ > 0` (solution `w`), then `w σ` is off the exterior coordinates at
`T + σ`: the fresh real flow is strictly increasing on the positive alive points and keeps negative points
negative. -/
theorem not_mem_exteriorCoords_add_of_pos (hW : Continuous W) {T σ : ℝ} (hT : 0 ≤ T)
    (hσ : 0 < σ) {u : ℝ} (hu : 0 < u) (hext : u ∉ exteriorCoords W T) {w : ℝ → ℂ}
    (hw : IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w) : (w σ).re ∉ exteriorCoords W (T + σ) := by
  set V : ℝ → ℝ := fun r => W (T + r) - W T with hV
  have hVc : Continuous V := by fun_prop
  have hV0 : V 0 = 0 := by simp [hV]
  have hσI : σ ∈ Icc (0 : ℝ) σ := ⟨hσ.le, le_rfl⟩
  -- a gap around `u` in the exterior coordinates at `T`
  obtain ⟨ε, hε, hgap⟩ : ∃ ε > (0 : ℝ), ∀ x : ℝ, (∃ v, IsForwardSol W (x : ℂ) T v) →
      ε ≤ |(fwdMap W T x).re - u| := by
    by_contra hc
    push Not at hc
    refine hext (Metric.mem_closure_iff.2 fun ε hε => ?_)
    obtain ⟨x, hx, hlt⟩ := hc ε hε
    exact ⟨_, ⟨x, hx, rfl⟩, by rw [Real.dist_eq, abs_sub_comm]; exact hlt⟩
  have hwpos : 0 < (w σ).re := by
    rw [← fwdMap_eq_of_isForwardSol hVc hw hσI]; exact re_fwdMap_pos hVc hV0 hu hw hσI
  -- the right comparison point
  obtain ⟨wb, hwb⟩ := RS.exists_isForwardSol_of_lt hVc hσ.le (by rw [hV0]; exact hu)
    (show u < u + ε / 2 by linarith) hw
  have hδp : (w σ).re < (wb σ).re := re_lt_of_isForwardSol hVc hV0 hu (by linarith) hw hwb σ hσI
  -- the left comparison
  obtain ⟨δm, hδm, hδmw, hleft⟩ : ∃ δm > (0 : ℝ), δm ≤ (w σ).re ∧ ∀ a : ℝ, 0 < a → a ≤ u - ε →
      ∀ va : ℝ → ℂ, IsForwardSol V (a : ℂ) σ va → (va σ).re ≤ (w σ).re - δm := by
    by_cases hc : ∃ wc : ℝ → ℂ, 0 < u - ε / 2 ∧ IsForwardSol V ((u - ε / 2 : ℝ) : ℂ) σ wc
    · obtain ⟨wc, hc0, hwc⟩ := hc
      have hlt : (wc σ).re < (w σ).re := re_lt_of_isForwardSol hVc hV0 hc0 (by linarith) hwc hw σ hσI
      have hwcpos : 0 < (wc σ).re := by
        rw [← fwdMap_eq_of_isForwardSol hVc hwc hσI]; exact re_fwdMap_pos hVc hV0 hc0 hwc hσI
      refine ⟨(w σ).re - (wc σ).re, by linarith, by linarith, fun a ha hau va hva => ?_⟩
      have := re_lt_of_isForwardSol hVc hV0 ha (show a < u - ε / 2 by linarith) hva hwc σ hσI
      linarith
    · refine ⟨(w σ).re, hwpos, le_rfl, fun a ha hau va hva => ?_⟩
      exfalso
      obtain ⟨wc, hwc⟩ := RS.exists_isForwardSol_of_lt hVc hσ.le (by rw [hV0]; exact ha)
        (show a < u - ε / 2 by linarith) hva
      exact hc ⟨wc, by linarith, hwc⟩
  intro hmem
  obtain ⟨r, ⟨x, ⟨wx, hwx⟩, rfl⟩, hr⟩ := Metric.mem_closure_iff.1 hmem (min ((wb σ).re - (w σ).re) δm)
    (lt_min (by linarith) hδm)
  rw [Real.dist_eq] at hr
  obtain ⟨va, hva, hfa⟩ := exists_isForwardSol_shift_of_add hW hT hσ.le hwx
  have hxT : ∃ v, IsForwardSol W (x : ℂ) T v := ⟨wx, isForwardSol_restrict hwx hT (by linarith)⟩
  obtain ⟨vx, hvx⟩ := hxT
  set a := (fwdMap W T x).re with ha
  have haeq : fwdMap W T x = (a : ℂ) := fwdMap_eq_ofReal_re hW hvx ⟨hT, le_rfl⟩
  rw [haeq] at hva
  have hgapa := hgap x ⟨vx, hvx⟩
  rw [← ha] at hgapa
  rw [hfa] at hr
  rcases lt_trichotomy a 0 with ha0 | ha0 | ha0
  · have := re_fwdMap_neg hVc hV0 ha0 hva hσI
    rw [fwdMap_eq_of_isForwardSol hVc hva hσI] at this
    have h1 := min_le_right ((wb σ).re - (w σ).re) δm
    rw [abs_lt] at hr
    linarith [hr.1]
  · rw [ha0, Complex.ofReal_zero] at hva
    exact not_isForwardSol_zero hV0 hσ.le hva
  · rcases le_or_gt (u + ε) a with hau | hau
    · have := re_lt_of_isForwardSol hVc hV0 (show 0 < u + ε / 2 by linarith) (by linarith) hwb hva σ hσI
      have h1 := min_le_left ((wb σ).re - (w σ).re) δm
      rw [abs_lt] at hr
      linarith [hr.2]
    · have hau' : a ≤ u - ε := by
        rcases le_or_gt a u with h | h
        · rw [abs_of_nonpos (by linarith)] at hgapa; linarith
        · rw [abs_of_pos (by linarith)] at hgapa; linarith
      have := hleft a ha0 hau' va hva
      have h1 := min_le_right ((wb σ).re - (w σ).re) δm
      rw [abs_lt] at hr
      linarith [hr.1]

/-- Exterior coordinates of the reflected driver. -/
theorem mem_exteriorCoords_neg_iff (hW : Continuous W) {T r : ℝ} (hT : 0 ≤ T) :
    r ∈ exteriorCoords (fun t => -W t) T ↔ -r ∈ exteriorCoords W T := by
  have hset : {r : ℝ | ∃ x : ℝ, (∃ v, IsForwardSol (fun t => -W t) (x : ℂ) T v) ∧
      (fwdMap (fun t => -W t) T x).re = r} =
      -{r : ℝ | ∃ x : ℝ, (∃ v, IsForwardSol W (x : ℂ) T v) ∧ (fwdMap W T x).re = r} := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_neg]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : ∃ v, IsForwardSol W ((-x : ℝ) : ℂ) T v := by
        rw [← exists_isForwardSol_neg_iff (W := W), neg_neg]; exact hx
      obtain ⟨v, hv⟩ := hx'
      refine ⟨-x, ⟨v, hv⟩, ?_⟩
      have := fwdMap_neg_real hW hv ⟨hT, le_rfl⟩
      rw [neg_neg] at this
      rw [this, neg_re]; ring
    · rintro ⟨x, ⟨v, hv⟩, hr⟩
      refine ⟨-x, ?_, ?_⟩
      · rw [exists_isForwardSol_neg_iff]; exact ⟨v, hv⟩
      · rw [fwdMap_neg_real hW hv ⟨hT, le_rfl⟩, neg_re, hr, neg_neg]
  unfold exteriorCoords
  rw [hset, Metric.mem_closure_iff, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨b, hb, hd⟩ := h ε hε
    exact ⟨-b, hb, by rw [Real.dist_eq] at hd ⊢; rw [← abs_neg]; ring_nf; ring_nf at hd; linarith [abs_sub_comm r b,
      show |(-r) - (-b)| = |r - b| by rw [← abs_neg]; ring_nf]⟩
  · intro h ε hε
    obtain ⟨b, hb, hd⟩ := h ε hε
    refine ⟨-b, by rw [Set.mem_neg, neg_neg]; exact hb, ?_⟩
    rw [Real.dist_eq] at hd ⊢
    have : r - -b = -(-r - b) := by ring
    rw [this, abs_neg]; exact hd

/-- **The negative retained side stays off the exterior coordinates** (reflection of
`not_mem_exteriorCoords_add_of_pos`). -/
theorem not_mem_exteriorCoords_add_of_neg (hW : Continuous W) {T σ : ℝ} (hT : 0 ≤ T) (hσ : 0 < σ) {u : ℝ}
    (hu : u < 0) (hext : u ∉ exteriorCoords W T) {w : ℝ → ℂ}
    (hw : IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w) : (w σ).re ∉ exteriorCoords W (T + σ) := by
  have hw' : IsForwardSol (fun r => (fun t => -W t) (T + r) - (fun t => -W t) T) ((-u : ℝ) : ℂ) σ
      (fun t => -w t) := by
    have h := RS.isForwardSol_neg hw
    rw [← Complex.ofReal_neg] at h
    refine (isForwardSol_congr_drive (fun r _ => ?_)).1 h
    ring
  have hext' : -u ∉ exteriorCoords (fun t => -W t) T := by
    rw [mem_exteriorCoords_neg_iff hW hT, neg_neg]; exact hext
  have h := not_mem_exteriorCoords_add_of_pos (W := fun t => -W t) (by fun_prop) hT hσ (neg_pos.2 hu)
    hext' hw'
  rwa [mem_exteriorCoords_neg_iff hW (by linarith), neg_re, neg_neg] at h

/-! ### The deterministic §A.4.2 -/

/-- **The generic step**: a fresh-alive coordinate whose fresh image is off the exterior coordinates at a time
`T + σ` where the hull is bounded by a crosscut with ends on both sides of `0` has an interior boundary value. -/
theorem exists_tendsto_fwdMapInv_of_crosscut_shift (hW : Continuous W) (hW0 : W 0 = 0) {T σ : ℝ}
    (hT : 0 ≤ T) (hσ : 0 < σ) {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W (T + σ)) H)
    (hFc : ContinuousOn F Hbar) (hFb : ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W (T + σ)) {γ : ℝ → ℂ}
    (hγ : IsRealCrosscut γ) (h0 : (γ 0).re < 0) (h1 : 0 < (γ 1).re)
    (hfr : frontier (H \ fwdHull W (T + σ)) ∩ H = γ '' Ioo 0 1) {u : ℝ} {w : ℝ → ℂ}
    (hw : IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w)
    (hwext : (w σ).re ∉ exteriorCoords W (T + σ)) :
    ∃ P ∈ H, Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 P) := by
  have hVc : Continuous fun r => W (T + r) - W T := by fun_prop
  have hwr : w σ = ((w σ).re : ℂ) := by
    rw [← fwdMap_eq_of_isForwardSol hVc hw ⟨hσ.le, le_rfl⟩]
    exact fwdMap_eq_ofReal_re hVc hw ⟨hσ.le, le_rfl⟩
  refine ⟨F (w σ), ?_, tendsto_fwdMapInv_of_isForwardSol_shift hW hW0 hT hσ.le hFeq hFc hw⟩
  rw [hwr]
  exact mem_H_of_frontier_eq_crosscut hW hW0 (by linarith) hFeq hFc hFb hγ h0 h1 hfr hwext

/-- The data of §A.3 at the first swallowing time `σ₀` of a real point `x`: a simple crosscut `γ` with ends on both
sides of `0` bounding the hull, and a continuous extension `F` of `f_{σ₀}` to `ℍ̄` with real boundary values off
`ℍ \ K_{σ₀}`. -/
structure CrosscutAt (W : ℝ → ℝ) (σ₀ : ℝ) (F : ℂ → ℂ) (γ : ℝ → ℂ) : Prop where
  eqOn : EqOn F (fwdMapInv W σ₀) H
  continuousOn : ContinuousOn F Hbar
  bdry : ∀ x : ℂ, x.im = 0 → F x ∉ H \ fwdHull W σ₀
  crosscut : IsRealCrosscut γ
  re_zero_neg : (γ 0).re < 0
  re_one_pos : 0 < (γ 1).re
  frontier_eq : frontier (H \ fwdHull W σ₀) ∩ H = γ '' Ioo 0 1

/-- **§A.4.2, deterministic, right side.** Let `x` be alive at `T`, let the fresh chain swallow `g_T(x) − W_T` at
`σ` while `q > 0` is still alive, and let the hull at the first swallowing time `σ₀` of `x` be bounded by a crosscut
(`CrosscutAt`). Then every `u ≥ q` off the exterior coordinates at `T` has an interior boundary value of `f_T`. -/
theorem exists_tendsto_fwdMapInv_of_restart_pos (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ} {u₀ : ℝ → ℂ} (hu₀ : IsForwardSol W (x : ℂ) T u₀) {σ : ℝ}
    (hsw : RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ) {q : ℝ} (hq : 0 < q)
    (hqa : ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v) {σ₀ : ℝ} (hσ₀ : RealSwallowAt W x σ₀)
    {F : ℂ → ℂ} {γ : ℝ → ℂ} (hC : CrosscutAt W σ₀ F γ) {u : ℝ} (hqu : q ≤ u)
    (hu : u ∉ exteriorCoords W T) : ∃ P ∈ H, Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 P) := by
  have hVc : Continuous fun r => W (T + r) - W T := by fun_prop
  have hσ := hsw.1
  have hp : u₀ T = (((fwdMap W T x).re : ℝ) : ℂ) := by
    rw [← fwdMap_eq_ofReal_re hW hu₀ ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu₀ ⟨hT, le_rfl⟩]
  have hσeq : σ₀ = T + σ := hσ₀.eq (realSwallowAt_add_of_shift hW hT hu₀ hp hsw)
  subst hσeq
  obtain ⟨v, hv⟩ := hqa
  obtain ⟨w, hw⟩ : ∃ w, IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w := by
    rcases eq_or_lt_of_le hqu with h | h
    · exact ⟨v, h ▸ hv⟩
    · exact RS.exists_isForwardSol_of_lt hVc hσ.le (by simp; exact hq) h hv
  exact exists_tendsto_fwdMapInv_of_crosscut_shift hW hW0 hT hσ hC.eqOn hC.continuousOn hC.bdry hC.crosscut
    hC.re_zero_neg hC.re_one_pos hC.frontier_eq hw
    (not_mem_exteriorCoords_add_of_pos hW hT hσ (by linarith) hu hw)

/-- **§A.4.2, deterministic, left side** (the reflection of `exists_tendsto_fwdMapInv_of_restart_pos`): `q < 0`
alive for the fresh chain when it swallows `g_T(x) − W_T`, and `u ≤ q`. -/
theorem exists_tendsto_fwdMapInv_of_restart_neg (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ} {u₀ : ℝ → ℂ} (hu₀ : IsForwardSol W (x : ℂ) T u₀) {σ : ℝ}
    (hsw : RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ) {q : ℝ} (hq : q < 0)
    (hqa : ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v) {σ₀ : ℝ} (hσ₀ : RealSwallowAt W x σ₀)
    {F : ℂ → ℂ} {γ : ℝ → ℂ} (hC : CrosscutAt W σ₀ F γ) {u : ℝ} (hqu : u ≤ q)
    (hu : u ∉ exteriorCoords W T) : ∃ P ∈ H, Tendsto (fwdMapInv W T) (𝓝[H] (u : ℂ)) (𝓝 P) := by
  have hVc : Continuous fun r => W (T + r) - W T := by fun_prop
  have hσ := hsw.1
  have hp : u₀ T = (((fwdMap W T x).re : ℝ) : ℂ) := by
    rw [← fwdMap_eq_ofReal_re hW hu₀ ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu₀ ⟨hT, le_rfl⟩]
  have hσeq : σ₀ = T + σ := hσ₀.eq (realSwallowAt_add_of_shift hW hT hu₀ hp hsw)
  subst hσeq
  obtain ⟨w, hw⟩ : ∃ w, IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w := by
    rcases eq_or_lt_of_le hqu with h | h
    · exact h ▸ hqa
    · rw [← exists_isForwardSol_neg_iff] at hqa ⊢
      obtain ⟨v, hv⟩ := hqa
      exact RS.exists_isForwardSol_of_lt hVc.neg hσ.le (by simp; linarith) (by linarith) hv
  exact exists_tendsto_fwdMapInv_of_crosscut_shift hW hW0 hT hσ hC.eqOn hC.continuousOn hC.bdry hC.crosscut
    hC.re_zero_neg hC.re_one_pos hC.frontier_eq hw
    (not_mem_exteriorCoords_add_of_neg hW hT hσ (by linarith) hu hw)

/-! ### Injectivity of the retained sides -/

/-- The fresh real flow is strictly increasing on negative alive points too. -/
theorem re_lt_of_isForwardSol_neg (hW : Continuous W) (hW0 : W 0 = 0) {x y T : ℝ} (hy : y < 0) (hxy : x < y)
    {v w : ℝ → ℂ} (hv : IsForwardSol W (x : ℂ) T v) (hw : IsForwardSol W (y : ℂ) T w) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : (v t).re < (w t).re := by
  have hv' := RS.isForwardSol_neg hv
  have hw' := RS.isForwardSol_neg hw
  rw [← Complex.ofReal_neg] at hv' hw'
  have := re_lt_of_isForwardSol (W := fun t => -W t) hW.neg (by simp [hW0]) (neg_pos.2 hy) (by linarith) hw' hv' t ht
  simp only [neg_re] at this
  linarith

/-- **Injectivity through the restart.** If `u₁, u₂` are alive for the fresh chain at `σ` on the same side of the
driver, and `F_{T+σ}` is injective on `ℝ`, then equal boundary values of `f_T` at `u₁, u₂` force `u₁ = u₂`. -/
theorem eq_of_tendsto_fwdMapInv_shift (hW : Continuous W) (hW0 : W 0 = 0) {T σ : ℝ} (hT : 0 ≤ T) (hσ : 0 < σ)
    {F : ℂ → ℂ} (hFeq : EqOn F (fwdMapInv W (T + σ)) H) (hFc : ContinuousOn F Hbar)
    (hFi : Function.Injective fun v : ℝ => F v) {u₁ u₂ : ℝ} (hside : 0 < u₁ * u₂) {w₁ w₂ : ℝ → ℂ}
    (hw₁ : IsForwardSol (fun r => W (T + r) - W T) (u₁ : ℂ) σ w₁)
    (hw₂ : IsForwardSol (fun r => W (T + r) - W T) (u₂ : ℂ) σ w₂) {p₁ p₂ : ℂ}
    (h₁ : Tendsto (fwdMapInv W T) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁)) (h₂ : Tendsto (fwdMapInv W T) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂))
    (hp : p₁ = p₂) : u₁ = u₂ := by
  have hVc : Continuous fun r => W (T + r) - W T := by fun_prop
  have hV0 : (fun r => W (T + r) - W T) 0 = 0 := by simp
  have hσI : σ ∈ Icc (0 : ℝ) σ := ⟨hσ.le, le_rfl⟩
  have hreal : ∀ {u : ℝ} {w : ℝ → ℂ}, IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w →
      w σ = ((w σ).re : ℂ) := fun {u w} hw => by
    rw [← fwdMap_eq_of_isForwardSol hVc hw hσI]; exact fwdMap_eq_ofReal_re hVc hw hσI
  have hl₁ := tendsto_fwdMapInv_of_isForwardSol_shift hW hW0 hT hσ.le hFeq hFc hw₁
  have hl₂ := tendsto_fwdMapInv_of_isForwardSol_shift hW hW0 hT hσ.le hFeq hFc hw₂
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (u₁ : ℂ)) (by simp)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (u₂ : ℂ)) (by simp)
  have he₁ := tendsto_nhds_unique h₁ hl₁
  have he₂ := tendsto_nhds_unique h₂ hl₂
  rw [he₁, he₂, hreal hw₁, hreal hw₂] at hp
  have hre := hFi hp
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · rcases lt_or_gt_of_ne (show u₁ ≠ 0 by rintro rfl; simp at hside) with h0 | h0
    · have : u₂ < 0 := by nlinarith
      exact absurd hre (re_lt_of_isForwardSol_neg hVc hV0 this hlt hw₁ hw₂ hσI).ne
    · exact absurd hre (re_lt_of_isForwardSol hVc hV0 h0 hlt hw₁ hw₂ σ hσI).ne
  · rcases lt_or_gt_of_ne (show u₂ ≠ 0 by rintro rfl; simp at hside) with h0 | h0
    · have : u₁ < 0 := by nlinarith
      exact absurd hre.symm (re_lt_of_isForwardSol_neg hVc hV0 this hlt hw₂ hw₁ hσI).ne
    · exact absurd hre.symm (re_lt_of_isForwardSol hVc hV0 h0 hlt hw₂ hw₁ σ hσI).ne

/-- **§A.4.2, deterministic, injectivity on the right**: under the hypotheses of
`exists_tendsto_fwdMapInv_of_restart_pos`, equal boundary values of `f_T` at `u₁, u₂ ≥ q` force `u₁ = u₂`. -/
theorem eq_of_restart_pos (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ} {u₀ : ℝ → ℂ} (hu₀ : IsForwardSol W (x : ℂ) T u₀) {σ : ℝ}
    (hsw : RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ) {q : ℝ} (hq : 0 < q)
    (hqa : ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v) {σ₀ : ℝ} (hσ₀ : RealSwallowAt W x σ₀)
    {F : ℂ → ℂ} {γ : ℝ → ℂ} (hC : CrosscutAt W σ₀ F γ) {u₁ u₂ : ℝ} (hq₁ : q ≤ u₁) (hq₂ : q ≤ u₂) {p₁ p₂ : ℂ}
    (h₁ : Tendsto (fwdMapInv W T) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁)) (h₂ : Tendsto (fwdMapInv W T) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂))
    (hp : p₁ = p₂) : u₁ = u₂ := by
  have hVc : Continuous fun r => W (T + r) - W T := by fun_prop
  have hσ := hsw.1
  have hp' : u₀ T = (((fwdMap W T x).re : ℝ) : ℂ) := by
    rw [← fwdMap_eq_ofReal_re hW hu₀ ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu₀ ⟨hT, le_rfl⟩]
  have hσeq : σ₀ = T + σ := hσ₀.eq (realSwallowAt_add_of_shift hW hT hu₀ hp' hsw)
  subst hσeq
  obtain ⟨v, hv⟩ := hqa
  have halive : ∀ {u : ℝ}, q ≤ u → ∃ w, IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w := by
    intro u hqu
    rcases eq_or_lt_of_le hqu with h | h
    · exact ⟨v, h ▸ hv⟩
    · exact RS.exists_isForwardSol_of_lt hVc hσ.le (by simp; exact hq) h hv
  obtain ⟨w₁, hw₁⟩ := halive hq₁
  obtain ⟨w₂, hw₂⟩ := halive hq₂
  have hinj := injective_of_frontier_eq_crosscut hW hW0 (by linarith) hC.eqOn hC.continuousOn hC.bdry
    hC.crosscut (by linarith [hC.re_zero_neg, hC.re_one_pos]) hC.frontier_eq
  exact eq_of_tendsto_fwdMapInv_shift hW hW0 hT hσ hC.eqOn hC.continuousOn hinj
    (mul_pos (by linarith) (by linarith)) hw₁ hw₂ h₁ h₂ hp

/-- **§A.4.2, deterministic, injectivity on the left** (reflection of `eq_of_restart_pos`). -/
theorem eq_of_restart_neg (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {x : ℝ} {u₀ : ℝ → ℂ} (hu₀ : IsForwardSol W (x : ℂ) T u₀) {σ : ℝ}
    (hsw : RealSwallowAt (fun r => W (T + r) - W T) (fwdMap W T x).re σ) {q : ℝ} (hq : q < 0)
    (hqa : ∃ v, IsForwardSol (fun r => W (T + r) - W T) (q : ℂ) σ v) {σ₀ : ℝ} (hσ₀ : RealSwallowAt W x σ₀)
    {F : ℂ → ℂ} {γ : ℝ → ℂ} (hC : CrosscutAt W σ₀ F γ) {u₁ u₂ : ℝ} (hq₁ : u₁ ≤ q) (hq₂ : u₂ ≤ q) {p₁ p₂ : ℂ}
    (h₁ : Tendsto (fwdMapInv W T) (𝓝[H] (u₁ : ℂ)) (𝓝 p₁)) (h₂ : Tendsto (fwdMapInv W T) (𝓝[H] (u₂ : ℂ)) (𝓝 p₂))
    (hp : p₁ = p₂) : u₁ = u₂ := by
  have hVc : Continuous fun r => W (T + r) - W T := by fun_prop
  have hσ := hsw.1
  have hp' : u₀ T = (((fwdMap W T x).re : ℝ) : ℂ) := by
    rw [← fwdMap_eq_ofReal_re hW hu₀ ⟨hT, le_rfl⟩, fwdMap_eq_of_isForwardSol hW hu₀ ⟨hT, le_rfl⟩]
  have hσeq : σ₀ = T + σ := hσ₀.eq (realSwallowAt_add_of_shift hW hT hu₀ hp' hsw)
  subst hσeq
  have halive : ∀ {u : ℝ}, u ≤ q → ∃ w, IsForwardSol (fun r => W (T + r) - W T) (u : ℂ) σ w := by
    intro u hqu
    rcases eq_or_lt_of_le hqu with h | h
    · exact h ▸ hqa
    · have hqa' := hqa
      rw [← exists_isForwardSol_neg_iff] at hqa' ⊢
      obtain ⟨v, hv⟩ := hqa'
      exact RS.exists_isForwardSol_of_lt hVc.neg hσ.le (by simp; linarith) (by linarith) hv
  obtain ⟨w₁, hw₁⟩ := halive hq₁
  obtain ⟨w₂, hw₂⟩ := halive hq₂
  have hinj := injective_of_frontier_eq_crosscut hW hW0 (by linarith) hC.eqOn hC.continuousOn hC.bdry
    hC.crosscut (by linarith [hC.re_zero_neg, hC.re_one_pos]) hC.frontier_eq
  exact eq_of_tendsto_fwdMapInv_shift hW hW0 hT hσ hC.eqOn hC.continuousOn hinj
    (mul_pos_of_neg_of_neg (by linarith) (by linarith)) hw₁ hw₂ h₁ h₂ hp

end InteractingSLE.ZhanGT4

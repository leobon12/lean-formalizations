/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TerminalEscape
import InteractingSLE.Spec.Dimension.TraceBridge
import QuantumZipper.Proofs.Loewner.CaraRZ

/-!
# Aux. lemma 125: no extra killing time, and the infinite relative lifetime

Packet PROVE-STRIPSYS7. Specification §7.4, proof of Aux. lemma 125 (`source/spec/p385-432.md` L224–L232, p. 397):

> *There is no extra killing time.* All side partial sums are greater than `−2`, so the integrated driving
> construction has no continuation threshold and no finite coordinate explosion. […] Stop before a fixed coordinate
> bound or at `ζ`, whichever occurs first. On the latter event, bounded monotone force coordinates give finite
> reciprocal integrals and finite coordinate limits; the Brownian driver has its continuous limit. […]
>
> If `ζ` were finite, continuity of the complete pocket traversal and the Jordan boundary homeomorphism would give
> `|X_C(s)| → ∞` as `s ↑ ζ`. The preceding bound makes the driver bounded on that finite interval. The elementary
> Loewner rectangle bound then bounds the whole trace prefix, a contradiction. Thus `ζ = ∞`.

**The route used here is pathwise.** The source excludes a finite coordinate explosion by comparing with the infinite
reference law (weak uniqueness). For the path equations of Definition 2.1 this step is already deterministic in the
project: Aux. lemma 3's pathwise part (`Sec2.IsForcePath.tendsto_or_criticalEscape`, PROVE-SEC2-TERM) shows that at
a finite positive lifetime, with the driving noise continuous up to it, the state either converges or one side escapes
with side total exactly `−2`. That lemma assumes the maximality conditions of Definition 2.1, which a relative
lifetime does not satisfy a priori. They are not needed: if the state does not converge, the maximality condition at
the lifetime is vacuous (`exists_tendsto_of_isForcePathPre`). Hence:

* a solution of the path equations before an arbitrary lifetime `ζ` (no maximality), driven by a continuous noise, with
  both side totals `≠ −2` (e.g. all side partial sums `> −2`), has a finite state limit at every finite positive `ζ`,
  so its driver is bounded on `[0, ζ)` (`exists_bound_of_isForcePathPre`);
* by the Loewner radius bound (`QuantumZipper.fwdHull_subset_closedBall`: `K_s ⊆ B(0, M + 3√s)` when `|W| ≤ M` on
  `[0, s]`), all its hulls `K_s`, `s < ζ`, lie in one ball (`iUnion_fwdHull_subset_closedBall`);
* **`lifetime_eq_top_of_not_isBounded`**: if the hulls are unbounded whenever `ζ` is finite (the source's
  `|X_C(s)| → ∞`, the trace points in `ℍ` lying in the hulls), then `ζ = ∞`.

## Main definitions

* `IsForcePathPre`: the conditions of `Sec2.IsForcePath` (all of Definition 2.1 except the driving equation) that
  refer only to times before the lifetime — everything except the two maximality conditions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Aux125

/-- **The path conditions of Definition 2.1 before the lifetime**: all fields of `Sec2.IsForcePath` except the two
maximality conditions (`threshold_of_eq_zero`, `threshold_of_tendsto`). A relative lifetime of a pocket traversal
satisfies these, and its maximality is what Aux. lemma 125 proves. -/
structure IsForcePathPre {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (ζ : ℝ≥0∞) : Prop where
  w_zero : w 0 = 0
  vL_zero : ∀ i, vL i 0 = xL i
  vR_zero : ∀ i, vR i 0 = xR i
  continuousOn_w : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}
  continuousOn_vL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ}
  continuousOn_vR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}
  antitone_vL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → Antitone fun i => vL i t
  vL_le_w : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i, vL i t ≤ w t
  w_le_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i, w t ≤ vR i t
  monotone_vR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → Monotone fun i => vR i t
  integrable_gapL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t
  integrable_gapR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR i s.toNNReal)⁻¹) volume 0 t
  vL_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal)
  vR_eq : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ → ∀ i,
    vR i t = xR i + ∫ s in (0 : ℝ)..t, 2 / (vR i s.toNNReal - w s.toNNReal)
  volume_collisionL : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vL i s.toNNReal} = 0
  volume_collisionR : ∀ i,
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = vR i s.toNNReal} = 0
  not_threshold : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ →
    ¬ ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun i => vR i t)

namespace IsForcePathPre

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A force path (Definition 2.1 without its driving equation) satisfies the pre-lifetime conditions. -/
theorem of_isForcePath (h : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ) :
    IsForcePathPre xL xR ρL ρR w vL vR ζ :=
  ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL, h.continuousOn_vR,
    h.antitone_vL, h.vL_le_w, h.w_le_vR, h.monotone_vR, h.integrable_gapL, h.integrable_gapR, h.vL_eq,
    h.vR_eq, h.volume_collisionL, h.volume_collisionR, h.not_threshold⟩

/-- **Shortening the lifetime**: the pre-lifetime conditions hold for every earlier lifetime. -/
theorem mono (h : IsForcePathPre xL xR ρL ρR w vL vR ζ) {ζ' : ℝ≥0∞} (hζ' : ζ' ≤ ζ) :
    IsForcePathPre xL xR ρL ρR w vL vR ζ' := by
  have hlt : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < ζ' → (t : ℝ≥0∞) < ζ := fun ht => ht.trans_le hζ'
  refine ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w.mono fun t ht => hlt ht,
    fun i => (h.continuousOn_vL i).mono fun t ht => hlt ht, fun i => (h.continuousOn_vR i).mono fun t ht => hlt ht,
    fun ht => h.antitone_vL (hlt ht), fun ht => h.vL_le_w (hlt ht), fun ht => h.w_le_vR (hlt ht),
    fun ht => h.monotone_vR (hlt ht), fun ht => h.integrable_gapL (hlt ht), fun ht => h.integrable_gapR (hlt ht),
    fun ht => h.vL_eq (hlt ht), fun ht => h.vR_eq (hlt ht), fun i => ?_, fun i => ?_,
    fun ht => h.not_threshold (hlt ht)⟩
  · refine measure_mono_null ?_ (h.volume_collisionL i)
    intro s hs
    exact ⟨hs.1, hs.2.1.trans_le hζ', hs.2.2⟩
  · refine measure_mono_null ?_ (h.volume_collisionR i)
    intro s hs
    exact ⟨hs.1, hs.2.1.trans_le hζ', hs.2.2⟩

/-- The driving equation holds for every earlier lifetime. -/
theorem _root_.InteractingSLE.Sec7.Aux125.driverEq_mono (hw : Sec2.DriverEq a ρL ρR w vL vR b ζ) {ζ' : ℝ≥0∞}
    (hζ' : ζ' ≤ ζ) : Sec2.DriverEq a ρL ρR w vL vR b ζ' := fun t ht => hw t (ht.trans_le hζ')

/-- **Restoring the maximality conditions**: at a positive lifetime, together with the maximality condition at the
lifetime, the pre-lifetime conditions are a force path. -/
theorem toIsForcePath (h : IsForcePathPre xL xR ρL ρR w vL vR ζ) (hζ0 : ζ ≠ 0)
    (hmax : ∀ {T : ℝ≥0}, 0 < T → (T : ℝ≥0∞) = ζ →
      ∀ {w₀ : ℝ} {vL₀ : Fin nL → ℝ} {vR₀ : Fin nR → ℝ},
        Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) →
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) :
    Sec2.IsForcePath xL xR ρL ρR w vL vR ζ :=
  ⟨h.w_zero, h.vL_zero, h.vR_zero, h.continuousOn_w, h.continuousOn_vL, h.continuousOn_vR,
    h.antitone_vL, h.vL_le_w, h.w_le_vR, h.monotone_vR, h.integrable_gapL, h.integrable_gapR, h.vL_eq,
    h.vR_eq, h.volume_collisionL, h.volume_collisionR, h.not_threshold, fun h0 => absurd h0 hζ0, hmax⟩

/-- **No finite coordinate explosion** (proof of Aux. lemma 125, "no finite coordinate explosion […] finite
coordinate limits"; Aux. lemma 3's pathwise part without the maximality conditions): at a finite positive lifetime,
with the driving noise continuous up to it and both side totals different from `−2`, the state converges. -/
theorem exists_tendsto (h : IsForcePathPre xL xR ρL ρR w vL vR ζ) (hw : Sec2.DriverEq a ρL ρR w vL vR b ζ)
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2) {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ)
    (hb : ContinuousOn b (Icc 0 T)) :
    ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) := by
  by_contra hne
  push Not at hne
  have hζ0 : ζ ≠ 0 := by
    rw [← hζ]
    exact_mod_cast hT.ne'
  have hfp : Sec2.IsForcePath xL xR ρL ρR w vL vR ζ :=
    h.toIsForcePath hζ0 fun {T'} _ hT' {w₀} {vL₀} {vR₀} hlim => by
      have e : T' = T := by exact_mod_cast hT'.trans hζ.symm
      subst e
      exact absurd hlim (hne w₀ vL₀ vR₀)
  rcases hfp.tendsto_or_criticalEscape hw hT hζ hb with ⟨w₀, vL₀, vR₀, hlim, -⟩ | ⟨hs, -⟩ | ⟨hs, -⟩
  · exact hne w₀ vL₀ vR₀ hlim
  · exact hL hs
  · exact hR hs

/-- **The driver is bounded before a finite lifetime** ("The preceding bound makes the driver bounded on that finite
interval"). -/
theorem exists_bound (h : IsForcePathPre xL xR ρL ρR w vL vR ζ) (hw : Sec2.DriverEq a ρL ρR w vL vR b ζ)
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2) {T : ℝ≥0} (hT : 0 < T) (hζ : (T : ℝ≥0∞) = ζ)
    (hb : ContinuousOn b (Icc 0 T)) : ∃ M : ℝ, ∀ t : ℝ≥0, t < T → |w t| ≤ M := by
  obtain ⟨w₀, _, _, hlim⟩ := h.exists_tendsto hw hL hR hT hζ hb
  have hW : Tendsto w (𝓝[<] T) (𝓝 w₀) := hlim.fst_nhds
  -- near `T`, `w` is within `1` of `w₀`
  have hev : ∀ᶠ t in 𝓝[<] T, |w t - w₀| < 1 := by
    filter_upwards [hW.eventually (Metric.ball_mem_nhds w₀ one_pos)] with t ht
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  obtain ⟨t₁, ht₁T, ht₁⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (show (0 : ℝ≥0) < T from hT)).1
    (show {t | |w t - w₀| < 1} ∈ 𝓝[<] T from hev)
  -- on `[0, t₁]`, `w` is continuous, hence bounded
  have hcont : ContinuousOn w (Icc 0 t₁) := h.continuousOn_w.mono fun t ht => by
    rw [mem_ofPred_eq, ← hζ]
    exact_mod_cast ht.2.trans_lt ht₁T
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc.image_of_continuousOn hcont).isBounded.exists_norm_le
  refine ⟨max M₁ (|w₀| + 1), fun t ht => ?_⟩
  rcases le_or_gt t t₁ with htt₁ | htt₁
  · exact (by simpa using hM₁ (w t) ⟨t, ⟨zero_le, htt₁⟩, rfl⟩ : |w t| ≤ M₁).trans (le_max_left _ _)
  · have h1 : |w t - w₀| < 1 := ht₁ ⟨htt₁, ht⟩
    have h2 : |w t| ≤ |w₀| + 1 := by
      have := abs_sub_abs_le_abs_sub (w t) w₀
      linarith
    exact h2.trans (le_max_right _ _)

end IsForcePathPre

/-! ### The Loewner radius bound before a finite lifetime -/

section Hull

open QuantumZipper (fwdHull)

/-- **The Loewner rectangle bound before a finite horizon**: if `w` is continuous and bounded by `M` on `[0, T)`,
every hull `K_s`, `s < T`, of the driver `r ↦ w(r)` lies in the closed ball of radius `M + 3√T`
(`QuantumZipper.fwdHull_subset_closedBall`, applied to the driver frozen after a time in `(s, T)`). -/
theorem fwdHull_subset_closedBall_of_bound {w : ℝ≥0 → ℝ} {T : ℝ≥0} (hwc : ContinuousOn w (Iio T)) {M : ℝ}
    (hM : ∀ t : ℝ≥0, t < T → |w t| ≤ M) {s : ℝ≥0} (hs : s < T) :
    fwdHull (fun r : ℝ => w r.toNNReal) s ⊆ closedBall 0 (M + 3 * Real.sqrt T) := by
  obtain ⟨s₁, hss₁, hs₁T⟩ := exists_between hs
  obtain ⟨s₂, hs₁s₂, hs₂T⟩ := exists_between hs₁T
  have hs₁pos : (0 : ℝ) < s₁ := lt_of_le_of_lt s.2 (by exact_mod_cast hss₁)
  -- the driver frozen at `s₂`
  set A : ℝ → ℝ := fun r => w (min r.toNNReal s₂) with hA
  have hAc : Continuous A := by
    have hc : ContinuousOn w (Iic s₂) := hwc.mono fun t ht => lt_of_le_of_lt ht hs₂T
    have hm : Continuous fun r : ℝ => min r.toNNReal s₂ := continuous_real_toNNReal.min continuous_const
    exact hc.comp_continuous hm fun r => show min r.toNNReal s₂ ≤ s₂ from min_le_right _ _
  have hAM : ∀ r ∈ Icc (0 : ℝ) s₁, |A r| ≤ M := fun r _ =>
    hM _ (lt_of_le_of_lt (min_le_right _ _) hs₂T)
  have heq : ∀ r ∈ Icc (0 : ℝ) s₂, w r.toNNReal = A r := by
    intro r hr
    have : r.toNNReal ≤ s₂ := Real.toNNReal_le_iff_le_coe.2 hr.2
    simp only [hA, min_eq_left this]
  have hK : fwdHull (fun r : ℝ => w r.toNNReal) s₁ = fwdHull A s₁ :=
    fwdHull_eq_of_eqOn hs₁pos.le (by exact_mod_cast hs₁s₂) heq
  have hsub := QuantumZipper.CaraR.fwdHull_subset_closedBall hAc hs₁pos hAM
  have hmono : fwdHull (fun r : ℝ => w r.toNNReal) s ⊆ fwdHull (fun r : ℝ => w r.toNNReal) s₁ :=
    QuantumZipper.fwdHull_mono.1 (by exact_mod_cast hss₁.le)
  refine (hmono.trans (hK ▸ hsub)).trans (closedBall_subset_closedBall ?_)
  have : Real.sqrt s₁ ≤ Real.sqrt T := Real.sqrt_le_sqrt (by exact_mod_cast hs₁T.le)
  linarith

/-- All hulls before a finite horizon lie in one ball when the driver is bounded there. -/
theorem iUnion_fwdHull_subset_closedBall {w : ℝ≥0 → ℝ} {T : ℝ≥0} (hwc : ContinuousOn w (Iio T)) {M : ℝ}
    (hM : ∀ t : ℝ≥0, t < T → |w t| ≤ M) :
    (⋃ (s : ℝ≥0) (_ : s < T), fwdHull (fun r : ℝ => w r.toNNReal) s) ⊆ closedBall 0 (M + 3 * Real.sqrt T) :=
  iUnion₂_subset fun _ hs => fwdHull_subset_closedBall_of_bound hwc hM hs

end Hull

/-! ### The infinite relative lifetime -/

section Lifetime

open QuantumZipper (fwdHull)

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The relative lifetime is infinite** (proof of Aux. lemma 125: "If `ζ` were finite, continuity of the complete
pocket traversal and the Jordan boundary homeomorphism would give `|X_C(s)| → ∞` as `s ↑ ζ`. The preceding bound makes
the driver bounded on that finite interval. The elementary Loewner rectangle bound then bounds the whole trace prefix,
a contradiction. Thus `ζ = ∞`."). Pathwise form: a solution of the path equations of Definition 2.1 before `ζ`
(without maximality), with continuous driving noise and both side totals `≠ −2`, whose hulls before `ζ` are unbounded
whenever `ζ` is finite, has `ζ = ∞`. -/
theorem lifetime_eq_top_of_not_isBounded (h : IsForcePathPre xL xR ρL ρR w vL vR ζ)
    (hw : Sec2.DriverEq a ρL ρR w vL vR b ζ) (hb : Continuous b) (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2)
    (hgeo : ζ ≠ ⊤ →
      ¬ Bornology.IsBounded (⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < ζ), fwdHull (fun r : ℝ => w r.toNNReal) s)) :
    ζ = ⊤ := by
  by_contra hne
  obtain ⟨T, hT⟩ : ∃ T : ℝ≥0, (T : ℝ≥0∞) = ζ := ⟨ζ.toNNReal, ENNReal.coe_toNNReal hne⟩
  have hunb := hgeo hne
  have hset : (⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < ζ), fwdHull (fun r : ℝ => w r.toNNReal) s) =
      ⋃ (s : ℝ≥0) (_ : s < T), fwdHull (fun r : ℝ => w r.toNNReal) s := by
    refine iUnion_congr fun s => ?_
    rw [← hT, ENNReal.coe_lt_coe]
  rw [hset] at hunb
  rcases eq_zero_or_pos T with hT0 | hT0
  · subst hT0
    refine hunb ?_
    have : (⋃ (s : ℝ≥0) (_ : s < (0 : ℝ≥0)), fwdHull (fun r : ℝ => w r.toNNReal) s) = ∅ := by
      simp
    rw [this]
    exact Bornology.isBounded_empty
  · obtain ⟨M, hM⟩ := h.exists_bound hw hL hR hT0 hT hb.continuousOn
    have hwc : ContinuousOn w (Iio T) := h.continuousOn_w.mono fun t ht => by
      rw [mem_ofPred_eq, ← hT]
      exact_mod_cast ht
    exact hunb (isBounded_closedBall.subset (iUnion_fwdHull_subset_closedBall hwc hM))

/-- **The relative lifetime is infinite, for integrated paths**: the same, for the full Definition 2.1 data
(`IsIntegratedSLEPath`), where the hypothesis on the hulls is all that remains. -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.lifetime_eq_top_of_not_isBounded
    (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b) (hL : ∑ i, ρL i ≠ -2)
    (hR : ∑ j, ρR j ≠ -2)
    (hgeo : ζ ≠ ⊤ →
      ¬ Bornology.IsBounded (⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < ζ), fwdHull (fun r : ℝ => w r.toNNReal) s)) :
    ζ = ⊤ :=
  Aux125.lifetime_eq_top_of_not_isBounded (IsForcePathPre.of_isForcePath h.isForcePath) h.driverEq hb hL hR hgeo

/-- **The relative lifetime is infinite, below an SDE lifetime** (proof of Aux. lemma 125): if the coordinates solve
Definition 2.1 up to its lifetime `ζ` (for instance the continuation threshold of Aux. lemma 122's evolution), the
relative lifetime `ζ' ≤ ζ` of the pocket traversal is infinite as soon as the hulls before a finite `ζ'` are
unbounded. -/
theorem lifetime_eq_top_of_le (h : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b)
    (hL : ∑ i, ρL i ≠ -2) (hR : ∑ j, ρR j ≠ -2) {ζ' : ℝ≥0∞} (hζ' : ζ' ≤ ζ)
    (hgeo : ζ' ≠ ⊤ →
      ¬ Bornology.IsBounded (⋃ (s : ℝ≥0) (_ : (s : ℝ≥0∞) < ζ'), fwdHull (fun r : ℝ => w r.toNNReal) s)) :
    ζ' = ⊤ :=
  Aux125.lifetime_eq_top_of_not_isBounded ((IsForcePathPre.of_isForcePath h.isForcePath).mono hζ')
    (driverEq_mono h.driverEq hζ') hb hL hR hgeo

end Lifetime

end Aux125

end Sec7

end InteractingSLE

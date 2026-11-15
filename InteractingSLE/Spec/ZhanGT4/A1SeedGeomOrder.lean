/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawPath
import InteractingSLE.Spec.ZhanGT4.DualSeedOmit

/-!
# Zhan's A.1 (R80): the order of seeded image force points, and `SeedImageGeometry` from the force equations

Packet PROVE-A1-SEEDGEOM. A22's `SeedImageGeometry` (the deterministic image equations of a seeded capacity-coordinate
path) has, besides the force equations, the order fields: the left force points are antitone and the right ones
monotone in their index, all left points lie left of the driver and all right points right of it, strictly at positive
times. PROVE-A1-FAMILY recorded that "the ordering and seed conditions are not yet proved for seeded coordinates".

The order between two force points of one side is preserved by the Loewner flow: both solve `v' = 2/(v − w)`, which is
Lipschitz in `v` away from the driver, so two solutions that meet at a positive time agree before it (Mathlib's backward
uniqueness `ODE_solution_unique_of_mem_Icc_left`, as in A19's `seed_ne_fwdMap`). Only the entrance at time zero is
singular, and only for seeds; a strict initial order never needs it, and equal non-seed starts are equal throughout by
forward uniqueness.

## Main results

* `lipschitzOnWith_loewner_real`: `x ↦ 2/(x − w)` is `(2/c²)`-Lipschitz on `{c ≤ |x − w|}`;
* **`forceCoord_lt_of_lt_of_meet`**: two integrated Loewner force points with `v₁(0) < v₂(0)` that never meet on the
  driver keep `v₁ < v₂` on the whole interval (seeds allowed; hitting the driver elsewhere allowed);
  `forceCoord_lt_of_lt`: the case of a lower point that avoids the driver at positive times;
* **`forceCoord_eqOn_of_eq`**: two integrated Loewner force points with a common start off the driver and gaps that
  never vanish agree on the whole interval;
* **`seedImageGeometry_of_forces`**: the force equations, the positive-time sides, the initial order and the seed sums
  give `SeedImageGeometry` (the order fields are proved);
* `SeedImageGeometry.congr`, **`SeedImageGeometry.stop`**: only the data on `[0, T]` matter; the geometry of the data
  stopped at `T`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1SeedGeom

open Sec2

/-! ### One-dimensional Loewner flow: non-crossing -/

/-- **The real Loewner vector field is Lipschitz away from the driver**: `x ↦ 2/(x − w)` is `(2/c²)`-Lipschitz on
`{x : c ≤ |x − w|}`. -/
theorem lipschitzOnWith_loewner_real {w c : ℝ} (hc : 0 < c) :
    LipschitzOnWith (2 / c ^ 2).toNNReal (fun x : ℝ => 2 / (x - w)) {x | c ≤ |x - w|} := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx' : c ≤ |x - w| := hx
  have hy' : c ≤ |y - w| := hy
  have hx0 : x - w ≠ 0 := fun h => by rw [h, abs_zero] at hx'; linarith
  have hy0 : y - w ≠ 0 := fun h => by rw [h, abs_zero] at hy'; linarith
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
  have e : 2 / (x - w) - 2 / (y - w) = 2 * (y - x) / ((x - w) * (y - w)) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_mul, abs_sub_comm y x]
  have hxy : c * c ≤ |x - w| * |y - w| := mul_le_mul hx' hy' hc.le (abs_nonneg _)
  have hpos : 0 < |x - w| * |y - w| := by positivity
  rw [div_le_iff₀ hpos, abs_two]
  calc 2 * |x - y| = 2 / c ^ 2 * |x - y| * (c * c) := by field_simp
    _ ≤ 2 / c ^ 2 * |x - y| * (|x - w| * |y - w|) := by gcongr

/-- **The right derivative of an integral** at an interior point `s ∈ [0, T)` of an interval on which the integrand is
continuous. -/
theorem hasDerivWithinAt_integral_right {f : ℝ → ℝ} {x₀ T s : ℝ} (hf : ContinuousOn f (Icc 0 T))
    (hs : s ∈ Ico 0 T) :
    HasDerivWithinAt (fun r => x₀ + ∫ τ in (0 : ℝ)..r, f τ) (f s) (Ici s) s := by
  have hint : IntervalIntegrable f volume 0 s :=
    (hf.mono (Icc_subset_Icc_right hs.2.le)).intervalIntegrable_of_Icc hs.1
  have hsub : Ioo s T ⊆ Icc 0 T := fun r hr => ⟨hs.1.trans hr.1.le, hr.2.le⟩
  have hc : ContinuousWithinAt f (Ioi s) s := by
    have h1 : ContinuousWithinAt f (Icc 0 T) s := hf s ⟨hs.1, hs.2.le⟩
    exact h1.mono_of_mem_nhdsWithin (mem_of_superset (Ioo_mem_nhdsGT hs.2) hsub)
  have hmeas : StronglyMeasurableAtFilter f (𝓝[>] s) volume :=
    ⟨Ioo s T, Ioo_mem_nhdsGT hs.2, (hf.mono hsub).aestronglyMeasurable measurableSet_Ioo⟩
  exact (intervalIntegral.integral_hasDerivWithinAt_right (s := Ici s) (t := Ioi s) hint hmeas hc).const_add x₀

/-- The Loewner rate of a force point is continuous where its gap does not vanish. -/
theorem continuousOn_rate {w v : ℝ → ℝ} {s : Set ℝ} (hw : ContinuousOn w s) (hv : ContinuousOn v s)
    (hne : ∀ r ∈ s, v r ≠ w r) : ContinuousOn (fun r => 2 / (v r - w r)) s :=
  continuousOn_const.div (hv.sub hw) fun r hr => sub_ne_zero.2 (hne r hr)

section Flow

variable {w v₁ v₂ : ℝ → ℝ} {T : ℝ}

/-- The left derivative of an integrated force point at a positive time with a nonzero gap. -/
theorem hasDerivWithinAt_forceCoord_left {v : ℝ → ℝ} (hw : ContinuousOn w (Icc 0 T))
    (hv : ContinuousOn v (Icc 0 T)) (hint : ∀ s ∈ Icc 0 T, IntervalIntegrable (fun r => 2 / (v r - w r)) volume 0 s)
    (heq : ∀ s ∈ Icc 0 T, v s = v 0 + ∫ r in (0 : ℝ)..s, 2 / (v r - w r)) {s : ℝ} (hs : s ∈ Ioc 0 T)
    (hne : v s ≠ w s) : HasDerivWithinAt v (2 / (v s - w s)) (Iic s) s := by
  have hsT : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hcw : ContinuousWithinAt (fun r => 2 / (v r - w r)) (Icc 0 s) s :=
    continuousWithinAt_const.div (((hv.sub hw).mono hsT) s ⟨hs.1.le, le_rfl⟩) (sub_ne_zero.2 hne)
  have h := hasDerivWithinAt_integral_left (x₀ := v 0) hs.1 (hint s ⟨hs.1.le, hs.2⟩) hcw
  have hev : v =ᶠ[𝓝[Iic s] s] fun r => v 0 + ∫ τ in (0 : ℝ)..r, 2 / (v τ - w τ) := by
    filter_upwards [Icc_mem_nhdsLE hs.1] with r hr
    exact heq r ⟨hr.1, hr.2.trans hs.2⟩
  exact h.congr_of_eventuallyEq hev (heq s ⟨hs.1.le, hs.2⟩)

/-- A uniform positive lower bound for a continuous nonvanishing gap on a compact interval. -/
theorem exists_pos_le_abs_gap {v : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hw : ContinuousOn w (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hne : ∀ r ∈ Icc a b, v r ≠ w r) :
    ∃ c > 0, ∀ r ∈ Icc a b, c ≤ |v r - w r| := by
  obtain ⟨r₀, hr₀, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn (nonempty_Icc.2 hab)
    ((hv.sub hw).abs)
  exact ⟨|v r₀ - w r₀|, abs_pos.2 (sub_ne_zero.2 (hne r₀ hr₀)), fun r hr => hmin hr⟩

/-- A continuous function nonzero at a point of `[0, T]` stays nonzero on a relative neighbourhood. -/
theorem exists_pos_forall_ne_of_continuousWithinAt {g : ℝ → ℝ} {t₀ : ℝ}
    (hg : ContinuousWithinAt g (Icc 0 T) t₀) (h0 : g t₀ ≠ 0) :
    ∃ δ > 0, ∀ r ∈ Icc 0 T, |r - t₀| < δ → g r ≠ 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.1 hg |g t₀| (abs_pos.2 h0)
  refine ⟨δ, hδ, fun r hr hrt hgr => ?_⟩
  have h := hball hr (by rwa [Real.dist_eq])
  rw [Real.dist_eq, hgr, zero_sub, abs_neg] at h
  exact lt_irrefl _ h

/-- **Two integrated Loewner force points do not cross, unless they meet on the driver.** If `v₁, v₂` are continuous
on `[0, T]`, satisfy `v s = v 0 + ∫₀ˢ 2/(v − w)`, `v₁(0) < v₂(0)`, and wherever they meet at a positive time they are
off the driver, then `v₁ < v₂` on `[0, T]`. They may hit the driver elsewhere (marks swallowed before the lifetime), and
their entrance at time zero may be singular (seeds). At a first meeting time both gaps are nonzero, hence nonzero on a
left neighbourhood, where backward uniqueness makes the two solutions equal — contradicting minimality. -/
theorem forceCoord_lt_of_lt_of_meet (hw : ContinuousOn w (Icc 0 T)) (hv₁ : ContinuousOn v₁ (Icc 0 T))
    (hv₂ : ContinuousOn v₂ (Icc 0 T)) (hmeet : ∀ s ∈ Ioc 0 T, v₁ s = v₂ s → v₁ s ≠ w s)
    (hint₁ : ∀ s ∈ Icc 0 T, IntervalIntegrable (fun r => 2 / (v₁ r - w r)) volume 0 s)
    (heq₁ : ∀ s ∈ Icc 0 T, v₁ s = v₁ 0 + ∫ r in (0 : ℝ)..s, 2 / (v₁ r - w r))
    (hint₂ : ∀ s ∈ Icc 0 T, IntervalIntegrable (fun r => 2 / (v₂ r - w r)) volume 0 s)
    (heq₂ : ∀ s ∈ Icc 0 T, v₂ s = v₂ 0 + ∫ r in (0 : ℝ)..s, 2 / (v₂ r - w r))
    (h0 : v₁ 0 < v₂ 0) : ∀ s ∈ Icc 0 T, v₁ s < v₂ s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hle⟩ := hcon
  have hsT : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
  have hD : ContinuousOn (fun r => v₂ r - v₁ r) (Icc 0 s) := (hv₂.sub hv₁).mono hsT
  set Z : Set ℝ := Icc 0 s ∩ (fun r => v₂ r - v₁ r) ⁻¹' {0} with hZ
  have hZc : IsClosed Z := hD.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hZne : Z.Nonempty := by
    obtain ⟨r, hr, hr0⟩ := intermediate_value_Icc' hs.1 hD
      (show (0 : ℝ) ∈ Icc (v₂ s - v₁ s) (v₂ 0 - v₁ 0) from ⟨by linarith, by linarith⟩)
    exact ⟨r, hr, hr0⟩
  have hZbdd : BddBelow Z := ⟨0, fun r hr => hr.1.1⟩
  set t₀ := sInf Z with ht₀
  have ht₀Z : t₀ ∈ Z := hZc.csInf_mem hZne hZbdd
  have hmeet₀ : v₂ t₀ - v₁ t₀ = 0 := ht₀Z.2
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le ht₀Z.1.1 with h | h
    · rw [← h] at hmeet₀
      linarith
    · exact h
  have ht₀T : t₀ ≤ T := ht₀Z.1.2.trans hs.2
  have ht₀m : t₀ ∈ Icc 0 T := ⟨ht₀pos.le, ht₀T⟩
  have hne₁₀ : v₁ t₀ ≠ w t₀ := hmeet t₀ ⟨ht₀pos, ht₀T⟩ (by linarith)
  have hne₂₀ : v₂ t₀ ≠ w t₀ := by rw [show v₂ t₀ = v₁ t₀ by linarith]; exact hne₁₀
  obtain ⟨δ₁, hδ₁, hδ₁ne⟩ := exists_pos_forall_ne_of_continuousWithinAt ((hv₁.sub hw) t₀ ht₀m)
    (sub_ne_zero.2 hne₁₀)
  obtain ⟨δ₂, hδ₂, hδ₂ne⟩ := exists_pos_forall_ne_of_continuousWithinAt ((hv₂.sub hw) t₀ ht₀m)
    (sub_ne_zero.2 hne₂₀)
  set a : ℝ := max (t₀ / 2) (t₀ - min δ₁ δ₂ / 2) with ha
  have hδm : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hale : a ≤ t₀ := max_le (by linarith) (by linarith)
  have hapos : 0 < a := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hat : Icc a t₀ ⊆ Ioc 0 T := fun r hr => ⟨by linarith [hr.1], hr.2.trans ht₀T⟩
  have hat' : Icc a t₀ ⊆ Icc 0 T := fun r hr => Ioc_subset_Icc_self (hat hr)
  have hclose (r : ℝ) (hr : r ∈ Icc a t₀) : |r - t₀| < min δ₁ δ₂ := by
    have h1 : t₀ - min δ₁ δ₂ / 2 ≤ r := (le_max_right _ _).trans hr.1
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hr.2])]
    linarith
  have hgap₁ (r : ℝ) (hr : r ∈ Icc a t₀) : v₁ r ≠ w r :=
    sub_ne_zero.1 (hδ₁ne r (hat' hr) ((hclose r hr).trans_le (min_le_left _ _)))
  have hgap₂ (r : ℝ) (hr : r ∈ Icc a t₀) : v₂ r ≠ w r :=
    sub_ne_zero.1 (hδ₂ne r (hat' hr) ((hclose r hr).trans_le (min_le_right _ _)))
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_abs_gap hale (hw.mono hat') (hv₁.mono hat') hgap₁
  obtain ⟨c₂, hc₂, hc₂le⟩ := exists_pos_le_abs_gap hale (hw.mono hat') (hv₂.mono hat') hgap₂
  set c := min c₁ c₂ with hc
  have hcpos : 0 < c := lt_min hc₁ hc₂
  have hEq := ODE_solution_unique_of_mem_Icc_left (v := fun r x => 2 / (x - w r))
    (s := fun r => {x : ℝ | c ≤ |x - w r|}) (K := (2 / c ^ 2).toNNReal) (a := a) (b := t₀)
    (fun r _ => lipschitzOnWith_loewner_real hcpos) (hv₁.mono hat')
    (fun r hr => hasDerivWithinAt_forceCoord_left hw hv₁ hint₁ heq₁ (hat (Ioc_subset_Icc_self hr))
      (hgap₁ r (Ioc_subset_Icc_self hr)))
    (fun r hr => (min_le_left _ _).trans (hc₁le r (Ioc_subset_Icc_self hr)))
    (hv₂.mono hat')
    (fun r hr => hasDerivWithinAt_forceCoord_left hw hv₂ hint₂ heq₂ (hat (Ioc_subset_Icc_self hr))
      (hgap₂ r (Ioc_subset_Icc_self hr)))
    (fun r hr => (min_le_right _ _).trans (hc₂le r (Ioc_subset_Icc_self hr)))
    (by linarith)
  have haZ : a ∈ Z := by
    refine ⟨⟨hapos.le, hale.trans ht₀Z.1.2⟩, ?_⟩
    show v₂ a - v₁ a = 0
    rw [hEq ⟨le_rfl, hale⟩, sub_self]
  have hmin := csInf_le hZbdd haZ
  have hlt : a < t₀ := max_lt (by linarith) (by linarith)
  linarith

/-- **Two integrated Loewner force points do not cross.** If `v₁, v₂` are continuous on `[0, T]`, avoid the driver at
positive times (the lower one suffices), satisfy `v s = v 0 + ∫₀ˢ 2/(v − w)` and `v₁(0) < v₂(0)`, then `v₁ < v₂` on
`[0, T]`. Their entrance at time zero may be singular (seeds): only positive-time gaps are used. -/
theorem forceCoord_lt_of_lt (hw : ContinuousOn w (Icc 0 T)) (hv₁ : ContinuousOn v₁ (Icc 0 T))
    (hv₂ : ContinuousOn v₂ (Icc 0 T)) (hne₁ : ∀ s ∈ Ioc 0 T, v₁ s ≠ w s)
    (hint₁ : ∀ s ∈ Icc 0 T, IntervalIntegrable (fun r => 2 / (v₁ r - w r)) volume 0 s)
    (heq₁ : ∀ s ∈ Icc 0 T, v₁ s = v₁ 0 + ∫ r in (0 : ℝ)..s, 2 / (v₁ r - w r))
    (hint₂ : ∀ s ∈ Icc 0 T, IntervalIntegrable (fun r => 2 / (v₂ r - w r)) volume 0 s)
    (heq₂ : ∀ s ∈ Icc 0 T, v₂ s = v₂ 0 + ∫ r in (0 : ℝ)..s, 2 / (v₂ r - w r))
    (h0 : v₁ 0 < v₂ 0) : ∀ s ∈ Icc 0 T, v₁ s < v₂ s :=
  forceCoord_lt_of_lt_of_meet hw hv₁ hv₂ (fun s hs _ => hne₁ s hs) hint₁ heq₁ hint₂ heq₂ h0

/-- **Equal starts off the driver stay equal**: two integrated Loewner force points with `v₁(0) = v₂(0)` whose gaps
never vanish on `[0, T]` agree on `[0, T]` (forward uniqueness). -/
theorem forceCoord_eqOn_of_eq (hw : ContinuousOn w (Icc 0 T)) (hv₁ : ContinuousOn v₁ (Icc 0 T))
    (hv₂ : ContinuousOn v₂ (Icc 0 T)) (hne₁ : ∀ s ∈ Icc 0 T, v₁ s ≠ w s) (hne₂ : ∀ s ∈ Icc 0 T, v₂ s ≠ w s)
    (heq₁ : ∀ s ∈ Icc 0 T, v₁ s = v₁ 0 + ∫ r in (0 : ℝ)..s, 2 / (v₁ r - w r))
    (heq₂ : ∀ s ∈ Icc 0 T, v₂ s = v₂ 0 + ∫ r in (0 : ℝ)..s, 2 / (v₂ r - w r))
    (h0 : v₁ 0 = v₂ 0) : EqOn v₁ v₂ (Icc 0 T) := by
  rcases lt_or_ge T 0 with hT | hT
  · intro s hs; exact absurd (hs.1.trans hs.2) (not_le.2 hT)
  obtain ⟨c₁, hc₁, hc₁le⟩ := exists_pos_le_abs_gap hT hw hv₁ hne₁
  obtain ⟨c₂, hc₂, hc₂le⟩ := exists_pos_le_abs_gap hT hw hv₂ hne₂
  set c := min c₁ c₂ with hc
  have hcpos : 0 < c := lt_min hc₁ hc₂
  have hd {v : ℝ → ℝ} (hv : ContinuousOn v (Icc 0 T)) (hne : ∀ s ∈ Icc 0 T, v s ≠ w s)
      (heq : ∀ s ∈ Icc 0 T, v s = v 0 + ∫ r in (0 : ℝ)..s, 2 / (v r - w r)) (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivWithinAt v (2 / (v s - w s)) (Ici s) s := by
    have h := hasDerivWithinAt_integral_right (x₀ := v 0) (continuousOn_rate hw hv hne) hs
    have hev : v =ᶠ[𝓝[Ici s] s] fun r => v 0 + ∫ τ in (0 : ℝ)..r, 2 / (v τ - w τ) := by
      filter_upwards [Icc_mem_nhdsGE hs.2] with r hr
      exact heq r ⟨hs.1.trans hr.1, hr.2⟩
    exact h.congr_of_eventuallyEq hev (heq s ⟨hs.1, hs.2.le⟩)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun r x => 2 / (x - w r))
    (s := fun r => {x : ℝ | c ≤ |x - w r|}) (K := (2 / c ^ 2).toNNReal) (a := 0) (b := T)
    (fun r _ => lipschitzOnWith_loewner_real hcpos) hv₁ (hd hv₁ hne₁ heq₁)
    (fun r hr => (min_le_left _ _).trans (hc₁le r (Ico_subset_Icc_self hr))) hv₂ (hd hv₂ hne₂ heq₂)
    (fun r hr => (min_le_right _ _).trans (hc₂le r (Ico_subset_Icc_self hr))) h0

end Flow

/-! ### `SeedImageGeometry` from the force equations -/

section Geometry

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {T : ℝ≥0}

/-- `2/(v − w) = −2·(w − v)⁻¹`, also at a zero gap. -/
theorem two_div_sub_eq (a b : ℝ) : 2 / (b - a) = -2 * (a - b)⁻¹ := by
  rw [div_eq_mul_inv, ← neg_sub, inv_neg]
  ring

/-- **A force point on `ℝ≥0` read in real time**: the reciprocal-gap integrability and the integrated force equation
of `SeedImageGeometry` give those of `forceCoord_lt_of_lt` for `s ↦ v(s⁺)`, `s ↦ w(s⁺)` on `[0, T]`. -/
theorem forceCoord_real {v : ℝ≥0 → ℝ} {x : ℝ} (hv0 : v 0 = x)
    (hint : ∀ t ≤ T, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t)
    (heq : ∀ t ≤ T, v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal)) :
    (∀ s ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun r : ℝ => 2 / (v r.toNNReal - w r.toNNReal)) volume 0 s) ∧
      ∀ s ∈ Icc (0 : ℝ) T, v s.toNNReal = v (Real.toNNReal 0) +
        ∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) := by
  have hsT (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · have h := (hint s.toNNReal (hsT s hs)).const_mul (-2)
    rw [Real.coe_toNNReal _ hs.1] at h
    exact h.congr (fun r _ => (two_div_sub_eq _ _).symm)
  · rw [Real.toNNReal_zero, hv0, heq _ (hsT s hs), Real.coe_toNNReal _ hs.1]

/-- **`SeedImageGeometry` from the force equations, the sides and the initial order.** The order fields are proved:
two left (right) force points keep their initial order by `forceCoord_lt_of_lt`; equal starts are equal throughout by
`forceCoord_eqOn_of_eq`, which needs them off the driver (at most one seed per side and value, `hsL`, `hsR`). -/
theorem seedImageGeometry_of_forces (hw0 : w 0 = 0) (hL0 : ∀ i, vL i 0 = xL i) (hR0 : ∀ j, vR j 0 = xR j)
    (hw : Continuous w) (hvL : ∀ i, Continuous (vL i)) (hvR : ∀ j, Continuous (vR j))
    (hintL : ∀ t ≤ T, ∀ i,
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 t)
    (hintR : ∀ t ≤ T, ∀ j,
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹) volume 0 t)
    (heqL : ∀ t ≤ T, ∀ i, vL i t = xL i + ∫ s in (0 : ℝ)..t, 2 / (vL i s.toNNReal - w s.toNNReal))
    (heqR : ∀ t ≤ T, ∀ j, vR j t = xR j + ∫ s in (0 : ℝ)..t, 2 / (vR j s.toNNReal - w s.toNNReal))
    (hltL : ∀ t, 0 < t → t ≤ T → ∀ i, vL i t < w t) (hgtR : ∀ t, 0 < t → t ≤ T → ∀ j, w t < vR j t)
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hordL : Antitone xL) (hordR : Monotone xR)
    (hsL : ∀ i i', xL i = xL i' → xL i = 0 → i = i') (hsR : ∀ j j', xR j = xR j' → xR j = 0 → j = j')
    (hseedL : -2 < seedSum xL ρL) (hseedR : -2 < seedSum xR ρR) :
    SeedImageGeometry xL xR ρL ρR w vL vR T := by
  have hwc : ContinuousOn (fun s : ℝ => w s.toNNReal) (Icc 0 T) :=
    (hw.comp continuous_real_toNNReal).continuousOn
  have hcv (v : ℝ≥0 → ℝ) (hv : Continuous v) : ContinuousOn (fun s : ℝ => v s.toNNReal) (Icc 0 T) :=
    (hv.comp continuous_real_toNNReal).continuousOn
  have hpos (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) T) : 0 < s.toNNReal ∧ s.toNNReal ≤ T :=
    ⟨Real.toNNReal_pos.2 hs.1, Real.toNNReal_le_iff_le_coe.2 hs.2⟩
  have hw0' : w (Real.toNNReal 0) = 0 := by rw [Real.toNNReal_zero, hw0]
  -- the left marks
  have hneL (i) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) T) : vL i s.toNNReal ≠ w s.toNNReal :=
    (hltL _ (hpos s hs).1 (hpos s hs).2 i).ne
  have hneR (j) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) T) : vR j s.toNNReal ≠ w s.toNNReal :=
    (hgtR _ (hpos s hs).1 (hpos s hs).2 j).ne'
  have hneL0 (i) (hi : xL i ≠ 0) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : vL i s.toNNReal ≠ w s.toNNReal := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hw0', Real.toNNReal_zero, hL0]; exact hi
    · exact hneL i s ⟨h, hs.2⟩
  have hneR0 (j) (hj : xR j ≠ 0) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) : vR j s.toNNReal ≠ w s.toNNReal := by
    rcases eq_or_lt_of_le hs.1 with h | h
    · rw [← h, hw0', Real.toNNReal_zero, hR0]; exact hj
    · exact hneR j s ⟨h, hs.2⟩
  have hrL (i) := forceCoord_real (hL0 i) (fun t ht => hintL t ht i) (fun t ht => heqL t ht i)
  have hrR (j) := forceCoord_real (hR0 j) (fun t ht => hintR t ht j) (fun t ht => heqR t ht j)
  have hTmem {t : ℝ≥0} (ht : t ≤ T) : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg, ht⟩
  refine
    { w_zero := hw0
      left_zero := hL0
      right_zero := hR0
      continuous_w := hw
      continuous_left := hvL
      continuous_right := hvR
      order_left := fun t ht i i' hii' => ?_
      order_right := fun t ht j j' hjj' => ?_
      left_le := fun t ht i => ?_
      right_ge := fun t ht j => ?_
      left_lt := hltL
      right_gt := hgtR
      integrable_left := hintL
      integrable_right := hintR
      force_left := heqL
      force_right := heqR
      seed_left := hseedL
      seed_right := hseedR }
  · show vL i' t ≤ vL i t
    rcases lt_or_eq_of_le (hordL hii') with hlt | heq'
    · have h := forceCoord_lt_of_lt hwc (hcv _ (hvL i')) (hcv _ (hvL i)) (hneL i') (hrL i').1 (hrL i').2
        (hrL i).1 (hrL i).2 (by rw [Real.toNNReal_zero, hL0, hL0]; exact hlt) _ (hTmem ht)
      rw [Real.toNNReal_coe] at h
      exact h.le
    · by_cases hii : i = i'
      · rw [hii]
      have hx : xL i ≠ 0 := fun h0 => hii (hsL i i' heq'.symm h0)
      have h := forceCoord_eqOn_of_eq hwc (hcv _ (hvL i')) (hcv _ (hvL i)) (hneL0 i' (heq' ▸ hx))
        (hneL0 i hx) (hrL i').2 (hrL i).2 (by rw [Real.toNNReal_zero, hL0, hL0, heq']) (hTmem ht)
      simp only [Real.toNNReal_coe] at h
      exact h.le
  · show vR j t ≤ vR j' t
    rcases lt_or_eq_of_le (hordR hjj') with hlt | heq'
    · have h := forceCoord_lt_of_lt hwc (hcv _ (hvR j)) (hcv _ (hvR j')) (hneR j) (hrR j).1 (hrR j).2
        (hrR j').1 (hrR j').2 (by rw [Real.toNNReal_zero, hR0, hR0]; exact hlt) _ (hTmem ht)
      rw [Real.toNNReal_coe] at h
      exact h.le
    · by_cases hjj : j = j'
      · rw [hjj]
      have hx : xR j ≠ 0 := fun h0 => hjj (hsR j j' heq' h0)
      have h := forceCoord_eqOn_of_eq hwc (hcv _ (hvR j)) (hcv _ (hvR j')) (hneR0 j hx)
        (hneR0 j' (heq' ▸ hx)) (hrR j).2 (hrR j').2 (by rw [Real.toNNReal_zero, hR0, hR0, heq']) (hTmem ht)
      simp only [Real.toNNReal_coe] at h
      exact h.le
  · rcases eq_or_lt_of_le (zero_le (a := t)) with h | h
    · rw [← h, hw0, hL0]; exact hxL i
    · exact (hltL t h ht i).le
  · rcases eq_or_lt_of_le (zero_le (a := t)) with h | h
    · rw [← h, hw0, hR0]; exact hxR j
    · exact (hgtR t h ht j).le

/-- **Only the data on `[0, T]` matter** for `SeedImageGeometry` (given continuity of the new data). -/
theorem _root_.InteractingSLE.ZhanGT4.SeedImageGeometry.congr {w' : ℝ≥0 → ℝ} {vL' : Fin nL → ℝ≥0 → ℝ}
    {vR' : Fin nR → ℝ≥0 → ℝ}
    (h : SeedImageGeometry xL xR ρL ρR w vL vR T) (hw : ∀ t ≤ T, w' t = w t)
    (hvL : ∀ i, ∀ t ≤ T, vL' i t = vL i t) (hvR : ∀ j, ∀ t ≤ T, vR' j t = vR j t) (hcw : Continuous w')
    (hcL : ∀ i, Continuous (vL' i)) (hcR : ∀ j, Continuous (vR' j)) :
    SeedImageGeometry xL xR ρL ρR w' vL' vR' T := by
  have hle {t : ℝ≥0} (ht : t ≤ T) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) : s.toNNReal ≤ T := by
    rw [uIcc_of_le t.coe_nonneg] at hs
    exact (Real.toNNReal_le_toNNReal hs.2).trans (by rw [Real.toNNReal_coe]; exact ht)
  have hle' {t : ℝ≥0} (ht : t ≤ T) {s : ℝ} (hs : s ∈ uIoc (0 : ℝ) t) : s.toNNReal ≤ T :=
    hle ht (uIoc_subset_uIcc hs)
  refine
    { w_zero := by rw [hw 0 (zero_le (a := T))]; exact h.w_zero
      left_zero := fun i => by rw [hvL i 0 (zero_le (a := T))]; exact h.left_zero i
      right_zero := fun j => by rw [hvR j 0 (zero_le (a := T))]; exact h.right_zero j
      continuous_w := hcw
      continuous_left := hcL
      continuous_right := hcR
      order_left := fun t ht i i' hii' => by
        simp only [hvL _ t ht]; exact h.order_left t ht hii'
      order_right := fun t ht j j' hjj' => by
        simp only [hvR _ t ht]; exact h.order_right t ht hjj'
      left_le := fun t ht i => by rw [hvL i t ht, hw t ht]; exact h.left_le t ht i
      right_ge := fun t ht j => by rw [hvR j t ht, hw t ht]; exact h.right_ge t ht j
      left_lt := fun t hp ht i => by rw [hvL i t ht, hw t ht]; exact h.left_lt t hp ht i
      right_gt := fun t hp ht j => by rw [hvR j t ht, hw t ht]; exact h.right_gt t hp ht j
      integrable_left := fun t ht i => (h.integrable_left t ht i).congr fun s hs => by
        simp only [hw _ (hle' ht hs), hvL i _ (hle' ht hs)]
      integrable_right := fun t ht j => (h.integrable_right t ht j).congr fun s hs => by
        simp only [hw _ (hle' ht hs), hvR j _ (hle' ht hs)]
      force_left := fun t ht i => by
        rw [hvL i t ht, h.force_left t ht i]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by
          simp only [hw _ (hle ht hs), hvL i _ (hle ht hs)]
      force_right := fun t ht j => by
        rw [hvR j t ht, h.force_right t ht j]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by
          simp only [hw _ (hle ht hs), hvR j _ (hle ht hs)]
      seed_left := h.seed_left
      seed_right := h.seed_right }

/-- **The geometry of the data stopped at `T`.** -/
theorem _root_.InteractingSLE.ZhanGT4.SeedImageGeometry.stop (h : SeedImageGeometry xL xR ρL ρR w vL vR T) :
    SeedImageGeometry xL xR ρL ρR (fun t => w (min t T)) (fun i t => vL i (min t T)) (fun j t => vR j (min t T))
      T :=
  h.congr (fun t ht => by rw [min_eq_left ht]) (fun i t ht => by rw [min_eq_left ht])
    (fun j t ht => by rw [min_eq_left ht]) (h.continuous_w.comp (continuous_id.min continuous_const))
    (fun i => (h.continuous_left i).comp (continuous_id.min continuous_const))
    (fun j => (h.continuous_right j).comp (continuous_id.min continuous_const))

/-- **Data agreeing with a geometry on `[0, T]`, stopped at `T`, have the geometry** (the form of A1-FAMILY's
`hgeom`: the canonical image data stopped at the cap). -/
theorem _root_.InteractingSLE.ZhanGT4.SeedImageGeometry.stop_of_eqOn {w' : ℝ≥0 → ℝ}
    {vL' : Fin nL → ℝ≥0 → ℝ} {vR' : Fin nR → ℝ≥0 → ℝ} (h : SeedImageGeometry xL xR ρL ρR w vL vR T)
    (hw : ∀ t ≤ T, w' t = w t) (hvL : ∀ i, ∀ t ≤ T, vL' i t = vL i t) (hvR : ∀ j, ∀ t ≤ T, vR' j t = vR j t) :
    SeedImageGeometry xL xR ρL ρR (fun t => w' (min t T)) (fun i t => vL' i (min t T))
      (fun j t => vR' j (min t T)) T := by
  have e₁ : (fun t => w' (min t T)) = fun t => w (min t T) := funext fun t => hw _ (min_le_right _ _)
  have e₂ : (fun i t => vL' i (min t T)) = fun i t => vL i (min t T) :=
    funext fun i => funext fun t => hvL i _ (min_le_right _ _)
  have e₃ : (fun j t => vR' j (min t T)) = fun j t => vR j (min t T) :=
    funext fun j => funext fun t => hvR j _ (min_le_right _ _)
  rw [e₁, e₂, e₃]
  exact h.stop

/-- **A geometry up to `T` restricts to every earlier horizon.** -/
theorem _root_.InteractingSLE.ZhanGT4.SeedImageGeometry.mono (h : SeedImageGeometry xL xR ρL ρR w vL vR T)
    {T' : ℝ≥0} (hT : T' ≤ T) : SeedImageGeometry xL xR ρL ρR w vL vR T' where
  w_zero := h.w_zero
  left_zero := h.left_zero
  right_zero := h.right_zero
  continuous_w := h.continuous_w
  continuous_left := h.continuous_left
  continuous_right := h.continuous_right
  order_left t ht := h.order_left t (ht.trans hT)
  order_right t ht := h.order_right t (ht.trans hT)
  left_le t ht := h.left_le t (ht.trans hT)
  right_ge t ht := h.right_ge t (ht.trans hT)
  left_lt t hp ht := h.left_lt t hp (ht.trans hT)
  right_gt t hp ht := h.right_gt t hp (ht.trans hT)
  integrable_left t ht := h.integrable_left t (ht.trans hT)
  integrable_right t ht := h.integrable_right t (ht.trans hT)
  force_left t ht := h.force_left t (ht.trans hT)
  force_right t ht := h.force_right t (ht.trans hT)
  seed_left := h.seed_left
  seed_right := h.seed_right

end Geometry

end InteractingSLE.ZhanGT4.A1SeedGeom

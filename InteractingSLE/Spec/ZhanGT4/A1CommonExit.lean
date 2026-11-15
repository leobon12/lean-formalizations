/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1EightSeedExit
import InteractingSLE.Spec.ZhanGT4.A1G3CalcG3Rec
import InteractingSLE.Spec.ZhanGT4.A1EightFinGap

/-!
# Zhan's A.1: the enclosure exit precedes the lifetime

Packet PROVE-A1-COMMON. Source: Astra, *Follow-up proofs*, §A.1.3 (`ig1_followup_proofs.txt` L300–L330: the curves are
run up to their exits from separated enclosures "before any force collision"), and the maximality of the lifetime
(Specification p. 20, Aux. lemma 3; the frozen `IsIntegratedSLEPath`'s last clause).

A1-EIGHTSEED's rectangle exits `lifeExit w ζ E N` are capped by the lifetime, and A1-EIGHTSEED / A1-G3CALC /
A1-EIGHTFIN need them **strictly** before it. This file proves it pathwise, for every sample with a continuous driving
Brownian path:

* `vR_mono_of_path`, `vL_anti_of_path`: force points move away from the driver;
* `driver_eq_of_path`: `w_t = √a b_t − Σ (ρ/2)(v_t − x)` (each drift integral is a force-point increment);
* **`exists_tendsto_state_of_path`**: with a continuous Brownian path and one-sided bounds on the force points, the
  state has a limit from the left at every time up to the lifetime;
* **`protected_bounds_of_path`**: while the hull stays in a bounded enclosure protected from the mark `x_R(j)` (and the
  left force points are seeds), the seeds are bounded, the mark is bounded and stays at a uniform positive gap from
  the driver (A1-EIGHTFIN's `exists_real_gap_lower`);
* **`lifeExit_lt_of_protected`**: hence the lifetime cannot end before the exit: at a finite lifetime the left limit
  exists, satisfies the threshold condition (maximality), and has the mark off the driver, which the word excludes.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Common

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A1EightSeed

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- `2/(v − w) = −2 (w − v)⁻¹`. -/
theorem two_div_sub_eq (v u : ℝ) : 2 / (v - u) = -2 * (u - v)⁻¹ := by
  rw [div_eq_mul_inv, ← neg_sub u v, inv_neg]; ring

/-- `ρ/(w − v) = (−ρ/2) · 2/(v − w)`. -/
theorem div_sub_eq_force (ρ v u : ℝ) : ρ / (u - v) = -ρ / 2 * (2 / (v - u)) := by
  rw [two_div_sub_eq, div_eq_mul_inv]; ring

/-- **Right force points move away from the driver**: `v_R` is nondecreasing before the lifetime. -/
theorem vR_mono_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nR) {s t : ℝ≥0}
    (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) : vR i s ≤ vR i t := by
  obtain ⟨-, -, -, -, -, -, -, -, hwR, -, -, hiR, -, -, hReq, -⟩ := hP
  have hs : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hst) ht
  have hint : ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => 2 / (vR i r.toNNReal - w r.toNNReal)) volume 0 u := fun u hu => by
    have e : (fun r : ℝ => 2 / (vR i r.toNNReal - w r.toNNReal)) =
        fun r : ℝ => -2 * (w r.toNNReal - vR i r.toNNReal)⁻¹ := funext fun r => two_div_sub_eq _ _
    rw [e]; exact (hiR u hu i).const_mul _
  have hdiff := intervalIntegral.integral_interval_sub_left (hint t ht) (hint s hs)
  have hnn : 0 ≤ ∫ r in (s : ℝ)..t, 2 / (vR i r.toNNReal - w r.toNNReal) := by
    refine intervalIntegral.integral_nonneg (NNReal.coe_le_coe.2 hst) fun r hr => ?_
    have hr0 : 0 ≤ r := s.coe_nonneg.trans hr.1
    have hrt : (r.toNNReal : ℝ≥0∞) < ζ :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht
    exact div_nonneg (by norm_num) (sub_nonneg.2 (hwR _ hrt i))
  have h1 := hReq t ht i
  have h2 := hReq s hs i
  linarith

/-- **Left force points move away from the driver**: `v_L` is nonincreasing before the lifetime. -/
theorem vL_anti_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nL) {s t : ℝ≥0}
    (hst : s ≤ t) (ht : (t : ℝ≥0∞) < ζ) : vL i t ≤ vL i s := by
  obtain ⟨-, -, -, -, -, -, -, hLw, -, -, hiL, -, -, hLeq, -⟩ := hP
  have hs : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hst) ht
  have hint : ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ →
      IntervalIntegrable (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) volume 0 u := fun u hu => by
    have e : (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) =
        fun r : ℝ => -2 * (w r.toNNReal - vL i r.toNNReal)⁻¹ := funext fun r => two_div_sub_eq _ _
    rw [e]; exact (hiL u hu i).const_mul _
  have hdiff := intervalIntegral.integral_interval_sub_left (hint t ht) (hint s hs)
  have hnp : ∫ r in (s : ℝ)..t, 2 / (vL i r.toNNReal - w r.toNNReal) ≤ 0 := by
    have h := intervalIntegral.integral_nonneg (μ := volume)
      (f := fun r : ℝ => -(2 / (vL i r.toNNReal - w r.toNNReal)))
      (NNReal.coe_le_coe.2 hst) fun r hr => by
        have hrt : (r.toNNReal : ℝ≥0∞) < ζ :=
          lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hr.2)) ht
        exact neg_nonneg.2 (div_nonpos_iff.2 (Or.inl ⟨by norm_num, sub_nonpos.2 (hLw _ hrt i)⟩))
    rw [intervalIntegral.integral_neg] at h
    linarith
  have h1 := hLeq t ht i
  have h2 := hLeq s hs i
  linarith

/-- **The driver in closed form**: each drift integral is a force-point increment,
`∫₀ᵗ ρ/(w − v) = −(ρ/2)(v_t − x)`, so `w_t = √a b_t − Σ (ρ/2)(v_t − x)` before the lifetime. -/
theorem driver_eq_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    w t = Real.sqrt a * b t + (∑ i, -ρL i / 2 * (vL i t - xL i)) + ∑ j, -ρR j / 2 * (vR j t - xR j) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hweq, hLeq, hReq, -⟩ := hP
  rw [hweq t ht]
  have eL : ∀ i, (∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal)) = -ρL i / 2 * (vL i t - xL i) :=
    fun i => by
      simp_rw [div_sub_eq_force (ρL i)]
      rw [intervalIntegral.integral_const_mul, hLeq t ht i]
      ring
  have eR : ∀ j, (∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal)) = -ρR j / 2 * (vR j t - xR j) :=
    fun j => by
      simp_rw [div_sub_eq_force (ρR j)]
      rw [intervalIntegral.integral_const_mul, hReq t ht j]
      ring
  simp only [eL, eR]

/-- **The state has a limit from the left** at every time `T ≤ ζ` at which the Brownian path is continuous, when the
left force points are bounded below and the right ones bounded above before `T`. -/
theorem exists_tendsto_state_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) ≤ ζ) (hb : ContinuousAt b T) {CL CR : ℝ} (hL : ∀ t < T, ∀ i, CL ≤ vL i t)
    (hR : ∀ t < T, ∀ i, vR i t ≤ CR) :
    ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) := by
  have hlt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht => lt_of_lt_of_le (ENNReal.coe_lt_coe.2 ht) hT
  have hRl : ∀ j, Tendsto (vR j) (𝓝[<] T) (𝓝 (sSup (vR j '' Iio T))) := fun j =>
    MonotoneOn.tendsto_nhdsLT (fun s _ t ht hst => vR_mono_of_path hP j hst (hlt t ht))
      ⟨CR, by rintro _ ⟨t, ht, rfl⟩; exact hR t ht j⟩
  have hLl : ∀ i, Tendsto (vL i) (𝓝[<] T) (𝓝 (-sSup ((fun t => -vL i t) '' Iio T))) := fun i => by
    have h := MonotoneOn.tendsto_nhdsLT (f := fun t => -vL i t) (x := T)
      (fun s _ t ht hst => neg_le_neg (vL_anti_of_path hP i hst (hlt t ht)))
      ⟨-CL, by rintro _ ⟨t, ht, rfl⟩; exact neg_le_neg (hL t ht i)⟩
    simpa using h.neg
  have hbl : Tendsto b (𝓝[<] T) (𝓝 (b T)) := hb.tendsto.mono_left nhdsWithin_le_nhds
  have hrhs := ((hbl.const_mul (Real.sqrt a)).add (tendsto_finsetSum Finset.univ fun i _ =>
      ((hLl i).sub_const (xL i)).const_mul (-ρL i / 2))).add
    (tendsto_finsetSum Finset.univ fun j _ => ((hRl j).sub_const (xR j)).const_mul (-ρR j / 2))
  have hw : Tendsto w (𝓝[<] T) _ := hrhs.congr' (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (driver_eq_of_path hP (hlt t ht)).symm)
  exact ⟨_, _, _, hw.prodMk_nhds ((tendsto_pi_nhds.2 hLl).prodMk_nhds (tendsto_pi_nhds.2 hRl))⟩

/-- `extPath v` at a nonnegative real time `t` is `v t`. -/
theorem extPath_coe (v : ℝ≥0 → ℝ) (t : ℝ≥0) : Strip.extPath v (t : ℝ) = v t := by
  simp only [Strip.extPath, Real.toNNReal_coe]

/-- **A continuous driver for the hull at a time before the lifetime**: the path's driver stopped slightly after `t`
is continuous, starts at `0`, agrees with the path on `[0, t]` and has the same hull at `t`. -/
theorem exists_stopped_driver (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) :
    ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ EqOn W' (Strip.extPath w) (Icc 0 t) ∧ W' t = w t ∧
      fwdHull W' t = fwdHull (Strip.extPath w) t := by
  obtain ⟨hw0, -, -, hcw, -⟩ := hP
  obtain ⟨r, htr, -, hcr⟩ := exists_real_btwn_continuousOn hcw ht
  have hr0 : 0 ≤ r := t.coe_nonneg.trans htr.le
  have hEq : EqOn (A1Ref.stopDrv (Strip.extPath w) r) (Strip.extPath w) (Icc 0 r) := A1Ref.stopDrv_eqOn _ r
  have hEqt : EqOn (A1Ref.stopDrv (Strip.extPath w) r) (Strip.extPath w) (Icc 0 t) := fun s hs =>
    hEq ⟨hs.1, hs.2.trans htr.le⟩
  refine ⟨_, A1Ref.continuous_stopDrv hcr hr0, ?_, hEqt, by rw [hEqt ⟨t.coe_nonneg, le_rfl⟩, extPath_coe],
    (LocalExt.fwdHull_congr_of_eqOn_of_lt t.coe_nonneg htr fun s hs => (hEq hs).symm).symm⟩
  simp only [A1Ref.stopDrv, min_eq_left hr0, max_self, Strip.extPath, Real.toNNReal_zero, hw0]

/-- **A left seed is bounded below** while the hull lies in `B̄(0, R)`: `−7R ≤ v_L(t)`. -/
theorem seed_lower_bound_of_path (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {R : ℝ} (hR : 0 < R)
    (i : Fin nL) (hxi : xL i = 0) (hne : ∀ (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ → vL i s ≠ w s) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < ζ) (hK : fwdHull (Strip.extPath w) t ⊆ closedBall (0 : ℂ) R) : -(7 * R) ≤ vL i t := by
  obtain ⟨W', hW'c, hW'0, hEqt, -, hhull⟩ := exists_stopped_driver hP ht
  have hseed := A1SeedField.isSeedCoordinate_vL_of_path hP i hxi ht
    (fun s hs hst => hne s hs (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hst) ht)) hEqt
  have hb := hseed.abs_le_of_hull_subset_ball hW'c t.coe_nonneg hR (by rw [hhull]; exact hK)
    (by rw [hW'0, abs_zero]; exact hR.le) ⟨t.coe_nonneg, le_rfl⟩
  rw [extPath_coe] at hb
  exact (abs_le.1 hb).1

/-- A gap that holds before `T` passes to the left limit. -/
theorem le_of_tendsto_gap {f g : ℝ≥0 → ℝ} {T : ℝ≥0} (hT0 : 0 < T) {f₀ g₀ c : ℝ}
    (hf : Tendsto f (𝓝[<] T) (𝓝 f₀)) (hg : Tendsto g (𝓝[<] T) (𝓝 g₀)) (h : ∀ t < T, c ≤ |f t - g t|) :
    c ≤ |f₀ - g₀| := by
  have hne : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  refine ge_of_tendsto ((hf.sub hg).abs) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h t ht

/-- **The gap of a force point that has not yet met the driver**: if `v` is a force point of the path
(`v = x + ∫ 2/(v − w)`) that has not met the driver on `[0, t]`, `t` before the lifetime, the hull at `t` lies in the
set `E` and `c` bounds the forward flows of `x` below for hulls in `E` (A1-EIGHTFIN's uniform gap
`exists_real_gap_lower`), then `c ≤ |v_t − w_t|`, and `|v_t| ≤ |x| + 5R` when `E ⊆ B̄(0, R)`: `v − w` is the forward
flow of `x` (`A1G3Calc.isForwardSol_of_force`). -/
theorem mark_gap_of_sep (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {v : ℝ≥0 → ℝ} {x : ℝ}
    (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {E : Set ℂ} (h0E : (0 : ℂ) ∈ closure E) {c : ℝ}
    (hlow : ∀ W : ℝ → ℝ, Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure E → ∀ T : ℝ, fwdHull W T ⊆ E →
      ∀ u : ℝ → ℂ, IsForwardSol W (x : ℂ) T u → ∀ t ∈ Icc (0 : ℝ) T, c ≤ ‖u t‖)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hK : fwdHull (Strip.extPath w) t ⊆ E) (hsep : ∀ r ≤ t, v r ≠ w r) :
    c ≤ |v t - w t| ∧ ∀ {R : ℝ}, 0 < R → E ⊆ closedBall (0 : ℂ) R → |v t| ≤ |x| + 5 * R := by
  obtain ⟨W', hW'c, hW'0, hEqt, hW't, hhull⟩ := exists_stopped_driver hP ht
  have hKt : fwdHull W' t ⊆ E := by rw [hhull]; exact hK
  have hu := A1G3Calc.isForwardSol_of_force hvc hveq ht hsep hW'c.continuousOn hEqt
  have hgap := hlow W' hW'c (by rw [hW'0]; simpa using h0E) t hKt _ hu t ⟨t.coe_nonneg, le_rfl⟩
  simp only [extPath_coe, hW't, Complex.norm_real, Real.norm_eq_abs] at hgap
  refine ⟨hgap, fun {R} hR hER => ?_⟩
  have hup := norm_sol_add_sub_le hW'c t.coe_nonneg (c := 0) hR (by simpa using hKt.trans hER) hu
  simp only [extPath_coe, hW't, Complex.ofReal_zero, sub_zero] at hup
  rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, sub_add_cancel, Complex.norm_real,
    Real.norm_eq_abs] at hup
  exact hup

/-- **A protected force point never meets the driver while the hull lies in the enclosure, and keeps a uniform gap.**
If `v` is a force point of the path started at `x ≠ 0` and `B(x, ρ)` misses the `ℍ`-hull `E`, there is `c > 0` such
that at every time `t` before the lifetime whose hull lies in `E`, `c ≤ |v_s − w_s|` for all `s ≤ t` (and
`|v_t| ≤ |x| + 5R` when `E ⊆ B̄(0, R)`). Deterministic: before the first meeting time `τ ≤ t`, `v − w` is the forward
flow of `x`, whose modulus stays `≥ c` (A1-EIGHTFIN's uniform gap), so by continuity `|v_τ − w_τ| ≥ c`, a
contradiction. -/
theorem protected_mark_bounds (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {v : ℝ≥0 → ℝ} {x : ℝ}
    (hvc : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hx0 : x ≠ 0) {E : Set ℂ} (hE : IsHPHull E) (h0E : (0 : ℂ) ∈ closure E) {ρ : ℝ} (hρ : 0 < ρ)
    (hxE : Disjoint (ball (x : ℂ) ρ) E) :
    ∃ c > (0 : ℝ), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → fwdHull (Strip.extPath w) t ⊆ E →
      (∀ s ≤ t, c ≤ |v s - w s|) ∧ ∀ {R : ℝ}, 0 < R → E ⊆ closedBall (0 : ℂ) R → |v t| ≤ |x| + 5 * R := by
  obtain ⟨c, hc, hlow⟩ := A1EightFin.exists_real_gap_lower hE hρ hxE
  have hP' := hP
  obtain ⟨hw0, -, -, hcw, -⟩ := hP'
  -- the separation on `[0, t]`
  have hsep : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → fwdHull (Strip.extPath w) t ⊆ E → ∀ r ≤ t, v r ≠ w r := by
    intro t ht hK
    by_contra hcon
    push Not at hcon
    obtain ⟨r₁, hr₁t, hr₁⟩ := hcon
    have hlt : ∀ s : ℝ≥0, s ≤ t → (s : ℝ≥0∞) < ζ := fun s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht
    have hcont : ContinuousOn (fun s => v s - w s) (Iic t) :=
      (hvc.mono fun s hs => hlt s hs).sub (hcw.mono fun s hs => hlt s hs)
    set Z : Set ℝ≥0 := Iic t ∩ (fun s => v s - w s) ⁻¹' {0} with hZ
    have hZc : IsClosed Z := hcont.preimage_isClosed_of_isClosed isClosed_Iic isClosed_singleton
    have hZne : Z.Nonempty := ⟨r₁, hr₁t, by simp [hr₁]⟩
    set τ := sInf Z with hτ
    have hτZ : τ ∈ Z := hZc.csInf_mem hZne (OrderBot.bddBelow _)
    have hτt : τ ≤ t := hτZ.1
    have hτeq : v τ - w τ = 0 := hτZ.2
    have hbefore : ∀ r < τ, v r ≠ w r := fun r hr he => by
      have : τ ≤ r := csInf_le (OrderBot.bddBelow _) ⟨hr.le.trans hτt, by simp [he]⟩
      exact absurd hr (not_lt.2 this)
    have hτ0 : 0 < τ := by
      refine lt_of_le_of_ne zero_le fun h0 => ?_
      have h00 : v 0 - w 0 = 0 := by rw [h0]; exact hτeq
      have hv0 : v 0 = x := by
        have := hveq 0 (hlt 0 zero_le)
        simpa using this
      rw [hv0, hw0, sub_zero] at h00
      exact hx0 h00
    have hgapb : ∀ s < τ, c ≤ |v s - w s| := fun s hs =>
      (mark_gap_of_sep hP hvc hveq h0E hlow (hlt s (hs.le.trans hτt))
        (((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 (hs.le.trans hτt))).trans hK)
        fun r hr => hbefore r (lt_of_le_of_lt hr hs)).1
    have hca : ContinuousAt (fun s => v s - w s) τ := by
      have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
      exact ((hvc.sub hcw).continuousAt (hopen.mem_nhds (hlt τ hτt)))
    have hg := le_of_tendsto_gap (g := fun _ => (0 : ℝ)) hτ0 (hca.tendsto.mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds fun s hs => by simpa using hgapb s hs
    rw [hτeq, sub_zero, abs_zero] at hg
    linarith
  refine ⟨c, hc, fun t ht hK => ⟨fun s hs => ?_, fun {R} hR hER => ?_⟩⟩
  · have hst : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht
    have hKs := ((QuantumZipper.fwdHull_mono).1 (NNReal.coe_le_coe.2 hs)).trans hK
    exact (mark_gap_of_sep hP hvc hveq h0E hlow hst hKs (hsep s hst hKs)).1
  · exact (mark_gap_of_sep hP hvc hveq h0E hlow ht hK (hsep t ht hK)).2 hR hER

/-- **The enclosure exit precedes the lifetime (core form).** Suppose the Brownian path is continuous, the seed state
is not a threshold state, the force points are bounded on the appropriate sides while the hull lies in `E`, and no left
limit of the state reached with the hull in `E` is a threshold state. Then `lifeExit w ζ E N < ζ`: at a finite lifetime
`ζ ≤ N` with the hull in `E` the left limit exists (`exists_tendsto_state_of_path`) and maximality makes it a threshold
state. -/
theorem lifeExit_lt_of_bounds (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b)
    {E : Set ℂ} (hthr0 : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) {CL CR : ℝ}
    (hbd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → fwdHull (Strip.extPath w) t ⊆ E → (∀ i, CL ≤ vL i t) ∧ ∀ i, vR i t ≤ CR)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → (∀ t < T, fwdHull (Strip.extPath w) t ⊆ E) →
      ∀ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ),
        Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) →
        ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) (N : ℝ≥0) :
    (lifeExit w ζ E N : ℝ≥0∞) < ζ := by
  set T := lifeExit w ζ E N with hTdef
  by_contra hge
  rw [not_lt] at hge
  have hall : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ ∧ fwdHull (Strip.extPath w) t ⊆ E := fun t ht =>
    lt_and_subset_of_lt_lifeExit ht
  have hP' := hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hthrz, hthrT⟩ := hP'
  rcases eq_zero_or_pos T with hT0 | hT0
  · have hζ : ζ = 0 := le_antisymm (by rw [hT0] at hge; simpa using hge) zero_le
    exact hthr0 (hthrz hζ)
  have hTζ : (T : ℝ≥0∞) = ζ := by
    refine le_antisymm ?_ hge
    by_contra hlt
    rw [not_le] at hlt
    have hζfin : ζ ≠ ⊤ := ne_top_of_lt hlt
    have hlt' : ζ.toNNReal < T := by
      rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hζfin]; exact hlt
    have := (hall _ hlt').1
    rw [ENNReal.coe_toNNReal hζfin] at this
    exact lt_irrefl _ this
  obtain ⟨w₀, vL₀, vR₀, hl⟩ := exists_tendsto_state_of_path hP hTζ.le hb.continuousAt
    (fun t ht i => (hbd t (hall t ht).1 (hall t ht).2).1 i) (fun t ht i => (hbd t (hall t ht).1 (hall t ht).2).2 i)
  exact hlim T hT0 hTζ (fun t ht => (hall t ht).2) w₀ vL₀ vR₀ hl (hthrT T hT0 hTζ w₀ vL₀ vR₀ hl)

/-- **The exit precedes the lifetime: a protected right mark** (the small curves of A.1). All left force points are
seeds (off the driver at positive times), the last right mark `x_R(j) ≠ 0` is protected by a bounded `ℍ`-hull
enclosure `E` (so it stays off the driver while the hull is in `E`, `protected_mark_bounds`), and the word's
threshold condition fails whenever that mark is
off the driver. -/
theorem lifeExit_lt_of_protected (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b)
    {E : Set ℂ} {R : ℝ} (hR : 0 < R) (hER : E ⊆ closedBall (0 : ℂ) R) (hE : IsHPHull E)
    (h0E : (0 : ℂ) ∈ closure E) (hxL : ∀ i, xL i = 0)
    (hneL : ∀ i (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ → vL i s ≠ w s) {j : Fin nR} (hj : ∀ i, i ≤ j) {ρ : ℝ}
    (hρ : 0 < ρ) (hjE : Disjoint (ball (xR j : ℂ) ρ) E) (hxj : xR j ≠ 0)
    (hword : ∀ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin nR → ℝ), vR₀ j ≠ w₀ →
      ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) (N : ℝ≥0) :
    (lifeExit w ζ E N : ℝ≥0∞) < ζ := by
  have hP' := hP
  obtain ⟨-, -, -, -, -, hcR, -, -, -, hmono, -, -, -, -, hReq, -⟩ := hP'
  obtain ⟨c, hc, hmk⟩ := protected_mark_bounds hP (hcR j) (fun t ht => hReq t ht j) hxj hE h0E hρ hjE
  refine lifeExit_lt_of_bounds hP hb (hword 0 xL xR hxj) (CL := -(7 * R)) (CR := |xR j| + 5 * R)
    (fun t ht hK => ⟨fun i => seed_lower_bound_of_path hP hR i (hxL i) (hneL i) ht (hK.trans hER),
      fun i => (hmono t ht (hj i)).trans (abs_le.1 ((hmk t ht hK).2 hR hER)).2⟩) ?_ N
  intro T hT0 hTζ hK w₀ vL₀ vR₀ hl
  have hlt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht => hTζ ▸ ENNReal.coe_lt_coe.2 ht
  have hg := le_of_tendsto_gap hT0 (((continuous_apply j).continuousAt.tendsto.comp
      ((continuous_snd.comp continuous_snd).continuousAt.tendsto.comp hl)))
    (continuous_fst.continuousAt.tendsto.comp hl) fun t ht => (hmk t (hlt t ht) (hK t ht)).1 t le_rfl
  exact hword w₀ vL₀ vR₀ fun he => by
    simp only [Function.comp_apply] at hg
    rw [he, sub_self, abs_zero] at hg; linarith

/-- **The exit precedes the lifetime: a protected left mark, no right force points** (the large curves of A.1). The
last left mark `x_L(j) ≠ 0` is protected by a bounded `ℍ`-hull enclosure `E` (so it stays off the driver while the
hull is in `E`), and the word's threshold condition fails whenever that mark is off the driver. -/
theorem lifeExit_lt_of_protected_left {xL : Fin nL → ℝ} {ρL : Fin nL → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {xR ρR : Fin 0 → ℝ} {vR : Fin 0 → ℝ≥0 → ℝ}
    (hP : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hb : Continuous b)
    {E : Set ℂ} {R : ℝ} (hR : 0 < R) (hER : E ⊆ closedBall (0 : ℂ) R) (hE : IsHPHull E)
    (h0E : (0 : ℂ) ∈ closure E) {j : Fin nL} (hj : ∀ i, i ≤ j) {ρ : ℝ}
    (hρ : 0 < ρ) (hjE : Disjoint (ball (xL j : ℂ) ρ) E) (hxj : xL j ≠ 0)
    (hword : ∀ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin 0 → ℝ), vL₀ j ≠ w₀ →
      ¬ ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀) (N : ℝ≥0) :
    (lifeExit w ζ E N : ℝ≥0∞) < ζ := by
  have hP' := hP
  obtain ⟨-, -, -, -, hcL, -, hanti, -, -, -, -, -, -, hLeq, -⟩ := hP'
  obtain ⟨c, hc, hmk⟩ := protected_mark_bounds hP (hcL j) (fun t ht => hLeq t ht j) hxj hE h0E hρ hjE
  refine lifeExit_lt_of_bounds hP hb (hword 0 xL xR hxj) (CL := -(|xL j| + 5 * R)) (CR := 0)
    (fun t ht hK => ⟨fun i => (abs_le.1 ((hmk t ht hK).2 hR hER)).1.trans (hanti t ht (hj i)), fun i => i.elim0⟩) ?_ N
  intro T hT0 hTζ hK w₀ vL₀ vR₀ hl
  have hlt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < ζ := fun t ht => hTζ ▸ ENNReal.coe_lt_coe.2 ht
  have hg := le_of_tendsto_gap hT0 (((continuous_apply j).continuousAt.tendsto.comp
      ((continuous_fst.comp continuous_snd).continuousAt.tendsto.comp hl)))
    (continuous_fst.continuousAt.tendsto.comp hl) fun t ht => (hmk t (hlt t ht) (hK t ht)).1 t le_rfl
  exact hword w₀ vL₀ vR₀ fun he => by
    simp only [Function.comp_apply] at hg
    rw [he, sub_self, abs_zero] at hg; linarith

end Path

end InteractingSLE.ZhanGT4.A1Common

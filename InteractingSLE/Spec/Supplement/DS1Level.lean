/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS1Loc

/-!
# Lemma DS1: the generator bound along a path and the estimate at one localization level

Packet PROVE-T14-TIP (specification supplement §12, **Lemma DS1**, `source/spec/p529-576.md` L523–L575, pp. 551–553).

* `itoGen_ge_path`: at a non-collision time before the far stop, the Itô generator of the DS1 observable is at least
  `c₀ h_ν(X₁) − C₂`, where `h_ν(x) = 1{x < r}(x + ν)^{p−2}` (`occ`), `c₀ = pε/4` and `C₂` depends only on the bounds;
* `continuousOn_fn1`, `continuousOn_fn2`: `f'`, `f''` are continuous on `(−ν, ∞)`;
* `integral_occ_le`: pathwise, `c₀ ∫₀^τ h_ν(X₁) ≤ ∫₀^τ itoGen + C₂ τ` up to `τ = t ∧ σ_n`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DS1

open Supp8.GB5

variable {nL nR : ℕ}

/-- The regularized occupation density `h_ν(x) = 1{x < r} (x + ν)^{p−2}` of (DS1.3). -/
def occ (p ν r x : ℝ) : ℝ := {y : ℝ | y < r}.indicator (fun y => (y + ν) ^ (p - 2)) x

theorem occ_nonneg {p ν r x : ℝ} (hν : 0 ≤ ν) (hx : 0 ≤ x) : 0 ≤ occ p ν r x := by
  unfold occ; by_cases h : x < r
  · simp only [mem_ofPred_eq, h, indicator_of_mem]; exact Real.rpow_nonneg (by linarith) _
  · simp only [mem_ofPred_eq, h, not_false_eq_true, indicator_of_notMem]; exact le_rfl

theorem occ_le {p ν r x : ℝ} (hp : p < 2) (hν : 0 < ν) (hx : 0 ≤ x) : occ p ν r x ≤ ν ^ (p - 2) := by
  unfold occ; by_cases h : x < r
  · simp only [mem_ofPred_eq, h, indicator_of_mem]
    exact Real.rpow_le_rpow_of_nonpos hν (by linarith) (by linarith)
  · simp only [mem_ofPred_eq, h, not_false_eq_true, indicator_of_notMem]; exact (Real.rpow_pos_of_pos hν _).le

theorem measurable_occ (p ν r : ℝ) : Measurable (occ p ν r) := by
  unfold occ
  exact ((measurable_id.add_const ν).pow_const (p - 2)).indicator (measurableSet_lt measurable_id measurable_const)

/-! ### Continuity of `f'` and `f''` -/

theorem continuous_cut (r : ℝ) : Continuous (cut r) :=
  Real.smoothTransition.continuous.comp (continuous_const.sub (continuous_id.div_const r))

theorem continuous_cut1 (r : ℝ) : Continuous (cut1 r) :=
  ((contDiff_deriv_smoothTransition.continuous.comp (continuous_const.sub (continuous_id.div_const r))).div_const
    r).neg

theorem continuous_cut2 (r : ℝ) : Continuous (cut2 r) :=
  (continuous_deriv_deriv_smoothTransition.comp (continuous_const.sub (continuous_id.div_const r))).div_const _

theorem continuousOn_rpow_add {ν q : ℝ} : ContinuousOn (fun x : ℝ => (x + ν) ^ q) (Ioi (-ν)) := fun x hx => by
  have hx' : x + ν ≠ 0 := by simp only [Set.mem_Ioi] at hx; linarith
  exact ((continuousAt_id.add continuousAt_const).rpow_const (Or.inl hx')).continuousWithinAt

theorem continuousOn_fn1 {p ν r : ℝ} : ContinuousOn (fn1 p ν r) (Ioi (-ν)) := by
  unfold fn1 pw1 pw
  exact ((continuousOn_const.mul continuousOn_rpow_add).mul (continuous_cut r).continuousOn).add
    ((continuousOn_rpow_add.sub continuousOn_const).mul (continuous_cut1 r).continuousOn)

theorem continuousOn_fn2 {p ν r : ℝ} : ContinuousOn (fn2 p ν r) (Ioi (-ν)) := by
  unfold fn2 pw2 pw1 pw
  exact (((continuousOn_const.mul continuousOn_rpow_add).mul (continuous_cut r).continuousOn).add
    (continuousOn_const.mul ((continuousOn_const.mul continuousOn_rpow_add).mul
      (continuous_cut1 r).continuousOn))).add
    ((continuousOn_rpow_add.sub continuousOn_const).mul (continuous_cut2 r).continuousOn)

/-! ### The generator along a path -/

section Path

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The constant `C₂` bounding the generator from below on `[r, 2r]`. -/
def cst2 (κ p r K : ℝ) (nL nR : ℕ) (Rw a : ℝ) : ℝ := bnd1 p r K * cstV nL nR Rw a r + κ / 2 * bnd2 p r K

theorem cst2_nonneg {κ p r K Rw a : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r) (hK : 0 ≤ K) (hR : 0 ≤ Rw) (ha : 0 < a) :
    0 ≤ cst2 κ p r K nL nR Rw a := by
  unfold cst2
  have := bnd1_nonneg (p := p) hr hK; have := bnd2_nonneg (p := p) hr hK
  have := cstV_nonneg (nL := nL) (nR := nR) hR ha hr
  positivity

/-- The gap `X₁` read off GB5's coordinates. -/
theorem gapX_coordAt (κ : ℝ) (i0 : Fin nR) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) :
    gapX κ (coordAt κ i0 i0 w vR b t, b t) = vR i0 t - w t := by
  simp only [gapX, coordAt]; ring

/-- **The generator bound at one time.** At a non-collision time `s < ζ` with the far right gaps at least `g`, under
the parameter constraints of the proof (`κ(1 − p) ≤ ε`, `2rC₀ ≤ ε/4`, `8r ≤ a`, `2r < g`), the Itô generator of the
DS1 observable is at least `c₀ h_ν(X₁) − C₂`. -/
theorem itoGen_ge_path (hP : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 < κ) (hnR : 0 < nR)
    {mR : ℕ} (hmR : mR ≤ nR) {p ν r ε Rw g a K : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hν : 0 < ν) (hνr : ν ≤ r)
    (hr : 0 < r) (hra : 8 * r ≤ a) (hrg : 2 * r < g) (hκp : κ * (1 - p) ≤ ε)
    (hrC : 2 * r * cst0 nL nR Rw g a ≤ ε / 4) (hR : 0 ≤ Rw) (hg : 0 < g) (ha : 0 < a)
    (hρL : ∀ i, |ρL i| ≤ Rw) (hρR : ∀ j, |ρR j| ≤ Rw)
    (hin : ∀ j : Fin nR, (j : ℕ) < mR → ε ≤ ∑ l ∈ univ.filter (fun l => l ≤ j), ρR l + 2)
    (hcross : ∀ i, a ≤ xR ⟨0, hnR⟩ - xL i)
    (hK : ∀ y, |deriv Real.smoothTransition y| ≤ K ∧ |deriv (deriv Real.smoothTransition) y| ≤ K)
    {s : ℝ} (hsζ : (s.toNNReal : ℝ≥0∞) < ζ)
    (hfar : ∀ j : Fin nR, mR ≤ (j : ℕ) → g ≤ vR j s.toNNReal - w s.toNNReal)
    (hncL : ∀ i, w s.toNNReal ≠ vL i s.toNNReal) (hncR : ∀ i, w s.toNNReal ≠ vR i s.toNNReal) :
    p * ε / 4 * occ p ν r (vR ⟨0, hnR⟩ s.toNNReal - w s.toNNReal) - cst2 κ p r K nL nR Rw a ≤
      Ito.itoGen (obs κ p ν r) (coordAt κ ⟨0, hnR⟩ ⟨0, hnR⟩ w vR b s.toNNReal, b s.toNNReal)
        (densAt ρL ρR ⟨0, hnR⟩ ⟨0, hnR⟩ w vL vR s) := by
  set i0 : Fin nR := ⟨0, hnR⟩
  set t := s.toNNReal
  have hF := hP.isForcePath
  set X : Fin nR → ℝ := fun j => vR j t - w t with hX
  set Y : Fin nL → ℝ := fun i => w t - vL i t with hY
  have hXpos : ∀ j, 0 < X j := fun j => sub_pos.2 (lt_of_le_of_ne (hF.w_le_vR hsζ j) (hncR j))
  have hYpos : ∀ i, 0 < Y i := fun i => sub_pos.2 (lt_of_le_of_ne (hF.vL_le_w hsζ i) (fun h => hncL i h.symm))
  have hXm : Monotone X := fun j j' hjj' => by
    simp only [hX]; linarith [hF.monotone_vR hsζ hjj']
  -- the cross gap
  have hcr : ∀ i, a ≤ X i0 + Y i := fun i => by
    have h1 := hF.le_vR_of_le (zero_le (a := t)) hsζ i0
    have h2 := hF.vL_le_of_le (zero_le (a := t)) hsζ i
    rw [hF.vR_zero] at h1; rw [hF.vL_zero] at h2
    simp only [hX, hY]; linarith [hcross i]
  have hq : (coordAt κ i0 i0 w vR b t, b t) ∈ obsRegion κ ν := by
    show 0 < gapX κ _ + ν
    rw [gapX_coordAt]; linarith [hXpos i0]
  rw [itoGen_obs hκ.le hq, gapX_coordAt, densAt_fst_eq hnR]
  change p * ε / 4 * occ p ν r (X i0) - _ ≤ fn1 p ν r (X i0) * (2 / X i0 + ∑ j, ρR j / X j - ∑ i, ρL i / Y i) +
    κ / 2 * fn2 p ν r (X i0)
  have hC2 := cst2_nonneg (nL := nL) (nR := nR) (p := p) hκ.le hr
    ((abs_nonneg _).trans (hK 0).1) hR ha
  have hpε : 0 ≤ p * ε / 4 := by
    have : 0 ≤ ε := le_trans (mul_nonneg hκ.le (by linarith)) hκp
    positivity
  rcases lt_or_ge (X i0) (2 * r) with h2 | h2
  · -- the left gaps are at least `3a/4`
    have hY3 : ∀ i, 3 * a / 4 ≤ Y i := fun i => by linarith [hcr i]
    rcases lt_or_ge (X i0) r with h1 | h1
    · have hocc : occ p ν r (X i0) = (X i0 + ν) ^ (p - 2) := by
        simp only [occ, mem_ofPred_eq, h1, indicator_of_mem]
      rw [hocc]
      have hv := drift_ge hnR hmR hR hg ha hρL hρR (hXpos i0) hXm hfar hin hY3 (by linarith)
      have := gen_ge_of_lt hp0 hp1 hκ.le hν hνr hr (hXpos i0) h1 hκp (cst0_nonneg hR hg ha) hrC hv
      linarith
    · have hocc : occ p ν r (X i0) = 0 := by
        simp only [occ, mem_ofPred_eq, not_lt.2 h1, not_false_eq_true, indicator_of_notMem]
      rw [hocc, mul_zero, zero_sub]
      have hv := abs_drift_le hnR hR ha hr hρL hρR h1 hXm hY3
      exact gen_ge_of_mem_Icc hp0 hp1 hκ.le hν hνr hr h1 h2.le hv hK
  · have hocc : occ p ν r (X i0) = 0 := by
      simp only [occ, mem_ofPred_eq, not_lt.2 (le_trans (by linarith : r ≤ 2 * r) h2), not_false_eq_true,
        indicator_of_notMem]
    rw [hocc, mul_zero, zero_sub, gen_eq_zero_of_ge hr h2]
    linarith

end Path

end DS1

end Supp12

end InteractingSLE

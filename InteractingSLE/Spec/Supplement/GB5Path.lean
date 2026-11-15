/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB5Lyap
import InteractingSLE.Spec.Ito.Coordinates
import InteractingSLE.Spec.Sec2.TerminalPath
import InteractingSLE.Spec.Sec4.RepulsionDrift

/-!
# Lemma GB5: pathwise facts along one integrated path

Packet PROVE-T14-GB. Along a path satisfying the frozen `IsIntegratedSLEPath` (Definition 2.1), for a right label `j`
and the nearest right label `i₀ = 0`, the Itô coordinates of `GB5Lyap.lean` are

  `Λ_t = (V^j_t − W_t + √k b_t, V^j_t − V^{i₀}_t)`,  `x = Λ₁ − √k b = X_j`,  `d = V^j − V^{i₀}`,

with density `λ_s = (2/X_j − μ_s, 2/X_j − 2/X_{i₀})` (`μ` the drift of the driver, `X_i = V^i − W`).

* `coordAt_eq_add_integral`: `Λ_t = Λ_0 + ∫₀ᵗ λ` for `t < ζ` (if `b_0 = 0`);
* `integral_norm_densAt_le`: the variation bound `∫₀ᵀ ‖λ‖ ≤ gbKb` when all marks stay in `[−n, n]`;
* `exists_EA` (with `abel_lower_drop`, `A_nonneg_drop`, `H_ge_drop`): the source's `E`, `A ≥ 0`, `H ≥ ε(1/U₁ − 1)`
  at one time, from the partial-sum conditions at the current group ends (coincident marks stay coincident,
  `IsIntegratedSLEPath.vR_eq_of_xR_eq`, so current group ends are initial group ends);
* `itoGen_le_at`: at a non-collision time, the Itô generator of the Lyapunov observable is at most
  `(1 + α + pλ) |β| / X_j` (`β` the opposite-side drift of `X_j`);
* `integral_itoGen_le`: its integral over `[0, T]` is at most the constant `gbCst` while either the nearest left gap
  is at least `γ` or `X_j ≥ γ'` (the localization of the opposite group; source: "the opposite driving drift is
  bounded on that entire stopped interval").
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB5

variable {nL nR : ℕ}

/-! ### Coordinates and density -/

/-- The Itô coordinates `(V^j − W + √k b, V^j − V^{i₀})`. -/
def coordAt (k : ℝ) (j i₀ : Fin nR) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) :
    ℝ × ℝ :=
  (vR j t - w t + Real.sqrt k * b t, vR j t - vR i₀ t)

/-- Their density at real time `s`: `(2/X_j − μ, 2/X_j − 2/X_{i₀})`. -/
def densAt (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j i₀ : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ) : ℝ × ℝ :=
  (2 / (vR j s.toNNReal - w s.toNNReal) - Ito.driftAt ρL ρR w vL vR s,
    2 / (vR j s.toNNReal - w s.toNNReal) - 2 / (vR i₀ s.toNNReal - w s.toNNReal))

/-- The drift of `X_j` from the opposite (left) side, `β = −Σ ρ^L_i/(W − V^{L,i})`. -/
def betaAt (ρL : Fin nL → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  -∑ i, ρL i / (w s.toNNReal - vL i s.toNNReal)

theorem lyapX_coordAt (k : ℝ) (j i₀ : Fin nR) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ)
    (t : ℝ≥0) : lyapX k (coordAt k j i₀ w vR b t, b t) = vR j t - w t := by
  simp only [lyapX, coordAt]; ring

variable {k : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  {j i₀ : Fin nR}

theorem intervalIntegrable_two_div_gapR (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    IntervalIntegrable (fun s : ℝ => 2 / (vR i s.toNNReal - w s.toNNReal)) volume 0 t :=
  Ito.intervalIntegrable_two_div_sub (hP.isForcePath.integrable_gapR ht i)

theorem intervalIntegrable_densAt (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    IntervalIntegrable (densAt ρL ρR j i₀ w vL vR) volume 0 t := by
  have h1 := (intervalIntegrable_two_div_gapR hP ht j).sub (Ito.intervalIntegrable_driftAt hP ht)
  have h2 := (intervalIntegrable_two_div_gapR hP ht j).sub (intervalIntegrable_two_div_gapR hP ht i₀)
  rw [intervalIntegrable_iff] at h1 h2 ⊢
  exact h1.prodMk h2

theorem integral_densAt_fst {t : ℝ}
    (hg : IntervalIntegrable (densAt ρL ρR j i₀ w vL vR) volume 0 t) :
    (∫ s in (0 : ℝ)..t, densAt ρL ρR j i₀ w vL vR s).1 =
      ∫ s in (0 : ℝ)..t, (densAt ρL ρR j i₀ w vL vR s).1 :=
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).intervalIntegral_comp_comm hg).symm

theorem integral_densAt_snd {t : ℝ}
    (hg : IntervalIntegrable (densAt ρL ρR j i₀ w vL vR) volume 0 t) :
    (∫ s in (0 : ℝ)..t, densAt ρL ρR j i₀ w vL vR s).2 =
      ∫ s in (0 : ℝ)..t, (densAt ρL ρR j i₀ w vL vR s).2 :=
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).intervalIntegral_comp_comm hg).symm

/-- **The coordinates are absolutely continuous**: `Λ_t = Λ_0 + ∫₀ᵗ λ` for `t < ζ`, if `b_0 = 0`. -/
theorem coordAt_eq_add_integral (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) (hb0 : b 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    coordAt k j i₀ w vR b t = coordAt k j i₀ w vR b 0 + ∫ s in (0 : ℝ)..t, densAt ρL ρR j i₀ w vL vR s := by
  have hF := hP.isForcePath
  have hint := intervalIntegrable_densAt (j := j) (i₀ := i₀) hP ht
  have hj := hF.vR_eq ht j
  have hi := hF.vR_eq ht i₀
  have hw := Ito.w_eq_sqrt_mul_add_integral hP ht
  have hw0 : w 0 = 0 := hF.w_zero
  have hj0 : vR j 0 = xR j := hF.vR_zero j
  have hi0 : vR i₀ 0 = xR i₀ := hF.vR_zero i₀
  refine Prod.ext ?_ ?_
  · rw [Prod.fst_add, integral_densAt_fst hint]
    simp only [densAt, coordAt]
    rw [intervalIntegral.integral_sub (intervalIntegrable_two_div_gapR hP ht j)
      (Ito.intervalIntegrable_driftAt hP ht), hw0, hj0, hb0]
    rw [hw] at *
    linarith
  · rw [Prod.snd_add, integral_densAt_snd hint]
    simp only [densAt, coordAt]
    rw [intervalIntegral.integral_sub (intervalIntegrable_two_div_gapR hP ht j)
      (intervalIntegrable_two_div_gapR hP ht i₀), hj0, hi0]
    linarith

/-! ### The variation bound -/

/-- The bound on the variation of the coordinates when all marks stay in `[−n, n]`. -/
def gbKb (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (j i₀ : Fin nR) (n : ℝ) :
    ℝ :=
  2 * (n + |xR j|) + (n + |xR i₀|) + (∑ i, |ρL i| * ((|xL i| + n) / 2)) +
    ∑ i, |ρR i| * ((n + |xR i|) / 2)

theorem intervalIntegrable_inv_gapR' (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) :
    IntervalIntegrable (fun s : ℝ => (vR i s.toNNReal - w s.toNNReal)⁻¹) volume 0 t := by
  refine ((hP.isForcePath.integrable_gapR ht i).neg).congr fun s _ => ?_
  simp only [Pi.neg_apply]
  rw [← inv_neg, neg_sub]

theorem integral_inv_gapR_le (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nR) {n : ℝ} (hn : |vR i t| ≤ n) :
    ∫ s in (0 : ℝ)..t, (vR i s.toNNReal - w s.toNNReal)⁻¹ ≤ (n + |xR i|) / 2 := by
  rw [Ito.integral_inv_gap_eq_right (hP.isForcePath.vR_eq ht i)]
  have := le_abs_self (vR i t)
  have := neg_abs_le (xR i)
  linarith

theorem integral_inv_gapL_le (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (i : Fin nL) {n : ℝ} (hn : |vL i t| ≤ n) :
    ∫ s in (0 : ℝ)..t, (w s.toNNReal - vL i s.toNNReal)⁻¹ ≤ (|xL i| + n) / 2 := by
  rw [Ito.integral_inv_gap_eq (hP.isForcePath.vL_eq ht i)]
  have := neg_abs_le (vL i t)
  have := le_abs_self (xL i)
  linarith

theorem abs_div_gapR {ρ wv v : ℝ} (h : wv ≤ v) : |ρ / (wv - v)| = |ρ| * (v - wv)⁻¹ := by
  rw [abs_div, div_eq_mul_inv, abs_of_nonpos (by linarith : wv - v ≤ 0), neg_sub]

theorem abs_div_gapL {ρ wv v : ℝ} (h : v ≤ wv) : |ρ / (wv - v)| = |ρ| * (wv - v)⁻¹ := by
  rw [abs_div, div_eq_mul_inv, abs_of_nonneg (by linarith : 0 ≤ wv - v)]

/-- **The variation bound**: `∫₀ᵀ ‖λ‖ ≤ gbKb` if all marks are in `[−n, n]` at time `T < ζ`. -/
theorem integral_norm_densAt_le (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) {n : ℝ} (hL : ∀ i, |vL i T| ≤ n) (hR : ∀ i, |vR i T| ≤ n) :
    ∫ s in (0 : ℝ)..T, ‖densAt ρL ρR j i₀ w vL vR s‖ ≤ gbKb xL xR ρL ρR j i₀ n := by
  have hF := hP.isForcePath
  set gR : Fin nR → ℝ → ℝ := fun i s => (vR i s.toNNReal - w s.toNNReal)⁻¹ with hgR
  set gL : Fin nL → ℝ → ℝ := fun i s => (w s.toNNReal - vL i s.toNNReal)⁻¹ with hgL
  have iR : ∀ i, IntervalIntegrable (gR i) volume 0 T := fun i => intervalIntegrable_inv_gapR' hP hT i
  have iL : ∀ i, IntervalIntegrable (gL i) volume 0 T := fun i => hF.integrable_gapL hT i
  set g : ℝ → ℝ := fun s => 4 * gR j s + 2 * gR i₀ s + (∑ i, |ρL i| * gL i s) +
    ∑ i, |ρR i| * gR i s with hg
  have iLs : IntervalIntegrable (fun s => ∑ i, |ρL i| * gL i s) volume 0 T := by
    have := IntervalIntegrable.sum univ fun i _ => (iL i).const_mul |ρL i|
    simpa only [Finset.sum_fn] using this
  have iRs : IntervalIntegrable (fun s => ∑ i, |ρR i| * gR i s) volume 0 T := by
    have := IntervalIntegrable.sum univ fun i _ => (iR i).const_mul |ρR i|
    simpa only [Finset.sum_fn] using this
  have ig : IntervalIntegrable g volume 0 T :=
    ((((iR j).const_mul 4).add ((iR i₀).const_mul 2)).add iLs).add iRs
  have hle : ∫ s in (0 : ℝ)..T, ‖densAt ρL ρR j i₀ w vL vR s‖ ≤ ∫ s in (0 : ℝ)..T, g s := by
    refine intervalIntegral.integral_mono_on T.coe_nonneg
      (intervalIntegrable_densAt hP hT).norm ig fun s hs => ?_
    have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hs.2
    have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hsT) hT
    have hwR : ∀ i, w s.toNNReal ≤ vR i s.toNNReal := fun i => hF.w_le_vR hsζ i
    have hwL : ∀ i, vL i s.toNNReal ≤ w s.toNNReal := fun i => hF.vL_le_w hsζ i
    have hgR0 : ∀ i, 0 ≤ gR i s := fun i => inv_nonneg.2 (sub_nonneg.2 (hwR i))
    have hgL0 : ∀ i, 0 ≤ gL i s := fun i => inv_nonneg.2 (sub_nonneg.2 (hwL i))
    have h2R : ∀ i, |2 / (vR i s.toNNReal - w s.toNNReal)| = 2 * gR i s := fun i => by
      rw [abs_div, abs_two, abs_of_nonneg (sub_nonneg.2 (hwR i)), div_eq_mul_inv]
    have hdrift : |Ito.driftAt ρL ρR w vL vR s| ≤ (∑ i, |ρL i| * gL i s) + ∑ i, |ρR i| * gR i s := by
      unfold Ito.driftAt
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
        exact abs_div_gapL (hwL i)
      · refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ => ?_))
        exact abs_div_gapR (hwR i)
    have hn : ‖densAt ρL ρR j i₀ w vL vR s‖ ≤ |(densAt ρL ρR j i₀ w vL vR s).1| +
        |(densAt ρL ρR j i₀ w vL vR s).2| := by
      rw [Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
    refine hn.trans ?_
    simp only [densAt]
    have e1 := abs_sub (2 / (vR j s.toNNReal - w s.toNNReal)) (Ito.driftAt ρL ρR w vL vR s)
    have e2 := abs_sub (2 / (vR j s.toNNReal - w s.toNNReal)) (2 / (vR i₀ s.toNNReal - w s.toNNReal))
    rw [h2R j] at e1 e2
    rw [h2R i₀] at e2
    simp only [hg]
    linarith
  have heq : ∫ s in (0 : ℝ)..T, g s = 4 * (∫ s in (0 : ℝ)..T, gR j s) +
      2 * (∫ s in (0 : ℝ)..T, gR i₀ s) + (∑ i, |ρL i| * ∫ s in (0 : ℝ)..T, gL i s) +
      ∑ i, |ρR i| * ∫ s in (0 : ℝ)..T, gR i s := by
    simp only [hg]
    rw [intervalIntegral.integral_add ((((iR j).const_mul 4).add ((iR i₀).const_mul 2)).add iLs) iRs,
      intervalIntegral.integral_add (((iR j).const_mul 4).add ((iR i₀).const_mul 2)) iLs,
      intervalIntegral.integral_add ((iR j).const_mul 4) ((iR i₀).const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum fun i _ => (iL i).const_mul |ρL i|,
      intervalIntegral.integral_finsetSum fun i _ => (iR i).const_mul |ρR i|]
    simp only [intervalIntegral.integral_const_mul]
  refine hle.trans (heq.trans_le ?_)
  unfold gbKb
  have hj := integral_inv_gapR_le hP hT j (hR j)
  have hi := integral_inv_gapR_le hP hT i₀ (hR i₀)
  have hLs : (∑ i, |ρL i| * ∫ s in (0 : ℝ)..T, gL i s) ≤ ∑ i, |ρL i| * ((|xL i| + n) / 2) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (integral_inv_gapL_le hP hT i (hL i))
      (abs_nonneg _)
  have hRs : (∑ i, |ρR i| * ∫ s in (0 : ℝ)..T, gR i s) ≤ ∑ i, |ρR i| * ((n + |xR i|) / 2) :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (integral_inv_gapR_le hP hT i (hR i))
      (abs_nonneg _)
  linarith

/-! ### The source's hypotheses at one time -/

/-- ℕ-indexed weights (`0` beyond `nR`). -/
def rhoN (ρR : Fin nR → ℝ) (i : ℕ) : ℝ := if h : i < nR then ρR ⟨i, h⟩ else 0

/-- ℕ-indexed gaps (`1` beyond `nR`). -/
def gapN (g : Fin nR → ℝ) (i : ℕ) : ℝ := if h : i < nR then g ⟨i, h⟩ else 1

theorem gapN_fin (g : Fin nR → ℝ) (i : Fin nR) : gapN g i = g i := by
  simp [gapN, i.2]

theorem sum_div_eq_sum_range (ρR g : Fin nR → ℝ) :
    ∑ i, ρR i / g i = ∑ i ∈ range nR, rhoN ρR i / gapN g i := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => rhoN ρR i / gapN g i) nR]
  refine sum_congr rfl fun i _ => ?_
  simp [rhoN, gapN, i.2]

theorem partialSum_eq (ρR : Fin nR → ℝ) (i : Fin nR) :
    ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l = ∑ l ∈ range (i.1 + 1), rhoN ρR l :=
  Sec4.sum_filter_le_eq_sum_range ρR i

/-- **Abel lower bound with conditions only where `f` drops**: if `f` is nonincreasing on `[0, n]` and the partial
sum `S_i` is at least `L` whenever `f_{i+1} < f_i`, then `L (f₀ − f_n) ≤ Σ_{i<n} a_i (f_i − f_n)`. (The source's
compression of coincident groups: the terms with `f_{i+1} = f_i` vanish.) -/
theorem abel_lower_drop {a f : ℕ → ℝ} {n : ℕ} {L : ℝ} (hf : ∀ i < n, f (i + 1) ≤ f i)
    (hS : ∀ i < n, f (i + 1) < f i → L ≤ ∑ l ∈ range (i + 1), a l) :
    L * (f 0 - f n) ≤ ∑ i ∈ range n, a i * (f i - f n) := by
  rw [Supp8.abel_sum, ← Supp8.sum_sub_succ, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  rcases (hf i hi').lt_or_eq with h | h
  · exact mul_le_mul_of_nonneg_right (hS i hi' h) (sub_nonneg.2 (hf i hi'))
  · rw [h, sub_self, mul_zero, mul_zero]

/-- **GB5, the outer group, with group-end conditions**: `0 ≤ A = X₀ Σ_{i<n} ρ_i/X_i − L` if `X` is positive and
nondecreasing and `S_i ≥ L` at every group end (`X_i < X_{i+1}`, or `i` the last label). -/
theorem A_nonneg_drop {ρ X : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hX : ∀ i < n, 0 < X i)
    (hmono : ∀ i, i + 1 < n → X i ≤ X (i + 1)) {L : ℝ}
    (hS : ∀ i < n, (i + 1 < n → X i < X (i + 1)) → L ≤ ∑ l ∈ range (i + 1), ρ l) :
    0 ≤ X 0 * ∑ i ∈ range n, ρ i / X i - L := by
  have hX0 := hX 0 hn
  set r : ℕ → ℝ := fun i => X 0 / X i with hr
  have hsum : X 0 * ∑ i ∈ range n, ρ i / X i = ∑ i ∈ range n, ρ i * r i := by
    rw [mul_sum]; exact sum_congr rfl fun i _ => by simp only [hr]; ring
  have hra : ∀ i, i + 1 < n → r (i + 1) ≤ r i := fun i hi =>
    div_le_div_of_nonneg_left hX0.le (hX i (by omega)) (hmono i hi)
  have hr0 : ∀ i < n, 0 ≤ r i := fun i hi => (div_pos hX0 (hX i hi)).le
  have hlow := abel_lower_drop (a := ρ) (f := Supp8.truncZero r n) (L := L)
    (Supp8.truncZero_antitone hra hr0) (fun i hi hlt => hS i hi fun hi1 => by
      simp only [Supp8.truncZero, hi1, hi, ↓reduceIte, hr] at hlt
      exact (div_lt_div_iff_of_pos_left hX0 (hX (i + 1) hi1) (hX i hi)).1 hlt)
  rw [Supp8.sum_mul_truncZero] at hlow
  have h0 : Supp8.truncZero r n 0 = 1 := by simp [Supp8.truncZero, hn, hr, div_self hX0.ne']
  have hn' : Supp8.truncZero r n n = 0 := by simp [Supp8.truncZero]
  rw [h0, hn', sub_zero, mul_one] at hlow
  rw [hsum]
  linarith

/-- **GB5, the inner group, with group-end conditions**: `H ≥ ε (1/U₁ − 1)` if `U` is positive and nondecreasing up
to `U_n = 1` and `ε ≤ S_i + 2` at every group end (`U_i < U_{i+1}`). -/
theorem H_ge_drop {ρ U : ℕ → ℝ} {n : ℕ} (hUn : U n = 1) (hU : ∀ i ≤ n, 0 < U i)
    (hmono : ∀ i < n, U i ≤ U (i + 1)) {ε : ℝ}
    (hε : ∀ i < n, U i < U (i + 1) → ε ≤ ∑ l ∈ range (i + 1), ρ l + 2) :
    ε * (1 / U 0 - 1) ≤ ∑ i ∈ range n, ρ i * (1 / U i - 1) + 2 * (1 / U 0 - 1) := by
  rw [Supp8.gb5_H_eq ρ U n hUn]
  have ht := Supp8.sum_sub_succ (fun i => 1 / U i) n
  simp only [hUn, div_one] at ht
  rw [← ht, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have hi' := mem_range.1 hi
  rcases (hmono i hi').lt_or_eq with h | h
  · exact mul_le_mul_of_nonneg_right (hε i hi' h)
      (sub_nonneg.2 (one_div_le_one_div_of_le (hU i hi'.le) (hmono i hi')))
  · rw [h, sub_self, mul_zero, mul_zero]

/-- **The source's quantities `E`, `A`, `H` at one time.** For positive nondecreasing right gaps `g`, a label `j`,
and the partial-sum conditions at the current group ends (`g_i < g_{i'}` for all `i' > i`): `ε ≤ S_i + 2` for `i < j`
and `S_i ≥ c` for `i ≥ j`. Then there are `E`, `A` with `2 + g_j Σ ρ_i/g_i − k/2 = E + A` (`gb5_drift_logX`),
`A ≥ 0` and `ε (g_j/g_0 − 1) ≤ E + 2 (g_j/g_0 − 1)`. -/
theorem exists_EA (j : Fin nR) (hnR : 0 < nR) {ρR g : Fin nR → ℝ} (hg : ∀ i, 0 < g i) (hgm : Monotone g)
    {εH : ℝ} (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → g i < g i') →
      εH ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2)
    (hout : ∀ i : Fin nR, j ≤ i → (∀ i', i < i' → g i < g i') →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l) :
    ∃ E A : ℝ, 2 + g j * ∑ i, ρR i / g i - k / 2 = E + A ∧ 0 ≤ A ∧
      εH * (g j / g ⟨0, hnR⟩ - 1) ≤ E + 2 * (g j / g ⟨0, hnR⟩ - 1) := by
  set ρ := rhoN ρR with hρ
  set X := gapN g with hX
  have hjN : (j : ℕ) < nR := j.2
  have hXj : X j = g j := gapN_fin g j
  have hX0 : X 0 = g ⟨0, hnR⟩ := by simp [hX, gapN, hnR]
  have hXpos : ∀ i, i < nR → 0 < X i := fun i hi => by simp only [hX, gapN, hi, ↓reduceDIte]; exact hg _
  have hXmono : ∀ i, i + 1 < nR → X i ≤ X (i + 1) := fun i hi => by
    simp only [hX, gapN, hi, (by omega : i < nR), ↓reduceDIte]
    exact hgm (show (⟨i, by omega⟩ : Fin nR) ≤ ⟨i + 1, hi⟩ from Fin.mk_le_mk.2 (by omega))
  -- a jump of `X` at `i` makes `i` a current group end
  have hend : ∀ i (hi : i < nR), (i + 1 < nR → X i < X (i + 1)) →
      ∀ i' : Fin nR, (⟨i, hi⟩ : Fin nR) < i' → g ⟨i, hi⟩ < g i' := by
    intro i hi hjump i' hii'
    have hi1 : i + 1 < nR := lt_of_le_of_lt (Fin.lt_def.1 hii') i'.2
    have h1 := hjump hi1
    simp only [hX, gapN, hi, hi1, ↓reduceDIte] at h1
    exact lt_of_lt_of_le h1 (hgm (Fin.mk_le_of_le_val (by have := Fin.lt_def.1 hii'; simp at this; omega)))
  set s := ∑ i ∈ range j, ρ i with hs
  refine ⟨∑ i ∈ range j, ρ i * (X j / X i - 1),
    X j * ∑ i ∈ Ico (j : ℕ) nR, ρ i / X i - ((k / 2 - 2) - s), ?_, ?_, ?_⟩
  · have h := Supp8.gb5_drift_logX ρ X hjN.le k
    rw [sum_div_eq_sum_range, ← hXj]
    exact h
  · -- the outer group
    have hn : 0 < nR - j := by omega
    have hA := A_nonneg_drop (ρ := fun i => ρ (j + i)) (X := fun i => X (j + i)) hn
      (fun i hi => hXpos _ (by omega)) (fun i hi => by
        have := hXmono (j + i) (by omega); simpa [add_assoc] using this)
      (L := k / 2 - 2 - s) (fun i hi hjump => by
        have h1 := hout ⟨j + i, by omega⟩ (Fin.mk_le_mk.2 (by simp))
          (hend (j + i) (by omega) fun h' => by
            have := hjump (by omega); simpa [add_assoc] using this)
        rw [partialSum_eq] at h1
        have h2 : ∑ l ∈ range (j + i + 1), ρ l = s + ∑ l ∈ range (i + 1), ρ (j + l) := by
          rw [show j + i + 1 = (j : ℕ) + (i + 1) by ring, Finset.sum_range_add]
        simp only at h1
        rw [h2] at h1
        linarith)
    rw [Finset.sum_Ico_eq_sum_range]
    simpa using hA
  · -- the inner group
    have hjpos : 0 < X j := hXpos j hjN
    have h := H_ge_drop (ρ := ρ) (U := fun i => X i / X j) (n := j) (div_self hjpos.ne')
      (fun i hi => div_pos (hXpos i (by omega)) hjpos)
      (fun i hi => div_le_div_of_nonneg_right (hXmono i (by omega)) hjpos.le)
      (ε := εH) (fun i hi hlt => by
        have hlt' : X i < X (i + 1) := (div_lt_div_iff_of_pos_right hjpos).1 hlt
        have h1 := hin ⟨i, by omega⟩ (Fin.mk_lt_mk.2 hi) (hend i (by omega) fun _ => hlt')
        rwa [partialSum_eq] at h1)
    simp only [one_div_div] at h
    rw [hX0, hXj] at h
    rw [hXj]
    exact h

/-! ### The generator bound along the path -/

/-- **The pointwise generator bound** at a time at which every right mark is strictly right of the driver and
`V^{i₀} < V^j` (`i₀ = 0`): `itoGen F ≤ (1 + α + pλ) |β| / X_j`. -/
theorem itoGen_le_at (hk : 0 < k) {εH : ℝ} (hε : 0 < εH) (hnR : 0 < nR) {t : ℝ≥0}
    (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → vR i t < vR i' t) →
      εH ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2)
    (hout : ∀ i : Fin nR, j ≤ i → (∀ i', i < i' → vR i t < vR i' t) →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l)
    (hmono : Monotone fun i => vR i t) (hgap : ∀ i, w t < vR i t)
    (hd : vR ⟨0, hnR⟩ t < vR j t) :
    Ito.itoGen (lyapObs k εH) (coordAt k j ⟨0, hnR⟩ w vR b t, b t)
        (densAt ρL ρR j ⟨0, hnR⟩ w vL vR t) ≤
      (1 + alphaC εH + expoC k * lamC k εH) * |betaAt ρL w vL t| / (vR j t - w t) := by
  set g : Fin nR → ℝ := fun i => vR i t - w t with hgdef
  have hg : ∀ i, 0 < g i := fun i => sub_pos.2 (hgap i)
  have hgm : Monotone g := fun i i' hii' => sub_le_sub_right (hmono hii') _
  obtain ⟨E, A, hQ, hA, hH⟩ := exists_EA (k := k) j hnR hg hgm
    (fun i hi hge => hin i hi fun i' hii' => by have := hge i' hii'; simp only [hgdef] at this; linarith)
    (fun i hi hge => hout i hi fun i' hii' => by have := hge i' hii'; simp only [hgdef] at this; linarith)
  set q := (coordAt k j ⟨0, hnR⟩ w vR b t, b t) with hqdef
  have hx : lyapX k q = g j := lyapX_coordAt k j _ w vR b t
  have hq2 : q.1.2 = vR j t - vR ⟨0, hnR⟩ t := rfl
  have hxd : lyapX k q - q.1.2 = g ⟨0, hnR⟩ := by rw [hx, hq2]; simp only [hgdef]; ring
  have hreg : q ∈ lyapRegion k := ⟨by rw [hx]; exact hg j, by rw [hq2]; linarith⟩
  have hdx : q.1.2 < lyapX k q := by have := hg ⟨0, hnR⟩; linarith
  have hsumR : ∑ i, ρR i / (w t - vR i t) = -∑ i, ρR i / g i := by
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [hgdef]
    rw [← neg_sub, div_neg]
  have hvec : densAt ρL ρR j ⟨0, hnR⟩ w vL vR t =
      ((2 + g j * ∑ i, ρR i / g i) / lyapX k q + betaAt ρL w vL t,
        2 / lyapX k q - 2 / (lyapX k q - q.1.2)) := by
    rw [hxd, hx]
    have hj0 : g j ≠ 0 := (hg j).ne'
    refine Prod.ext ?_ ?_
    · simp only [densAt, Real.toNNReal_coe, Ito.driftAt, betaAt]
      rw [hsumR, add_div, mul_div_cancel_left₀ _ hj0]
      ring
    · simp only [densAt, Real.toNNReal_coe]
      rfl
  rw [hvec]
  have h := itoGen_lyapObs_le hk hε hreg hdx (β := betaAt ρL w vL t) hQ hA (by rw [hxd, hx]; exact hH)
  rw [hx] at h ⊢
  exact h

/-- The opposite-side drift over `X_j`, under the localization of the opposite group. -/
theorem abs_betaAt_div_le {γ γ' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ') {t : ℝ≥0}
    (hanti : Antitone fun i => vL i t) (hL : ∀ i, vL i t < w t) {x : ℝ} (hx : 0 < x)
    (hloc : ∀ h : 0 < nL, γ ≤ w t - vL ⟨0, h⟩ t ∨ γ' ≤ x) :
    |betaAt ρL w vL t| / x ≤
      (∑ i, |ρL i|) / γ * x⁻¹ + 1 / γ' * ∑ i, |ρL i| * (w t - vL i t)⁻¹ := by
  have hb : |betaAt ρL w vL t| ≤ ∑ i, |ρL i| * (w t - vL i t)⁻¹ := by
    simp only [betaAt, Real.toNNReal_coe, abs_neg]
    exact (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun i _ =>
      abs_div_gapL (hL i).le))
  have h0 : ∀ i, 0 ≤ |ρL i| * (w t - vL i t)⁻¹ := fun i =>
    mul_nonneg (abs_nonneg _) (inv_nonneg.2 (sub_nonneg.2 (hL i).le))
  have hA : 0 ≤ (∑ i, |ρL i|) / γ * x⁻¹ :=
    mul_nonneg (div_nonneg (sum_nonneg fun i _ => abs_nonneg _) hγ.le) (inv_nonneg.2 hx.le)
  have hB : 0 ≤ 1 / γ' * ∑ i, |ρL i| * (w t - vL i t)⁻¹ :=
    mul_nonneg (by positivity) (sum_nonneg fun i _ => h0 i)
  rcases Nat.eq_zero_or_pos nL with hnL | hnL
  · subst hnL
    have h0 : betaAt ρL w vL t = 0 := by simp [betaAt]
    rw [h0, abs_zero, zero_div]
    exact add_nonneg hA hB
  rcases hloc hnL with h | h
  · -- every left gap is at least `γ`
    have hle : ∑ i, |ρL i| * (w t - vL i t)⁻¹ ≤ (∑ i, |ρL i|) / γ := by
      rw [sum_div]
      refine sum_le_sum fun i _ => ?_
      have hi : γ ≤ w t - vL i t :=
        h.trans (sub_le_sub_left (hanti (show (⟨0, hnL⟩ : Fin nL) ≤ i from Nat.zero_le _)) _)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hγ hi) (abs_nonneg _)
    have : |betaAt ρL w vL t| / x ≤ (∑ i, |ρL i|) / γ * x⁻¹ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hb.trans hle) (inv_nonneg.2 hx.le)
    linarith
  · have : |betaAt ρL w vL t| / x ≤ 1 / γ' * ∑ i, |ρL i| * (w t - vL i t)⁻¹ := by
      rw [div_eq_mul_inv, mul_comm]
      have hxi : x⁻¹ ≤ 1 / γ' := by rw [one_div]; exact inv_anti₀ hγ' h
      exact mul_le_mul hxi hb (abs_nonneg _) (by positivity)
    linarith

/-- The constant bounding the integrated generator. -/
def gbCst (k εH γ γ' : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (j : Fin nR) (n : ℝ) :
    ℝ :=
  (1 + alphaC εH + expoC k * lamC k εH) *
    ((∑ i, |ρL i|) / γ * ((n + |xR j|) / 2) + 1 / γ' * ∑ i, |ρL i| * ((|xL i| + n) / 2))

/-- Almost every time of `[0, ζ)` is a non-collision time. -/
theorem ae_noncollision (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) :
    ∀ᵐ s : ℝ, 0 ≤ s → (s.toNNReal : ℝ≥0∞) < ζ →
      (∀ i, w s.toNNReal ≠ vL i s.toNNReal) ∧ ∀ i, w s.toNNReal ≠ vR i s.toNNReal := by
  have hF := hP.isForcePath
  have hL : ∀ i, ∀ᵐ s : ℝ, 0 ≤ s → (s.toNNReal : ℝ≥0∞) < ζ → w s.toNNReal ≠ vL i s.toNNReal :=
    fun i => (measure_eq_zero_iff_ae_notMem.1 (hF.volume_collisionL i)).mono fun s hs h0 hζ heq =>
      hs ⟨h0, hζ, heq⟩
  have hR : ∀ i, ∀ᵐ s : ℝ, 0 ≤ s → (s.toNNReal : ℝ≥0∞) < ζ → w s.toNNReal ≠ vR i s.toNNReal :=
    fun i => (measure_eq_zero_iff_ae_notMem.1 (hF.volume_collisionR i)).mono fun s hs h0 hζ heq =>
      hs ⟨h0, hζ, heq⟩
  filter_upwards [ae_all_iff.2 hL, ae_all_iff.2 hR] with s h1 h2 h0 hζ
  exact ⟨fun i => h1 i h0 hζ, fun i => h2 i h0 hζ⟩

/-- **The integrated generator bound** on `[0, T]`, `T < ζ`: if `V^{i₀} < V^j` on `[0, T]`, the opposite group is
localized (`γ ≤ W − V^{L,0}` or `γ' ≤ X_j` at every time), and the marks are in `[−n, n]` at `T`, then
`∫₀ᵀ itoGen F ≤ gbCst`. -/
theorem integral_itoGen_le (hP : IsIntegratedSLEPath k xL xR ρL ρR w vL vR b ζ) (hk : 0 < k) {εH : ℝ}
    (hε : 0 < εH) (hnR : 0 < nR) (hxm : Monotone xR)
    (hin : ∀ i : Fin nR, i < j → (∀ i', i < i' → xR i < xR i') →
      εH ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l + 2)
    (hout : ∀ i : Fin nR, j ≤ i → (∀ i', i < i' → xR i < xR i') →
      k / 2 - 2 ≤ ∑ l ∈ univ.filter (fun l => l ≤ i), ρR l)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hd : ∀ s ≤ T, vR ⟨0, hnR⟩ s < vR j s)
    {γ γ' n : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ')
    (hloc : ∀ s ≤ T, ∀ h : 0 < nL, γ ≤ w s - vL ⟨0, h⟩ s ∨ γ' ≤ vR j s - w s)
    (hL : ∀ i, |vL i T| ≤ n) (hR : |vR j T| ≤ n) :
    ∫ s in (0 : ℝ)..T, Ito.itoGen (lyapObs k εH)
        (coordAt k j ⟨0, hnR⟩ w vR b s.toNNReal, b s.toNNReal) (densAt ρL ρR j ⟨0, hnR⟩ w vL vR s) ≤
      gbCst k εH γ γ' xL xR ρL j n := by
  have hF := hP.isForcePath
  have hC0 : 0 ≤ 1 + alphaC εH + expoC k * lamC k εH := by
    have := alphaC_pos hε; have := expoC_pos hk; have := lamC_pos hk hε; positivity
  have hcst0 : 0 ≤ gbCst k εH γ γ' xL xR ρL j n := by
    unfold gbCst
    refine mul_nonneg hC0 (add_nonneg (mul_nonneg ?_ ?_) (mul_nonneg (by positivity) ?_))
    · exact div_nonneg (sum_nonneg fun i _ => abs_nonneg _) hγ.le
    · have := neg_abs_le (vR j T); have := abs_nonneg (xR j)
      have := (abs_nonneg (vR j T)).trans hR; positivity
    · refine sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) ?_
      have := (abs_nonneg (vL i T)).trans (hL i); have := abs_nonneg (xL i); positivity
  set C := 1 + alphaC εH + expoC k * lamC k εH with hC
  set bnd : ℝ → ℝ := fun s => C * ((∑ i, |ρL i|) / γ * (vR j s.toNNReal - w s.toNNReal)⁻¹ +
    1 / γ' * ∑ i, |ρL i| * (w s.toNNReal - vL i s.toNNReal)⁻¹) with hbnd
  have iR := intervalIntegrable_inv_gapR' hP hT j
  have iL : ∀ i, IntervalIntegrable (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹) volume 0 T :=
    fun i => hF.integrable_gapL hT i
  have iLs : IntervalIntegrable (fun s : ℝ => ∑ i, |ρL i| * (w s.toNNReal - vL i s.toNNReal)⁻¹)
      volume 0 T := by
    have := IntervalIntegrable.sum univ fun i _ => (iL i).const_mul |ρL i|
    simpa only [Finset.sum_fn] using this
  have ib : IntervalIntegrable bnd volume 0 T :=
    ((iR.const_mul ((∑ i, |ρL i|) / γ)).add (iLs.const_mul (1 / γ'))).const_mul C
  have hib : ∫ s in (0 : ℝ)..T, bnd s ≤ gbCst k εH γ γ' xL xR ρL j n := by
    simp only [hbnd]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (iR.const_mul ((∑ i, |ρL i|) / γ)) (iLs.const_mul (1 / γ')), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun i _ =>
        (iL i).const_mul |ρL i|]
    simp only [intervalIntegral.integral_const_mul]
    unfold gbCst
    refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hC0
    · exact mul_le_mul_of_nonneg_left (integral_inv_gapR_le hP hT j hR)
        (div_nonneg (sum_nonneg fun i _ => abs_nonneg _) hγ.le)
    · refine mul_le_mul_of_nonneg_left (sum_le_sum fun i _ => ?_) (by positivity)
      exact mul_le_mul_of_nonneg_left (integral_inv_gapL_le hP hT i (hL i)) (abs_nonneg _)
  by_cases hint : IntervalIntegrable (fun s : ℝ => Ito.itoGen (lyapObs k εH)
      (coordAt k j ⟨0, hnR⟩ w vR b s.toNNReal, b s.toNNReal) (densAt ρL ρR j ⟨0, hnR⟩ w vL vR s))
      volume 0 T
  swap
  · rw [intervalIntegral.integral_undef hint]; exact hcst0
  refine le_trans (intervalIntegral.integral_mono_ae_restrict T.coe_nonneg hint ib ?_) hib
  rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_noncollision hP] with s hs hsI
  have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.2 hsI.2
  have hsζ : (s.toNNReal : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hsT) hT
  obtain ⟨hncL, hncR⟩ := hs hsI.1 hsζ
  have hgap : ∀ i, w s.toNNReal < vR i s.toNNReal := fun i =>
    lt_of_le_of_ne (hF.w_le_vR hsζ i) (hncR i)
  have hLg : ∀ i, vL i s.toNNReal < w s.toNNReal := fun i =>
    lt_of_le_of_ne (hF.vL_le_w hsζ i) (fun h => hncL i h.symm)
  have hcur : ∀ i : Fin nR, (∀ i', i < i' → vR i s.toNNReal < vR i' s.toNNReal) →
      ∀ i', i < i' → xR i < xR i' := fun i hcur i' hii' => by
    refine lt_of_le_of_ne (hxm hii'.le) fun heq => ?_
    have := hP.vR_eq_of_xR_eq hsζ heq
    exact absurd this (hcur i' hii').ne
  have h1 := itoGen_le_at (b := b) (ρL := ρL) (vL := vL) hk hε hnR
    (fun i hi hge => hin i hi (hcur i hge)) (fun i hi hge => hout i hi (hcur i hge))
    (hF.monotone_vR hsζ) hgap (hd _ hsT)
  rw [show ((s.toNNReal : ℝ≥0) : ℝ) = s from Real.coe_toNNReal s hsI.1] at h1
  have h2 := abs_betaAt_div_le (ρL := ρL) hγ hγ' (hF.antitone_vL hsζ) hLg
    (sub_pos.2 (hgap j)) (hloc _ hsT)
  have h3 : |betaAt ρL w vL s.toNNReal| = |betaAt ρL w vL s| := by
    simp only [betaAt, Real.toNNReal_coe]
  simp only [hbnd]
  rw [h3] at h2
  calc _ ≤ C * |betaAt ρL w vL s| / (vR j s.toNNReal - w s.toNNReal) := h1
    _ = C * (|betaAt ρL w vL s| / (vR j s.toNNReal - w s.toNNReal)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 hC0

end GB5

end Supp8

end InteractingSLE

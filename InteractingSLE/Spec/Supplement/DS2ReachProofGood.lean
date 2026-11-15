/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofMeas

/-!
# DS2 in reach form, IV: the stopped state path of one good integrated path

Packet PROVE-T14-DS. One integrated path `(w, v^L, v^R)` of a DS1 word, driven by a continuous path `b`, started in
the outer closed buffer `cBuf` (coordinates `≤ R + 1`, far gaps `≥ g/2`), is stopped at its exit from `cBuf` before
the horizon `T` (`GoodPath.stopped`). Facts used for tightness and for the identification of limits:

* `GoodPath.stop`: the path is continuous before its lifetime and exits `cBuf` before it
  (`lt_lifetime_of_forall_inCBuffer`);
* `GoodPath.stopped_mem_cBuf`, `stopped_zero`, `isOrderedState_stopped`: the stopped path stays in `cBuf`, starts at
  the initial state, and is ordered;
* `GoodPath.dist_stopped_le` (**the modulus**, from (DS2.1) `DS2.integral_inv_gap_le`): for times `x ≤ y` and
  `δ > 0`, `dist(f x, f y) ≤ √κ |b y' − b x'| + C₁ (I^R_δ + I^L_δ + (y − x)/δ)`, where `x' = x ∧ τ`, `y' = y ∧ τ`
  and `I_δ` are the truncated inverse-gap integrals of the two nearest gaps up to the exit.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2

/-- The state space `ℝ × ℝ^{n_L} × ℝ^{n_R}`. -/
abbrev SState (nL nR : ℕ) := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)

section Buffers

variable {nL nR : ℕ}

/-- The outer **closed buffer** `|coordinates| ≤ R + 1`, far gaps `≥ g/2`. -/
def cBuf (mL mR : ℕ) (R g : ℝ) : Set (SState nL nR) := {p | InCBuffer mL mR (R + 1) (g / 2) p}

/-- The outer **open buffer** `|coordinates| < R + 1`, far gaps `> g/2`. -/
def oBuf (mL mR : ℕ) (R g : ℝ) : Set (SState nL nR) := {p | InBuffer mL mR (R + 1) (g / 2) p}

theorem isClosed_cBuf (mL mR : ℕ) (R g : ℝ) : IsClosed (cBuf (nL := nL) (nR := nR) mL mR R g) :=
  isClosed_setOf_inCBuffer mL mR (R + 1) (g / 2)

theorem isOpen_oBuf (mL mR : ℕ) (R g : ℝ) : IsOpen (oBuf (nL := nL) (nR := nR) mL mR R g) :=
  isOpen_setOf_inBuffer mL mR (R + 1) (g / 2)

theorem oBuf_subset_interior_cBuf (mL mR : ℕ) (R g : ℝ) :
    oBuf (nL := nL) (nR := nR) mL mR R g ⊆ interior (cBuf mL mR R g) :=
  (isOpen_oBuf mL mR R g).subset_interior_iff.2 fun _ hp => InBuffer.inCBuffer hp

/-- The inner buffer `InBuffer R g` lies in the outer open buffer. -/
theorem inBuffer_subset_oBuf {mL mR : ℕ} {R g : ℝ} (hg : 0 < g) {p : SState nL nR}
    (hp : InBuffer mL mR R g p) : p ∈ oBuf mL mR R g :=
  inBuffer_mono (by linarith) (by linarith) hp

/-- The closed buffer is compact. -/
theorem isCompact_cBuf (mL mR : ℕ) (R g : ℝ) : IsCompact (cBuf (nL := nL) (nR := nR) mL mR R g) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_cBuf mL mR R g) ?_
  refine (Metric.isBounded_closedBall (x := (0 : SState nL nR)) (r := R + 1)).subset fun p hp => ?_
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := hp
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Prod.norm_def]
  refine max_le (by rwa [Real.norm_eq_abs]) (max_le ?_ ?_)
  · have hR : 0 ≤ R + 1 := (abs_nonneg _).trans h1
    exact (pi_norm_le_iff_of_nonneg hR).2 fun i => by rw [Real.norm_eq_abs]; exact h2 i
  · have hR : 0 ≤ R + 1 := (abs_nonneg _).trans h1
    exact (pi_norm_le_iff_of_nonneg hR).2 fun j => by rw [Real.norm_eq_abs]; exact h3 j

end Buffers

/-! ### Good paths -/

section Good

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {T : ℝ≥0} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The state path `s ↦ (w s, v^L s, v^R s)`. -/
def stOf (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (s : ℝ≥0) : SState nL nR :=
  (w s, fun i => vL i s, fun j => vR j s)

/-- A **good path**: an integrated path of a DS1 word, driven by a continuous `b`, started in the outer closed
buffer. -/
structure GoodPath (κ : ℝ) (mL mR : ℕ) (Rw ε R g : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (b : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop where
  path : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ
  cont : Continuous b
  word : IsDS1Word mL mR Rw ε xL xR ρL ρR
  init : ((0 : ℝ), xL, xR) ∈ cBuf (nL := nL) (nR := nR) mL mR R g

namespace GoodPath

variable (h : GoodPath κ mL mR Rw ε R g xL xR ρL ρR w vL vR b ζ)
include h

theorem upTo : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b ζ := h.path.isSLEPathUpTo le_rfl

theorem continuousOn_stOf : ContinuousOn (stOf w vL vR) {s | (s : ℝ≥0∞) < ζ} :=
  h.upTo.continuousOn_w.prodMk ((continuousOn_pi.2 h.upTo.continuousOn_vL).prodMk
    (continuousOn_pi.2 h.upTo.continuousOn_vR))

/-- **The path exits the closed buffer before its lifetime.** -/
theorem stop (hε : 0 < ε) (hg : 0 < g) :
    ContinuousOn (stOf w vL vR) {s | (s : ℝ≥0∞) < ζ} ∧
      (exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ : ℝ≥0∞) < ζ :=
  ⟨h.continuousOn_stOf, exitTime_lt_lifetime fun hK =>
    lt_lifetime_of_forall_inCBuffer hε (half_pos hg) h.word h.path h.cont h.init hK⟩

/-- The stopped state path. -/
def stopped (_h : GoodPath κ mL mR Rw ε R g xL xR ρL ρR w vL vR b ζ) (T : ℝ≥0) :
    C(Set.Icc (0 : ℝ≥0) T, SState nL nR) :=
  stopPath (cBuf mL mR R g) T (stOf w vL vR) ζ 0

theorem stopped_apply (hε : 0 < ε) (hg : 0 < g) (t : Set.Icc (0 : ℝ≥0) T) :
    h.stopped T t = stOf w vL vR (min (t : ℝ≥0) (exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ)) :=
  stopPath_apply (h.stop hε hg) 0 t

theorem stopped_mem_cBuf (hε : 0 < ε) (hg : 0 < g) (t : Set.Icc (0 : ℝ≥0) T) :
    h.stopped T t ∈ cBuf mL mR R g := by
  rw [h.stopped_apply hε hg]
  set τ := exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ
  rcases lt_or_ge (t : ℝ≥0) τ with ht | ht
  · rw [min_eq_left ht.le]
    exact (lt_and_mem_of_lt_exitTime ht).2
  · rw [min_eq_right ht]
    refine mem_exitTime (isClosed_cBuf mL mR R g) (h.stop (T := T) hε hg).1 (h.stop hε hg).2 ?_
    have : stOf w vL vR 0 = ((0 : ℝ), xL, xR) := by
      simp only [stOf, h.upTo.w_zero, h.upTo.vL_zero, h.upTo.vR_zero]
    rw [this]
    exact h.init

theorem stopped_zero (hε : 0 < ε) (hg : 0 < g) :
    h.stopped T ⟨0, zero_le, zero_le⟩ = ((0 : ℝ), xL, xR) := by
  rw [h.stopped_apply hε hg]
  simp only [zero_le, min_eq_left, stOf, h.upTo.w_zero, h.upTo.vL_zero, h.upTo.vR_zero]

theorem isOrderedState_stopped (hε : 0 < ε) (hg : 0 < g) (t : Set.Icc (0 : ℝ≥0) T) :
    IsOrderedState (h.stopped T t) := by
  rw [h.stopped_apply hε hg]
  exact isOrderedState_of_upTo h.upTo (lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) (h.stop hε hg).2)

/-- The truncated inverse-gap integral of the nearest right gap up to the exit time. -/
def iR (_h : GoodPath κ mL mR Rw ε R g xL xR ρL ρR w vL vR b ζ) (hnR : 0 < nR) (T : ℝ≥0) (δ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ : ℝ),
    invCut δ (vR ⟨0, hnR⟩ u.toNNReal - w u.toNNReal)

/-- The truncated inverse-gap integral of the nearest left gap up to the exit time. -/
def iL (_h : GoodPath κ mL mR Rw ε R g xL xR ρL ρR w vL vR b ζ) (hnL : 0 < nL) (T : ℝ≥0) (δ : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ : ℝ),
    invCut δ (w u.toNNReal - vL ⟨0, hnL⟩ u.toNNReal)

theorem iR_nonneg (hnR : 0 < nR) (δ : ℝ) : 0 ≤ h.iR hnR T δ :=
  intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun _ _ => invCut_nonneg _ _

theorem iL_nonneg (hnL : 0 < nL) (δ : ℝ) : 0 ≤ h.iL hnL T δ :=
  intervalIntegral.integral_nonneg (NNReal.coe_nonneg _) fun _ _ => invCut_nonneg _ _

omit h in
/-- `min y τ − min x τ ≤ y − x` for `x ≤ y`. -/
theorem min_sub_min_le {x y τ : ℝ≥0} (hxy : x ≤ y) : ((min y τ : ℝ≥0) : ℝ) - (min x τ : ℝ≥0) ≤ y - x := by
  rcases le_total y τ with hy | hy
  · rw [min_eq_left hy, min_eq_left (hxy.trans hy)]
  · rw [min_eq_right hy]
    rcases le_total x τ with hx | hx
    · rw [min_eq_left hx]
      have : (τ : ℝ) ≤ y := by exact_mod_cast hy
      linarith
    · rw [min_eq_right hx, sub_self]
      have : (x : ℝ) ≤ y := by exact_mod_cast hxy
      linarith

/-- **The modulus of the stopped path** (from (DS2.1)): for times `x ≤ y` and `δ > 0`,
`dist(f x, f y) ≤ √κ |b y' − b x'| + (2 + (n_L + n_R) R_w)(I^R_δ + I^L_δ + (y − x)/δ)`. -/
theorem dist_stopped_le (hε : 0 < ε) (hg : 0 < g) (hnL : 0 < nL) (hnR : 0 < nR) {x y : Set.Icc (0 : ℝ≥0) T}
    (hxy : x ≤ y) {δ : ℝ} (hδ : 0 < δ) :
    dist (h.stopped T x) (h.stopped T y) ≤
      Real.sqrt κ * |b (min (y : ℝ≥0) (exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ)) -
        b (min (x : ℝ≥0) (exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ))| +
      (2 + (nL + nR) * Rw) * (h.iR hnR T δ + h.iL hnL T δ + ((y : ℝ) - x) / δ) := by
  set τ := exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ with hτdef
  have hstop := h.stop (T := T) hε hg
  set x' := min (x : ℝ≥0) τ
  set y' := min (y : ℝ≥0) τ
  have hxy' : x' ≤ y' := min_le_min_right _ (Subtype.coe_le_coe.2 hxy)
  have hyτ : y' ≤ τ := min_le_right _ _
  have hy'ζ : (y' : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hyτ) hstop.2
  have hx'ζ : (x' : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hxy') hy'ζ
  have hup := h.upTo
  have hRw : 0 ≤ Rw := (abs_nonneg _).trans (h.word.2.2.1 ⟨0, hnR⟩)
  have hρL := h.word.2.1
  have hρR := h.word.2.2.1
  have hlen : ((y' : ℝ) - x') ≤ (y : ℝ) - x := min_sub_min_le (Subtype.coe_le_coe.2 hxy)
  have hlen0 : 0 ≤ ((y : ℝ) - x) / δ := div_nonneg (sub_nonneg.2 (by exact_mod_cast hxy)) hδ.le
  set IR := h.iR hnR T δ
  set IL := h.iL hnL T δ
  have hIR := h.iR_nonneg (T := T) hnR δ
  have hIL := h.iL_nonneg (T := T) hnL δ
  -- right coordinates
  have hR : ∀ j, |vR j y' - vR j x'| ≤ 2 * (IR + ((y : ℝ) - x) / δ) := by
    intro j
    have hsub := hup.vR_sub hxy' hy'ζ j
    have hnn : 0 ≤ vR j y' - vR j x' := sub_nonneg.2 (hup.le_vR_of_le hxy' hy'ζ j)
    rw [abs_of_nonneg hnn, hsub]
    have e : (fun r : ℝ => 2 / (vR j r.toNNReal - w r.toNNReal)) =
        fun r => 2 * (vR j r.toNNReal - w r.toNNReal)⁻¹ := by
      funext r; rw [div_eq_mul_inv]
    rw [e, intervalIntegral.integral_const_mul]
    have hb : (∫ u in (x' : ℝ)..y', (vR j u.toNNReal - w u.toNNReal)⁻¹) ≤ IR + ((y' : ℝ) - x') / δ :=
      integral_inv_gap_le hnR h.path.isForcePath j hxy' hyτ hstop.2 hδ
    have : ((y' : ℝ) - x') / δ ≤ ((y : ℝ) - x) / δ := div_le_div_of_nonneg_right hlen hδ.le
    nlinarith
  -- left coordinates, by reflection
  have hL : ∀ i, |vL i y' - vL i x'| ≤ 2 * (IL + ((y : ℝ) - x) / δ) := by
    intro i
    have hsub := hup.vL_sub hxy' hy'ζ i
    have hnp : vL i y' - vL i x' ≤ 0 := sub_nonpos.2 (hup.vL_le_of_le hxy' hy'ζ i)
    rw [abs_of_nonpos hnp, hsub]
    have e : (fun r : ℝ => 2 / (vL i r.toNNReal - w r.toNNReal)) =
        fun r => -(2 * ((fun i => -vL i) i r.toNNReal - (-w) r.toNNReal)⁻¹) := by
      funext r
      simp only [Pi.neg_apply]
      rw [show -vL i r.toNNReal - -w r.toNNReal = -(vL i r.toNNReal - w r.toNNReal) by ring, inv_neg,
        div_eq_mul_inv]
      ring
    rw [e, intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul]
    have hb := integral_inv_gap_le hnL h.path.isForcePath.reflect i hxy' hyτ hstop.2 hδ
    have e2 : (∫ u in (0 : ℝ)..(τ : ℝ), invCut δ ((fun j => -vL j) ⟨0, hnL⟩ u.toNNReal - (-w) u.toNNReal)) = IL := by
      simp only [Pi.neg_apply, neg_sub_neg]
      rfl
    rw [e2] at hb
    have e3 : (fun u : ℝ => ((fun i => -vL i) i u.toNNReal - (-w) u.toNNReal)⁻¹) =
        fun u => (w u.toNNReal - vL i u.toNNReal)⁻¹ := by
      funext u; simp only [Pi.neg_apply, neg_sub_neg]
    rw [e3] at hb
    have e4 : (fun r : ℝ => ((fun i => -vL i) i r.toNNReal - (-w) r.toNNReal)⁻¹) =
        fun u => (w u.toNNReal - vL i u.toNNReal)⁻¹ := e3
    rw [e4]
    have : ((y' : ℝ) - x') / δ ≤ ((y : ℝ) - x) / δ := div_le_div_of_nonneg_right hlen hδ.le
    nlinarith
  -- the driver, by the linear identity
  have hW : |w y' - w x'| ≤ Real.sqrt κ * |b y' - b x'| + (nL + nR) * Rw * (IR + IL + ((y : ℝ) - x) / δ) := by
    rw [w_eq_linear hup hy'ζ, w_eq_linear hup hx'ζ]
    have e : Real.sqrt κ * b y' - (∑ i, ρL i / 2 * (vL i y' - xL i)) - (∑ j, ρR j / 2 * (vR j y' - xR j)) -
        (Real.sqrt κ * b x' - (∑ i, ρL i / 2 * (vL i x' - xL i)) - ∑ j, ρR j / 2 * (vR j x' - xR j)) =
        Real.sqrt κ * (b y' - b x') - (∑ i, ρL i / 2 * (vL i y' - vL i x')) -
          ∑ j, ρR j / 2 * (vR j y' - vR j x') := by
      have hs1 : ∑ i, ρL i / 2 * (vL i y' - vL i x') =
          (∑ i, ρL i / 2 * (vL i y' - xL i)) - ∑ i, ρL i / 2 * (vL i x' - xL i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      have hs2 : ∑ j, ρR j / 2 * (vR j y' - vR j x') =
          (∑ j, ρR j / 2 * (vR j y' - xR j)) - ∑ j, ρR j / 2 * (vR j x' - xR j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hs1, hs2]
      ring
    rw [e]
    have h1 : |∑ i, ρL i / 2 * (vL i y' - vL i x')| ≤ nL * Rw * (IL + ((y : ℝ) - x) / δ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ i ∈ (univ : Finset (Fin nL)), |ρL i / 2 * (vL i y' - vL i x')| ≤ Rw * (IL + ((y : ℝ) - x) / δ) := by
        intro i _
        rw [abs_mul, abs_div, abs_two]
        have := mul_le_mul (hρL i) (hL i) (abs_nonneg _) hRw
        nlinarith [abs_nonneg (ρL i), abs_nonneg (vL i y' - vL i x')]
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring_nf
      exact le_refl _
    have h2 : |∑ j, ρR j / 2 * (vR j y' - vR j x')| ≤ nR * Rw * (IR + ((y : ℝ) - x) / δ) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      have : ∀ j ∈ (univ : Finset (Fin nR)), |ρR j / 2 * (vR j y' - vR j x')| ≤ Rw * (IR + ((y : ℝ) - x) / δ) := by
        intro j _
        rw [abs_mul, abs_div, abs_two]
        have := mul_le_mul (hρR j) (hR j) (abs_nonneg _) hRw
        nlinarith [abs_nonneg (ρR j), abs_nonneg (vR j y' - vR j x')]
      refine (Finset.sum_le_sum this).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring_nf
      exact le_refl _
    have h3 : |Real.sqrt κ * (b y' - b x')| = Real.sqrt κ * |b y' - b x'| := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hnLR : (0 : ℝ) ≤ nL * Rw * IR := by positivity
    have hnLR' : (0 : ℝ) ≤ nR * Rw * IL := by positivity
    have t1 := abs_sub (Real.sqrt κ * (b y' - b x') - ∑ i, ρL i / 2 * (vL i y' - vL i x'))
      (∑ j, ρR j / 2 * (vR j y' - vR j x'))
    have t2 := abs_sub (Real.sqrt κ * (b y' - b x')) (∑ i, ρL i / 2 * (vL i y' - vL i x'))
    calc |Real.sqrt κ * (b y' - b x') - (∑ i, ρL i / 2 * (vL i y' - vL i x')) - ∑ j, ρR j / 2 * (vR j y' - vR j x')|
        ≤ |Real.sqrt κ * (b y' - b x')| + |∑ i, ρL i / 2 * (vL i y' - vL i x')| +
          |∑ j, ρR j / 2 * (vR j y' - vR j x')| := by linarith
      _ ≤ Real.sqrt κ * |b y' - b x'| + (nL + nR) * Rw * (IR + IL + ((y : ℝ) - x) / δ) := by
        rw [h3]; nlinarith
  -- assemble the three components
  have hS : 0 ≤ IR + IL + ((y : ℝ) - x) / δ := by linarith
  have hC : (0 : ℝ) ≤ (nL + nR) * Rw := by positivity
  have hB0 : 0 ≤ Real.sqrt κ * |b y' - b x'| := by positivity
  have hBpos : 0 ≤ Real.sqrt κ * |b y' - b x'| + (2 + (nL + nR) * Rw) * (IR + IL + ((y : ℝ) - x) / δ) := by
    positivity
  rw [h.stopped_apply hε hg x, h.stopped_apply hε hg y]
  simp only [stOf, Prod.dist_eq]
  refine max_le ?_ (max_le ((dist_pi_le_iff hBpos).2 fun i => ?_) ((dist_pi_le_iff hBpos).2 fun j => ?_))
  · rw [Real.dist_eq, abs_sub_comm]
    nlinarith
  · rw [Real.dist_eq, abs_sub_comm]
    have := hL i
    nlinarith
  · rw [Real.dist_eq, abs_sub_comm]
    have := hR j
    nlinarith

/-- The state stays in the closed buffer up to the exit time. -/
theorem stOf_mem_cBuf_of_le (hε : 0 < ε) (hg : 0 < g) {u : ℝ≥0}
    (hu : u ≤ exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ) : stOf w vL vR u ∈ cBuf mL mR R g := by
  have := h.stopped_mem_cBuf (T := T) hε hg ⟨u, zero_le, hu.trans exitTime_le⟩
  rwa [h.stopped_apply hε hg, min_eq_left hu] at this

end GoodPath

end Good

end DSReach

end Supp12

end InteractingSLE

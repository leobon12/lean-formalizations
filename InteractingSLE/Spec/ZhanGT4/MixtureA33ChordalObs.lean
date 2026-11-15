/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeObs

/-!
# The strip martingale with marks on the upper strip boundary: the observable

Packet PROVE-ZHAN-A33 (Astra, *Follow-up proofs* §A.3.2, `source/external/AstraIG1/ig1_followup_proofs.txt`
L686–L705: "Mapping back gives the original killed chordal law as a mixture of `SLE_κ(−4, κ − 4)` from `(0; y, x)`";
ruling R36). PROVE-ZHAN-A2's strip observable (`Zhan.stripMartObs`) is written for an R36 word whose end mark `v`
(the image `−1` of the strip end `−∞`) is the **outermost** left mark, so every other mark is a point of the lower
strip boundary. A point `u + iπ` of the **upper** strip boundary is the chordal point `−1 − e^u`, beyond the end mark.
Here the end mark is the **innermost** left mark (index `0`), the other left marks (indices `i.succ`) lie beyond it
(upper strip marks), and the right marks are lower strip marks. The observable is the same,

  `Φ = log(W − v) + Σᵢ (ρᵢ/2) log|Vᵢ − v| + (κ/2 − 2 − τ₋) t(s)`,

now with `Vᵢ < v` for the upper marks (`Real.log` is `log |·|`), and its generators vanish along the evolution by the
same per-mark cancellation (`Zhan.mark_term_eq_zero` needs only `Vᵢ ≠ v`).

## Main results

* `upObs`, `upObs2 = Φ² − κ t`, `upGap`, `upRegion` (`W − v > 0`, `v − Vᵢ > 0` for upper marks, `Vⱼ − v > 0` for
  right marks), `upDens` (the strip density with the end mark at index `0`);
* `contDiffOn_upObs`, `contDiffOn_upObs2`, `isOpen_upRegion`;
* `itoGen_upObs_upDens`, `itoGen_upObs2_upDens`: both generators vanish along the density off collisions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.UpMark

open Zhan

variable {nL nR : ℕ}

/-- The argument of the driver logarithm with the end mark at index `0`: `√κ x + ℓ(q) − q₀` (`= W − v`). -/
def upGap (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (p : SCoord nL nR × ℝ) : ℝ :=
  Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1 - p.1.1 0

/-- **The strip observable with the end mark at index `0`.** -/
def upObs (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (p : SCoord nL nR × ℝ) : ℝ :=
  Real.log (upGap κ xL xR ρL ρR p)
    + ∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 0)
    + ∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 0)
    + (κ / 2 - 2 - ρL 0) * p.1.2.2

/-- The open region: `W − v > 0`, the upper marks strictly below the end mark, the right marks strictly above. -/
def upRegion (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ) :
    Set (SCoord nL nR × ℝ) :=
  {p | 0 < upGap κ xL xR ρL ρR p ∧ (∀ i : Fin nL, 0 < p.1.1 0 - p.1.1 i.succ) ∧
    ∀ j, 0 < p.1.2.1 j - p.1.1 0}

/-- The density of the strip coordinates along a chordal path, with the end mark at index `0`. -/
def upDens (w : ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin nR → ℝ) : SCoord nL nR :=
  (fun i => 2 / (vL i - w), fun j => 2 / (vR j - w), ((w - vL 0) ^ 2)⁻¹)

/-- `Φ² − κ T`. -/
def upObs2 (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (p : SCoord nL nR × ℝ) : ℝ :=
  upObs κ xL xR ρL ρR p * upObs κ xL xR ρL ρR p + -κ * p.1.2.2

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)

theorem upMark_ne {p : SCoord nL nR × ℝ} (hp : p ∈ upRegion κ xL xR ρL ρR) (i : Fin nL) :
    p.1.1 i.succ - p.1.1 0 ≠ 0 := by
  have := hp.2.1 i; intro h; linarith

theorem upObs_line (p : SCoord nL nR × ℝ) (v : SCoord nL nR) (t : ℝ) :
    upObs κ xL xR ρL ρR (p.1 + t • v, p.2) =
      Real.log ((Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1 - p.1.1 0)
          + t * (driftLin₀ ρL ρR v - v.1 0))
        + ∑ i, ρL i / 2 * Real.log ((p.1.1 i - p.1.1 0) + t * (v.1 i - v.1 0))
        + ∑ j, ρR j / 2 * Real.log ((p.1.2.1 j - p.1.1 0) + t * (v.2.1 j - v.1 0))
        + (κ / 2 - 2 - ρL 0) * (p.1.2.2 + t * v.2.2) := by
  have hL : ∑ i, ρL i * ((p.1.1 i + t * v.1 i) - xL i) =
      ∑ i, ρL i * (p.1.1 i - xL i) + t * ∑ i, ρL i * v.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ j, ρR j * ((p.1.2.1 j + t * v.2.1 j) - xR j) =
      ∑ j, ρR j * (p.1.2.1 j - xR j) + t * ∑ j, ρR j * v.2.1 j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hLi : ∀ i, (p.1.1 i + t * v.1 i) - (p.1.1 0 + t * v.1 0) =
      (p.1.1 i - p.1.1 0) + t * (v.1 i - v.1 0) := fun i => by ring
  have hRj : ∀ j, (p.1.2.1 j + t * v.2.1 j) - (p.1.1 0 + t * v.1 0) =
      (p.1.2.1 j - p.1.1 0) + t * (v.2.1 j - v.1 0) := fun j => by ring
  simp only [upObs, upGap, driftLin, driftLin₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hL, hR, hLi, hRj]
  congr 4
  ring

theorem contDiff_upGap {n : WithTop ℕ∞} : ContDiff ℝ n (upGap κ xL xR ρL ρR) := by
  unfold upGap driftLin
  fun_prop

theorem isOpen_upRegion : IsOpen (upRegion κ xL xR ρL ρR) := by
  have h1 : IsOpen {p : SCoord nL nR × ℝ | 0 < upGap κ xL xR ρL ρR p} :=
    isOpen_lt continuous_const (contDiff_upGap κ xL xR ρL ρR (n := 0)).continuous
  have h2 : IsOpen {p : SCoord nL nR × ℝ | ∀ i : Fin nL, 0 < p.1.1 0 - p.1.1 i.succ} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  have h3 : IsOpen {p : SCoord nL nR × ℝ | ∀ j, 0 < p.1.2.1 j - p.1.1 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (by fun_prop)
  exact h1.inter (h2.inter h3)

theorem contDiffOn_upObs {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (upObs κ xL xR ρL ρR) (upRegion κ xL xR ρL ρR) := by
  have e : upObs κ xL xR ρL ρR = fun p => Real.log (upGap κ xL xR ρL ρR p)
      + ∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 0)
      + ∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 0)
      + (κ / 2 - 2 - ρL 0) * p.1.2.2 := rfl
  rw [e]
  refine (((ContDiffOn.log (contDiff_upGap κ xL xR ρL ρR).contDiffOn fun p hp => hp.1.ne').add
    (ContDiffOn.sum fun i _ => ?_)).add (ContDiffOn.sum fun j _ => ?_)).add (by fun_prop)
  · induction i using Fin.cases with
    | zero =>
      have : (fun p : SCoord nL nR × ℝ => ρL 0 / 2 * Real.log (p.1.1 0 - p.1.1 0)) = fun _ => 0 := by
        funext p; simp
      rw [this]; exact contDiffOn_const
    | succ i =>
      exact contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun p hp => upMark_ne κ xL xR ρL ρR hp i)
  · exact contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun p hp => (hp.2.2 j).ne')

theorem contDiffAt_upObs {n : WithTop ℕ∞} {p : SCoord nL nR × ℝ} (hp : p ∈ upRegion κ xL xR ρL ρR) :
    ContDiffAt ℝ n (upObs κ xL xR ρL ρR) p :=
  (contDiffOn_upObs κ xL xR ρL ρR).contDiffAt ((isOpen_upRegion κ xL xR ρL ρR).mem_nhds hp)

/-- `∂_Λ` of the observable. -/
theorem partialFst_upObs {p : SCoord nL nR × ℝ} (hp : p ∈ upRegion κ xL xR ρL ρR) (v : SCoord nL nR) :
    Ito.partialFst (upObs κ xL xR ρL ρR) p v =
      (driftLin₀ ρL ρR v - v.1 0) / upGap κ xL xR ρL ρR p
      + ∑ i, ρL i / 2 * ((v.1 i - v.1 0) / (p.1.1 i - p.1.1 0))
      + ∑ j, ρR j / 2 * ((v.2.1 j - v.1 0) / (p.1.2.1 j - p.1.1 0))
      + (κ / 2 - 2 - ρL 0) * v.2.2 := by
  have hd : DifferentiableAt ℝ (upObs κ xL xR ρL ρR) p :=
    (contDiffAt_upObs κ xL xR ρL ρR (n := 1) hp).differentiableAt (by norm_num)
  refine Ito.partialFst_eq_of_hasDerivAt hd ?_
  rw [show (fun t : ℝ => upObs κ xL xR ρL ρR (p.1 + t • v, p.2)) = _ from funext (upObs_line κ xL xR ρL ρR p v)]
  refine (((hasDerivAt_log_add_mul_line (Or.inl hp.1.ne')).add (HasDerivAt.fun_sum fun i _ => ?_)).add
    (HasDerivAt.fun_sum fun j _ => ?_)).add ?_
  · refine (hasDerivAt_log_add_mul_line ?_).const_mul _
    induction i using Fin.cases with
    | zero => right; simp
    | succ i => left; exact upMark_ne κ xL xR ρL ρR hp i
  · exact (hasDerivAt_log_add_mul_line (Or.inl (hp.2.2 j).ne')).const_mul _
  · have := (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add p.1.2.2).const_mul (κ / 2 - 2 - ρL 0)
    simpa using this

theorem hasDerivAt_upObs_snd {p : SCoord nL nR × ℝ} (hp : 0 < upGap κ xL xR ρL ρR p) :
    HasDerivAt (fun y : ℝ => upObs κ xL xR ρL ρR (p.1, y)) (Real.sqrt κ / upGap κ xL xR ρL ρR p) p.2 := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sqrt κ * y + driftLin xL xR ρL ρR p.1 - p.1.1 0)
      (Real.sqrt κ * 1) p.2 :=
    (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const _).sub_const _
  have h2 := (((h1.log hp.ne').add_const (∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 0)))
    |>.add_const (∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 0))).add_const
    ((κ / 2 - 2 - ρL 0) * p.1.2.2)
  exact h2.congr_deriv (by rw [mul_one]; rfl)

theorem partialSnd_upObs {p : SCoord nL nR × ℝ} (hp : p ∈ upRegion κ xL xR ρL ρR) :
    Ito.partialSnd (upObs κ xL xR ρL ρR) p = Real.sqrt κ / upGap κ xL xR ρL ρR p :=
  Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_upObs κ xL xR ρL ρR (n := 1) hp).differentiableAt
    (by norm_num)) (hasDerivAt_upObs_snd κ xL xR ρL ρR hp.1)

theorem partialSndSnd_upObs (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ} (hp : p ∈ upRegion κ xL xR ρL ρR) :
    Ito.partialSndSnd (upObs κ xL xR ρL ρR) p = -(κ / upGap κ xL xR ρL ρR p ^ 2) := by
  set c := driftLin xL xR ρL ρR p.1 - p.1.1 0 with hc
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : SCoord nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : SCoord nL nR × ℝ) ∈ upRegion κ xL xR ρL ρR :=
    hline.eventually ((isOpen_upRegion κ xL xR ρL ρR).mem_nhds (by simpa using hp))
  refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_upObs κ xL xR ρL ρR hp)
    (g := fun y => Real.sqrt κ * (Real.sqrt κ * y + c)⁻¹) (hev.mono fun y hy => ?_) ?_
  · rw [partialSnd_upObs κ xL xR ρL ρR hy, div_eq_mul_inv]
    congr 2
    simp only [upGap, hc]
    ring
  · have hg : upGap κ xL xR ρL ρR p = Real.sqrt κ * p.2 + c := by
      simp only [upGap, hc]; ring
    have h1 : HasDerivAt (fun y : ℝ => Real.sqrt κ * y + c) (Real.sqrt κ * 1) p.2 :=
      ((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const c
    have h2 := (h1.inv (by rw [← hg]; exact hp.1.ne')).const_mul (Real.sqrt κ)
    refine h2.congr_deriv ?_
    rw [hg]
    have hs : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
    calc _ = -(Real.sqrt κ * Real.sqrt κ) / (Real.sqrt κ * p.2 + c) ^ 2 := by ring
      _ = _ := by rw [hs, neg_div]

/-- The Itô generator of the observable. -/
theorem itoGen_upObs (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ} (hp : p ∈ upRegion κ xL xR ρL ρR)
    (v : SCoord nL nR) :
    Ito.itoGen (upObs κ xL xR ρL ρR) p v =
      (driftLin₀ ρL ρR v - v.1 0) / upGap κ xL xR ρL ρR p
      + ∑ i, ρL i / 2 * ((v.1 i - v.1 0) / (p.1.1 i - p.1.1 0))
      + ∑ j, ρR j / 2 * ((v.2.1 j - v.1 0) / (p.1.2.1 j - p.1.1 0))
      + (κ / 2 - 2 - ρL 0) * v.2.2
      - κ / (2 * upGap κ xL xR ρL ρR p ^ 2) := by
  rw [Ito.itoGen, partialFst_upObs κ xL xR ρL ρR hp, partialSndSnd_upObs κ xL xR ρL ρR hκ hp]
  ring

/-- **The observable has no drift along the evolution** (off collisions of the other marks with the driver). -/
theorem itoGen_upObs_upDens (hκ : 0 ≤ κ) {vL : Fin (nL + 1) → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + driftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ upRegion κ xL xR ρL ρR) (hL : ∀ i : Fin nL, vL i.succ ≠ w)
    (hR : ∀ j, vR j ≠ w) :
    Ito.itoGen (upObs κ xL xR ρL ρR) ((vL, vR, T), b) (upDens w vL vR) = 0 := by
  rw [itoGen_upObs κ xL xR ρL ρR hκ hp]
  have hg : upGap κ xL xR ρL ρR ((vL, vR, T), b) = w - vL 0 := by
    simp only [upGap, hw]
  have hG : w - vL 0 ≠ 0 := by rw [← hg]; exact hp.1.ne'
  rw [hg]
  simp only [upDens, driftLin₀]
  set G := w - vL 0 with hGdef
  set lv := 2 / (vL 0 - w) with hlv
  have hsplit : (-(1 / 2) * (∑ i, ρL i * (2 / (vL i - w))) - (1 / 2) * (∑ j, ρR j * (2 / (vR j - w)))
      - lv) / G
      + ∑ i, ρL i / 2 * ((2 / (vL i - w) - lv) / (vL i - vL 0))
      + ∑ j, ρR j / 2 * ((2 / (vR j - w) - lv) / (vR j - vL 0)) =
      (∑ i, (-(1 / 2) * (ρL i * (2 / (vL i - w))) / G
          + ρL i / 2 * ((2 / (vL i - w) - lv) / (vL i - vL 0))))
      + (∑ j, (-(1 / 2) * (ρR j * (2 / (vR j - w))) / G
          + ρR j / 2 * ((2 / (vR j - w) - lv) / (vR j - vL 0))))
      - lv / G := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hRz : ∑ j, (-(1 / 2) * (ρR j * (2 / (vR j - w))) / G
      + ρR j / 2 * ((2 / (vR j - w) - lv) / (vR j - vL 0))) = 0 :=
    Finset.sum_eq_zero fun j _ => mark_term_eq_zero (hR j) (hp.2.2 j).ne' hG
  have hLz : ∑ i, (-(1 / 2) * (ρL i * (2 / (vL i - w))) / G
      + ρL i / 2 * ((2 / (vL i - w) - lv) / (vL i - vL 0))) =
      -(1 / 2) * (ρL 0 * lv) / G := by
    rw [Fin.sum_univ_succ, Finset.sum_eq_zero fun i _ =>
      mark_term_eq_zero (hL i) (upMark_ne κ xL xR ρL ρR hp i) hG]
    simp [hlv]
  rw [hsplit, hRz, hLz]
  have hv : vL 0 - w = -G := by rw [hGdef]; ring
  rw [hlv, hv]
  field_simp
  ring

theorem contDiffOn_upObs2 {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (upObs2 κ xL xR ρL ρR) (upRegion κ xL xR ρL ρR) :=
  ((contDiffOn_upObs κ xL xR ρL ρR).mul (contDiffOn_upObs κ xL xR ρL ρR)).add (by fun_prop)

/-- **`Φ² − κ T` has no drift along the evolution** (off collisions). -/
theorem itoGen_upObs2_upDens (hκ : 0 ≤ κ) {vL : Fin (nL + 1) → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + driftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ upRegion κ xL xR ρL ρR) (hL : ∀ i : Fin nL, vL i.succ ≠ w)
    (hR : ∀ j, vR j ≠ w) :
    Ito.itoGen (upObs2 κ xL xR ρL ρR) ((vL, vR, T), b) (upDens w vL vR) = 0 := by
  have hΦ := contDiffAt_upObs κ xL xR ρL ρR (n := 2) hp
  have hc : ContDiffAt ℝ 2 (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) ((vL, vR, T), b) := by
    fun_prop
  have e : upObs2 κ xL xR ρL ρR = fun q => (fun q => upObs κ xL xR ρL ρR q *
      upObs κ xL xR ρL ρR q) q + (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) q := rfl
  rw [e, Ito.itoGen_add (hΦ.mul hΦ) hc, Ito.itoGen_mul hΦ hΦ,
    itoGen_upObs_upDens κ xL xR ρL ρR hκ hw hp hL hR, itoGen_clockObs,
    partialSnd_upObs κ xL xR ρL ρR hp]
  have hg : upGap κ xL xR ρL ρR ((vL, vR, T), b) = w - vL 0 := by
    simp only [upGap, hw]
  have hG : w - vL 0 ≠ 0 := by rw [← hg]; exact hp.1.ne'
  rw [hg]
  simp only [upDens]
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
  field_simp
  rw [hs]
  ring

end InteractingSLE.ZhanGT4.UpMark

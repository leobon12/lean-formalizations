/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Observable
import InteractingSLE.Spec.Ito.Bracket
import InteractingSLE.Spec.Ito.TwoPointGen
import InteractingSLE.Spec.Zhan.StripTimeGap

/-!
# The strip martingale: the observable and its Itô generator

Packet PROVE-ZHAN-A2 (Astra, *Formalization proofs and dependency audit* §3, "Complete proof of target change",
`source/external/AstraIG1/ig1_formalization_proofs.txt` L1028–L1090; ruling R36). In the R36 form a strip evolution
is a chordal evolution whose outermost left mark `v = V^{L, last}` (started at `−1`) is the end `−∞` of the strip;
the strip driver is `ξ_t = t + log(W − v)` at chordal time `s(t)`, with the strip clock `t(s) = ∫₀ˢ (W − v)⁻²`, and a
lower mark `V` has strip coordinate `p = t + log|V − v|`. The target change says that the martingale part of `ξ` is
`√κ` times a Brownian motion in the strip clock. In chordal time this is the statement that

  `Φ = log(W − v) + Σᵢ (ρᵢ/2) log|Vᵢ − v| + (κ/2 − 2 − τ₋) t(s)`

(the sum over all marks other than `v`; `τ₋` the weight of `v`) is a continuous local martingale with
`d⟨Φ⟩ = κ dt(s)`, i.e. `Φ` and `Φ² − κ t(s)` have no drift. In strip time,
`Φ = ξ_t + Σᵢ (ρᵢ/2)(pᵢ(t) − pᵢ(0)) − ((τ₋ − τ₊)/2) t + const` (the coth drift integrated along the marks' own
equations), which is the integrated strip equation of the driver.

The Itô generator is computed without stochastic integrals, in the coordinates of the localized Itô formula
(`Ito.martingale_itoLocalized`): `Λ = (V^L, V^R, t(s))` (absolutely continuous, density `stripDens`), with the driver
recovered from `W = √κ B + ℓ(V)`, `ℓ(V) = −½ Σ ρ (V − x)` (the identity (N1), `IsForcePath.w_eq_N1`).

## Main results

* `stripMartObs`, `stripMartObs2 = Φ² − κ t`: the observables on `SCoord nL nR × ℝ`;
* `contDiffOn_stripMartObs`, `contDiffOn_stripMartObs2`, `isOpen_stripMartRegion`: smoothness on the open region
  `W − v > 0`, `Vᵢ − v > 0`;
* `itoGen_stripMartObs`: the generator `(ℓ'(λ) − λ_v)/G + Σ (ρᵢ/2)(λᵢ − λ_v)/(Vᵢ − v) + c λ_t − κ/(2G²)`;
* `itoGen_stripMartObs_stripDens`, `itoGen_stripMartObs2_stripDens`: both generators vanish along the strip density off
  collisions of the lower marks with the driver (the per-mark cancellation `mark_term_eq_zero` and the charge
  `c = κ/2 − 2 − τ₋`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

variable {nL nR : ℕ}

/-- Coordinates of the strip martingale. -/
abbrev SCoord (nL nR : ℕ) : Type := (Fin (nL + 1) → ℝ) × (Fin nR → ℝ) × ℝ

/-- `ℓ(q) = −½ Σ ρ (q − x)`. -/
def driftLin (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (q : SCoord nL nR) : ℝ :=
  -(1 / 2) * ∑ i, ρL i * (q.1 i - xL i) - (1 / 2) * ∑ j, ρR j * (q.2.1 j - xR j)

/-- Linear part. -/
def driftLin₀ (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ) (v : SCoord nL nR) : ℝ :=
  -(1 / 2) * ∑ i, ρL i * v.1 i - (1 / 2) * ∑ j, ρR j * v.2.1 j

/-- The strip observable. -/
def stripMartObs (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (p : SCoord nL nR × ℝ) : ℝ :=
  Real.log (Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1 - p.1.1 (Fin.last nL))
    + ∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 (Fin.last nL))
    + ∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 (Fin.last nL))
    + (κ / 2 - 2 - ρL (Fin.last nL)) * p.1.2.2

theorem hasDerivAt_log_add_mul_line {c d : ℝ} (h : c ≠ 0 ∨ (c = 0 ∧ d = 0)) :
    HasDerivAt (fun t : ℝ => Real.log (c + t * d)) (d / c) 0 := by
  rcases h with hc | ⟨rfl, rfl⟩
  · have h1 : HasDerivAt (fun t : ℝ => c + t * d) (1 * d) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
    have h2 := h1.log (by simpa using hc)
    simpa using h2
  · simpa using hasDerivAt_const (0 : ℝ) (Real.log 0)

theorem stripMartObs_line (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (p : SCoord nL nR × ℝ) (v : SCoord nL nR) (t : ℝ) :
    stripMartObs κ xL xR ρL ρR (p.1 + t • v, p.2) =
      Real.log ((Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1 - p.1.1 (Fin.last nL))
          + t * (driftLin₀ ρL ρR v - v.1 (Fin.last nL)))
        + ∑ i, ρL i / 2 * Real.log ((p.1.1 i - p.1.1 (Fin.last nL)) + t * (v.1 i - v.1 (Fin.last nL)))
        + ∑ j, ρR j / 2 * Real.log ((p.1.2.1 j - p.1.1 (Fin.last nL))
            + t * (v.2.1 j - v.1 (Fin.last nL)))
        + (κ / 2 - 2 - ρL (Fin.last nL)) * (p.1.2.2 + t * v.2.2) := by
  have hL : ∑ i, ρL i * ((p.1.1 i + t * v.1 i) - xL i) =
      ∑ i, ρL i * (p.1.1 i - xL i) + t * ∑ i, ρL i * v.1 i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hR : ∑ j, ρR j * ((p.1.2.1 j + t * v.2.1 j) - xR j) =
      ∑ j, ρR j * (p.1.2.1 j - xR j) + t * ∑ j, ρR j * v.2.1 j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hLi : ∀ i, (p.1.1 i + t * v.1 i) - (p.1.1 (Fin.last nL) + t * v.1 (Fin.last nL)) =
      (p.1.1 i - p.1.1 (Fin.last nL)) + t * (v.1 i - v.1 (Fin.last nL)) := fun i => by ring
  have hRj : ∀ j, (p.1.2.1 j + t * v.2.1 j) - (p.1.1 (Fin.last nL) + t * v.1 (Fin.last nL)) =
      (p.1.2.1 j - p.1.1 (Fin.last nL)) + t * (v.2.1 j - v.1 (Fin.last nL)) := fun j => by ring
  simp only [stripMartObs, driftLin, driftLin₀, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hL, hR, hLi, hRj]
  congr 4
  ring


/-- The argument of the driver logarithm: `g = √κ x + ℓ(q) − q_last` (`= W − v` along a path). -/
def gapArg (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)
    (p : SCoord nL nR × ℝ) : ℝ :=
  Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1 - p.1.1 (Fin.last nL)

/-- The open region where the strip observable is smooth. -/
def stripMartRegion (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) : Set (SCoord nL nR × ℝ) :=
  {p | 0 < gapArg κ xL xR ρL ρR p ∧ (∀ i : Fin nL, 0 < p.1.1 i.castSucc - p.1.1 (Fin.last nL)) ∧
    ∀ j, 0 < p.1.2.1 j - p.1.1 (Fin.last nL)}

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin nR → ℝ)

theorem contDiff_gapArg {n : WithTop ℕ∞} : ContDiff ℝ n (gapArg κ xL xR ρL ρR) := by
  unfold gapArg driftLin
  fun_prop

theorem isOpen_stripMartRegion : IsOpen (stripMartRegion κ xL xR ρL ρR) := by
  have h1 : IsOpen {p : SCoord nL nR × ℝ | 0 < gapArg κ xL xR ρL ρR p} :=
    isOpen_lt continuous_const (contDiff_gapArg κ xL xR ρL ρR (n := 0)).continuous
  have h2 : IsOpen {p : SCoord nL nR × ℝ | ∀ i : Fin nL, 0 < p.1.1 i.castSucc - p.1.1 (Fin.last nL)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)
  have h3 : IsOpen {p : SCoord nL nR × ℝ | ∀ j, 0 < p.1.2.1 j - p.1.1 (Fin.last nL)} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt continuous_const (by fun_prop)
  exact h1.inter (h2.inter h3)

theorem stripMartObs_eq (p : SCoord nL nR × ℝ) : stripMartObs κ xL xR ρL ρR p =
    Real.log (gapArg κ xL xR ρL ρR p)
    + ∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 (Fin.last nL))
    + ∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 (Fin.last nL))
    + (κ / 2 - 2 - ρL (Fin.last nL)) * p.1.2.2 := rfl

theorem contDiffOn_stripMartObs {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (stripMartObs κ xL xR ρL ρR) (stripMartRegion κ xL xR ρL ρR) := by
  have e : stripMartObs κ xL xR ρL ρR = fun p => Real.log (gapArg κ xL xR ρL ρR p)
      + ∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 (Fin.last nL))
      + ∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 (Fin.last nL))
      + (κ / 2 - 2 - ρL (Fin.last nL)) * p.1.2.2 := rfl
  rw [e]
  refine (((ContDiffOn.log (contDiff_gapArg κ xL xR ρL ρR).contDiffOn fun p hp => hp.1.ne').add
    (ContDiffOn.sum fun i _ => ?_)).add (ContDiffOn.sum fun j _ => ?_)).add (by fun_prop)
  · induction i using Fin.lastCases with
    | last =>
      have : (fun p : SCoord nL nR × ℝ => ρL (Fin.last nL) / 2 *
          Real.log (p.1.1 (Fin.last nL) - p.1.1 (Fin.last nL))) = fun _ => 0 := by
        funext p; simp
      rw [this]; exact contDiffOn_const
    | cast i =>
      refine contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun p hp => (hp.2.1 i).ne')
  · exact contDiffOn_const.mul (ContDiffOn.log (by fun_prop) fun p hp => (hp.2.2 j).ne')


theorem contDiffAt_stripMartObs {n : WithTop ℕ∞} {p : SCoord nL nR × ℝ}
    (hp : p ∈ stripMartRegion κ xL xR ρL ρR) : ContDiffAt ℝ n (stripMartObs κ xL xR ρL ρR) p :=
  (contDiffOn_stripMartObs κ xL xR ρL ρR).contDiffAt ((isOpen_stripMartRegion κ xL xR ρL ρR).mem_nhds hp)

/-- `∂_Λ` of the strip observable. -/
theorem partialFst_stripMartObs {p : SCoord nL nR × ℝ} (hp : p ∈ stripMartRegion κ xL xR ρL ρR)
    (v : SCoord nL nR) :
    Ito.partialFst (stripMartObs κ xL xR ρL ρR) p v =
      (driftLin₀ ρL ρR v - v.1 (Fin.last nL)) / gapArg κ xL xR ρL ρR p
      + ∑ i, ρL i / 2 * ((v.1 i - v.1 (Fin.last nL)) / (p.1.1 i - p.1.1 (Fin.last nL)))
      + ∑ j, ρR j / 2 * ((v.2.1 j - v.1 (Fin.last nL)) / (p.1.2.1 j - p.1.1 (Fin.last nL)))
      + (κ / 2 - 2 - ρL (Fin.last nL)) * v.2.2 := by
  have hd : DifferentiableAt ℝ (stripMartObs κ xL xR ρL ρR) p :=
    (contDiffAt_stripMartObs κ xL xR ρL ρR (n := 1) hp).differentiableAt (by norm_num)
  refine Ito.partialFst_eq_of_hasDerivAt hd ?_
  rw [show (fun t : ℝ => stripMartObs κ xL xR ρL ρR (p.1 + t • v, p.2)) = _ from
    funext (stripMartObs_line κ xL xR ρL ρR p v)]
  refine (((hasDerivAt_log_add_mul_line (Or.inl hp.1.ne')).add (HasDerivAt.fun_sum fun i _ => ?_)).add
    (HasDerivAt.fun_sum fun j _ => ?_)).add ?_
  · refine (hasDerivAt_log_add_mul_line ?_).const_mul _
    induction i using Fin.lastCases with
    | last => right; simp
    | cast i => left; exact (hp.2.1 i).ne'
  · exact (hasDerivAt_log_add_mul_line (Or.inl (hp.2.2 j).ne')).const_mul _
  · have := (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add p.1.2.2).const_mul
      (κ / 2 - 2 - ρL (Fin.last nL))
    simpa using this

/-- The Brownian-slot derivative of the strip observable. -/
theorem hasDerivAt_stripMartObs_snd {p : SCoord nL nR × ℝ} (hp : 0 < gapArg κ xL xR ρL ρR p) :
    HasDerivAt (fun y : ℝ => stripMartObs κ xL xR ρL ρR (p.1, y))
      (Real.sqrt κ / gapArg κ xL xR ρL ρR p) p.2 := by
  have h1 : HasDerivAt (fun y : ℝ => Real.sqrt κ * y + driftLin xL xR ρL ρR p.1 - p.1.1 (Fin.last nL))
      (Real.sqrt κ * 1) p.2 :=
    (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const _).sub_const _
  have h2 := (((h1.log hp.ne').add_const (∑ i, ρL i / 2 * Real.log (p.1.1 i - p.1.1 (Fin.last nL))))
    |>.add_const (∑ j, ρR j / 2 * Real.log (p.1.2.1 j - p.1.1 (Fin.last nL)))).add_const
    ((κ / 2 - 2 - ρL (Fin.last nL)) * p.1.2.2)
  exact h2.congr_deriv (by rw [mul_one]; rfl)

theorem partialSnd_stripMartObs {p : SCoord nL nR × ℝ} (hp : p ∈ stripMartRegion κ xL xR ρL ρR) :
    Ito.partialSnd (stripMartObs κ xL xR ρL ρR) p = Real.sqrt κ / gapArg κ xL xR ρL ρR p :=
  Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_stripMartObs κ xL xR ρL ρR (n := 1) hp).differentiableAt
    (by norm_num)) (hasDerivAt_stripMartObs_snd κ xL xR ρL ρR hp.1)

theorem partialSndSnd_stripMartObs (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ}
    (hp : p ∈ stripMartRegion κ xL xR ρL ρR) :
    Ito.partialSndSnd (stripMartObs κ xL xR ρL ρR) p = -(κ / gapArg κ xL xR ρL ρR p ^ 2) := by
  set c := driftLin xL xR ρL ρR p.1 - p.1.1 (Fin.last nL) with hc
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : SCoord nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : SCoord nL nR × ℝ) ∈ stripMartRegion κ xL xR ρL ρR :=
    hline.eventually ((isOpen_stripMartRegion κ xL xR ρL ρR).mem_nhds (by simpa using hp))
  refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_stripMartObs κ xL xR ρL ρR hp)
    (g := fun y => Real.sqrt κ * (Real.sqrt κ * y + c)⁻¹) (hev.mono fun y hy => ?_) ?_
  · rw [partialSnd_stripMartObs κ xL xR ρL ρR hy, div_eq_mul_inv]
    congr 2
    simp only [gapArg, hc]
    ring
  · have hg : gapArg κ xL xR ρL ρR p = Real.sqrt κ * p.2 + c := by
      simp only [gapArg, hc]; ring
    have h1 : HasDerivAt (fun y : ℝ => Real.sqrt κ * y + c) (Real.sqrt κ * 1) p.2 :=
      ((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const c
    have h2 := (h1.inv (by rw [← hg]; exact hp.1.ne')).const_mul (Real.sqrt κ)
    refine h2.congr_deriv ?_
    rw [hg]
    have hs : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
    calc _ = -(Real.sqrt κ * Real.sqrt κ) / (Real.sqrt κ * p.2 + c) ^ 2 := by ring
      _ = _ := by rw [hs, neg_div]

/-- **The Itô generator of the strip observable.** -/
theorem itoGen_stripMartObs (hκ : 0 ≤ κ) {p : SCoord nL nR × ℝ} (hp : p ∈ stripMartRegion κ xL xR ρL ρR)
    (v : SCoord nL nR) :
    Ito.itoGen (stripMartObs κ xL xR ρL ρR) p v =
      (driftLin₀ ρL ρR v - v.1 (Fin.last nL)) / gapArg κ xL xR ρL ρR p
      + ∑ i, ρL i / 2 * ((v.1 i - v.1 (Fin.last nL)) / (p.1.1 i - p.1.1 (Fin.last nL)))
      + ∑ j, ρR j / 2 * ((v.2.1 j - v.1 (Fin.last nL)) / (p.1.2.1 j - p.1.1 (Fin.last nL)))
      + (κ / 2 - 2 - ρL (Fin.last nL)) * v.2.2
      - κ / (2 * gapArg κ xL xR ρL ρR p ^ 2) := by
  rw [Ito.itoGen, partialFst_stripMartObs κ xL xR ρL ρR hp, partialSndSnd_stripMartObs κ xL xR ρL ρR hκ hp]
  ring


/-- The density of the strip coordinates along a chordal path: the force-point velocities `2/(V − W)` and the strip
clock rate `(W − v)⁻²`. -/
def stripDens (w : ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin nR → ℝ) : SCoord nL nR :=
  (fun i => 2 / (vL i - w), fun j => 2 / (vR j - w), ((w - vL (Fin.last nL)) ^ 2)⁻¹)

omit κ xL xR ρL ρR in
/-- One mark's contribution cancels: `−½ρ (2/(a − w))/G + (ρ/2)(2/(a − w) − 2/(v − w))/(a − v) = 0`, `G = w − v`. -/
theorem mark_term_eq_zero {ρ a v w : ℝ} (haw : a ≠ w) (hav : a - v ≠ 0) (hvw : w - v ≠ 0) :
    -(1 / 2) * (ρ * (2 / (a - w))) / (w - v) + ρ / 2 * ((2 / (a - w) - 2 / (v - w)) / (a - v)) = 0 := by
  have h1 : a - w ≠ 0 := sub_ne_zero.2 haw
  have h2 : v - w ≠ 0 := by intro h; apply hvw; linarith
  field_simp
  ring

/-- **The strip observable has no drift along the strip evolution** (off collisions of the lower marks with the
driver): with `W = √κ b + ℓ(V)` (the identity (N1)) and the strip density, the Itô generator vanishes. -/
theorem itoGen_stripMartObs_stripDens (hκ : 0 ≤ κ) {vL : Fin (nL + 1) → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + driftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ stripMartRegion κ xL xR ρL ρR) (hL : ∀ i : Fin nL, vL i.castSucc ≠ w)
    (hR : ∀ j, vR j ≠ w) :
    Ito.itoGen (stripMartObs κ xL xR ρL ρR) ((vL, vR, T), b) (stripDens w vL vR) = 0 := by
  rw [itoGen_stripMartObs κ xL xR ρL ρR hκ hp]
  have hg : gapArg κ xL xR ρL ρR ((vL, vR, T), b) = w - vL (Fin.last nL) := by
    simp only [gapArg, hw]
  have hG : w - vL (Fin.last nL) ≠ 0 := by rw [← hg]; exact hp.1.ne'
  rw [hg]
  simp only [stripDens, driftLin₀]
  set G := w - vL (Fin.last nL) with hGdef
  set lv := 2 / (vL (Fin.last nL) - w) with hlv
  have hsplit : (-(1 / 2) * (∑ i, ρL i * (2 / (vL i - w))) - (1 / 2) * (∑ j, ρR j * (2 / (vR j - w)))
      - lv) / G
      + ∑ i, ρL i / 2 * ((2 / (vL i - w) - lv) / (vL i - vL (Fin.last nL)))
      + ∑ j, ρR j / 2 * ((2 / (vR j - w) - lv) / (vR j - vL (Fin.last nL))) =
      (∑ i, (-(1 / 2) * (ρL i * (2 / (vL i - w))) / G
          + ρL i / 2 * ((2 / (vL i - w) - lv) / (vL i - vL (Fin.last nL)))))
      + (∑ j, (-(1 / 2) * (ρR j * (2 / (vR j - w))) / G
          + ρR j / 2 * ((2 / (vR j - w) - lv) / (vR j - vL (Fin.last nL)))))
      - lv / G := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have hRz : ∑ j, (-(1 / 2) * (ρR j * (2 / (vR j - w))) / G
      + ρR j / 2 * ((2 / (vR j - w) - lv) / (vR j - vL (Fin.last nL)))) = 0 :=
    Finset.sum_eq_zero fun j _ => mark_term_eq_zero (hR j) (hp.2.2 j).ne' hG
  have hLz : ∑ i, (-(1 / 2) * (ρL i * (2 / (vL i - w))) / G
      + ρL i / 2 * ((2 / (vL i - w) - lv) / (vL i - vL (Fin.last nL)))) =
      -(1 / 2) * (ρL (Fin.last nL) * lv) / G := by
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero fun i _ =>
      mark_term_eq_zero (hL i) (hp.2.1 i).ne' hG]
    simp [hlv]
  rw [hsplit, hRz, hLz]
  have hv : vL (Fin.last nL) - w = -G := by rw [hGdef]; ring
  rw [hlv, hv]
  field_simp
  ring


/-- The quadratic strip observable `Φ² − κ T`: along the evolution, the square of the strip martingale minus `κ`
times the strip clock. -/
def stripMartObs2 (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin nR → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin nR → ℝ) (p : SCoord nL nR × ℝ) : ℝ :=
  stripMartObs κ xL xR ρL ρR p * stripMartObs κ xL xR ρL ρR p + -κ * p.1.2.2

theorem contDiffOn_stripMartObs2 {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (stripMartObs2 κ xL xR ρL ρR) (stripMartRegion κ xL xR ρL ρR) :=
  ((contDiffOn_stripMartObs κ xL xR ρL ρR).mul (contDiffOn_stripMartObs κ xL xR ρL ρR)).add (by fun_prop)

omit xL xR ρL ρR in
/-- The generator of the linear clock observable `−κ T`. -/
theorem itoGen_clockObs (p : SCoord nL nR × ℝ) (v : SCoord nL nR) :
    Ito.itoGen (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) p v = -κ * v.2.2 := by
  have hc : ContDiff ℝ 2 (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) := by fun_prop
  have h1 : Ito.partialFst (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) p v = -κ * v.2.2 := by
    refine Ito.partialFst_eq_of_hasDerivAt (hc.differentiable (by norm_num) p) ?_
    have := (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2).const_add p.1.2.2).const_mul (-κ)
    simpa using this
  have h2 : Ito.partialSndSnd (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt hc.contDiffAt (g := fun _ => 0)
      (Eventually.of_forall fun y => ?_) (hasDerivAt_const _ _)
    refine Ito.partialSnd_eq_of_hasDerivAt (hc.differentiable (by norm_num) _) ?_
    simpa using hasDerivAt_const y (-κ * p.1.2.2)
  rw [Ito.itoGen, h1, h2]
  ring

/-- **`Φ² − κ T` has no drift along the strip evolution** (off collisions). -/
theorem itoGen_stripMartObs2_stripDens (hκ : 0 ≤ κ) {vL : Fin (nL + 1) → ℝ} {vR : Fin nR → ℝ} {T b w : ℝ}
    (hw : w = Real.sqrt κ * b + driftLin xL xR ρL ρR (vL, vR, T))
    (hp : ((vL, vR, T), b) ∈ stripMartRegion κ xL xR ρL ρR) (hL : ∀ i : Fin nL, vL i.castSucc ≠ w)
    (hR : ∀ j, vR j ≠ w) :
    Ito.itoGen (stripMartObs2 κ xL xR ρL ρR) ((vL, vR, T), b) (stripDens w vL vR) = 0 := by
  have hΦ := contDiffAt_stripMartObs κ xL xR ρL ρR (n := 2) hp
  have hc : ContDiffAt ℝ 2 (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) ((vL, vR, T), b) := by
    fun_prop
  have e : stripMartObs2 κ xL xR ρL ρR = fun q => (fun q => stripMartObs κ xL xR ρL ρR q *
      stripMartObs κ xL xR ρL ρR q) q + (fun q : SCoord nL nR × ℝ => -κ * q.1.2.2) q := rfl
  rw [e, Ito.itoGen_add (hΦ.mul hΦ) hc, Ito.itoGen_mul hΦ hΦ,
    itoGen_stripMartObs_stripDens κ xL xR ρL ρR hκ hw hp hL hR, itoGen_clockObs,
    partialSnd_stripMartObs κ xL xR ρL ρR hp]
  have hg : gapArg κ xL xR ρL ρR ((vL, vR, T), b) = w - vL (Fin.last nL) := by
    simp only [gapArg, hw]
  have hG : w - vL (Fin.last nL) ≠ 0 := by rw [← hg]; exact hp.1.ne'
  rw [hg]
  simp only [stripDens]
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ
  field_simp
  rw [hs]
  ring

end Zhan

end InteractingSLE

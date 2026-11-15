/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.Observable
import InteractingSLE.Spec.Zhan.StripNoncollisionGen

/-!
# The retargeted driving martingale: the Itô observable

Packet PROVE-SEC7-C8. Along an integrated `SLE_κ(ρ)` evolution with a right target mark `V = V^{R,k}`, the
coordinates `Λ = (V^L, V^R, α, β, S)` are absolutely continuous (`α' = −2α/q²`, `β' = −2α/q³`, `S' = α²/q⁴`,
`q = V − W`) and the driver is the affine function (N1) `W = √κ b − ½ Σ ρ (V − x)` of `Λ` and the Brownian value `b`
(`drv`). The martingale part of the transformed driver `M_t(W_t)` (with its (N1) drift removed) is, up to a
constant,

  `Ψ = c_β β + α/q + ½ Σ_{v ≠ V} ρ_v α/(V − v)`,  `c_β = (κ − 4 − ρ_k)/2`        (`obs`).

* `contDiffOn_obs`: `Ψ` is smooth on the open region `q > 0`, `V ≠ v` (`obsRegion`);
* `partialFst_obs`, `partialSnd_obs` (`∂_b Ψ = √κ α/q²`), `partialSndSnd_obs` (`∂²_b Ψ = 2κα/q³`);
* **`itoGen_obs_eq_zero`**: the Itô drift of `Ψ` vanishes at the density of the coordinates when no mark is at the
  driver (the per-mark identity `mark_term_eq` and the charge `c_β`), and `(∂_b Ψ)² = κ S'`.

So `Ψ` is a local martingale with bracket `κ S`; its time change by `S` is `√κ` times a Brownian motion.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Finset

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-- Coordinates `(V^L, V^R, α, β, S)`. -/
abbrev RCoord (nL nR : ℕ) : Type := (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ × ℝ × ℝ

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
  (k : Fin nR)

/-- (N1): the driver `W = √κ b − ½ Σ ρ (V − x)` as an affine function of the coordinates. -/
def drv (p : RCoord nL nR × ℝ) : ℝ :=
  Real.sqrt κ * p.2 - (1 / 2) * (∑ i, ρL i * (p.1.1 i - xL i)) - (1 / 2) * (∑ i, ρR i * (p.1.2.1 i - xR i))

/-- The target gap `q = V − W`. -/
def qOf (p : RCoord nL nR × ℝ) : ℝ := p.1.2.1 k - drv κ xL xR ρL ρR p

/-- The coefficient of `β`: `c_β = (κ − 4 − ρ_k)/2`. -/
def cBeta : ℝ := (κ - 4 - ρR k) / 2

/-- **The retargeted observable** `Ψ = c_β β + α/q + ½ Σ_{v ≠ V} ρ_v α/(V − v)`. -/
def obs (p : RCoord nL nR × ℝ) : ℝ :=
  cBeta κ ρR k * p.1.2.2.2.1 + p.1.2.2.1 / qOf κ xL xR ρL ρR k p
    + (1 / 2) * (∑ i, ρL i * (p.1.2.2.1 / (p.1.2.1 k - p.1.1 i)))
    + (1 / 2) * (∑ i ∈ univ.erase k, ρR i * (p.1.2.2.1 / (p.1.2.1 k - p.1.2.1 i)))

/-- The open region `q > 0`, `V ≠ v^L_i`, `V ≠ v^R_i` (`i ≠ k`). -/
def obsRegion : Set (RCoord nL nR × ℝ) :=
  {p | 0 < qOf κ xL xR ρL ρR k p ∧ (∀ i, p.1.2.1 k - p.1.1 i ≠ 0) ∧ ∀ i, i ≠ k → p.1.2.1 k - p.1.2.1 i ≠ 0}

theorem contDiff_drv {n : WithTop ℕ∞} : ContDiff ℝ n (drv κ xL xR ρL ρR) := by
  unfold drv; fun_prop

theorem contDiff_qOf {n : WithTop ℕ∞} : ContDiff ℝ n (qOf κ xL xR ρL ρR k) := by
  unfold qOf; exact (by fun_prop : ContDiff ℝ n fun p : RCoord nL nR × ℝ => p.1.2.1 k).sub (contDiff_drv ..)

theorem isOpen_obsRegion : IsOpen (obsRegion κ xL xR ρL ρR k) := by
  have h1 : IsOpen {p : RCoord nL nR × ℝ | 0 < qOf κ xL xR ρL ρR k p} :=
    isOpen_lt continuous_const (contDiff_qOf κ xL xR ρL ρR k (n := 0)).continuous
  have h2 : IsOpen {p : RCoord nL nR × ℝ | ∀ i, p.1.2.1 k - p.1.1 i ≠ 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (by fun_prop) continuous_const
  have h3 : IsOpen {p : RCoord nL nR × ℝ | ∀ i, i ≠ k → p.1.2.1 k - p.1.2.1 i ≠ 0} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun _ =>
      isOpen_ne_fun (by fun_prop) continuous_const
  exact h1.inter (h2.inter h3)

theorem contDiffOn_obs {n : WithTop ℕ∞} : ContDiffOn ℝ n (obs κ xL xR ρL ρR k) (obsRegion κ xL xR ρL ρR k) := by
  have hα : ContDiff ℝ n fun p : RCoord nL nR × ℝ => p.1.2.2.1 := by fun_prop
  refine (((contDiff_const.mul (by fun_prop)).contDiffOn.add ?_).add ?_).add ?_
  · exact hα.contDiffOn.div (contDiff_qOf ..).contDiffOn fun p hp => hp.1.ne'
  · refine contDiffOn_const.mul (ContDiffOn.sum fun i _ => contDiffOn_const.mul ?_)
    exact hα.contDiffOn.div (by fun_prop) fun p hp => hp.2.1 i
  · refine contDiffOn_const.mul (ContDiffOn.sum fun i hi => contDiffOn_const.mul ?_)
    exact hα.contDiffOn.div (by fun_prop) fun p hp => hp.2.2 i (Finset.ne_of_mem_erase hi)

/-! ### Partial derivatives -/

/-- The derivative of the driver along a direction of the coordinates. -/
def dDrv (v : RCoord nL nR) : ℝ := -(1 / 2) * (∑ i, ρL i * v.1 i) - (1 / 2) * (∑ i, ρR i * v.2.1 i)

theorem hasDerivAt_affine_div (a b c d : ℝ) (hc : c ≠ 0) :
    HasDerivAt (fun t : ℝ => (a + t * b) / (c + t * d)) ((b * c - a * d) / c ^ 2) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a
  have h2 : HasDerivAt (fun t : ℝ => c + t * d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const d).const_add c
  have h := h1.fun_div h2 (by simpa using hc)
  simpa using h

theorem sum_mul_add_line {ι : Type*} (s : Finset ι) (ρ a b x : ι → ℝ) (t : ℝ) :
    ∑ i ∈ s, ρ i * ((a i + t * b i) - x i) = (∑ i ∈ s, ρ i * (a i - x i)) + t * ∑ i ∈ s, ρ i * b i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `Ψ` along the line `Λ + t v` (fixed Brownian value). -/
theorem obs_line (p : RCoord nL nR × ℝ) (v : RCoord nL nR) (t : ℝ) :
    obs κ xL xR ρL ρR k (p.1 + t • v, p.2) =
      cBeta κ ρR k * (p.1.2.2.2.1 + t * v.2.2.2.1)
        + (p.1.2.2.1 + t * v.2.2.1) / (qOf κ xL xR ρL ρR k p + t * (v.2.1 k - dDrv ρL ρR v))
        + (1 / 2) * (∑ i, ρL i * ((p.1.2.2.1 + t * v.2.2.1) /
            ((p.1.2.1 k - p.1.1 i) + t * (v.2.1 k - v.1 i))))
        + (1 / 2) * (∑ i ∈ univ.erase k, ρR i * ((p.1.2.2.1 + t * v.2.2.1) /
            ((p.1.2.1 k - p.1.2.1 i) + t * (v.2.1 k - v.2.1 i)))) := by
  simp only [obs, qOf, drv, dDrv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [sum_mul_add_line, sum_mul_add_line]
  have e2 : ∀ i, p.1.2.1 k + t * v.2.1 k - (p.1.1 i + t * v.1 i) =
      (p.1.2.1 k - p.1.1 i) + t * (v.2.1 k - v.1 i) := fun i => by ring
  have e3 : ∀ i, p.1.2.1 k + t * v.2.1 k - (p.1.2.1 i + t * v.2.1 i) =
      (p.1.2.1 k - p.1.2.1 i) + t * (v.2.1 k - v.2.1 i) := fun i => by ring
  simp only [e2, e3]
  ring

variable {κ xL xR ρL ρR k}

/-- **`∂_Λ Ψ · v`**. -/
theorem partialFst_obs {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k) (v : RCoord nL nR) :
    Ito.partialFst (obs κ xL xR ρL ρR k) p v =
      cBeta κ ρR k * v.2.2.2.1
        + (v.2.2.1 * qOf κ xL xR ρL ρR k p - p.1.2.2.1 * (v.2.1 k - dDrv ρL ρR v)) / qOf κ xL xR ρL ρR k p ^ 2
        + (1 / 2) * (∑ i, ρL i * ((v.2.2.1 * (p.1.2.1 k - p.1.1 i) - p.1.2.2.1 * (v.2.1 k - v.1 i)) /
            (p.1.2.1 k - p.1.1 i) ^ 2))
        + (1 / 2) * (∑ i ∈ univ.erase k, ρR i * ((v.2.2.1 * (p.1.2.1 k - p.1.2.1 i) -
            p.1.2.2.1 * (v.2.1 k - v.2.1 i)) / (p.1.2.1 k - p.1.2.1 i) ^ 2)) := by
  have hdiff : DifferentiableAt ℝ (obs κ xL xR ρL ρR k) p :=
    ((contDiffOn_obs κ xL xR ρL ρR k (n := 1)).contDiffAt
      ((isOpen_obsRegion κ xL xR ρL ρR k).mem_nhds hp)).differentiableAt (by norm_num)
  refine Ito.partialFst_eq_of_hasDerivAt hdiff ?_
  simp only [obs_line]
  have hβ : HasDerivAt (fun t : ℝ => cBeta κ ρR k * (p.1.2.2.2.1 + t * v.2.2.2.1)) (cBeta κ ρR k * v.2.2.2.1) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2.2.1).const_add p.1.2.2.2.1).const_mul (cBeta κ ρR k)
  have hL : HasDerivAt (fun t : ℝ => ∑ i, ρL i * ((p.1.2.2.1 + t * v.2.2.1) /
      ((p.1.2.1 k - p.1.1 i) + t * (v.2.1 k - v.1 i))))
      (∑ i, ρL i * ((v.2.2.1 * (p.1.2.1 k - p.1.1 i) - p.1.2.2.1 * (v.2.1 k - v.1 i)) /
        (p.1.2.1 k - p.1.1 i) ^ 2)) 0 :=
    HasDerivAt.fun_sum (u := univ) (A := fun i (t : ℝ) => ρL i * ((p.1.2.2.1 + t * v.2.2.1) /
      ((p.1.2.1 k - p.1.1 i) + t * (v.2.1 k - v.1 i)))) fun i _ =>
        (hasDerivAt_affine_div _ _ _ _ (hp.2.1 i)).const_mul (ρL i)
  have hR : HasDerivAt (fun t : ℝ => ∑ i ∈ univ.erase k, ρR i * ((p.1.2.2.1 + t * v.2.2.1) /
      ((p.1.2.1 k - p.1.2.1 i) + t * (v.2.1 k - v.2.1 i))))
      (∑ i ∈ univ.erase k, ρR i * ((v.2.2.1 * (p.1.2.1 k - p.1.2.1 i) - p.1.2.2.1 * (v.2.1 k - v.2.1 i)) /
        (p.1.2.1 k - p.1.2.1 i) ^ 2)) 0 :=
    HasDerivAt.fun_sum (u := univ.erase k) (A := fun i (t : ℝ) => ρR i * ((p.1.2.2.1 + t * v.2.2.1) /
      ((p.1.2.1 k - p.1.2.1 i) + t * (v.2.1 k - v.2.1 i)))) fun i hi =>
        (hasDerivAt_affine_div _ _ _ _ (hp.2.2 i (Finset.ne_of_mem_erase hi))).const_mul (ρR i)
  exact ((hβ.fun_add (hasDerivAt_affine_div _ _ _ _ hp.1.ne')).fun_add (hL.const_mul _)).fun_add (hR.const_mul _)

/-- **`∂_b Ψ = √κ α/q²`**. -/
theorem hasDerivAt_obs_snd {p : RCoord nL nR × ℝ} (hp : 0 < qOf κ xL xR ρL ρR k p) :
    HasDerivAt (fun y => obs κ xL xR ρL ρR k (p.1, y))
      (Real.sqrt κ * p.1.2.2.1 / qOf κ xL xR ρL ρR k p ^ 2) p.2 := by
  have hq : HasDerivAt (fun y => qOf κ xL xR ρL ρR k (p.1, y)) (-Real.sqrt κ) p.2 := by
    simp only [qOf, drv]
    have := (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).sub_const
      ((1 / 2) * (∑ i, ρL i * (p.1.1 i - xL i)))).sub_const ((1 / 2) * (∑ i, ρR i * (p.1.2.1 i - xR i)))
    simpa using this.const_sub (p.1.2.1 k)
  have h2 : HasDerivAt (fun y => p.1.2.2.1 / qOf κ xL xR ρL ρR k (p.1, y))
      ((0 * qOf κ xL xR ρL ρR k (p.1, p.2) - p.1.2.2.1 * -Real.sqrt κ) / qOf κ xL xR ρL ρR k (p.1, p.2) ^ 2) p.2 :=
    (hasDerivAt_const p.2 p.1.2.2.1).fun_div hq (by simpa using hp.ne')
  have h : HasDerivAt (fun y => obs κ xL xR ρL ρR k (p.1, y))
      (0 + (0 * qOf κ xL xR ρL ρR k (p.1, p.2) - p.1.2.2.1 * -Real.sqrt κ) / qOf κ xL xR ρL ρR k (p.1, p.2) ^ 2
        + 0 + 0) p.2 :=
    (((hasDerivAt_const p.2 (cBeta κ ρR k * p.1.2.2.2.1)).fun_add h2).fun_add
      (hasDerivAt_const p.2 ((1 / 2) * (∑ i, ρL i * (p.1.2.2.1 / (p.1.2.1 k - p.1.1 i)))))).fun_add
      (hasDerivAt_const p.2 ((1 / 2) * (∑ i ∈ univ.erase k, ρR i * (p.1.2.2.1 / (p.1.2.1 k - p.1.2.1 i)))))
  refine h.congr_deriv ?_
  simp only [Prod.mk.eta]
  ring

theorem partialSnd_obs {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k) :
    Ito.partialSnd (obs κ xL xR ρL ρR k) p = Real.sqrt κ * p.1.2.2.1 / qOf κ xL xR ρL ρR k p ^ 2 := by
  have hdiff : DifferentiableAt ℝ (obs κ xL xR ρL ρR k) p :=
    ((contDiffOn_obs κ xL xR ρL ρR k (n := 1)).contDiffAt
      ((isOpen_obsRegion κ xL xR ρL ρR k).mem_nhds hp)).differentiableAt (by norm_num)
  exact Ito.partialSnd_eq_of_hasDerivAt hdiff (hasDerivAt_obs_snd hp.1)

/-- **`∂²_b Ψ = 2κα/q³`** (`κ ≥ 0`). -/
theorem partialSndSnd_obs (hκ : 0 ≤ κ) {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k) :
    Ito.partialSndSnd (obs κ xL xR ρL ρR k) p = 2 * κ * p.1.2.2.1 / qOf κ xL xR ρL ρR k p ^ 3 := by
  have hU := isOpen_obsRegion κ xL xR ρL ρR k
  have hC : ContDiffAt ℝ 2 (obs κ xL xR ρL ρR k) p :=
    (contDiffOn_obs κ xL xR ρL ρR k).contDiffAt (hU.mem_nhds hp)
  have hline : ContinuousAt (fun y : ℝ => ((p.1, y) : RCoord nL nR × ℝ)) p.2 :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : ∀ᶠ y in 𝓝 p.2, Ito.partialSnd (obs κ xL xR ρL ρR k) (p.1, y) =
      Real.sqrt κ * p.1.2.2.1 / qOf κ xL xR ρL ρR k (p.1, y) ^ 2 := by
    have : ∀ᶠ y in 𝓝 p.2, ((p.1, y) : RCoord nL nR × ℝ) ∈ obsRegion κ xL xR ρL ρR k :=
      hline.eventually (hU.mem_nhds (by simpa using hp))
    filter_upwards [this] with y hy
    exact partialSnd_obs hy
  refine Ito.partialSndSnd_eq_of_hasDerivAt hC hev ?_
  have hq : HasDerivAt (fun y => qOf κ xL xR ρL ρR k (p.1, y)) (-Real.sqrt κ) p.2 := by
    simp only [qOf, drv]
    have := (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).sub_const
      ((1 / 2) * (∑ i, ρL i * (p.1.1 i - xL i)))).sub_const ((1 / 2) * (∑ i, ρR i * (p.1.2.1 i - xR i)))
    simpa using this.const_sub (p.1.2.1 k)
  have hq0 : qOf κ xL xR ρL ρR k (p.1, p.2) ≠ 0 := by simpa using hp.1.ne'
  have h := (hasDerivAt_const p.2 (Real.sqrt κ * p.1.2.2.1)).fun_div (hq.fun_pow 2) (pow_ne_zero 2 hq0)
  refine h.congr_deriv ?_
  have hs : Real.sqrt κ * Real.sqrt κ = κ := Real.mul_self_sqrt hκ
  simp only [Prod.mk.eta] at hq0 ⊢
  field_simp
  rw [Real.sq_sqrt hκ]
  ring

/-! ### The generator vanishes along the coordinate density -/

variable (κ xL xR ρL ρR k) in
/-- The density of the coordinates: `(2/(V^L − W), 2/(V^R − W), −2α/q², −2α/q³, α²/q⁴)`. -/
def dens (p : RCoord nL nR × ℝ) : RCoord nL nR :=
  (fun i => 2 / (p.1.1 i - drv κ xL xR ρL ρR p), fun i => 2 / (p.1.2.1 i - drv κ xL xR ρL ρR p),
    -2 * p.1.2.2.1 / qOf κ xL xR ρL ρR k p ^ 2, -2 * p.1.2.2.1 / qOf κ xL xR ρL ρR k p ^ 3,
    p.1.2.2.1 ^ 2 / qOf κ xL xR ρL ρR k p ^ 4)

/-- **The per-mark identity**: `((−2α/q²) D − α(2/q − 2/a))/D² = 2α/(q² a)` for `D = q − a`. -/
theorem mark_term_eq {α q a D : ℝ} (hq : q ≠ 0) (hD : D ≠ 0) (ha : a ≠ 0) (hqa : q - a = D) :
    ((-2 * α / q ^ 2) * D - α * (2 / q - 2 / a)) / D ^ 2 = 2 * α / (q ^ 2 * a) := by
  subst hqa
  field_simp
  ring

/-- **The Itô drift of `Ψ` vanishes** at the coordinate density when no mark is at the driver. -/
theorem itoGen_obs_eq_zero (hκ : 0 ≤ κ) {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k)
    (hL : ∀ i, p.1.1 i ≠ drv κ xL xR ρL ρR p) (hR : ∀ i, p.1.2.1 i ≠ drv κ xL xR ρL ρR p) :
    Ito.itoGen (obs κ xL xR ρL ρR k) p (dens κ xL xR ρL ρR k p) = 0 := by
  set w := drv κ xL xR ρL ρR p with hw
  set q := qOf κ xL xR ρL ρR k p with hqdef
  have hq : q ≠ 0 := hp.1.ne'
  have hqk : p.1.2.1 k - w = q := rfl
  rw [Ito.itoGen, partialFst_obs hp, partialSndSnd_obs hκ hp]
  simp only [dens]
  rw [← hw, ← hqdef, hqk]
  have hmL : ∀ i ∈ (Finset.univ : Finset (Fin nL)), ρL i * ((-2 * p.1.2.2.1 / q ^ 2 * (p.1.2.1 k - p.1.1 i) - p.1.2.2.1 * (2 / q - 2 / (p.1.1 i - w))) /
      (p.1.2.1 k - p.1.1 i) ^ 2) = p.1.2.2.1 / q ^ 2 * (ρL i * (2 / (p.1.1 i - w))) := by
    intro i _
    rw [mark_term_eq hq (hp.2.1 i) (sub_ne_zero.2 (hL i)) (by rw [← hqk]; ring)]
    field_simp
  have hmR : ∀ i ∈ (Finset.univ : Finset (Fin nR)).erase k, ρR i * ((-2 * p.1.2.2.1 / q ^ 2 * (p.1.2.1 k - p.1.2.1 i) -
      p.1.2.2.1 * (2 / q - 2 / (p.1.2.1 i - w))) / (p.1.2.1 k - p.1.2.1 i) ^ 2) =
      p.1.2.2.1 / q ^ 2 * (ρR i * (2 / (p.1.2.1 i - w))) := by
    intro i hi
    rw [mark_term_eq hq (hp.2.2 i (Finset.ne_of_mem_erase hi)) (sub_ne_zero.2 (hR i)) (by rw [← hqk]; ring)]
    field_simp
  rw [Finset.sum_congr rfl hmL, Finset.sum_congr rfl hmR, ← Finset.mul_sum, ← Finset.mul_sum]
  have hsplit : ∑ i, ρR i * (2 / (p.1.2.1 i - w)) = ρR k * (2 / q) + ∑ i ∈ univ.erase k, ρR i * (2 / (p.1.2.1 i - w)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k), hqk]
  simp only [dDrv]
  rw [hsplit]
  simp only [cBeta]
  field_simp
  ring

/-- **The bracket**: `(∂_b Ψ)² = κ α²/q⁴ = κ S'`. -/
theorem partialSnd_obs_sq (hκ : 0 ≤ κ) {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k) :
    Ito.partialSnd (obs κ xL xR ρL ρR k) p ^ 2 = κ * (dens κ xL xR ρL ρR k p).2.2.2.2 := by
  rw [partialSnd_obs hp]
  simp only [dens]
  rw [div_pow, mul_pow, Real.sq_sqrt hκ, ← pow_mul]
  ring

/-! ### The exponential martingale -/

theorem itoGen_clock_coord (c : ℝ) (p : RCoord nL nR × ℝ) (v : RCoord nL nR) :
    Ito.itoGen (fun q : RCoord nL nR × ℝ => c * q.1.2.2.2.2) p v = c * v.2.2.2.2 := by
  have hc : ContDiff ℝ 2 (fun q : RCoord nL nR × ℝ => c * q.1.2.2.2.2) := by fun_prop
  have h1 : Ito.partialFst (fun q : RCoord nL nR × ℝ => c * q.1.2.2.2.2) p v = c * v.2.2.2.2 := by
    refine Ito.partialFst_eq_of_hasDerivAt (hc.differentiable (by norm_num) p) ?_
    have := (((hasDerivAt_id (0 : ℝ)).mul_const v.2.2.2.2).const_add p.1.2.2.2.2).const_mul c
    simpa using this
  have h2 : Ito.partialSndSnd (fun q : RCoord nL nR × ℝ => c * q.1.2.2.2.2) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt hc.contDiffAt (g := fun _ => 0)
      (Eventually.of_forall fun y => ?_) (hasDerivAt_const _ _)
    refine Ito.partialSnd_eq_of_hasDerivAt (hc.differentiable (by norm_num) _) ?_
    simpa using hasDerivAt_const y (c * p.1.2.2.2.2)
  rw [Ito.itoGen, h1, h2]
  ring

variable (κ xL xR ρL ρR k) in
/-- The exponential observable `Z_a = exp(a Ψ/√κ − a² S/2)`. -/
def expObs (a : ℝ) (p : RCoord nL nR × ℝ) : ℝ :=
  Real.exp (a / Real.sqrt κ * obs κ xL xR ρL ρR k p + -(a ^ 2 / 2) * p.1.2.2.2.2)

theorem contDiffOn_expObs (a : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (expObs κ xL xR ρL ρR k a) (obsRegion κ xL xR ρL ρR k) :=
  Real.contDiff_exp.comp_contDiffOn ((contDiffOn_const.mul (contDiffOn_obs κ xL xR ρL ρR k)).add (by fun_prop))

/-- **`Z_a` has no drift** along the coordinate density, off collisions (`κ > 0`). -/
theorem itoGen_expObs_eq_zero (hκ : 0 < κ) (a : ℝ) {p : RCoord nL nR × ℝ} (hp : p ∈ obsRegion κ xL xR ρL ρR k)
    (hL : ∀ i, p.1.1 i ≠ drv κ xL xR ρL ρR p) (hR : ∀ i, p.1.2.1 i ≠ drv κ xL xR ρL ρR p) :
    Ito.itoGen (expObs κ xL xR ρL ρR k a) p (dens κ xL xR ρL ρR k p) = 0 := by
  have hU := isOpen_obsRegion κ xL xR ρL ρR k
  have hΦ : ContDiffAt ℝ 2 (obs κ xL xR ρL ρR k) p := (contDiffOn_obs κ xL xR ρL ρR k).contDiffAt (hU.mem_nhds hp)
  set H : RCoord nL nR × ℝ → ℝ :=
    fun q => a / Real.sqrt κ * obs κ xL xR ρL ρR k q + -(a ^ 2 / 2) * q.1.2.2.2.2 with hHdef
  have hH1 : ContDiffAt ℝ 2 (fun q => a / Real.sqrt κ * obs κ xL xR ρL ρR k q) p := contDiffAt_const.mul hΦ
  have hH2 : ContDiffAt ℝ 2 (fun q : RCoord nL nR × ℝ => -(a ^ 2 / 2) * q.1.2.2.2.2) p := by fun_prop
  have hH : ContDiffAt ℝ 2 H p := hH1.add hH2
  have e : expObs κ xL xR ρL ρR k a = fun q => Real.exp (H q) := rfl
  rw [e, itoGen_comp_of_hasDerivAt (φ := Real.exp) (φ' := Real.exp) (d2 := Real.exp (H p))
    Real.contDiff_exp.contDiffAt hH (Eventually.of_forall fun x => Real.hasDerivAt_exp x)
    (Real.hasDerivAt_exp _)]
  have hgenH : Ito.itoGen H p (dens κ xL xR ρL ρR k p) = -(a ^ 2 / 2) * (dens κ xL xR ρL ρR k p).2.2.2.2 := by
    have eH : H = fun q => (fun q => a / Real.sqrt κ * obs κ xL xR ρL ρR k q) q +
        (fun q : RCoord nL nR × ℝ => -(a ^ 2 / 2) * q.1.2.2.2.2) q := rfl
    rw [eH, Ito.itoGen_add hH1 hH2, itoGen_clock_coord,
      itoGen_comp_of_hasDerivAt (φ := fun x => a / Real.sqrt κ * x) (φ' := fun _ => a / Real.sqrt κ) (d2 := 0)
        (contDiff_const.mul contDiff_id).contDiffAt hΦ
        (Eventually.of_forall fun x => by simpa using (hasDerivAt_id x).const_mul (a / Real.sqrt κ))
        (hasDerivAt_const _ _),
      itoGen_obs_eq_zero hκ.le hp hL hR]
    ring
  have hsndH : Ito.partialSnd H p = a / Real.sqrt κ * Ito.partialSnd (obs κ xL xR ρL ρR k) p := by
    refine Ito.partialSnd_eq_of_hasDerivAt (hH.differentiableAt (by norm_num)) ?_
    have := ((hasDerivAt_obs_snd hp.1).const_mul (a / Real.sqrt κ)).add_const (-(a ^ 2 / 2) * p.1.2.2.2.2)
    rw [partialSnd_obs hp]
    simpa [hHdef] using this
  rw [hgenH, hsndH, mul_pow, partialSnd_obs_sq hκ.le hp, div_pow, Real.sq_sqrt hκ.le]
  field_simp
  ring

end Retarget

end Zhan

end InteractingSLE

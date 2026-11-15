/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripNoncollisionGen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Aux. lemma 102: the angular coordinate and its Itô generator

Packet PROVE-SEC7-C7. Specification p. 347, (P1)–(P4), and p. 348, Aux. lemma 102. For an integrated
`SLE_κ(ρ)` evolution of a separated word with at least one mark on each side, let `D = V^{R,0} − V^{L,0}` be the
cross-gap of the two nearest marks and `U = (W − V^{L,0})/D ∈ [0, 1]` the angular coordinate. In the coordinates of
the localized Itô formula (`Λ = (V^L, V^R, c)`, the Brownian coordinate `b`, the driver `W = √κ b + ℓ(V)` by (N1)),
`U` is a smooth function on the open set `{D > 0}` (`angU`, `angRegion`), affine in `b`, and along the force-point
velocities `2/(V − W)` its drift is (P2)–(P3):

  `itoGen U = (a/U − b/(1 − U))/D² + E/D`,  `a = 2 + Σρ^L`, `b = 2 + Σρ^R`,

with the finite-variation error `E = Σ ρ^{L,i} ((W − V^{L,i})⁻¹ − (W − V^{L,0})⁻¹) − Σ ρ^{R,j} (…)`
(`itoGen_angU_angDens`). For a smooth `φ`, `itoGen (φ ∘ U) = φ'(U) itoGen U + (κ/2) φ''(U)/D²`
(`itoGen_comp_angU`).

Instead of the Brownian tubes of the source's proof, the finiteness of the angular clock is proved with a
**Lyapunov function** `f(u) = −cosh(λ(u − c))` (`lyapF`): if `a ≤ 0` or `b ≤ 0`, there are `λ`, `c ∈ {0, ½, 1}` with
`f'(u)(a/u − b/(1 − u)) + (κ/2) f''(u) ≤ −c₀ < 0` on `(0, 1)` (`exists_lyap`).

## Main results

* `angU`, `gapD`, `angRegion`, `angDens`, `angErr`, `angDrift`;
* `contDiffOn_angU`, `partialFst_angU`, `partialSnd_angU`, `itoGen_comp_angU`, `itoGen_angU_angDens`;
* `lyapF`, `lyapF'`, `lyapF''`, `exists_lyap`, `abs_lyapF_le`, `abs_lyapF'_le`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Clock

open Zhan

variable {nL nR : ℕ}

/-! ### The angular coordinate -/

section Coord

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
  (ρR : Fin (nR + 1) → ℝ)

/-- The cross-gap `D = V^{R,0} − V^{L,0}` of coordinates `p = ((V^L, V^R, c), b)`. -/
def gapD (p : SCoord nL (nR + 1) × ℝ) : ℝ := p.1.2.1 0 - p.1.1 0

/-- The driver `W = √κ b + ℓ(V)` of coordinates (the identity (N1)). -/
def drv (p : SCoord nL (nR + 1) × ℝ) : ℝ := Real.sqrt κ * p.2 + driftLin xL xR ρL ρR p.1

/-- The angular coordinate `U = (W − V^{L,0})/D`. -/
def angU (p : SCoord nL (nR + 1) × ℝ) : ℝ := (drv κ xL xR ρL ρR p - p.1.1 0) / gapD p

/-- The open region `{D > 0}` on which `U` is smooth. -/
def angRegion : Set (SCoord nL (nR + 1) × ℝ) := {p | 0 < gapD p}

theorem continuous_gapD : Continuous (gapD (nL := nL) (nR := nR)) := by
  unfold gapD; fun_prop

theorem isOpen_angRegion : IsOpen (angRegion (nL := nL) (nR := nR)) :=
  isOpen_lt continuous_const continuous_gapD

theorem contDiff_drv {n : WithTop ℕ∞} : ContDiff ℝ n (drv κ xL xR ρL ρR) := by
  unfold drv driftLin; fun_prop

theorem contDiff_gapD {n : WithTop ℕ∞} : ContDiff ℝ n (gapD (nL := nL) (nR := nR)) := by
  unfold gapD; fun_prop

theorem contDiffOn_angU {n : WithTop ℕ∞} : ContDiffOn ℝ n (angU κ xL xR ρL ρR) angRegion :=
  ((contDiff_drv κ xL xR ρL ρR).sub (by fun_prop)).contDiffOn.div contDiff_gapD.contDiffOn
    fun _ hp => (ne_of_gt hp)

theorem contDiffAt_angU {n : WithTop ℕ∞} {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) :
    ContDiffAt ℝ n (angU κ xL xR ρL ρR) p :=
  (contDiffOn_angU κ xL xR ρL ρR).contDiffAt (isOpen_angRegion.mem_nhds hp)

theorem drv_line (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) (t : ℝ) :
    drv κ xL xR ρL ρR (p.1 + t • v, p.2) = drv κ xL xR ρL ρR p + t * driftLin₀ ρL ρR v := by
  have h := gapArg_line κ xL xR ρL ρR p v t
  simp only [gapArg, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  simp only [drv]
  linarith

/-- **`∂_Λ U · v`**: `(ℓ'(v) − v_{L,0} − U (v_{R,0} − v_{L,0}))/D`. -/
theorem partialFst_angU {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) (v : SCoord nL (nR + 1)) :
    Ito.partialFst (angU κ xL xR ρL ρR) p v =
      (driftLin₀ ρL ρR v - v.1 0 - angU κ xL xR ρL ρR p * (v.2.1 0 - v.1 0)) / gapD p := by
  refine Ito.partialFst_eq_of_hasDerivAt ((contDiffAt_angU κ xL xR ρL ρR (n := 1) hp).differentiableAt
    (by norm_num)) ?_
  set N := drv κ xL xR ρL ρR p - p.1.1 0 with hN
  set D := gapD p with hD
  have hline : (fun t : ℝ => angU κ xL xR ρL ρR (p.1 + t • v, p.2)) =
      fun t => (N + t * (driftLin₀ ρL ρR v - v.1 0)) / (D + t * (v.2.1 0 - v.1 0)) := by
    funext t
    simp only [angU, gapD, drv_line, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hN, hD]
    congr 1 <;> ring
  rw [hline]
  have h1 : HasDerivAt (fun t : ℝ => N + t * (driftLin₀ ρL ρR v - v.1 0))
      (1 * (driftLin₀ ρL ρR v - v.1 0)) 0 := ((hasDerivAt_id (0 : ℝ)).mul_const _).const_add N
  have h2 : HasDerivAt (fun t : ℝ => D + t * (v.2.1 0 - v.1 0)) (1 * (v.2.1 0 - v.1 0)) 0 :=
    ((hasDerivAt_id (0 : ℝ)).mul_const _).const_add D
  have hD0 : D + 0 * (v.2.1 0 - v.1 0) ≠ 0 := by rw [zero_mul, add_zero]; exact hp.ne'
  refine (h1.div h2 hD0).congr_deriv ?_
  rw [show angU κ xL xR ρL ρR p = N / D from rfl]
  field_simp
  ring

/-- **`∂_b U = √κ/D`.** -/
theorem partialSnd_angU {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) :
    Ito.partialSnd (angU κ xL xR ρL ρR) p = Real.sqrt κ / gapD p := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_angU κ xL xR ρL ρR (n := 1) hp).differentiableAt
    (by norm_num)) ?_
  have hline : (fun y : ℝ => angU κ xL xR ρL ρR (p.1, y)) =
      fun y => (Real.sqrt κ * y + (driftLin xL xR ρL ρR p.1 - p.1.1 0)) / gapD p := by
    funext y
    simp only [angU, drv, gapD]
    ring
  rw [hline]
  have h := (((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).add_const
    (driftLin xL xR ρL ρR p.1 - p.1.1 0)).div_const (gapD p)
  simpa using h

/-- **`∂²_b U = 0`** (`U` is affine in `b`). -/
theorem partialSndSnd_angU {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) :
    Ito.partialSndSnd (angU κ xL xR ρL ρR) p = 0 := by
  refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_angU κ xL xR ρL ρR hp)
    (g := fun _ => Real.sqrt κ / gapD p) ?_ (hasDerivAt_const _ _)
  refine Eventually.of_forall fun y => ?_
  have hp' : 0 < gapD ((p.1, y) : SCoord nL (nR + 1) × ℝ) := hp
  rw [partialSnd_angU κ xL xR ρL ρR hp']
  rfl

/-- **The Itô generator of `φ ∘ U`**: `φ'(U) ∂_Λ U · v + (κ/2) φ''(U)/D²`. -/
theorem itoGen_comp_angU (hκ : 0 ≤ κ) {φ φ' φ'' : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (h1 : ∀ x, HasDerivAt φ (φ' x) x) (h2 : ∀ x, HasDerivAt φ' (φ'' x) x)
    {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (fun q => φ (angU κ xL xR ρL ρR q)) p v =
      φ' (angU κ xL xR ρL ρR p) *
          ((driftLin₀ ρL ρR v - v.1 0 - angU κ xL xR ρL ρR p * (v.2.1 0 - v.1 0)) / gapD p) +
        κ / 2 * φ'' (angU κ xL xR ρL ρR p) / gapD p ^ 2 := by
  rw [itoGen_comp_of_hasDerivAt hφ.contDiffAt (contDiffAt_angU κ xL xR ρL ρR hp)
    (Eventually.of_forall h1) (h2 _), Ito.itoGen, partialFst_angU κ xL xR ρL ρR hp,
    partialSndSnd_angU κ xL xR ρL ρR hp, partialSnd_angU κ xL xR ρL ρR hp, div_pow,
    Real.sq_sqrt hκ]
  ring

theorem contDiffOn_comp_angU {n : WithTop ℕ∞} {φ : ℝ → ℝ} (hφ : ContDiff ℝ n φ) :
    ContDiffOn ℝ n (fun q => φ (angU κ xL xR ρL ρR q)) angRegion :=
  hφ.comp_contDiffOn (contDiffOn_angU κ xL xR ρL ρR)

end Coord

/-! ### Along the force-point velocities -/

section Dens

/-- The density of the coordinates along a path: the force-point velocities `2/(V − W)` and a third rate `c`. -/
def angDens (w : ℝ) (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ) (c : ℝ) : SCoord nL (nR + 1) :=
  (fun i => 2 / (vL i - w), fun j => 2 / (vR j - w), c)

/-- The finite-variation error (P3): `Σ ρ^{L,i} ((W − V^{L,i})⁻¹ − (W − V^{L,0})⁻¹) − Σ ρ^{R,j} ((V^{R,j} − W)⁻¹ −
(V^{R,0} − W)⁻¹)`. -/
def angErr (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) : ℝ :=
  (∑ i, ρL i * ((w - vL i)⁻¹ - (w - vL 0)⁻¹)) - ∑ j, ρR j * ((vR j - w)⁻¹ - (vR 0 - w)⁻¹)

/-- The Jacobi drift `a/u − b/(1 − u)`. -/
def angDrift (a b u : ℝ) : ℝ := a / u - b / (1 - u)

theorem two_div_sub_eq (v w : ℝ) : 2 / (v - w) = -(2 * (w - v)⁻¹) := by
  rw [show v - w = -(w - v) by ring, div_neg, div_eq_mul_inv]

theorem driftLin₀_angDens (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (w : ℝ)
    (vL : Fin (nL + 1) → ℝ) (vR : Fin (nR + 1) → ℝ) (c : ℝ) :
    driftLin₀ ρL ρR (angDens w vL vR c) = (∑ i, ρL i * (w - vL i)⁻¹) + ∑ j, ρR j * (w - vR j)⁻¹ := by
  simp only [driftLin₀, angDens, two_div_sub_eq, Finset.mul_sum]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- **(P2)–(P3)**: the drift of `U` along the force-point velocities, for `V^{L,0} < W < V^{R,0}`. -/
theorem drift_angU_eq (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) {w : ℝ}
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hL : vL 0 < w) (hR : w < vR 0) (c : ℝ) :
    (driftLin₀ ρL ρR (angDens w vL vR c) - (angDens w vL vR c).1 0 -
        (w - vL 0) / (vR 0 - vL 0) * ((angDens w vL vR c).2.1 0 - (angDens w vL vR c).1 0)) /
        (vR 0 - vL 0) =
      angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) ((w - vL 0) / (vR 0 - vL 0)) / (vR 0 - vL 0) ^ 2 +
        angErr ρL ρR w vL vR / (vR 0 - vL 0) := by
  rw [driftLin₀_angDens]
  have hsL : ∑ i, ρL i * (w - vL i)⁻¹ =
      (∑ i, ρL i * ((w - vL i)⁻¹ - (w - vL 0)⁻¹)) + (∑ i, ρL i) * (w - vL 0)⁻¹ := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsR : ∑ j, ρR j * (w - vR j)⁻¹ =
      -(∑ j, ρR j * ((vR j - w)⁻¹ - (vR 0 - w)⁻¹)) - (∑ j, ρR j) * (vR 0 - w)⁻¹ := by
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show w - vR j = -(vR j - w) by ring, inv_neg]
    ring
  rw [hsL, hsR]
  simp only [angDens, angErr, angDrift]
  set EL := ∑ i, ρL i * ((w - vL i)⁻¹ - (w - vL 0)⁻¹)
  set ER := ∑ j, ρR j * ((vR j - w)⁻¹ - (vR 0 - w)⁻¹)
  set SL := ∑ i, ρL i
  set SR := ∑ j, ρR j
  have hL' : w - vL 0 ≠ 0 := (sub_pos.2 hL).ne'
  have hR' : vR 0 - w ≠ 0 := (sub_pos.2 hR).ne'
  have hD : vR 0 - vL 0 ≠ 0 := (sub_pos.2 (hL.trans hR)).ne'
  have hL'' : vL 0 - w ≠ 0 := fun h => hL' (by linarith)
  have h1 : 1 - (w - vL 0) / (vR 0 - vL 0) = (vR 0 - w) / (vR 0 - vL 0) := by
    field_simp; ring
  rw [h1]
  field_simp
  ring

end Dens

/-! ### The Lyapunov functions `−cosh(λ(u − c))` -/

section Lyap

/-- `f(u) = −cosh(λ(u − c))`. -/
def lyapF (lam c u : ℝ) : ℝ := -Real.cosh (lam * (u - c))

/-- `f'(u) = −λ sinh(λ(u − c))`. -/
def lyapF' (lam c u : ℝ) : ℝ := -(lam * Real.sinh (lam * (u - c)))

/-- `f''(u) = −λ² cosh(λ(u − c))`. -/
def lyapF'' (lam c u : ℝ) : ℝ := -(lam ^ 2 * Real.cosh (lam * (u - c)))

theorem hasDerivAt_lyapF (lam c u : ℝ) : HasDerivAt (lyapF lam c) (lyapF' lam c u) u := by
  have h : HasDerivAt (fun u : ℝ => lam * (u - c)) lam u := by
    simpa using ((hasDerivAt_id u).sub_const c).const_mul lam
  have h2 := ((Real.hasDerivAt_cosh (lam * (u - c))).comp u h).neg
  unfold lyapF lyapF'
  exact h2.congr_deriv (by ring)

theorem hasDerivAt_lyapF' (lam c u : ℝ) : HasDerivAt (lyapF' lam c) (lyapF'' lam c u) u := by
  have h : HasDerivAt (fun u : ℝ => lam * (u - c)) lam u := by
    simpa using ((hasDerivAt_id u).sub_const c).const_mul lam
  have h2 := (((Real.hasDerivAt_sinh (lam * (u - c))).comp u h).const_mul lam).neg
  unfold lyapF' lyapF''
  exact h2.congr_deriv (by ring)

theorem contDiff_lyapF {n : WithTop ℕ∞} (lam c : ℝ) : ContDiff ℝ n (lyapF lam c) := by
  unfold lyapF
  exact (Real.contDiff_cosh.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).neg

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [Real.sinh_eq, Real.cosh_eq, abs_le]
  constructor <;> nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

theorem cosh_le_of_abs_le {x y : ℝ} (h : |x| ≤ y) : Real.cosh x ≤ Real.cosh y :=
  Real.cosh_le_cosh.2 (h.trans (le_abs_self y))

/-- `|f| ≤ cosh λ` on `[0, 1]` for `c ∈ [0, 1]`, `λ ≥ 0`. -/
theorem abs_lyapF_le {lam c u : ℝ} (hlam : 0 ≤ lam) (hc : c ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    |lyapF lam c u| ≤ Real.cosh lam := by
  have habs : |lam * (u - c)| ≤ lam := by
    rw [abs_mul, abs_of_nonneg hlam]
    have : |u - c| ≤ 1 := abs_le.2 ⟨by linarith [hc.2, hu.1], by linarith [hc.1, hu.2]⟩
    nlinarith [abs_nonneg (u - c)]
  rw [lyapF, abs_neg, abs_of_pos (Real.cosh_pos _)]
  exact cosh_le_of_abs_le habs

/-- `|f'| ≤ λ cosh λ` on `[0, 1]` for `c ∈ [0, 1]`, `λ ≥ 0`. -/
theorem abs_lyapF'_le {lam c u : ℝ} (hlam : 0 ≤ lam) (hc : c ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    |lyapF' lam c u| ≤ lam * Real.cosh lam := by
  have habs : |lam * (u - c)| ≤ lam := by
    rw [abs_mul, abs_of_nonneg hlam]
    have : |u - c| ≤ 1 := abs_le.2 ⟨by linarith [hc.2, hu.1], by linarith [hc.1, hu.2]⟩
    nlinarith [abs_nonneg (u - c)]
  rw [lyapF', abs_neg, abs_mul, abs_of_nonneg hlam]
  exact mul_le_mul_of_nonneg_left ((abs_sinh_le_cosh _).trans (cosh_le_of_abs_le habs)) hlam

/-- The Lyapunov generator `f'(u)(a/u − b/(1 − u)) + (κ/2) f''(u)`. -/
def lyapGen (κ a b lam c u : ℝ) : ℝ := lyapF' lam c u * angDrift a b u + κ / 2 * lyapF'' lam c u

/-- **The Lyapunov inequality**: if `a ≤ 0` or `b ≤ 0`, there are `λ ≥ 0`, `c ∈ [0, 1]` and `c₀ > 0` with
`f'(u)(a/u − b/(1 − u)) + (κ/2) f''(u) ≤ −c₀` on `(0, 1)`. Cases: `a ≥ 0 ≥ b` (`c = 0`), `a ≤ 0 ≤ b` (`c = 1`),
`a, b < 0` (`c = ½`, `λ = (4 max(|a|, |b|) + 2)/κ`). -/
theorem exists_lyap {κ a b : ℝ} (hκ : 0 < κ) (hab : a ≤ 0 ∨ b ≤ 0) :
    ∃ lam c c₀ : ℝ, 0 ≤ lam ∧ c ∈ Icc (0 : ℝ) 1 ∧ 0 < c₀ ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, lyapGen κ a b lam c u ≤ -c₀ := by
  -- case `a ≥ 0 ≥ b`
  by_cases h1 : 0 ≤ a ∧ b ≤ 0
  · refine ⟨1, 0, κ / 2, zero_le_one, ⟨le_rfl, zero_le_one⟩, by positivity, fun u hu => ?_⟩
    have hs : 0 ≤ Real.sinh (1 * (u - 0)) := Real.sinh_nonneg_iff.2 (by linarith [hu.1])
    have hC := Real.one_le_cosh (1 * (u - 0))
    have hu1 : 0 < 1 - u := by linarith [hu.2]
    have ha : 0 ≤ a / u := div_nonneg h1.1 hu.1.le
    have hb : b / (1 - u) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1.2 hu1.le
    simp only [lyapGen, lyapF', lyapF'', angDrift]
    nlinarith [mul_nonneg hs ha, mul_nonneg hs (neg_nonneg.2 hb)]
  by_cases h2 : a ≤ 0 ∧ 0 ≤ b
  · refine ⟨1, 1, κ / 2, zero_le_one, ⟨zero_le_one, le_rfl⟩, by positivity, fun u hu => ?_⟩
    have hs : Real.sinh (1 * (u - 1)) ≤ 0 := by
      have : ¬ 0 < Real.sinh (1 * (u - 1)) := fun h =>
        absurd (Real.sinh_pos_iff.1 h) (by linarith [hu.2])
      linarith [not_lt.1 this]
    have hC := Real.one_le_cosh (1 * (u - 1))
    have hu1 : 0 < 1 - u := by linarith [hu.2]
    have ha : a / u ≤ 0 := div_nonpos_of_nonpos_of_nonneg h2.1 hu.1.le
    have hb : 0 ≤ b / (1 - u) := div_nonneg h2.2 hu1.le
    simp only [lyapGen, lyapF', lyapF'', angDrift]
    nlinarith [mul_nonneg (neg_nonneg.2 hs) (neg_nonneg.2 ha), mul_nonneg (neg_nonneg.2 hs) hb]
  -- case `a, b < 0`
  have ha : a < 0 := by
    by_contra ha'
    have ha0 : 0 ≤ a := not_lt.1 ha'
    rcases le_total b 0 with hb | hb
    · exact h1 ⟨ha0, hb⟩
    · rcases hab with h | h
      · exact h2 ⟨h, hb⟩
      · exact h1 ⟨ha0, h⟩
  have hb : b < 0 := by
    by_contra hb'
    exact h2 ⟨ha.le, not_lt.1 hb'⟩
  set M := max |a| |b| with hM
  set lam := (4 * M + 2) / κ with hlam
  have hM0 : 0 ≤ M := (abs_nonneg a).trans (le_max_left _ _)
  have hlam0 : 0 < lam := by positivity
  have hkl : κ / 2 * lam = 2 * M + 1 := by rw [hlam]; field_simp; ring
  refine ⟨lam, 1 / 2, lam, hlam0.le, ⟨by norm_num, by norm_num⟩, hlam0, fun u hu => ?_⟩
  have hu1 : 0 < 1 - u := by linarith [hu.2]
  set S := Real.sinh (lam * (u - 1 / 2))
  set C := Real.cosh (lam * (u - 1 / 2))
  have hC := Real.one_le_cosh (lam * (u - 1 / 2))
  have hSC := abs_sinh_le_cosh (lam * (u - 1 / 2))
  have haM : |a| ≤ M := le_max_left _ _
  have hbM : |b| ≤ M := le_max_right _ _
  have key : lyapF' lam (1 / 2) u * angDrift a b u ≤ 2 * M * lam * C := by
    simp only [lyapF', angDrift]
    rcases le_total (1 / 2 : ℝ) u with hu2 | hu2
    · have hS : 0 ≤ S := Real.sinh_nonneg_iff.2 (mul_nonneg hlam0.le (by linarith))
      have hbu : b / (1 - u) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hb.le hu1.le
      have hau : -(a / u) ≤ 2 * M := by
        rw [← neg_div, div_le_iff₀ hu.1]
        have : -a ≤ M := by rw [← abs_of_neg ha]; exact haM
        nlinarith
      have hSle : S ≤ C := (le_abs_self S).trans hSC
      nlinarith [mul_nonneg hS (neg_nonneg.2 hbu), mul_le_mul_of_nonneg_left hau hS,
        mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 2 * M * lam), hlam0]
    · have hS : S ≤ 0 := by
        have : ¬ 0 < S := fun h => absurd (Real.sinh_pos_iff.1 h)
          (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hlam0.le (by linarith)))
        linarith [not_lt.1 this]
      have hau : a / u ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha.le hu.1.le
      have hbu : -(b / (1 - u)) ≤ 2 * M := by
        rw [← neg_div, div_le_iff₀ hu1]
        have : -b ≤ M := by rw [← abs_of_neg hb]; exact hbM
        nlinarith
      have hSle : -S ≤ C := (neg_le_abs S).trans hSC
      nlinarith [mul_nonneg (neg_nonneg.2 hS) (neg_nonneg.2 hau),
        mul_le_mul_of_nonneg_left hbu (neg_nonneg.2 hS),
        mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 2 * M * lam), hlam0]
  simp only [lyapGen]
  have h2' : κ / 2 * lyapF'' lam (1 / 2) u = -(lam * C * (2 * M + 1)) := by
    simp only [lyapF'']
    rw [← hkl]; ring
  rw [h2']
  nlinarith [mul_le_mul_of_nonneg_left hC hlam0.le]

end Lyap

end Clock

end Sec7

end InteractingSLE

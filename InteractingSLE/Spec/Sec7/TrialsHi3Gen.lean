/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi2Clock
import InteractingSLE.Spec.Ito.TwoPointGen
import InteractingSLE.Spec.Zhan.StripNoncollisionGen

/-!
# The low-sector trial bound: the swallow Lyapunov function and its generator

Packet PROVE-TRIALS-HI3. Specification §7.3, Aux. lemmas 110–111 (`source/spec/p337-384.md` L560–L655): in the low
sector a side whose total `s` lies in `(κ/2 − 4, κ/2 − 2)` is swallowed as a whole at a finite time with positive
probability ("swallows an entire side at a finite continuous endpoint"). Here this is proved on the driving process
(no strip SLE, no field comparison) from a tight start: write

  `X = V^{R,j₁} − W` (the far right gap, `j₁ = Fin.last nR`),  `Δ = V^{R,j₁} − V^{R,0}` (the right spread).

Along the path, with `ℓ = Σ ρ^{L,i}/(W − V^{L,i})` and `R_j = V^{R,j} − W`,

* `gen X^λ = λ X^{λ−2} (2 + Σ ρ^{R,j} X/R_j − ℓ X + κ(λ − 1)/2)`,
* `gen (Δ/X)^μ = μ (Δ/X)^μ X^{−2} (−2X/R_0 − 2 − Σ ρ^{R,j} X/R_j + ℓ X + κ(μ + 1)/2)`.

When the right spread is small relative to `X` and the left marks are far, `Σ ρ^{R,j} X/R_j ≈ s` and `ℓX ≈ 0`, so the
first bracket is `≈ s − (κ/2 − 2) < 0` and the second `≈ (κ/2 − 4) − s < 0`. This file builds the smooth (cut-off)
Lyapunov function `lyapT = α X^λ + β (Δ/X)^μ` on the integrated coordinates and computes its Itô generator along the
path (`itoGen_lyapT_pathCoord`), and proves the pointwise bound `genT ≤ −α λ θ/2 · X^{λ−2}` on the tight region
(`genT_le`).

## Main results

* `cutPow`, `contDiff_cutPow`, `cutPow_eventuallyEq`;
* `farX`, `sprD` and their partial derivatives; `lyapT`, `contDiff_lyapT`;
* `genT`, **`itoGen_lyapT_pathCoord`**, **`genT_le`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi3

open Zhan Clock

/-! ### A smooth cutoff of a real power -/

section Cut

/-- A smooth cutoff of `x ↦ x ^ p` at the level `a`: `x ^ p` for `x > a`, `0` for `x ≤ a/2`. -/
def cutPow (a p x : ℝ) : ℝ := Real.smoothTransition (2 * x / a - 1) * x ^ p

variable {a : ℝ}

theorem cutPow_eventuallyEq (ha : 0 < a) (p : ℝ) {x : ℝ} (hx : a < x) :
    cutPow a p =ᶠ[𝓝 x] fun y => y ^ p := by
  filter_upwards [lt_mem_nhds hx] with y hy
  have h1 : 1 ≤ 2 * y / a - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ ha]; linarith
  simp [cutPow, Real.smoothTransition.one_of_one_le h1]

theorem contDiff_cutPow (ha : 0 < a) (p : ℝ) : ContDiff ℝ 3 (cutPow a p) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge (a / 4) x with hx | hx
  · have hx0 : x ≠ 0 := by
      have : 0 < a / 4 := by positivity
      exact (this.trans hx).ne'
    have h1 : ContDiff ℝ 3 fun y : ℝ => Real.smoothTransition (2 * y / a - 1) :=
      (Real.smoothTransition.contDiff (n := 3)).comp (by fun_prop)
    exact h1.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hx0)
  · have h0 : cutPow a p =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [gt_mem_nhds (show x < a / 2 by linarith)] with y hy
      have : 2 * y / a - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one ha]; linarith
      simp [cutPow, Real.smoothTransition.zero_of_nonpos this]
    exact contDiffAt_const.congr_of_eventuallyEq h0

/-- Near a point `x > a` the cutoff power has the derivative of the power. -/
theorem eventually_hasDerivAt_cutPow (ha : 0 < a) (p : ℝ) {x : ℝ} (hx : a < x) :
    ∀ᶠ y in 𝓝 x, HasDerivAt (cutPow a p) (p * y ^ (p - 1)) y := by
  filter_upwards [lt_mem_nhds hx] with y hy
  have hy0 : y ≠ 0 := (ha.trans hy).ne'
  exact (Real.hasDerivAt_rpow_const (Or.inl hy0)).congr_of_eventuallyEq
    (cutPow_eventuallyEq ha p hy)

/-- The second derivative of the cutoff power at `x > 0`. -/
theorem hasDerivAt_rpow_deriv (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => p * y ^ (p - 1)) (p * ((p - 1) * x ^ (p - 2))) x := by
  have h := (Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx.ne')).const_mul p
  rw [show p - 1 - 1 = p - 2 by ring] at h
  exact h

end Cut

/-! ### The far gap and the spread as functions of the integrated coordinates -/

section Coord

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
  (ρR : Fin (nR + 1) → ℝ) (j₁ : Fin (nR + 1))

/-- The far right gap `X = V^{R,j₁} − W` of coordinates (`W` by (N1)). -/
def farX (p : SCoord nL (nR + 1) × ℝ) : ℝ := p.1.2.1 j₁ - drv κ xL xR ρL ρR p

/-- The right spread `Δ = V^{R,j₁} − V^{R,0}` of coordinates. -/
def sprD (p : SCoord nL (nR + 1) × ℝ) : ℝ := p.1.2.1 j₁ - p.1.2.1 0

theorem contDiff_farX {n : WithTop ℕ∞} : ContDiff ℝ n (farX κ xL xR ρL ρR j₁) := by
  unfold farX
  exact (by fun_prop : ContDiff ℝ n fun p : SCoord nL (nR + 1) × ℝ => p.1.2.1 j₁).sub
    (contDiff_drv κ xL xR ρL ρR)

theorem contDiff_sprD {n : WithTop ℕ∞} : ContDiff ℝ n (sprD (nL := nL) j₁) := by
  unfold sprD; fun_prop

theorem partialFst_farX (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) :
    Ito.partialFst (farX κ xL xR ρL ρR j₁) p v = v.2.1 j₁ - driftLin₀ ρL ρR v := by
  refine Ito.partialFst_eq_of_hasDerivAt ((contDiff_farX κ xL xR ρL ρR j₁ (n := 1)).differentiable
    (by norm_num) p) ?_
  have hline : (fun t : ℝ => farX κ xL xR ρL ρR j₁ (p.1 + t • v, p.2)) =
      fun t => farX κ xL xR ρL ρR j₁ p + t * (v.2.1 j₁ - driftLin₀ ρL ρR v) := by
    funext t
    simp only [farX, drv_line, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  rw [hline]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.1 j₁ - driftLin₀ ρL ρR v)).const_add
    (farX κ xL xR ρL ρR j₁ p)

theorem partialSnd_farX (p : SCoord nL (nR + 1) × ℝ) :
    Ito.partialSnd (farX κ xL xR ρL ρR j₁) p = -Real.sqrt κ := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_farX κ xL xR ρL ρR j₁ (n := 1)).differentiable
    (by norm_num) p) ?_
  have hline : (fun y : ℝ => farX κ xL xR ρL ρR j₁ (p.1, y)) =
      fun y => (p.1.2.1 j₁ - driftLin xL xR ρL ρR p.1) - Real.sqrt κ * y := by
    funext y
    simp only [farX, drv]
    ring
  rw [hline]
  simpa using ((hasDerivAt_id p.2).const_mul (Real.sqrt κ)).const_sub
    (p.1.2.1 j₁ - driftLin xL xR ρL ρR p.1)

theorem partialSndSnd_farX (p : SCoord nL (nR + 1) × ℝ) :
    Ito.partialSndSnd (farX κ xL xR ρL ρR j₁) p = 0 := by
  refine Ito.partialSndSnd_eq_of_hasDerivAt ((contDiff_farX κ xL xR ρL ρR j₁).contDiffAt)
    (g := fun _ => -Real.sqrt κ) ?_ (hasDerivAt_const _ _)
  exact Eventually.of_forall fun y => partialSnd_farX κ xL xR ρL ρR j₁ (p.1, y)

theorem itoGen_farX (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (farX κ xL xR ρL ρR j₁) p v = v.2.1 j₁ - driftLin₀ ρL ρR v := by
  rw [Ito.itoGen, partialFst_farX, partialSndSnd_farX]; ring

theorem partialSnd_sprD (p : SCoord nL (nR + 1) × ℝ) : Ito.partialSnd (sprD (nL := nL) j₁) p = 0 := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_sprD j₁ (n := 1)).differentiable (by norm_num) p) ?_
  simpa [sprD] using hasDerivAt_const p.2 (p.1.2.1 j₁ - p.1.2.1 0)

theorem itoGen_sprD (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (sprD (nL := nL) j₁) p v = v.2.1 j₁ - v.2.1 0 := by
  have h1 : Ito.partialFst (sprD (nL := nL) j₁) p v = v.2.1 j₁ - v.2.1 0 := by
    refine Ito.partialFst_eq_of_hasDerivAt ((contDiff_sprD j₁ (n := 1)).differentiable (by norm_num) p) ?_
    have hline : (fun t : ℝ => sprD (nL := nL) j₁ (p.1 + t • v, p.2)) =
        fun t => sprD (nL := nL) j₁ p + t * (v.2.1 j₁ - v.2.1 0) := by
      funext t
      simp only [sprD, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [hline]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.1 j₁ - v.2.1 0)).const_add (sprD (nL := nL) j₁ p)
  have h2 : Ito.partialSndSnd (sprD (nL := nL) j₁) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt ((contDiff_sprD j₁).contDiffAt) (g := fun _ => 0) ?_
      (hasDerivAt_const _ _)
    exact Eventually.of_forall fun y => partialSnd_sprD j₁ (p.1, y)
  rw [Ito.itoGen, h1, h2]; ring

end Coord

/-! ### The Lyapunov function -/

section Lyap

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
  (ρR : Fin (nR + 1) → ℝ) (j₁ : Fin (nR + 1))

/-- **The swallow Lyapunov function** `α X^λ + β Δ^μ X^{−μ}` (cut off below the level `a`). -/
def lyapT (a α β lam μ : ℝ) (p : SCoord nL (nR + 1) × ℝ) : ℝ :=
  α * cutPow a lam (farX κ xL xR ρL ρR j₁ p) +
    β * (cutPow a μ (sprD j₁ p) * cutPow a (-μ) (farX κ xL xR ρL ρR j₁ p))

variable {a : ℝ}

theorem contDiff_lyapT (ha : 0 < a) (α β lam μ : ℝ) : ContDiff ℝ 3 (lyapT κ xL xR ρL ρR j₁ a α β lam μ) := by
  unfold lyapT
  have h1 := (contDiff_cutPow ha lam).comp (contDiff_farX κ xL xR ρL ρR j₁)
  have h2 := (contDiff_cutPow ha μ).comp (contDiff_sprD (nL := nL) j₁)
  have h3 := (contDiff_cutPow ha (-μ)).comp (contDiff_farX κ xL xR ρL ρR j₁)
  exact (contDiff_const.mul h1).add (contDiff_const.mul (h2.mul h3))

/-- The generator of a cut-off power of the far gap, at a point where the gap exceeds the level. -/
theorem itoGen_cutPow_farX (hκ : 0 ≤ κ) (ha : 0 < a) (q : ℝ) {p : SCoord nL (nR + 1) × ℝ}
    (hX : a < farX κ xL xR ρL ρR j₁ p) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (fun r => cutPow a q (farX κ xL xR ρL ρR j₁ r)) p v =
      q * farX κ xL xR ρL ρR j₁ p ^ (q - 1) * (v.2.1 j₁ - driftLin₀ ρL ρR v) +
        1 / 2 * (q * ((q - 1) * farX κ xL xR ρL ρR j₁ p ^ (q - 2))) * κ := by
  have hX0 : 0 < farX κ xL xR ρL ρR j₁ p := ha.trans hX
  rw [itoGen_comp_of_hasDerivAt ((contDiff_cutPow ha q).contDiffAt.of_le (by norm_num))
    ((contDiff_farX κ xL xR ρL ρR j₁).contDiffAt) (eventually_hasDerivAt_cutPow ha q hX)
    (hasDerivAt_rpow_deriv q hX0), itoGen_farX, partialSnd_farX, neg_sq, Real.sq_sqrt hκ]

/-- The generator of the product `Δ^μ X^{−μ}` (cut off), at a point where both exceed the level. -/
theorem itoGen_cutPow_sprD_mul (hκ : 0 ≤ κ) (ha : 0 < a) (μ : ℝ) {p : SCoord nL (nR + 1) × ℝ}
    (hX : a < farX κ xL xR ρL ρR j₁ p) (hD : a < sprD j₁ p) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (fun r => cutPow a μ (sprD j₁ r) * cutPow a (-μ) (farX κ xL xR ρL ρR j₁ r)) p v =
      sprD j₁ p ^ μ * (-μ * farX κ xL xR ρL ρR j₁ p ^ (-μ - 1) * (v.2.1 j₁ - driftLin₀ ρL ρR v) +
          1 / 2 * (-μ * ((-μ - 1) * farX κ xL xR ρL ρR j₁ p ^ (-μ - 2))) * κ) +
        farX κ xL xR ρL ρR j₁ p ^ (-μ) * (μ * sprD j₁ p ^ (μ - 1) * (v.2.1 j₁ - v.2.1 0)) := by
  have hD0 : 0 < sprD j₁ p := ha.trans hD
  have hc1 : ContDiffAt ℝ 2 (fun r => cutPow a μ (sprD j₁ r)) p :=
    ((contDiff_cutPow ha μ).comp (contDiff_sprD (nL := nL) j₁)).contDiffAt.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 (fun r => cutPow a (-μ) (farX κ xL xR ρL ρR j₁ r)) p :=
    ((contDiff_cutPow ha (-μ)).comp (contDiff_farX κ xL xR ρL ρR j₁)).contDiffAt.of_le (by norm_num)
  have hg1 : Ito.itoGen (fun r => cutPow a μ (sprD j₁ r)) p v = μ * sprD j₁ p ^ (μ - 1) * (v.2.1 j₁ - v.2.1 0) := by
    rw [itoGen_comp_of_hasDerivAt ((contDiff_cutPow ha μ).contDiffAt.of_le (by norm_num))
      ((contDiff_sprD (nL := nL) j₁).contDiffAt) (eventually_hasDerivAt_cutPow ha μ hD)
      (hasDerivAt_rpow_deriv μ hD0), itoGen_sprD, partialSnd_sprD]
    ring
  have hs1 : Ito.partialSnd (fun r => cutPow a μ (sprD j₁ r)) p = 0 := by
    rw [partialSnd_comp_of_hasDerivAt (φ' := fun y => μ * y ^ (μ - 1))
      ((contDiff_sprD (nL := nL) j₁ (n := 1)).differentiable (by norm_num) p)
      (eventually_hasDerivAt_cutPow ha μ hD).self_of_nhds, partialSnd_sprD, mul_zero]
  rw [Ito.itoGen_mul hc1 hc2, hg1, itoGen_cutPow_farX κ xL xR ρL ρR j₁ hκ ha (-μ) hX, hs1, zero_mul, add_zero,
    (cutPow_eventuallyEq ha μ hD).self_of_nhds, (cutPow_eventuallyEq ha (-μ) hX).self_of_nhds]

/-- **The generator of the swallow Lyapunov function** at a point where `X` and `Δ` exceed the level. -/
theorem itoGen_lyapT (hκ : 0 ≤ κ) (ha : 0 < a) (α β lam μ : ℝ) {p : SCoord nL (nR + 1) × ℝ}
    (hX : a < farX κ xL xR ρL ρR j₁ p) (hD : a < sprD j₁ p) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (lyapT κ xL xR ρL ρR j₁ a α β lam μ) p v =
      α * (lam * farX κ xL xR ρL ρR j₁ p ^ (lam - 1) * (v.2.1 j₁ - driftLin₀ ρL ρR v) +
          1 / 2 * (lam * ((lam - 1) * farX κ xL xR ρL ρR j₁ p ^ (lam - 2))) * κ) +
        β * (sprD j₁ p ^ μ * (-μ * farX κ xL xR ρL ρR j₁ p ^ (-μ - 1) * (v.2.1 j₁ - driftLin₀ ρL ρR v) +
            1 / 2 * (-μ * ((-μ - 1) * farX κ xL xR ρL ρR j₁ p ^ (-μ - 2))) * κ) +
          farX κ xL xR ρL ρR j₁ p ^ (-μ) * (μ * sprD j₁ p ^ (μ - 1) * (v.2.1 j₁ - v.2.1 0))) := by
  have hc1 : ContDiffAt ℝ 2 (fun r => cutPow a lam (farX κ xL xR ρL ρR j₁ r)) p :=
    ((contDiff_cutPow ha lam).comp (contDiff_farX κ xL xR ρL ρR j₁)).contDiffAt.of_le (by norm_num)
  have hc2 : ContDiffAt ℝ 2 (fun r => cutPow a μ (sprD j₁ r) * cutPow a (-μ) (farX κ xL xR ρL ρR j₁ r)) p :=
    ((((contDiff_cutPow ha μ).comp (contDiff_sprD (nL := nL) j₁)).mul
      ((contDiff_cutPow ha (-μ)).comp (contDiff_farX κ xL xR ρL ρR j₁))).contDiffAt).of_le (by norm_num)
  have hsc : ∀ (c : ℝ) {F : SCoord nL (nR + 1) × ℝ → ℝ}, ContDiffAt ℝ 2 F p →
      Ito.itoGen (fun r => c * F r) p v = c * Ito.itoGen F p v := fun c F hF => by
    rw [itoGen_comp_of_hasDerivAt (φ := fun x => c * x) (φ' := fun _ => c) (d2 := 0)
      (contDiff_const.mul contDiff_id).contDiffAt hF
      (Eventually.of_forall fun x => by simpa using (hasDerivAt_id x).const_mul c) (hasDerivAt_const _ _)]
    ring
  have e : lyapT κ xL xR ρL ρR j₁ a α β lam μ = fun r =>
      (fun r => α * cutPow a lam (farX κ xL xR ρL ρR j₁ r)) r +
        (fun r => β * (cutPow a μ (sprD j₁ r) * cutPow a (-μ) (farX κ xL xR ρL ρR j₁ r))) r := rfl
  rw [e, Ito.itoGen_add (contDiffAt_const.mul hc1) (contDiffAt_const.mul hc2), hsc α hc1, hsc β hc2,
    itoGen_cutPow_farX κ xL xR ρL ρR j₁ hκ ha lam hX, itoGen_cutPow_sprD_mul κ xL xR ρL ρR j₁ hκ ha μ hX hD]

end Lyap

/-! ### The generator as an explicit expression, and its bound -/

section Expr

/-- **The generator of `lyapT` in the variables** `X` (far gap), `Δ` (spread), `gX` (drift of `X`), `gD` (drift of
`Δ`). -/
def genTE (κ α β lam μ X Δ gX gD : ℝ) : ℝ :=
  α * (lam * X ^ (lam - 1) * gX + 1 / 2 * (lam * ((lam - 1) * X ^ (lam - 2))) * κ) +
    β * (Δ ^ μ * (-μ * X ^ (-μ - 1) * gX + 1 / 2 * (-μ * ((-μ - 1) * X ^ (-μ - 2))) * κ) +
      X ^ (-μ) * (μ * Δ ^ (μ - 1) * gD))

/-- **The factored form**: with `gX = (2 + SR − LX)/X` and `gD = 2/X − 2/R₀`, `R₀ = X − Δ`,
`genTE = α λ X^{λ−2} (2 + SR − LX + κ(λ − 1)/2) + β μ Δ^μ X^{−μ−2} (−(2 + SR − LX) + κ(μ + 1)/2 − 2X/R₀)`. -/
theorem genTE_eq {κ α β lam μ X Δ R₀ SR LX : ℝ} (hX : 0 < X) (hΔ : 0 < Δ) (hR₀ : R₀ = X - Δ) (hR₀p : 0 < R₀) :
    genTE κ α β lam μ X Δ ((2 + SR - LX) / X) (2 / X - 2 / R₀) =
      α * lam * X ^ (lam - 2) * (2 + SR - LX + κ * (lam - 1) / 2) +
        β * μ * (Δ ^ μ * X ^ (-μ - 2)) * (-(2 + SR - LX) + κ * (μ + 1) / 2 - 2 * X / R₀) := by
  have e1 : X ^ (lam - 1) = X ^ (lam - 2) * X := by
    rw [← Real.rpow_add_one hX.ne']; ring_nf
  have e2 : X ^ (-μ - 1) = X ^ (-μ - 2) * X := by
    rw [← Real.rpow_add_one hX.ne']; ring_nf
  have e3 : X ^ (-μ) = X ^ (-μ - 2) * X ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hX]; ring_nf
  have e4 : Δ ^ (μ - 1) = Δ ^ μ / Δ := by
    rw [Real.rpow_sub_one hΔ.ne']
  have hXne := hX.ne'
  have hΔne := hΔ.ne'
  have hRne := hR₀p.ne'
  simp only [genTE, e1, e2, e3, e4]
  rw [hR₀] at hRne ⊢
  field_simp
  ring

/-- **The pointwise bound on the tight region.** If `|SR − s| ≤ e₁`, `|LX| ≤ e₂`, `0 < Δ`, `R₀ = X − Δ > 0`, and the
brackets are controlled, `(s − (κ/2 − 2)) + κλ/2 + e₁ + e₂ ≤ −θ/2` and `(κ/2 − 4 − s) + κμ/2 + e₁ + e₂ ≤ 0`, then
`genTE ≤ −α λ (θ/2) X^{λ−2}`. -/
theorem genTE_le {κ α β lam μ X Δ R₀ SR LX s e₁ e₂ θ : ℝ} (hX : 0 < X) (hΔ : 0 < Δ) (hR₀ : R₀ = X - Δ)
    (hR₀p : 0 < R₀) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hlam : 0 < lam) (hμ : 0 < μ) (hSR : |SR - s| ≤ e₁)
    (hLX : |LX| ≤ e₂) (h1 : (s - (κ / 2 - 2)) + κ * lam / 2 + e₁ + e₂ ≤ -(θ / 2))
    (h2 : (κ / 2 - 4 - s) + κ * μ / 2 + e₁ + e₂ ≤ 0) :
    genTE κ α β lam μ X Δ ((2 + SR - LX) / X) (2 / X - 2 / R₀) ≤ -(α * lam * (θ / 2) * X ^ (lam - 2)) := by
  rw [genTE_eq hX hΔ hR₀ hR₀p]
  have hA : 0 < X ^ (lam - 2) := Real.rpow_pos_of_pos hX _
  have hB : 0 < Δ ^ μ * X ^ (-μ - 2) := mul_pos (Real.rpow_pos_of_pos hΔ _) (Real.rpow_pos_of_pos hX _)
  have hXR : 1 ≤ X / R₀ := by rw [le_div_iff₀ hR₀p]; linarith
  have hSR' := abs_le.1 hSR
  have hLX' := abs_le.1 hLX
  have b1 : 2 + SR - LX + κ * (lam - 1) / 2 ≤ -(θ / 2) := by linarith
  have b2 : -(2 + SR - LX) + κ * (μ + 1) / 2 - 2 * X / R₀ ≤ 0 := by
    have : 2 * X / R₀ = 2 * (X / R₀) := by ring
    rw [this]; linarith
  have t1 : α * lam * X ^ (lam - 2) * (2 + SR - LX + κ * (lam - 1) / 2) ≤
      α * lam * X ^ (lam - 2) * (-(θ / 2)) :=
    mul_le_mul_of_nonneg_left b1 (by positivity)
  have t2 : β * μ * (Δ ^ μ * X ^ (-μ - 2)) * (-(2 + SR - LX) + κ * (μ + 1) / 2 - 2 * X / R₀) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) b2
  nlinarith [t1, t2]

end Expr

/-! ### Along the path -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The drift `gX` of the far gap along the path. -/
def driftX (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (j₁ : Fin (nR + 1)) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  2 / (vR j₁ t - w t) - ((∑ i, ρL i * (w t - vL i t)⁻¹) + ∑ j, ρR j * (w t - vR j t)⁻¹)

/-- **The generator of the swallow Lyapunov function along the path**, at real time `s`. -/
def genT (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (j₁ : Fin (nR + 1)) (α β lam μ : ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  genTE κ α β lam μ (vR j₁ s.toNNReal - w s.toNNReal) (vR j₁ s.toNNReal - vR 0 s.toNNReal)
    (driftX ρL ρR j₁ w vL vR s.toNNReal) (2 / (vR j₁ s.toNNReal - w s.toNNReal) - 2 / (vR 0 s.toNNReal - w s.toNNReal))

variable (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
include hp

theorem drv_pathCoord (I : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    drv κ xL xR ρL ρR (pathCoord vL vR b I t) = w t := by
  rw [hp.isForcePath.w_eq_N1 hp.driverEq ht]
  simp only [drv, driftLin, pathCoord]
  ring

theorem farX_pathCoord (j₁ : Fin (nR + 1)) (I : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    farX κ xL xR ρL ρR j₁ (pathCoord vL vR b I t) = vR j₁ t - w t := by
  rw [farX, drv_pathCoord hp I ht]; rfl

omit hp in
theorem sprD_pathCoord (j₁ : Fin (nR + 1)) (I : ℝ) (t : ℝ≥0) :
    sprD j₁ (pathCoord vL vR b I t) = vR j₁ t - vR 0 t := rfl

/-- **The generator of `lyapT` along the path** (with the force-point velocities), where the far gap and the spread
exceed the cutoff level. -/
theorem itoGen_lyapT_pathCoord (hκ : 0 ≤ κ) {a : ℝ} (ha : 0 < a) (j₁ : Fin (nR + 1)) (α β lam μ I c : ℝ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hX : a < vR j₁ t - w t) (hD : a < vR j₁ t - vR 0 t) :
    Ito.itoGen (lyapT κ xL xR ρL ρR j₁ a α β lam μ) (pathCoord vL vR b I t)
        (angDens (w t) (fun i => vL i t) (fun j => vR j t) c) =
      genT κ ρL ρR j₁ α β lam μ w vL vR t := by
  have hX' : a < farX κ xL xR ρL ρR j₁ (pathCoord vL vR b I t) := by rw [farX_pathCoord hp j₁ I ht]; exact hX
  have hD' : a < sprD j₁ (pathCoord vL vR b I t) := hD
  rw [itoGen_lyapT κ xL xR ρL ρR j₁ hκ ha α β lam μ hX' hD', farX_pathCoord hp j₁ I ht, sprD_pathCoord,
    driftLin₀_angDens]
  simp only [genT, genTE, driftX, angDens, Real.toNNReal_coe]

end Path

/-! ### The bound on the tight region, along the path -/

section Region

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The drift of the far gap in the factored form `(2 + SR − LX)/X`. -/
theorem driftX_eq {j₁ : Fin (nR + 1)} {t : ℝ≥0} (hX : 0 < vR j₁ t - w t) (hR : ∀ j, 0 < vR j t - w t) :
    driftX ρL ρR j₁ w vL vR t =
      (2 + (∑ j, ρR j * ((vR j₁ t - w t) / (vR j t - w t))) -
        (vR j₁ t - w t) * ∑ i, ρL i * (w t - vL i t)⁻¹) / (vR j₁ t - w t) := by
  have hXne := hX.ne'
  have e : ∀ j, ρR j * (w t - vR j t)⁻¹ = -(ρR j * ((vR j₁ t - w t) / (vR j t - w t)) / (vR j₁ t - w t)) := by
    intro j
    have hj := (hR j).ne'
    rw [show w t - vR j t = -(vR j t - w t) by ring, inv_neg]
    field_simp
  simp only [driftX, e, Finset.sum_neg_distrib, ← Finset.sum_div]
  field_simp
  ring

/-- **The generator bound on the tight region** at one time `t < ζ`: the far gap `X > 0`, the spread
`0 < Δ ≤ ε₁ X` with `ε₁ < 1`, the nearest left gap `L₀ > 0` with `X ≤ η L₀`, and the bracket conditions with
`e₁ = Σ|ρ^R| ε₁/(1 − ε₁)`, `e₂ = Σ|ρ^L| η`. -/
theorem genT_le_of_region (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {α β lam μ ε₁ η θ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hlam : 0 < lam)
    (hμ : 0 < μ) (hε₁ : ε₁ < 1) (hX : 0 < vR (Fin.last nR) t - w t)
    (hΔ : 0 < vR (Fin.last nR) t - vR 0 t)
    (hΔε : vR (Fin.last nR) t - vR 0 t ≤ ε₁ * (vR (Fin.last nR) t - w t)) (hL0 : 0 < w t - vL 0 t)
    (hXη : vR (Fin.last nR) t - w t ≤ η * (w t - vL 0 t))
    (h1 : ((∑ j, ρR j) - (κ / 2 - 2)) + κ * lam / 2 + (∑ j, |ρR j|) * (ε₁ / (1 - ε₁)) +
      (∑ i, |ρL i|) * η ≤ -(θ / 2))
    (h2 : (κ / 2 - 4 - ∑ j, ρR j) + κ * μ / 2 + (∑ j, |ρR j|) * (ε₁ / (1 - ε₁)) + (∑ i, |ρL i|) * η ≤ 0) :
    genT κ ρL ρR (Fin.last nR) α β lam μ w vL vR t ≤
      -(α * lam * (θ / 2) * (vR (Fin.last nR) t - w t) ^ (lam - 2)) := by
  have hf := hp.isForcePath
  set X := vR (Fin.last nR) t - w t with hXdef
  set Δ := vR (Fin.last nR) t - vR 0 t with hΔdef
  set L₀ := w t - vL 0 t with hL₀def
  have hε₁0 : 0 ≤ ε₁ := by
    by_contra h
    have : ε₁ * X < 0 := mul_neg_of_neg_of_pos (not_le.1 h) hX
    linarith
  have h1ε : 0 < 1 - ε₁ := by linarith
  have hRX : vR 0 t - w t = X - Δ := by simp only [hXdef, hΔdef]; ring
  have hR0 : 0 < vR 0 t - w t := by rw [hRX]; nlinarith
  -- the right gaps lie in `[R₀, X]`
  have hRj : ∀ j, vR 0 t - w t ≤ vR j t - w t ∧ vR j t - w t ≤ X := fun j => by
    have h0 := hf.monotone_vR ht (Fin.zero_le j)
    have h1 := hf.monotone_vR ht (Fin.le_last j)
    simp only at h0 h1
    exact ⟨by linarith, by simp only [hXdef]; linarith⟩
  have hRpos : ∀ j, 0 < vR j t - w t := fun j => hR0.trans_le (hRj j).1
  -- the left gaps are at least `L₀`
  have hLi : ∀ i, L₀ ≤ w t - vL i t := fun i => by
    have h0 := hf.antitone_vL ht (Fin.zero_le i)
    simp only at h0
    simp only [hL₀def]; linarith
  -- `|SR − s| ≤ e₁`
  set SR := ∑ j, ρR j * (X / (vR j t - w t)) with hSRdef
  have hratio : ∀ j, 0 ≤ X / (vR j t - w t) - 1 ∧ X / (vR j t - w t) - 1 ≤ ε₁ / (1 - ε₁) := fun j => by
    have hj := hRpos j
    have hjX := (hRj j).2
    have hj0 := (hRj j).1
    constructor
    · rw [sub_nonneg, le_div_iff₀ hj]; linarith
    · rw [div_sub_one hj.ne', div_le_div_iff₀ hj h1ε]
      have hXR : X - (vR j t - w t) ≤ Δ := by rw [hRX] at hj0; linarith
      nlinarith
  have hSR : |SR - ∑ j, ρR j| ≤ (∑ j, |ρR j|) * (ε₁ / (1 - ε₁)) := by
    have e : SR - ∑ j, ρR j = ∑ j, ρR j * (X / (vR j t - w t) - 1) := by
      simp only [hSRdef, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (hratio j).1]
    exact mul_le_mul_of_nonneg_left (hratio j).2 (abs_nonneg _)
  -- `|LX| ≤ e₂`
  set LX := X * ∑ i, ρL i * (w t - vL i t)⁻¹ with hLXdef
  have hLX : |LX| ≤ (∑ i, |ρL i|) * η := by
    rw [hLXdef, abs_mul, abs_of_pos hX]
    have hs : |∑ i, ρL i * (w t - vL i t)⁻¹| ≤ ∑ i, |ρL i| * L₀⁻¹ := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_inv, abs_of_pos (hL0.trans_le (hLi i))]
      exact mul_le_mul_of_nonneg_left (inv_anti₀ hL0 (hLi i)) (abs_nonneg _)
    rw [← Finset.sum_mul] at hs
    have hXL : X * L₀⁻¹ ≤ η := by rw [← div_eq_mul_inv, div_le_iff₀ hL0]; exact hXη
    calc X * |∑ i, ρL i * (w t - vL i t)⁻¹| ≤ X * ((∑ i, |ρL i|) * L₀⁻¹) :=
          mul_le_mul_of_nonneg_left hs hX.le
      _ = (∑ i, |ρL i|) * (X * L₀⁻¹) := by ring
      _ ≤ (∑ i, |ρL i|) * η :=
          mul_le_mul_of_nonneg_left hXL (Finset.sum_nonneg fun i _ => abs_nonneg _)
  -- the factored form
  have hgen : genT κ ρL ρR (Fin.last nR) α β lam μ w vL vR t =
      genTE κ α β lam μ X Δ ((2 + SR - LX) / X) (2 / X - 2 / (X - Δ)) := by
    rw [← hRX]
    simp only [genT, Real.toNNReal_coe, driftX_eq hX hRpos]
    rfl
  rw [hgen]
  exact genTE_le hX hΔ rfl (by rw [← hRX]; exact hR0) hα hβ hlam hμ hSR hLX h1 h2

end Region

end TrialsHi3

end Sec7

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi3Tight

/-!
# The critical side oscillation: the Lyapunov function and its generator

Packet PROVE-TRIALS-HI4. Specification §7.3, Aux. lemma 111 ("Both totals are at least `c`" and "A sole right mark is
allowed to continue", `source/spec/p337-384.md` L594–L655). For the transfer of a reference success event to the
proposed weights the change-of-weights energy is bounded by the *side oscillation* `∫ (1/R₀² − 1/X²)` of the changed
side (`TrialsHi.changeEnergy_le_osc`), where for the right side

  `R₀ = V^{R,0} − W` (the nearest gap),  `X = V^{R,last} − W` (the far gap),  `Δ = X − R₀` (the spread),

and `D = V^{R,0} − V^{L,0}` is the nearest cross gap. When the reference weight `s` of the nearest right mark is
*critical* (`s = κ/2 − 2`), the inverse moments of `R₀` are not integrable; the deterministic contraction of the spread
(`dΔ = −2Δ/(R₀X) dt`) is used instead. With `r` the weight of the nearest left mark (the only other nonzero weight),
`y = Δ/R₀ ≤ 1`, and

  `Φ = (Δ/R₀)^μ + K (Δ/D)^μ`,  `μ ≤ 1`, `κ μ ≤ 1/2`, `K = 2|r|(1 + 4|r|)`,

the generator is `≤ −(μ/4) (1/R₀² − 1/X²)` for every `s ≥ κ/2 − 2` and every `r` (`critGenE_le`). The left mark may
collide with the driver: its drift enters only through `r R₀/L₀`, which is either small (`R₀ ≪ D`) or absorbed by the
term `K (Δ/D)^μ`, whose generator contains `−2Kμ (Δ/D)^μ/(R₀ L₀)`.

This file builds `Φ` on the integrated coordinates (cut off below a level so that it is `C³`), computes its Itô
generator along the path (`itoGen_critPhi_pathCoord`), and proves the pointwise bound.

## Main results

* `critPhi`, `contDiff_critPhi`, `itoGen_critPhi`, `itoGen_critPhi_pathCoord`;
* `critGenE`, `critGenE_eq`, **`critGenE_le`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi4

open Zhan Clock TrialsHi3

/-! ### The Lyapunov function on the coordinates -/

section Lyap

variable {nL nR : ℕ} (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
  (ρR : Fin (nR + 1) → ℝ)

/-- **The critical-oscillation Lyapunov function** `(Δ/R₀)^μ + K (Δ/D)^μ` (cut off below the levels `a` and `1`),
with `R₀ = V^{R,0} − W`, `Δ = V^{R,last} − V^{R,0}` and `D = V^{R,0} − V^{L,0}`. -/
def critPhi (a μ K : ℝ) (p : SCoord nL (nR + 1) × ℝ) : ℝ :=
  cutPow a μ (sprD (Fin.last nR) p) * cutPow a (-μ) (farX κ xL xR ρL ρR 0 p) +
    K * (cutPow a μ (sprD (Fin.last nR) p) * cutPow 1 (-μ) (gapD p))

variable {a : ℝ}

theorem contDiff_critPhi (ha : 0 < a) (μ K : ℝ) : ContDiff ℝ 3 (critPhi κ xL xR ρL ρR a μ K) := by
  unfold critPhi
  have h1 := (contDiff_cutPow ha μ).comp (contDiff_sprD (nL := nL) (Fin.last nR))
  have h2 := (contDiff_cutPow ha (-μ)).comp (contDiff_farX κ xL xR ρL ρR 0)
  have h3 := (contDiff_cutPow one_pos (-μ)).comp (contDiff_gapD (nL := nL) (nR := nR))
  exact (h1.mul h2).add (contDiff_const.mul (h1.mul h3))

theorem critPhi_nonneg (ha : 0 < a) (μ : ℝ) {K : ℝ} (hK : 0 ≤ K) (p : SCoord nL (nR + 1) × ℝ) :
    0 ≤ critPhi κ xL xR ρL ρR a μ K p := by
  unfold critPhi
  have h1 := cutPow_nonneg ha μ (sprD (nL := nL) (Fin.last nR) p)
  have h2 := cutPow_nonneg ha (-μ) (farX κ xL xR ρL ρR 0 p)
  have h3 := cutPow_nonneg one_pos (-μ) (gapD p)
  positivity

theorem partialSnd_gapD (p : SCoord nL (nR + 1) × ℝ) : Ito.partialSnd (gapD (nL := nL) (nR := nR)) p = 0 := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiff_gapD (n := 1)).differentiable (by norm_num) p) ?_
  simpa [gapD] using hasDerivAt_const p.2 (p.1.2.1 0 - p.1.1 0)

theorem itoGen_gapD (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (gapD (nL := nL) (nR := nR)) p v = v.2.1 0 - v.1 0 := by
  have h1 : Ito.partialFst (gapD (nL := nL) (nR := nR)) p v = v.2.1 0 - v.1 0 := by
    refine Ito.partialFst_eq_of_hasDerivAt ((contDiff_gapD (n := 1)).differentiable (by norm_num) p) ?_
    have hline : (fun t : ℝ => gapD (nL := nL) (nR := nR) (p.1 + t • v, p.2)) =
        fun t => gapD p + t * (v.2.1 0 - v.1 0) := by
      funext t
      simp only [gapD, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    rw [hline]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (v.2.1 0 - v.1 0)).const_add (gapD p)
  have h2 : Ito.partialSndSnd (gapD (nL := nL) (nR := nR)) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiff_gapD.contDiffAt) (g := fun _ => 0) ?_
      (hasDerivAt_const _ _)
    exact Eventually.of_forall fun y => partialSnd_gapD (p.1, y)
  rw [Ito.itoGen, h1, h2]; ring

/-- The generator of a cut-off power of a coordinate function `F` with `∂_b F = 0`. -/
theorem itoGen_cutPow_of_partialSnd {a' q : ℝ} (ha' : 0 < a') {F : SCoord nL (nR + 1) × ℝ → ℝ}
    (hF : ContDiff ℝ 3 F) {p : SCoord nL (nR + 1) × ℝ} (hFp : a' < F p) (hs : Ito.partialSnd F p = 0)
    (v : SCoord nL (nR + 1)) :
    Ito.itoGen (fun r => cutPow a' q (F r)) p v = q * F p ^ (q - 1) * Ito.itoGen F p v := by
  rw [itoGen_comp_of_hasDerivAt ((contDiff_cutPow ha' q).contDiffAt.of_le (by norm_num))
    (hF.contDiffAt.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)) (eventually_hasDerivAt_cutPow ha' q hFp)
    (hasDerivAt_rpow_deriv q (ha'.trans hFp)), hs]
  ring

theorem partialSnd_cutPow_of_partialSnd {a' q : ℝ} (ha' : 0 < a') {F : SCoord nL (nR + 1) × ℝ → ℝ}
    (hF : ContDiff ℝ 3 F) {p : SCoord nL (nR + 1) × ℝ} (hFp : a' < F p) (hs : Ito.partialSnd F p = 0) :
    Ito.partialSnd (fun r => cutPow a' q (F r)) p = 0 := by
  rw [partialSnd_comp_of_hasDerivAt (φ' := fun y => q * y ^ (q - 1))
    ((hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiable (by norm_num) p)
    (eventually_hasDerivAt_cutPow ha' q hFp).self_of_nhds, hs, mul_zero]

/-- **The generator of the critical-oscillation Lyapunov function** where `R₀`, `Δ` exceed `a` and `D > 1`. -/
theorem itoGen_critPhi (hκ : 0 ≤ κ) (ha : 0 < a) (μ K : ℝ) {p : SCoord nL (nR + 1) × ℝ}
    (hR : a < farX κ xL xR ρL ρR 0 p) (hΔ : a < sprD (Fin.last nR) p) (hD : 1 < gapD p)
    (v : SCoord nL (nR + 1)) :
    Ito.itoGen (critPhi κ xL xR ρL ρR a μ K) p v =
      sprD (Fin.last nR) p ^ μ * (-μ * farX κ xL xR ρL ρR 0 p ^ (-μ - 1) * (v.2.1 0 - driftLin₀ ρL ρR v) +
          1 / 2 * (-μ * ((-μ - 1) * farX κ xL xR ρL ρR 0 p ^ (-μ - 2))) * κ) +
        farX κ xL xR ρL ρR 0 p ^ (-μ) * (μ * sprD (Fin.last nR) p ^ (μ - 1) *
          (v.2.1 (Fin.last nR) - v.2.1 0)) +
      K * (sprD (Fin.last nR) p ^ μ * (-μ * gapD p ^ (-μ - 1) * (v.2.1 0 - v.1 0)) +
        gapD p ^ (-μ) * (μ * sprD (Fin.last nR) p ^ (μ - 1) * (v.2.1 (Fin.last nR) - v.2.1 0))) := by
  have hcS : ContDiffAt ℝ 2 (fun r => cutPow a μ (sprD (nL := nL) (Fin.last nR) r)) p :=
    ((contDiff_cutPow ha μ).comp (contDiff_sprD (nL := nL) (Fin.last nR))).contDiffAt.of_le (by norm_num)
  have hcR : ContDiffAt ℝ 2 (fun r => cutPow a (-μ) (farX κ xL xR ρL ρR 0 r)) p :=
    ((contDiff_cutPow ha (-μ)).comp (contDiff_farX κ xL xR ρL ρR 0)).contDiffAt.of_le (by norm_num)
  have hcD : ContDiffAt ℝ 2 (fun r => cutPow 1 (-μ) (gapD (nL := nL) (nR := nR) r)) p :=
    ((contDiff_cutPow one_pos (-μ)).comp (contDiff_gapD (nL := nL) (nR := nR))).contDiffAt.of_le
      (by norm_num)
  have hgS := itoGen_cutPow_of_partialSnd (q := μ) ha (contDiff_sprD (nL := nL) (Fin.last nR)) hΔ
    (partialSnd_sprD (Fin.last nR) p) v
  have hsS := partialSnd_cutPow_of_partialSnd (q := μ) ha (contDiff_sprD (nL := nL) (Fin.last nR)) hΔ
    (partialSnd_sprD (Fin.last nR) p)
  have hgD := itoGen_cutPow_of_partialSnd (q := -μ) one_pos (contDiff_gapD (nL := nL) (nR := nR)) hD
    (partialSnd_gapD p) v
  have hsD := partialSnd_cutPow_of_partialSnd (q := -μ) one_pos (contDiff_gapD (nL := nL) (nR := nR)) hD
    (partialSnd_gapD p)
  have hR0 : 0 < farX κ xL xR ρL ρR 0 p := ha.trans hR
  have hgR : Ito.itoGen (fun r => cutPow a (-μ) (farX κ xL xR ρL ρR 0 r)) p v =
      -μ * farX κ xL xR ρL ρR 0 p ^ (-μ - 1) * (v.2.1 0 - driftLin₀ ρL ρR v) +
        1 / 2 * (-μ * ((-μ - 1) * farX κ xL xR ρL ρR 0 p ^ (-μ - 2))) * κ := by
    rw [itoGen_comp_of_hasDerivAt ((contDiff_cutPow ha (-μ)).contDiffAt.of_le (by norm_num))
      ((contDiff_farX κ xL xR ρL ρR 0).contDiffAt) (eventually_hasDerivAt_cutPow ha (-μ) hR)
      (hasDerivAt_rpow_deriv (-μ) hR0), itoGen_farX, partialSnd_farX, neg_sq, Real.sq_sqrt hκ]
  have hsc : ∀ (c : ℝ) {F : SCoord nL (nR + 1) × ℝ → ℝ}, ContDiffAt ℝ 2 F p →
      Ito.itoGen (fun r => c * F r) p v = c * Ito.itoGen F p v := fun c F hF => by
    rw [itoGen_comp_of_hasDerivAt (φ := fun x => c * x) (φ' := fun _ => c) (d2 := 0)
      (contDiff_const.mul contDiff_id).contDiffAt hF
      (Eventually.of_forall fun x => by simpa using (hasDerivAt_id x).const_mul c) (hasDerivAt_const _ _)]
    ring
  have e : critPhi κ xL xR ρL ρR a μ K = fun r =>
      (fun r => cutPow a μ (sprD (Fin.last nR) r) * cutPow a (-μ) (farX κ xL xR ρL ρR 0 r)) r +
        (fun r => K * (cutPow a μ (sprD (Fin.last nR) r) * cutPow 1 (-μ) (gapD r))) r := rfl
  rw [e, Ito.itoGen_add (hcS.mul hcR) (contDiffAt_const.mul (hcS.mul hcD)), hsc K (hcS.mul hcD),
    Ito.itoGen_mul hcS hcR, Ito.itoGen_mul hcS hcD, hgS, hgR, hgD, hsS, hsD, itoGen_sprD, itoGen_gapD,
    (cutPow_eventuallyEq ha μ hΔ).self_of_nhds, (cutPow_eventuallyEq ha (-μ) hR).self_of_nhds,
    (cutPow_eventuallyEq one_pos (-μ) hD).self_of_nhds]
  ring

end Lyap

/-! ### The generator as an explicit expression -/

section Expr

/-- **The generator of `critPhi` in the variables** `R₀`, `Δ`, `D` and the drifts `gR` (of `R₀`), `gΔ` (of `Δ`),
`gD` (of `D`). -/
def critGenE (κ μ K R Δ D gR gΔ gD : ℝ) : ℝ :=
  Δ ^ μ * (-μ * R ^ (-μ - 1) * gR + 1 / 2 * (-μ * ((-μ - 1) * R ^ (-μ - 2))) * κ) +
      R ^ (-μ) * (μ * Δ ^ (μ - 1) * gΔ) +
    K * (Δ ^ μ * (-μ * D ^ (-μ - 1) * gD) + D ^ (-μ) * (μ * Δ ^ (μ - 1) * gΔ))

/-- **The factored form** with `gR = (2 + s)/R − r/L`, `gΔ = 2/(R + Δ) − 2/R`, `gD = 2/R + 2/L`, `D = R + L`. -/
theorem critGenE_eq {κ μ K R Δ L s r : ℝ} (hR : 0 < R) (hΔ : 0 < Δ) (hL : 0 < L) :
    critGenE κ μ K R Δ (R + L) ((2 + s) / R - r / L) (2 / (R + Δ) - 2 / R) (2 / R + 2 / L) =
      μ * (Δ / R) ^ μ / R ^ 2 * (-(2 + s) + r * R / L + (μ + 1) * κ / 2 - 2 * R / (R + Δ)) -
        2 * K * μ * (Δ / (R + L)) ^ μ * (1 / (R * L) + 1 / ((R + Δ) * R)) := by
  have hD : 0 < R + L := by linarith
  have hX : 0 < R + Δ := by linarith
  have e1 : R ^ (-μ - 1) = R ^ (-μ) / R := Real.rpow_sub_one hR.ne' _
  have e2 : R ^ (-μ - 2) = R ^ (-μ) / R ^ 2 := by
    rw [Real.rpow_sub hR, Real.rpow_two]
  have e3 : Δ ^ (μ - 1) = Δ ^ μ / Δ := Real.rpow_sub_one hΔ.ne' _
  have e4 : (R + L) ^ (-μ - 1) = (R + L) ^ (-μ) / (R + L) := Real.rpow_sub_one hD.ne' _
  have e5 : (Δ / R) ^ μ = Δ ^ μ * R ^ (-μ) := by
    rw [Real.div_rpow hΔ.le hR.le, Real.rpow_neg hR.le, div_eq_mul_inv]
  have e6 : (Δ / (R + L)) ^ μ = Δ ^ μ * (R + L) ^ (-μ) := by
    rw [Real.div_rpow hΔ.le hD.le, Real.rpow_neg hD.le, div_eq_mul_inv]
  rw [e5, e6]
  simp only [critGenE, e1, e2, e3, e4]
  have hRne := hR.ne'
  have hΔne := hΔ.ne'
  have hLne := hL.ne'
  have hDne := hD.ne'
  have hXne := hX.ne'
  field_simp
  ring

/-- `y ≤ y^μ` for `0 < y ≤ 1`, `0 < μ ≤ 1`. -/
theorem le_rpow_of_le_one {y μ : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) (hμ1 : μ ≤ 1) : y ≤ y ^ μ := by
  have := Real.rpow_le_rpow_of_exponent_ge hy hy1 hμ1
  rwa [Real.rpow_one] at this

/-- `1/R² − 1/(R + Δ)² ≤ 2 (Δ/R)/R²` for `R > 0`, `Δ ≥ 0`. -/
theorem inv_sq_sub_inv_sq_le' {R Δ : ℝ} (hR : 0 < R) (hΔ : 0 ≤ Δ) :
    1 / R ^ 2 - 1 / (R + Δ) ^ 2 ≤ 2 * (Δ / R) / R ^ 2 := by
  have hX : 0 < R + Δ := by linarith
  have key : 1 / R ^ 2 - 1 / (R + Δ) ^ 2 = Δ * (2 * R + Δ) / (R ^ 2 * (R + Δ) ^ 2) := by
    field_simp; ring
  rw [key, show 2 * (Δ / R) / R ^ 2 = 2 * Δ / R ^ 3 by field_simp,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : (2 * R + Δ) * R ≤ 2 * (R + Δ) ^ 2 := by nlinarith
  calc Δ * (2 * R + Δ) * R ^ 3 = Δ * R ^ 2 * ((2 * R + Δ) * R) := by ring
    _ ≤ Δ * R ^ 2 * (2 * (R + Δ) ^ 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = 2 * Δ * (R ^ 2 * (R + Δ) ^ 2) := by ring

/-- **The pointwise generator bound** (every `s ≥ κ/2 − 2`, every `r`): for `R, L, Δ > 0` with `Δ ≤ R`, `0 < μ ≤ 1`,
`κ μ ≤ 1/2` and `K ≥ 2|r|(1 + 4|r|)`, the generator of `critPhi` is at most `−(μ/4) (1/R² − 1/(R + Δ)²)`. -/
theorem critGenE_le {κ μ K R Δ L s r : ℝ} (hR : 0 < R) (hΔ : 0 < Δ) (hL : 0 < L) (hΔR : Δ ≤ R)
    (hs : κ / 2 - 2 ≤ s) (hμ : 0 < μ) (hμ1 : μ ≤ 1) (hκμ : κ * μ ≤ 1 / 2) (hK : 2 * |r| * (1 + 4 * |r|) ≤ K) :
    critGenE κ μ K R Δ (R + L) ((2 + s) / R - r / L) (2 / (R + Δ) - 2 / R) (2 / R + 2 / L) ≤
      -(μ / 4 * (1 / R ^ 2 - 1 / (R + Δ) ^ 2)) := by
  rw [critGenE_eq hR hΔ hL]
  have hD : 0 < R + L := by linarith
  have hX : 0 < R + Δ := by linarith
  set y := Δ / R with hy
  have hy0 : 0 < y := div_pos hΔ hR
  have hy1 : y ≤ 1 := (div_le_one hR).2 hΔR
  set A := y ^ μ with hA
  set Bq := (Δ / (R + L)) ^ μ with hBq
  have hA0 : 0 ≤ A := Real.rpow_nonneg hy0.le _
  have hBq0 : 0 ≤ Bq := Real.rpow_nonneg (div_pos hΔ hD).le _
  have hyA : y ≤ A := le_rpow_of_le_one hy0 hy1 hμ1
  have hosc := inv_sq_sub_inv_sq_le' hR hΔ.le
  rw [← hy] at hosc
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  -- the bracket without the left term
  have hRX : 2 * R / (R + Δ) ≥ 1 := by rw [ge_iff_le, le_div_iff₀ hX]; linarith
  have hpos2 : 0 ≤ 2 * K * μ * Bq * (1 / (R * L) + 1 / ((R + Δ) * R)) := by positivity
  by_cases hgood : r * R / L ≤ 1 / 4
  · -- the left term is small
    have hbr : -(2 + s) + r * R / L + (μ + 1) * κ / 2 - 2 * R / (R + Δ) ≤ -(1 / 2) := by nlinarith
    have h1 : μ * A / R ^ 2 * (-(2 + s) + r * R / L + (μ + 1) * κ / 2 - 2 * R / (R + Δ)) ≤
        μ * A / R ^ 2 * (-(1 / 2)) := mul_le_mul_of_nonneg_left hbr (by positivity)
    have h2 : μ / 4 * (1 / R ^ 2 - 1 / (R + Δ) ^ 2) ≤ μ * A / R ^ 2 * (1 / 2) := by
      have : 1 / R ^ 2 - 1 / (R + Δ) ^ 2 ≤ 2 * A / R ^ 2 := hosc.trans (by gcongr)
      calc μ / 4 * (1 / R ^ 2 - 1 / (R + Δ) ^ 2) ≤ μ / 4 * (2 * A / R ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = μ * A / R ^ 2 * (1 / 2) := by ring
    linarith
  · -- the left mark is near: `R ≥ D/(1 + 4r)`, absorbed by the `D` term
    push Not at hgood
    have hr : 0 < r := by
      by_contra h
      push Not at h
      have : r * R / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h hR.le) hL.le
      linarith
    rw [abs_of_pos hr] at hK
    have hLR : L < 4 * r * R := by
      rw [lt_div_iff₀ hL] at hgood; linarith
    set I := 1 / (R * L) with hI
    set iR := 1 / R ^ 2 with hiR
    have hI0 : 0 ≤ I := by positivity
    have hiR0 : 0 ≤ iR := by positivity
    have hRR : iR ≤ 4 * r * I := by
      simp only [hiR, hI]
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith
    have hrI : iR * (r * R / L) = r * I := by simp only [hiR, hI]; field_simp
    have hDR : (R + L) / R ≤ 1 + 4 * r := by rw [div_le_iff₀ hR]; linarith
    have hAB : A ≤ (1 + 4 * r) * Bq := by
      have e : A = Bq * ((R + L) / R) ^ μ := by
        rw [hA, hBq, hy, ← Real.mul_rpow (div_pos hΔ hD).le (div_pos hD hR).le]
        congr 1; field_simp
      have h1 : 1 ≤ (R + L) / R := by rw [le_div_iff₀ hR]; linarith
      have h2 : ((R + L) / R) ^ μ ≤ (R + L) / R := by
        have := Real.rpow_le_rpow_of_exponent_le h1 hμ1
        rwa [Real.rpow_one] at this
      rw [e]
      calc Bq * ((R + L) / R) ^ μ ≤ Bq * (1 + 4 * r) := mul_le_mul_of_nonneg_left (h2.trans hDR) hBq0
        _ = (1 + 4 * r) * Bq := by ring
    have hbr : -(2 + s) + r * R / L + (μ + 1) * κ / 2 - 2 * R / (R + Δ) ≤ 1 / 4 + r * R / L := by nlinarith
    have hμA : 0 ≤ μ * A := mul_nonneg hμ.le hA0
    -- the first term
    have h1 : μ * A / R ^ 2 * (-(2 + s) + r * R / L + (μ + 1) * κ / 2 - 2 * R / (R + Δ)) ≤
        2 * μ * A * r * I := by
      have e : μ * A / R ^ 2 = μ * A * iR := by simp only [hiR]; ring
      rw [e]
      calc μ * A * iR * (-(2 + s) + r * R / L + (μ + 1) * κ / 2 - 2 * R / (R + Δ))
          ≤ μ * A * iR * (1 / 4 + r * R / L) := mul_le_mul_of_nonneg_left hbr (mul_nonneg hμA hiR0)
        _ = μ * A * (iR / 4 + iR * (r * R / L)) := by ring
        _ = μ * A * (iR / 4 + r * I) := by rw [hrI]
        _ ≤ μ * A * (r * I + r * I) := mul_le_mul_of_nonneg_left (by linarith) hμA
        _ = 2 * μ * A * r * I := by ring
    -- the oscillation
    have h2 : μ / 4 * (1 / R ^ 2 - 1 / (R + Δ) ^ 2) ≤ 2 * μ * A * r * I := by
      have ho : 1 / R ^ 2 - 1 / (R + Δ) ^ 2 ≤ 2 * A * iR := by
        calc 1 / R ^ 2 - 1 / (R + Δ) ^ 2 ≤ 2 * y / R ^ 2 := hosc
          _ = 2 * y * iR := by simp only [hiR]; ring
          _ ≤ 2 * A * iR := mul_le_mul_of_nonneg_right (by linarith) hiR0
      calc μ / 4 * (1 / R ^ 2 - 1 / (R + Δ) ^ 2) ≤ μ / 4 * (2 * A * iR) :=
            mul_le_mul_of_nonneg_left ho (by positivity)
        _ = μ * A / 2 * iR := by ring
        _ ≤ μ * A / 2 * (4 * r * I) := mul_le_mul_of_nonneg_left hRR (by positivity)
        _ = 2 * μ * A * r * I := by ring
    -- the `D` term
    have h3 : 4 * μ * A * r * I ≤ 2 * K * μ * Bq * (1 / (R * L) + 1 / ((R + Δ) * R)) := by
      have hJ : (0 : ℝ) ≤ 1 / ((R + Δ) * R) := by positivity
      have hrI0 : 0 ≤ r * I := mul_nonneg hr.le hI0
      calc 4 * μ * A * r * I = 4 * μ * (r * I) * A := by ring
        _ ≤ 4 * μ * (r * I) * ((1 + 4 * r) * Bq) := mul_le_mul_of_nonneg_left hAB (by positivity)
        _ = 2 * (2 * r * (1 + 4 * r)) * μ * Bq * I := by ring
        _ ≤ 2 * K * μ * Bq * I := by
            have h0 : 0 ≤ μ * Bq * I := by positivity
            have := mul_le_mul_of_nonneg_right hK h0
            linarith
        _ ≤ 2 * K * μ * Bq * (1 / (R * L) + 1 / ((R + Δ) * R)) := by
            rw [← hI]
            exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith

end Expr

/-! ### Along the path -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The generator of `critPhi` along the path**, at real time `s`. -/
def critGen (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (μ K : ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  critGenE κ μ K (vR 0 s.toNNReal - w s.toNNReal) (vR (Fin.last nR) s.toNNReal - vR 0 s.toNNReal)
    (vR 0 s.toNNReal - vL 0 s.toNNReal) (driftX ρL ρR 0 w vL vR s.toNNReal)
    (2 / (vR (Fin.last nR) s.toNNReal - w s.toNNReal) - 2 / (vR 0 s.toNNReal - w s.toNNReal))
    (2 / (vR 0 s.toNNReal - w s.toNNReal) - 2 / (vL 0 s.toNNReal - w s.toNNReal))

/-- **The generator of `critPhi` along the path** (with the force-point velocities), where `R₀`, `Δ` exceed the
cutoff level and `D > 1`. -/
theorem itoGen_critPhi_pathCoord (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 ≤ κ) {a : ℝ}
    (ha : 0 < a) (μ K I c : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hR : a < vR 0 t - w t)
    (hΔ : a < vR (Fin.last nR) t - vR 0 t) (hD : 1 < vR 0 t - vL 0 t) :
    Ito.itoGen (critPhi κ xL xR ρL ρR a μ K) (pathCoord vL vR b I t)
        (angDens (w t) (fun i => vL i t) (fun j => vR j t) c) =
      critGen κ ρL ρR μ K w vL vR t := by
  have hR' : a < farX κ xL xR ρL ρR 0 (pathCoord vL vR b I t) := by
    rw [farX_pathCoord hp 0 I ht]; exact hR
  have hΔ' : a < sprD (Fin.last nR) (pathCoord vL vR b I t) := hΔ
  have hD' : 1 < gapD (pathCoord vL vR b I t) := hD
  rw [itoGen_critPhi κ xL xR ρL ρR hκ ha μ K hR' hΔ' hD', farX_pathCoord hp 0 I ht, sprD_pathCoord,
    driftLin₀_angDens]
  simp only [critGen, critGenE, driftX, angDens, Real.toNNReal_coe, gapD, pathCoord]

/-- `critPhi` along the path, where `R₀`, `Δ` exceed the cutoff level and `D > 1`. -/
theorem critPhi_pathCoord (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {a : ℝ} (ha : 0 < a)
    (μ K I : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hR : a < vR 0 t - w t)
    (hΔ : a < vR (Fin.last nR) t - vR 0 t) (hD : 1 < vR 0 t - vL 0 t) :
    critPhi κ xL xR ρL ρR a μ K (pathCoord vL vR b I t) =
      ((vR (Fin.last nR) t - vR 0 t) / (vR 0 t - w t)) ^ μ +
        K * ((vR (Fin.last nR) t - vR 0 t) / (vR 0 t - vL 0 t)) ^ μ := by
  have hR' : a < farX κ xL xR ρL ρR 0 (pathCoord vL vR b I t) := by
    rw [farX_pathCoord hp 0 I ht]; exact hR
  have hR0 : 0 < vR 0 t - w t := ha.trans hR
  have hΔ0 : 0 < vR (Fin.last nR) t - vR 0 t := ha.trans hΔ
  have hD0 : 0 < vR 0 t - vL 0 t := one_pos.trans hD
  have e1 : sprD (Fin.last nR) (pathCoord vL vR b I t) = vR (Fin.last nR) t - vR 0 t := rfl
  have e2 : gapD (pathCoord vL vR b I t) = vR 0 t - vL 0 t := rfl
  simp only [critPhi]
  rw [e1, e2, farX_pathCoord hp 0 I ht, cutPow_eq ha hΔ, cutPow_eq ha hR, cutPow_eq one_pos hD]
  rw [Real.div_rpow hΔ0.le hR0.le, Real.div_rpow hΔ0.le hD0.le, Real.rpow_neg hR0.le, Real.rpow_neg hD0.le]
  ring

/-- `critPhi` along the path is at most its uncut value (where `R₀ > 0`, `Δ ≥ 0`, `D > 0`). -/
theorem critPhi_pathCoord_le (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) {a : ℝ} (ha : 0 < a)
    (μ : ℝ) {K : ℝ} (hK : 0 ≤ K) (I : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) (hR : 0 < vR 0 t - w t)
    (hΔ : 0 ≤ vR (Fin.last nR) t - vR 0 t) (hD : 0 < vR 0 t - vL 0 t) :
    critPhi κ xL xR ρL ρR a μ K (pathCoord vL vR b I t) ≤
      ((vR (Fin.last nR) t - vR 0 t) / (vR 0 t - w t)) ^ μ +
        K * ((vR (Fin.last nR) t - vR 0 t) / (vR 0 t - vL 0 t)) ^ μ := by
  have e1 : sprD (Fin.last nR) (pathCoord vL vR b I t) = vR (Fin.last nR) t - vR 0 t := rfl
  have e2 : gapD (pathCoord vL vR b I t) = vR 0 t - vL 0 t := rfl
  simp only [critPhi]
  rw [e1, e2, farX_pathCoord hp 0 I ht]
  set Δ := vR (Fin.last nR) t - vR 0 t
  set R := vR 0 t - w t
  set D := vR 0 t - vL 0 t
  have h1 := cutPow_le (a := a) (p := μ) hΔ
  have h2 := cutPow_le (a := a) (p := -μ) hR.le
  have h3 := cutPow_le (a := 1) (p := -μ) hD.le
  have h1' := cutPow_nonneg ha μ Δ
  have h2' := cutPow_nonneg ha (-μ) R
  have h3' := cutPow_nonneg one_pos (-μ) D
  rw [Real.div_rpow hΔ hR.le, Real.div_rpow hΔ hD.le, div_eq_mul_inv, div_eq_mul_inv, ← Real.rpow_neg hR.le,
    ← Real.rpow_neg hD.le]
  have hΔμ := Real.rpow_nonneg hΔ μ
  have e1 : cutPow a μ Δ * cutPow a (-μ) R ≤ Δ ^ μ * R ^ (-μ) :=
    mul_le_mul h1 h2 h2' hΔμ
  have e2 : cutPow a μ Δ * cutPow 1 (-μ) D ≤ Δ ^ μ * D ^ (-μ) :=
    mul_le_mul h1 h3 h3' hΔμ
  have := mul_le_mul_of_nonneg_left e2 hK
  linarith

end Path

end TrialsHi4

end Sec7

end InteractingSLE

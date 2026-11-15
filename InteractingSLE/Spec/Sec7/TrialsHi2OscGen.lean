/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TrialsHi2Lyap
import InteractingSLE.Spec.Sec7.ContinuityProb7Clock

/-!
# The generator of the side-oscillation Lyapunov function along the evolution

Packet PROVE-TRIALS-HI2. In the coordinates of the localized Itô formula (`Clock.angU`, `Clock.gapD`), the function
`Φ = D^{−θ} H(U)` (`oscΦ`, `H = oscH`) is smooth on `{D > 0}`. Its Itô generator is
`D^{−θ} itoGen(H ∘ U) − θ D^{−θ−1} (v^{R,0} − v^{L,0}) H(U)` (`itoGen_oscΦ`: the product rule, `D` has no Brownian
part), so along a path it is `oscGen` (`itoGen_oscΦ_pathCoord`). For a word whose only nonzero weights are at the
nearest marks (no finite-variation error), at a non-collision time `oscGen = D^{−θ−2} J(U)` with the Lyapunov bracket
`J` of `TrialsHi2Lyap`, hence `oscGen ≤ −c₀ D^{−θ−2} ((1 − U)² + ε²)^{−θ/2−1}` (`oscGen_le`).

## Main results

* `itoGen_gapPow`, `partialSnd_gapPow`, `oscΦ`, `contDiffOn_oscΦ`, `itoGen_oscΦ`;
* `oscGen`, `itoGen_oscΦ_pathCoord`, `angErr_eq_zero`, **`oscGen_le`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace TrialsHi2

open Zhan Clock

variable {nL nR : ℕ}

/-! ### The power of the cross-gap -/

section GapPow

theorem gapD_line (p : SCoord nL (nR + 1) × ℝ) (v : SCoord nL (nR + 1)) (t : ℝ) :
    gapD ((p.1 + t • v, p.2) : SCoord nL (nR + 1) × ℝ) = gapD p + t * (v.2.1 0 - v.1 0) := by
  simp only [gapD, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

theorem contDiffAt_gapPow {θ : ℝ} {n : WithTop ℕ∞} {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) :
    ContDiffAt ℝ n (fun q : SCoord nL (nR + 1) × ℝ => gapD q ^ (-θ)) p :=
  contDiff_gapD.contDiffAt.rpow_const_of_ne hp.ne'

theorem partialSnd_gapPow {θ : ℝ} {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) :
    Ito.partialSnd (fun q : SCoord nL (nR + 1) × ℝ => gapD q ^ (-θ)) p = 0 := by
  refine Ito.partialSnd_eq_of_hasDerivAt ((contDiffAt_gapPow (n := 1) hp).differentiableAt (by norm_num)) ?_
  have e : (fun y : ℝ => gapD ((p.1, y) : SCoord nL (nR + 1) × ℝ) ^ (-θ)) = fun _ => gapD p ^ (-θ) := rfl
  rw [e]
  exact hasDerivAt_const _ _

/-- **The generator of `D^{−θ}`**: `−θ D^{−θ−1} (v^{R,0} − v^{L,0})`. -/
theorem itoGen_gapPow {θ : ℝ} {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (fun q : SCoord nL (nR + 1) × ℝ => gapD q ^ (-θ)) p v =
      -θ * gapD p ^ (-θ - 1) * (v.2.1 0 - v.1 0) := by
  have hF : Ito.partialFst (fun q : SCoord nL (nR + 1) × ℝ => gapD q ^ (-θ)) p v =
      -θ * gapD p ^ (-θ - 1) * (v.2.1 0 - v.1 0) := by
    refine Ito.partialFst_eq_of_hasDerivAt ((contDiffAt_gapPow (n := 1) hp).differentiableAt (by norm_num)) ?_
    have hline : (fun t : ℝ => gapD ((p.1 + t • v, p.2) : SCoord nL (nR + 1) × ℝ) ^ (-θ)) =
        fun t => (gapD p + t * (v.2.1 0 - v.1 0)) ^ (-θ) := by
      funext t; rw [gapD_line]
    rw [hline]
    have h1 : HasDerivAt (fun t : ℝ => gapD p + t * (v.2.1 0 - v.1 0)) (1 * (v.2.1 0 - v.1 0)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).mul_const _).const_add _
    have h2 := h1.rpow_const (p := -θ) (Or.inl (by simp only [zero_mul, add_zero]; exact hp.ne'))
    refine h2.congr_deriv ?_
    simp only [zero_mul, add_zero]
    ring
  have hSS : Ito.partialSndSnd (fun q : SCoord nL (nR + 1) × ℝ => gapD q ^ (-θ)) p = 0 := by
    refine Ito.partialSndSnd_eq_of_hasDerivAt (contDiffAt_gapPow hp) (g := fun _ => 0) ?_ (hasDerivAt_const _ _)
    refine Eventually.of_forall fun y => ?_
    have hp' : 0 < gapD ((p.1, y) : SCoord nL (nR + 1) × ℝ) := hp
    exact partialSnd_gapPow hp'
  rw [Ito.itoGen, hF, hSS]
  ring

end GapPow

/-! ### The Lyapunov function in coordinates -/

section Phi

variable (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)

/-- **The side-oscillation Lyapunov function** `Φ = D^{−θ} (ψ_ε(1 − U) + λ)` of coordinates. -/
def oscΦ (θ ε lam : ℝ) (p : SCoord nL (nR + 1) × ℝ) : ℝ :=
  gapD p ^ (-θ) * oscH θ ε lam (angU κ xL xR ρL ρR p)

variable {κ xL xR ρL ρR}

theorem contDiffOn_oscΦ {θ ε : ℝ} (hε : 0 < ε) (lam : ℝ) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (oscΦ κ xL xR ρL ρR θ ε lam) angRegion :=
  (contDiff_gapD.contDiffOn.rpow_const_of_ne fun _ hp => (ne_of_gt hp)).mul
    (contDiffOn_comp_angU κ xL xR ρL ρR (contDiff_oscH hε lam))

theorem oscΦ_nonneg {θ ε lam : ℝ} (hlam : 0 ≤ lam) {p : SCoord nL (nR + 1) × ℝ} (hp : 0 < gapD p) :
    0 ≤ oscΦ κ xL xR ρL ρR θ ε lam p :=
  mul_nonneg (Real.rpow_nonneg hp.le _) (oscH_nonneg hlam _)

/-- **The generator of `Φ`** (product rule; `D` has no Brownian part). -/
theorem itoGen_oscΦ {θ ε : ℝ} (hε : 0 < ε) (lam : ℝ) {p : SCoord nL (nR + 1) × ℝ}
    (hp : 0 < gapD p) (v : SCoord nL (nR + 1)) :
    Ito.itoGen (oscΦ κ xL xR ρL ρR θ ε lam) p v =
      gapD p ^ (-θ) * Ito.itoGen (fun q => oscH θ ε lam (angU κ xL xR ρL ρR q)) p v +
        oscH θ ε lam (angU κ xL xR ρL ρR p) * (-θ * gapD p ^ (-θ - 1) * (v.2.1 0 - v.1 0)) := by
  have h2 : ContDiffAt ℝ 2 (fun q => oscH θ ε lam (angU κ xL xR ρL ρR q)) p :=
    (contDiff_oscH hε lam).contDiffAt.comp p (contDiffAt_angU κ xL xR ρL ρR hp)
  have h := Ito.itoGen_mul (contDiffAt_gapPow (θ := θ) (n := 2) hp) h2 v
  rw [partialSnd_gapPow hp, zero_mul, add_zero, itoGen_gapPow hp v] at h
  exact h

end Phi

/-! ### Along one path -/

section Path

variable {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The generator of `Φ` along the path**, at real time `s`. -/
def oscGen (κ : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (θ ε lam : ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin (nL + 1) → ℝ≥0 → ℝ) (vR : Fin (nR + 1) → ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  gapAt vL vR s.toNNReal ^ (-θ) * genExpr κ ρL ρR (oscH' θ ε) (oscH'' θ ε) w vL vR s +
    oscH θ ε lam (angAt w vL vR s.toNNReal) * (-θ * gapAt vL vR s.toNNReal ^ (-θ - 1) *
      (2 / (vR 0 s.toNNReal - w s.toNNReal) - 2 / (vL 0 s.toNNReal - w s.toNNReal)))

theorem itoGen_oscΦ_pathCoord (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hκ : 0 ≤ κ)
    (hx : 0 < xR 0 - xL 0) {θ ε : ℝ} (hε : 0 < ε) (lam I c : ℝ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    Ito.itoGen (oscΦ κ xL xR ρL ρR θ ε lam) (pathCoord vL vR b I t)
        (angDens (w t) (fun i => vL i t) (fun j => vR j t) c) =
      oscGen κ ρL ρR θ ε lam w vL vR t := by
  have hD : 0 < gapD (pathCoord vL vR b I t) := hx.trans_le (le_gapAt hp ht)
  rw [itoGen_oscΦ hε lam hD, itoGen_pathCoord_eq hp hκ hx (contDiff_oscH hε lam) (hasDerivAt_oscH hε lam)
    (hasDerivAt_oscH' hε) I c ht, angU_pathCoord hp I ht]
  simp only [oscGen, Real.toNNReal_coe, angDens]
  rfl

theorem angErr_eq_zero (hρL : ∀ i, i ≠ 0 → ρL i = 0) (hρR : ∀ j, j ≠ 0 → ρR j = 0) (wt : ℝ)
    (vLt : Fin (nL + 1) → ℝ) (vRt : Fin (nR + 1) → ℝ) : angErr ρL ρR wt vLt vRt = 0 := by
  unfold angErr
  have h1 : ∑ i, ρL i * ((wt - vLt i)⁻¹ - (wt - vLt 0)⁻¹) = 0 := Finset.sum_eq_zero fun i _ => by
    by_cases hi : i = 0
    · subst hi; ring
    · rw [hρL i hi, zero_mul]
  have h2 : ∑ j, ρR j * ((vRt j - wt)⁻¹ - (vRt 0 - wt)⁻¹) = 0 := Finset.sum_eq_zero fun j _ => by
    by_cases hj : j = 0
    · subst hj; ring
    · rw [hρR j hj, zero_mul]
  rw [h1, h2, sub_zero]

/-- **The generator bound at a non-collision time** for a word whose only nonzero weights are at the nearest marks:
`oscGen ≤ −c₀ D^{−θ}/D² ((1 − U)² + ε²)^{−θ/2−1}`. -/
theorem oscGen_le (hρL : ∀ i, i ≠ 0 → ρL i = 0)
    (hρR : ∀ j, j ≠ 0 → ρR j = 0) {θ ε lam c₀ : ℝ}
    (hJ : ∀ u ∈ Ioo (0 : ℝ) 1, oscJ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) θ ε lam u ≤
      -c₀ * ((1 - u) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1))
    {s : ℝ} (hL0 : vL 0 s.toNNReal < w s.toNNReal) (hR0 : w s.toNNReal < vR 0 s.toNNReal) :
    oscGen κ ρL ρR θ ε lam w vL vR s ≤
      -c₀ * (gapAt vL vR s.toNNReal ^ (-θ) / gapAt vL vR s.toNNReal ^ 2 *
        ((1 - angAt w vL vR s.toNNReal) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) := by
  have hD : 0 < gapAt vL vR s.toNNReal := sub_pos.2 (hL0.trans hR0)
  have hU : angAt w vL vR s.toNNReal ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (sub_pos.2 hL0) hD, (div_lt_one hD).2 ?_⟩
    simp only [gapAt]; linarith
  have hnum : numAt ρL ρR w vL vR s.toNNReal / gapAt vL vR s.toNNReal =
      angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) (angAt w vL vR s.toNNReal) / gapAt vL vR s.toNNReal ^ 2 := by
    have h := drift_angU_eq ρL ρR (w := w s.toNNReal) (vL := fun i => vL i s.toNNReal)
      (vR := fun j => vR j s.toNNReal) hL0 hR0 0
    rw [driftLin₀_angDens, angErr_eq_zero hρL hρR, zero_div, add_zero] at h
    simpa only [numAt, angAt, gapAt, angDens] using h
  set U := angAt w vL vR s.toNNReal with hUdef
  set D := gapAt vL vR s.toNNReal with hDdef
  have hDne : D ≠ 0 := hD.ne'
  have hU0 : U ≠ 0 := hU.1.ne'
  have hU1 : 1 - U ≠ 0 := by linarith [hU.2]
  have hDv : D = vR 0 s.toNNReal - vL 0 s.toNNReal := rfl
  have hL : w s.toNNReal - vL 0 s.toNNReal = D * U := by
    rw [hUdef, angAt, ← hDdef]; field_simp
  have hLR : 2 / (vR 0 s.toNNReal - w s.toNNReal) - 2 / (vL 0 s.toNNReal - w s.toNNReal) =
      2 / (D * (U * (1 - U))) := by
    have hR : vR 0 s.toNNReal - w s.toNNReal = D * (1 - U) := by
      rw [show D * (1 - U) = D - D * U by ring, ← hL, hDv]; ring
    have hL' : vL 0 s.toNNReal - w s.toNNReal = -(D * U) := by linarith
    rw [hR, hL']
    field_simp
    ring
  have hpow : D ^ (-θ - 1) = D ^ (-θ) / D := Real.rpow_sub_one hDne (-θ)
  have hgen : oscGen κ ρL ρR θ ε lam w vL vR s =
      D ^ (-θ) / D ^ 2 * oscJ κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) θ ε lam U := by
    simp only [oscGen, genExpr, ← hUdef, ← hDdef]
    rw [hnum, hLR, hpow]
    simp only [oscJ]
    field_simp
    ring
  rw [hgen]
  have hc : 0 ≤ D ^ (-θ) / D ^ 2 := div_nonneg (Real.rpow_nonneg hD.le _) (by positivity)
  have := mul_le_mul_of_nonneg_left (hJ U hU) hc
  linarith [show D ^ (-θ) / D ^ 2 * (-c₀ * ((1 - U) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) =
    -c₀ * (D ^ (-θ) / D ^ 2 * ((1 - U) ^ 2 + ε ^ 2) ^ (-θ / 2 - 1)) by ring]

end Path

end TrialsHi2

end Sec7

end InteractingSLE

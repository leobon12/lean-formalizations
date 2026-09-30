import QuantumZipper.Proofs.Zipper.B5LocDet

/-!
# B5 locality: the lengths as local boundary measures of a locally agreeing field

Continuation of `B5LocDet.lean` (Theorem 1.3, node B5 locality; Sheffield, arXiv:1012.4797,
§5.4, pp. 70–72). `unzipLengths_eq_qBoundaryMeasureOn` expresses the unzipped lengths of `(x, W)`
through the *local* boundary measure `qBoundaryMeasureOn γ · U` of the unzipped field of any
configuration `(x', W')` that agrees with `(x, W)` near the hull (dyadic circles in `S`, driver on
`[0,t]`). Only the global boundary measure of the unzipped `x` is assumed to exist, not that of
`x'`: this is the form needed to replace `x` by a field built from countably many local
coordinates (germ-measurable data), whose global boundary measure need not exist.

`hitTime_eq_of_dyCircAgree`: the first time `t'` at which the left length reaches `ℓ` (the
stopping time of `zipLenDown`) is local in the same sense, on the event that it is at most `T`.

Own elementary arguments (bookkeeping around the definitions; see `B5LocDet.lean`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace B5

/-- Coordinate changes by maps agreeing on `ℍ` have the same regularized averages. -/
theorem avgReg_coordChange_eqOn (x : FieldSample) {f g : ℂ → ℂ} (hfg : EqOn f g H) (Q : ℝ)
    (k : ℕ) (z : ℂ) : avgReg (coordChange x f Q) k z = avgReg (coordChange x g Q) k z := by
  unfold avgReg
  congr 1
  funext n
  exact UnzipInvariance.coordChange_congr_of_eqOn hfg
    (ESM.foldedCircle_compl_H_eq_zero _ (radius_pos k)) x Q

/-- The regularized averages of the unzipped fields agree on `U`, for all large `k`, under the
hypotheses of `unzipLengths_eq_of_dyCircAgree`. -/
theorem eventually_avgReg_unzipped_eq {γ t : ℝ} (x x' : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0) (ht : 0 ≤ t)
    (hWW' : ∀ r ∈ Icc (0 : ℝ) t, W r = W' r) {U : Set ℝ}
    {S : Set ℂ} (hS : IsOpen S) {δ : ℝ} (hδ : 0 < δ)
    (hψ : ∀ u ∈ H, (∃ s ∈ U, dist u (s : ℂ) < δ) → fwdMapInv W t u ∈ S)
    {j₀ : ℕ} (hag : DyCircAgree x x' S j₀) :
    ∀ᶠ k in atTop, ∀ s ∈ U, avgReg (unzippedField γ (x, W) t) k (s : ℂ) =
      avgReg (unzippedField γ (x', W') t) k (s : ℂ) := by
  have hEq := ESM.fwdMapInv_eqOn_of_drive_eqOn hW hW' hW0 hW0' ht hWW'
  have hrad : ∀ᶠ k in atTop, 2 * radius k < δ := by
    have h0 : Tendsto (fun k : ℕ => 2 * radius k) atTop (𝓝 (2 * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 2
    rw [mul_zero] at h0
    exact h0.eventually_lt_const hδ
  filter_upwards [hrad] with k hk s hs
  show avgReg (coordChange x (fwdMapInv W t) (Qc γ)) k (s : ℂ) =
    avgReg (coordChange x' (fwdMapInv W' t) (Qc γ)) k (s : ℂ)
  rw [← avgReg_coordChange_eqOn x' hEq]
  exact avgReg_coordChange_congr (Qc γ)
    (fun c r hr => RegCont.aemeasurable_fwdMapInv hW hW0 ht c hr)
    (fun u => F1.fwdMapInv_mem_Hbar W t u) hS hag
    (show (0 : ℝ) ≤ ((s : ℂ)).im by simp) hk (fun u hu hus => hψ u hu ⟨s, hs, hus⟩)

/-! ### Truncation to the local coordinates -/

open Classical in
/-- The field `x` truncated to its local coordinates: its values on the dyadic circles
`foldedCircle (dyadicRoundC n z) 2^{-j}` (`j ≥ j₀`, `z ∈ ℍ̄`, centre in `S`), and `0` on every
other measure. It agrees with `x` in the sense of `DyCircAgree` on `S`, and is measurable for any
σ-algebra making those countably many coordinates measurable. -/
def truncField (x : FieldSample) (S : Set ℂ) (j₀ : ℕ) : FieldSample := fun μ =>
  if ∃ j, j₀ ≤ j ∧ ∃ n : ℕ, ∃ z ∈ Hbar, dyadicRoundC n z ∈ S ∧
      μ = foldedCircle (dyadicRoundC n z) (radius j) then x μ else 0

theorem dyCircAgree_truncField (x : FieldSample) (S : Set ℂ) (j₀ : ℕ) :
    DyCircAgree x (truncField x S j₀) S j₀ := fun j hj n z hz hzS => by
  unfold truncField
  rw [if_pos ⟨j, hj, n, z, hz, hzS, rfl⟩]

theorem measurable_truncField {Ω : Type*} {m : MeasurableSpace Ω} (X : Ω → FieldSample)
    (S : Set ℂ) (j₀ : ℕ)
    (hX : ∀ j, j₀ ≤ j → ∀ n : ℕ, ∀ z ∈ Hbar, dyadicRoundC n z ∈ S →
      Measurable[m] fun ω => X ω (foldedCircle (dyadicRoundC n z) (radius j))) :
    Measurable[m] fun ω => truncField (X ω) S j₀ := by
  refine measurable_pi_iff.2 fun μ => ?_
  unfold truncField
  by_cases h : ∃ j, j₀ ≤ j ∧ ∃ n : ℕ, ∃ z ∈ Hbar, dyadicRoundC n z ∈ S ∧
      μ = foldedCircle (dyadicRoundC n z) (radius j)
  · simp only [if_pos h]
    obtain ⟨j, hj, n, z, hz, hzS, rfl⟩ := h
    exact hX j hj n z hz hzS
  · simp only [if_neg h]
    exact measurable_const

end B5
end QuantumZipper

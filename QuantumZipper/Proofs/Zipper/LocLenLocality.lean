import QuantumZipper.Proofs.Zipper.LocLenBridge
import QuantumZipper.Proofs.Zipper.B5LocOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), node B4: locality of the open-arc lengths

Berestycki–Powell, arXiv:2404.16642, proof of Lemma 8.27, p. 294: the quantum lengths of the
curve pieces are determined by the field and the curve near those pieces ("this is clear since
these pairs are obtained … by zipping down 1 unit of right quantum boundary length"); Sheffield
arXiv:1012.4797 §5.4 p. 70 uses the same locality. With the open-arc reading this is immediate:
`arcLen` only reads the dyadic approximations on the arc, so two fields whose regularized
averages agree on the arc (for small radii) have the same open-arc lengths. No global boundary
limit is assumed (compare the old `B5.unzipLengths_eq_qBoundaryMeasureOn`, B5LocOn.lean:66, which
needs the global limit of the unzipped field).

* `qBoundaryMeasureOn_congr_of_eventually_avgReg`, `arcLen_congr_of_eventually_avgReg`;
* **B4** `unzipLengthsArc_eq_of_dyCircAgree`: configurations agreeing near the hull (dyadic
  circles in `S`, driver on `[0,t]`) have equal open-arc lengths at time `t`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace LocLen

/-- The chosen local boundary measure on an open `V` only reads the dyadic averages on `V`, for
small radii. -/
theorem qBoundaryMeasureOn_congr_of_eventually_avgReg {γ : ℝ} {x y : FieldSample} {V : Set ℝ}
    (hV : IsOpen V) (h : ∀ᶠ k in atTop, ∀ s ∈ V, avgReg x k (s : ℂ) = avgReg y k (s : ℂ)) :
    qBoundaryMeasureOn γ x V = qBoundaryMeasureOn γ y V := by
  have key : ∀ {x y : FieldSample},
      (∀ᶠ k in atTop, ∀ s ∈ V, avgReg x k (s : ℂ) = avgReg y k (s : ℂ)) →
      ∀ ν, IsVagueLimitOnR V (bdryApprox γ x) ν → IsVagueLimitOnR V (bdryApprox γ y) ν := by
    intro x y h ν hν
    refine ⟨hν.1, hν.2.1, fun f hf hfc hfV => (hν.2.2 f hf hfc hfV).congr' ?_⟩
    filter_upwards [h] with k hk
    exact PalmNorm.integral_eq_of_restrict_eq'
      (PalmNorm.bdryApprox_restrict_eq hV.measurableSet hk)
      (fun s hs => image_eq_zero_of_notMem_tsupport fun h' => hs (hfV h'))
  have h' : ∀ᶠ k in atTop, ∀ s ∈ V, avgReg y k (s : ℂ) = avgReg x k (s : ℂ) :=
    h.mono fun k hk s hs => (hk s hs).symm
  by_cases hex : ∃ ν, IsVagueLimitOnR V (bdryApprox γ x) ν
  · obtain ⟨ν, hν⟩ := hex
    rw [LocalRule.qBoundaryMeasureOn_eq hV hν, LocalRule.qBoundaryMeasureOn_eq hV (key h ν hν)]
  · have hey : ¬∃ ν, IsVagueLimitOnR V (bdryApprox γ y) ν :=
      fun ⟨ν, hν⟩ => hex ⟨ν, key h' ν hν⟩
    unfold qBoundaryMeasureOn
    rw [dif_neg hex, dif_neg hey]

/-- Open-arc lengths only read the dyadic averages on the arc (small radii). -/
theorem arcLen_congr_of_eventually_avgReg {γ : ℝ} {x y : FieldSample} {a b : ℝ}
    (h : ∀ᶠ k in atTop, ∀ s ∈ Ioo a b, avgReg x k (s : ℂ) = avgReg y k (s : ℂ)) :
    arcLen γ x a b = arcLen γ y a b :=
  congrArg (fun m : Measure ℝ => m (Ioo a b))
    (qBoundaryMeasureOn_congr_of_eventually_avgReg (γ := γ) isOpen_Ioo h)

/-- **B4 (locality of the open-arc lengths).** If `(x', W')` agrees with `(x, W)` near the hull
(the drivers agree on `[0,t]`, and the dyadic circle averages of `x`, `x'` agree on circles in
`S` from scale `j₀` on, where `S` contains the preimages under `f_t` of the `δ`-neighbourhood of
an open `U ⊇ (O⁻_t,0) ∪ (0,O⁺_t)`), the open-arc lengths of `η[0,t]` agree. No boundary limit is
assumed. -/
theorem unzipLengthsArc_eq_of_dyCircAgree {γ t : ℝ} (x x' : FieldSample) {W W' : ℝ → ℝ}
    (hW : Continuous W) (hW' : Continuous W') (hW0 : W 0 = 0) (hW0' : W' 0 = 0) (ht : 0 ≤ t)
    (hWW' : ∀ r ∈ Icc (0 : ℝ) t, W r = W' r) {U : Set ℝ}
    (hU₁ : Ioo (sideImages W t).1 0 ⊆ U) (hU₂ : Ioo 0 (sideImages W t).2 ⊆ U)
    {S : Set ℂ} (hS : IsOpen S) {δ : ℝ} (hδ : 0 < δ)
    (hψ : ∀ u ∈ H, (∃ s ∈ U, dist u (s : ℂ) < δ) → fwdMapInv W t u ∈ S)
    {j₀ : ℕ} (hag : B5.DyCircAgree x x' S j₀) :
    unzipLengthsArc γ (x, W) t = unzipLengthsArc γ (x', W') t := by
  have hloc := B5.eventually_avgReg_unzipped_eq (γ := γ) x x' hW hW' hW0 hW0' ht hWW' hS hδ hψ hag
  have hside := ESM.sideImages_congr_drive ht hWW'
  show (arcLen γ (unzippedField γ (x, W) t) (sideImages W t).1 0,
      arcLen γ (unzippedField γ (x, W) t) 0 (sideImages W t).2) =
    (arcLen γ (unzippedField γ (x', W') t) (sideImages W' t).1 0,
      arcLen γ (unzippedField γ (x', W') t) 0 (sideImages W' t).2)
  rw [← hside]
  exact Prod.ext (arcLen_congr_of_eventually_avgReg (hloc.mono fun k hk s hs => hk s (hU₁ hs)))
    (arcLen_congr_of_eventually_avgReg (hloc.mono fun k hk s hs => hk s (hU₂ hs)))

end LocLen
end QuantumZipper

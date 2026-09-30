import QuantumZipper.Proofs.Thm18.G1ZA1cDet
import QuantumZipper.Proofs.Zipper.LocLenRules
import QuantumZipper.Proofs.Zipper.LocLenBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G1ARC (deterministic part of A1c with open arcs): the segment length at the new root

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71): after unzipping by quantum length `ℓ` the old root sits at `O^∓_{t'}` and the
boundary arc between it and the new root has quantum length `ℓ` (lengths are carried by the
conformal maps and scale by (1.8) under rescaling).

Open-arc copy of `Thm18Asm.G1ZA1c.g1zA1c_seg` (G1ZA1cDet.lean): the unzipped field `x` is only
assumed to have a LOCAL boundary limit on a set `U` containing the open arc (D75: goodness away
from the tip), while the rescaled field `rescale x Q a` (the field of the unzipped configuration,
whose law is the wedge law by E6) is globally good. The pushed side measure of the segment is then
the open-arc length `arcLen γ x O 0` (left) / `arcLen γ x 0 O` (right). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G1ZA1c LocLen

/-- The global boundary measure of a good rescaled field on an open interval is the open-arc
length of the unrescaled field, read with its local limit. -/
theorem g1zArc_Ioo {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsRegularSample x) {U : Set ℝ}
    {ν' : Measure ℝ} (hν' : HasBdryLimitOn γ x U ν') {a : ℝ} (ha : 0 < a)
    (hx'' : IsLQGGood γ (rescale x (Qc γ) a)) {p q : ℝ} (hpq : Ioo (a * p) (a * q) ⊆ U) :
    qBoundaryMeasure γ (rescale x (Qc γ) a) (Ioo p q) = arcLen γ x (a * p) (a * q) := by
  have h1 : arcLen γ (rescale x (Qc γ) a) p q =
      qBoundaryMeasure γ (rescale x (Qc γ) a) (Ioo p q) := by
    rw [arcLen_eq_of_hasBdryLimitOn hx''.1
      (hx''.qBoundaryMeasure_spec.hasBdryLimitOn isOpen_univ) (subset_univ _),
      Measure.restrict_univ]
  rw [← h1, arcLen_rescale_of_hasBdryLimitOn hx hγ ha hν' hpq,
    arcLen_eq_of_hasBdryLimitOn hx hν' hpq]

/-- **The segment length at the new root, open arcs** (copy of `g1zA1c_seg`). -/
theorem g1zA1cArc_seg {γ : ℝ} (hγ : 0 < γ) {x : FieldSample} (hx : IsRegularSample x)
    {U : Set ℝ} {ν' : Measure ℝ} (hν' : HasBdryLimitOn γ x U ν') {a : ℝ} (ha : 0 < a)
    (hx'' : IsLQGGood γ (rescale x (Qc γ) a))
    (hat : ∀ t, qBoundaryMeasure γ (rescale x (Qc γ) a) {t} = 0)
    {left : Bool} {ψ : ℂ → ℂ} {Φ : ℝ ≃o ℝ} (hR : SideReflGood left ψ Φ) {β : ℝ}
    (hβ : β ∈ g1SideHalf left) {O : ℝ}
    (hlim : Tendsto (fun u => (a : ℂ) * ψ u) (𝓝[H] (β : ℂ)) (𝓝 (O : ℂ)))
    (hU : (if left then Ioo O 0 else Ioo 0 O) ⊆ U) :
    (((qBoundaryMeasure γ (rescale x (Qc γ) a)).restrict (g1SideHalf left)).map Φ.symm)
        (g1SideSeg left β) =
      if left then arcLen γ x O 0 else arcLen γ x 0 O := by
  have hval := g1zA1c_refl_val hR hβ hlim
  have h0 : Φ 0 = 0 := hR.1
  have hΦm : Measurable Φ.symm := Φ.symm.continuous.measurable
  set ν := qBoundaryMeasure γ (rescale x (Qc γ) a) with hν
  haveI : NullSingletonClass ν := ⟨hat⟩
  have hsegm : MeasurableSet (g1SideSeg left β) := by
    unfold g1SideSeg; split_ifs <;> exact measurableSet_Icc
  rw [Measure.map_apply hΦm hsegm, Measure.restrict_apply (hΦm hsegm)]
  cases left
  · -- right side: `Φ⁻¹⁻¹[0, β] ∩ (0, ∞) = (0, Φ β]`
    have hset : Φ.symm ⁻¹' g1SideSeg false β ∩ g1SideHalf false = Ioc 0 (Φ β) := by
      ext y
      simp only [g1SideSeg, g1SideHalf, Bool.false_eq_true, if_false, mem_inter_iff,
        mem_preimage, mem_Icc, mem_Ioi, mem_Ioc]
      rw [OrderIso.le_symm_apply, OrderIso.symm_apply_le, h0]
      constructor
      · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1.le, h2⟩, h1⟩
    simp only [Bool.false_eq_true, if_false] at hU ⊢
    have hpq : Ioo (a * 0) (a * Φ β) ⊆ U := by rw [mul_zero, hval]; exact hU
    rw [hset, measure_congr Ioo_ae_eq_Ioc.symm, hν, g1zArc_Ioo hγ hx hν' ha hx'' hpq, mul_zero,
      hval]
  · -- left side: `Φ⁻¹⁻¹[β, 0] ∩ (−∞, 0) = [Φ β, 0)`
    have hset : Φ.symm ⁻¹' g1SideSeg true β ∩ g1SideHalf true = Ico (Φ β) 0 := by
      ext y
      simp only [g1SideSeg, g1SideHalf, if_true, mem_inter_iff,
        mem_preimage, mem_Icc, mem_Iio, mem_Ico]
      rw [OrderIso.le_symm_apply, OrderIso.symm_apply_le, h0]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2.le⟩, h2⟩
    simp only [if_true] at hU ⊢
    have hpq : Ioo (a * Φ β) (a * 0) ⊆ U := by rw [mul_zero, hval]; exact hU
    rw [hset, measure_congr Ioo_ae_eq_Ico.symm, hν, g1zArc_Ioo hγ hx hν' ha hx'' hpq, mul_zero,
      hval]

end R18
end QuantumZipper

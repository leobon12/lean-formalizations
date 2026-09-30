import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.LocLenPStarGood
import QuantumZipper.Proofs.Zipper.F1ReflReg
import QuantumZipper.Proofs.Zipper.F1Side3
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.LocLenLocalityF1Close

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), part of task R6e: reflection of the open-arc lengths

Open-arc copies of `F1.unzipLengths_reflect_of` (F1Reflect.lean:102),
`F1.unzipLengths_reflect_of_good` (F1ReflReg.lean:165) and `F1.pstar_refl_one`
(F1NodeAsm.lean:99): the reflection `z ↦ −z̄` exchanges the two sides of `η`
(Sheffield arXiv:1012.4797 §5.4 p. 72, "by symmetry"). The old proof needs global goodness of
the unzipped field at time `t` (`AllOffsets.qBoundaryMeasure_reflectH`); here a local limit off
the tip and the root images (`IsLQGGoodOff … (offSet W t)`) suffices, and for `P_*` samples it is
supplied by `pStarGoodOffAll_of_yMergeOffTip`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace LocLen

/-- **Reflection of the open-arc lengths** (deterministic): if the unzipped field of `c` at `t`
has a dyadic local limit off `offSet c.2 t`, `O⁻_t ≤ 0 ≤ O⁺_t`, and the reflected configuration's
unzipped field has the reflected regularized averages, the open-arc lengths are swapped. -/
theorem unzipLengthsArc_reflect_of {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} {t : ℝ}
    (havg : ∀ (k : ℕ) (s : ℝ), avgReg (unzippedField γ (F1.reflectConfig c) t) k (s : ℂ) =
      avgReg (unzippedField γ c t) k ((-s : ℝ) : ℂ))
    {ν : Measure ℝ} (hν : IsVagueLimitOnR (offSet c.2 t)ᶜ (bdryApprox γ (unzippedField γ c t)) ν)
    (hsign : (sideImages c.2 t).1 ≤ 0 ∧ 0 ≤ (sideImages c.2 t).2)
    (hside : sideImages (-c.2) t = (-(sideImages c.2 t).2, -(sideImages c.2 t).1)) :
    unzipLengthsArc γ (F1.reflectConfig c) t = (unzipLengthsArc γ c t).swap := by
  have hν' := isVagueLimitOnR_neg havg (isClosed_offSet c.2 t).isOpen_compl hν
  set a := (sideImages c.2 t).1
  set b := (sideImages c.2 t).2
  have hs1 : Ioo a 0 ⊆ (offSet c.2 t)ᶜ := fun u hu hu' =>
    disjoint_left.1 (Ioo_left_disjoint_offSet c.2 t hsign.2) hu hu'
  have hs2 : Ioo 0 b ⊆ (offSet c.2 t)ᶜ := fun u hu hu' =>
    disjoint_left.1 (Ioo_right_disjoint_offSet c.2 t hsign.1) hu hu'
  have hpre : ∀ p q : ℝ, Ioo p q ⊆ (offSet c.2 t)ᶜ →
      Ioo (-q) (-p) ⊆ (fun u : ℝ => -u) ⁻¹' (offSet c.2 t)ᶜ := fun p q h u hu =>
    h ⟨by linarith [hu.2], by linarith [hu.1]⟩
  have hneg : ∀ p q : ℝ, (fun u : ℝ => -u) ⁻¹' Ioo (-q) (-p) = Ioo p q := fun p q => by
    ext u; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;>
      linarith [h.1, h.2]
  show (arcLen γ (unzippedField γ (F1.reflectConfig c) t) (sideImages (-c.2) t).1 0,
      arcLen γ (unzippedField γ (F1.reflectConfig c) t) 0 (sideImages (-c.2) t).2) =
    (arcLen γ (unzippedField γ c t) 0 b, arcLen γ (unzippedField γ c t) a 0)
  rw [hside]
  dsimp only
  have e1 := arcLen_eq_of_isVagueLimitOnR hν' (by simpa using hpre 0 b hs2)
  have e2 := arcLen_eq_of_isVagueLimitOnR hν' (by simpa using hpre a 0 hs1)
  rw [e1, e2, arcLen_eq_of_isVagueLimitOnR hν hs2, arcLen_eq_of_isVagueLimitOnR hν hs1,
    Measure.map_apply measurable_neg measurableSet_Ioo,
    Measure.map_apply measurable_neg measurableSet_Ioo]
  have h1 := hneg 0 b
  have h2 := hneg a 0
  rw [neg_zero] at h1 h2
  rw [h1, h2]

/-- Open-arc copy of `F1.unzipLengths_reflect_of_good`: goodness off `offSet` replaces global
goodness. -/
theorem unzipLengthsArc_reflect_of_goodOff {γ : ℝ} {c : FieldSample × (ℝ → ℝ)} {t : ℝ}
    (hW : Continuous c.2) (hW0 : c.2 0 = 0) (ht : 0 ≤ t) (hh : IsRegularSample c.1)
    (hgood : IsLQGGoodOff γ (unzippedField γ c t) (offSet c.2 t))
    (hsign : (sideImages c.2 t).1 ≤ 0 ∧ 0 ≤ (sideImages c.2 t).2)
    (hside : sideImages (-c.2) t = (-(sideImages c.2 t).2, -(sideImages c.2 t).1)) :
    unzipLengthsArc γ (F1.reflectConfig c) t = (unzipLengthsArc γ c t).swap := by
  obtain ⟨F0, hF0⟩ := hh
  obtain ⟨⟨F, hF⟩, ⟨ν, hν⟩, -⟩ := hgood
  have hreg := F1.regEq_unzippedField_reflect hW hW0 ht hF0 hF
  have havg : ∀ (k : ℕ) (s : ℝ), avgReg (unzippedField γ (F1.reflectConfig c) t) k (s : ℂ) =
      avgReg (unzippedField γ c t) k ((-s : ℝ) : ℂ) := fun k s => by
    rw [hreg k s, F1.avgReg_reflectH_eq hF k (show (0 : ℝ) ≤ ((s : ℝ) : ℂ).im by simp)]
    congr 1
    simp
  exact unzipLengthsArc_reflect_of havg (hν.isVagueLimitOnR ⟨F, hF⟩) hsign hside

/-- Open-arc copy of `F1.pstar_refl_one`: the reflection identity at time `1` for `P_*` samples,
from goodness off `offSet` (no global goodness at time `1`). -/
theorem pstar_refl_one_arc (hG : PStarGoodOffAllStmt) {κ : ℝ} {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → FieldSample}
    {B' : ℝ≥0 → Ω' → ℝ} (h : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', unzipLengthsArc (Real.sqrt κ) (F1.reflectConfig (Y ω, drive κ B' ω)) 1 =
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1).swap := by
  have hS := F1.thm18Setting_of_pstar h
  have hIn := Thm18Asm.thm18Inputs_of_setting hS
  have hB := h.2.2.2.1
  filter_upwards [hG κ P' Y B' h, hIn.1, hB.cont, hB.eval_zero_ae_eq_zero,
    F1.ae_sideImages_reflect_drive hB h.1 h.2.1.le zero_le_one,
    B5.ae_forall_sideImages_sign h.1 h.2.1 hB] with ω hg hY hc h0 hside hsign
  refine unzipLengthsArc_reflect_of_goodOff (F1.continuous_drive_of κ hc) ?_ zero_le_one hY.1.1
    (hg 1 zero_le_one) (hsign 1 zero_le_one) hside
  show drive κ B' ω 0 = 0
  simp [drive, h0]

/-- Closed form. -/
theorem pstar_refl_one_arc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) {κ : ℝ} {Ω' : Type}
    [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → FieldSample}
    {B' : ℝ≥0 → Ω' → ℝ} (h : Thm13Asm.IsPStarSample κ P' Y B') :
    ∀ᵐ ω ∂P', unzipLengthsArc (Real.sqrt κ) (F1.reflectConfig (Y ω, drive κ B' ω)) 1 =
      (unzipLengthsArc (Real.sqrt κ) (Y ω, drive κ B' ω) 1).swap :=
  pstar_refl_one_arc (pStarGoodOffAll_of_yMergeOffTip hYO) h

end LocLen
end QuantumZipper

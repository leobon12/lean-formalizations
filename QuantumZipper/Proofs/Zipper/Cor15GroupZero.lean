import QuantumZipper.Proofs.Zipper.Cor15GroupNeg
import QuantumZipper.Proofs.LQG.AllOffsetsBasic
import QuantumZipper.Proofs.Field.Factorization

/-!
# Corollary 1.5 (b) for all nonpositive times

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
`theorem1_5b_nonpos`: for `s, t ≤ 0`, almost surely `Z^CAP_{s+t} c = Z^CAP_s (Z^CAP_t c)` up to
`ConfigEq`, unconditionally. The cases `s, t < 0` and `s = 0 > t` are in `Cor15GroupNeg`; here
the cases with `t = 0`.

Input: `ae_evalReg_fc_h0rev_add`, a.s. the field `𝔥₀ + X` is regular at every dyadic folded
circle (`UnzipFull.ae_split_fc_fixed` at the zero driver for the `𝔥₀` part and
`AllOffsets.ae_evalReg_fc_eq` for the free field). Then `Z^CAP_0 c` agrees with `c` up to
`ConfigEq` (`Cor15Group.configEq_zipCapUp_zero`); its driver is even literally `c`'s driver, and
unzipping reads the field only through `avgReg` (`Factorization.coordChange_congr`), so
`Z^CAP_s (Z^CAP_0 c) = Z^CAP_s c` for `s < 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Cor15Group

/-- A.s. the field `𝔥₀ + X` is regular at every dyadic folded circle. -/
theorem ae_evalReg_fc_h0rev_add (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      evalReg (ofFun (h0rev κ) + X ω) (foldedCircle (CoordsFull.fullIndex i).1
        (CoordsFull.fullIndex i).2) = (ofFun (h0rev κ) + X ω) (foldedCircle
          (CoordsFull.fullIndex i).1 (CoordsFull.fullIndex i).2) := by
  refine ae_all_iff.2 fun i => ?_
  have hr := UnzipFull.fullIndex_radius_pos i
  set w := (CoordsFull.fullIndex i).1
  set r := (CoordsFull.fullIndex i).2
  have hW : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have h1 := UnzipFull.ae_split_fc_fixed UnzipFull.inputs_holds κ hX hW le_rfl
    (TwoPoint.measurable_revMap hW le_rfl) w hr
  have hmap : (foldedCircle w r).map (revMap (fun _ => (0 : ℝ)) 0) = foldedCircle w r := by
    have h : revMap (fun _ => (0 : ℝ)) 0 =ᵐ[foldedCircle w r] id :=
      (TwoPoint.foldedCircle_ae_mem_H w hr).mono fun z hz =>
        CharFun.revMap_zero_eq continuous_const rfl hz
    rw [Measure.map_congr h, Measure.map_id]
  rw [hmap] at h1
  have h2 := AllOffsets.ae_evalReg_fc_eq hX (CircleFubini.foldH_mem_Hbar' w) hr
  rw [CoordReg.foldedCircle_foldH] at h2
  filter_upwards [h1, h2] with ω e1 e2
  rw [e1, e2]
  rfl

/-- Unzipping reads the field only through `avgReg`. -/
theorem zipCapDown_congr (γ a : ℝ) {y c : FieldSample × (ℝ → ℝ)} (h1 : avgReg y.1 = avgReg c.1)
    (h2 : y.2 = c.2) : zipCapDown γ a y = zipCapDown γ a c := by
  unfold zipCapDown
  rw [Factorization.coordChange_congr h1, h2]

variable (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)

/-- A.s. `Z^CAP_0 c` has the regularized field of `c` and literally the driver of `c`. -/
theorem ae_zipCapUp_zero_eq (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, avgReg (zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)).1 =
        avgReg (ofFun (h0rev κ) + X ω) ∧
      (zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)).2 = drive κ B ω := by
  filter_upwards [ae_evalReg_fc_h0rev_add κ hX, hB.eval_zero_ae_eq_zero] with ω hreg h0
  have hc := configEq_zipCapUp_zero (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) hreg
    (drive_zero h0)
  refine ⟨funext fun k => funext fun z => (hc.1 k z).symm, funext fun u => ?_⟩
  rcases le_or_gt 0 u with hu | hu
  · exact (hc.2 u hu).symm
  · show (if u ≤ 0 then _ else _) = _
    simp only [hu.le, ↓reduceIte]
    rw [max_eq_right hu.le, sub_zero, sub_self]
    simp [drive, Real.toNNReal_of_nonpos hu.le, h0]

/-- **Corollary 1.5 (b) for `s ≤ 0`, `t ≤ 0`** (unconditional). -/
theorem theorem1_5b_nonpos (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) {s t : ℝ} (hs : s ≤ 0) (ht : t ≤ 0) :
    ∀ᵐ ω ∂P, ConfigEq
      (zipCap (Real.sqrt κ) (s + t) (ofFun (h0rev κ) + X ω, drive κ B ω))
      (zipCap (Real.sqrt κ) s (zipCap (Real.sqrt κ) t (ofFun (h0rev κ) + X ω, drive κ B ω))) := by
  rcases ht.lt_or_eq with ht | rfl
  · rcases hs.lt_or_eq with hs | rfl
    · exact theorem1_5b_neg_neg κ P B X hB hX hind hs ht
    · exact theorem1_5b_zero_neg κ P B X hB hX hind ht
  · rw [add_zero, zipCap_of_nonneg (le_refl (0 : ℝ))]
    filter_upwards [ae_zipCapUp_zero_eq κ P B X hB hX, ae_evalReg_fc_h0rev_add κ hX,
      hB.eval_zero_ae_eq_zero] with ω ⟨h1, h2⟩ hreg h0
    rcases hs.lt_or_eq with hs | rfl
    · rw [zipCap_of_neg hs, zipCapDown_congr (Real.sqrt κ) (-s)
        (y := zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω))
        (c := (ofFun (h0rev κ) + X ω, drive κ B ω)) h1 h2]
      exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    · rw [zipCap_of_nonneg (le_refl (0 : ℝ))]
      set y := zipCapUp (Real.sqrt κ) 0 (ofFun (h0rev κ) + X ω, drive κ B ω)
      refine configEq_zipCapUp_zero _ y (fun i => ?_) (by rw [h2]; exact drive_zero h0)
      obtain ⟨hWc, hW0, -, -⟩ := weldDriver_spec
        ⟨_, Cor15Partial.isWeldingDriver_zero (Real.sqrt κ) (ofFun (h0rev κ) + X ω)⟩
      have hr := UnzipFull.fullIndex_radius_pos i
      rw [Factorization.evalReg_congr h1]
      show _ = coordChange (ofFun (h0rev κ) + X ω)
        (revMapInv (weldDriver (Real.sqrt κ) (ofFun (h0rev κ) + X ω) 0) 0) (Qc (Real.sqrt κ)) _
      rw [CoordReg.coordChange_fc_congr _ (Cor15Partial.revMapInv_zero_eqOn hWc hW0) _ _ hr,
        Cor15Partial.coordChange_id_apply]

end Cor15Group
end QuantumZipper

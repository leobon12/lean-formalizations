import QuantumZipper.Proofs.Zipper.F1ReadMeasLoc
import QuantumZipper.Proofs.Zipper.LocLenMeasArc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R2a: the open-arc local lengths are a measurable functional

Open-arc copy of `B5.LocLengthsMeasStmt` (B5LocF1Assembly.lean:69) and of its proof
`F1.locLengthsMeasStmt_holds` (F1ReadMeasLoc.lean:133): the reader `vagueRd` of closed intervals
is replaced by the open-arc reader `LocLen.arcRd` (LocLenMeasArc.lean), and the target is
`unzipLengthsArc`. The local limit is only asked on the two open arcs themselves; the side
conditions `|O^±_t| < a` of the old statement are kept (unused) so that the consumer
(`B5.locality_core`) can be copied verbatim. Own bookkeeping (Sheffield arXiv:1012.4797 §5.4
pp. 70–72 states locality without proof; B-P arXiv:2404.16642 p. 294).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open ESM CharFun CoordsFull

/-- Open-arc copy of `B5.LocLengthsMeasStmt`. -/
def LocLengthsMeasArcStmt (γ κ : ℝ) : Prop :=
  ∀ (u : ℝ≥0) (a t : ℝ), 0 < a → 0 < t → t ≤ u →
    ∃ Φ : FieldSample × (Set.Iic u → ℝ) → ℝ≥0∞ × ℝ≥0∞, Measurable Φ ∧
      ∀ q : FieldSample × (Set.Iic u → ℝ), Continuous q.2 → q.2 ⟨0, Set.mem_Iic.2 zero_le⟩ = 0 →
        (∀ x : ℝ, x ≠ 0 → ∃ v, IsForwardSol (B5.clampDrive κ u q.2) (x : ℂ) t v) →
        |(sideImages (B5.clampDrive κ u q.2) t).1| < a →
        |(sideImages (B5.clampDrive κ u q.2) t).2| < a →
        (∃ ν, IsVagueLimitOnR (Ioo (sideImages (B5.clampDrive κ u q.2) t).1 0)
          (bdryApprox γ (unzippedField γ (q.1, B5.clampDrive κ u q.2) t)) ν) →
        (∃ ν, IsVagueLimitOnR (Ioo 0 (sideImages (B5.clampDrive κ u q.2) t).2)
          (bdryApprox γ (unzippedField γ (q.1, B5.clampDrive κ u q.2) t)) ν) →
        Φ q = LocLen.unzipLengthsArc γ (q.1, B5.clampDrive κ u q.2) t

/-- **The open-arc local-lengths reader.** -/
def locRdArc (γ κ : ℝ) (u : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) (q : FieldSample × (Set.Iic u → ℝ)) :
    ℝ≥0∞ × ℝ≥0∞ :=
  (LocLen.arcRd γ (surQC κ t ht (Qc γ) (q.1, pathT t (extIic u q.2)))
      (sideReader κ t ht (pathT t (extIic u q.2))).1 0,
    LocLen.arcRd γ (surQC κ t ht (Qc γ) (q.1, pathT t (extIic u q.2))) 0
      (sideReader κ t ht (pathT t (extIic u q.2))).2)

theorem measurable_locRdArc (γ κ : ℝ) (u : ℝ≥0) (t : ℝ) (ht : 0 ≤ t) :
    Measurable (locRdArc γ κ u t ht) := by
  have hX := measurable_locX γ κ u t ht
  have hs := measurable_locS κ u t ht
  exact (LocLen.measurable_arcRd_comp γ hX hs.fst measurable_const).prodMk
    (LocLen.measurable_arcRd_comp γ hX measurable_const hs.snd)

theorem arcRd_congr {γ : ℝ} {x x' : FieldSample} (h : bdryApprox γ x = bdryApprox γ x')
    (b c : ℝ) : LocLen.arcRd γ x b c = LocLen.arcRd γ x' b c := by
  unfold LocLen.arcRd
  simp only [vagueRd_congr h]

/-- **(R4, open arcs) holds.** -/
theorem locLengthsMeasArcStmt_holds (γ κ : ℝ) : LocLengthsMeasArcStmt γ κ := by
  intro u a t ha ht htu
  refine ⟨locRdArc γ κ u t ht.le, measurable_locRdArc γ κ u t ht.le,
    fun q hq hq0 halive hs1 hs2 hlim1 hlim2 => ?_⟩
  set p := extIic u q.2 with hpdef
  have hpc : Continuous p := continuous_extIic u hq
  have hUC : DyUC p := dyUC_of_continuous hpc
  set W := B5.clampDrive κ u q.2 with hWdef
  have hrd : readDrv p = fun r => p r.toNNReal := by
    have e : (fun t : ℝ≥0 => (fun r : ℝ => p r.toNNReal) t) = p :=
      funext fun t => by simp only [Real.toNNReal_coe]
    have h := readDrv_eq (W := fun r : ℝ => p r.toNNReal) (hpc.comp continuous_real_toNNReal)
      (fun s => by simp only [Real.toNNReal_coe])
    rwa [e] at h
  have hWp : ∀ r, W r = Real.sqrt κ * p r.toNNReal := fun r => rfl
  have hc : Continuous W := by
    have : W = fun r => Real.sqrt κ * p r.toNNReal := funext hWp
    rw [this]; exact continuous_const.mul (hpc.comp continuous_real_toNNReal)
  have h0 : W 0 = 0 := by
    rw [hWp]
    have e : p (0 : ℝ).toNNReal = q.2 ⟨0, Set.mem_Iic.2 zero_le⟩ := by
      simp only [hpdef, extIic, Real.toNNReal_zero, zero_le, min_eq_left]
    rw [e, hq0, mul_zero]
  set f := pathT t p with hfdef
  have hf : ∀ r ∈ Icc (0 : ℝ) t, Wof κ t ht.le f r = W r := by
    intro r hr
    classical
    simp only [Wof, hfdef, pathT, hUC, ↓reduceDIte, ContinuousMap.coe_mk,
      projIcc_of_mem ht.le hr, hrd, hWp]
  -- side images
  have hside : sideImages W t = sideReader κ t ht.le f := by
    refine (sideImages_congr_drive ht.le fun r hr => (hf r hr).symm).trans ?_
    refine sideImages_Wof_eq_sideReader κ t ht.le f fun x hx => ?_
    obtain ⟨v, hv⟩ := halive x hx
    exact ⟨v, isForwardSol_congr_drive (fun r hr => (hf r hr).symm) hv⟩
  -- field
  have hEqOn : EqOn (fwdMapInv W t) (revMap (Wof κ t ht.le (revPath t ht.le f)) t) H := by
    intro w hw
    rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev W hc h0 ht.le hw]
    refine ReverseFlow.revMap_congr_drive w fun r hr => ?_
    have hr' : t - r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2], by linarith [hr.1]⟩
    have ht' : t ∈ Icc (0 : ℝ) t := ⟨ht.le, le_rfl⟩
    have e1 := hf (t - r) hr'
    have e2 := hf t ht'
    show W (t - r) - W t = _
    rw [← e1, ← e2]
    simp only [Wof, projIcc_of_mem ht.le hr, projIcc_of_mem ht.le hr', projIcc_of_mem ht.le ht',
      revPath_apply]
    ring
  have hco : coordsFull (unzippedField γ (q.1, W) t) =
      coordsFull (surQC κ t ht.le (Qc γ) (q.1, f)) := by
    rw [surQC, coordsFull_fromCoords_coordsFull]
    funext i
    exact UnzipInvariance.coordChange_congr_of_eqOn hEqOn
      (foldedCircle_compl_H_eq_zero _ (UnzipFull.fullIndex_radius_pos i)) q.1 (Qc γ)
  have hbd : bdryApprox γ (surQC κ t ht.le (Qc γ) (q.1, f)) =
      bdryApprox γ (unzippedField γ (q.1, W) t) :=
    Factorization.bdryApprox_congr (avgReg_congr_full hco.symm) _
  obtain ⟨ν₁, hν₁⟩ := hlim1
  obtain ⟨ν₂, hν₂⟩ := hlim2
  unfold locRdArc
  rw [← hfdef, arcRd_congr hbd, arcRd_congr hbd, ← hside,
    LocLen.arcRd_eq_arcLen isOpen_Ioo hν₁ subset_rfl,
    LocLen.arcRd_eq_arcLen isOpen_Ioo hν₂ subset_rfl]
  rfl

end F1
end QuantumZipper

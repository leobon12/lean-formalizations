import QuantumZipper.Proofs.Zipper.LocLenLocalityF1
import QuantumZipper.Proofs.Zipper.LocLenF2Loc
import QuantumZipper.Proofs.Zipper.F2Step3DensSign

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6d closed: B5 locality for F1 with open arcs

Input (R1′) `B5.WedgeUnzipArcLimitStmt` of `B5.f1LocalityArcStmt_of_arcLimits` follows from the
local limits off `{O⁻_t, 0, O⁺_t}` (`LocLen.wedgeUnzipLimitLoc_of_yMergeOffTip`, R4d) by
restriction to the two open arcs, using the side signs `O⁻_t ≤ 0 ≤ O⁺_t` (proved,
`F2.ae_forall_sideImages_fst_nonpos` and the reflection step of `F2.step3SideSign_holds`).
Hence `f1LocalityArc_of_yMergeOffTip`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B5

/-- Side signs at all times for `√κ B` (copy of the proof of `F2.step3SideSign_holds`, which only
uses the Brownian motion). -/
theorem ae_forall_sideImages_sign {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      (sideImages (drive κ B ω) t).1 ≤ 0 ∧ 0 ≤ (sideImages (drive κ B ω) t).2 := by
  filter_upwards [F2.ae_forall_sideImages_fst_nonpos hκ hκ4 hB,
    F2.ae_forall_sideImages_fst_nonpos hκ hκ4 hB.neg, RS.ae_real_alive hB hκ hκ4.le]
    with ω h1 hneg halive t ht
  refine ⟨h1 t ht, ?_⟩
  obtain ⟨a, b, hL, hR⟩ := F1.exists_tendsto_sideImages_of_alive ht fun x hx => halive x hx t ht
  have hdr : drive κ (-B) ω = -drive κ B ω := by
    funext s; simp [drive]
  have h := hneg t ht
  rw [hdr, F1.sideImages_reflect_swap ht hL hR] at h
  simp only at h
  linarith

/-- (R1′) from the local limits off the tip and root images. -/
theorem wedgeUnzipArcLimit_of_loc {γ α κ : ℝ} (h : LocLen.WedgeUnzipLimitLocStmt γ α κ) :
    WedgeUnzipArcLimitStmt γ α κ := by
  intro hκ hκ4 hγ hα Ω _ P X A B hP hX hA hB hAm hBm hind
  filter_upwards [h hκ hκ4 hγ hα Ω P X A B hP hX hA hB hAm hBm hind,
    ae_forall_sideImages_sign hκ hκ4 hB] with ω hω hs m
  obtain ⟨ν, hν⟩ := hω m
  have ht : (0 : ℝ) ≤ (GermZeroOne.epsSeq m : ℝ) := NNReal.coe_nonneg _
  obtain ⟨hm, hp⟩ := hs _ ht
  have hopen : IsOpen (LocLen.offSet (drive κ B ω) (GermZeroOne.epsSeq m : ℝ))ᶜ :=
    (LocLen.isClosed_offSet _ _).isOpen_compl
  refine ⟨⟨_, E1.isVagueLimitOnR_restrict_open hν isOpen_Ioo fun u hu hu' =>
      disjoint_left.1 (LocLen.Ioo_left_disjoint_offSet _ _ hp) hu hu'⟩,
    ⟨_, E1.isVagueLimitOnR_restrict_open hν isOpen_Ioo fun u hu hu' =>
      disjoint_left.1 (LocLen.Ioo_right_disjoint_offSet _ _ hm) hu hu'⟩⟩

/-- **B5 locality for F1 with open-arc lengths**, from the SW leaf `YMergeOffTipStmt` only. -/
theorem f1LocalityArc_of_yMergeOffTip (hYO : WedgeUnzip.YMergeOffTipStmt) (κ : ℝ) :
    F1LocalityArcStmt (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) κ :=
  f1LocalityArcStmt_of_arcLimits
    (wedgeUnzipArcLimit_of_loc (LocLen.wedgeUnzipLimitLoc_of_yMergeOffTip hYO κ))

end B5
end QuantumZipper

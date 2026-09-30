import QuantumZipper.Proofs.Zipper.LocLenF2Chain
import QuantumZipper.Proofs.Zipper.LocLenB5UPlus
import QuantumZipper.Proofs.Zipper.F2WeldTimes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R7-S14 (1): F2 step (1) with open-arc lengths (`f2WeldLenArc_holds`)

Source: Sheffield, arXiv:1012.4797, §5.4 pp. 70–72 (step 1: the lengths of the two sides of
`η_T[0,r]` are the boundary lengths of their preimages in the fixed chart `T`, additive along
`η_T`). Copy of `F2.f2WeldLen_of_inputs` (F2Weld.lean) with the open-arc B5 input
`LocLen.b5UniformArcStmt_holds` (lengths = `ν_T`-masses of OPEN preimage arcs) and the proved
welding structure `F2.weldTimesStmt`. The only change: `ν_T(Ioo a b) = ν_T(Icc a b)` since the
fixed-time chart-`T` measure has no atoms (`RevCouplingReg.revCouplingBoundaryMeasureRegular`,
`LocLen.measure_Icc_eq_Ioo_of_noAtoms`). No TipCore / TIP-X / variable-time goodness is used.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- **F2 step (1), open arcs** (copy of `F2.f2WeldLen_of_inputs`). -/
theorem f2WeldLenArc_holds : F2WeldLenArcStmt := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind
  obtain ⟨B'', hB'', hind'', hV⟩ := B2.b2_V_brownian (κ := κ) hB hind hT.le
  filter_upwards [b5UniformArcStmt_holds κ hκ hκ4 T hT P B'' X hB'' hX hind'', hV, hB.cont,
    hB.eval_zero_ae_eq_zero, hB''.cont, hB''.eval_zero_ae_eq_zero,
    B2.b2_ident_qBoundaryMeasure (κ := κ) hB'' hX hind'' hT.le,
    RevCouplingReg.revCouplingBoundaryMeasureRegular κ hκ hκ4 T hT P B X hB hX hind,
    F2.weldTimesStmt κ hκ hκ4 T hT P B hB] with ω hUω hVω hc h0 hc'' h0'' hid hR hWω
  have hWc : Continuous (drive κ B ω) := drive_continuous hc
  have hW0 : drive κ B ω 0 = 0 := drive_zero h0
  have hVV : EqOn (B2.Vr κ T B'' ω) (drive κ B ω) (Icc 0 T) := fun s hs => by
    have h1 := hVω (T - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h2 := hVω T ⟨hT.le, le_rfl⟩
    simp only [B2.Vr] at h1 h2 ⊢
    rw [B2.vrev_of_mem hs, ← h1, ← h2, B2.vrev_of_mem ⟨by linarith [hs.2], by linarith [hs.1]⟩,
      B2.vrev_of_mem ⟨hT.le, le_rfl⟩, sub_sub_cancel, sub_self, hW0]
    ring
  have hVVu : ∀ u ∈ Icc (0 : ℝ) T, EqOn (B2.Vr κ T B'' ω) (drive κ B ω) (Icc 0 u) :=
    fun u hu s hs => hVV ⟨hs.1, hs.2.trans hu.2⟩
  have hrev : revMap (B2.Vr κ T B'' ω) T = revMap (drive κ B ω) T :=
    funext fun z => ReverseFlow.revMap_congr_drive z hVV
  have hν : qBoundaryMeasure (Real.sqrt κ) (B2.h0f κ T B'' X ω) =
      qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) := by
    rw [hid]; simp only [couplingFieldRev, hrev]
  have hL : ∀ s ∈ Icc (0 : ℝ) T, unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) s =
      unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B'' X ω) s := fun s hs => by
    rw [F2.cfgT_eq]
    exact unzipLengthsArc_eq_of_drive_eqOn _ (B2.continuous_vrev hWc T)
      (drive_continuous hc'') (B2.vrev_zero hT.le) (drive_zero h0'') hs.1
      fun r hr => hVω r ⟨hr.1, hr.2.trans hs.2⟩
  set ν := qBoundaryMeasure (Real.sqrt κ) (couplingFieldRev κ (drive κ B ω) T (X ω)) with hνdef
  have hTT : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hLen : ∀ s ∈ Icc (0 : ℝ) T,
      (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) s).1 =
          ν (Icc (zeroMinus (drive κ B ω) T) (zeroMinus (drive κ B ω) (T - s))) ∧
        (unzipLengthsArc (Real.sqrt κ) (F2.cfgT κ T B X ω) s).2 =
          ν (Icc (zeroPlus (drive κ B ω) (T - s)) (zeroPlus (drive κ B ω) T)) := by
    intro s hs
    have hTs : T - s ∈ Icc (0 : ℝ) T := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    obtain ⟨h1, h2⟩ := hUω s hs
    rw [hL s hs, h1, h2, hν, F2.zeroMinus_congr_drive (hVVu T hTT),
      F2.zeroMinus_congr_drive (hVVu _ hTs), F2.zeroPlus_congr_drive (hVVu T hTT),
      F2.zeroPlus_congr_drive (hVVu _ hTs)]
    exact ⟨(measure_Icc_eq_Ioo_of_noAtoms (hR.1 _) (hR.1 _)).symm,
      (measure_Icc_eq_Ioo_of_noAtoms (hR.1 _) (hR.1 _)).symm⟩
  have hLT := hLen T hTT
  rw [sub_self, B5.zeroMinus_zero_time hWc hW0, F2.zeroPlus_zero_time hWc hW0] at hLT
  refine ⟨?_, ?_⟩
  · rw [hLT.1]; exact (hR.2.2 _ _).ne
  · intro xm xp hxm hxp heq hmem
    obtain ⟨u, hu, rfl, rfl, hmo, hpo⟩ := hWω xm xp hxm hxp heq hmem
    have hs : T - u ∈ Icc (0 : ℝ) T := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hLr := hLen (T - u) hs
    rw [sub_sub_cancel] at hLr
    refine ⟨T - u, hs, ?_, ?_⟩
    · rw [hLr.1, hLT.1, add_comm]
      exact F2.measure_Icc_add_Icc hR.1 hmo hxm.le
    · rw [hLr.2, hLT.2]
      exact F2.measure_Icc_add_Icc hR.1 hxp.le hpo

end LocLen
end QuantumZipper

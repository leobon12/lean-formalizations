import QuantumZipper.Proofs.Thm18.ZqCMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZQ-CORE (7): `G3ZqO6CoreDStmt` from the Palm transfer of the core functional

`g3ZqO6CoreDStmt_of_zoomTransfer : ZqCZoomTransferStmt → G3ZqO6CoreDStmt`: the window mass is
`zqCWinMassStmt_holds` (ZqCMass2), the Palm-side limit is `tendsto_palm_side` (ZqCAsm, from the
conditional zoom `palm_window_fix` and dominated convergence), and its measurability is
`aemeasurable_palmJ` (ZqCMeas).

Sheffield, arXiv:1012.4797, pp. 70–71. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace ZqC

open G3Z2b2 D3Plus G1Zm G3Zq G3ZqL G3ZqO Factorization

/-- **The core node from the Palm transfer of the core functional.** -/
theorem g3ZqO6CoreDStmt_of_zoomTransfer (hT : ZqCZoomTransferStmt) :
    G3ZqO6CoreDStmt := by
  intro γ hγ hγ2 Ψ hsel Ω' _ P' _ X A hX hA hXA Ω'' _ P'' _ Y'' hW Ω _ P _ B hB left R Γ hΓ hΓ1
    U hU η hη hη4 δ hδ hδη
  obtain ⟨V, hV, hPF⟩ := exists_palmFor hγ hγ2 P' X A hX hA hXA
  refine Eventually.of_forall fun a hac hs e he => ?_
  have ha : G3ZqGoodPath γ a := ⟨hac, hs⟩
  have hTr := hT γ hγ hγ2 Ψ hsel P' X A hX hA hXA V hV hPF a ha left R Γ hΓ hΓ1 U hU
    η hη hη4 δ hδ hδη
  have hJm : ∀ L, AEMeasurable (palmJ γ L R Γ Ψ left U δ a P' V)
      (volume.restrict (coreSet left η)) := fun L =>
    aemeasurable_palmJ hsel L R hΓ left U hη hη4 hδ hδη a P' hV
  have hMe := zqCWinMassStmt_holds γ hγ hγ2 P' X A hX hA hXA V hV hPF left U hU η hη hη4 δ hδ hδη
  set c := ∫⁻ ω, Γ (locFieldFull R (Y'' ω)) ∂P'' with hc
  have hc1 : c ≤ 1 := by
    rw [hc]
    exact (lintegral_mono fun ω => hΓ1 _).trans (le_of_eq (lintegral_one.trans measure_univ))
  set Iinf := ∫⁻ x, (coreSet left η).indicator (fun x => rhoP γ x *
    (P' (palmWin γ left U δ x V) * c)) x with hIinf
  have hIe : Iinf = c * ∫⁻ ω', winCoreD γ left U η δ (wedgeU γ X A ω') ∂P' := by
    rw [hMe, ← lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top hc1), hIinf]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ coreSet left η
    · simp only [indicator_of_mem hx]; ring
    · simp only [indicator_of_notMem hx, mul_zero]
  have hWfin : ∫⁻ ω', winCoreD γ left U η δ (wedgeU γ X A ω') ∂P' ≠ ⊤ :=
    ne_top_of_le_ne_top (lintegral_bdryM_core_lt_top hγ hγ2 P' X A hX hA hXA left hη hη4).ne
      (lintegral_mono fun ω' => measure_mono inter_subset_right)
  have hIfin : Iinf ≠ ⊤ := by
    rw [hIe]
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top hc1) hWfin
  have hlim := tendsto_palm_side hγ hγ2 hsel ha P' V hV P'' Y'' hW R Γ hΓ hΓ1 U hη hη4 hδ hδη
    hJm
  have he2 : (0 : ℝ≥0∞) < e / 2 := ENNReal.div_pos he.ne' ENNReal.ofNat_ne_top
  have hsum : e / 2 + e / 2 = e := ENNReal.add_halves e
  rw [← hIe]
  filter_upwards [(ENNReal.tendsto_nhds hIfin).1 hlim (e / 2) he2, hTr (e / 2) he2] with L hL1 hL2
  have hL1' := hL1
  simp only [mem_Icc] at hL1'
  constructor
  · calc _ ≤ _ := hL2.1
      _ ≤ (Iinf + e / 2) + e / 2 := add_le_add hL1'.2 (le_refl (e / 2))
      _ = Iinf + e := by rw [add_assoc, hsum]
  · calc Iinf ≤ _ + e / 2 := tsub_le_iff_right.1 hL1'.1
      _ ≤ (∫⁻ ω', g1PhiD γ L R Γ Ψ left U η δ (wedgeU γ X A ω', a) ∂P' + e / 2) + e / 2 :=
          add_le_add hL2.2 le_rfl
      _ = _ := by rw [add_assoc, hsum]

end ZqC
end Thm18Asm
end QuantumZipper

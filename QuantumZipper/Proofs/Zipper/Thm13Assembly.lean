import QuantumZipper.Proofs.Zipper.Thm13AssemblyStmt
import QuantumZipper.Proofs.Thm14.FromThm13
import QuantumZipper.Proofs.Thm14.WeldingData
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.LQG.RevCouplingReg
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

/-!
# Theorem 1.3, top-level conditional assembly (THM13-ASM)

`theorem1_3_of_nodes`: Theorem 1.3 (Sheffield arXiv:1012.4797, Theorem 1.3, proof in §5.4,
pp. 70–72) from the not-yet-proved E/F nodes of `blueprint/E_BRANCH_BLUEPRINT.md`, stated in
`Thm13AssemblyStmt.lean`. The three clauses of `theorem1_3` are obtained as follows.

* **Clause 1** (every non-tip point of `η_T` has preimages `x₋ < 0 < x₊`; STATEMENT_SPEC A10,
  SECTION5 F2 step (5)) is proved here, unconditionally: `RS.rohdeSchrammSimple` makes the hull a
  simple curve a.s. (`Thm14FromThm13.ae_isSimpleCurveHull_revHull`), `CaraR.revMapCaratheodory`
  gives the Carathéodory extension `F`, and the deterministic `clause1_of_car` reads the two
  preimages off `F` (surjectivity onto `ℍ̄`, the real-image criterion, the welding homeomorphism
  and the intermediate value theorem; own elementary argument).
* **Clause 2** (lengths agree, base pair included, D9) is the chain
  E4 → E5 → E6 (local) → E6 (`configLawFull`) → F1 → F2 of node hypotheses.
* **Clause 3** (`ν` charges open intervals, D13) is the proved B3(a),
  `RevCouplingReg.revCouplingBoundaryMeasureRegular`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm13Asm

open Thm14WeldingData in
/-- **Clause 1, deterministic.** If `F` is the Carathéodory extension of `revMap W T`, every
point `z` of the hull other than the tip `revMapBdry W T 0` is the boundary image of some
`x₋ < 0` and some `x₊ > 0`. -/
theorem clause1_of_car {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt W T F) :
    ∀ z ∈ revHull W T, z ≠ revMapBdry W T 0 →
      ∃ xm xp : ℝ, xm < 0 ∧ 0 < xp ∧ revMapBdry W T xm = z ∧ revMapBdry W T xp = z := by
  intro z hz hz0
  simp only [revMapBdry_eq_of_car hF] at hz0 ⊢
  obtain ⟨w, hw, hwz⟩ := hF.2.2.1 (WeldingUniqueness.wu_H_subset_Hbar hz.1)
  have hwR : w.im = 0 := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ w.im from hw) with h | h
    · exact h.symm
    · exfalso
      exact hz.2 ⟨w, h, by rw [← hF.1 h]; exact hwz⟩
  have hwe : w = (w.re : ℂ) := Complex.ext rfl (by simp [hwR])
  set x := w.re with hxdef
  have hFx : F x = z := by rw [← hwe]; exact hwz
  have him : (F x).im ≠ 0 := by rw [hFx]; exact ne_of_gt hz.1
  have h2 : ¬ (x ≤ zeroMinus W T ∨ zeroPlus W T ≤ x) := (hF.2.2.2.2.2.1 x).not.1 him
  push Not at h2
  have hx0 : x ≠ 0 := fun h => hz0 (by rw [← hFx, h])
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · have hmem : x ∈ Icc (zeroMinus W T) 0 := ⟨h2.1.le, hneg.le⟩
    obtain ⟨hφ0, hφF⟩ := weldingHom_mem_of_car hF hmem
    refine ⟨x, weldingHom W T x, hneg, lt_of_le_of_ne hφ0 fun h => hz0 ?_, hFx, ?_⟩
    · rw [← hFx, ← hφF, ← h]
    · rw [hφF, hFx]
  · have hIcc : x ∈ Icc (weldingHom W T 0) (weldingHom W T (zeroMinus W T)) := by
      rw [weldingHom_zero, hF.2.2.2.2.1]; exact ⟨hpos.le, h2.2.le⟩
    obtain ⟨s, hs, hφs⟩ := intermediate_value_Icc' (WeldingUniqueness.zeroMinus_nonpos W T)
      (continuousOn_weldingHom_of_car hF) hIcc
    have hFs : F s = F x := by rw [← hφs, (weldingHom_mem_of_car hF hs).2]
    refine ⟨s, x, lt_of_le_of_ne hs.2 fun h => ?_, hpos, by rw [hFs, hFx], hFx⟩
    rw [h, weldingHom_zero] at hφs
    exact hx0 hφs.symm

/-- **Clause 1, almost surely** (unconditional: Rohde–Schramm simplicity and the Carathéodory
extension are proved). -/
theorem ae_clause1 {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 4) {T : ℝ} (hT : 0 < T)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ z ∈ revHull (drive κ B ω) T, z ≠ revMapBdry (drive κ B ω) T 0 →
      ∃ xm xp : ℝ, xm < 0 ∧ 0 < xp ∧
        revMapBdry (drive κ B ω) T xm = z ∧ revMapBdry (drive κ B ω) T xp = z := by
  filter_upwards [Thm14FromThm13.ae_isSimpleCurveHull_revHull RS.rohdeSchrammSimple hκ0 hκ4 hT
    P B hB, hB.cont, hB.eval_zero_ae_eq_zero] with ω hsimple hc h0
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  obtain ⟨F, hF⟩ := CaraR.revMapCaratheodory _ hWc hW0 T hT hsimple
  exact clause1_of_car hF

end Thm13Asm
end QuantumZipper

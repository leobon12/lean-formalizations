import QuantumZipper.Proofs.Zipper.LocLenE6NodeCore
import QuantumZipper.Proofs.Zipper.LocLenE6NodeId
import QuantumZipper.Proofs.Zipper.LocLenE6NodeReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R5b (D75): the E6 node with open arcs

Open-arc copy of `E6.e6NodeStmtRich_of_nodes_nm` (E6MeasNode.lean:125): Sheffield
arXiv:1012.4797, §5.4, proof of Thm 1.8 (3), pp. 70–72 (the quantum wedge is stationary under
`Z^LEN`), B-P arXiv:2404.16642 Prop 8.20. The chain is the old one with
`zipLenDown ↦ zipLenDownArc`: the abstract core `e6_concrete_rich_nmZ` (LocLenE6NodeCore.lean),
E6-ID `e6_idLoc_richArc` (LocLenE6NodeId.lean), the auxiliary Palm setup
`E6.exists_e6PalmSetup`, and the B5 locality with the deterministic regularity set
`RegDetArc` (`pstar_regDetArc`, LocLenE6NodeReg.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.LocLen
open R5c

open B2 E1 D3Plus E6

/-- **The open-arc E6 node** from `HitScaleZipArcStmt` and the three E6 inputs (copy of
`E6.e6NodeStmtRich_of_nodes_nm`). -/
theorem e6NodeStmtRichArc_of_nodes (hSZ : HitScaleZipArcStmt)
    (hLC : LenCollidedAllArcStmt) (hCZ : CanonZipRawAllArcStmt) (hPR : E6PalmRegArcStmt) :
    E6NodeStmtRichArc := by
  intro hE5 κ Ω' _ P' _ Y B' hP ℓ₁ hℓ R Γ hΓ hΓ1
  obtain ⟨hκ, hκ4, hY, hB', hYB⟩ := hP
  obtain ⟨Ω, _, P, B, X, hPp, hS⟩ := exists_e6PalmSetup hκ hκ4
  have := hPp
  set T : ℝ := 4 / (4 - κ) with hTdef
  obtain ⟨hT, hB, hX, hind⟩ : 0 < T ∧ IsBrownianReal B P ∧ IsFreeGFFModConstH X P ∧
      IndepFun (pathOf B) X P := ⟨hS.2.2.1, hS.2.2.2.1, hS.2.2.2.2.1, hS.2.2.2.2.2.1⟩
  have hTδ : 4 * (1 : ℝ) ^ 2 / (4 - κ) ≤ T := by rw [hTdef]; norm_num
  obtain ⟨hReg', hLoc⟩ := pstar_regDetArc hSZ κ P' Y B' ⟨hκ, hκ4, hY, hB', hYB⟩ ℓ₁ hℓ
  have hId := e6_idLoc_richArc (foldedCircle (3 * Complex.I) 1) hκ hκ4 hT hB hX hind
    (hLC κ T P B X hκ hκ4 hT hB hX hind) (hCZ κ T P B X hκ hκ4 hT hB hX hind) 1 ℓ₁ hℓ
  exact e6_concrete_rich_nmZ hE5 (zipLenDownArc (Real.sqrt κ) ℓ₁) κ T P B X _ hS P' Y B' hY
    hB' hYB 1 one_pos hTδ ℓ₁ hℓ (RegDetArc (Real.sqrt κ) κ ℓ₁)
    (aemeasurable_locRich_pstar ⟨hκ, hκ4, hY, hB', hYB⟩) hReg' (hPR κ T P B X _ hS ℓ₁ hℓ) hId
    hLoc R Γ hΓ hΓ1

end QuantumZipper.LocLen

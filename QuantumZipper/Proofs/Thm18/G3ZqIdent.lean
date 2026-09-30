import QuantumZipper.Proofs.Thm18.G3ZqBody
import QuantumZipper.Proofs.Thm18.G2Close
import QuantumZipper.Proofs.Thm18.G2PalmMain
import QuantumZipper.Proofs.Thm18.R18G3TFreeId

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (10): the plain limit is the wedge law (identification of the free joint limit)

`G3ZqPathSmallUStmt` compares the map functional with the limit `c` of the **plain** free joint
zoom probabilities. The plain engine (`g2FixMixStmt_holds`) only asserts that some limit laws
exist. Rerunning its proved chain with the explicit wedge law `g2WedgeLaw P' Y'` (the law used
by the agreement node `g2RootXAgreeStmt_of_nodes`) gives the plain mixing body with that law
(`plainBody_wedgeLaw`), hence `c = 𝒲(s) · 𝒲(t)` for the wedge law `𝒲` (`plain_limit_eq`); the
map body (`g3FixMixBody_map`, G3ZqBody) has the same law.

Own bookkeeping; all inputs are the committed plain G2 nodes (Sheffield, arXiv:1012.4797,
proof of Prop. 5.5, pp. 65–66).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

/-- **The plain mixing body with the explicit wedge law.** -/
theorem plainBody_wedgeLaw {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample)
    (hW : IsQuantumWedge γ γ Y' P') :
    R18.G3FixMixBody (g2WedgeLaw P' Y') (g2WedgeLaw P' Y') (g3PalmLaw γ) (g3X γ) (g3R γ)
      (g3Uf γ) (g3Vf γ) := by
  have hI : D3Plus.D3PlusIStmtRich := D3Plus.d3PlusIRich_of_N2 D3Plus.d3PlusIN2RichStmt_holds
  have hRG := g2PalmRegGoodStmt_of_good (g2PalmGoodStmt_holds hγ hγ2)
  have hCX := g2RootXCondStmt_of_cutLoc (g2RootXCutLocStmt_holds hγ hγ2)
  have hCR := g2RootRCondStmt_of_loc (g2RootRCutLocStmt_of_len (g2RootRCutLenLocStmt_holds hγ hγ2))
  have hFX := g2RootXFixStmt_of_model hI
    (g2RootXModelStmt_of_agree hγ hγ2 (g2RootXAgreeStmt_of_nodes hγ hγ2 hW hRG hCX))
  have hFR := g2RootRFixStmt_of_model hI
    (g2RootRModelStmt_of_agree hγ hγ2 (g2RootRAgreeStmt_of_nodes hγ hγ2 hW hRG hCR))
  obtain ⟨hSX, hSR⟩ := g2RootLenSmooth_of_disint hγ hγ2 (g2RootXDisintStmt_holds hγ hγ2)
    (g2RootRDisintStmt_holds hγ hγ2)
  have hcX := g2RootXCutStmt_of_palm hγ hγ2 (g2RootXPalmIdStmt_holds hγ hγ2) hFX
  have hcR := g2RootRCutStmt_of_palm hγ (g2RootRPalmIdStmt_holds hγ hγ2) hFR
  exact g3FixMixBodyZ_of_len (Z := zoomLaw γ) (Z' := zoomLaw γ) hγ hγ2
    (g2FixMixLenX_of_root hγ hγ2 (g2FixMixRootXStmt_of_cut hSX hcX))
    (g2FixMixLenR_of_root hγ hγ2 (g2FixMixRootRStmt_of_cut hSR hcR))

/-- **The limit of the plain free joint zoom probabilities is `𝒲(s) 𝒲(t)`.** -/
theorem plain_limit_eq {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω']
    (P' : Measure Ω') [IsProbabilityMeasure P'] (Y' : Ω' → FieldSample)
    (hW : IsQuantumWedge γ γ Y' P') {s t : Set LawD} (hs : s ∈ lawCyl) (ht : t ∈ lawCyl) {c : ℝ}
    (hc : Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter
      (𝓝 c)) :
    c = (g2WedgeLaw P' Y').real s * (g2WedgeLaw P' Y').real t :=
  tendsto_nhds_unique hc
    (R18.g3FreeJointLim_of_body hγ hγ2 (plainBody_wedgeLaw hγ hγ2 P' Y' hW) s hs t ht)

end G3Zq
end Thm18Asm
end QuantumZipper

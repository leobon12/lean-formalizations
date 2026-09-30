import QuantumZipper.Proofs.Thm18.G1FrostAlphaVar
import QuantumZipper.Proofs.Thm18.G1FrostAlphaKoebe
import QuantumZipper.Proofs.Thm18.G1PsiExtMain
import QuantumZipper.Proofs.Complex.KernelChordRight
import QuantumZipper.Proofs.Complex.UniformizerTopo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FROST-B, part 4: `G1PsiExtStmt` from the Hölder input alone

* **`pushFrostmanα_of_side`**: for every simple chord, every side and every normalized
  uniformizer `φ`, each continuous extension `ψe` of `φ⁻¹` to `Hbar` satisfies
  `PushFrostmanα koebeFrostExp ψe` (the Koebe-type bound `fcFrostmanα_of_univalent`,
  G1FrostAlphaKoebe.lean, plus `pushFrostmanα_of_fc`). Deterministic, every simple chord.
* **`sideFrostDetStmtα_holds`**: the deterministic `α`-Frostman statement, `α = koebeFrostExp`.
* **`psiBoundsGoodStmt_of_holder_α`**: `PsiBoundsGoodStmt γ (SideHolderGood γ)`, via the
  exponent-general potential/variance toolkit (`pushFamBounds_of_regα`, G1FrostAlphaVar.lean).
* **`g1PsiExtStmt_of_holder_α : G1GoodBMStmt SideHolderGood → G1PsiExtStmt`**: node G1 now
  rests on the SLE Hölder-domain input only (the Frostman input `SideFrostDetStmt` at the fixed
  exponent `1/3` is no longer needed).

Own bookkeeping (the same assembly as `psiBoundsGoodStmt_of_reg`, G1PathCoord.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

/-- The sides of a simple chord are open. -/
theorem isOpen_sideDom_α {η : ℝ → ℂ} (hη : IsSimpleChord η) (left : Bool) :
    IsOpen (sideDom η left) := by
  cases left
  · exact CA.Kernel.isOpen_rightComponent_qz hη
  · exact CA.Uniformizer.isOpen_leftComponent hη

/-- **Frostman bound for the side maps** (deterministic, every simple chord). -/
theorem pushFrostmanα_of_side {η : ℝ → ℂ} (hη : IsSimpleChord η) {left : Bool} {φ : ℂ → ℂ}
    (hφ : IsNormalizedUniformizer (sideDom η left) φ) {ψe : ℂ → ℂ}
    (hc : ContinuousOn ψe Hbar) (heq : EqOn (invFunOn φ (sideDom η left)) ψe H) :
    PushFrostmanα koebeFrostExp ψe := by
  have hp := G1.invFunOn_props (isOpen_sideDom_α hη left) hφ
  have hd : DifferentiableOn ℂ ψe H := hp.1.congr fun z hz => (heq hz).symm
  have hi : InjOn ψe H := (G1.injOn_invFunOn_of_uniformizer hφ).congr heq
  exact pushFrostmanα_of_fc koebeFrostExp_pos.le hc (fcFrostmanα_of_univalent hc hd hi)

/-- **`PsiBoundsGoodStmt` for the Hölder predicate alone.** -/
theorem psiBoundsGoodStmt_of_holder_α (γ : ℝ) : PsiBoundsGoodStmt γ (SideHolderGood γ) := by
  intro a _ hsc hg left φ hφ
  obtain ⟨ψe, hc, heq, hH⟩ := hg left φ hφ
  obtain ⟨ψc, -, hcc, hcH, heqc⟩ := psiExtContStmt_holds _ hsc left φ hφ
  have hsame : EqOn ψc ψe Hbar :=
    eqOn_Hbar_of_continuousOn_of_eqOn_H hcc hc fun z hz => (heqc hz).symm.trans (heq hz)
  have hmaps : MapsTo ψe Hbar Hbar := fun z hz => (hsame hz) ▸ hcH hz
  obtain ⟨β, hβ, hB⟩ := pushFamBounds_of_regα koebeFrostExp_pos koebeFrostExp_le_one hc hmaps hH
    (pushFrostmanα_of_side hsc hφ hc heq)
  exact ⟨ψe, β, hβ, hc, heq, hB⟩

/-- **Node G1 from the Hölder-domain input alone.** -/
theorem g1PsiExtStmt_of_holder_α (hH : G1GoodBMStmt SideHolderGood) : G1PsiExtStmt :=
  g1PsiExtStmt_of_coord SideHolderGood (g1PathCoordGoodStmt_of_bm hH)
    fun γ _ _ => psiBoundsGoodStmt_of_holder_α γ

end G1RC
end Thm18Asm
end QuantumZipper

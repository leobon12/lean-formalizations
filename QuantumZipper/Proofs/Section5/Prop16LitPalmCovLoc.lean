import QuantumZipper.Proofs.Section5.Prop16LitFixCov
import QuantumZipper.Proofs.Section5.Prop16PalmRep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: locality of the chart coordinate-change identity

`Prop16Lit.litIdent_congr`: the identity of clause (1) of `Prop16LitCovStmt` at a point `t`
(`(μ_{zoomFieldLit}|_{B(0,r)∩ℍ}).map ψ = μ_{zoomField}|_{ψ(B(0,r)∩ℍ)}`) only depends on the field
through its dyadic folded circle averages inside an open set `W ⊇ D`. In particular it can be read
from the rebuilt field `repFam D a b 0 y` of the local readings `y` (`Prop16PalmRep.lean`).

The literal zoom reads the translate at chart images of small circles in `B(0,r) ∩ ℍ`, which lie in
a compact subset of `D − t` (`circAgree_zoomFieldLit`); the straight zoom is
`circAgree_zoomFree_nc`. Own elementary argument (the proof of `Prop16Area.G.fcAgree_translate`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Lit

open Prop16Asm

/-- The chart identity (clause (1) of `Prop16LitCovStmt`) for a field `Y` at the point `t`. -/
def litIdent (γ C : ℝ) (D : Set ℂ) (ψ : ℂ → ℂ) (r : ℝ) (Y : FieldSample) (t : ℝ) : Prop :=
  (qAreaMeasureOn γ (zoomFieldLit γ C Y t ψ) (ball 0 r ∩ H)).map ψ =
    (qAreaMeasureOn γ (zoomField γ C Y t) (zoomDomain D t)).restrict (ψ '' (ball 0 r ∩ H))

/-- **Locality of the literal zoom.** -/
theorem circAgree_zoomFieldLit {W : Set ℂ} (hWo : IsOpen W) {x x' : FieldSample}
    (h : Prop16Area.G.CircAgree W x x') (γ C t : ℝ) {ψ : ℂ → ℂ} (hψm : Measurable ψ) {r : ℝ}
    (hψc : ContinuousOn ψ (ball 0 r))
    (hψ : ∀ u ∈ ball (0 : ℂ) r ∩ H, ψ u ∈ H ∧ ψ u + (t : ℂ) ∈ W) :
    Prop16Area.G.CircAgree (ball 0 r ∩ H) (zoomFieldLit γ C x t ψ)
      (zoomFieldLit γ C x' t ψ) := by
  have hT := (Prop16Area.G.fcAgree_translate hWo h t).circAgree
  have hWt : IsOpen ((fun z => z + (t : ℂ)) ⁻¹' W) :=
    hWo.preimage (continuous_id.add continuous_const)
  intro n k z hz hsub
  have hKc : IsCompact (closedBall (dyadicRoundC n z) (radius k) ∩ Hbar) :=
    Prop16Area.G.isCompact_closedBall_inter_Hbar _ _
  have hKB : closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ ball 0 r := fun u hu => (hsub hu).1
  have hψK : IsCompact (ψ '' (closedBall (dyadicRoundC n z) (radius k) ∩ Hbar)) :=
    hKc.image_of_continuousOn (hψc.mono hKB)
  have hev : evalReg (translate x (t : ℂ))
        ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) =
      evalReg (translate x' (t : ℂ)) ((foldedCircle (dyadicRoundC n z) (radius k)).map ψ) := by
    refine Prop16Area.G.evalReg_eq_of_circAgree hWt hT hψK ?_ ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact (hψ u (hsub hu)).2
    · refine (ae_map_iff hψm.aemeasurable
        (hψK.isClosed.measurableSet.inter isClosed_Hbar.measurableSet)).2 ?_
      filter_upwards [Prop16Area.G.ae_fc_mem_ball_inter
        (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k)] with u hu
      exact ⟨⟨u, hu, rfl⟩, show (0 : ℝ) ≤ (ψ u).im from le_of_lt (hψ u (hsub hu)).1⟩
  simp only [zoomFieldLit, addConst, coordChange, hev]

end Prop16Lit

end QuantumZipper

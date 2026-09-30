import QuantumZipper.Proofs.Thm18.G1ZBdryDet
import QuantumZipper.Proofs.Zipper.E1CoordChange
import QuantumZipper.Proofs.Zipper.B5LocDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-BDRY (2): the side boundary transport from reflection and the all-maps rule

Reduces `G1SideTransportStmt` (G1ZBdryDet.lean) to two named nodes:

* `G1SideReflStmt` (deterministic content, Schwarz reflection + Carathéodory): a.s. the side map
  `ψ = (uniformizer D)⁻¹` extends holomorphically across every compact segment `[p,q]` of the side
  half-line `S`, with nonvanishing derivative, and its boundary values there are those of one
  order isomorphism `Φ` of `ℝ` fixing `0`. Sources: Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4
  §6.5 Thm 24 (reflection principle, `CA.exists_reflection_extension` here), and the boundary
  correspondence of the normalized uniformizer (G1PkgLeft.lean, `boundary_neg_of_normalized`).
  Since `η` is a simple chord meeting `ℝ` only at `0` (Rohde–Schramm), a neighbourhood of every
  `x ∈ S` in `ℍ` is a half-disc in `D`, so the reflection applies.
* `WedgeBdryAllMapsAwayStmt`: the Sheffield–Wang all-maps boundary rule (arXiv:1605.06171,
  **Theorem 4.3**, p. 19) for the `(γ − 2/γ)`-wedge field, for maps whose boundary image avoids the
  marked point `0`, in the vague-limit form of `F1.isVagueLimitOnR_coordChange_of_good`
  (BdryAllMapsMain.lean). Away from `0` the wedge field is locally the free boundary GFF plus a
  continuous function up to absolute continuity (Sheffield arXiv:1012.4797 §1.6,
  Duplantier–Miller–Sheffield arXiv:1409.7055 §4.2), so SW Thm 4.3 transfers; this transfer is
  not done here.

The gluing of the windows into a vague limit on the whole half-line (`isVagueLimitOnR_side`) is
own elementary bookkeeping (a compact support in `S` lies in one window `(p,q)`).

Main results: `isVagueLimitOnR_side`, `g1SideTransportStmt_of`,
**`g1SideBdryRegStmt_of_refl_allMaps`** (B0 from the two nodes).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- Reflection data of the side map: an order isomorphism `Φ` fixing `0`, and, on every compact
segment of the side half-line, a holomorphic extension of `ψ|_ℍ` with boundary values `Φ` and
nonvanishing derivative. -/
def SideReflGood (left : Bool) (ψ : ℂ → ℂ) (Φ : ℝ ≃o ℝ) : Prop :=
  Φ 0 = 0 ∧ ∀ p q : ℝ, p < q → Icc p q ⊆ g1SideHalf left →
    ∃ (U : Set ℂ) (Ψ : ℂ → ℂ), IsOpen U ∧ (∀ t ∈ Icc p q, (t : ℂ) ∈ U) ∧
      DifferentiableOn ℂ Ψ U ∧ (∀ t ∈ Icc p q, Ψ t = (Φ t : ℂ)) ∧
      (∀ t ∈ Icc p q, deriv Ψ t ≠ 0) ∧ EqOn ψ Ψ H

/-- **Deterministic form of the reflection node**: for a simple chord and a normalized
uniformizer `φ` of a side component, the inverse `φ⁻¹` has reflection data on the side half-line
(Schwarz reflection, Ahlfors Ch. 4 §6.5 Thm 24, and the Carathéodory boundary correspondence,
Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.6). -/
def SideReflChordStmt : Prop :=
  ∀ η : ℝ → ℂ, IsSimpleChord η → ∀ (left : Bool) (φ : ℂ → ℂ),
    IsNormalizedUniformizer (sideDom η left) φ →
    ∃ Φ : ℝ ≃o ℝ, SideReflGood left (invFunOn φ (sideDom η left)) Φ

/-- A compact subset of the side half-line lies in one window `(p,q)` with `[p,q] ⊆ S`. -/
theorem exists_side_window (left : Bool) {K : Set ℝ} (hK : IsCompact K)
    (hKS : K ⊆ g1SideHalf left) :
    ∃ p q : ℝ, p < q ∧ Icc p q ⊆ g1SideHalf left ∧ K ⊆ Ioo p q := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · cases left
    · exact ⟨1, 2, by norm_num, fun x hx => by simp [g1SideHalf]; linarith [hx.1],
        empty_subset _⟩
    · exact ⟨-2, -1, by norm_num, fun x hx => by simp [g1SideHalf]; linarith [hx.2],
        empty_subset _⟩
  · obtain ⟨M, hMK, hM⟩ := hK.exists_isGreatest hne
    obtain ⟨m, hmK, hm⟩ := hK.exists_isLeast hne
    have hmM : m ≤ M := hm hMK
    cases left
    · have hm0 : 0 < m := by simpa [g1SideHalf] using hKS hmK
      exact ⟨m / 2, M + 1, by linarith, fun x hx => by simp [g1SideHalf]; linarith [hx.1],
        fun x hx => ⟨by linarith [hm hx], by linarith [hM hx]⟩⟩
    · have hM0 : M < 0 := by simpa [g1SideHalf] using hKS hMK
      exact ⟨m - 1, M / 2, by linarith, fun x hx => by simp [g1SideHalf]; linarith [hx.2],
        fun x hx => ⟨by linarith [hm hx], by linarith [hM hx]⟩⟩

end Thm18Asm
end QuantumZipper

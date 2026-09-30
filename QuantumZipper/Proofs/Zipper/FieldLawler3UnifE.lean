import QuantumZipper.Proofs.Zipper.FieldLawler3UnifC
import QuantumZipper.Proofs.Zipper.FieldLawler3SymHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-UNIF (E): `FL3Unif (hullComp η) F` for a crosscut `η`

`fl3u_FL3Unif_exists`: for a crosscut `η` of `ℍ` with feet `a ≠ b` there is `F` with
`FL3Unif (hullComp η) F` (the input of `fl3Sym_excR_symm`), together with its inverse `Φ`
(continuous on `ℍ̄`, `F ∘ Φ = id` on `ℍ̄`, `Φ ∘ F = id` on `closure H_η`). Direct from
`fl3u_conformal_exists` (Carathéodory's theorem in the Jordan case, Pommerenke 1992, Thm 2.6).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

/-- **FL3-UNIF: a uniformization of `H_η` with boundary correspondence.** -/
theorem fl3u_FL3Unif_exists {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a ≠ b) :
    ∃ F Φ : ℂ → ℂ, FL3Unif (hullComp η) F ∧ BijOn F (hullComp η) H ∧
      (∀ p ∈ closure (hullComp η), F p ∈ Hbar ∧ Φ (F p) = p) ∧ (∀ z ∈ Hbar, F (Φ z) = z) ∧
      ContinuousOn Φ Hbar ∧ Function.Injective (fun x : ℝ => Φ x) ∧
      range (fun x : ℝ => Φ x) = frontier (hullComp η) ∧
      Tendsto Φ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
  obtain ⟨F, Φ, hbij, hd, hc, hFΦ, hΦF, hre, hinf, -, hΦc, hΦi, hΦr, hΦinf⟩ :=
    fl3u_conformal_exists hη ha hb hab
  refine ⟨F, Φ, ⟨lwExc_hullComp_isOpen hη, hd, hbij.mapsTo, hc, hre, ?_, hinf⟩, hbij, hFΦ, hΦF,
    hΦc, hΦi, hΦr, hΦinf⟩
  intro p hp q hq h
  rw [← (hFΦ p (frontier_subset_closure hp)).2, ← (hFΦ q (frontier_subset_closure hq)).2, h]

end FieldLawler
end QuantumZipper

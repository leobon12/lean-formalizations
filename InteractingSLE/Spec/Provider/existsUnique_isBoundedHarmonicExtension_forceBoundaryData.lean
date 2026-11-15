import InteractingSLE.Frozen.Spec.forceBoundaryData
import InteractingSLE.Frozen.Spec.forceJumpSet
import InteractingSLE.Frozen.Spec.IsBoundedHarmonicExtension
import InteractingSLE.Impl.ForceBoundaryData

/-!
# Provider for the frozen anchor `InteractingSLE/Frozen/Spec/existsUnique_isBoundedHarmonicExtension_forceBoundaryData.lean`

Quarantined while that anchor is DRAFT_SORRY: only its frozen file and audit files may import this module
(lean-orchestrator draft quarantine). Packet SEAL-COMP.

## Proof
The landed implementation `InteractingSLE.Impl.existsUnique_isBoundedHarmonicExtension_forceBoundaryData`
proves the same statement for the structure-based definitions of ARCH-2's audited candidate (C2-v1).
The frozen definitions (FREEZE-PREP rewrite, R22) take the weights `ρL ρR` as data binders instead of a
`ForceWord`; the structure-based boundary data reads only the weights of the word, never its positions.
So for the force word `forceWordOfWeights ρL ρR` with all positions `0` (trivially ordered),
`Impl.forceBoundaryData κ (forceWordOfWeights ρL ρR) vL vR` is definitionally
`forceBoundaryData κ ρL ρR vL vR`, and `Impl.forceJumpSet`, `Impl.IsBoundedHarmonicExtension` are
definitionally the frozen `forceJumpSet`, `IsBoundedHarmonicExtension`. The provider export is the
implementation theorem at that word.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace InteractingSLE

namespace Spec

namespace Provider

/-- The ordered force word with weights `(ρL; ρR)` and all marks at `0`. Only its weights enter the
boundary data, so it transports the implementation theorem to the frozen data-binder form. -/
def forceWordOfWeights {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Impl.ForceWord where
  nL := nL
  nR := nR
  xL := fun _ => 0
  xR := fun _ => 0
  ρL := ρL
  ρR := ρR
  antitone_xL := fun _ _ _ => le_rfl
  xL_nonpos := fun _ => le_rfl
  monotone_xR := fun _ _ _ => le_rfl
  xR_nonneg := fun _ => le_rfl

theorem impl_forceBoundaryData_forceWordOfWeights (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    Impl.forceBoundaryData κ (forceWordOfWeights ρL ρR) vL vR = forceBoundaryData κ ρL ρR vL vR :=
  rfl

theorem impl_forceJumpSet_forceWordOfWeights {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    Impl.forceJumpSet (forceWordOfWeights ρL ρR) vL vR = forceJumpSet vL vR :=
  rfl

theorem impl_isBoundedHarmonicExtension_iff (g : ℝ → ℝ) (S : Set ℝ) (u : ℂ → ℝ) :
    Impl.IsBoundedHarmonicExtension g S u ↔ IsBoundedHarmonicExtension g S u :=
  Iff.rfl

/-- Provider of the frozen companion theorem of Theorem 1.1
(`InteractingSLE.existsUnique_isBoundedHarmonicExtension_forceBoundaryData`), with exactly its type (arguments implicit, so that the
frozen anchor's sealed body is the bare `by exact` the checker allows). -/
theorem existsUnique_isBoundedHarmonicExtension_forceBoundaryData {κ : ℝ} {nL nR : ℕ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR)
        (forceJumpSet vL vR) u ∧
      ∀ v : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR vL vR)
        (forceJumpSet vL vR) v → EqOn v u QuantumZipper.H := by
  obtain ⟨u, hu, huniq⟩ :=
    Impl.existsUnique_isBoundedHarmonicExtension_forceBoundaryData κ (forceWordOfWeights ρL ρR)
      vL vR
  rw [impl_forceBoundaryData_forceWordOfWeights, impl_forceJumpSet_forceWordOfWeights] at hu huniq
  exact ⟨u, (impl_isBoundedHarmonicExtension_iff _ _ _).1 hu,
    fun v hv => huniq v ((impl_isBoundedHarmonicExtension_iff _ _ _).2 hv)⟩

end Provider

end Spec

end InteractingSLE

import HigherDimLQGContinuity.Core.Lemma43Confine
import HigherDimLQGContinuity.Forcing.Confinement

/-!
# Discharge of the interface `Lemma43Confine` (orchestrator; ruling N23)

Q6's `lemma43_confine` carries the trigger binder `btrig` and the hypothesis `7 * ε₀ < btrig` of Part B's signature,
which the confinement does not use; the frozen interface `Lemma43Confine` (IA1's text) omits them. Instantiating
`btrig := 7 * ε₀ + 1` gives the interface.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace HigherDimLQGContinuity

/-- **Lemma 4.3(a)** as the frozen interface `Lemma43Confine` (producer: Q6's `lemma43_confine`). -/
theorem lemma43_confine_holds (d : ℕ) : Lemma43Confine d := by
  intro D E D' E' f ξ η M θ h δsep ε₀ εnet εatt aout H b v d₀ Ω cert hWD hWE hξ hη hd₀ hmis hv hvle hΩ hcollar hnet
    hsep hexc P a c hgeo ha hc hvisit
  have key := lemma43_confine d (btrig := 7 * ε₀ + 1) cert hWD hWE hξ hη hd₀ hmis hv hvle hΩ hcollar hnet
    (by linarith) hsep hexc P a c hgeo ha hc hvisit
  dsimp only at key
  obtain ⟨h1, -, h3, -, h5, h6⟩ := key
  exact ⟨h1, h3, h5, h6⟩

end HigherDimLQGContinuity

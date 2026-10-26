import SupercriticalLFPPAS.Assembly.Adapters
import SupercriticalLFPPAS.Normalizer.Window

/-!
# The all-ξ corollary, unconditional

Lemma 6.1 (`Normalizer.normalizerWindow_of`, packet L61) discharges the last input of the assembly, so the composition
`Assembly.lfpp_ae_lscTendsto_allXi_of_window` holds outright: for **every** `ξ > 0` (not only `ξ > ξ_crit`), whenever the
rescaled heat-kernel LFPP converges in probability in the lower-semicontinuous topology to some `L`, it converges almost
surely along every sequence `ε_n → 0`, for every jointly continuous family of heat versions. This corollary is not a frozen
anchor; the frozen Theorem 1.1 (`Frozen/Lfpp_ae_lscTendsto.lean`) is its restriction to `ξ > ξ_crit` and is sealed through its
own provider.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SupercriticalLFPPAS.Assembly

/-- Lemma 6.1 in the assembly's form, with its two inputs discharged: confinement (`Local.confinement_of`, from the
localized comparison and the localization approximation) and the mesh oscillation bound (`Field.meshOsc_holds`). -/
theorem normalizerWindow_holds (S : Core.Setup) : Core.NormalizerWindowStmt S :=
  Normalizer.normalizerWindow_of S (Local.confinement_of S (locCompare_holds S) Field.locApprox_holds)
    Field.meshOsc_holds

/-- **Theorem 1.1 for every `ξ > 0`** (unfrozen corollary): almost sure LSC convergence along every sequence of cutoffs,
given convergence in probability to some `L`. -/
theorem lfpp_ae_lscTendsto_allXi : Core.Lfpp_ae_lscTendstoAllXiStmt :=
  lfpp_ae_lscTendsto_allXi_of_window normalizerWindow_holds

end SupercriticalLFPPAS.Assembly

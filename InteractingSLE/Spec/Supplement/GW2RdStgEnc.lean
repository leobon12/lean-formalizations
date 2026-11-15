/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdRootLink

/-!
# GW2's stage identity: one record for a stage-start history

Packet PROVE-GW2-RELDET, ruling R106. GB6's engine (`Q3Stop.HasRelSafe`, `Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`)
conditions on ONE record `rec : Ω → RecData`. At stage `n` the conditioning is the stage-start history of ROOT2's
source: the counterflow record and the `n` stopped canonical pieces (`GW2TipSystem.stageMap`, valued in
`RecData × (Fin n → RecData)`). Both are uncountable standard Borel spaces, so they are Borel isomorphic
(`PolishSpace.measurableEquivOfNotCountable`), and the engine runs unchanged on the encoded history:

* `stageEnc n : RecData × (Fin n → RecData) ≃ᵐ RecData`;
* `stageEncRec`: the encoded stage-start history of ROOT2's source; it generates exactly the stage-start σ-algebra
  (`comap_stageEncRec`), so conditioning on it is conditioning on `c.sigma r l` (`comap_stageEncRec_sigma`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24

/-- The space of records is uncountable. -/
instance uncountable_recData : Uncountable RecData :=
  (show Function.Injective (fun x : ℝ => ((fun _ => x, 0, false) : RecData)) from
    fun _ _ h => congr_fun (congrArg Prod.fst h) 0).uncountable

/-- A record together with a finite vector of records is uncountable. -/
instance uncountable_recData_prod (n : ℕ) : Uncountable (RecData × (Fin n → RecData)) :=
  (show Function.Injective (fun r : RecData => ((r, fun _ => r) : RecData × (Fin n → RecData))) from
    fun _ _ h => congrArg Prod.fst h).uncountable

/-- **The Borel encoding of a stage-start history** (a counterflow record and `n` piece records) as one record. -/
def stageEnc (n : ℕ) : (RecData × (Fin n → RecData)) ≃ᵐ RecData :=
  PolishSpace.measurableEquivOfNotCountable not_countable not_countable

/-- The comap of an encoded map is the comap of the map. -/
theorem comap_stageEnc_comp {Ω : Type*} {n : ℕ} (f : Ω → RecData × (Fin n → RecData)) :
    MeasurableSpace.comap (fun ω => stageEnc n (f ω)) inferInstance = MeasurableSpace.comap f inferInstance := by
  change MeasurableSpace.comap (stageEnc n ∘ f) inferInstance = _
  rw [← MeasurableSpace.comap_comp, (stageEnc n).measurableEmbedding.comap_eq]

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The encoded stage-start history** of ROOT2's source at root `r` after history `l`: the counterflow record and the
`|l| + 1` stopped canonical pieces, as one record. -/
def stageEncRec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) : RecData :=
  stageEnc ((entryList l).length + 1)
    (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ (schedSpecOf r.1 l) ((entryList l).length + 1) ω)

/-- **The encoded history generates exactly the retained σ-algebra** `c.sigma r l`. -/
theorem comap_stageEncRec_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSpace.comap (stageEncRec c r l) inferInstance = c.sigma r l :=
  comap_stageEnc_comp _

/-- The encoded history is measurable for the retained σ-algebra. -/
theorem measurable_stageEncRec_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    Measurable[c.sigma r l] (stageEncRec c r l) := by
  rw [← comap_stageEncRec_sigma]
  exact comap_measurable _

/-- The decoded history is the stage-start map. -/
theorem stageEnc_symm_stageEncRec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (ω : Ω) : (stageEnc ((entryList l).length + 1)).symm (stageEncRec c r l ω) =
      stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ (schedSpecOf r.1 l) ((entryList l).length + 1) ω :=
  (stageEnc _).symm_apply_apply _

end InteractingSLE.Theorem14.GW2Rd

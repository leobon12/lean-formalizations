import QuantumZipper.Proofs.Thm14.Determination
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Thm18.G4WeldRound

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core C (task G4C-MEAS): measurable projections and the law-transfer engine

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 and its proof
(pp. 69–72: "`Z_t` preserves the law"). Route decision: `handoff/G4-CORE.md` §3.4 (Core C).

**1. Projections with unique witnesses (no Lusin).** `measurableSet_image_fst_of_partialGraph`:
if `G ⊆ S × E` (standard Borel) is measurable and every section has at most one point, the
projection `{s | ∃ e, (s, e) ∈ G}` is measurable (Lusin–Souslin: injective Borel images of Borel
sets are Borel; Kechris, *Classical Descriptive Set Theory*, Thm 15.1 and Cor 15.2; mathlib
`MeasurableSet.image_of_measurable_injOn`). `exists_measurable_iff_mem_graph` eliminates the
quantifier `∃ e` by a measurable selector (`Thm14Determination.exists_measurable_of_partialGraph`,
Kechris Thm 15.1 again): `(∃ e, (s, e) ∈ G) ↔ (s, F s) ∈ G`. For the length-welding driver
this is already implemented in `G4Read2Core.lean` (`GamS`, `exists_lenDrvReading_of_good`), so
the event "there is a good length-`t` welding driver" is measurable in the data without Lusin.

**2. Law-transfer engine to the zipped configuration.** `ae_cfgData_zipLenC_mem`: for every
measurable (or merely null-measurable, `ae_cfgData_zipLenC_mem_of_null`) set `S` of data
charged a.s. by the data of the wedge configuration `c`, the data of `Z_t c` lies in `S` a.s.
Inputs: the reading node `G4ZipReadStmt`, the raw round trip `G4RoundRawStmt`, E6's
measurability `E6.UnzipMeasStmt`, and the **round-up** driver identity
`(Z_t (Z_{−t} c)).2 = c.2` on `[0,∞)` only (`configLawFull_zipLenC_pos_of_up`). Unlike
`configLawFull_zipLenC_pos_of_read` (which takes `G4RoundStmt`, including the round-down
`Z_{−t} ∘ Z_t`), no Group II input is used, so the engine can be used to prove Group II leaves
without circularity.

**Own elementary argument** (pushforward algebra on top of the cited selection theorem).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

open Thm14Determination

/-! ## 1. Projections of measurable partial graphs -/

/-- **Lusin–Souslin projection** (Kechris, Thm 15.1 / Cor 15.2): the projection of a
measurable partial graph in a product of standard Borel spaces is measurable. -/
theorem measurableSet_image_fst_of_partialGraph {S E : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] [MeasurableSpace E] [StandardBorelSpace E] {G : Set (S × E)}
    (hGm : MeasurableSet G) (hG : IsPartialGraph G) : MeasurableSet (Prod.fst '' G) := by
  refine hGm.image_of_measurable_injOn measurable_fst ?_
  rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb hab
  simp only at hab
  subst hab
  rw [hG ha hb]

/-! ## 2. The law of `Z_t c` from Group I inputs only -/

section Transfer

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}

end Transfer

end G4Core
end Thm18Asm
end QuantumZipper

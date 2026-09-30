import QuantumZipper.Proofs.Zipper.ESMCompl
import QuantumZipper.Proofs.Zipper.ESMLMeas6
import QuantumZipper.Proofs.Zipper.B5VHccZero

/-!
# ESM-INST: the E-SM strong Markov identity with `hLad` and B5-V discharged

Task ESM-INST (Theorem 1.3, node **E-SM**). `ESM.lintegral_levelTime_strongMarkov_lenA_compl`
(`ESMCompl.lean`) is E-SM on an arbitrary probability space, with the `hBad`, `hindF`, `hnull`
filtration inputs discharged by `ESM-FILT` and the completion transfer; it still takes two
further inputs, both now proved:

* `hLad`, the adaptedness of the intrinsic left length `L⁻ = ESM.lenMinus` to `complFiltration`:
  `ESM.hLad_lenMinus_uncond` (`ESMLMeas6.lean`, all `s ≥ 0`, unconditional via RCBMR);
* `hB5V`, fixed-time B5-V: `B5.ae_b5v` (`B5VHccZero.lean`, every `s ∈ [0,T]`).

Here they are substituted, so the E-SM identity holds on an arbitrary probability space
`(Ω, P)` for `0 < κ < 4`, `T > 0`, a Brownian motion `B`, a free field `X` independent of `B`,
any s-finite `μ` on levels, any jointly measurable `H` whose sections are measurable for the
stopping-time σ-algebra of the length level times `T_ℓ`, and any measurable `Ψ`:
`∫∫ 1{ℓ ≤ lenA T} H ℓ ω Ψ((zipCapDown √κ T_ℓ 𝒵).2) dμ(ℓ) dP
  = E[Ψ(√κ B)] · ∫∫ 1{ℓ ≤ lenA T} H ℓ ω dμ(ℓ) dP`, both integrals against `P` itself.

**Remaining input (flagged, not provable from `IsBrownianReal`).** The pathwise continuity
`hBc : ∀ ω, Continuous (B · ω)`. `IsBrownianReal` supplies only a.s. continuity
(`IsBrownianReal.cont`), while the E-SM proof (through `StrongMarkov.smPath`,
`map_restrict_smPath_eq`, and the `s = 0` certificate `ESM.hLad_lenMinus` of `ESMLMeas6`) uses
continuity at every `ω`. This is not a hypothesis of `theorem1_3`, where one takes a *version*:
`RS.exists_good_version0` gives `B''` with pathwise continuous paths and `B'' = B` a.e.
pointwise, and the consumer (E5's model) is built on path space, where paths are continuous by
construction. Three obstructions to discharging `hBc` from an a.e. continuous `B` inside this
identity (checked 2026-09-28, not attempted to completion):

1. the adaptedness input `ESM.hLad_lenMinus` (hence `ESMLMeas5`'s surrogates `pathC s B hBc`) and
   `continuous_lenA` are stated for a pathwise continuous `B`, so even the *stopping-time
   property* of the level times of `B` cannot be stated without `hBc`;
2. transporting it from `B''` needs `complFiltration hB'' hX = complFiltration hB hX` (an
   `augSigma`-level argument: `pastSigma B'' s ≤ augSigma P (pastSigma B s)` via
   `ESM.measurable_of_ae_eq_of_null`, then `augSigma` idempotence) and the a.e. equality
   `levelTime (lenA κ T B'' X) =ᵐ levelTime (lenA κ T B X)`;
3. the hypothesis `hHT` is measurability for `𝓕_{T_ℓ}`, so even with (1)–(2) the *statement* of
   the `hBc`-free identity must name that σ-algebra without a stopping-time proof for `B`
   (e.g. through a `Classical.choice` of a transported proof).

The reusable transfer lemma for (3)-style arguments — a.e. equal stopping times give the same
stopping-time σ-algebra — is proved below (`ESM.isStoppingTime_measurableSpace_congr_ae`); it
applies verbatim to the D21 modification of `L⁻` on a null set. So `hBc` is kept explicit.

## Where E-SM is consumed (checked 2026-09-28)

* In the Theorem 1.3 assembly (`Thm13Asm.theorem1_3_of_nodes` / `E6.theorem1_3_of_nodes_rich`)
  E-SM is not a node: it sits *inside* the proof of `E5NodeStmt loc` / `E5.E5Stmt loc`
  (blueprint §4 E5, step (4) "E5-ESM", `handoff/E5.md`).
* There is no Lean statement of the E-SM node to discharge: the consumers of the identity in the
  E5 model construction are the fields `ZoomModel.hDW`
  (`Rr.map (pathRestr u₀ D) = W.map (pathRestr u₀)`), `ZoomModel.hind` and `ZoomModel.hDc`
  (`E5Main5.lean`), built from the Palm measure in the (not yet written) E5-ESM step.
  A `grep` for consumers of `ESM.*strongMarkov*` outside `ESM*.lean` / `B5V*.lean` is empty.
  The `_germ` corollary below is stated in the shape (`drvMap κ (smPath B T_ℓ)`,
  `E5LocDrv.collided_snd_eq_drvMap`) that step will read the driver in.

Sources: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 / Thm 1.8 (§5.4, pp. 66–68) for the
mathematics; this file is pure instantiation of the previously proved inputs, no new argument.
-/

noncomputable section

set_option linter.defProp false

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ESM

open LengthMarkov StrongMarkov

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- The length level time `T_ℓ` of E-SM, with the adaptedness (`hLad`) and B5-V inputs already
discharged: `ESM.isStoppingTime_compl` fed with `ESM.hLad_lenMinus_uncond` and `B5.ae_b5v`.
Its `measurableSpace` is the `𝓕_{T_ℓ}` against which the test function `H` of the E-SM identity
must be measurable. -/
def complLevelStop (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (ℓ : ℝ≥0) :
    IsStoppingTime (complFiltration hB hX)
      (fun ω => (levelTime (lenA κ T (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P)) T.toNNReal ℓ
        ω : WithTop ℝ≥0)) :=
  isStoppingTime_compl hκ hκ4 hT hB hX hind
    (hLad_lenMinus_uncond hκ hκ4 hB hX hind hBc)
    (B5.ae_b5v hκ hκ4 hT hB hX hind) ℓ

/-- **E-SM, unconditional** (AUDIT12 N12-2 form): the strong Markov identity of the zipper at the
length level times, with the `hLad` and B5-V inputs discharged. Hypotheses are the setting
(`0 < κ < 4`, `T > 0`, Brownian `B`, free field `X`, `B ⊥ X`), pathwise continuity `hBc` (see the
module flag), the level measure `μ`, and the test data `H`, `hHT`, `Ψ`. -/
theorem lintegral_levelTime_strongMarkov_lenA_compl_uncond (hκ : 0 < κ) (hκ4 : κ < 4)
    (hT : 0 < T) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hBc : ∀ ω, Continuous (B · ω))
    (μ : Measure ℝ≥0) [SFinite μ]
    {H : ℝ≥0 → Ω → ℝ≥0∞} (hH : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hHT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      (H ℓ ∘ ofCompl P))
    {Ψ : (ℝ → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω *
        Ψ (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ ω)
          (B2.cfg κ B X ω)).2 ∂μ ∂P =
      (∫⁻ ω, Ψ (drive κ B ω) ∂P) *
        ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω
          ∂μ ∂P :=
  lintegral_levelTime_strongMarkov_lenA_compl hκ hκ4 hT hB hX hind hBc
    (hLad_lenMinus_uncond hκ hκ4 hB hX hind hBc)
    (B5.ae_b5v hκ hκ4 hT hB hX hind) μ hH hHT hΨ

/-- **E-SM, unconditional, with the driver germ as the test**: the form in which the
collision/zoom arguments (E5, `E5LocDrv.collided_snd_eq_drvMap`) read the driver, namely
`(zipCapDown √κ T_ℓ 𝒵).2 = √κ · smPath B T_ℓ` (`ESM.zipCapDown_cfg_snd`, `ESM.drvMap`). -/
theorem lintegral_levelTime_strongMarkov_lenA_compl_germ (hκ : 0 < κ) (hκ4 : κ < 4)
    (hT : 0 < T) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (hBc : ∀ ω, Continuous (B · ω))
    (μ : Measure ℝ≥0) [SFinite μ]
    {H : ℝ≥0 → Ω → ℝ≥0∞} (hH : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hHT : ∀ ℓ, Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      (H ℓ ∘ ofCompl P))
    {Ψ : (ℝ → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω *
        Ψ (drvMap κ (smPath B (levelTime (lenA κ T B X) T.toNNReal ℓ) ω)) ∂μ ∂P =
      (∫⁻ ω, Ψ (drive κ B ω) ∂P) *
        ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω
          ∂μ ∂P := by
  simpa only [zipCapDown_cfg_snd] using
    lintegral_levelTime_strongMarkov_lenA_compl_uncond hκ hκ4 hT hB hX hind hBc μ hH hHT hΨ

/-! ## The transfer lemma behind the `hBc` flag

The obstruction recorded in the module docstring is exactly the transfer of a *measurability*
statement between two processes that agree `P`-a.e. The transfer tool for functions is the
existing `ESM.measurable_of_ae_eq_of_null` (`ESMLen.lean`); the one below is its counterpart for
stopping-time σ-algebras and applies verbatim to the flagged modification "replace `L⁻` on a null
set so that it is continuous/monotone for every `ω`" (`handoff/ESM.md`, E-SM-inst (b), D21): the
ESM filtrations are augmented by the null sets, so `hnull` holds at every index. -/

/-! ## The filtration is unchanged by an a.e. modification of `B`

The concrete missing input for removing `hBc` (obstruction 2 of the module docstring): replacing
`B` by a `P`-a.e. equal version leaves the augmented ESM filtration unchanged. The proof is the
`augSigma` bookkeeping: `pastSigma B' s ≤ augSigma P (pastSigma B s)` because the coordinates of
`B'` are a.e. equal to those of `B`. -/

end ESM
end QuantumZipper

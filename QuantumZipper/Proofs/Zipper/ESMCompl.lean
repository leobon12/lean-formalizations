import QuantumZipper.Proofs.Zipper.ESMComplBasic
import QuantumZipper.Proofs.Zipper.ESMFilt
import QuantumZipper.Proofs.Wire2

/-!
# ESM-COMPL (2/2): the E-SM strong Markov identity on an arbitrary probability space

AUDIT12 note N12-2. `Wire2.lintegral_levelTime_strongMarkov_lenA` (E-SM-inst (b) with the
length process `lenA`, decision D21) takes a filtration with `hBad`, `hindF`, `hnull`; the
filtration of `ESM.exists_filtration_ESM` has them only when the ambient σ-algebra is
`P`-complete. Here the ambient space `(Ω, mΩ, P)` is arbitrary:

* `complFiltration hB hX`: the ESM-FILT filtration `σ(X) ⊔ σ(B|[0,s]) ⊔ (null sets)` built on the
  completed space `(NullMeasurableSpace Ω P, P.completion)` (`ESM.esmFiltration`);
* `isStoppingTime_compl`: the level times `T_ℓ` are stopping times for it (given `hLad`, `hB5V`);
* **`lintegral_levelTime_strongMarkov_lenA_compl`**: the E-SM identity, with both sides
  Lebesgue integrals against the **original** `P`. `hBad`, `hindF`, `hnull` are discharged;
  the remaining inputs are `hLad` (adaptedness of `L⁻` to `complFiltration`), `hB5V` (fixed-time
  B5-V under `P`) and the pathwise continuity `hBc` already required by the source theorem.

The transfer (`ESMComplBasic`) is standard completion bookkeeping (own). Mathematics of the
identity: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 / Thm 1.8 (strong Markov property of the
driver at stopping times), via `LengthMarkov.lintegral_levelTime_strongMarkov`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ESM

open LengthMarkov StrongMarkov

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

lemma measurable_B_compl (hB : IsBrownianReal B P) (t : ℝ≥0) :
    Measurable (B t ∘ ofCompl P) :=
  aemeasurable_iff_measurable.mp (aemeasurable_completion (hB.aemeasurable t))

lemma measurable_X_compl (hX : IsFreeGFFModConstH X P) : Measurable (X ∘ ofCompl P) :=
  measurable_pi_iff.mpr (isFreeGFFModConstH_completion hX).measurable_coord

/-- **The E-SM filtration on the completed space**: `σ(X) ⊔ σ(B u, u ≤ s)` augmented by the
null sets, on `(NullMeasurableSpace Ω P, P.completion)`. -/
def complFiltration (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) :
    Filtration ℝ≥0 (NullMeasurableSpace.instMeasurableSpace : MeasurableSpace
      (NullMeasurableSpace Ω P)) :=
  esmFiltration (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P) P.completion
    (measurable_B_compl hB) (measurable_X_compl hX) fun _ hN => NullMeasurableSet.of_null hN

variable [IsProbabilityMeasure P]

/-- `hBad`, `hindF`, `hnull` for `complFiltration` (ESM-FILT on the completed space). -/
theorem complFiltration_spec (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) :
    (∀ t, Measurable[complFiltration hB hX t] (B t ∘ ofCompl P)) ∧
      (∀ t, Indep (complFiltration hB hX t)
        (MeasurableSpace.comap (smPath (fun t => B t ∘ ofCompl P) (fun _ => t))
          MeasurableSpace.pi) P.completion) ∧
      (∀ N : Set (NullMeasurableSpace Ω P), P N = 0 →
        MeasurableSet[complFiltration hB hX 0] N) :=
  esmFiltration_spec _ _ P.completion _ _ _ (isBrownianReal_completion hB).toIsPreBrownianReal
    (indepFun_completion hind)

omit [IsProbabilityMeasure P] in
lemma hB5V_compl
    (hB5V : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∀ᵐ ω ∂P, lenMinus κ B X s ω = B5.lenRHS κ T B X ω s) :
    ∀ s : ℝ≥0, (s : ℝ) ≤ T → ∀ᵐ ω ∂P.completion,
      lenMinus κ (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P) s ω =
        B5.lenRHS κ T (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P) ω s :=
  fun s hs => ae_completion_iff.2 (hB5V s hs)

/-- The length level times are stopping times of `complFiltration` (given `hLad`, `hB5V`). -/
theorem isStoppingTime_compl (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hLad : ∀ s, Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P))
    (hB5V : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∀ᵐ ω ∂P, lenMinus κ B X s ω = B5.lenRHS κ T B X ω s) (ℓ : ℝ≥0) :
    IsStoppingTime (complFiltration hB hX) (fun ω => (levelTime
      (lenA κ T (fun t => B t ∘ ofCompl P) (X ∘ ofCompl P)) T.toNNReal ℓ ω : WithTop ℝ≥0)) :=
  isStoppingTime_levelTime (continuous_lenA hT.le) (monotone_lenA hT.le)
    (adapted_lenA hT.le (Wire2.ae_mem_lenGood hκ hκ4 hT (isBrownianReal_completion hB)
      (isFreeGFFModConstH_completion hX) (indepFun_completion hind))
      (complFiltration_spec hB hX hind).2.2 hLad (hB5V_compl hB5V)) T.toNNReal ℓ

/-- **E-SM strong Markov identity on an arbitrary probability space** (AUDIT12 N12-2).
For `H ℓ` jointly measurable and `𝓕_{T_ℓ}`-measurable (for the stopping-time σ-algebra of
`complFiltration` on the completed space), any s-finite `μ` and measurable `Ψ ≥ 0`,
`∫∫ 1{ℓ ≤ lenA T} H ℓ ω Ψ((zipCapDown √κ T_ℓ 𝒵).2) dμ(ℓ) dP
  = E[Ψ(√κ B)] · ∫∫ 1{ℓ ≤ lenA T} H ℓ ω dμ(ℓ) dP`, all integrals against `P` itself. -/
theorem lintegral_levelTime_strongMarkov_lenA_compl (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hLad : ∀ s, Measurable[complFiltration hB hX s] (lenMinus κ B X s ∘ ofCompl P))
    (hB5V : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∀ᵐ ω ∂P, lenMinus κ B X s ω = B5.lenRHS κ T B X ω s)
    (μ : Measure ℝ≥0) [SFinite μ]
    {H : ℝ≥0 → Ω → ℝ≥0∞} (hH : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hHT : ∀ ℓ, Measurable[(isStoppingTime_compl hκ hκ4 hT hB hX hind hLad hB5V
      ℓ).measurableSpace] (H ℓ ∘ ofCompl P))
    {Ψ : (ℝ → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω *
        Ψ (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ ω)
          (B2.cfg κ B X ω)).2 ∂μ ∂P =
      (∫⁻ ω, Ψ (drive κ B ω) ∂P) *
        ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω
          ∂μ ∂P := by
  have hH' : Measurable (fun p : ℝ≥0 × NullMeasurableSpace Ω P => H p.1 (ofCompl P p.2)) :=
    have hs : Measurable (fun p : ℝ≥0 × NullMeasurableSpace Ω P => ofCompl P p.2) :=
      measurable_ofCompl.comp measurable_snd
    have hf : Measurable (fun p : ℝ≥0 × NullMeasurableSpace Ω P => p.1) := measurable_fst
    hH.comp (hf.prodMk hs)
  have h := Wire2.lintegral_levelTime_strongMarkov_lenA (𝓕 := complFiltration hB hX)
    hκ hκ4 hT (isBrownianReal_completion hB) (isFreeGFFModConstH_completion hX)
    (indepFun_completion hind) (fun ω => hBc (ofCompl P ω))
    (complFiltration_spec hB hX hind).1 (complFiltration_spec hB hX hind).2.1
    (complFiltration_spec hB hX hind).2.2 hLad (hB5V_compl hB5V) μ hH' hHT hΨ
  have e1 := lintegral_completion (P := P) fun ω => ∫⁻ ℓ,
    {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω *
      Ψ (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ ω)
        (B2.cfg κ B X ω)).2 ∂μ
  have e2 := lintegral_completion (P := P) fun ω => Ψ (drive κ B ω)
  have e3 := lintegral_completion (P := P) fun ω => ∫⁻ ℓ,
    {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω ∂μ
  rw [← e1, ← e2, ← e3]
  exact h

end ESM
end QuantumZipper

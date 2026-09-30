import QuantumZipper.Proofs.Zipper.SWCoreNA2Dist
import QuantumZipper.Proofs.Zipper.SWCoreNA2Unif
import QuantumZipper.Proofs.Zipper.SWCoreNA2Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-NA2: the primed distortion core (D59) for finite-parameter families

Task SWC-NA (`handoff/SW-CORE.md` §5, decision D59). For two sequences of finite-parameter families
of test measures `μ_k(q) = circM.map (Φμ k q)`, `ν_k(q) = circM.map (Φν k q)` (e.g. pushed circles
`(F q)_* fc(c q, a(q) 2^{-k})` and image circles `fc(F q (c q), a(q) 2^{-k}‖(F q)'(c q)‖)`, with
the radius factor `a(q) ∈ [1,2]` a parameter: all radii of each dyadic block), with the Kolmogorov
bounds and the variance inputs of `swcNA2_distortion_small`, almost surely:

* (i) (existence of the pushed limits, N1) for every `k` and every compact set of parameters,
  `∫ avgReg x j dμ_k(q) → evalReg x (μ_k(q))` uniformly as `j → ∞`, and `q ↦ evalReg x (μ_k q)` is
  continuous; the same for `ν_k`;
* (ii) (distortion, N2) for every box and `η > 0`, eventually in `k`,
  `sup_q |evalReg x (μ_k q) − evalReg x (ν_k q)| ≤ η`

(`swcNA2_family_core`). Sources: Sheffield–Wang arXiv:1605.06171, Lemmas 3.4–3.5 (pp. 15–16),
pathwise via Kolmogorov chaining (Duplantier–Sheffield 2011, Prop. 3.1) and Borel–Cantelli.
Own bookkeeping of the repository tools.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology Real

namespace QuantumZipper
namespace SWCore

open KolmD KolmG Thm18Asm.G1RC

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Two continuous modifications of the same process are indistinguishable. -/
theorem swcNA2_ae_eq_of_continuous [IsProbabilityMeasure P] {Y Y' : (Fin n → ℝ) → Ω → ℝ}
    (hY : ∀ ω, Continuous fun q => Y q ω) (hY' : ∀ ω, Continuous fun q => Y' q ω)
    (h : ∀ q, (fun ω => Y q ω) =ᵐ[P] fun ω => Y' q ω) :
    ∀ᵐ ω ∂P, ∀ q, Y q ω = Y' q ω := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Fin n → ℝ)
  have : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ q : D, Y q ω = Y' q ω := ae_all_iff.2 fun q => h q
  filter_upwards [hall] with ω hω q
  have := Continuous.ext_on hDd (hY ω) (hY' ω) (fun q hq => hω ⟨q, hq⟩)
  exact congrFun this q

/-- **The primed distortion core for finite-parameter families (N1 + N2).** -/
theorem swcNA2_family_core [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {Φμ Φν : ℕ → (Fin n → ℝ) → ℝ → ℂ}
    (hcμ : ∀ k, Continuous (uncurry (Φμ k))) (hcν : ∀ k, Continuous (uncurry (Φν k)))
    (hHμ : ∀ k q θ, Φμ k q θ ∈ Hbar) (hHν : ∀ k q θ, Φν k q θ ∈ Hbar)
    (hBμ : ∀ k, ∃ β' : ℝ, 0 < β' ∧ FamilyBounds (smoothFam circM (Φμ k)) β')
    (hBν : ∀ k, ∃ β' : ℝ, 0 < β' ∧ FamilyBounds (smoothFam circM (Φν k)) β') {β : ℝ} (hβ : 0 < β)
    (hμ : ∀ k, FamilyBounds (fun q => circM.map (Φμ k q)) β)
    (hν : ∀ k, FamilyBounds (fun q => circM.map (Φν k q)) β)
    (hvar : ∀ R : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k, ∀ q ∈ boxD (d := n) R,
      |kernelCov2 neumannH (circM.map (Φμ k q), circM.map (Φν k q))
        (circM.map (Φμ k q), circM.map (Φν k q))| ≤ C * (1 / 2) ^ k)
    (hmod : ∀ R : ℕ, ∃ L : ℝ, 0 ≤ L ∧ ∀ k, ∀ q ∈ boxD (d := n) R, ∀ q' ∈ boxD (d := n) R,
      |kernelCov2 neumannH (circM.map (Φμ k q), circM.map (Φμ k q'))
        (circM.map (Φμ k q), circM.map (Φμ k q'))| ≤ L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ) ∧
      |kernelCov2 neumannH (circM.map (Φν k q), circM.map (Φν k q'))
        (circM.map (Φν k q), circM.map (Φν k q'))| ≤ L * 2 ^ k * ‖q - q'‖ ^ (1 / 2 : ℝ)) :
    ∀ᵐ ω ∂P,
      (∀ k, ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn (fun j q => ∫ u, avgReg (X ω) j u ∂(circM.map (Φμ k q)))
          (fun q => evalReg (X ω) (circM.map (Φμ k q))) atTop K) ∧
      (∀ k, ∀ K : Set (Fin n → ℝ), IsCompact K →
        TendstoUniformlyOn (fun j q => ∫ u, avgReg (X ω) j u ∂(circM.map (Φν k q)))
          (fun q => evalReg (X ω) (circM.map (Φν k q))) atTop K) ∧
      (∀ k, Continuous fun q => evalReg (X ω) (circM.map (Φμ k q))) ∧
      (∀ k, Continuous fun q => evalReg (X ω) (circM.map (Φν k q))) ∧
      ∀ R : ℕ, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ q ∈ boxD (d := n) R,
        |evalReg (X ω) (circM.map (Φμ k q)) - evalReg (X ω) (circM.map (Φν k q))| ≤ η := by
  -- N1 for each `k`
  choose βμ hβμ hBμ' using hBμ
  choose βν hβν hBν' using hBν
  choose Aμ hAμc hAμV hAμU using fun k =>
    swcNA2_tendstoUniformlyOn_avgReg (hcμ k) (hHμ k) isCompact_Icc circM_compl (hβμ k) (hBμ' k) hX
  choose Aν hAνc hAνV hAνU using fun k =>
    swcNA2_tendstoUniformlyOn_avgReg (hcν k) (hHν k) isCompact_Icc circM_compl (hβν k) (hBν' k) hX
  -- N2
  obtain ⟨Yμ, Yν, hYμc, hYνc, hYμV, hYνV, hsmall⟩ := swcNA2_distortion_small hX hβ
    hμ hν hvar hmod
  have hidμ : ∀ᵐ ω ∂P, ∀ k q, Yμ k q ω = Aμ k q ω := ae_all_iff.2 fun k =>
    swcNA2_ae_eq_of_continuous (hYμc k) (hAμc k) fun q =>
      (hYμV k q).trans (hAμV k q).symm
  have hidν : ∀ᵐ ω ∂P, ∀ k q, Yν k q ω = Aν k q ω := ae_all_iff.2 fun k =>
    swcNA2_ae_eq_of_continuous (hYνc k) (hAνc k) fun q =>
      (hYνV k q).trans (hAνV k q).symm
  have hUμ : ∀ᵐ ω ∂P, ∀ k, ∀ K : Set (Fin n → ℝ), IsCompact K →
      TendstoUniformlyOn (fun j q => ∫ u, avgReg (X ω) j u ∂(circM.map (Φμ k q)))
        (fun q => Aμ k q ω) atTop K := ae_all_iff.2 hAμU
  have hUν : ∀ᵐ ω ∂P, ∀ k, ∀ K : Set (Fin n → ℝ), IsCompact K →
      TendstoUniformlyOn (fun j q => ∫ u, avgReg (X ω) j u ∂(circM.map (Φν k q)))
        (fun q => Aν k q ω) atTop K := ae_all_iff.2 hAνU
  filter_upwards [hUμ, hUν, hidμ, hidν, hsmall] with ω h1 h2 h3 h4 h5
  -- `evalReg` is the limit
  have heμ : ∀ k q, evalReg (X ω) (circM.map (Φμ k q)) = Aμ k q ω := fun k q =>
    ((h1 k {q} isCompact_singleton).tendsto_at (mem_singleton q)).limUnder_eq
  have heν : ∀ k q, evalReg (X ω) (circM.map (Φν k q)) = Aν k q ω := fun k q =>
    ((h2 k {q} isCompact_singleton).tendsto_at (mem_singleton q)).limUnder_eq
  refine ⟨fun k K hK => ?_, fun k K hK => ?_, fun k => ?_, fun k => ?_, fun R η hη => ?_⟩
  · simp_rw [heμ]; exact h1 k K hK
  · simp_rw [heν]; exact h2 k K hK
  · simp_rw [heμ]; exact hAμc k ω
  · simp_rw [heν]; exact hAνc k ω
  · filter_upwards [h5 R η hη] with k hk q hq
    rw [heμ, heν, ← h3, ← h4]
    exact hk q hq

end SWCore
end QuantumZipper

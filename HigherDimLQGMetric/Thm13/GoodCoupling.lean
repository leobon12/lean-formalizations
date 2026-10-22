import HigherDimLQGMetric.Thm13.ProbSubseq

/-! The L7f limit is determined by the field and admits an almost sure
subsequence on the fixed-marginal coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l8_exists_good_coupling
    (hL6a : ∀ d ξ κ, L6a_tight d ξ κ)
    (hLen : (∀ d ξ κ, L6a_tight d ξ κ) → ∀ {d : ℕ} (ξ : ℝ) (κ : Rd d → ℝ)
      (_hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
        DGZ.RealEpsAdapterShape d κ ξ Q)
      {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistRd d),
      IsNormalizedLGF h P →
      ∀ μ : ProbabilityMeasure C(Rd d × Rd d, ℝ),
        μ ∈ closure {ν : ProbabilityMeasure C(Rd d × Rd d, ℝ) |
          ∃ ε ∈ Ioo (0 : ℝ) 1,
            (ν : Measure C(Rd d × Rd d, ℝ)) =
              P.map (fun ω => toCMapRd ((aEps κ ξ ε)⁻¹ •
                lfppDist κ ξ ε (h ω)))} →
        ∀ᵐ E ∂(μ : Measure C(Rd d × Rd d, ℝ)), IsContLengthFn E)
    (hL7f : ∀ d ξ κ, L7f_determined d ξ κ)
    {d : ℕ} (hd : 2 ≤ d) (ξ : ℝ) (κ : Rd d → ℝ)
    (hB2 : ∃ Q : ℝ, DGZ.DGZHyp d κ ξ Q ∧
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hMarkov : DMarkovRd) (hShell : ShellDecouplingFun)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (hεt : Tendsto εs atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (_ : IsProbabilityMeasure P) (h : Ω → DistRd d)
        (Dh : Ω → ContMetric d),
        IsNormalizedLGF h P ∧ Measurable Dh ∧
          (∀ᵐ ω ∂P, (Dh ω).IsLength ∧ IsProperFn (Dh ω).1) ∧
          LQGMetric.AEDeterminedBy Dh h P ∧
          StablyTendstoLU P h
            (fun n ω => lfppSeq κ ξ (εs ∘ φ) (h ω) n)
            (fun ω => (Dh ω).1) ∧
          (∀ᵐ ω ∂P, Tendsto
            (fun n => lfppSeq κ ξ (εs ∘ φ) (h ω) n)
            atTop (𝓝 (Dh ω).1)) := by
  obtain ⟨φ₀, hφ₀, Ω, mΩ, P, hP, h, Dh, hh, hDm, hgood, hstable⟩ :=
    l8_exists_limit_coupling hL6a hLen hd ξ κ hB2 εs hεs hεt
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := hP
  have hε₀t : Tendsto (εs ∘ φ₀) atTop (𝓝 0) :=
    hεt.comp hφ₀.tendsto_atTop
  obtain ⟨hdet, hprob⟩ :=
    (hL7f d ξ κ) hB2 hMarkov hShell (εs ∘ φ₀)
      (fun n => hεs (φ₀ n)) hε₀t P h Dh hh hDm hstable
  obtain ⟨Q, hQ, _⟩ := hB2
  have hXm (n : ℕ) : AEMeasurable
      (fun ω => lfppSeq κ ξ (εs ∘ φ₀) (h ω) n) P :=
    l6a_aemeasurable_normalized_lfpp hQ.dim κ hQ.kernel ξ
      (hεs (φ₀ n)) P h hh.1.isLGFPlusBddCont
  obtain ⟨ns, hns, hae⟩ := l8_exists_subseq_ae_of_prob P
    (fun n ω => lfppSeq κ ξ (εs ∘ φ₀) (h ω) n)
    (fun ω => (Dh ω).1) hXm hprob
  refine ⟨φ₀ ∘ ns, hφ₀.comp hns, Ω, mΩ, P, hP, h, Dh,
    hh, hDm, hgood, hdet, ?_, ?_⟩
  · intro g hg hgb ψ hψ hψb
    exact (hstable g hg hgb ψ hψ hψb).comp hns.tendsto_atTop
  · simpa only [Function.comp_def, lfppSeq] using hae

end HigherDimLQGMetric

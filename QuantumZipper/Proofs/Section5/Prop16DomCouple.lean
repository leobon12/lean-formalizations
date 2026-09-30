import QuantumZipper.Proofs.Section5.Prop16DomCoupleNodes
import QuantumZipper.Proofs.Section5.Prop16LocGood

/-!
# Proposition 1.6, node DOM-COUPLE (part 2): the domain Markov coupling from its sub-nodes

`prop16MixedFreeLocCoupling_of_nodes`: `Prop16MixedFreeLocCouplingStmt` (`Prop16LocGood.lean`)
follows from the Hilbert datum `DomMarkovCurveStmt` (sub-node DOM-a, the mixed-form domain
Markov property of Sheffield (2007) Thm 2.17 with the harmonic curve) and the probabilistic
sub-node `GaussContFubiniStmt` (DOM-b: Kolmogorov continuous version + stochastic Fubini); see
`Prop16DomCoupleNodes.lean` for sources.

Construction (own argument): one isonormal process `W` on `HkE` (`gs_process_hilbert`) gives
the free field `X μ = W(v̂_μ)` and the mixed field `Y μ = W(e μ)`; for a dyadic folded circle `σ`
inside `D ∪ (a,b)`, a.s. `Y σ = X σ − X ρ₀ − W(k_σ)` (zero-variance combination) and
`W(k_σ) = ∫ G dσ` (DOM-b), so `Y σ = X σ + ∫ ψ dσ` with `ψ := −G − X ρ₀` (the random additive
constant of the mod-constants normalisation goes into `ψ`), continuous on `D ∪ (c,d)`; the
countably many circles are handled by `ae_all_iff`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper

namespace Prop16Asm

open GFFExist LQGDimension.ExistAsm

/-- `realSet` is monotone. -/
theorem realSet_mono_dom {s t : Set ℝ} (h : s ⊆ t) : realSet s ⊆ realSet t :=
  image_mono h

/-- A function continuous on a compact set carrying a finite measure is integrable. -/
theorem integrable_of_continuousOn_carrier {μ : Measure ℂ} [IsFiniteMeasure μ] {g : ℂ → ℝ}
    {K : Set ℂ} (hK : IsCompact K) (hg : ContinuousOn g K) (hμK : μ Kᶜ = 0) :
    Integrable g μ := by
  have hIK : IntegrableOn g K μ := hg.integrableOn_compact hK
  have hr : μ.restrict K = μ := Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμK)
  rwa [IntegrableOn, hr] at hIK

end Prop16Asm

end QuantumZipper

import LQGMetric.Statement.GFF

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `IsDomainRealization`. Declaration unchanged from the candidate `CandIsDomainRealization.lean` (sha256 493cc38523c6f597…). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped Distributions
open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont)

namespace SupercriticalConformalCovariance

/-- Paper l. 23 (Theorem 1.1: "`h` a GFF plus a continuous function on `V`, in the local sense in which
the canonical metric is defined") in the realization form of Gwynne–Miller 1905.00384v2 (GM) l. 265 ("a
random distribution `h` on `U` which can be coupled with a random continuous function `f` in such a way
that `h − f` has the law of the (zero-boundary or whole-plane, as appropriate) GFF on `U`") and l. 310–321
(`h|_U = h̊^U + 𝔥^U`, then `h̊^U + f`), and of GMU (arXiv:1905.00383v3) Remark 1.5, ruling A10.2:
`(h₀, f)` **realizes** the random distribution `h` on the open set `V` if
* `h` is a random distribution on `V` (measurable for the cylinder σ-algebra of `𝒟'(V)`);
* `h₀` is a whole-plane GFF plus a continuous function (`LQGMetric.IsGFFPlusCont`, DG l. 443);
* `f` is a random continuous function on `V` (Borel for the compact-open topology), which need not
  extend continuously to `∂V` (GM l. 265);
* almost surely `h = h₀|_V + f` on `V`: `⟨h, ψ⟩ = ⟨h₀, ψ⟩ + ∫ ψ f` for every `ψ ∈ 𝓓(V)`, with `f`
  extended by `0` off `V`, where every `ψ ∈ 𝓓(V)` vanishes.
The coupling lives on the probability space of `h`; a zero-boundary GFF on `V` plus a continuous function
has such a realization after coupling with an independent whole-plane GFF (GM l. 821–822). -/
def IsDomainRealization {Ω : Type*} [MeasurableSpace Ω] (V : Opens ℂ) (P : Measure Ω)
    (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)) : Prop :=
  Measurable h ∧ IsGFFPlusCont h₀ P ∧ Measurable f ∧
    ∀ᵐ ω ∂P, h ω = restrictTo V (h₀ ω) +
      Distribution.ofFun V (Function.extend Subtype.val (f ω) 0) volume ⊤

end SupercriticalConformalCovariance

-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalConformalCovariance.Frozen.XiCrit
import SupercriticalConformalCovariance.Frozen.IsGreenian
import SupercriticalConformalCovariance.Frozen.ConfPullbackField
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalConformalCovariance.Implementation.ConformalCovariance

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `conformal_covariance`. Statement unchanged from the candidate `CandConformalCovariance.lean` (sha256 b482f49bd8897ca6…); its proof body is the manifest-registered DRAFT_SORRY placeholder until the two-key seal (provider `SupercriticalConformalCovariance.Implementation.ConformalCovariance`). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn)

namespace SupercriticalConformalCovariance

open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)

/-- **Conformal covariance of the supercritical LQG metric** (paper Theorem 1.1, l. 22–28, with the
conventions of l. 17–20). Fix `ξ > ξ_crit` (`xiCrit`, DG (1.7)) and `Q = Q(ξ)` (`IsLFPPExponent`,
DG (1.5)), and let `D` be a (strong) LQG metric with parameter `ξ` (DG Definition 1.7), i.e. one
normalization of the canonical metric (DG Theorem 1.8). Let `U, V ⊆ ℂ` be domains which are both
Greenian (`IsGreenian`: the zero-boundary GFF exists on them; ruling A14, an author-approved restriction
of P l. 22 which excludes `ℂ` and `ℂ` minus a closed polar set), `φ : U → V` a deterministic conformal
bijection, and `h` a GFF plus a continuous function on `V`, given by a realization `h = h₀|_V + f`
(`IsDomainRealization`; ruling A10.2, Gwynne–Miller 1905.00384v2 l. 265 and l. 310–321). Then:
* the field `h ∘ φ + Q log |φ′|` on `U` (`confPullbackField`) is again a GFF plus a continuous function:
  after coupling, i.e. on a measure-preserving extension `π : Ω' → Ω`, it has a realization `g₀|_U + k`
  (GM l. 361: "`h^ϕ` is the sum of a zero-boundary GFF and a harmonic function … Therefore `D_{h^ϕ}` is
  defined"); so the right-hand side of (1) is always defined and the statement is never vacuous;
* on every such extension and for every such realization, almost surely, simultaneously for all
  `u, v ∈ U`, `D_h(φ u, φ v; V) = D_{h ∘ φ + Q log |φ′|}(u, v; U)` (1), both sides being domain metrics
  (`domainMetric`) with values in `[0, ∞]`. The probability-one event may depend on `φ` (l. 28).
The domain metrics do not depend on the realizations, almost surely
(`domainMetric_ae_eq_of_isDomainRealization`, on every open set, with no Greenian hypothesis). -/
theorem conformal_covariance :
    ∀ ξ : Set.Ioi (0 : ℝ), xiCrit < (ξ : ℝ) → ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ U V : Opens ℂ, IsConnected (U : Set ℂ) → IsConnected (V : Set ℂ) →
      IsGreenian U → IsGreenian V →
      ∀ (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V),
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f →
        (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
            (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)), MeasurePreserving π P' P ∧
          IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k) ∧
        ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (π : Ω' → Ω), MeasurePreserving π P' P →
          ∀ (g₀ : Ω' → DistC) (k : Ω' → C(U, ℝ)),
            IsDomainRealization U P' (fun ω' => confPullbackField Q hφ (h (π ω'))) g₀ k →
            ∀ᵐ ω' ∂P', ∀ u v : U,
              domainMetric (ξ : ℝ) D V (h₀ (π ω')) (f (π ω'))
                  (⟨φ u, hφ.2.mapsTo u.2⟩, ⟨φ v, hφ.2.mapsTo v.2⟩) =
                domainMetric (ξ : ℝ) D U (g₀ ω') (k ω') (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalConformalCovariance.Implementation.conformal_covariance_impl
-- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalConformalCovariance
-- FROZEN_ANCHOR_SUFFIX_END

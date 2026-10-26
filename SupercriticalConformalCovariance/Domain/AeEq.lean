import SupercriticalConformalCovariance.Domain.Locality
import SupercriticalConformalCovariance.Domain.Exhaust
import SupercriticalConformalCovariance.Domain.Cutoff
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric

/-!
# Realization independence of the domain metric

Provider for the candidate `domainMetric_ae_eq_of_isDomainRealization`
(ruling A10.2), by GMU Remark 1.5's bump-function argument
(arXiv:1905.00383v3, TeX l. 360–374) with the coin-mixture
universal locality:

1. exhaust `V` by the open sets `W n = exW V n` (every compact subset of `V` lies in one);
2. cut `f` off: `F n = χ_n f ∈ C(ℂ)` with `χ_n = 1` on `W n`, `tsupport χ_n ⋐ V`;
3. a.s. (Axiom III for `h₀`, simultaneous in the shift, and continuity of `(ℂ, D_{h₀}) → ℂ`), the
   domain metric is `inf_n D_{h₀ + F n}(·, ·; W n)` (`weylScaleOn_eq_iInf_internal`);
4. `(h₀ + χ_n f)|_{W n} = h|_{W n} = (h₀' + χ_n f')|_{W n}` (`restrictTo_addFun_cutExt`), so by
   pathwise locality (`ae_internal_eq_of_ae_restrictTo_eq_lsc`, one functional for both fields)
   the internal metrics agree a.s., for all `n` at once.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Domain

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont addFun)
open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric weylScale)
open SupercriticalConformalCovariance (IsDomainRealization domainMetric weylScaleOn)

/-- The open sets of the exhaustion of `V`, as `Opens`. -/
def exWO (V : Opens ℂ) (n : ℕ) : Opens ℂ := ⟨exW V n, isOpen_exW V n⟩

theorem exWO_le (V : Opens ℂ) (n : ℕ) : exWO V n ≤ V := exW_subset V n

/-- The `n`-th cut-off extension `χ_n f ∈ C(ℂ)` of `f ∈ C(V)`. -/
def cutF (V : Opens ℂ) (n : ℕ) (f : C((V : Set ℂ), ℝ)) : C(ℂ, ℝ) :=
  cutExt V.isOpen (tsupport_cutoff_subset (V : Set ℂ) n) f

theorem cutF_eq (V : Opens ℂ) (n : ℕ) (f : C((V : Set ℂ), ℝ)) (z : ℂ) (hz : z ∈ exW V n) :
    cutF V n f z = f ⟨z, exW_subset V n hz⟩ :=
  cutExt_eq_of_eq_one V.isOpen _ f (exW_subset V n hz) (cutoff_eq_one V n hz)

/-- **One sample.** On the common sample event of `h₀`, the domain metric is the exhaustion infimum
of the internal metrics of `D_{h₀ + χ_n f}` on `W n`. -/
theorem domainMetric_eq_iInf_internal_of_sample {ξ : ℝ} (hξ : 0 ≤ ξ) (D : DistC → LSCMetric)
    (V : Opens ℂ) (h₀ : DistC) (f : C((V : Set ℂ), ℝ))
    (hforget : Continuous (forget (D h₀))) (hL : (D h₀).IsLengthSpace)
    (hW : ∀ g : C(ℂ, ℝ), weylScale ξ g (D h₀) = (D (addFun h₀ g)).1) (p : V × V) :
    domainMetric ξ D V h₀ f p = ⨅ (n : ℕ) (hx : (p.1 : ℂ) ∈ exW V n) (hy : (p.2 : ℂ) ∈ exW V n),
      (D (addFun h₀ (cutF V n f))).internal (exW V n) (⟨p.1, hx⟩, ⟨p.2, hy⟩) :=
  weylScaleOn_eq_iInf_internal (D h₀) ξ hξ hforget hL f (exW V) (exW_subset V)
    (fun K hK hKV => exists_subset_exW V.isOpen hK hKV) (fun n => cutF V n f)
    (fun n z hz => cutF_eq V n f z hz)
    (fun n => D (addFun h₀ (cutF V n f))) (fun n q => (congrFun (hW (cutF V n f)) q).symm) p

/-- **Exhaustion representation, almost surely.** For a realization `(h₀, f)` and a strong LQG
metric, a.s. the domain metric equals the exhaustion infimum of whole-plane internal metrics. -/
theorem ae_domainMetric_eq_iInf_internal {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn V) (h₀ : Ω → DistC) (f : Ω → C((V : Set ℂ), ℝ))
    (hR : IsDomainRealization V P h h₀ f) :
    ∀ᵐ ω ∂P, ∀ p : V × V, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) p =
      ⨅ (n : ℕ) (hx : (p.1 : ℂ) ∈ exW V n) (hy : (p.2 : ℂ) ∈ exW V n),
        (D (addFun (h₀ ω) (cutF V n (f ω)))).internal (exW V n) (⟨p.1, hx⟩, ⟨p.2, hy⟩) := by
  filter_upwards [ae_sample_of_isGFFPlusCont hD P h₀ hR.2.1] with ω ⟨hf, hL, hW⟩ p
  exact domainMetric_eq_iInf_internal_of_sample (le_of_lt ξ.2) D V (h₀ ω) (f ω) hf hL hW p

/-- The cut-off fields `h₀ + χ_n f` of a realization agree with `h` on `W n`, a.s. -/
theorem ae_restrictTo_cutF {V : Opens ℂ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistOn V} {h₀ : Ω → DistC} {f : Ω → C((V : Set ℂ), ℝ)}
    (hR : IsDomainRealization V P h h₀ f) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ φ : LQGMetric.TestOn (exWO V n),
      restrictTo (exWO V n) (addFun (h₀ ω) (cutF V n (f ω))) φ =
        h ω (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := exWO V n) (Ω₂ := V) φ) := by
  filter_upwards [hR.2.2.2] with ω hω φ
  exact restrictTo_addFun_cutExt (exWO_le V n) (tsupport_cutoff_subset (V : Set ℂ) n)
    (fun z hz => cutoff_eq_one V n hz) (h ω) (h₀ ω) (f ω) hω φ

/-- **Realization independence of the domain metric** (form without the exponent hypothesis). -/
theorem ae_domainMetric_eq_of_isDomainRealization {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (V : Opens ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn V} {h₀ h₀' : Ω → DistC} {f f' : Ω → C(V, ℝ)}
    (hR : IsDomainRealization V P h h₀ f) (hR' : IsDomainRealization V P h h₀' f') :
    ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) = domainMetric (ξ : ℝ) D V (h₀' ω) (f' ω) := by
  -- pathwise locality on each `W n`
  have hloc : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (D (addFun (h₀ ω) (cutF V n (f ω)))).internal (exWO V n : Set ℂ) =
        (D (addFun (h₀' ω) (cutF V n (f' ω)))).internal (exWO V n : Set ℂ) := by
    intro n
    refine ae_internal_eq_of_ae_restrictTo_eq_lsc hD
      (isGFFPlusCont_addFun_of_measurable hR.2.1 (measurable_cutExt V.isOpen _ hR.2.2.1))
      (isGFFPlusCont_addFun_of_measurable hR'.2.1 (measurable_cutExt V.isOpen _ hR'.2.2.1))
      (exWO V n) ?_
    filter_upwards [ae_restrictTo_cutF hR n, ae_restrictTo_cutF hR' n] with ω h1 h2
    ext φ
    exact (h1 φ).trans (h2 φ).symm
  filter_upwards [ae_all_iff.2 hloc, ae_domainMetric_eq_iInf_internal hD V P h h₀ f hR,
    ae_domainMetric_eq_iInf_internal hD V P h h₀' f' hR'] with ω hl e1 e2
  funext p
  rw [e1 p, e2 p]
  refine iInf_congr fun n => iInf_congr fun hx => iInf_congr fun hy => ?_
  have := hl n
  exact congrFun this (⟨p.1, hx⟩, ⟨p.2, hy⟩)

/-- **Realization independence of the domain metric** (provider for the candidate
`SupercriticalConformalCovariance.domainMetric_ae_eq_of_isDomainRealization`; identical statement;
the exponent hypothesis is not used). -/
theorem domainMetric_ae_eq_of_isDomainRealization :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ V : Opens ℂ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ h₀' : Ω → DistC) (f f' : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f → IsDomainRealization V P h h₀' f' →
        ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) = domainMetric (ξ : ℝ) D V (h₀' ω) (f' ω) :=
  fun _ _ _ _ hD V _ _ _ _ _ _ _ _ _ hR hR' => ae_domainMetric_eq_of_isDomainRealization hD V hR hR'

end SupercriticalConformalCovariance.Domain

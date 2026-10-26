import SupercriticalConformalCovariance.Good.Assembly
import SupercriticalConformalCovariance.BiLip.Lemma21
import SupercriticalConformalCovariance.Domain.Axioms

set_option autoImplicit false
noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.Good

open LQGMetric (DistC IsWholePlaneGFF)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric)
open SupercriticalConformalCovariance (IsConformalBijection domainMetric)

/-- The target domain metric pulled back to source endpoints, extended by infinity
off the source domain so it has the total type consumed by `G5`. -/
def transportedE (ξ : ℝ) (D : DistC → LSCMetric)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (g₀ : DistC) (k : C(V, ℝ)) (p : ℂ × ℂ) : ℝ≥0∞ := by
  classical
  exact if hu : p.1 ∈ (U : Set ℂ) ∧ p.2 ∈ (U : Set ℂ) then
    domainMetric ξ D V g₀ k
      (⟨φ p.1, hφ.2.1 hu.1⟩, ⟨φ p.2, hφ.2.1 hu.2⟩)
  else ⊤

theorem transportedE_on (ξ : ℝ) (D : DistC → LSCMetric)
    {U V : Opens ℂ} {φ : ℂ → ℂ} (hφ : IsConformalBijection φ U V)
    (g₀ : DistC) (k : C(V, ℝ)) (u v : U) :
    transportedE ξ D hφ g₀ k ((u : ℂ), (v : ℂ)) =
      domainMetric ξ D V g₀ k
        (⟨φ u, hφ.2.1 u.2⟩, ⟨φ v, hφ.2.1 v.2⟩) := by
  simp [transportedE]

/-- Paper l. 375–380, with the deterministic Lemma 2.1 constant. -/
def shieldK (C : ℝ) : ℝ := 1 / (4 * C ^ 2)

theorem shieldK_pos {C : ℝ} (hC : 1 ≤ C) : 0 < shieldK C := by
  unfold shieldK
  positivity

theorem shieldK_loop_factor {C : ℝ} (hC : 1 ≤ C) :
    2 * C * shieldK C = 1 / (2 * C) := by
  have hCn : C ≠ 0 := ne_of_gt (by linarith : 0 < C)
  unfold shieldK
  field_simp
  ring

theorem shieldK_escape_gap {C : ℝ} (hC : 1 ≤ C) :
    2 * C * shieldK C < 1 / C := by
  rw [shieldK_loop_factor hC]
  have hCp : 0 < C := by linarith
  apply (div_lt_div_iff₀ (by positivity) hCp).2
  nlinarith

/-- In the whole-plane-restricted instance, the source domain metric is the
internal metric of the realized whole-plane metric, simultaneously in pairs. -/
theorem ae_source_domainMetric_eq_internal
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsStrongLQGMetric ξ Q D) (U : Opens ℂ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D U (h ω) 0 =
      (D (h ω)).internal U :=
  SupercriticalConformalCovariance.Domain.ae_domainMetric_zero_eq_internal hD U P
    (LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh)

/-- The existing cover assembly with the target metric fixed to its domain
realization. Its two hypotheses are the literal event locality and the compact
uniform failure estimate of Proposition 4.3, both stated for this metric. -/
theorem ae_goodCover_of_locality_and_prop43_transport
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (k : ℝ) (hk : 0 < k) :
    ∃ (p : ℝ) (θ : Ioi (0 : ℝ)) (n : ℕ)
      (q : Ioo (0 : ℝ) (1 / 100))
      (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)),
      0 < p ∧ p < 1 ∧ (q : ℝ) = (1 / 2 : ℝ) ^ n ∧
      ∀ {U V : Opens ℂ} (φ : ℂ → ℂ)
        (hφ : IsConformalBijection φ U V)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h g₀ : Ω → DistC)
        (f : Ω → C(V, ℝ))
        (hI : SupercriticalConformalCovariance.BiLip.IsInstance Q U V hφ P h g₀ f),
        ∀ (exhaustion : ℕ → Set ℂ),
          (∀ m, IsCompact (exhaustion m)) →
          (∀ m, exhaustion m ⊆ U) →
          ∀ η : ℝ, 0 < η →
          (∀ L : Set ℂ, IsCompact L → L ⊆ U →
            ∃ r₀ : ℝ, 0 < r₀ ∧
              ∀ z ∈ L, ∀ r ∈ Ioc (0 : ℝ) r₀,
                LQGMetric.Blueprint.AEEventIn P
                  (SupercriticalConformalCovariance.Cover.localSigma h z r)
                  (GoodEvent h (D ∘ h)
                    (fun ω => transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
                    ξ Q q a K θ k η z r)) →
          (∀ L : Set ℂ, IsCompact L → L ⊆ U →
            ∃ r₀ : ℝ, 0 < r₀ ∧
              ∀ z ∈ L, ∀ r : Ioi (0 : ℝ), (r : ℝ) ≤ r₀ →
                P (RegularBadEvent h (D ∘ h)
                  (fun ω => transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
                  ξ Q q a θ η z r) ≤ ENNReal.ofReal ((1 - p) / 2)) →
          ∀ᵐ ω ∂P,
            SupercriticalConformalCovariance.Improve.GoodCover (D (h ω))
              (transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
              ξ Q q a K θ k η exhaustion coverScale := by
  obtain ⟨p, θ, n, q, a, K, hp, hp1, hq, H⟩ :=
    ae_goodCover_of_locality_and_prop43 ξ Q hQ D hD k hk
  refine ⟨p, θ, n, q, a, K, hp, hp1, hq, ?_⟩
  intro U V φ hφ Ω _ P _ h g₀ f hI exhaustion hKc hKU η hη hloc hbad
  exact H P h hI.1.1
    (fun ω => transportedE (ξ : ℝ) D hφ (g₀ ω) (f ω))
    U U.isOpen exhaustion hKc hKU η hη hloc hbad

end SupercriticalConformalCovariance.Good

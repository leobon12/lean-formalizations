import SupercriticalConformalCovariance.BiLip.Step2

/-!
# Lemma 2.1, l. 96: "The same constant compares lengths of every path for the two metrics after the natural
pullback"

On the almost-sure event of `lemma21_of_seq_inputs` the two metrics `d = D_h(·,·;U)` and `e` (in source
coordinates) satisfy `e ≤ C d` and `d ≤ C e` pointwise on `U × U`; the lengths of every path in `U`, measured
with `e` and with `d` (suprema over partitions, `curveLengthWith`), are then compared with the same `C`
(`curveLengthWith_le_of_le_on`). For `e` this length is the `e`-length `lenT` of the deterministic core.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology MeasureTheory TopologicalSpace
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric IsLFPPExponent)
open SupercriticalConformalCovariance (IsConformalBijection)
open LQGMetric (DistC)
open HigherDimLQGMetric (curveLengthWith)

/-- A pointwise comparison on `U` compares the lengths of every path in `U`. -/
theorem curveLengthWith_le_of_le_on {U : Set ℂ} {e d : ℂ → ℂ → ℝ≥0∞} {K : ℝ≥0∞}
    (hle : ∀ u ∈ U, ∀ v ∈ U, e u v ≤ K * d u v) {P : ℝ → ℂ} {a b : ℝ}
    (hPU : ∀ t ∈ Icc a b, P t ∈ U) :
    curveLengthWith e P a b ≤ K * curveLengthWith d P a b := by
  rw [← HigherDimLQGMetric.curveLengthWith_const_mul]
  exact HigherDimLQGMetric.curveLengthWith_mono fun u v hau huv hvb =>
    hle _ (hPU u ⟨hau, huv.trans hvb⟩) _ (hPU v ⟨hau.trans huv, hvb⟩)

/-- `lenT` is the `e`-length: the `dV`-length of `φ ∘ P` equals the length of `P` for `e = eT`. -/
theorem lenT_eq_curveLengthWith_eT (D₀ : LSCMetric) (ξ : ℝ) {V : Set ℂ} (k : C(V, ℝ))
    (φ : ℂ → ℂ) (P : ℝ → ℂ) (a b : ℝ) :
    lenT D₀ ξ k φ P a b = curveLengthWith (eT D₀ ξ k φ) P a b := rfl

/-- **Lemma 2.1 with the length clause** (l. 90–96), from the two open inputs: almost surely, for every path in
`U`, `C⁻¹ len_d(P) ≤ len_e(P) ≤ C len_d(P)` as well as the pointwise comparison. Here `d = D_h(·,·;U)` and
`e = eT` (the pulled-back domain metric of the target realization, `= domainMetric … (φ ·, φ ·)` on `U`). -/
theorem lemma21_lengths_of_seq_inputs (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (D : DistC → LSCMetric) (hD : IsStrongLQGMetric ξ Q D)
    (hT : TargetTightSeq ξ Q D) (hloc : GoodEventsLocal ξ Q D) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (U V : Opens ℂ) (φ : ℂ → ℂ) (hφ : IsConformalBijection φ U V)
        {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h g₀ : Ω → DistC) (k : Ω → C(V, ℝ)), IsInstance Q U V hφ P h g₀ k →
        ∀ᵐ ω ∂P,
          (∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
            eT (D (g₀ ω)) ξ (k ω) φ u v ≤ ENNReal.ofReal C * pathInf (D (h ω)) U u v ∧
            pathInf (D (h ω)) U u v ≤ ENNReal.ofReal C * eT (D (g₀ ω)) ξ (k ω) φ u v) ∧
          ∀ (γ : ℝ → ℂ) (a b : ℝ), (∀ t ∈ Icc a b, γ t ∈ (U : Set ℂ)) →
            curveLengthWith (eT (D (g₀ ω)) ξ (k ω) φ) γ a b ≤
                ENNReal.ofReal C * curveLengthWith (pathInf (D (h ω)) U) γ a b ∧
              curveLengthWith (pathInf (D (h ω)) U) γ a b ≤
                ENNReal.ofReal C * curveLengthWith (eT (D (g₀ ω)) ξ (k ω) φ) γ a b := by
  obtain ⟨C, hC, H⟩ := lemma21_of_seq_inputs ξ Q hQ D hD hT hloc
  refine ⟨C, hC, fun U V φ hφ Ω _ P _ h g₀ k hI => ?_⟩
  have hφU : MapsTo φ U V := hφ.2.mapsTo
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  filter_upwards [H U V φ hφ P h g₀ k hI, SupercriticalConformalCovariance.Domain.ae_sample_of_isGFFPlusCont hD P g₀ hI.2.2.1]
    with ω hω hs
  have hpt : ∀ u ∈ (U : Set ℂ), ∀ v ∈ (U : Set ℂ),
      eT (D (g₀ ω)) ξ (k ω) φ u v ≤ ENNReal.ofReal C * pathInf (D (h ω)) U u v ∧
        pathInf (D (h ω)) U u v ≤ ENNReal.ofReal C * eT (D (g₀ ω)) ξ (k ω) φ u v := by
    intro u hu v hv
    obtain ⟨h₁, h₂⟩ := hω ⟨u, hu⟩ ⟨v, hv⟩
    have he : SupercriticalConformalCovariance.domainMetric (ξ : ℝ) D V (g₀ ω) (k ω)
        (⟨φ u, hφU hu⟩, ⟨φ v, hφU hv⟩) = eT (D (g₀ ω)) ξ (k ω) φ u v :=
      SupercriticalConformalCovariance.Domain.weylScaleOn_eq_dV hs.1 (k ω) _
    have hd : (D (h ω)).internal U (⟨u, hu⟩, ⟨v, hv⟩) = pathInf (D (h ω)) U u v := rfl
    rw [he, hd] at h₁ h₂
    refine ⟨h₂, ?_⟩
    -- `d ≤ C e` from `C⁻¹ d ≤ e`
    have hCC : ENNReal.ofReal C * ENNReal.ofReal C⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul hC0.le, mul_inv_cancel₀ hC0.ne', ENNReal.ofReal_one]
    calc pathInf (D (h ω)) U u v
        = ENNReal.ofReal C * (ENNReal.ofReal C⁻¹ * pathInf (D (h ω)) U u v) := by
          rw [← mul_assoc, hCC, one_mul]
      _ ≤ ENNReal.ofReal C * eT (D (g₀ ω)) ξ (k ω) φ u v := by gcongr
  refine ⟨hpt, fun γ a b hγU => ⟨?_, ?_⟩⟩
  · exact curveLengthWith_le_of_le_on (fun u hu v hv => (hpt u hu v hv).1) hγU
  · exact curveLengthWith_le_of_le_on (fun u hu v hv => (hpt u hu v hv).2) hγU

end SupercriticalConformalCovariance.BiLip

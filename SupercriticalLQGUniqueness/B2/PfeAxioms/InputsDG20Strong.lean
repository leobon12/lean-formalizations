import SupercriticalLQGUniqueness.B2.Iface.Statements

 








set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC)
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs

open SupercriticalLQGUniqueness.B2.Iface

 


def DG20LimitStrong : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            (∀ r : ℚ, ∀ hr : 0 < r,
              Tendsto (fun n => (r : ℝ) *
                (m ⟨(ε (φ n) : ℝ) / (r : ℝ),
                  Set.mem_Ioi.mpr (div_pos (ε (φ n)).property
                    (Rat.cast_pos.mpr hr))⟩ : ℝ) /
                (m (ε (φ n)) : ℝ)) atTop
                (𝓝 (c ⟨(r : ℝ), Set.mem_Ioi.mpr (Rat.cast_pos.mpr hr)⟩ : ℝ))) ∧
            ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
              (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
              ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ),
                (∀ δ, IsHeatSmoothing P h δ (X δ)) →
              ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
                (_ : IsProbabilityMeasure P') (h' : Ω' → DistC)
                (F : ℕ → Ω' → ℂ × ℂ → EReal) (L : Ω' → LSCMetric),
                Measurable L ∧ IsNormalizedWholePlaneGFF h' P' ∧
                (∀ n, P'.map (fun ω => (h' ω, F n ω)) =
                  P.map (fun ω => (h ω,
                    rescaledLFPP (ξ : ℝ) (m (ε (φ n))) (X (ε (φ n)) ω)))) ∧
                (∀ᵐ ω ∂P', LSCTendsto (fun n => F n ω) (L ω).toLSCFun.1) ∧
                (∀ᵐ ω ∂P', ∀ u v : ℂ, IsRationalPoint u → IsRationalPoint v →
                  Tendsto (fun n => F n ω (u, v)) atTop
                    (𝓝 ((L ω).toLSCFun.1 (u, v)))) ∧
                (∀ᵐ ω ∂P', (L ω).IsLengthSpace ∧
                  (∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
                    ∀ v : ℂ, (L ω).1 (u, v) < ENNReal.ofReal η → dist u v < δ) ∧
                  (∀ u v : ℂ, (L ω).1 (u, v) < ∞ →
                    ∃ (γ : ℝ → ℂ) (a b : ℝ),
                      (L ω).IsCurve γ a b ∧ γ a = u ∧ γ b = v ∧
                        (L ω).len γ a b = (L ω).1 (u, v))) ∧
                (∀ n, ∀ᵐ ω ∂P', Continuous (F n ω))

 

theorem dg20Limit_of_strong (hStrong : DG20LimitStrong) : DG20Limit := by
  intro ξ Q hQ m hm ε hε
  obtain ⟨φ, hφ, c, hc, hCouple⟩ := hStrong ξ Q hQ m hm ε hε
  refine ⟨φ, hφ, c, hc, ?_⟩
  intro Ω _ P _ h hh X hX
  obtain ⟨Ω', M', P', hP', h', F, L, hL, hh', hLaw, hLsc, hRat, hGeom, _⟩ :=
    hCouple P h hh X hX
  exact ⟨Ω', M', P', hP', h', F, L, hL, hh', hLaw, hLsc, hRat, hGeom⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs

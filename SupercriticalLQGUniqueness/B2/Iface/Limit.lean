import SupercriticalLQGUniqueness.B2.Iface.Statements

 








set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal
open LQGMetric (DistC DistOn restrictTo addFun IsGFFPlusCont IsGFFPlusBddCont)

namespace SupercriticalLQGUniqueness.B2.Iface

 
def PLThm19Limit : Prop :=
  ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
    ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ ε : ℕ → Set.Ioi (0 : ℝ),
        Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) →
        ∀ D : DistC → LSCMetric,
          SubseqLimit ξ m ε D →
          ∀ c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
            IsPfeWeakMetric ξ D c →
            (∃ C : ℝ, 0 < C ∧ ∀ r : Set.Ioi (0 : ℝ),
              C⁻¹ * (r : ℝ) ^ ((ξ : ℝ) * Q) ≤ c r ∧
              (c r : ℝ) ≤ C * (r : ℝ) ^ ((ξ : ℝ) * Q)) ∧
            IsWeakLQGMetric ξ Q D

 
theorem plThm19Limit_of_plThm19 (h : PLThm19) : PLThm19Limit :=
  fun ξ Q hQ _m _hm _ε _hε D _hD c hc => h ξ Q hQ D c hc

end SupercriticalLQGUniqueness.B2.Iface

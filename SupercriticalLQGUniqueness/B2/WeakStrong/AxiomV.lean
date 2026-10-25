import SupercriticalLQGUniqueness.B2.WeakStrong.InternalChain
import SupercriticalLQGUniqueness.B2.WeakStrong.WeylLocal
import SupercriticalLQGUniqueness.Frozen.IsWeakLQGMetric
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.GapChecks.Gapc2
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete

 





















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC addFun IsGFFPlusCont)

namespace SupercriticalLQGUniqueness.B2.WeakStrong

variable {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}

 
theorem finiteness_of_weak (hD : IsWeakLQGMetric ξ Q D) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsGFFPlusCont h P → ∀ U : TopologicalSpace.Opens ℂ,
        IsConnected (U : Set ℂ) →
        ∀ K₁ K₂ : Set ℂ, IsCompact K₁ → IsCompact K₂ → IsConnected K₁ → IsConnected K₂ →
          K₁.Nontrivial → K₂.Nontrivial → K₁ ⊆ U → K₂ ⊆ U → Disjoint K₁ K₂ →
          ∀ᵐ ω ∂P, (D (h ω)).internalSetDist (U : Set ℂ)
            (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ∞ := by
  intro Ω _ P _ h hh U hUc K₁ K₂ _ _ hc₁ hc₂ hn₁ hn₂ hs₁ hs₂ _
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁⟩ := hn₁
  obtain ⟨x₂, hx₂, y₂, hy₂, hxy₂⟩ := hn₂
  obtain ⟨n, c, ρ, hρ, hball, hstep, h₁, h₁', h₂, h₂'⟩ :=
    exists_annular_chain U.isOpen hUc (hs₁ hx₁) (hs₂ hx₂) hxy₁ hxy₂
  obtain ⟨k, F, hk, hkplus, -, hdec⟩ :=
    Uniqueness.TwoScale.GapChecks.exists_normalized_decomposition hh
  have hQ : 0 < Q := Uniqueness.Positivity.FromAxioms.axpos ξ Q D hD
  have hξ : (0 : ℝ) ≤ ξ := le_of_lt ξ.2
  have hann : ∀ᵐ ω ∂P, ∀ i, aroundDist (D (k ω)) (annAt (c i) ρ hρ) < ⊤ :=
    ae_all_iff.2 fun i => Uniqueness.Geodesics.ClosedBalls.ae_aroundDist_lt_top hD P k hk _
  filter_upwards [hann, hD.2.2.2.1 P k hkplus,
    Uniqueness.BiLipschitz.Barrier.ae_curves_continuous hD hQ P k hk] with ω hA hW hcont
  have hE : ∀ p, D (h ω) p = weylScale ξ (F ω) (D (k ω)) p := by
    intro p
    rw [hdec ω, hW (F ω)]
  refine internalSetDist_lt_top_of_loops (D (h ω)) n c hρ hball hstep hc₁.isPreconnected
    hc₂.isPreconnected hx₁ hy₁ hx₂ hy₂ h₁ h₁' h₂ h₂' (fun i => ?_)
  obtain ⟨Pc, a, b, hPc, hPA, hPd, hPl⟩ :=
    Uniqueness.Geodesics.ClosedBalls.aroundDist_exists_finite_trace _ _ (hA i)
  obtain ⟨hE1, hE2⟩ := weyl_curve_finite (D (k ω)) (D (h ω)) ξ hξ (F ω) hcont.1 hE hPc hPl
  exact ⟨Pc, a, b, hE1, hPA, hPd, hE2⟩

end SupercriticalLQGUniqueness.B2.WeakStrong

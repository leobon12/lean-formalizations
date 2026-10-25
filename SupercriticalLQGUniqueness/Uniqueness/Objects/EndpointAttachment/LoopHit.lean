import SupercriticalLQGUniqueness.Uniqueness.Objects.Shadow.Endpoint
import SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment.CorrectedComparator




 
set_option autoImplicit false

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment

 


theorem first_hit_corrected_loop {P π : ℝ → ℂ} {y : ℂ}
    {β σ s t H : ℝ}
    (hH : 0 < H) (hβσ : β ≤ σ)
    (hP : ContinuousOn P (Icc β σ))
    (hπ : ContinuousOn π (Icc s t))
    (htrace : π '' Icc s t ⊆ Objects.CorrectedEvent.ann y (2 * H) (3 * H))
    (hsep : LQGMetric.Disconnects (π '' Icc s t)
      (sphere y (2 * H)) (sphere y (3 * H)))
    (hβ : dist (P β) y ≤ H) (hσ : 3 * H ≤ dist (P σ) y) :
    ∃ z ∈ Icc β σ, P z ∈ π '' Icc s t ∧ β < z ∧
      (∀ q ∈ Ico β z, P q ∉ π '' Icc s t) ∧
      MapsTo P (Icc β z) (ball y (3 * H)) := by
  have hclosed : IsClosed (π '' Icc s t) :=
    (isCompact_Icc.image_of_continuousOn hπ).isClosed
  have hKB : π '' Icc s t ⊆ ball y (3 * H) := by
    intro x hx
    exact (mem_ball).2 (htrace hx).2
  have hβsmall : P β ∈ closedBall y (2 * H) := by
    apply mem_closedBall.mpr
    linarith
  have hσlarge : P σ ∈ (ball y (3 * H))ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using hσ
  have hβK : P β ∉ π '' Icc s t := by
    intro hhit
    have hlarge := (htrace hhit).1
    linarith
  exact Objects.Shadow.first_separator_hit_inside_collar hβσ (by linarith)
    hP hclosed hsep hKB hβsmall hσlarge hβK


 

theorem paid_comparator_first_hit (D : LSCMetric)
    {P : ℝ → ℂ} {y : ℂ} {H β σ d coeff : ℝ}
    (hH : 0 < H) (hβσ : β ≤ σ)
    (hP : ContinuousOn P (Icc β σ))
    (hβ : dist (P β) y ≤ H) (hσ : 3 * H ≤ dist (P σ) y)
    (hcoeff : 0 < coeff) (hd : 0 < d)
    (hcompare : Objects.CorrectedEvent.around D y (2 * H) (3 * H) ≤
      ENNReal.ofReal coeff * Objects.CorrectedEvent.acr D y (H / 4) (H / 2))
    (hcross : Objects.CorrectedEvent.acr D y (H / 4) (H / 2) ≤ ENNReal.ofReal d) :
    ∃ (π : ℝ → ℂ) (s t z : ℝ),
      D.IsCurve π s t ∧ ContinuousOn π (Icc s t) ∧
      π '' Icc s t ⊆ Objects.CorrectedEvent.ann y (2 * H) (3 * H) ∧
      LQGMetric.Disconnects (π '' Icc s t)
        (sphere y (2 * H)) (sphere y (3 * H)) ∧
      D.len π s t < ENNReal.ofReal (2 * coeff * d) ∧
      z ∈ Icc β σ ∧ P z ∈ π '' Icc s t ∧ β < z ∧
      (∀ q ∈ Ico β z, P q ∉ π '' Icc s t) ∧
      MapsTo P (Icc β z) (ball y (3 * H)) := by
  obtain ⟨π, s, t, hπ, hEuclid, htrace, hsep, hlen⟩ :=
    exists_corrected_paid_loop_continuous D y (H / 4) (2 * H)
      (H / 2) (3 * H) hcoeff hd hcompare hcross
  obtain ⟨z, hz, hhit, hβz, hfirst, hcollar⟩ :=
    first_hit_corrected_loop hH hβσ hP hEuclid htrace hsep hβ hσ
  exact ⟨π, s, t, z, hπ, hEuclid, htrace, hsep, hlen,
    hz, hhit, hβz, hfirst, hcollar⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.EndpointAttachment

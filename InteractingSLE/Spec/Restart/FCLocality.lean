/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCPairData
import InteractingSLE.Spec.Sec7.StripMark

/-!
# Marked locality at every shifted line of one capped pair

Choose the capped paths once, independently of the physical line. Their shifted
unions have open complements everywhere, satisfy history-marked locality, and
have the marked Gaussian component kernels of Aux. 77 at every line.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Restart.FCPlumb

open LocalSets WholeField Sec6

universe u

variable {Ω : Type*}

/-- The shifted union of two continuous paths frozen after a finite time is relatively closed everywhere. -/
theorem isOpen_compl_shUnion_of_frozen {η₁ η₂ : Ω → ℝ≥0 → ℂ} {m : ℝ≥0}
    (hc₁ : ∀ ω, Continuous (η₁ ω)) (hc₂ : ∀ ω, Continuous (η₂ ω))
    (hfr₁ : ∀ ω s, m ≤ s → η₁ ω s = η₁ ω m)
    (hfr₂ : ∀ ω s, m ≤ s → η₂ ω s = η₂ ω m)
    (t₁ t₂ : ℝ≥0) (ω : Ω) : IsOpen (H \ shUnion η₁ η₂ t₁ t₂ ω) := by
  have hK := (isCompact_image_of_const (hc₁ ω) (hfr₁ ω)
    (recFst (fullHist η₁ η₂ ω) + t₁)).union
      (isCompact_image_of_const (hc₂ ω) (hfr₂ ω) (recSnd (fullHist η₁ η₂ ω) + t₂))
  rw [shUnion_eq, H_diff_inter_H]
  exact QuantumZipper.isOpen_H.sdiff hK.isClosed

section CompleteMarks

variable {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- History-marked locality also holds after completing the marks by null sets inside the ambient space. -/
theorem isHistoryAvoidanceLocal_aeSigma
    (hloc : IsHistoryAvoidanceLocal 𝒢 A h P) :
    IsHistoryAvoidanceLocal (mΩ ⊓ aeSigma 𝒢 P) A h P := by
  apply Sec7.StripMark.isHistoryAvoidanceLocal_of_ae_le hloc
  intro F hF
  have hle : mΩ ⊓ aeSigma 𝒢 P ≤ aeSigma 𝒢 P := inf_le_right
  exact hle F hF

end CompleteMarks

section Capped

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- The common-first-point property passes to capped versions of the original pair. -/
theorem ae_firstContact_capped (hL77 : Supp10.Lemma77Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (m : ℝ≥0) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ}
    (hag₁ : ∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) :
    ∀ᵐ ω ∂P, (∃ s r : ℝ≥0, ηc₁ ω s = ηc₂ ω r) →
      ∃ s₀ t₀ : ℝ≥0, IsFirstContact (ηc₁ ω) ⊤ (ηc₂ ω) ⊤ s₀ t₀ := by
  filter_upwards [hL77 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hag₁, hag₂] with ω h77 hcap₁ hcap₂
  rintro ⟨s, r, hsr⟩
  rw [hcap₁, hcap₂] at hsr
  obtain ⟨s₀, t₀, hfc, -, -⟩ := h77
    ⟨_, _, capTime_le m (ζ₁ ω) s, capTime_le m (ζ₂ ω) r, hsr⟩
  obtain ⟨hs₀, ht₀⟩ := hfc.2.2.2 _ _ (capTime_le m (ζ₁ ω) s) (capTime_le m (ζ₂ ω) r) hsr
  exact ⟨s₀, t₀, isFirstContact_capped hcap₁ hcap₂ hfc
    (hs₀.trans (capTime_le_cap m (ζ₁ ω) s)) (ht₀.trans (capTime_le_cap m (ζ₂ ω) r))⟩

/-- One pair of capped versions supplies locality and component kernels at every deterministic shifted line.
The versions are chosen before the line parameters, so no selection depending on the line is needed. -/
theorem exists_capped_shUnion_local_kernels (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (m : ℝ≥0) :
    ∃ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ,
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ s, Measurable fun ω => ηc₁ ω s) ∧ (∀ s, Measurable fun ω => ηc₂ ω s) ∧
      (∀ ω s, m ≤ s → ηc₁ ω s = ηc₁ ω m) ∧ (∀ ω s, m ≤ s → ηc₂ ω s = ηc₂ ω m) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₁ ω s = η₁ ω (capTime m (ζ₁ ω) s)) ∧
      (∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime m (ζ₂ ω) s)) ∧
      ∀ t₁ t₂ : ℝ≥0,
        (∀ ω, IsOpen (H \ shUnion ηc₁ ηc₂ t₁ t₂ ω)) ∧
        IsHistoryAvoidanceLocal
          (mΩ ⊓ aeSigma (MeasurableSpace.comap
            (shHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) t₁ t₂)
              inferInstance) P)
          (shUnion ηc₁ ηc₂ t₁ t₂) (centredField h u₀) P ∧
        ∃ g : Ω → DistOn upperHalfPlaneOpens,
          IsLocalSetMean (shUnion ηc₁ ηc₂ t₁ t₂) (centredField h u₀) P g ∧
          ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
            ∀ z₀ ∈ H \ shUnion ηc₁ ηc₂ t₁ t₂ ω,
              tsupport φ ⊆ connectedComponentIn (H \ shUnion ηc₁ ηc₂ t₁ t₂ ω) z₀ →
              P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
                germSigma (shUnion ηc₁ ηc₂ t₁ t₂) (centredField h u₀) ⊔
                  MeasurableSpace.comap (shHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m)
                    (fun ω => cutLife (ζ₂ ω) m) t₁ t₂) inferInstance] ω =
                Complex.exp (Complex.I * (g ω φ : ℂ)) *
                  ((Real.exp (-(1 / 2) * QuantumZipper.zeroGFFTestCov
                    (connectedComponentIn (H \ shUnion ηc₁ ηc₂ t₁ t₂ ω) z₀) φ φ) : ℝ) : ℂ) := by
  obtain ⟨ηc₁, hc₁, hm₁, h0₁, hfr₁, hag₁, hdet₁, hdetζ₁⟩ :=
    exists_capped_version hL75 hκ hκ4 hb hh hη₁ u₀ m
  obtain ⟨ηc₂, hc₂, hm₂, h0₂, hfr₂, hag₂, hdet₂, hdetζ₂⟩ :=
    exists_capped_version hL75 hκ hκ4 hb hh hη₂ u₀ m
  have hloc₁ := hA56 κ hκ hκ4 b jumps hb x₁ θ₁ P h hh η₁ ζ₁ hη₁ u₀ hu₀ m ηc₁ hc₁ hm₁ hag₁
  have hloc₂ := hA56 κ hκ hκ4 b jumps hb x₂ θ₂ P h hh η₂ ζ₂ hη₂ u₀ hu₀ m ηc₂ hc₂ hm₂ hag₂
  have hζm₁ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₁)
  have hζm₂ := (measurable_cutLife m).comp (measurable_lifetime_of_isFlowLine hη₂)
  have hh0 := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  have hfc := ae_firstContact_capped hL77 hκ hκ4 hb hx hθ hh hη₁ hη₂ m hag₁ hag₂
  refine ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hfr₁, hfr₂, hag₁, hag₂, fun t₁ t₂ => ?_⟩
  have hopen := isOpen_compl_shUnion_of_frozen hc₁ hc₂ hfr₁ hfr₂ t₁ t₂
  have hmark := isHistoryAvoidanceLocal_shUnion (t₁ := t₁) (t₂ := t₂)
    hh0.measurable hc₁ hc₂ h0₁ h0₂ hm₁ hm₂ hζm₁ hζm₂
    hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc
  refine ⟨hopen, isHistoryAvoidanceLocal_aeSigma hmark, ?_⟩
  exact ae_condExp_exp_eq_shUnion hh0.measurable hc₁ hc₂ h0₁ h0₂ hm₁ hm₂ hζm₁ hζm₂
    hdet₁ hdet₂ hdetζ₁ hdetζ₂ hloc₁ hloc₂ hfc hh0 (ae_of_all _ hopen)

end Capped

end InteractingSLE.Restart.FCPlumb

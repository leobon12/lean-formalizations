/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.RetPlumbProofHist

/-!
# The line kernel in the retained domain

Packet PROVE-RETPLUMB. Aux. 77's marked Gaussian kernel at a deterministic line
is transferred to the unbounded retained domain and to the sigma algebra enlarged
by the completed physical history. This is the `hcond` argument of `Lemma76FR1`,
before its random chart transport. The mean and the line kernel are obtained from
`exists_cstUnion_marked_of_isFlowLine`, without a new probabilistic hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.RetAux79

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open Supp7 Sec7 Sec7.Lemma76F LocalSets

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω]

/-- Germs of the stopped union, labelled killed histories, and the completed
physical information at the line. -/
@[instance_reducible]
def retLineSigma (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (u₀ : ℂ → ℝ) (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (u r : ℝ≥0) : MeasurableSpace Ω :=
  (germSigma (cstUnion ηc₁ ηc₂ u r) (WholeField.centredField h u₀) ⊔
    MeasurableSpace.comap (cstHist ηc₁ ηc₂
      (fun ω => cutLife (ζ₁ ω) (capR u r))
      (fun ω => cutLife (ζ₂ ω) (capR u r)) u r) inferInstance) ⊔
    retSigma76 P η₁ η₂ ζ₁ ζ₂ u r

theorem retLineSigma_le {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : Measurable h) (u₀ : ℂ → ℝ) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    {ζ₁ ζ₂ : Ω → ℝ≥0∞} (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω))
    (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t)
    (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t) (u r : ℝ≥0) :
    retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ u r ≤ mΩ :=
  sup_le (sup_le
    (germSigma_le (measurable_cstUnion hc₁ hc₂ hm₁ hm₂ u r)
      (WholeField.measurable_centredField hh u₀))
    (measurable_cstHist hm₁ hm₂ ((measurable_cutLife _).comp hζ₁)
      ((measurable_cutLife _).comp hζ₂) u r).comap_le)
    (retSigma76_le P η₁ η₂ ζ₁ ζ₂ u r)

theorem retPhysFiltration_le_retLineSigma (P : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (u₀ : ℂ → ℝ)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞)
    (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (u r t : ℝ≥0) :
    retPhysFiltration P η₁ η₂ ζ₁ ζ₂ u r t ≤
      retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ u (r + t) := le_sup_right

variable {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- The marked component kernel, in the unbounded retained domain and with the
completed physical history included in the conditioning sigma algebra. -/
theorem ae_condExp_cexp_retDomain {d : RetData Ω} (hd : d.IsMeasGood)
    (hh : Measurable h) (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω →
      ω ∈ d.G ∧ (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧
        ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω))
    (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t)
    (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hlaw : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ∀ z₀ ∈ H \ cstUnion ηc₁ ηc₂ d.u d.r ω,
        tsupport φ ⊆ connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) z₀ →
        P[fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) |
          germSigma (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) ⊔
            MeasurableSpace.comap (cstHist ηc₁ ηc₂
              (fun ω => cutLife (ζ₁ ω) (capR d.u d.r))
              (fun ω => cutLife (ζ₂ ω) (capR d.u d.r)) d.u d.r) inferInstance] ω =
          Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) * zeroGFFTestCov
              (connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) z₀) φ φ) : ℝ) : ℂ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
      tsupport φ ⊆ d.D ω →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ d.u d.r] ω =
        Complex.exp (Complex.I *
          ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov (d.D ω) φ φ : ℝ) : ℂ)) := by
  classical
  set F := cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR d.u d.r))
    (fun ω => cutLife (ζ₂ ω) (capR d.u d.r)) d.u d.r with hF
  set 𝒦 := germSigma (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) ⊔
    MeasurableSpace.comap F inferInstance with h𝒦
  let _ : MeasurableSpace Ω := mΩ
  have hcmp : ∀ᵐ ω ∂P, retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ω = F ω := by
    filter_upwards [hag₁, hag₂] with ω e₁ e₂
    have a₁ : cappedPath η₁ ζ₁ (capR d.u d.r) ω = ηc₁ ω := (funext e₁).symm
    have a₂ : cappedPath η₂ ζ₂ (capR d.u d.r) ω = ηc₂ ω := (funext e₂).symm
    simp only [retHist76, cstHist, hF, a₁, a₂]
  have htr : ∀ B, MeasurableSet[retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ d.u d.r] B →
      MeasurableSet[aeSigma 𝒦 P] (B ∩ univ) := by
    intro B hB
    have ht := measurableSet_aeSigma_inter_of_ae
      (Ψ := retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r) (F := F) (𝒦 := 𝒦)
      le_sup_right MeasurableSet.univ
      (by filter_upwards [hcmp] with ω he using ⟨Iff.rfl, fun _ => he⟩) B hB
    rwa [preimage_univ] at ht
  have hup := ae_condExp_eq_of_trace (𝒦 := 𝒦) le_sup_left
    (retLineSigma_le hh u₀ η₁ η₂ hζ₁ hζ₂ hc₁ hc₂ hm₁ hm₂ d.u d.r) htr
    (GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hh))
  set S := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hS
  have hsplit : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      Complex.exp (Complex.I * (S φ : ℂ)) •
        fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul, WholeField.centredField, ← Complex.exp_add]
    congr 1
    rw [sub_apply]
    push_cast
    ring
  have hsm := condExp_smul (μ := P) (Complex.exp (Complex.I * (S φ : ℂ)))
    (fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ))) 𝒦
  filter_upwards [hup, hsm, hlaw φ, hag, hag₁, hag₂] with ω hupω hsmω hlawω hagω e₁ e₂ hp hsupp
  obtain ⟨hG, a₁, a₂⟩ := hagω hp.1 hp.2.1
  have hE : ω ∈ d.E := mem_E_of_isDisjointPair hd hG a₁ a₂ hp
  have b₁ : ∀ s ≤ d.u, d.η₁ ω s = ηc₁ ω s := fun s hs => by
    rw [e₁ s, capTime_eq_of_lt hp.1 (lt_capR_left d.u d.r) hs]
    exact a₁ s hs
  have b₂ : ∀ t ≤ d.r, d.η₂ ω t = ηc₂ ω t := fun t ht => by
    rw [e₂ t, capTime_eq_of_lt hp.2.1 (lt_capR_right d.u d.r) ht]
    exact a₂ t ht
  have hKU : d.K ω ∩ H = cstUnion ηc₁ ηc₂ d.u d.r ω := by
    rw [RetData.K_of_mem hE, cstUnion_eq, prefixSet,
      image_congr fun s hs => b₁ s hs.2, image_congr fun t ht => b₂ t ht.2]
  obtain ⟨R, hR, hKR, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq
    (hd.isCompact_K ω).isClosed (hd.isCompact_K ω).isBounded
  have hcc : connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω)
      (((R + 1 : ℝ) : ℂ) * I) = d.D ω := by
    rw [← hKU, H_diff_inter_H, show d.D ω = H \ fillH (d.K ω) from rfl, hEq]
  have hzD : ((R + 1 : ℝ) : ℂ) * I ∈ d.D ω := by
    change ((R + 1 : ℝ) : ℂ) * I ∈ H \ fillH (d.K ω)
    rw [hEq]
    refine mem_connectedComponentIn ⟨?_, fun hz => ?_⟩
    · change 0 < (((R + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith only [hR]
    · have h1 := hKR hz
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hR])] at h1
      linarith only [h1]
  have hz : ((R + 1 : ℝ) : ℂ) * I ∈ H \ cstUnion ηc₁ ηc₂ d.u d.r ω := by
    rw [← hcc] at hzD
    exact connectedComponentIn_subset _ _ hzD
  have heup : P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
      retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ d.u d.r] ω =
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒦] ω := hupω (mem_univ ω)
  rw [heup, hsplit]
  refine hsmω.trans ?_
  rw [Pi.smul_apply, smul_eq_mul, hlawω _ hz (hcc ▸ hsupp), hcc, add_apply,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The capped versions, local-set mean, and Gaussian line kernel all exist.
The only mathematical inputs are the two flow lines and Lemma 7.5. -/
theorem exists_retDomain_kernel {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {x₁ x₂ θ₁ θ₂ : ℝ} (hL75 : Theorem15.Lemma75Statement.{v})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω →
      ω ∈ d.G ∧ (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧
        ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ t, Measurable fun ω => ηc₁ ω t) ∧ (∀ t, Measurable fun ω => ηc₂ ω t) ∧
      (∀ ω, ηc₁ ω 0 = x₁) ∧ (∀ ω, ηc₂ ω 0 = x₂) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t)) ∧
      IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        Lemma76Exit.IsDisjointPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r →
        tsupport φ ⊆ d.D ω →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ d.u d.r] ω =
          Complex.exp (Complex.I *
            ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
              (((1 / 2 : ℝ) * zeroGFFTestCov (d.D ω) φ φ : ℝ) : ℂ)) := by
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, h0₁, h0₂, ha₁, ha₂, g, hg, hlaw⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR d.u d.r) d.u d.r
  exact ⟨ηc₁, ηc₂, g, hc₁, hc₂, hm₁, hm₂, h0₁, h0₂, ha₁, ha₂, hg,
    ae_condExp_cexp_retDomain hd hh.1 (measurable_lifetime_of_isFlowLine hη₁)
      (measurable_lifetime_of_isFlowLine hη₂) hag hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hlaw⟩

end InteractingSLE.Restart.RetAux79

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.AStopSafeKernel

/-!
# The retained line kernel and filled line in the filled-union domain

Packet PROVE-T15-ASTOP-SAFE (item 5 of `RLC.OrdModel.AStopSourceInputs`, first continuation). At a later line
`(u + t, r)` of the first continuation where the second prefix is enclosed, the chart event of the line data fails
(the second tip is not adherent to the later domain) and the line is read in the exchanged later chart
(PROVE-T15-ORDDET6). The line kernel and the filled line are therefore stated here without any retained data, in the
complement of the filled union `ℍ \ fill(η₁[0,u] ∪ η₂[0,r])`:

* `ae_condExp_cexp_fill` (RETPLUMB's `ae_condExp_cexp_retDomain` with the domain the filled-union complement: the
  unbounded component of `ℍ` minus the stopped union is that complement, `HalfPlaneSep.exists_H_diff_fillH_eq`);
* **`exists_kernel_fill`**, **`exists_filled_line_fill`**: the capped versions, the local-set mean and the Gaussian line
  kernel, and the history-local filled line, at every live sample, in terms of the flow lines themselves.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.AStopSafe

open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)
open Restart Restart.RetAux79 Supp7 Sec7 Sec7.Lemma76F LocalSets WholeField

universe v

variable {Ω : Type v} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **The marked component kernel in the filled-union complement** (RETPLUMB's `ae_condExp_cexp_retDomain`, the
retained domain replaced by `ℍ \ fill(ηc₁[0,u] ∪ ηc₂[0,r])`; no chart event is needed). -/
theorem ae_condExp_cexp_fill (hh : Measurable h) (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂) {u r : ℝ≥0}
    {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω))
    (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t)
    (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR u r) (ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR u r) (ζ₂ ω) t))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hlaw : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
      ∀ z₀ ∈ H \ cstUnion ηc₁ ηc₂ u r ω,
        tsupport φ ⊆ connectedComponentIn (H \ cstUnion ηc₁ ηc₂ u r ω) z₀ →
        P[fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) |
          germSigma (cstUnion ηc₁ ηc₂ u r) (WholeField.centredField h u₀) ⊔
            MeasurableSpace.comap (cstHist ηc₁ ηc₂
              (fun ω => cutLife (ζ₁ ω) (capR u r))
              (fun ω => cutLife (ζ₂ ω) (capR u r)) u r) inferInstance] ω =
          Complex.exp (Complex.I * (g ω φ : ℂ)) *
            ((Real.exp (-(1 / 2) * zeroGFFTestCov
              (connectedComponentIn (H \ cstUnion ηc₁ ηc₂ u r ω) z₀) φ φ) : ℝ) : ℂ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, tsupport φ ⊆ H \ fillH (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r) →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
        retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ u r] ω =
        Complex.exp (Complex.I *
          ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov (H \ fillH (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r)) φ φ : ℝ) :
              ℂ)) := by
  classical
  set F := cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) (capR u r))
    (fun ω => cutLife (ζ₂ ω) (capR u r)) u r with hF
  set 𝒦 := germSigma (cstUnion ηc₁ ηc₂ u r) (WholeField.centredField h u₀) ⊔
    MeasurableSpace.comap F inferInstance with h𝒦
  let _ : MeasurableSpace Ω := mΩ
  have hcmp : ∀ᵐ ω ∂P, retHist76 η₁ η₂ ζ₁ ζ₂ u r ω = F ω := by
    filter_upwards [hag₁, hag₂] with ω e₁ e₂
    have a₁ : cappedPath η₁ ζ₁ (capR u r) ω = ηc₁ ω := (funext e₁).symm
    have a₂ : cappedPath η₂ ζ₂ (capR u r) ω = ηc₂ ω := (funext e₂).symm
    simp only [retHist76, cstHist, hF, a₁, a₂]
  have htr : ∀ B, MeasurableSet[retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ u r] B →
      MeasurableSet[aeSigma 𝒦 P] (B ∩ univ) := by
    intro B hB
    have ht := measurableSet_aeSigma_inter_of_ae
      (Ψ := retHist76 η₁ η₂ ζ₁ ζ₂ u r) (F := F) (𝒦 := 𝒦)
      le_sup_right MeasurableSet.univ
      (by filter_upwards [hcmp] with ω he using ⟨Iff.rfl, fun _ => he⟩) B hB
    rwa [preimage_univ] at ht
  have hup := ae_condExp_eq_of_trace (𝒦 := 𝒦) le_sup_left
    (retLineSigma_le hh u₀ η₁ η₂ hζ₁ hζ₂ hc₁ hc₂ hm₁ hm₂ u r) htr
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
  filter_upwards [hup, hsm, hlaw φ] with ω hupω hsmω hlawω hsupp
  have hKc : IsCompact (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r) :=
    (isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω))
  have hKU : (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r) ∩ H = cstUnion ηc₁ ηc₂ u r ω := (cstUnion_eq _ _ _ _ _).symm
  obtain ⟨R, hR, hKR, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hKc.isClosed hKc.isBounded
  have hcc : connectedComponentIn (H \ cstUnion ηc₁ ηc₂ u r ω)
      (((R + 1 : ℝ) : ℂ) * I) = H \ fillH (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r) := by
    rw [← hKU, H_diff_inter_H, hEq]
  have hzD : ((R + 1 : ℝ) : ℂ) * I ∈ H \ fillH (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r) := by
    rw [hEq]
    refine mem_connectedComponentIn ⟨?_, fun hz => ?_⟩
    · change 0 < (((R + 1 : ℝ) : ℂ) * I).im
      simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
      linarith only [hR]
    · have h1 := hKR hz
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith only [hR])] at h1
      linarith only [h1]
  have hz : ((R + 1 : ℝ) : ℂ) * I ∈ H \ cstUnion ηc₁ ηc₂ u r ω := by
    rw [← hcc] at hzD
    exact connectedComponentIn_subset _ _ hzD
  have heup : P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
      retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ u r] ω =
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | 𝒦] ω := hupω (mem_univ ω)
  rw [heup, hsplit]
  refine hsmω.trans ?_
  rw [Pi.smul_apply, smul_eq_mul, hlawω _ hz (hcc ▸ hsupp), hcc, add_apply,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

omit mΩ [IsProbabilityMeasure P] in
/-- On a live sample the capped union is the union of the flow-line prefixes. -/
theorem capped_union_eq {u r : ℝ≥0} {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} {ω : Ω}
    (e₁ : ∀ t, ηc₁ ω t = η₁ ω (capTime (capR u r) (ζ₁ ω) t))
    (e₂ : ∀ t, ηc₂ ω t = η₂ ω (capTime (capR u r) (ζ₂ ω) t))
    (hu : (u : ℝ≥0∞) < ζ₁ ω) (hr : (r : ℝ≥0∞) < ζ₂ ω) :
    ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r = η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r := by
  rw [image_congr fun s hs => (e₁ s).trans (by rw [capTime_eq_of_lt hu (lt_capR_left u r) hs.2]),
    image_congr fun s hs => (e₂ s).trans (by rw [capTime_eq_of_lt hr (lt_capR_right u r) hs.2])]

/-- **The line kernel in the filled-union complement at every live sample**: capped versions, the local-set mean and
the Gaussian kernel at the line `(u, r)`. -/
theorem exists_kernel_fill {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (u r : ℝ≥0) :
    ∃ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
      (∀ ω, Continuous (ηc₁ ω)) ∧ (∀ ω, Continuous (ηc₂ ω)) ∧
      (∀ t, Measurable fun ω => ηc₁ ω t) ∧ (∀ t, Measurable fun ω => ηc₂ ω t) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR u r) (ζ₁ ω) t)) ∧
      (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR u r) (ζ₂ ω) t)) ∧
      IsLocalSetMean (cstUnion ηc₁ ηc₂ u r) (WholeField.centredField h u₀) P g ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω →
        tsupport φ ⊆ H \ fillH (η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | retLineSigma P h u₀ η₁ η₂ ζ₁ ζ₂ ηc₁ ηc₂ u r] ω =
          Complex.exp (Complex.I *
            ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
              (((1 / 2 : ℝ) * zeroGFFTestCov (H \ fillH (η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r)) φ φ : ℝ) : ℂ)) := by
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, -, -, ha₁, ha₂, g, hg, hlaw⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement
      hκ hκ4 hb hh hη₁ hη₂ hu₀ (capR u r) u r
  refine ⟨ηc₁, ηc₂, g, hc₁, hc₂, hm₁, hm₂, ha₁, ha₂, hg, fun φ => ?_⟩
  filter_upwards [ae_condExp_cexp_fill hh.1 (measurable_lifetime_of_isFlowLine hη₁)
    (measurable_lifetime_of_isFlowLine hη₂) hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hlaw φ, ha₁, ha₂] with ω hk e₁ e₂ hu hr hsupp
  rw [← capped_union_eq e₁ e₂ hu hr] at hsupp ⊢
  exact hk hsupp

/-- **The filled-line input to (L) at every live sample**, in the filled-union complement. -/
theorem exists_filled_line_fill {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}
    (hL75 : Theorem15.Lemma75Statement.{v}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    (hu₀ : IsBoundedHarmonicExtension b jumps u₀) (u r : ℝ≥0) :
    ∃ B : Ω → Set ℂ,
      Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ u r, hittingSigma] B ∧
      (∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) ∧
      IsHistoryAvoidanceLocal (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r) B (centredField h u₀) P ∧
      ∀ᵐ ω ∂P, (u : ℝ≥0∞) < ζ₁ ω → (r : ℝ≥0∞) < ζ₂ ω →
        H \ B ω = H \ fillH (η₁ ω '' Icc 0 u ∪ η₂ ω '' Icc 0 r) := by
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, ha₁, ha₂, hloc⟩ :=
    exists_cstUnion_local_retSigma76 hL75 hκ hκ4 hb hh hη₁ hη₂ hu₀ u r
  refine ⟨fun ω => fillH (ηc₁ ω '' Icc 0 u ∪ ηc₂ ω '' Icc 0 r), ?_, ?_,
    isHistoryAvoidanceLocal_capped_fill_retSigma76 hc₁ hc₂ hm₁ hm₂ ha₁ ha₂ hloc, ?_⟩
  · exact @measurable_fillH_of_dyadic Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ u r) _
      (isDyadicHitMeasurable_capped_union_retSigma76 hc₁ hc₂ hm₁ hm₂ ha₁ ha₂)
      (fun ω => (isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω)))
  · intro ω
    exact ⟨fillH_subset_H _, isOpen_H_diff_fillH
      ((isCompact_Icc.image (hc₁ ω)).union (isCompact_Icc.image (hc₂ ω))).isBounded⟩
  · filter_upwards [ha₁, ha₂] with ω e₁ e₂ hu hr
    rw [capped_union_eq e₁ e₂ hu hr]

end InteractingSLE.RLC.AStopSafe

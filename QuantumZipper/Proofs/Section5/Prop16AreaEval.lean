import QuantumZipper.Proofs.Section5.Prop16AreaLocal

/-!
# Proposition 1.6, D4-a (part 2): the area pairing equals `locArea` on good samples

For every vague limit `μ` of `areaApprox γ x` on a set `V` with `ball 0 R ∩ ℍ ⊆ V ⊆ ℍ` and every
continuous compactly supported `f` vanishing outside `ball 0 R`, `∫ f dμ = locArea γ R f x`
(`integral_eq_locArea`). Proof: for nonnegative `g`, each `∫ g · bump R n dμ` is the limit of the
approximating integrals (the cut-off product is supported in `V`), it is finite, and monotone
convergence in `n` recovers `∫⁻ g dμ` because `μ` does not charge `ball 0 R \ ℍ ⊆ Vᶜ`. Then split
`f` into positive and negative parts (Bochner convention for non-integrable `f`).
Own elementary proof (see `Prop16AreaLocal.lean`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Area

theorem isOpen_hball (R : ℕ) : IsOpen (hball R) := Metric.isOpen_ball.inter isOpen_H

theorem hball_compl_nonempty (R : ℕ) : (hball R)ᶜ.Nonempty :=
  ⟨0, fun h => by simpa [H] using h.2⟩

theorem liApprox_eq_lintegral {γ : ℝ} {R : ℕ} {x : FieldSample} {V : Set ℂ} {μ : Measure ℂ}
    (hVH : V ⊆ H) (hBV : hball R ⊆ V) (hμ : IsVagueLimitOn V (areaApprox γ x) μ)
    {g : ℂ → ℝ} (hg : Continuous g) (hg0 : ∀ z, 0 ≤ g z) (hgc : HasCompactSupport g)
    (hgR : ∀ z, g z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) :
    liApprox γ R g x = ∫⁻ z, ENNReal.ofReal (g z) ∂μ := by
  have hstep : ∀ n : ℕ, ENNReal.ofReal (LQGMeas.areaFun γ (fun z => g z * bump R n z) x) =
      ∫⁻ z, ENNReal.ofReal (g z) * ENNReal.ofReal (bump R n z) ∂μ := by
    intro n
    have hc : Continuous fun z => g z * bump R n z := hg.mul (LQGMeas.continuous_openBump _ n)
    have hcs : HasCompactSupport fun z => g z * bump R n z := hgc.mul_right
    have hts : tsupport (fun z => g z * bump R n z) ⊆ V :=
      (tsupport_mul_subset_right.trans (LQGMeas.tsupport_openBump_subset _ n)).trans hBV
    have hlim : LQGMeas.areaFun γ (fun z => g z * bump R n z) x = ∫ z, g z * bump R n z ∂μ :=
      (hμ.2.2 _ hc hcs hts).liminf_eq
    have hfin : μ (tsupport fun z => g z * bump R n z) ≠ ⊤ := (hμ.2.1 _ hcs hts).ne
    obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
    have hint : Integrable (fun z => g z * bump R n z) μ :=
      (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
        (Measure.integrableOn_of_bounded (M := C) hfin hc.aestronglyMeasurable
          (Eventually.of_forall fun z => hC z))
    rw [hlim, ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun z =>
      mul_nonneg (hg0 z) (LQGMeas.openBump_nonneg _ _ _))]
    exact lintegral_congr fun z => ENNReal.ofReal_mul (hg0 z)
  have hmono : Monotone fun n z => ENNReal.ofReal (g z) * ENNReal.ofReal (bump R n z) := by
    intro m n hmn z
    exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (LQGMeas.openBump_mono _ z hmn))
  have hmeas : ∀ n, Measurable fun z => ENNReal.ofReal (g z) * ENNReal.ofReal (bump R n z) :=
    fun n => (ENNReal.measurable_ofReal.comp hg.measurable).mul
      (ENNReal.measurable_ofReal.comp (LQGMeas.continuous_openBump _ n).measurable)
  unfold liApprox
  simp_rw [hstep]
  rw [← lintegral_iSup hmeas hmono]
  refine lintegral_congr_ae ?_
  have hV : ∀ᵐ z ∂μ, z ∈ V := by
    rw [ae_iff]; exact hμ.1
  filter_upwards [hV] with z hz
  rw [← ENNReal.mul_iSup]
  have hb : ⨆ n : ℕ, ENNReal.ofReal (bump R n z) = (hball R).indicator 1 z :=
    LQGMeas.iSup_openBump (isOpen_hball R) (hball_compl_nonempty R) z
  rw [hb]
  by_cases hB : z ∈ hball R
  · simp [indicator_of_mem hB]
  · have : g z = 0 := by
      by_contra h
      exact hB ⟨hgR z h, hVH hz⟩
    simp [this]

theorem ofReal_max_zero (t : ℝ) : ENNReal.ofReal (max t 0) = ENNReal.ofReal t := by
  rcases le_total t 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- **Evaluation.** On a good sample, the area pairing is `locArea`. -/
theorem integral_eq_locArea {γ : ℝ} {R : ℕ} {x : FieldSample} {V : Set ℂ} {μ : Measure ℂ}
    (hVH : V ⊆ H) (hBV : hball R ⊆ V) (hμ : IsVagueLimitOn V (areaApprox γ x) μ)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hfR : ∀ z, f z ≠ 0 → z ∈ Metric.ball (0 : ℂ) R) :
    ∫ z, f z ∂μ = locArea γ R f x := by
  have hsub : ∀ g : ℂ → ℝ, (∀ z, g z ≠ 0 → f z ≠ 0) → HasCompactSupport g := fun g hg =>
    hfc.mono' fun z hz => subset_tsupport f (hg z hz)
  have habs := liApprox_eq_lintegral hVH hBV hμ (g := fun z => |f z|) hf.abs
    (fun z => abs_nonneg _) (hsub _ fun z h => by simpa using h)
    (fun z h => hfR z (by simpa using h))
  have hpos := liApprox_eq_lintegral hVH hBV hμ (g := fun z => max (f z) 0)
    (hf.max continuous_const) (fun z => le_max_right _ _)
    (hsub _ fun z h hf0 => h (by simp [hf0])) (fun z h => hfR z fun hf0 => h (by simp [hf0]))
  have hneg := liApprox_eq_lintegral hVH hBV hμ (g := fun z => max (-f z) 0)
    (hf.neg.max continuous_const) (fun z => le_max_right _ _)
    (hsub _ fun z h hf0 => h (by simp [hf0])) (fun z h => hfR z fun hf0 => h (by simp [hf0]))
  have hfin : HasFiniteIntegral f μ ↔ ∫⁻ z, ENNReal.ofReal |f z| ∂μ < ⊤ := by
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
  unfold locArea
  rw [habs, hpos, hneg]
  simp_rw [ofReal_max_zero]
  by_cases hI : ∫⁻ z, ENNReal.ofReal |f z| ∂μ < ⊤
  · rw [if_pos hI]
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part
      ⟨hf.aestronglyMeasurable, hfin.2 hI⟩
  · rw [if_neg hI]
    exact integral_undef fun hint => hI (hfin.1 hint.2)

end Prop16Area

end QuantumZipper

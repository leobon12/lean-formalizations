/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RelSafeS3
import InteractingSLE.Spec.Restart.FCK2RealizeLaws
import InteractingSLE.GFF.LocalSets.SubdomainCov

/-!
# GB6's relative safe law, part 4: integrability of the chart field on the record event

Packet PROVE-GB6-RELSAFE2. The fourth clause of `Q3Stop.HasRelSafe` asks the relative field `Hc φ` to be integrable
under the conditioned law. GB6's chart field is only constrained on the record event, so it is first cut to that
event; there, given the record, `Hc φ` is Gaussian with mean `∫ 𝔥_β φ` (`β` the conditional word,
`GB6.gb6_condDet_r1`) and variance `σ²_ℍ(φ)`. The words `β(r)` have heights in one finite set and boundedly many
jumps (`Q3Stop.gb6WordOfRec_bounded`), so the means are uniformly bounded, and the landed conditional Gaussian
first-moment theorem (`FCPlumb.integrable_of_condGaussian_bounded_mean`) gives integrability.

* `exists_bound_mean_gb6`: `|𝔥_β(z)| ≤ C` for all records and all `z`;
* `isCondGaussian_indicator_chartField`: the cut field is conditionally Gaussian given the record;
* **`integrable_indicator_chartField`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC zeroGFFTestCov)
open LQGMetric (TestOn DistOn)

namespace InteractingSLE.Supp8.RelSafeS

open Exist.StagedLaw Supp8.GB6 Restart

/-! ### A uniform bound for the means of GB6's words -/

theorem abs_mean_le_of_bounded {c : BoundaryWord} {M : ℝ} {N : ℕ} (hM : ∀ j, |c.2.2 j| ≤ M) (hN : c.1 ≤ N)
    (z : ℂ) : |c.mean z| ≤ M + N * (2 * M) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  unfold BoundaryWord.mean
  have hterm : ∀ j ∈ Finset.range c.1,
      |(c.2.2 j - c.2.2 (j + 1)) * (Complex.arg (z - c.2.1 j) / Real.pi)| ≤ 2 * M := by
    intro j _
    rw [abs_mul]
    have h1 : |c.2.2 j - c.2.2 (j + 1)| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [hM j, hM (j + 1)])
    have h2 : |Complex.arg (z - c.2.1 j) / Real.pi| ≤ 1 := by
      rw [abs_div, abs_of_pos Real.pi_pos, div_le_one Real.pi_pos]
      exact Complex.abs_arg_le_pi _
    calc |c.2.2 j - c.2.2 (j + 1)| * |Complex.arg (z - c.2.1 j) / Real.pi| ≤ 2 * M * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
      _ = 2 * M := mul_one _
  have hsum := Finset.abs_sum_le_sum_abs (fun j => (c.2.2 j - c.2.2 (j + 1)) *
    (Complex.arg (z - c.2.1 j) / Real.pi)) (Finset.range c.1)
  have hsum2 : ∑ j ∈ Finset.range c.1, |(c.2.2 j - c.2.2 (j + 1)) * (Complex.arg (z - c.2.1 j) / Real.pi)| ≤
      ∑ _j ∈ Finset.range c.1, 2 * M := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum2
  have hN' : (c.1 : ℝ) * (2 * M) ≤ N * (2 * M) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hN) (by linarith)
  calc |c.2.2 c.1 + ∑ j ∈ Finset.range c.1, (c.2.2 j - c.2.2 (j + 1)) * (Complex.arg (z - c.2.1 j) / Real.pi)|
      ≤ |c.2.2 c.1| + |∑ j ∈ Finset.range c.1, (c.2.2 j - c.2.2 (j + 1)) *
          (Complex.arg (z - c.2.1 j) / Real.pi)| := abs_add_le _ _
    _ ≤ M + N * (2 * M) := by linarith [hM c.1]

/-- **The means of GB6's conditional words are uniformly bounded.** -/
theorem exists_bound_mean_gb6 (κ θ : ℝ) (c : BoundaryWord) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : RecData) (z : ℂ), |(gb6WordOfRec κ θ c r).mean z| ≤ C := by
  obtain ⟨S, hS, N, hSN⟩ := Q3Stop.gb6WordOfRec_bounded κ θ c
  obtain ⟨M, hM⟩ := hS.bddAbove.union (hS.image (fun x => -x)).bddAbove |>.imp fun _ h => h
  have hM' : ∀ x ∈ S, |x| ≤ M := fun x hx => abs_le.2
    ⟨by have := hM (Or.inr ⟨x, hx, rfl⟩); linarith, hM (Or.inl hx)⟩
  have hM0 : ∀ r : RecData, 0 ≤ M := fun r => (abs_nonneg _).trans (hM' _ ((hSN r).1 0))
  by_cases hne : Nonempty RecData
  · obtain ⟨r₀⟩ := hne
    refine ⟨M + N * (2 * M), by have := hM0 r₀; positivity, fun r z => ?_⟩
    exact abs_mean_le_of_bounded (fun j => hM' _ ((hSN r).1 j)) (hSN r).2 z
  · exact ⟨0, le_rfl, fun r => absurd ⟨r⟩ hne⟩

theorem abs_integral_mean_mul_le {c : BoundaryWord} {C : ℝ} (hC : ∀ z, |c.mean z| ≤ C)
    (φ : TestOn upperHalfPlaneOpens) : |∫ z, c.mean z * φ z| ≤ C * ∫ z, |φ z| := by
  have hφi : Integrable (fun z => (φ : ℂ → ℝ) z) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have h := norm_integral_le_of_norm_le (hφi.norm.const_mul C)
    (Eventually.of_forall fun z => show ‖c.mean z * φ z‖ ≤ C * ‖φ z‖ by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC z) (norm_nonneg _))
  rw [Real.norm_eq_abs] at h
  rw [integral_const_mul] at h
  simpa only [Real.norm_eq_abs] using h

/-! ### The cut chart field is conditionally Gaussian given the record -/

section Gauss

variable {κ θ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h Hc : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
  {α : Ω → ℝ≥0 → ℂ} {c : BoundaryWord}

/-- The σ-algebra of the record of the flow prefix. -/
@[instance_reducible]
def recSigma {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) : MeasurableSpace Ω :=
  MeasurableSpace.comap (gb6Rec s Wα ζα) inferInstance

theorem zeroGFFTestCov_H_nonneg (φ : TestOn upperHalfPlaneOpens) : 0 ≤ zeroGFFTestCov H φ φ := by
  rw [LocalSets.zeroGFFTestCov_eq_inner_covVec QuantumZipper.isOpen_H subset_rfl]
  exact real_inner_self_nonneg

theorem cexp_mean_var (a v t : ℝ) :
    Complex.exp (Complex.I * ((t * a : ℝ) : ℂ) - ((t ^ 2 * v : ℝ) : ℂ) / 2) =
      Complex.exp (Complex.I * ((t * a : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * v)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The chart field cut to the record event is conditionally Gaussian given the record**, with mean the cut word
pairing and variance the cut `σ²_ℍ(φ)`. -/
theorem isCondGaussian_indicator_chartField (hκ : 0 < κ) (hG : IsGFFWithBoundaryData P h b J)
    (hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0) (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω)) (φ : TestOn upperHalfPlaneOpens) :
    Sec6.Prop65.IsCondGaussian (recSigma s Wα ζα) P
      ((gb6Rec s Wα ζα ⁻¹' gb6TS s).indicator fun ω => Hc ω φ)
      ((gb6Rec s Wα ζα ⁻¹' gb6TS s).indicator fun ω => ∫ z, (gb6WordOfRec κ θ c (gb6Rec s Wα ζα ω)).mean z * φ z)
      ((gb6Rec s Wα ζα ⁻¹' gb6TS s).indicator fun _ => zeroGFFTestCov H φ φ) (zeroGFFTestCov H φ φ) := by
  set rec := gb6Rec s Wα ζα with hrecdef
  have hrec : Measurable rec := (measurable_recOf_cfE hflc s).2
  have h𝒢 : recSigma s Wα ζα ≤ mΩ := hrec.comap_le
  set E : Set Ω := rec ⁻¹' gb6TS s with hEdef
  have hE𝒢 : MeasurableSet[recSigma s Wα ζα] E := ⟨gb6TS s, measurableSet_gb6TS s, rfl⟩
  have hEm : MeasurableSet E := h𝒢 _ hE𝒢
  have hrec𝒢 : Measurable[recSigma s Wα ζα] rec := Measurable.of_comap_le le_rfl
  have hφm : Measurable fun ω => Hc ω φ := (LQGMetric.measurable_distOn_apply φ).comp hHcm
  have hcov := zeroGFFTestCov_H_nonneg φ
  refine ⟨h𝒢, hφm.indicator hEm, ?_, ?_, fun ω => ?_, fun ω => ?_, fun t => ?_⟩
  · have hm : Measurable fun r : RecData => ∫ z, (gb6WordOfRec κ θ c r).mean z * φ z :=
      (BoundaryWord.measurable_integral_mean_mul φ).comp (measurable_gb6WordOfRec κ θ c)
    exact (hm.comp hrec𝒢).indicator hE𝒢
  · exact measurable_const.indicator hE𝒢
  · by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]; exact hcov
    · rw [indicator_of_notMem hω]
  · by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
    · rw [indicator_of_notMem hω]; exact hcov
  -- the conditional characteristic function
  have hr1 := gb6_condDet_r1 hκ hG hflc hα s hHcm hHc (t • φ)
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * (Hc ω (t • φ) : ℂ)) with hFdef
  have hFm : Measurable F :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((LQGMetric.measurable_distOn_apply (t • φ)).comp hHcm)))
  have hFi : Integrable F P := GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply (t • φ)).comp hHcm)
  have hsplit : (fun ω => Complex.exp (Complex.I * ((t * E.indicator (fun ω => Hc ω φ) ω : ℝ) : ℂ))) =
      E.indicator F + Eᶜ.indicator (fun _ => (1 : ℂ)) := by
    funext ω
    by_cases hω : ω ∈ E
    · simp only [Pi.add_apply, indicator_of_mem hω, indicator_of_notMem (notMem_compl_iff.2 hω), add_zero, hFdef]
      rw [map_smul, smul_eq_mul]
    · simp only [Pi.add_apply, indicator_of_notMem hω, indicator_of_mem (mem_compl hω), zero_add, mul_zero,
        Complex.ofReal_zero, Complex.exp_zero]
  have hc1 : P[E.indicator F | recSigma s Wα ζα] =ᵐ[P] E.indicator (P[F | recSigma s Wα ζα]) :=
    condExp_indicator hFi hE𝒢
  have hc2 : P[Eᶜ.indicator (fun _ => (1 : ℂ)) | recSigma s Wα ζα] = Eᶜ.indicator (fun _ => (1 : ℂ)) :=
    condExp_of_stronglyMeasurable h𝒢 ((measurable_const.indicator hE𝒢.compl).stronglyMeasurable)
      ((integrable_const (1 : ℂ)).indicator hEm.compl)
  rw [hsplit]
  refine (condExp_add (hFi.indicator hEm) ((integrable_const (1 : ℂ)).indicator hEm.compl) (recSigma s Wα ζα)).trans ?_
  rw [hc2]
  filter_upwards [hc1, hr1] with ω e1 e2
  rw [Pi.add_apply, e1]
  by_cases hω : ω ∈ E
  · have e2' : P[F | recSigma s Wα ζα] ω = gaussCF (gb6WordOfRec κ θ c (rec ω)) (t • φ) := e2 hω
    rw [indicator_of_mem hω, indicator_of_notMem (notMem_compl_iff.2 hω), add_zero, e2',
      indicator_of_mem hω, indicator_of_mem hω]
    unfold gaussCF
    have e3 : ∫ z, (gb6WordOfRec κ θ c (rec ω)).mean z * (t • φ) z =
        t * ∫ z, (gb6WordOfRec κ θ c (rec ω)).mean z * φ z := by
      rw [← integral_const_mul]
      congr 1
      funext z
      simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    have e4 : zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) ((t • φ : TestOn upperHalfPlaneOpens) : ℂ → ℝ)
        ((t • φ : TestOn upperHalfPlaneOpens) : ℂ → ℝ) = t ^ 2 * zeroGFFTestCov H φ φ :=
      LocalSets.zeroGFFTestCov_smul_self QuantumZipper.isOpen_H subset_rfl t φ
    rw [e3, e4]
    exact cexp_mean_var _ _ t
  · rw [indicator_of_notMem hω, indicator_of_mem (mem_compl hω), zero_add, indicator_of_notMem hω,
      indicator_of_notMem hω]
    simp

/-- **The chart field cut to the record event is integrable.** -/
theorem integrable_indicator_chartField (hκ : 0 < κ) (hG : IsGFFWithBoundaryData P h b J)
    (hflc : IsFlowLineDriver κ c.fn c.jumps θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0) (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H →
      IsChartTransport (ownComponentChart (fun r : ℝ => Wα r.toNNReal ω) s) (-1)
        (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (Hc ω)) (φ : TestOn upperHalfPlaneOpens) :
    Integrable ((gb6Rec s Wα ζα ⁻¹' gb6TS s).indicator fun ω => Hc ω φ) P := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_mean_gb6 κ θ c
  refine Restart.FCPlumb.integrable_of_condGaussian_bounded_mean
    (isCondGaussian_indicator_chartField (θ := θ) hκ hG hflc hα s hHcm hHc φ) (C := C * ∫ z, |φ z|) fun ω => ?_
  by_cases hω : ω ∈ gb6Rec s Wα ζα ⁻¹' gb6TS s
  · rw [indicator_of_mem hω, Real.norm_eq_abs]
    exact abs_integral_mean_mul_le (hC _) φ
  · rw [indicator_of_notMem hω, norm_zero]
    exact mul_nonneg hC0 (integral_nonneg fun _ => abs_nonneg _)

end Gauss

end InteractingSLE.Supp8.RelSafeS

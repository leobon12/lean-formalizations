/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.R1GlueChart
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# (R1) on the meeting branch: the glued conditional law of the chart field

Packet PROVE-RESTART-CPL7, (R1) of `FirstContactKernelClockStatement` (Lemma 7.8, p. 290). The per-box marked law of
PROVE-RESTART-CPL6 (`exists_fcUnion_marked_of_isFlowLine`, the two flow lines capped at `m`, given the germs and the
capped retained histories) is glued over the countably many boxes into **one** conditional law, given the retained
σ-algebra `retSigma d P` of the uncapped retained histories, on the meeting branch `meetSet d` (Lemma 7.7's proof:
"Finite common-contact realizations are covered by countably many bounded grid boxes", p. 288):

* on the box `m` the capped first-contact union is the first-contact compact `d.K` (`fcUnion_eq_K_of_good`) and the
  chart domain `d.D` is one of its complementary components (`D_eq_connectedComponentIn`);
* `ae_condExp_exp_eq_meetBox`: on the box `m`, given `𝒦_m ⊔ retSigma d P` (`𝒦_m` CPL6's σ-algebra of the germs and the
  capped histories), the field paired with a test function supported in `d.D` is Gaussian with mean `g_m + 𝔥₀` and the
  zero-boundary variance of `d.D` (`ae_condExp_eq_of_trace`: on the box the retained histories add nothing);
* **`ae_condExp_cexp_chartField_eq_gaussCF_meetSet`**: (R1) for the canonical chart field of CPL4, given the retained
  σ-algebra, on the meeting branch, **from Lemma 7.8's mean identification** `hmean` (in each box: the chart
  transport of the conditional mean is the word mean of the datum `β`), with the chart rebuilt from the retained
  histories (`stopData`, `chartField_stopData_eq`), the tower property and the localization on the boxes;
* `ae_mem_meetSet`: almost surely every first contact with two nonempty continuations is on the meeting branch.

The mean identification is Lemma 7.8's formula `𝒞_K = 𝔤 ∘ φ − χ arg φ′` on `D` (Aux. 27, 29, 57, 78, 80 and the nested
boundary comparisons), stated here as the hypothesis `hmean` for every box and every version of the local-set mean.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TopologicalSpace Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Restart

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets Sec6

/-! ### Deterministic geometry on a box -/

section Geom

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : PairData Ω}

/-- The chart domain is the component of each of its points in the complement of the first-contact compact. -/
theorem D_eq_connectedComponentIn (hd : d.IsMeasGood) (ω : Ω) {z₀ : ℂ} (hz₀ : z₀ ∈ d.D ω) :
    d.D ω = connectedComponentIn (H \ d.K ω) z₀ := by
  have hK := hd.isCompact_K ω
  obtain ⟨R, -, -, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hK.isClosed hK.isBounded
  have hD : d.D ω = H \ fillH (d.K ω) := rfl
  rw [hD, hEq] at hz₀ ⊢
  exact (connectedComponentIn_eq hz₀)

theorem nonempty_D (hd : d.IsMeasGood) (ω : Ω) : (d.D ω).Nonempty := by
  have hK := hd.isCompact_K ω
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  exact HalfPlaneSep.not_isBounded_H_diff_fillH hK.isClosed hK.isBounded (by
    rw [show H \ fillH (d.K ω) = d.D ω from rfl, hne]; exact Bornology.isBounded_empty)

omit mΩ in
/-- **On the box the capped first-contact union is the first-contact compact.** -/
theorem fcUnion_eq_K_of_good {η₁ η₂ ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (m : ℕ) {ω : Ω}
    (hbox : ω ∈ meetBox d m) (ha₁ : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s)
    (ha₂ : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t)
    (hc₁ : ∀ t, ηc₁ ω t = η₁ ω (capTime m (d.ζ₁ ω) t)) (hc₂ : ∀ t, ηc₂ ω t = η₂ ω (capTime m (d.ζ₂ ω) t))
    (heq : retHist d ω = fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) ω) :
    fcUnion ηc₁ ηc₂ ω = d.K ω ∩ H := by
  obtain ⟨hE, hs, ht, hsζ, htζ⟩ := mem_meetBox_iff.1 hbox
  have e₁ : recFst (fullHist ηc₁ ηc₂ ω) = d.s₀ ω := by
    have := congrArg (fun y : KHist × KHist => y.1.1.1) heq
    simp only [retHist, fcHist, khistOf, histOf, fcTime₁, hE, ↓reduceIte] at this
    exact this.symm
  have e₂ : recSnd (fullHist ηc₁ ηc₂ ω) = d.t₀ ω := by
    have := congrArg (fun y : KHist × KHist => y.2.1.1) heq
    simp only [retHist, fcHist, khistOf, histOf, fcTime₂, hE, ↓reduceIte] at this
    exact this.symm
  have i₁ : ηc₁ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.s₀ ω} = d.η₁ ω '' Icc 0 (d.s₀ ω) := by
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.s₀ ω} = Icc 0 (d.s₀ ω) := by
      ext t; simp [ENNReal.coe_le_coe]
    rw [hset]
    refine image_congr fun t htI => ?_
    have htle : (t : ℝ≥0∞) ≤ d.s₀ ω := ENNReal.coe_le_coe.2 htI.2
    rw [hc₁, capTime_of_le, ha₁ _ (htle.trans hsζ.le)]
    exact le_min (htle.trans hsζ.le) (ENNReal.coe_le_coe.2 (htI.2.trans hs.le))
  have i₂ : ηc₂ ω '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.t₀ ω} = d.η₂ ω '' Icc 0 (d.t₀ ω) := by
    have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ d.t₀ ω} = Icc 0 (d.t₀ ω) := by
      ext t; simp [ENNReal.coe_le_coe]
    rw [hset]
    refine image_congr fun t htI => ?_
    have htle : (t : ℝ≥0∞) ≤ d.t₀ ω := ENNReal.coe_le_coe.2 htI.2
    rw [hc₂, capTime_of_le, ha₂ _ (htle.trans htζ.le)]
    exact le_min (htle.trans htζ.le) (ENNReal.coe_le_coe.2 (htI.2.trans ht.le))
  rw [fcUnion_eq, e₁, e₂, i₁, i₂, PairData.K_of_mem hE, prefixSet]

theorem H_diff_inter_H (K : Set ℂ) : H \ (K ∩ H) = H \ K := by
  ext z; simp only [Set.mem_sdiff, mem_inter_iff, not_and]; tauto

/-- Measurability of pair data is monotone in the σ-algebra. -/
theorem PairData.IsMeasGood.mono_sigma {Ω : Type*} {𝒢 𝒦 : MeasurableSpace Ω} {d : PairData Ω}
    (hd : @PairData.IsMeasGood Ω 𝒢 d) (h : 𝒢 ≤ 𝒦) : @PairData.IsMeasGood Ω 𝒦 d :=
  @PairData.IsMeasGood.mk Ω 𝒦 d (h _ (@PairData.IsMeasGood.measurableSet_G Ω 𝒢 d hd))
    (fun t => (@PairData.IsMeasGood.meas₁ Ω 𝒢 d hd t).mono h le_rfl)
    (fun t => (@PairData.IsMeasGood.meas₂ Ω 𝒢 d hd t).mono h le_rfl)
    ((@PairData.IsMeasGood.measζ₁ Ω 𝒢 d hd).mono h le_rfl) ((@PairData.IsMeasGood.measζ₂ Ω 𝒢 d hd).mono h le_rfl)
    (@PairData.IsMeasGood.good Ω 𝒢 d hd)

end Geom

/-! ### The marked law on a box, given the enlarged σ-algebra -/

section Box

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {d : PairData Ω}

/-- **The marked law on the box `m`** (CPL6's law for the `m`-capped pair, transferred to the chart domain `d.D` and
to the enlarged σ-algebra `𝒦_m ⊔ retSigma d P`, and to the uncentred field `h = h⁰ + 𝔥₀`). -/
theorem ae_condExp_exp_eq_meetBox (hd : d.IsMeasGood) {u₀ : ℂ → ℝ} (hhm : Measurable h)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ d.ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ d.ζ₂ ω → d.η₂ ω t = η₂ ω t)
    (m : ℕ) {ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ} (hc₁ : ∀ ω, Continuous (ηc₁ ω)) (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hm₁ : ∀ t, Measurable fun ω => ηc₁ ω t) (hm₂ : ∀ t, Measurable fun ω => ηc₂ ω t)
    (hag₁ : ∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (d.ζ₁ ω) t))
    (hag₂ : ∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (d.ζ₂ ω) t))
    {g : Ω → DistOn upperHalfPlaneOpens}
    (hlaw : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ∀ z₀ ∈ H \ fcUnion ηc₁ ηc₂ ω,
      tsupport φ ⊆ connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀ →
      P[fun ω' => Complex.exp (Complex.I * (WholeField.centredField h u₀ ω' φ : ℂ)) |
          germSigma (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) ⊔
            MeasurableSpace.comap
              (fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m)) inferInstance] ω =
        Complex.exp (Complex.I * (g ω φ : ℂ)) *
          ((Real.exp (-(1 / 2) *
            QuantumZipper.zeroGFFTestCov (connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀) φ φ) : ℝ) : ℂ))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → tsupport φ ⊆ d.D ω →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) |
          (germSigma (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) ⊔
            MeasurableSpace.comap (fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m))
              inferInstance) ⊔ retSigma d P] ω =
        Complex.exp (Complex.I *
            ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov (d.D ω) φ φ : ℝ) : ℂ)) := by
  set h₀ := WholeField.centredField h u₀ with hh₀
  set S := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hS
  set F := fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m) with hF
  set 𝒦 := germSigma (fcUnion ηc₁ ηc₂) h₀ ⊔ MeasurableSpace.comap F inferInstance with h𝒦def
  let _ : MeasurableSpace Ω := mΩ
  have hh₀m : Measurable h₀ := WholeField.measurable_centredField hhm u₀
  have hFm : Measurable F := measurable_fcHist hm₁ hm₂ ((measurable_cutLife m).comp hd.measζ₁)
    ((measurable_cutLife m).comp hd.measζ₂)
  have h𝒦 : 𝒦 ≤ mΩ := sup_le (germSigma_le (measurable_fcUnion hc₁ hc₂ hm₁ hm₂) hh₀m) hFm.comap_le
  have h𝒦' : 𝒦 ⊔ retSigma d P ≤ mΩ := sup_le h𝒦 (retSigma_le P)
  have hcmp := ae_retHist_eq_fcHist hd hc₁ hc₂ m hae hag₁ hag₂
  have htr : ∀ B, MeasurableSet[𝒦 ⊔ retSigma d P] B → MeasurableSet[aeSigma 𝒦 P] (B ∩ meetBox d m) :=
    measurableSet_aeSigma_inter_of_ae (Ψ := retHist d) (F := F) le_sup_right (measurableSet_boxSet m) hcmp
  have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hhm)
  have h1 := ae_condExp_eq_of_trace le_sup_left h𝒦' htr hXi
  have hsplit : (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) =
      Complex.exp (Complex.I * (S φ : ℂ)) • fun ω' => Complex.exp (Complex.I * (h₀ ω' φ : ℂ)) := by
    funext ω'
    simp only [Pi.smul_apply, smul_eq_mul, hh₀, WholeField.centredField, ← Complex.exp_add]
    congr 1
    rw [sub_apply]
    push_cast
    ring
  have h2 := condExp_smul (μ := P) (Complex.exp (Complex.I * (S φ : ℂ)))
    (fun ω' => Complex.exp (Complex.I * (h₀ ω' φ : ℂ))) 𝒦
  filter_upwards [h1, h2, hlaw φ, hcmp, hae, hag₁, hag₂] with ω e1 e2 e3 hcmpω haeω hc₁' hc₂' hbox hsupp
  obtain ⟨-, heq⟩ := hcmpω
  obtain ⟨-, ha₁, ha₂⟩ := haeω
  rw [e1 hbox, hsplit, e2]
  have hU : fcUnion ηc₁ ηc₂ ω = d.K ω ∩ H := fcUnion_eq_K_of_good m hbox ha₁ ha₂ hc₁' hc₂' (heq hbox)
  obtain ⟨z₀, hz₀⟩ := nonempty_D hd ω
  have hDcc := D_eq_connectedComponentIn hd ω hz₀
  have hz₀' : z₀ ∈ H \ fcUnion ηc₁ ηc₂ ω := by
    rw [hU, H_diff_inter_H]
    exact HalfPlaneSep.H_diff_fillH_subset_H_diff (hd.isCompact_K ω).isClosed hz₀
  have hcc : connectedComponentIn (H \ fcUnion ηc₁ ηc₂ ω) z₀ = d.D ω := by
    rw [hU, H_diff_inter_H, ← hDcc]
  rw [Pi.smul_apply, smul_eq_mul, e3 z₀ hz₀' (hcc ▸ hsupp), hcc, add_apply,
    Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Box

/-! ### (R1) on the meeting branch -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **Lemma 7.8's mean identification on every box** (the hypothesis of the glued (R1)): for every cap `m`, every pair
of capped versions of the two flow lines and every version `g` of the conditional mean of the centred field given the
germs of their first-contact union, almost surely on the box `m` the chart transport of the conditional mean `g + 𝔥₀`
of the field is the word mean of the datum `β`. -/
def IsBoxMeanIdentification (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (η₁ η₂ : Ω → ℝ≥0 → ℂ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) {d : PairData Ω} (hd : d.IsMeasGood) (β : Ω → BoundaryWord) : Prop :=
  ∀ (m : ℕ) (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime m (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime m (ζ₂ ω) t)) →
    IsLocalSetMean (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
        (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, (β ω).mean z * φ z

/-- **(R1) on the meeting branch** (Lemma 7.8, p. 290; Lemma 7.7's bounded grid boxes, p. 288). Two flow lines as in
`FirstContactKernelClockStatement`, measurable pair data `d` agreeing with them, the canonical chart field
`hd.chartField κ h`: given the retained σ-algebra `retSigma d P` of the two labelled histories stopped at the first
contact, on the meeting branch `meetSet d` the chart field has the Gaussian characteristic functional of the word
datum `β`, as soon as `β` is measurable for the retained σ-algebra and Lemma 7.8's mean identification holds on every
box (`IsBoxMeanIdentification`). Inputs: Lemma 7.5, Lemma 7.7, and Aux. lemma 56 at first entrances
(`RetainedRangeEntranceStatement`), through PROVE-RESTART-CPL6's per-box marked law. -/
theorem ae_condExp_cexp_chartField_eq_gaussCF_meetSet (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u}) (hA56 : RetainedRangeEntranceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ < x₁) (hθ : θ₁ < θ₂ + Real.pi)
    (hh : IsGFFWithBoundaryData P h b jumps) (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁)
    (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) {d : PairData Ω} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁)
    (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hβ : Measurable[retSigma d P] β) (hmean : IsBoxMeanIdentification κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ meetSet d →
      P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | retSigma d P] ω =
        gaussCF (β ω) φ := by
  subst hζ₁ hζ₂
  have hG : ∀ᵐ ω ∂P, ω ∈ d.G := hae.mono fun ω h => h.1
  have hdS := hd.isMeasGood_stopData hG
  have hhm : Measurable h := hh.1
  have hYm : StronglyMeasurable[retSigma d P] fun ω => gaussCF (β ω) φ := by
    let _ : MeasurableSpace Ω := retSigma d P
    exact ((measurable_gaussCF φ).comp hβ).stronglyMeasurable
  have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp (hd.measurable_chartField κ hhm))
  suffices hbox : ∀ m : ℕ, ∀ᵐ ω ∂P, ω ∈ meetBox d m →
      P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | retSigma d P] ω =
        gaussCF (β ω) φ by
    filter_upwards [ae_all_iff.2 hbox] with ω hω hmem
    obtain ⟨m, hm⟩ := mem_iUnion.1 hmem
    exact hω m hm
  intro m
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, hag₁, hag₂, g, hg, hlaw⟩ :=
    exists_fcUnion_marked_of_isFlowLine hL75 hL77 hA56 hκ hκ4 hb hx hθ hh hη₁ hη₂ hu₀ m
  set 𝒦 := (germSigma (fcUnion ηc₁ ηc₂) (WholeField.centredField h u₀) ⊔
    MeasurableSpace.comap (fcHist ηc₁ ηc₂ (fun ω => cutLife (d.ζ₁ ω) m) (fun ω => cutLife (d.ζ₂ ω) m))
      inferInstance) ⊔ retSigma d P with h𝒦def
  let _ : MeasurableSpace Ω := mΩ
  have hFm := measurable_fcHist hm₁ hm₂ ((measurable_cutLife m).comp hd.measζ₁)
    ((measurable_cutLife m).comp hd.measζ₂)
  have h𝒦 : 𝒦 ≤ mΩ := sup_le (sup_le (germSigma_le (measurable_fcUnion hc₁ hc₂ hm₁ hm₂)
    (WholeField.measurable_centredField hhm u₀)) hFm.comap_le) (retSigma_le P)
  have h𝒢𝒦 : retSigma d P ≤ 𝒦 := le_sup_right
  have hdK := hdS.mono_sigma h𝒢𝒦
  have hbox𝒦 : MeasurableSet[𝒦] (meetBox d m) := h𝒢𝒦 _ (hd.measurableSet_meetBox P m)
  -- the marked law on the box, on the domain of the stopped chart
  have hcond : ∀ ψ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ meetBox d m → tsupport ψ ⊆ (stopData d).D ω →
      P[fun ω => Complex.exp (Complex.I * (h ω ψ : ℂ)) | 𝒦] ω =
        Complex.exp (Complex.I *
            ((g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((stopData d).D ω) ψ ψ : ℝ) : ℂ)) := by
    intro ψ
    filter_upwards [ae_condExp_exp_eq_meetBox hd hhm hae m hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hlaw ψ, hG]
      with ω hω hωG hbox hsupp
    rw [D_stopData_eq hd hωG] at hsupp ⊢
    exact hω hbox hsupp
  -- the mean identification in the stopped chart
  have hmean' : ∀ᵐ ω ∂P, ω ∈ meetBox d m → ∀ ψ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (@PairData.IsMeasGood.isConformal_chart Ω 𝒦 (stopData d) hdK ω) 1 0
        (QuantumZipper.chiC κ) (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) ψ =
        ∫ z, (β ω).mean z * ψ z := by
    filter_upwards [hmean m ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg, hG] with ω hω hωG hbox ψ
    rw [chartTransport_congr_chart (chart_stopData_eq hd hωG) _ (hd.isConformal_chart ω)]
    exact hω hbox ψ
  have hR1 := ae_condExp_cexp_chartField_eq_gaussCF_on h𝒦 hdK κ hhm hbox𝒦 hcond hmean' φ
  -- replace the stopped chart field by the chart field of `d`
  have hXiS : Integrable (fun ω' => Complex.exp (Complex.I *
      (@PairData.IsMeasGood.chartField Ω 𝒦 (stopData d) hdK κ h ω' φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp
      ((hdS.mono_sigma (retSigma_le P)).measurable_chartField κ hhm))
  have hloc := ae_condExp_congr_on (𝒦 := 𝒦) hbox𝒦 hXi hXiS
    (hG.mono fun ω hωG _ => by
      rw [show @PairData.IsMeasGood.chartField Ω 𝒦 (stopData d) hdK κ h ω =
        hd.chartField κ h ω from chartField_stopData_eq hd hG κ h hωG])
  have hon : ∀ᵐ ω ∂P, ω ∈ meetBox d m →
      P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒦] ω = gaussCF (β ω) φ := by
    filter_upwards [hR1, hloc] with ω h1 h2 hbox
    rw [h2 hbox, h1 hbox]
  exact ae_condExp_eq_on_of_le h𝒢𝒦 h𝒦 hXi hYm (fun ω => norm_gaussCF_le _ _)
    (hd.measurableSet_meetBox P m) hon

omit [IsProbabilityMeasure P] in
/-- **Almost surely every first contact with two nonempty continuations is on the meeting branch.** -/
theorem ae_mem_meetSet {d : PairData Ω} (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω t = η₂ ω t) :
    ∀ᵐ ω ∂P, ∀ s₀ t₀ : ℝ≥0, IsFirstContact (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) s₀ t₀ →
      (s₀ : ℝ≥0∞) < ζ₁ ω → (t₀ : ℝ≥0∞) < ζ₂ ω → ω ∈ meetSet d := by
  subst hζ₁ hζ₂
  filter_upwards [hae] with ω ⟨hG, ha₁, ha₂⟩ s₀ t₀ hfc hs ht
  obtain ⟨hE, e₁, e₂⟩ := PairData.eq_of_isFirstContact hG ((isFirstContact_congr ha₁ ha₂).2 hfc)
  exact mem_meetSet_iff.2 ⟨hE, e₁ ▸ hs, e₂ ▸ ht⟩

end Main

end Restart

end InteractingSLE

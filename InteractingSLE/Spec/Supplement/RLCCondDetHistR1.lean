/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma76FR1
import InteractingSLE.Spec.Supplement.G7RetainedPath

/-!
# G7's (R1) on an arbitrary event of retained pairs

Packet PROVE-CONDDET-HIST. Lemma 7.6's `Sec7.Lemma76F.exists_r1_of_meanIdent` proves (R1) at a disjoint pair: the
disjoint-pair event is measurable for the stopped retained data (`Lemma76F.pairSet`). G7's ordinary retained pairs
(`Supp7.IsOrdinaryRetainedPair`) include W0's ordered proper completions, an existential over curves with no known
measurable form. This file proves (R1) on **any** event `O` of retained pairs on which the mean identification holds,
measurable or not, through the measurable hull of `O` in the conditioning σ-algebra:

* `ae_mem_of_mem_toMeasurable`: if `𝒢 ≤ mΩ` contains the `P`-null sets, a `𝒢`-event containing almost every point of
  `O` contains almost every point of the `𝒢`-hull of `O`;
* `IsRetMeanIdentOn`: `Lemma76F.IsRetMeanIdent` with the disjoint-pair event replaced by `O`;
* **`exists_r1_of_meanIdentOn`**: a σ-algebra `𝒢 ⊇ retSigma76` and a `𝒢`-event `M` containing almost every point of
  `O`, such that every `𝒢`-event containing almost all of `O` contains almost all of `M`, and (R1) holds on `M`;
* `exists_r1_of_meanIdentOrd`: the case of the ordinary retained pairs.

Ingredients: PROVE-T15-CLOSE1's marked kernel of the stopped union (`exists_cstUnion_marked_of_isFlowLine`), its
stopped retained data and trace argument, and PROVE-RESTART-CPL7's random chart transport
(`Restart.ae_condExp_cexp_chartTransport_random_on`).

R43/R48: Lemma 7.5 only; for Theorem 1.5.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE

namespace RLC

open Supp7 Restart Sec6 LocalSets LQGMetric Sec7.Lemma76F

/-! ### Measurable hulls in a sub-σ-algebra -/

section Hull

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **Events containing almost all of a set contain almost all of its hull.** Let `𝒢 ≤ mΩ` contain every `P`-null
measurable set. If a `𝒢`-event `A` contains almost every point of a (possibly non-measurable) set `O`, then it
contains almost every point of the `𝒢`-measurable hull of `O` (for the trimmed measure). -/
theorem ae_mem_of_mem_toMeasurable (h𝒢 : 𝒢 ≤ mΩ)
    (hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[𝒢] N) (O : Set Ω) {A : Set Ω}
    (hA : MeasurableSet[𝒢] A) (hOA : ∀ᵐ ω ∂P, ω ∈ O → ω ∈ A) :
    ∀ᵐ ω ∂P, ω ∈ @toMeasurable Ω 𝒢 (P.trim h𝒢) O → ω ∈ A := by
  have hTm : MeasurableSet[𝒢] (@toMeasurable Ω 𝒢 (P.trim h𝒢) O) :=
    @measurableSet_toMeasurable Ω 𝒢 (P.trim h𝒢) O
  have hB0 : P {ω | ¬ (ω ∈ O → ω ∈ A)} = 0 := ae_iff.1 hOA
  have hN0 : P (toMeasurable P {ω | ¬ (ω ∈ O → ω ∈ A)}) = 0 := by rw [measure_toMeasurable]; exact hB0
  have hNm : MeasurableSet[𝒢] (toMeasurable P {ω | ¬ (ω ∈ O → ω ∈ A)}) :=
    hnull _ (measurableSet_toMeasurable _ _) hN0
  have hON : O ∩ Aᶜ ⊆ toMeasurable P {ω | ¬ (ω ∈ O → ω ∈ A)} := fun ω hω =>
    subset_toMeasurable P _ (fun h => hω.2 (h hω.1))
  have h1 : P.trim h𝒢 (@toMeasurable Ω 𝒢 (P.trim h𝒢) O ∩ Aᶜ) = 0 := by
    rw [@Measure.measure_toMeasurable_inter Ω 𝒢 (P.trim h𝒢) _ _ hA.compl (measure_ne_top _ _)]
    refine le_antisymm ?_ zero_le
    calc P.trim h𝒢 (O ∩ Aᶜ) ≤ P.trim h𝒢 (toMeasurable P {ω | ¬ (ω ∈ O → ω ∈ A)}) := measure_mono hON
      _ = P (toMeasurable P {ω | ¬ (ω ∈ O → ω ∈ A)}) := trim_measurableSet_eq h𝒢 hNm
      _ = 0 := hN0
  have h2 : P (@toMeasurable Ω 𝒢 (P.trim h𝒢) O ∩ Aᶜ) = 0 := by
    rwa [trim_measurableSet_eq h𝒢 (hTm.inter hA.compl)] at h1
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h2
  simp only [mem_ofPred_eq, not_imp] at hω
  exact ⟨hω.1, hω.2⟩

end Hull

/-! ### The mean identification on an event -/

section Defs

variable {Ω : Type*}

/-- **The mean identification on an event `O`** (`Sec7.Lemma76F.IsRetMeanIdent` with the disjoint-pair event replaced
by `O`): for every pair of capped versions of the two flow lines (cap `capR u r`) and every version `g` of the local-set
mean of the centred field for their stopped union, almost surely on `O` the chart transport of the conditional mean
`g + 𝔥₀` is the word mean of the datum `β`. -/
def IsRetMeanIdentOn [MeasurableSpace Ω] (κ : ℝ) (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) {d : RetData Ω} (hd : d.IsMeasGood) (O : Set Ω)
    (β : Ω → BoundaryWord) : Prop :=
  ∀ (ηc₁ ηc₂ : Ω → ℝ≥0 → ℂ) (g : Ω → DistOn upperHalfPlaneOpens),
    (∀ ω, Continuous (ηc₁ ω)) → (∀ ω, Continuous (ηc₂ ω)) → (∀ t, Measurable fun ω => ηc₁ ω t) →
    (∀ t, Measurable fun ω => ηc₂ ω t) → (∀ᵐ ω ∂P, ∀ t, ηc₁ ω t = η₁ ω (capTime (capR d.u d.r) (ζ₁ ω) t)) →
    (∀ᵐ ω ∂P, ∀ t, ηc₂ ω t = η₂ ω (capTime (capR d.u d.r) (ζ₂ ω) t)) →
    IsLocalSetMean (cstUnion ηc₁ ηc₂ d.u d.r) (WholeField.centredField h u₀) P g →
    ∀ᵐ ω ∂P, ω ∈ O → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
        (g ω + SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀) φ =
        ∫ z, (β ω).mean z * φ z

/-- The chart event of retained data with both cutoffs before the lifetime records `L₁`, `L₂`. -/
def recEv (d : RetData Ω) (L₁ L₂ : Ω → ℝ≥0∞) : Set Ω :=
  d.E ∩ {ω | (d.u : ℝ≥0∞) < L₁ ω} ∩ {ω | (d.r : ℝ≥0∞) < L₂ ω}

theorem measurableSet_recEv [MeasurableSpace Ω] {d : RetData Ω} (hd : d.IsMeasGood) {L₁ L₂ : Ω → ℝ≥0∞}
    (hL₁ : Measurable L₁) (hL₂ : Measurable L₂) : MeasurableSet (recEv d L₁ L₂) :=
  (hd.measurableSet_E.inter (measurableSet_lt measurable_const hL₁)).inter (measurableSet_lt measurable_const hL₂)

end Defs

/-! ### (R1) on an event from the mean identification -/

section Main

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ}
  {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- **(R1) on an arbitrary event of retained pairs from the mean identification.** Let `O` be any set (measurable or
not) on which almost surely both cutoffs precede the lifetimes and the retained chart exists, and let `β` be a word
measurable for the retained σ-algebra with the mean identification on `O`. Then there are a sub-σ-algebra
`𝒢 ⊇ retSigma76` and a `𝒢`-event `M` containing almost every point of `O` such that every `𝒢`-event containing almost
all of `O` contains almost all of `M` (`M` is a measurable hull of `O`), and on `M`, conditionally on `𝒢`, the retained
chart field has the Gaussian characteristic functional of `β`. The proof of `Sec7.Lemma76F.exists_r1_of_meanIdent`,
with the disjoint-pair event replaced by the `𝒢`-hull of `O` inside the recorded chart event. -/
theorem exists_r1_of_meanIdentOn (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {O : Set Ω}
    (hO : ∀ᵐ ω ∂P, ω ∈ O → (d.u : ℝ≥0∞) < ζ₁ ω ∧ (d.r : ℝ≥0∞) < ζ₂ ω ∧ ω ∈ d.E)
    {β : Ω → BoundaryWord} (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd O β) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω), retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧
      MeasurableSet[𝒢.1] M ∧ (∀ᵐ ω ∂P, ω ∈ O → ω ∈ M) ∧
      (∀ A : Set Ω, MeasurableSet[𝒢.1] A → (∀ᵐ ω ∂P, ω ∈ O → ω ∈ A) → ∀ᵐ ω ∂P, ω ∈ M → ω ∈ A) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ := by
  classical
  set m := capR d.u d.r with hmdef
  have hum : d.u < m := lt_capR_left d.u d.r
  have hrm : d.r < m := lt_capR_right d.u d.r
  obtain ⟨ηc₁, ηc₂, hc₁, hc₂, hm₁, hm₂, h0₁, h0₂, hag₁, hag₂, g, hg, hlaw⟩ :=
    exists_cstUnion_marked_of_isFlowLine hL75 WholeField.retainedRangeEntranceStatement hκ hκ4 hb hh hη₁ hη₂ hu₀
      m d.u d.r
  set h₀ := WholeField.centredField h u₀ with hh₀
  set S := SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u₀ with hS
  set F := cstHist ηc₁ ηc₂ (fun ω => cutLife (ζ₁ ω) m) (fun ω => cutLife (ζ₂ ω) m) d.u d.r with hF
  set 𝒦 := germSigma (cstUnion ηc₁ ηc₂ d.u d.r) h₀ ⊔ MeasurableSpace.comap F inferInstance with h𝒦def
  set R := @retSigma76 Ω mΩ P η₁ η₂ ζ₁ ζ₂ d.u d.r with hRdef
  let _ : MeasurableSpace Ω := mΩ
  have hhm : Measurable h := hh.1
  have hh₀m : Measurable h₀ := WholeField.measurable_centredField hhm u₀
  have hζm₁ := measurable_lifetime_of_isFlowLine hη₁
  have hζm₂ := measurable_lifetime_of_isFlowLine hη₂
  have hFm : Measurable F := measurable_cstHist hm₁ hm₂ ((measurable_cutLife m).comp hζm₁)
    ((measurable_cutLife m).comp hζm₂) d.u d.r
  have h𝒦 : 𝒦 ≤ mΩ := sup_le (germSigma_le (measurable_cstUnion hc₁ hc₂ hm₁ hm₂ d.u d.r) hh₀m) hFm.comap_le
  have h𝒦R : 𝒦 ⊔ R ≤ mΩ := sup_le h𝒦 (retSigma76_le P η₁ η₂ ζ₁ ζ₂ d.u d.r)
  -- the stopped retained data, measurable for `𝒦`
  set d' := stopRet ηc₁ ηc₂ d.u d.r with hd'def
  have hd' : @RetData.IsMeasGood Ω 𝒦 d' :=
    isMeasGood_stopRet (ζ₁ := fun ω => cutLife (ζ₁ ω) m) (ζ₂ := fun ω => cutLife (ζ₂ ω) m) le_sup_right hc₁ hc₂
      h0₁ h0₂
  have hd'Ω : @RetData.IsMeasGood Ω mΩ d' := RetData.IsMeasGood.mono_sigma hd' h𝒦
  have hd'𝒢 : @RetData.IsMeasGood Ω (𝒦 ⊔ R) d' := RetData.IsMeasGood.mono_sigma hd' le_sup_left
  -- the lifetime records
  set L₁ : Ω → ℝ≥0∞ := fun ω => (F ω).1.2 with hL₁def
  set L₂ : Ω → ℝ≥0∞ := fun ω => (F ω).2.2 with hL₂def
  have hFm𝒦 : Measurable[𝒦] F := (comap_measurable F).mono le_sup_right le_rfl
  have hL₁m : Measurable[𝒦] L₁ := measurable_snd.comp (measurable_fst.comp hFm𝒦)
  have hL₂m : Measurable[𝒦] L₂ := measurable_snd.comp (measurable_snd.comp hFm𝒦)
  have hL₁ : ∀ ω, (d.u : ℝ≥0∞) < L₁ ω ↔ (d.u : ℝ≥0∞) < ζ₁ ω := fun ω => lt_lifeRec_cutLife_iff hum (ζ₁ ω)
  have hL₂ : ∀ ω, (d.r : ℝ≥0∞) < L₂ ω ↔ (d.r : ℝ≥0∞) < ζ₂ ω := fun ω => lt_lifeRec_cutLife_iff hrm (ζ₂ ω)
  set Sv := recEv d' L₁ L₂ with hSvdef
  have hSv : MeasurableSet[𝒦] Sv := @measurableSet_recEv Ω 𝒦 d' hd' L₁ L₂ hL₁m hL₂m
  -- almost sure pathwise facts
  have hstop₁ : ∀ ω, ∀ s ≤ d.u, d'.η₁ ω s = hproj (ηc₁ ω s) := fun ω s hs => by
    show hproj (ηc₁ ω (min s d.u)) = _
    rw [min_eq_left hs]
  have hstop₂ : ∀ ω, ∀ t ≤ d.r, d'.η₂ ω t = hproj (ηc₂ ω t) := fun ω t ht => by
    show hproj (ηc₂ ω (min t d.r)) = _
    rw [min_eq_left ht]
  have hgood : ∀ᵐ ω ∂P, ((∀ s ≤ d.u, d'.η₁ ω s = ηc₁ ω s) ∧ (∀ t ≤ d.r, d'.η₂ ω t = ηc₂ ω t)) ∧
      ((d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧ ω ∈ d'.G ∧
        (∀ s ≤ d.u, d'.η₁ ω s = d.η₁ ω s) ∧ (∀ t ≤ d.r, d'.η₂ ω t = d.η₂ ω t) ∧
        (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t) := by
    filter_upwards [hag, hag₁, hag₂, Sec7.ae_im_nonneg_of_isFlowLine' hη₁, Sec7.ae_im_nonneg_of_isFlowLine' hη₂,
      ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂] with ω hagω e₁ e₂ hi₁ hi₂ hp₂
    have hA₁ : ∀ s ≤ d.u, d'.η₁ ω s = ηc₁ ω s := fun s hs => by
      rw [hstop₁ ω s hs, hproj_of_im_nonneg]
      rw [e₁ s]
      exact hi₁ _ (capTime_le m (ζ₁ ω) s)
    have hA₂ : ∀ t ≤ d.r, d'.η₂ ω t = ηc₂ ω t := fun t ht => by
      rw [hstop₂ ω t ht, hproj_of_im_nonneg]
      rw [e₂ t]
      exact hi₂ _ (capTime_le m (ζ₂ ω) t)
    refine ⟨⟨hA₁, hA₂⟩, fun hu hr => ?_⟩
    obtain ⟨hG, a₁, a₂⟩ := hagω hu hr
    have b₁ : ∀ s ≤ d.u, d'.η₁ ω s = η₁ ω s := fun s hs => by
      rw [hA₁ s hs, e₁ s, capTime_eq_of_lt hu hum hs]
    have b₂ : ∀ t ≤ d.r, d'.η₂ ω t = η₂ ω t := fun t ht => by
      rw [hA₂ t ht, e₂ t, capTime_eq_of_lt hr hrm ht]
    refine ⟨hG, ?_, fun s hs => (b₁ s hs).trans (a₁ s hs).symm, fun t ht => (b₂ t ht).trans (a₂ t ht).symm, a₁, a₂⟩
    intro t ht he
    have he' : d'.η₂ ω t = d'.η₂ ω d.r := he
    rw [b₂ t ht.le, b₂ d.r le_rfl] at he'
    exact ht.ne (hp₂.1 ((ENNReal.coe_le_coe.2 ht.le).trans hr.le) hr.le he')
  -- `O` lies in the recorded chart event almost surely
  have hOS : ∀ᵐ ω ∂P, ω ∈ O → ω ∈ Sv := by
    filter_upwards [hO, hgood] with ω hω hgω hωO
    obtain ⟨hu, hr, hE⟩ := hω hωO
    obtain ⟨hG, hG', c₁, c₂, -, -⟩ := hgω.2 hu hr
    have hE' : ω ∈ d'.E :=
      (RetData.chart_eq_of_agree (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂) hG hG' c₁ c₂).1.2 hE
    exact ⟨⟨hE', (hL₁ ω).2 hu⟩, (hL₂ ω).2 hr⟩
  -- on the recorded chart event the two retained charts agree
  have hchart : ∀ᵐ ω ∂P, ω ∈ Sv → d'.chart ω = d.chart ω := by
    filter_upwards [hgood] with ω hω hωS
    obtain ⟨hG, hG', c₁, c₂, -, -⟩ := hω.2 ((hL₁ ω).1 hωS.1.2) ((hL₂ ω).1 hωS.2)
    exact (RetData.chart_eq_of_agree (G' := d'.G) (η₁' := d'.η₁) (η₂' := d'.η₂) hG hG' c₁ c₂).2.2
  -- the conditional law of the field on `Sv`, for test functions in the chart domain
  have hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ Sv → tsupport φ ⊆ (d'.chart ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦] ω =
        Complex.exp (Complex.I * ((g ω + S) φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((d'.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
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
    filter_upwards [h2, hlaw φ, hgood] with ω e2 e3 hω hωS hsupp
    rw [hsplit]
    refine (e2.trans ?_)
    have hωE : ω ∈ d'.E := hωS.1.1
    have hdom : ((d'.chart ω).dom : Set ℂ) = d'.D ω := @RetData.IsMeasGood.coe_dom_chart Ω 𝒦 d' hd' ω
    have hK := @RetData.IsMeasGood.isCompact_K Ω 𝒦 d' hd' ω
    obtain ⟨R0, hR0, hKR, hEq⟩ := HalfPlaneSep.exists_H_diff_fillH_eq hK.isClosed hK.isBounded
    have hDdef : d'.D ω = H \ fillH (d'.K ω) := rfl
    have hKU : d'.K ω ∩ H = cstUnion ηc₁ ηc₂ d.u d.r ω := by
      rw [RetData.K_of_mem hωE, cstUnion_eq, prefixSet, image_congr fun s hs => hω.1.1 s hs.2,
        image_congr fun t ht => hω.1.2 t ht.2]
      rfl
    have hcc : connectedComponentIn (H \ cstUnion ηc₁ ηc₂ d.u d.r ω) (((R0 + 1 : ℝ) : ℂ) * I) = d'.D ω := by
      rw [← hKU, H_diff_inter_H, hDdef, hEq]
    have hz₀D : ((R0 + 1 : ℝ) : ℂ) * I ∈ d'.D ω := by
      rw [hDdef, hEq]
      refine mem_connectedComponentIn ⟨?_, fun hz => ?_⟩
      · show (0 : ℝ) < (((R0 + 1 : ℝ) : ℂ) * I).im
        simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
        linarith
      · have h1 := hKR hz
        rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
        linarith
    have hz₀ : ((R0 + 1 : ℝ) : ℂ) * I ∈ H \ cstUnion ηc₁ ηc₂ d.u d.r ω := by
      have := hz₀D
      rw [← hcc] at this
      exact connectedComponentIn_subset _ _ this
    rw [hdom] at hsupp ⊢
    rw [Pi.smul_apply, smul_eq_mul, e3 _ hz₀ (hcc ▸ hsupp), hcc, add_apply,
      Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- the retained σ-algebra adds only null-set information
  have hΨF : ∀ᵐ ω ∂P, retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r ω = F ω := by
    filter_upwards [hag₁, hag₂] with ω e₁ e₂
    have p₁ : cappedPath η₁ ζ₁ (capR d.u d.r) ω = ηc₁ ω := funext fun t => (e₁ t).symm
    have p₂ : cappedPath η₂ ζ₂ (capR d.u d.r) ω = ηc₂ ω := funext fun t => (e₂ t).symm
    simp only [retHist76, cstHist, hF, p₁, p₂]
    rfl
  have htr : ∀ B, MeasurableSet[𝒦 ⊔ R] B → MeasurableSet[aeSigma 𝒦 P] (B ∩ univ) := by
    intro B hB
    have := measurableSet_aeSigma_inter_of_ae (Ψ := retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r) (F := F) (𝒦 := 𝒦) (P := P)
      le_sup_right MeasurableSet.univ (by filter_upwards [hΨF] with ω hω; exact ⟨by simp, fun _ => hω⟩) B hB
    rwa [preimage_univ] at this
  -- the hull of `O` in `𝒦 ⊔ R`
  have hnull : ∀ N : Set Ω, MeasurableSet N → P N = 0 → MeasurableSet[𝒦 ⊔ R] N := by
    intro N hN hN0
    refine (le_sup_right : R ≤ 𝒦 ⊔ R) N (MeasurableSpace.measurableSet_inf.2 ⟨hN, ∅,
      @MeasurableSet.empty _ (MeasurableSpace.comap (retHist76 η₁ η₂ ζ₁ ζ₂ d.u d.r) inferInstance), ?_⟩)
    exact ae_eq_empty.2 hN0
  set T := @toMeasurable Ω (𝒦 ⊔ R) (P.trim h𝒦R) O with hTdef
  have hT : MeasurableSet[𝒦 ⊔ R] T := @measurableSet_toMeasurable Ω (𝒦 ⊔ R) (P.trim h𝒦R) O
  have hull : ∀ A : Set Ω, MeasurableSet[𝒦 ⊔ R] A → (∀ᵐ ω ∂P, ω ∈ O → ω ∈ A) → ∀ᵐ ω ∂P, ω ∈ T → ω ∈ A :=
    fun A hA hOA => ae_mem_of_mem_toMeasurable h𝒦R hnull O hA hOA
  set M := T ∩ Sv with hMdef
  have hM : MeasurableSet[𝒦 ⊔ R] M := hT.inter ((le_sup_left : 𝒦 ≤ 𝒦 ⊔ R) _ hSv)
  have hOM : ∀ᵐ ω ∂P, ω ∈ O → ω ∈ M := by
    filter_upwards [hOS] with ω hω hωO
    exact ⟨@subset_toMeasurable Ω (𝒦 ⊔ R) (P.trim h𝒦R) O ω hωO, hω hωO⟩
  -- the conditional law of the field given `𝒦 ⊔ R` on `M`
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M → tsupport φ ⊆ (d'.chart ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒦 ⊔ R] ω =
        Complex.exp (Complex.I * ((g ω + S) φ : ℂ) -
          (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((d'.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp hhm)
    filter_upwards [ae_condExp_eq_of_trace (P := P) le_sup_left h𝒦R htr hXi, hcond φ] with ω e1 e2 hωM hsupp
    rw [e1 (mem_univ ω), e2 hωM.2 hsupp]
  obtain ⟨hdomm, hfwdm, hliftm⟩ := @RetData.IsMeasGood.chart_measurability Ω (𝒦 ⊔ R) d' hd'𝒢
  have hlaw' := fun φ => ae_condExp_cexp_chartTransport_random_on (𝒢 := 𝒦 ⊔ R) h𝒦R
    (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢) hdomm hfwdm hliftm
    (@RetData.IsMeasGood.continuousOn_lift_chart Ω (𝒦 ⊔ R) d' hd'𝒢) hhm (QuantumZipper.chiC κ) hM hcond' φ
  -- the mean identification on `M`, one test function at a time, through the hull
  have hgm : Measurable[𝒦 ⊔ R] fun ω => g ω + S := by
    refine (@LQGMetric.measurable_distOn_iff _ Ω (𝒦 ⊔ R) _).2 fun φ => ?_
    have e : (fun ω => (g ω + S) φ) = fun ω => g ω φ + S φ := funext fun ω => add_apply _ _ _
    rw [e]
    refine Measurable.add_const ?_ _
    exact ((LQGMetric.measurable_distOn_apply φ).comp hg.1).mono (le_sup_left.trans le_sup_left) le_rfl
  have hmeanM : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
      Chart.chartTransport (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢 ω) 1 0
        (QuantumZipper.chiC κ) (g ω + S) φ = ∫ z, (β ω).mean z * φ z := by
    intro φ
    have h1 : Measurable[𝒦 ⊔ R] fun ω => Chart.chartTransport
        (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢 ω) 1 0 (QuantumZipper.chiC κ) (g ω + S) φ :=
      (LQGMetric.measurable_distOn_apply φ).comp (@Chart.measurable_chartTransport_random' Ω (𝒦 ⊔ R) _
        (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢) hdomm hfwdm hliftm
        (@RetData.IsMeasGood.continuousOn_lift_chart Ω (𝒦 ⊔ R) d' hd'𝒢) _ hgm 1 0 (QuantumZipper.chiC κ))
    have h2 : Measurable[𝒦 ⊔ R] fun ω => ∫ z, (β ω).mean z * φ z :=
      (BoundaryWord.measurable_integral_mean_mul φ).comp (hβ.mono le_sup_right le_rfl)
    have hA : MeasurableSet[𝒦 ⊔ R] {ω | Chart.chartTransport
        (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢 ω) 1 0 (QuantumZipper.chiC κ) (g ω + S) φ =
          ∫ z, (β ω).mean z * φ z} :=
      measurableSet_eq_fun (m := 𝒦 ⊔ R) h1 h2
    have hOA := hmean ηc₁ ηc₂ g hc₁ hc₂ hm₁ hm₂ hag₁ hag₂ hg
    have hOA' : ∀ᵐ ω ∂P, ω ∈ O → ω ∈ {ω | Chart.chartTransport
        (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢 ω) 1 0 (QuantumZipper.chiC κ) (g ω + S) φ =
          ∫ z, (β ω).mean z * φ z} := by
      filter_upwards [hOA, hOS, hchart] with ω e hS' hch hωO
      show _ = _
      rw [chartTransport_congr_chart (hch (hS' hωO)) _ (hd.isConformal_chart ω)]
      exact e hωO φ
    filter_upwards [hull _ hA hOA'] with ω hω hωM
    exact hω hωM.1
  -- assembly
  refine ⟨⟨𝒦 ⊔ R, h𝒦R⟩, M, le_sup_right, hM, hOM, fun A hA hOA => ?_, fun φ => ?_⟩
  · filter_upwards [hull A hA hOA] with ω hω hωM using hω hωM.1
  · have hXi : Integrable (fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp (hd.measurable_chartField κ hhm))
    have hXi' : Integrable (fun ω' => Complex.exp (Complex.I *
        (Chart.chartTransport (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢 ω') 1 0
          (QuantumZipper.chiC κ) (h ω') φ : ℂ))) P :=
      GFF.integrable_exp_I_mul ((LQGMetric.measurable_distOn_apply φ).comp (hd'Ω.measurable_chartField κ hhm))
    have hloc := ae_condExp_congr_on (𝒦 := 𝒦 ⊔ R) hM hXi hXi'
      (by
        filter_upwards [hchart] with ω hch hωM
        show Complex.exp (Complex.I * (Chart.chartTransport (hd.isConformal_chart ω) 1 0 (QuantumZipper.chiC κ)
          (h ω) φ : ℂ)) = _
        rw [chartTransport_congr_chart (hch hωM.2).symm (hd.isConformal_chart ω)
          (@RetData.IsMeasGood.isConformal_chart Ω (𝒦 ⊔ R) d' hd'𝒢 ω)])
    filter_upwards [hloc, hlaw' φ, hmeanM φ] with ω e1 e2 e3 hωM
    show P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒦 ⊔ R] ω = _
    rw [e1 hωM, e2 hωM, e3 hωM, gaussCF]
    have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
    rw [hH]
    congr 1
    push_cast
    ring

/-- **(R1) at the ordinary retained pairs from the mean identification there** (`exists_r1_of_meanIdentOn` with `O` the
ordinary-pair event; an ordinary pair lies in the chart event, `RetData.IsMeasGood.mem_E_of_ordinary`). -/
theorem exists_r1_of_meanIdentOrd (hL75 : Theorem15.Lemma75Statement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {d : RetData Ω} (hd : d.IsMeasGood)
    (hag : ∀ᵐ ω ∂P, (d.u : ℝ≥0∞) < ζ₁ ω → (d.r : ℝ≥0∞) < ζ₂ ω → ω ∈ d.G ∧
      (∀ s ≤ d.u, d.η₁ ω s = η₁ ω s) ∧ ∀ t ≤ d.r, d.η₂ ω t = η₂ ω t)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω → BoundaryWord}
    (hβ : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r] β)
    (hmean : IsRetMeanIdentOn κ P h η₁ η₂ ζ₁ ζ₂ u₀ hd
      {ω | IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r} β) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω), retSigma76 P η₁ η₂ ζ₁ ζ₂ d.u d.r ≤ 𝒢.1 ∧
      MeasurableSet[𝒢.1] M ∧
      (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ω ∈ M) ∧
      (∀ A : Set Ω, MeasurableSet[𝒢.1] A →
        (∀ᵐ ω ∂P, IsOrdinaryRetainedPair (η₁ ω) (ζ₁ ω) d.u (η₂ ω) (ζ₂ ω) d.r → ω ∈ A) → ∀ᵐ ω ∂P, ω ∈ M → ω ∈ A) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (hd.chartField κ h ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ := by
  refine exists_r1_of_meanIdentOn hL75 hκ hκ4 hb hh hη₁ hη₂ hd hag hu₀ ?_ hβ hmean
  filter_upwards [hag] with ω hagω hord
  obtain ⟨hG, a₁, a₂⟩ := hagω hord.1 hord.2.1
  exact ⟨hord.1, hord.2.1, hd.mem_E_of_ordinary hG a₁ a₂ hord⟩

end Main

end RLC

end InteractingSLE

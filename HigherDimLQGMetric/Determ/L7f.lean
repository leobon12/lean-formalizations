import HigherDimLQGMetric.Determ.CopyTight
import HigherDimLQGMetric.Determ.LFPPProb

/-! Determination and convergence in probability of stable LFPP limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open HigherDimLFPP (Rd e₁)
open scoped ENNReal

namespace HigherDimLQGMetric

private theorem determ_scaled_marginal_law {d : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (h' : Ω' → DistRd d) (D' : Ω' → ContMetric d)
    (hh : Measurable h) (hD : Measurable D)
    (hh' : Measurable h') (hD' : Measurable D')
    (hlaw : P.map (fun ω => (h ω, D ω)) = P'.map (fun ω => (h' ω, D' ω)))
    (ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) :
    P.map (fun ω => normalizedAtScale ξ (fun _ => D ω) c (h ω) r) =
      P'.map (fun ω => normalizedAtScale ξ (fun _ => D' ω) c (h' ω) r) := by
  simpa only [scaledField_zero] using
    determ_scaled_law_transfer P P' h D h' D' hh hD hh' hD' hlaw ξ c r 0

/-- An outer-measure union bound; measurability of the three events is unnecessary. -/
private theorem determ_two_bad_events {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B₁ B₂ E : Set Ω) (p q : ℝ) (hq : 0 ≤ q)
    (hpq : p + 2 * q ≤ 1)
    (hcover : (Set.univ : Set Ω) ⊆ B₁ ∪ B₂ ∪ E)
    (hbad₁ : μ B₁ < ENNReal.ofReal q)
    (hbad₂ : μ B₂ < ENNReal.ofReal q) :
    ENNReal.ofReal p ≤ μ E := by
  have hb₁ : μ.real B₁ < q := by
    have := (ENNReal.toReal_lt_toReal (measure_ne_top μ B₁)
      ENNReal.ofReal_ne_top).2 hbad₁
    simpa [measureReal_def, ENNReal.toReal_ofReal hq] using this
  have hb₂ : μ.real B₂ < q := by
    have := (ENNReal.toReal_lt_toReal (measure_ne_top μ B₂)
      ENNReal.ofReal_ne_top).2 hbad₂
    simpa [measureReal_def, ENNReal.toReal_ofReal hq] using this
  have hwhole : (1 : ℝ) ≤ μ.real B₁ + μ.real B₂ + μ.real E := by
    calc
      (1 : ℝ) = μ.real (Set.univ : Set Ω) := by simp
      _ ≤ μ.real ((B₁ ∪ B₂) ∪ E) := measureReal_mono hcover
      _ ≤ μ.real (B₁ ∪ B₂) + μ.real E := measureReal_union_le _ _
      _ ≤ μ.real B₁ + μ.real B₂ + μ.real E := by
        gcongr
        exact measureReal_union_le _ _
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).2 (by
    change p ≤ μ.real E
    linarith)

/-- Cancel the common positive finite field normalization in the two shell bounds. -/
private theorem determ_shell_of_scaled_bounds {d : ℕ}
    (D₁ D₂ : ContMetric d) (z : Rd d) (r A : ℝ) (hA : 1 < A)
    (s : ℝ≥0∞) (hs0 : s ≠ 0) (hsTop : s ≠ ∞)
    (hlo : ENNReal.ofReal A⁻¹ ≤ s * acrossDist D₁ z (r / 2) r)
    (hup : s * sphereDiam D₂ z r ≤ ENNReal.ofReal A) :
    internalDiamRd D₂ (Metric.sphere z r) (shellOpen z (r / 2) (2 * r)) ≤
      ENNReal.ofReal (A * A) *
        infPairs D₁.1 (Metric.sphere z (r / 2)) (Metric.sphere z r) := by
  have hA0 : 0 < A := by linarith
  have hmul : ENNReal.ofReal A = ENNReal.ofReal (A * A) * ENNReal.ofReal A⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * A)]
    congr 1
    field_simp
  have hscaled : s * sphereDiam D₂ z r ≤
      s * (ENNReal.ofReal (A * A) * acrossDist D₁ z (r / 2) r) := by
    calc
      _ ≤ ENNReal.ofReal A := hup
      _ = ENNReal.ofReal (A * A) * ENNReal.ofReal A⁻¹ := hmul
      _ ≤ ENNReal.ofReal (A * A) * (s * acrossDist D₁ z (r / 2) r) := by
        gcongr
      _ = _ := by ac_rfl
  have hfinal := (ENNReal.mul_le_mul_iff_right hs0 hsTop).1 hscaled
  have hsame : (shellOpen z (r / 2) (2 * r) : Set (Rd d)) =
      ann z (r / 2) (2 * r) := by
    rw [ann_eq_ball_diff]
    rfl
  rw [hsame]
  simpa only [sphereDiam, acrossDist, internalDiamRd, infPairs] using hfinal

theorem l7f_determined_of
    (hL7a : ∀ d ξ κ, L7a_locality d ξ κ)
    (hcopies : L7b_copies) (_hshell : L7c_metricShell)
    (hbilip : L7d_bilip)
    (hL6 : ∀ d ξ κ, L6f_tightScales d ξ κ) :
    ∀ d ξ κ, L7f_determined d ξ κ := by
  intro d ξ κ hB2 hMarkov hDec εs hε hε0 Ω _ P _ h Dh hh hDm hstable
  have hB2' := hB2
  obtain ⟨Q, hDGZ, -⟩ := hB2
  have hd : 2 ≤ d := hDGZ.dim
  have hloc : IsXiAdditiveRd ξ P h Dh Dh :=
    hL7a d ξ κ hB2' hMarkov εs hε hε0 P h Dh hh hDm hstable
  have hlen : ∀ᵐ ω ∂P, (Dh ω).IsLength := hloc.2.2.1.mono fun _ hω => hω.1
  let c : ℝ → ℝ := fun r =>
    lowerMedian P (fun ω => Real.exp (-ξ * sphereAvg (h ω) r 0) *
      (Dh ω).1 (0, r • e₁ d))
  obtain ⟨hc, hT⟩ := hL6 d ξ κ hB2' εs hε hε0 P h Dh hh hDm hstable
  haveI : Nonempty Ω := ⟨(nonempty_of_measure_ne_zero
    (show P (Set.univ : Set Ω) ≠ 0 by simp)).choose⟩
  haveI : Nonempty (ContMetric d) := ⟨Dh (Classical.choice ‹Nonempty Ω›)⟩
  obtain ⟨ν, hν, hpair1, hpair2, hci⟩ :=
    l7b_conditional_copies P h Dh hh.1.measurable hDm
  letI : IsProbabilityMeasure ν := hν
  let hνf : Ω × ContMetric d → DistRd d := fun q => h q.1
  let D₁ : Ω × ContMetric d → ContMetric d := fun q => Dh q.1
  let D₂ : Ω × ContMetric d → ContMetric d := Prod.snd
  have hνm : Measurable hνf := hh.1.measurable.comp measurable_fst
  have hD₁m : Measurable D₁ := hDm.comp measurable_fst
  have hD₂m : Measurable D₂ := measurable_snd
  have hfieldLaw : P.map h = ν.map hνf := by
    calc
      P.map h = (P.map (fun ω => (h ω, Dh ω))).map Prod.fst := by
        rw [Measure.map_map (μ := P) measurable_fst (hh.1.measurable.prodMk hDm)]
        rfl
      _ = (ν.map (fun q => (hνf q, D₁ q))).map Prod.fst := by rw [hpair1]
      _ = ν.map hνf := by
        rw [Measure.map_map (μ := ν) measurable_fst (hνm.prodMk hD₁m)]
        rfl
  have hhν : IsNormalizedLGF hνf ν :=
    determ_normalized_law_transfer P ν h hνf hh hνm hfieldLaw
  have hloc1 : IsXiAdditiveRd ξ ν hνf D₁ D₁ :=
    determ_xiAdditive_law_transfer P ν h Dh hνf D₁
      hh.1.measurable hDm hνm hD₁m hpair1.symm ξ hloc
  have hloc2 : IsXiAdditiveRd ξ ν hνf D₂ D₂ :=
    determ_xiAdditive_law_transfer P ν h Dh hνf D₂
      hh.1.measurable hDm hνm hD₂m hpair2.symm ξ hloc
  have hloc12 : IsXiAdditiveRd ξ ν hνf D₁ D₂ :=
    hcopies d hd ξ ν hνf D₁ D₂ hhν hloc1 hloc2 hci
  have hlen1 : ∀ᵐ q ∂ν, (D₁ q).IsLength :=
    hloc1.2.2.1.mono fun _ hq => hq.1
  have hlen2 : ∀ᵐ q ∂ν, (D₂ q).IsLength :=
    hloc2.2.2.1.mono fun _ hq => hq.1
  have hnormLaw (j : Fin 2) (r : ℝ) :
      P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) =
        ν.map (fun q => normalizedAtScale ξ
          (fun _ => if j = 0 then D₁ q else D₂ q) c (hνf q) r) := by
    fin_cases j
    · exact determ_scaled_marginal_law P ν h Dh hνf D₁
        hh.1.measurable hDm hνm hD₁m hpair1.symm ξ c r
    · exact determ_scaled_marginal_law P ν h Dh hνf D₂
        hh.1.measurable hDm hνm hD₂m hpair2.symm ξ c r
  have hcenterLaw (j : Fin 2) (r : ℝ) (hr : 0 < r) (z : Rd d) :
      ν.map (fun q => scaledField ξ
        (fun _ => if j = 0 then D₁ q else D₂ q) c r z (hνf q)) =
      ν.map (fun q => normalizedAtScale ξ
        (fun _ => if j = 0 then D₁ q else D₂ q) c (hνf q) r) := by
    fin_cases j
    · calc
        _ = P.map (fun ω => scaledField ξ (fun _ => Dh ω) c r z (h ω)) :=
            (determ_scaled_law_transfer P ν h Dh hνf D₁ hh.1.measurable hDm
              hνm hD₁m hpair1.symm ξ c r z).symm
        _ = P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) :=
            determ_limit_centerLaw hd κ hDGZ.kernel ξ εs hε P h Dh hh hDm hstable c r hr z
        _ = _ := hnormLaw 0 r
    · calc
        _ = P.map (fun ω => scaledField ξ (fun _ => Dh ω) c r z (h ω)) :=
            (determ_scaled_law_transfer P ν h Dh hνf D₂ hh.1.measurable hDm
              hνm hD₂m hpair2.symm ξ c r z).symm
        _ = P.map (fun ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r) :=
            determ_limit_centerLaw hd κ hDGZ.kernel ξ εs hε P h Dh hh hDm hstable c r hr z
        _ = _ := hnormLaw 1 r
  have hnormMeas (j : Fin 2) (r : ℝ) : Measurable
      (fun q => normalizedAtScale ξ
        (fun _ => if j = 0 then D₁ q else D₂ q) c (hνf q) r) := by
    fin_cases j
    · simpa [scaledField_zero, Function.comp_def] using
        (determ_measurable_scaledPair ξ c r (0 : Rd d)).comp (hνm.prodMk hD₁m)
    · simpa [scaledField_zero, Function.comp_def] using
        (determ_measurable_scaledPair ξ c r (0 : Rd d)).comp (hνm.prodMk hD₂m)
  have hcenterMeas (j : Fin 2) (r : ℝ) (z : Rd d) : Measurable
      (fun q => scaledField ξ
        (fun _ => if j = 0 then D₁ q else D₂ q) c r z (hνf q)) := by
    fin_cases j
    · simpa [Function.comp_def] using
        (determ_measurable_scaledPair ξ c r z).comp (hνm.prodMk hD₁m)
    · simpa [Function.comp_def] using
        (determ_measurable_scaledPair ξ c r z).comp (hνm.prodMk hD₂m)
  have hTν (j : Fin 2) : TightFamily ν
      (fun r q => normalizedAtScale ξ
        (fun _ => if j = 0 then D₁ q else D₂ q) c (hνf q) r) (Ioi 0) :=
    determ_tightFamily_law_transfer P ν
      (fun r ω => normalizedAtScale ξ (fun _ => Dh ω) c (h ω) r)
      (fun r q => normalizedAtScale ξ
        (fun _ => if j = 0 then D₁ q else D₂ q) c (hνf q) r)
      (Ioi 0) hT (fun r _ => (hnormMeas j r).aemeasurable)
      (fun r _ => hnormLaw j r)
  have hbounds (j : Fin 2) (hlenj : ∀ᵐ q ∂ν,
      (if j = 0 then D₁ q else D₂ q).IsLength)
      (η : ℝ≥0∞) (hη : 0 < η) :
      ∃ A : ℝ, 1 < A ∧ ∀ r : ℝ, 0 < r → ∀ z : Rd d,
      ν {q | ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (hνf q) r z)) *
        acrossDist (if j = 0 then D₁ q else D₂ q) z (r / 2) r <
          ENNReal.ofReal A⁻¹} < η ∧
      ν {q | ENNReal.ofReal A <
        ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (hνf q) r z)) *
          sphereDiam (if j = 0 then D₁ q else D₂ q) z r} < η := by
    exact bilip_uniformShellBounds_limit_allCentres hd ν ξ hνf
      (fun q => if j = 0 then D₁ q else D₂ q) c hc (hTν j)
      (fun r hr z => (hcenterMeas j r z).aemeasurable)
      (hcenterLaw j) hlenj hη
  obtain ⟨p, hp, hp1, hbil⟩ := hbilip d hd
  let q : ℝ := (1 - p) / 4
  have hq : 0 < q := by dsimp [q]; linarith
  have hη : 0 < ENNReal.ofReal q := ENNReal.ofReal_pos.2 hq
  have hlen0 : ∀ᵐ q ∂ν, (if (0 : Fin 2) = 0 then D₁ q else D₂ q).IsLength := by
    simpa using hlen1
  have hlen1' : ∀ᵐ q ∂ν, (if (1 : Fin 2) = 0 then D₁ q else D₂ q).IsLength := by
    simpa using hlen2
  obtain ⟨A₁, hA₁, hb₁⟩ := hbounds 0 hlen0 (ENNReal.ofReal q) hη
  obtain ⟨A₂, hA₂, hb₂⟩ := hbounds 1 hlen1' (ENNReal.ofReal q) hη
  let A : ℝ := max A₁ A₂
  have hA : 1 < A := hA₁.trans_le (le_max_left _ _)
  have hAi : A⁻¹ ≤ A₁⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le (by linarith : 0 < A₁) (le_max_left A₁ A₂)
  have hAup : A₂ ≤ A := le_max_right _ _
  have hlow (z : Rd d) (r : ℝ) (hr : 0 < r) :
      ν {w | ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (hνf w) r z)) *
        acrossDist (D₁ w) z (r / 2) r < ENNReal.ofReal A⁻¹} <
          ENNReal.ofReal q := by
    refine lt_of_le_of_lt (measure_mono ?_) (hb₁ r hr z).1
    intro w hw
    exact lt_of_lt_of_le hw (ENNReal.ofReal_le_ofReal hAi)
  have hup (z : Rd d) (r : ℝ) (hr : 0 < r) :
      ν {w | ENNReal.ofReal A <
        ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (hνf w) r z)) *
          sphereDiam (D₂ w) z r} < ENNReal.ofReal q := by
    refine lt_of_le_of_lt (measure_mono ?_) (hb₂ r hr z).2
    intro w hw
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hAup) hw
  have hprob (z : Rd d) (r : ℝ) (hr : 0 < r) :
      ENNReal.ofReal p ≤ ν {w |
        internalDiamRd (D₂ w) (Metric.sphere z r)
          (shellOpen z (r / 2) (2 * r)) ≤
            ENNReal.ofReal (A * A) *
              infPairs (D₁ w).1 (Metric.sphere z (r / 2)) (Metric.sphere z r)} := by
    let S (w : Ω × ContMetric d) : ℝ≥0∞ :=
      ENNReal.ofReal ((c r)⁻¹ * Real.exp (-ξ * sphereAvg (hνf w) r z))
    let B₁ : Set (Ω × ContMetric d) :=
      {w | S w * acrossDist (D₁ w) z (r / 2) r < ENNReal.ofReal A⁻¹}
    let B₂ : Set (Ω × ContMetric d) :=
      {w | ENNReal.ofReal A < S w * sphereDiam (D₂ w) z r}
    let E : Set (Ω × ContMetric d) :=
      {w | internalDiamRd (D₂ w) (Metric.sphere z r)
        (shellOpen z (r / 2) (2 * r)) ≤
          ENNReal.ofReal (A * A) *
            infPairs (D₁ w).1 (Metric.sphere z (r / 2)) (Metric.sphere z r)}
    have hcover : (Set.univ : Set (Ω × ContMetric d)) ⊆ B₁ ∪ B₂ ∪ E := by
      intro w _
      by_cases h₁ : w ∈ B₁
      · exact Or.inl (Or.inl h₁)
      by_cases h₂ : w ∈ B₂
      · exact Or.inl (Or.inr h₂)
      right
      have hs0 : S w ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr
        (mul_pos (inv_pos.mpr (hc r hr)) (Real.exp_pos _))
      have hsTop : S w ≠ ∞ := ENNReal.ofReal_ne_top
      exact determ_shell_of_scaled_bounds (D₁ w) (D₂ w) z r A hA (S w)
        hs0 hsTop (not_lt.mp h₁) (not_lt.mp h₂)
    have hpq : p + 2 * q ≤ 1 := by dsimp [q]; linarith
    exact determ_two_bad_events ν B₁ B₂ E p q hq.le hpq hcover
      (hlow z r hr) (hup z r hr)
  have hbound : ∀ᵐ w ∂ν, ∀ x y : Rd d,
      (D₂ w).1 (x, y) ≤ (A * A) * (D₁ w).1 (x, y) :=
    hbil ξ ν hνf D₁ D₂ hhν hloc12 (A * A) (by positivity)
      hprob
  have hdetν : LQGMetric.AEDeterminedBy D₁ hνf ν :=
    l7e_of_measurable_copy ν hνf D₁ D₂ (A * A) hhν hloc1 hD₂m hci
      (hpair1.trans hpair2.symm) hbound
  obtain ⟨F, hF, hdetν'⟩ := hdetν
  have hset : MeasurableSet {t : DistRd d × ContMetric d | t.2 = F t.1} :=
    measurableSet_eq_fun measurable_snd (hF.comp measurable_fst)
  have hdetlaw : ∀ᵐ t ∂ν.map (fun w => (hνf w, D₁ w)), t.2 = F t.1 :=
    (ae_map_iff (hνm.prodMk hD₁m).aemeasurable hset).2 hdetν'
  rw [hpair1] at hdetlaw
  have hdetP : LQGMetric.AEDeterminedBy Dh h P :=
    ⟨F, hF, (ae_map_iff (hh.1.measurable.prodMk hDm).aemeasurable hset).1 hdetlaw⟩
  exact ⟨hdetP, determ_lfppSeq_prob_of_det ξ κ hB2' εs hε P h Dh hh hstable hdetP⟩

end HigherDimLQGMetric

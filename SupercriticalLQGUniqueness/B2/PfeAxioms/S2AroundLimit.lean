import SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.JointCompact
import SupercriticalLQGUniqueness.B2.PfeWeyl.AnnularJoining
import LQGMetric.Metric.CurveNatural
import SupercriticalLQGUniqueness.B2.PfeWeyl.Inputs

 

















set_option autoImplicit false
noncomputable section

open Set Filter Topology unitInterval
open scoped ENNReal NNReal
open LQGMetric.MetricGeometry

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem exists_lipschitz_reparam_range_eq {X : Type*} [EMetricSpace X]
    {P : ℝ → X} {a b : ℝ} (hab : a ≤ b) (hP : ContinuousOn P (Icc a b))
    (hL : curveLength P a b ≠ ∞) :
    ∃ Q : unitInterval → X, LipschitzWith (curveLength P a b).toNNReal Q ∧
      Set.range Q = P '' Icc a b := by
  set L : ℝ := (curveLength P a b).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  set R := lengthParam P a b
  have hlip := lipschitzOnWith_lengthParam hab hP hL
  have himg := variationOnFromTo_image_Icc hab hP hL
  have hmaps : ∀ s : I, L * (s : ℝ) ∈ Icc 0 L := fun s =>
    ⟨mul_nonneg hL0 s.2.1, mul_le_of_le_one_right hL0 s.2.2⟩
  have hlipI : LipschitzWith (curveLength P a b).toNNReal (fun s : I => R (L * s)) := by
    intro s t
    have h1 := hlip (hmaps s) (hmaps t)
    refine h1.trans (le_of_eq ?_)
    rw [ENNReal.coe_one, one_mul, ENNReal.coe_toNNReal hL, edist_dist, edist_dist,
      Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hL0, ENNReal.ofReal_mul hL0,
      Subtype.dist_eq, Real.dist_eq, show ENNReal.ofReal L = curveLength P a b from
        ENNReal.ofReal_toReal hL]
  refine ⟨fun s => R (L * s), hlipI, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    have hs := hmaps s
    rw [← himg] at hs
    obtain ⟨t, ht, hts⟩ := hs
    exact ⟨t, ht, by
      change P t = R (L * s)
      rw [← hts]
      exact (lengthParam_variationOnFromTo hL ht).symm⟩
  · rintro _ ⟨t, ht, rfl⟩
    have hσ : variationOnFromTo P (Icc a b) a t ∈ Icc 0 L := by
      rw [← himg]; exact ⟨t, ht, rfl⟩
    by_cases hL0' : L = 0
    · refine ⟨⟨0, unitInterval.zero_mem⟩, ?_⟩
      have h0 : variationOnFromTo P (Icc a b) a t = 0 := by
        have := hσ.2; rw [hL0'] at this; exact le_antisymm this hσ.1
      change R (L * 0) = P t
      rw [mul_zero, ← h0]
      exact lengthParam_variationOnFromTo hL ht
    · have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hL0')
      refine ⟨⟨variationOnFromTo P (Icc a b) a t / L,
        div_nonneg hσ.1 hLpos.le, (div_le_one hLpos).2 hσ.2⟩, ?_⟩
      change R (L * (variationOnFromTo P (Icc a b) a t / L)) = P t
      rw [mul_div_cancel₀ _ hL0']
      exact lengthParam_variationOnFromTo hL ht

 
theorem len_projIcc_le_of_lipschitz (D : LSCMetric) {Q : unitInterval → ℂ} {M : ℝ≥0}
    (h : LipschitzWith M (D.pt ∘ Q)) :
    D.len (fun t => Q (projIcc 0 1 zero_le_one t)) 0 1 ≤ M := by
  change eVariationOn (D.pt ∘ fun t => Q (projIcc 0 1 zero_le_one t)) (Icc 0 1) ≤ M
  have hf : LipschitzWith M ((D.pt ∘ Q) ∘ projIcc (0 : ℝ) 1 zero_le_one) := by
    have := h.comp (LipschitzWith.projIcc zero_le_one)
    simpa only [mul_one] using this
  have h1 := (hf.lipschitzOnWith (s := univ)).comp_eVariationOn_le
    (g := id) (s := Icc (0 : ℝ) 1) (mapsTo_univ _ _)
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc 0 1) ≤ ENNReal.ofReal (1 - 0) := by
    have := (monotoneOn_id (s := Icc (0 : ℝ) 1)).eVariationOn_le
      (⟨le_rfl, zero_le_one⟩ : (0 : ℝ) ∈ Icc 0 1) (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc 0 1)
    simpa only [Set.inter_self, id] using this
  calc eVariationOn (D.pt ∘ fun t => Q (projIcc 0 1 zero_le_one t)) (Icc 0 1)
      = eVariationOn (((D.pt ∘ Q) ∘ projIcc (0 : ℝ) 1 zero_le_one) ∘ id) (Icc 0 1) := rfl
    _ ≤ M * eVariationOn (id : ℝ → ℝ) (Icc 0 1) := h1
    _ ≤ M * ENNReal.ofReal (1 - 0) := by gcongr
    _ = M := by simp

 
theorem disconnects_wider {K : Set ℂ} {c : ℂ} {r₁ r₂ r₁' r₂' : ℝ}
    (h : Disconnects K (Metric.sphere c r₁) (Metric.sphere c r₂))
    (h1 : r₁' ≤ r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ ≤ r₂') :
    Disconnects K (Metric.sphere c r₁') (Metric.sphere c r₂') := by
  rintro ⟨S, hS, hSK, ⟨x, hxS, hx⟩, ⟨y, hyS, hy⟩⟩
  apply h
  have hI := (hS.image (fun z => dist z c) (continuous_id.dist continuous_const).continuousOn)
  have hsub : Icc r₁' r₂' ⊆ (fun z => dist z c) '' S :=
    hI.Icc_subset ⟨x, hxS, hx⟩ ⟨y, hyS, hy⟩
  obtain ⟨u, huS, hu⟩ := hsub ⟨h1, h12.trans h2⟩
  obtain ⟨v, hvS, hv⟩ := hsub ⟨h1.trans h12, h2⟩
  exact ⟨S, hS, hSK, ⟨u, huS, hu⟩, ⟨v, hvS, hv⟩⟩

 
theorem closure_toSet_subset_wider (A A' : EuclideanAnnulus) (hc : A'.center = A.center)
    (hin : A'.innerRadius < A.innerRadius) (hout : A.outerRadius < A'.outerRadius) :
    closure A.toSet ⊆ A'.toSet := by
  have hcl : closure A.toSet ⊆ Metric.closedBall A.center A.outerRadius \
      Metric.ball A.center A.innerRadius := by
    apply closure_minimal
    · intro z hz
      refine ⟨Metric.ball_subset_closedBall hz.1, fun hzb => hz.2 (subset_closure hzb)⟩
    · exact Metric.isClosed_closedBall.sdiff Metric.isOpen_ball
  intro z hz
  obtain ⟨h1, h2⟩ := hcl hz
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, hc]
    exact lt_of_le_of_lt (Metric.mem_closedBall.1 h1) hout
  · intro hz'
    have hz'' := Metric.closure_ball_subset_closedBall hz'
    rw [Metric.mem_closedBall, hc] at hz''
    exact h2 (Metric.mem_ball.2 (lt_of_le_of_lt hz'' hin))

 


theorem aroundDist_le_of_tendsto {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) (A A' : EuclideanAnnulus)
    (hc : A'.center = A.center) (hin : A'.innerRadius < A.innerRadius)
    (hout : A.outerRadius < A'.outerRadius) {δ : ℝ}
    (hfreq : ∃ᶠ n in atTop, aroundDist (G n) A < ENNReal.ofReal δ) :
    aroundDist D A' ≤ ENNReal.ofReal δ := by
  obtain ⟨φ, hφ, hlt⟩ := extraction_of_frequently_atTop hfreq
  have hG' : Tendsto (fun n => G (φ n)) atTop (𝓝 D) := hG.comp hφ.tendsto_atTop
  choose π s t hcurve htr hsep hlen using fun n =>
    PfeWeyl.aroundDist_exists_curve_lt (G (φ n)) A (hlt n)
  have hfin : ∀ n, curveLength ((G (φ n)).pt ∘ π n) (s n) (t n) ≠ ∞ := fun n =>
    (lt_of_lt_of_le (hlen n) le_top).ne
  choose Q hQlip hQrange using fun n =>
    exists_lipschitz_reparam_range_eq (hcurve n).1 (hcurve n).2 (hfin n)
  set M : ℝ≥0 := (ENNReal.ofReal δ).toNNReal
  let toC : ∀ n, (G (φ n)).Space → ℂ := fun _ x => x
  let P : ℕ → unitInterval → ℂ := fun n u => toC n (Q n u)
  have hLip : ∀ n, LipschitzWith M ((G (φ n)).pt ∘ P n) := by
    intro n
    have h := (hQlip n).weaken (ENNReal.toNNReal_mono ENNReal.ofReal_ne_top (hlen n).le)
    exact h
  have hrangeP : ∀ n, Set.range (P n) = π n '' Icc (s n) (t n) := fun n => hQrange n
  set K : Set ℂ := closure A.toSet
  have hK : IsCompact K := by
    apply Bornology.IsBounded.isCompact_closure
    exact (Metric.isBounded_ball (x := A.center) (r := A.outerRadius)).subset
      (fun z hz => hz.1)
  have htrace : ∀ n (u : unitInterval), P n u ∈ K := by
    intro n u
    have hmem : P n u ∈ Set.range (P n) := ⟨u, rfl⟩
    rw [hrangeP n] at hmem
    obtain ⟨v, hv, hveq⟩ := hmem
    rw [← hveq]
    exact subset_closure (htr n v hv)
  obtain ⟨ψ, P₀, hψ, hlim, htrace₀⟩ :=
    Uniqueness.Toolkit.CompactPathInfimum.compact_trace_path_subseq hG' hK htrace hLip
  have hGψ : Tendsto (fun n => G (φ (ψ n))) atTop (𝓝 D) := hG'.comp hψ.tendsto_atTop
  have hDlip : LipschitzWith M (D.pt ∘ P₀) :=
    Uniqueness.Toolkit.PathInfimum.lipschitz_limit_of_epi hGψ hlim (fun n => hLip (ψ n))
  
  have hcont : ∀ n, Continuous (P (ψ n)) := fun n =>
    Uniqueness.Toolkit.CompactPathInfimum.continuous_euclidean_of_metric_on_compact
      (G (φ (ψ n))) hK (htrace (ψ n)) (hLip (ψ n)).continuous
  let Pc : ℕ → C(unitInterval, ℂ) := fun n => ⟨P (ψ n), hcont n⟩
  have hsepn : ∀ n, Disconnects (Set.range (Pc n)) A.innerBoundary A.outerBoundary := by
    intro n
    have heq : Set.range (Pc n) = π (ψ n) '' Icc (s (ψ n)) (t (ψ n)) := hrangeP (ψ n)
    rw [heq]
    exact hsep (ψ n)
  have hsep₀ := Uniqueness.Toolkit.PathInfimum.separator_stable_of_uniform_limit
    A.innerBoundary A.outerBoundary (P := Pc) (P₀ := P₀) hlim hsepn
  have hsep' : Disconnects (Set.range P₀) A'.innerBoundary A'.outerBoundary := by
    have h := disconnects_wider (K := Set.range P₀) (c := A.center) hsep₀ hin.le
      A.2.2.le hout.le
    simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.outerBoundary, hc] using h
  let P' : ℝ → ℂ := fun u => P₀ (projIcc 0 1 zero_le_one u)
  have hP'curve : D.IsCurve P' 0 1 :=
    ⟨zero_le_one, (hDlip.continuous.comp continuous_projIcc).continuousOn⟩
  have himage : P' '' Icc 0 1 = Set.range P₀ := by
    ext z
    constructor
    · rintro ⟨u, -, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨u, u.2, ?_⟩
      change P₀ (projIcc 0 1 zero_le_one u) = P₀ u
      rw [projIcc_val]
  have hP'tr : ∀ u ∈ Icc (0 : ℝ) 1, P' u ∈ A'.toSet := fun u _ =>
    closure_toSet_subset_wider A A' hc hin hout (htrace₀ _)
  calc aroundDist D A' ≤ D.len P' 0 1 := by
        unfold aroundDist
        exact iInf_le_of_le P' <| iInf_le_of_le 0 <| iInf_le_of_le 1 <|
          iInf_le_of_le hP'curve <| iInf_le_of_le hP'tr <|
            iInf_le_of_le (by rw [himage]; exact hsep') le_rfl
    _ ≤ M := len_projIcc_le_of_lipschitz D hDlip
    _ ≤ ENNReal.ofReal δ := ENNReal.coe_toNNReal_le_self

 

def SelfSmallAnnuli (D : LSCMetric) (K : Set ℂ) : Prop :=
  ∀ z ∈ K, PfeWeyl.IsNonsingular D z → ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ →
    ∃ A : EuclideanAnnulus, dist z A.center < A.innerRadius ∧ A.outerRadius < ρ ∧
      aroundDist D A < ENNReal.ofReal δ

 
theorem selfSmallAnnuli_of_smallAnnulusCosts {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D)) {K' K'' : Set ℂ}
    (hsmall : PfeWeyl.SmallAnnulusCosts G D K' K'') : SelfSmallAnnuli D K' := by
  intro z hz hns δ hδ ρ hρ
  obtain ⟨A, -, hzA, hAρ, -, hev⟩ := hsmall z hz hns (δ / 2) (half_pos hδ) (ρ / 2)
    (half_pos hρ)
  have hr0 : 0 < (dist z A.center + A.innerRadius) / 2 := by
    have := A.innerRadius_pos; positivity
  have hr1 : (dist z A.center + A.innerRadius) / 2 < A.innerRadius := by linarith
  have hr2 : A.outerRadius < (A.outerRadius + ρ) / 2 := by linarith
  let A' : EuclideanAnnulus :=
    ⟨(A.center, (dist z A.center + A.innerRadius) / 2, (A.outerRadius + ρ) / 2),
      hr0, by linarith [A.innerRadius_lt_outerRadius]⟩
  refine ⟨A', ?_, ?_, ?_⟩
  · change dist z A.center < (dist z A.center + A.innerRadius) / 2
    linarith
  · change (A.outerRadius + ρ) / 2 < ρ
    linarith
  · have h := aroundDist_le_of_tendsto hG A A' rfl hr1 hr2 hev.frequently
    exact lt_of_le_of_lt h (ENNReal.ofReal_lt_ofReal_iff hδ |>.2 (half_lt_self hδ))

end SupercriticalLQGUniqueness.B2.PfeAxioms

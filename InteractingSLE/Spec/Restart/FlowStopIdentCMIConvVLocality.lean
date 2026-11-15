/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvVReduce

/-! # Stopped-path agreement from the measurable-exit identification -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open LawUnique StoppedExtend StoppedExtendWF FlowStopIdentG FlowStopIdentCM Exist.Staged ConverseBefore

/-- A stopped flow line at a measurable exit version gives the same a.s. stopped match. -/
theorem ae_stopMatch_of_LV (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ)
    (h12p : Theorem12ParamStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ} {V : Set ℂ} (hV : IsOpen V) {y θ : ℝ} {S : Type u} [MeasurableSpace S]
    {Q₀ Q : Measure S} [IsProbabilityMeasure Q₀] [IsProbabilityMeasure Q] (hQQ₀ : Q ≪ Q₀)
    {H₀ Ĥ : S → DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U e : S → ℝ≥0∞}
    (hΓ : IsFlowLine κ b J y θ Q₀ H₀ Γ U) {ν : Measure (ℕ → ℝ)} [IsProbabilityMeasure ν]
    (he : e =ᵐ[Q₀] fun x => RLC.exitTime V (Γ x) (U x))
    (hL : IsStoppedFlowLineL κ bR Ĵ y θ V (Q.prod ν) (fun p => Ĥ p.1) (fun p => Γ p.1)
      fun p => e p.1) :
    ∀ᵐ x ∂Q, IsStopMatch (flowDetCode h12p hκ bR Ĵ y θ (Ĥ x)) (Γ x) (RLC.exitTime V (Γ x) (U x)) := by
  have hfacts : ∀ᵐ p ∂(Q.prod ν), FlowPathFacts κ b J y θ (Γ p.1) (U p.1) :=
    ae_fst_of_ae (P₀ := ν) (q := fun x => FlowPathFacts κ b J y θ (Γ x) (U x)) (hQQ₀.ae_le (ae_flowPathFacts hΓ))
  have he' := ae_fst_of_ae (P₀ := ν) (hQQ₀.ae_le he)
  have hG := isStoppedFlowLineG_of_L_ae_exit hV hfacts he' hL
  have m := hG.ae_stopMatch_of_extendGK (hext κ hκ hκ4) h13 hκ (isFlowDet_flowDetCode h12p hκ bR Ĵ y θ)
  have m' := ae_of_ae_fst (P₀ := ν)
    (q := fun x => IsStopMatch (flowDetCode h12p hκ bR Ĵ y θ (Ĥ x)) (Γ x) (e x)) m
  filter_upwards [m', hQQ₀.ae_le he] with x hx hex
  rwa [hex] at hx

section Locality
variable {S : Type u} [MeasurableSpace S] {Q₀ : Measure S} [IsProbabilityMeasure Q₀]

/-- The two explicit tilts give agreement through the raw exits almost surely. -/
theorem ae_stoppedAgree_of_CMIV (hCM : FlowLineStopIdentCMIVStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → StoppedHullExtendGKStatement.{u} κ) (h12p : Theorem12ParamStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b bR : ℝ → ℝ} {J Ĵ : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR Ĵ) {O : Set ℝ}
    (hO : IsOpen O) (hbO : ∀ x ∈ O, b x = bR x) {N : Set ℂ} (hN : IsOpen N) (hNO : ∀ z ∈ N, z.im = 0 → z.re ∈ O)
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVN : closure V ⊆ N) {a c : ℝ} (haO : Icc a c ⊆ O)
    (hVa : ∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) (hsN : shiftHullSet V a c ⊆ N) {F : CMCut} {q : ℂ → ℝ}
    (hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ) q)
    (hFq : ∀ z ∈ N, z ∈ H → F.f z = q z) (hFΔ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.f z = 0) (y θ : ℝ)
    {H₀ : S → DistOn upperHalfPlaneOpens} (hH : IsGFFWithBoundaryData Q₀ H₀ b J)
    {s : ℕ → TestOn upperHalfPlaneOpens} (hsle : ∀ n z, |s n z| ≤ |F.src z|)
    (hslim : ∀ z, Tendsto (fun n => s n z) atTop (𝓝 (F.src z))) {Λ : S → ℝ} (hΛm : Measurable Λ)
    (hΛ : ∀ᵐ x ∂Q₀, Tendsto (fun n => H₀ x (s n)) atTop (𝓝 (Λ x))) {k : ℝ} (hk : 0 < k)
    (hprob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x))))
    {Γ α : S → ℝ≥0 → ℂ} {U ζ : S → ℝ≥0∞} (hΓ : IsFlowLine κ b J y θ Q₀ H₀ Γ U)
    (hα : IsFlowLine κ bR Ĵ y θ (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)))
      (fun x => H₀ x + smoothDist upperHalfPlaneOpens fun z => q z - F.f z) α ζ) :
    ∀ᵐ x ∂Q₀, RLC.StoppedAgree V (Γ x) (U x) (α x) (ζ x) := by
  classical
  set Q := Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-Λ x)) with hQ
  set T : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens fun z => q z - F.f z with hT
  set Ĥ : S → DistOn upperHalfPlaneOpens := fun x => H₀ x + T with hĤdef
  have hQQ₀ : Q ≪ Q₀ := withDensity_absolutelyContinuous _ _
  have hQ₀Q : Q₀ ≪ Q := absolutelyContinuous_withDensity_exp hΛm hk
  have hint := integrable_exp_neg_of_prob hΛm hk hprob
  have hĤ : IsGFFWithBoundaryData Q Ĥ bR Ĵ := isGFFWithBoundaryData_shift hb F hq hH hsle hslim hΛm hΛ hint hk hprob
  -- the pair
  obtain ⟨e, hem, he, ν, hν, hL⟩ := hCM κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO N hN hNO V hV hVb hVN
    a c haO hVa hsN F q hq hFq hFΔ y θ Q₀ H₀ hH s hsle hslim Λ hΛm hΛ k hk hprob Γ U hΓ
  have m1 := ae_stopMatch_of_LV (Ĥ := Ĥ) (bR := bR) (Ĵ := Ĵ) hext h12p h13 hκ hκ4 hV hQQ₀ hΓ he hL
  -- the reversed pair
  have hqc : ContinuousOn q H := fun z hz => ((hq.1 z hz).1.continuousAt).continuousWithinAt
  have hTc : ContinuousOn (fun z => q z - F.f z) H := hqc.sub F.smooth.continuous.continuousOn
  have hTφ : ∀ φ : TestOn upperHalfPlaneOpens, T φ = ∫ z, φ z * (q z - F.f z) := fun φ => by
    rw [hT, SupercriticalConformalCovariance.GM24.smoothDist_apply hTc]
  obtain ⟨Cq, hCq⟩ := hq.2.1
  obtain ⟨Cf, hCf⟩ := F.smooth.continuous.bounded_above_of_compact_support F.compact
  set c₁ : ℝ := ∫ z, F.src z * (q z - F.f z) with hc₁
  have hTs : Tendsto (fun n => T (s n)) atTop (𝓝 c₁) := by
    simp only [hTφ]
    refine tendsto_integral_of_dominated_convergence (fun z => |F.src z| * (Cq + Cf))
      (fun n => ((LocalExt.integrable_mul_testOn hTc (s n)).congr
        (ae_of_all _ fun z => mul_comm _ _)).aestronglyMeasurable)
      (F.integrable_src.abs.mul_const _) (fun n => ae_of_all _ fun z => ?_) (ae_of_all _ fun z => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      by_cases hz : z ∈ H
      · refine mul_le_mul (hsle n z) ((abs_sub _ _).trans (add_le_add (hCq z hz) ?_)) (abs_nonneg _)
          (abs_nonneg _)
        rw [← Real.norm_eq_abs]; exact hCf z
      · have h0 := hsle n z
        rw [F.src_of_notMem hz, abs_zero] at h0
        rw [abs_nonpos_iff.1 h0, abs_zero, zero_mul, F.src_of_notMem hz, abs_zero, zero_mul]
    · exact (hslim z).mul_const _
  set Λ' : S → ℝ := fun x => -Λ x - c₁ with hΛ'def
  set k' : ℝ := Real.exp (-c₁) / k with hk'def
  have hk' : 0 < k' := div_pos (Real.exp_pos _) hk
  have hΛ'm : Measurable Λ' := hΛm.neg.sub_const _
  have hΛ' : ∀ᵐ x ∂Q, Tendsto (fun n => Ĥ x (-s n)) atTop (𝓝 (Λ' x)) := by
    filter_upwards [hQQ₀.ae_le hΛ] with x hx
    have e : ∀ n, Ĥ x (-s n) = -(H₀ x (s n) + T (s n)) := fun n => by
      rw [map_neg]; rfl
    simp only [e, hΛ'def]
    have := (hx.add hTs).neg
    convert this using 2
    ring
  -- the density of `Q₀` with respect to `Q`
  have hmg : Measurable fun x => ENNReal.ofReal (k * Real.exp (-Λ x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp hΛm.neg))
  have hmg' : Measurable fun x => ENNReal.ofReal (k' * Real.exp (-Λ' x)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp hΛ'm.neg))
  have hback : Q.withDensity (fun x => ENNReal.ofReal (k' * Real.exp (-Λ' x))) = Q₀ := by
    rw [hQ, ← withDensity_mul _ hmg hmg']
    have e : ((fun x => ENNReal.ofReal (k * Real.exp (-Λ x))) * fun x => ENNReal.ofReal (k' * Real.exp (-Λ' x))) =
        fun _ => 1 := by
      funext x
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (mul_nonneg hk.le (Real.exp_pos _).le)]
      have : k * Real.exp (-Λ x) * (k' * Real.exp (-Λ' x)) = 1 := by
        rw [hk'def, hΛ'def]
        simp only [neg_sub, sub_neg_eq_add]
        rw [show k * Real.exp (-Λ x) * (Real.exp (-c₁) / k * Real.exp (c₁ + Λ x)) =
          Real.exp (-Λ x) * Real.exp (-c₁) * Real.exp (c₁ + Λ x) * (k / k) by ring, div_self hk.ne', mul_one,
          ← Real.exp_add, ← Real.exp_add]
        rw [show -Λ x + -c₁ + (c₁ + Λ x) = 0 by ring, Real.exp_zero]
      rw [this, ENNReal.ofReal_one]
    rw [e]
    exact withDensity_one
  have hprob' : IsProbabilityMeasure (Q.withDensity fun x => ENNReal.ofReal (k' * Real.exp (-Λ' x))) := by
    rw [hback]; infer_instance
  -- the reversed data
  have hq' : IsBoundedHarmonicExtension (fun x => b x - bR x) ((Ĵ ∪ J : Finset ℝ) : Set ℝ) fun z => -q z := by
    refine ⟨hq.1.neg, ⟨Cq, fun z hz => by rw [abs_neg]; exact hCq z hz⟩, fun x hx => ?_⟩
    have h := (hq.2.2 x (by rwa [Finset.union_comm])).neg
    simpa only [neg_sub] using h
  have hF'q : ∀ z ∈ N, z ∈ H → F.neg.f z = -q z := fun z hz hzH => by rw [F.neg_f, hFq z hz hzH]
  have hF'Δ : ∀ z ∈ N, QuantumZipper.K3.greenDensity F.neg.f z = 0 := fun z hz => by
    rw [F.greenDensity_neg, hFΔ z hz, neg_zero]
  have hs'le : ∀ n z, |(-s n) z| ≤ |F.neg.src z| := fun n z => by
    rw [F.src_neg, abs_neg]
    show |-(s n z)| ≤ _
    rw [abs_neg]; exact hsle n z
  have hs'lim : ∀ z, Tendsto (fun n => (-s n) z) atTop (𝓝 (F.neg.src z)) := fun z => by
    rw [F.src_neg]
    exact (hslim z).neg
  obtain ⟨e', he'm, he', ν', hν', hL'⟩ := hCM κ hκ hκ4 bR b Ĵ J hbR hb O hO (fun x hx => (hbO x hx).symm)
    N hN hNO V hV hVb hVN a c haO hVa hsN F.neg (fun z => -q z) hq' hF'q hF'Δ y θ Q Ĥ hĤ
    (fun n => -s n) hs'le hs'lim Λ' hΛ'm hΛ' k' hk'
    hprob' α ζ hα
  have hfield : ∀ x, Ĥ x + smoothDist upperHalfPlaneOpens (fun z => -q z - F.neg.f z) = H₀ x := fun x => by
    ext φ
    have hc' : ContinuousOn (fun z => -q z - F.neg.f z) H := hqc.neg.sub F.neg.smooth.continuous.continuousOn
    show H₀ x φ + T φ + smoothDist upperHalfPlaneOpens (fun z => -q z - F.neg.f z) φ = H₀ x φ
    rw [SupercriticalConformalCovariance.GM24.smoothDist_apply (Y := fun z => -q z - F.neg.f z) hc', hTφ,
      add_assoc, ← integral_add]
    · convert add_zero (H₀ x φ) using 2
      rw [← integral_zero ℂ ℝ]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only [F.neg_f]
      ring
    · exact (LocalExt.integrable_mul_testOn hTc φ).congr (ae_of_all _ fun z => mul_comm _ _)
    · exact (LocalExt.integrable_mul_testOn hc' φ).congr (ae_of_all _ fun z => mul_comm _ _)
  rw [hback] at hL'
  simp only [hfield] at hL'
  have m2 := ae_stopMatch_of_LV (Ĥ := H₀) (bR := b) (Ĵ := J) hext h12p h13 hκ hκ4 hV hQ₀Q hα he' hL'
  have c1 := isFlowDet_flowDetCode h12p hκ bR Ĵ y θ Q Ĥ α ζ hα
  have c2 := isFlowDet_flowDetCode h12p hκ b J y θ Q₀ H₀ Γ U hΓ
  filter_upwards [hQ₀Q.ae_le m1, hQ₀Q.ae_le c1, m2, c2] with z e1 e2 e3 e4
  exact stoppedAgree_of_matches e1 e2 e3 e4

end Locality
end InteractingSLE.Restart.FlowStopIdentCMI

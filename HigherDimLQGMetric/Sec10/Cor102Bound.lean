import HigherDimLQGMetric.Sec10.Cor102Group

/-!
# Uniform bounds on the dilation factors

Tightness of the sharp normalized metrics and the positive unit point distance
force every deterministic dilation factor into one compact subinterval of `(0,∞)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology
open HigherDimLFPP (Rd e₁)
open scoped ENNReal

variable {d : ℕ}

/-- A fixed positive point distance has a positive-probability compact interval of values. -/
theorem s8c_point_quantile (hd : 3 ≤ d)
    {D : DistRd d → ContMetric d} (hDm : Measurable D) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (4⁻¹ : ℝ≥0∞) < (normLGFLaw d)
        {g | m ≤ (D g).1 (0, e₁ d) ∧ (D g).1 (0, e₁ d) ≤ M} := by
  have hd2 : 2 ≤ d := by omega
  let _ : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd2).1
  let Z : DistRd d → ℝ := fun g => (D g).1 (0, e₁ d)
  have hZm : Measurable Z :=
    (continuous_eval_const _).measurable.comp (measurable_subtype_coe.comp hDm)
  obtain ⟨m, M, hm, hmass⟩ :=
    l9c_uniform_bounds_of_ae_continuousOn (normLGFLaw d)
      (fun g (_ : ℝ) => Z g) (fun _ => hZm) (a := 1) (b := 1) le_rfl
      (ae_of_all _ fun g => ⟨continuousOn_const,
        fun _ _ => (D g).apply_pos
          (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm⟩)
  refine ⟨m, max 1 M, hm, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  have hp := hmass 1 (by simp)
  exact hp.trans_le (measure_mono fun g hg =>
    ⟨hg.1, hg.2.trans (le_max_right _ _)⟩)

/-- Equality of metric laws transports the probability of a scaled point interval. -/
theorem s8c_law_point_Icc
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    {X : Ω → C(Rd d × Rd d, ℝ)} (hXm : AEMeasurable X P)
    {D : Ω → ContMetric d} (hDm : Measurable D)
    {a m M : ℝ} (ha : 0 < a)
    (hlaw : P.map X = P.map (fun ω => a • (D ω).1)) :
    P {ω | a * m ≤ X ω (0, e₁ d) ∧ X ω (0, e₁ d) ≤ a * M} =
      P {ω | m ≤ (D ω).1 (0, e₁ d) ∧ (D ω).1 (0, e₁ d) ≤ M} := by
  let E : Set C(Rd d × Rd d, ℝ) :=
    {F | a * m ≤ F (0, e₁ d) ∧ F (0, e₁ d) ≤ a * M}
  have hEm : MeasurableSet E := by
    have he : Measurable fun F : C(Rd d × Rd d, ℝ) => F (0, e₁ d) :=
      (continuous_eval_const _).measurable
    simpa only [E, Set.ofPred_and] using
      (measurableSet_le measurable_const he).inter
        (measurableSet_le he measurable_const)
  have hYm : Measurable (fun ω => a • (D ω).1) :=
    (continuous_const_smul a).measurable.comp (measurable_subtype_coe.comp hDm)
  have h := congrArg (fun μ : Measure C(Rd d × Rd d, ℝ) => μ E) hlaw
  rw [Measure.map_apply_of_aemeasurable hXm hEm,
    Measure.map_apply hYm hEm] at h
  have hpre : (fun ω => a • (D ω).1) ⁻¹' E =
      {ω | m ≤ (D ω).1 (0, e₁ d) ∧ (D ω).1 (0, e₁ d) ≤ M} := by
    ext ω
    simp only [E, mem_preimage, mem_ofPred_eq, ContinuousMap.smul_apply, smul_eq_mul]
    exact ⟨fun ⟨h1,h2⟩ => ⟨(mul_le_mul_iff_of_pos_left ha).mp h1,
        (mul_le_mul_iff_of_pos_left ha).mp h2⟩,
      fun ⟨h1,h2⟩ => ⟨(mul_le_mul_iff_of_pos_left ha).mpr h1,
        (mul_le_mul_iff_of_pos_left ha).mpr h2⟩⟩
  rw [hpre] at h
  exact h

/-- The deterministic factors in the normalized metric laws are uniformly bounded above and
away from zero across all positive scales. -/
theorem s8c_factor_bounds (hd : 3 ≤ d) {ξ Q : ℝ}
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    (a : ℝ → ℝ) (ha : ∀ r : ℝ, 0 < r → 0 < a r)
    (hlaw : ∀ r : ℝ, 0 < r →
      (normLGFLaw d).map
        (fun g => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) g r) =
      (normLGFLaw d).map (fun g => a r • (D g).1)) :
    ∃ lo hi : ℝ, 0 < lo ∧ 0 < hi ∧
      ∀ r : ℝ, 0 < r → lo < a r ∧ a r < hi := by
  have hd2 : 2 ≤ d := by omega
  let P : Measure (DistRd d) := normLGFLaw d
  let _ : IsProbabilityMeasure P := (normLGFLaw_spec_holds d hd2).1
  have hn : IsNormalizedLGF id P := (normLGFLaw_spec_holds d hd2).2.1
  let X : ℝ → DistRd d → C(Rd d × Rd d, ℝ) :=
    fun r g => normalizedAtScale ξ D (fun s => s ^ (ξ * Q)) g r
  have hT : TightOver P X (Ioi 0) :=
    hD.tight_bdd P id hn.1.isLGFPlusBddCont
  obtain ⟨m,M,hm,hM,hquant⟩ := s8c_point_quantile hd hD.measurable
  let p : Rd d × Rd d := (0,e₁ d)
  have hp : p.1 ≠ p.2 :=
    (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
  obtain ⟨η,hη,hlo⟩ := hT.lower_offDiag (A := {p}) isCompact_singleton
    (by intro q hq; simpa only [mem_singleton_iff] using hq ▸ hp)
    (by norm_num : (0 : ℝ≥0∞) < 4⁻¹)
  let K : Set (Rd d) := {0,e₁ d}
  have hK : IsCompact K := isCompact_singleton.insert _
  obtain ⟨T,hTpos,hup⟩ := hT.upper_compact hK
    (by norm_num : (0 : ℝ≥0∞) < 4⁻¹)
  refine ⟨η / M, T / m, div_pos hη hM, div_pos hTpos hm, ?_⟩
  intro r hr
  have hprob : (4⁻¹ : ℝ≥0∞) <
      P {g | a r * m ≤ X r g p ∧ X r g p ≤ a r * M} := by
    rw [s8c_law_point_Icc P (hT.1 r hr) hD.measurable (ha r hr) (hlaw r hr)]
    exact hquant
  have hupper : a r * m < T := by
    by_contra hnot
    have hge : T ≤ a r * m := le_of_not_gt hnot
    have hsub : {g | a r * m ≤ X r g p ∧ X r g p ≤ a r * M} ⊆
        {g | ¬ ∀ u ∈ K, ∀ v ∈ K, X r g (u,v) < T} := by
      intro g hg hgood
      have hval := hgood 0 (by simp [K]) (e₁ d) (by simp [K])
      exact (not_lt_of_ge (hge.trans hg.1)) hval
    exact (lt_irrefl (4⁻¹ : ℝ≥0∞))
      ((hprob.trans_le (measure_mono hsub)).trans (hup r hr))
  have hlower : η < a r * M := by
    by_contra hnot
    have hle : a r * M ≤ η := le_of_not_gt hnot
    have hsub : {g | a r * m ≤ X r g p ∧ X r g p ≤ a r * M} ⊆
        {g | ¬ ∀ q ∈ ({p} : Set (Rd d × Rd d)), η < X r g q} := by
      intro g hg hgood
      have hval := hgood p (mem_singleton p)
      exact (not_lt_of_ge (hg.2.trans hle)) hval
    exact (lt_irrefl (4⁻¹ : ℝ≥0∞))
      ((hprob.trans_le (measure_mono hsub)).trans (hlo r hr))
  exact ⟨(div_lt_iff₀ hM).2 hlower, (lt_div_iff₀ hm).2 hupper⟩

end HigherDimLQGMetric

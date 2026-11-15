/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIStmt
import InteractingSLE.Spec.Supplement.RLCG3Source

/-!
# Lemma G3 in the source's form from (L1) for the explicit Cameron–Martin shift

Packet PROVE-L1-CMI. `RLC.G3SourceStatement` (PROVE-G3SRC, ruling R60) from the explicit-shift input
`FlowStopIdentCMI.FlowLineStopIdentCMIStatement`, the WFS kernel target for `0 < κ < 4` and Theorems 1.2 (param) /
1.3. The shift is constructed explicitly (in place of `RLC.exists_shift_isGFFWithBoundaryData`'s Radon–Nikodym
density): the cutoff field `F` of `FlowStopIdentCMI.exists_cmCut` around the compact set of both per-seed buffers,
the test functions `F.testSeq`, the Borel pairing `Λ = F.pair ∘ H₀`, the density `Z = e^{−Λ} / E[e^{−Λ}]`
(`FlowStopIdentCMI.integrable_exp_neg_of_isGFF`), and the field `H₀ + (q − F.f)`
(`FlowStopIdentCMI.isGFFWithBoundaryData_shift`); the per-seed agreement is `FlowStopIdentCMI.ae_stoppedAgree_of_CMI`.
When `O` is empty both buffers miss `ℝ`, so both curves exit at time `0` and agree there.

* `exitTime_eq_zero`, `stoppedAgree_zero`: the degenerate case;
* **`g3SourceStatement_of_CMI`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace RLC

open Restart.FlowStopIdentCM Restart.FlowStopIdentCMI
open QuantumZipper (H)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- A path that starts outside `V` exits at time `0`. -/
theorem exitTime_eq_zero {V : Set ℂ} {γ : ℝ≥0 → ℂ} (U : ℝ≥0∞) (h : γ 0 ∉ V) : exitTime V γ U = 0 := by
  refine le_antisymm ((min_le_right _ _).trans ?_) bot_le
  exact (iInf₂_le (0 : ℝ≥0) h).trans (by simp)

/-- Two paths starting at the same point outside `V` agree up to their common exit time `0`. -/
theorem stoppedAgree_zero {V : Set ℂ} {γ γ' : ℝ≥0 → ℂ} (U U' : ℝ≥0∞) (h0 : γ 0 = γ' 0) (h : γ 0 ∉ V) :
    StoppedAgree V γ U γ' U' := by
  refine ⟨by rw [exitTime_eq_zero U h, exitTime_eq_zero U' (h0 ▸ h)], fun s hs => ?_⟩
  rw [exitTime_eq_zero U h, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at hs
  rw [hs, h0]

/-- A flow line starts at its seed, almost surely. -/
theorem ae_start_of_isFlowLine {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {y θ : ℝ} {S : Type*} [MeasurableSpace S]
    {P : Measure S} {h : S → LQGMetric.DistOn upperHalfPlaneOpens} {Γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hΓ : IsFlowLine κ b J y θ P h Γ U) : ∀ᵐ x ∂P, Γ x 0 = y := by
  obtain ⟨h', 𝓕, W, VL, VR, B, -, -, htr⟩ := hΓ
  filter_upwards [htr] with x hx
  exact sub_eq_zero.1 hx.1

/-- **Lemma G3 in the source's form from (L1) for the explicit Cameron–Martin shift**, the WFS kernel target for
`0 < κ < 4` and Theorems 1.2 (param) / 1.3. -/
theorem g3SourceStatement_of_CMI (hCM : FlowLineStopIdentCMIStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} := by
  classical
  intro κ hκ hκ4 b bR J Ĵ hb hbR O hO hbO _hJO V₁ V₂ hV₁ hV₂ hV₁b hV₂b a₁ c₁ a₂ c₂ hI₁ hI₂ hV₁I hV₂I y₁ y₂ θ₁ θ₂
    S _ Q₀ _ H₀ hH Γ₁ Γ₂ U₁ U₂ h₁ h₂
  have hext : ∀ κ : ℝ, 0 < κ → κ < 4 → Restart.StoppedExtendWF.StoppedHullExtendGKStatement.{0} κ :=
    fun κ hκ hκ4 => WFS.stoppedHullExtendGKStatement_of_through hκ (hT κ hκ hκ4)
  have hKc := isCompact_g3SourceSet hV₁b hV₂b a₁ c₁ a₂ c₂
  have hKO : ∀ z ∈ shiftHullSet V₁ a₁ c₁ ∪ shiftHullSet V₂ a₂ c₂ ∪ (closure V₁ ∪ closure V₂), z.im = 0 →
      z.re ∈ O := fun z hz h0 => re_mem_of_mem_g3SourceSet hV₁b hV₂b hI₁ hI₂ hV₁I hV₂I hz h0
  by_cases hOn : O.Nonempty
  · obtain ⟨y₀, hy₀⟩ := hOn
    -- the harmonic extension of `bR − b`
    obtain ⟨u, hu, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hb
    obtain ⟨uR, huR, -⟩ := PiecewiseConstant.existsUnique_isBoundedHarmonicExtension hbR
    have hq : IsBoundedHarmonicExtension (fun x => bR x - b x) ((J ∪ Ĵ : Finset ℝ) : Set ℝ)
        fun z => uR z - u z :=
      isBoundedHarmonicExtension_mono' (isBoundedHarmonicExtension_sub huR hu)
        (by simp only [Finset.coe_union]; exact (union_comm _ _).subset)
    -- the cutoff
    obtain ⟨N, F, hNo, hKN, hNO, hFq, hFΔ⟩ := exists_cmCut hb hbR hO hbO hq hy₀ hKc hKO
    have hs₁ : shiftHullSet V₁ a₁ c₁ ⊆ N := fun z hz => hKN (Or.inl (Or.inl hz))
    have hs₂ : shiftHullSet V₂ a₂ c₂ ⊆ N := fun z hz => hKN (Or.inl (Or.inr hz))
    have hc₁ : closure V₁ ⊆ N := fun z hz => hKN (Or.inr (Or.inl hz))
    have hc₂ : closure V₂ ⊆ N := fun z hz => hKN (Or.inr (Or.inr hz))
    -- the pairing and the density
    have huc : ContinuousOn u H := fun z hz => ((hu.1 z hz).1.continuousAt).continuousWithinAt
    obtain ⟨C, hC⟩ := hu.2.1
    have hΛ := F.ae_tendsto_pair huc hC (hH.2 u hu)
    have hΛm : Measurable fun x => F.pair (H₀ x) := F.measurable_pair.comp hH.1
    have hint := integrable_exp_neg_of_isGFF hb hH F F.abs_testSeq_le hΛm hΛ
    set E : ℝ := ∫ x, Real.exp (-F.pair (H₀ x)) ∂Q₀ with hE
    have hE0 : 0 < E := integral_exp_pos hint
    set k : ℝ := E⁻¹ with hk
    have hk0 : 0 < k := inv_pos.2 hE0
    set Z : S → ℝ := fun x => k * Real.exp (-F.pair (H₀ x)) with hZ
    have hZint : Integrable Z Q₀ := hint.const_mul k
    have hZ1 : ∫ x, Z x ∂Q₀ = 1 := by
      rw [hZ, integral_const_mul, ← hE, hk, inv_mul_cancel₀ hE0.ne']
    have hprob : IsProbabilityMeasure (Q₀.withDensity fun x => ENNReal.ofReal (k * Real.exp (-F.pair (H₀ x)))) := by
      constructor
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hZint (ae_of_all _ fun x => (mul_pos hk0 (Real.exp_pos _)).le)]
      show ENNReal.ofReal (∫ x, Z x ∂Q₀) = 1
      rw [hZ1, ENNReal.ofReal_one]
    have hĤ := isGFFWithBoundaryData_shift hb F hq hH F.abs_testSeq_le F.tendsto_testSeq hΛm hΛ hint hk0 hprob
    obtain ⟨α₁, ζ₁, hα₁⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₁ θ₁ hĤ
    obtain ⟨α₂, ζ₂, hα₂⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₂ θ₂ hĤ
    refine ⟨Z, _, α₁, α₂, ζ₁, ζ₂, hZint.aemeasurable, ae_of_all _ fun x => mul_pos hk0 (Real.exp_pos _), hZ1,
      hĤ, hα₁, hα₂, ?_⟩
    filter_upwards [ae_stoppedAgree_of_CMI hCM hext h12p h13 hκ hκ4 hb hbR hO hbO hNo hNO hV₁ hV₁b hc₁ hI₁ hV₁I hs₁
        hq hFq hFΔ y₁ θ₁ hH F.abs_testSeq_le F.tendsto_testSeq hΛm hΛ hk0 hprob h₁ hα₁,
      ae_stoppedAgree_of_CMI hCM hext h12p h13 hκ hκ4 hb hbR hO hbO hNo hNO hV₂ hV₂b hc₂ hI₂ hV₂I hs₂
        hq hFq hFΔ y₂ θ₂ hH F.abs_testSeq_le F.tendsto_testSeq hΛm hΛ hk0 hprob h₂ hα₂] with x hx₁ hx₂
    exact ⟨hx₁, hx₂⟩
  · -- `O = ∅`: both buffers miss `ℝ`, both curves exit at time `0`
    rw [not_nonempty_iff_eq_empty] at hOn
    obtain ⟨Z, T, N, -, -, -, hZm, hZpos, hZ1, hĤ, -⟩ :=
      exists_shift_isGFFWithBoundaryData hb hbR hO hbO hKc hKO Q₀ hH
    set Q := Q₀.withDensity fun x => ENNReal.ofReal (Z x) with hQ
    have hint : Integrable Z Q₀ := Integrable.of_integral_ne_zero (by rw [hZ1]; exact one_ne_zero)
    have hQprob : IsProbabilityMeasure Q := by
      constructor
      rw [hQ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
        ← ofReal_integral_eq_lintegral_ofReal hint (hZpos.mono fun x hx => hx.le), hZ1, ENNReal.ofReal_one]
    have hPQ : Q₀ ≪ Q := by
      refine withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp hZm).aemeasurable ?_
      filter_upwards [hZpos] with x hx
      exact (ENNReal.ofReal_pos.2 hx).ne'
    obtain ⟨α₁, ζ₁, hα₁⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₁ θ₁ hĤ
    obtain ⟨α₂, ζ₂, hα₂⟩ := exists_isFlowLine_of_param h12p h13 hκ hbR y₂ θ₂ hĤ
    refine ⟨Z, _, α₁, α₂, ζ₁, ζ₂, hZm.aemeasurable, hZpos, hZ1, hĤ, hα₁, hα₂, ?_⟩
    have hy : ∀ (V : Set ℂ) (a c y : ℝ), (∀ z ∈ closure V, z.im = 0 → z.re ∈ Icc a c) → Icc a c ⊆ O →
        (y : ℂ) ∉ V := fun V a c y hVI hIO hy => by
      have := hIO (hVI (y : ℂ) (subset_closure hy) (by simp))
      rw [hOn] at this
      exact this
    filter_upwards [ae_start_of_isFlowLine h₁, ae_start_of_isFlowLine h₂, hPQ.ae_le (ae_start_of_isFlowLine hα₁),
      hPQ.ae_le (ae_start_of_isFlowLine hα₂)] with x e₁ e₂ e₃ e₄
    exact ⟨stoppedAgree_zero _ _ (e₁.trans e₃.symm) (by rw [e₁]; exact hy V₁ a₁ c₁ y₁ hV₁I hI₁),
      stoppedAgree_zero _ _ (e₂.trans e₄.symm) (by rw [e₂]; exact hy V₂ a₂ c₂ y₂ hV₂I hI₂)⟩

end RLC

end InteractingSLE

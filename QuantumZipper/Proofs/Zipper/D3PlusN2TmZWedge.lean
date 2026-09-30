import QuantumZipper.Proofs.Zipper.D3PlusN2TmZStmt

/-!
# N2-zero, node N2Z-WEDGELOC: the wedge side of the window transfer (proved)

Task N2-TMZERO. `n2ZWedgeLoc_holds : N2ZWedgeLocStmt`: for the circle-average embedded wedge
field `V = wedgeField (lateralPart X'') A Q`,

* its window data `resField K ∘ V` are a.e.-measurable (as `WedgeMeas.aemeasurable_coords_wedgeField`);
* a.s., on the window event `n2Good γ K R`, `locFieldFull R (canonical γ V) = gK γ K R (resField K V)`
  (`locFieldFull_canonical_eq_gK`: global = local area measure below the window, the global scale
  equals the window scale, then `locFieldFull_canonicalOn_eq_local`);
* `P''(resField K V ∉ n2Good γ K R) → 0` as `K → ∞` (`eventually_mem_n2Good`: the window scale is
  the global scale `scaleParam γ V ∈ (0, ∞)` once `K > (R+2)·scaleParam`; a.s. positivity
  `Wire2.ae_wedge_canonical_spec`).

Source: Duplantier–Miller–Sheffield arXiv:1409.7055, proof of Prop. 4.8 (p. 79: restriction of the
surfaces to `B(0,R)`); the Lean steps are own elementary arguments (locality of the area measure,
continuity of measure from above).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

theorem agreeNear_locModel_res (γ : ℝ) (K : ℕ) (y : FieldSample) :
    AgreeNear y (locModel γ 0 K (resField K y, 0)) K := by
  classical
  intro n k z hz
  have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet K := ⟨n, k, z, hz, rfl⟩
  simp [locModel, dif_pos hmem, resField]

theorem exists_isVagueLimitOn_of_scaleParam_pos {γ : ℝ} {y : FieldSample}
    (h : 0 < scaleParam γ y) : ∃ m, IsVagueLimitOn H (areaApprox γ y) m := by
  by_contra hne
  have h0 : qAreaMeasure γ y = 0 := by unfold qAreaMeasure; rw [dif_neg hne]
  unfold scaleParam at h
  rw [h0] at h
  simp at h

/-- With a global area measure, the window data determine the scale surrogate. -/
theorem scaleSur_res_eq {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hy : IsVagueLimitOn H (areaApprox γ y) μ) (K : ℕ) :
    scaleSur γ 0 K (resField K y, 0) = scaleParamOn γ y (halfDisc K) := by
  have hag := agreeNear_locModel_res γ K y
  have hyK := isVagueLimitOn_restrict (isOpen_halfDisc K) (halfDisc_subset_H K) hy
  have hgood : (resField K y, (0 : FieldSample)) ∈ goodN1 γ 0 K :=
    ⟨_, isVagueLimitOn_halfDisc_of_agree hag hyK⟩
  rw [scaleSur_eq hgood, ← scaleParamOn_halfDisc_congr hag]

/-- Global and window area agree below the window. -/
theorem qArea_eq_window {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hy : IsVagueLimitOn H (areaApprox γ y) μ) (K : ℕ) {b : ℝ} (hb : b ≤ K) :
    qAreaMeasure γ y (Metric.ball 0 b ∩ H) =
      qAreaMeasureOn γ y (halfDisc K) (Metric.ball 0 b ∩ H) := by
  have hag : AgreeNear y y K := fun _ _ _ _ => rfl
  rw [qAreaMeasure_eq hy, qAreaMeasureOn_eq_restrict_of_agree hag hy,
    Measure.restrict_apply (Metric.isOpen_ball.inter isOpen_H).measurableSet]
  have hsub : Metric.ball (0 : ℂ) b ∩ H ⊆ halfDisc K :=
    fun z hz => ⟨Metric.ball_subset_ball hb hz.1, hz.2⟩
  rw [inter_eq_left.2 hsub]

/-- **Deterministic window identity for the global canonical description.** -/
theorem locFieldFull_canonical_eq_gK {γ : ℝ} {y : FieldSample} {μ : Measure ℂ}
    (hy : IsVagueLimitOn H (areaApprox γ y) μ) {K R : ℕ} (hK : 0 < K)
    (hG : resField K y ∈ n2Good γ K R) :
    locFieldFull R (canonical γ y) = gK γ K R (resField K y) := by
  have hK' : (0 : ℝ) < K := Nat.cast_pos.2 hK
  obtain ⟨h0, hlt⟩ := hG
  rw [scaleSur_res_eq hy K] at h0 hlt
  have hlt' : scaleParamOn γ y (halfDisc K) < K :=
    hlt.trans_le (div_le_self hK'.le (by linarith [(R.cast_nonneg : (0 : ℝ) ≤ R)]))
  have hscale := scaleParam_eq_scaleParamOn_of_lt (fun b hb => qArea_eq_window hy K hb) h0 hlt'
  have e : canonical γ y = canonicalOn γ y (halfDisc K) := by
    rw [canonical, canonicalOn, hscale]
  rw [e]
  exact locFieldFull_canonicalOn_eq_local hK' le_rfl h0 hlt

/-- **The window event holds for all large windows** when the global scale is positive. -/
theorem eventually_mem_n2Good {γ : ℝ} {y : FieldSample} (hs : 0 < scaleParam γ y) (R : ℕ) :
    ∀ᶠ K : ℕ in atTop, resField K y ∈ n2Good γ K R := by
  obtain ⟨μ, hy⟩ := exists_isVagueLimitOn_of_scaleParam_pos hs
  have hR : (0 : ℝ) < R + 2 := by linarith [(R.cast_nonneg : (0 : ℝ) ≤ R)]
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop ((R + 2) * scaleParam γ y)]
    with K hK
  have hsK : scaleParam γ y < K := by nlinarith
  have hwin : scaleParamOn γ y (halfDisc K) = scaleParam γ y := by
    unfold scaleParamOn
    unfold scaleParam at hs hsK ⊢
    refine sInf_eq_of_agree_below (ε := K) (fun a ha => ha.1) (fun a ha => ha.1)
      (fun a ha => ?_) ?_ hsK
    · simp only [mem_setOf_eq, qArea_eq_window hy K ha.le]
    · by_contra hne
      rw [not_nonempty_iff_eq_empty] at hne
      rw [hne, Real.sInf_empty] at hs
      exact lt_irrefl _ hs
  refine ⟨?_, ?_⟩
  · rw [scaleSur_res_eq hy K, hwin]; exact hs
  · rw [scaleSur_res_eq hy K, hwin, lt_div_iff₀ hR]; linarith

/-! ## The probabilistic statements -/

theorem aemeasurable_resField_wedgeV {γ α : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → FieldSample} {A : ℝ → Ω → ℝ}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) (hA : IsWedgeProcess α (Qc γ) A P)
    (K : ℕ) : AEMeasurable (fun ω => resField K (wedgeV γ X A ω)) P := by
  obtain ⟨B, B', hB, hB', -, hAB⟩ := hA
  obtain ⟨G, hGm, hG0, hGc, hGmeas⟩ :=
    WedgeMeas.exists_good_version (P := P) (fun t => hB.aemeasurable t) hB.cont
  obtain ⟨G', hG'm, hG'0, hG'c, hG'meas⟩ :=
    WedgeMeas.exists_good_version (P := P) (fun t => hB'.aemeasurable t) hB'.cont
  set Bt : ℝ≥0 → Ω → ℝ := fun t => G.indicator (B t) with hBt
  set Bt' : ℝ≥0 → Ω → ℝ := fun t => G'.indicator (B' t) with hBt'
  have hcont : ∀ {C : ℝ≥0 → Ω → ℝ} {S : Set Ω}, (∀ ω ∈ S, Continuous (C · ω)) →
      ∀ ω, Continuous fun t => S.indicator (C t) ω := by
    intro C S hS ω
    by_cases hω : ω ∈ S
    · simp only [indicator_of_mem hω]; exact hS ω hω
    · simp only [indicator_of_notMem hω]; exact continuous_const
  have hÂ := WedgeMeas.measurable_wedgePath_joint α (Qc γ) (B := Bt) (B' := Bt')
    (hcont hGc) (hcont hG'c) hGmeas hG'meas
  set Â : Ω × ℝ → ℝ := fun q => wedgePath α (Qc γ) (fun s => Bt s q.1) (fun s => Bt' s q.1) q.2
  have hmeas : Measurable fun ω =>
      resField K (wedgeField (lateralPart (X ω)) (fun t => Â (ω, t)) (Qc γ)) := by
    refine measurable_pi_iff.2 fun μ => ?_
    have : IsFiniteMeasure μ.1 := μ.2.1.1
    exact WedgeMeas.measurable_wedgeField_apply hX hÂ (Qc γ) μ.1
  refine hmeas.aemeasurable.congr ?_
  have hae : ∀ᵐ ω ∂P, ω ∈ G ∩ G' := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) (measure_union_null hG0 hG'0)
    simp only [mem_setOf_eq, mem_inter_iff, not_and_or] at hω
    rcases hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  filter_upwards [hae] with ω hω
  have e : (fun t => Â (ω, t)) = fun t => A t ω := by
    funext t
    rw [hAB ω t]
    simp only [Â, hBt, hBt', indicator_of_mem hω.1, indicator_of_mem hω.2]
  simp only [wedgeV, e]

/-- **Node N2Z-WEDGELOC holds.** -/
theorem n2ZWedgeLoc_holds : N2ZWedgeLocStmt := by
  intro γ α Ω'' _ P'' _ X'' A hγ hγ2 hα hX'' hA hInd
  have hpos : ∀ᵐ ω ∂P'', 0 < scaleParam γ (wedgeV γ X'' A ω) :=
    (Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX'' hA hInd).mono fun ω h => h.1
  have hmeasV : ∀ K : ℕ, AEMeasurable (fun ω => resField K (wedgeV γ X'' A ω)) P'' :=
    aemeasurable_resField_wedgeV hX''.measurable_coord hA
  have hnull : P'' {ω | ¬ 0 < scaleParam γ (wedgeV γ X'' A ω)} = 0 := ae_iff.1 hpos
  refine ⟨hmeasV, fun K R hK => ?_, fun R => ?_⟩
  · refine measure_mono_null (fun ω hω => ?_) hnull
    obtain ⟨h1, h2⟩ := hω
    intro hs
    obtain ⟨μ, hy⟩ := exists_isVagueLimitOn_of_scaleParam_pos hs
    exact h2 (locFieldFull_canonical_eq_gK hy hK h1)
  · set S : ℕ → Set Ω'' := fun K => {ω | resField K (wedgeV γ X'' A ω) ∉ n2Good γ K R}
      with hS
    set T : ℕ → Set Ω'' := fun K => ⋃ j : ℕ, S (K + j) with hT
    have hSn : ∀ K, NullMeasurableSet (S K) P'' := fun K =>
      (hmeasV K).nullMeasurableSet_preimage (measurableSet_n2Good γ K R).compl
    have hTn : ∀ K, NullMeasurableSet (T K) P'' := fun K =>
      NullMeasurableSet.iUnion fun j => hSn (K + j)
    have hanti : Antitone T := by
      intro K K' hKK' ω hω
      simp only [hT, mem_iUnion] at hω ⊢
      obtain ⟨j, hj⟩ := hω
      refine ⟨K' - K + j, ?_⟩
      have e : K + (K' - K + j) = K' + j := by omega
      rw [e]; exact hj
    have hInter : P'' (⋂ K, T K) = 0 := by
      refine measure_mono_null (fun ω hω => ?_) hnull
      intro hs
      obtain ⟨K0, hK0⟩ := (eventually_mem_n2Good hs R).exists_forall_of_atTop
      have hmem := mem_iInter.1 hω K0
      simp only [hT, mem_iUnion] at hmem
      obtain ⟨j, hj⟩ := hmem
      exact hj (hK0 (K0 + j) (Nat.le_add_right _ _))
    have hlim := tendsto_measure_iInter_atTop (μ := P'') hTn hanti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun K => measure_mono ?_)
    intro ω hω
    simp only [hT, mem_iUnion]
    exact ⟨0, by rw [Nat.add_zero]; exact hω⟩

end D3Plus
end QuantumZipper

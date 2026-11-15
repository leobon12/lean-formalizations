/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.GFF.LocalSets.MarkedAvoidance
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Probability tools for the conditional-mean reconstruction (C.5)

Packet PROVE-WHOLEFIELD9 (follow-up note C.5, `source/external/AstraIG1/ig1_followup_proofs.txt` L1705–1840). Abstract
lemmas, no field or evolution:

* `ae_tendsto_condExp_of_tendsto_bdd`: **conditional dominated convergence, almost surely**: bounded `f_n → f` almost
  surely gives `E[f_n | 𝒢] → E[f | 𝒢]` almost surely;
* `measure_le_two_mul_abs_le_of_condCharFun`: **the median bound** (as in `LocalSets.measure_le_two_mul_abs_le`, for an
  arbitrary σ-algebra): if `E[e^{itX} | 𝒜] = e^{itM} e^{−t² q/2}` for every `t`, then `P(G) ≤ 2 P(G ∩ {|M| ≤ |X|})` for
  `G ∈ 𝒜`;
* `ae_bddAbove_of_median`: the median bound for a sequence turns almost-sure boundedness of `|X_n|` into almost-sure
  boundedness of `|M_n|`;
* `tendsto_of_bdd_of_tendsto_exp`: a bounded real sequence `μ_n` with `e^{icμ_n}` convergent for every rational `c`
  converges.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

/-! ### Conditional dominated convergence, almost surely -/

section DCT

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

omit [IsFiniteMeasure P] in
/-- `‖E[g | 𝒢]‖ ≤ 2 E[‖g‖ | 𝒢]` (real and imaginary parts). -/
theorem ae_norm_condExp_le {g : Ω → ℂ} (hg : Integrable g P) :
    ∀ᵐ ω ∂P, ‖(P[g | 𝒢]) ω‖ ≤ 2 * (P[fun ω => ‖g ω‖ | 𝒢]) ω := by
  have hre := Complex.reCLM.comp_condExp_comm (m := 𝒢) hg
  have him := Complex.imCLM.comp_condExp_comm (m := 𝒢) hg
  have hn : Integrable (fun ω => ‖g ω‖) P := hg.norm
  have hr : Integrable (fun ω => (g ω).re) P := Complex.reCLM.integrable_comp hg
  have hi : Integrable (fun ω => (g ω).im) P := Complex.imCLM.integrable_comp hg
  have m1 := condExp_mono (m := 𝒢) hr hn (Eventually.of_forall fun ω => Complex.re_le_norm (g ω))
  have m2 := condExp_mono (m := 𝒢) hr.neg hn (Eventually.of_forall fun ω => by
    have := Complex.abs_re_le_norm (g ω); simp only [Pi.neg_apply]; linarith [neg_abs_le (g ω).re])
  have m3 := condExp_mono (m := 𝒢) hi hn (Eventually.of_forall fun ω => Complex.im_le_norm (g ω))
  have m4 := condExp_mono (m := 𝒢) hi.neg hn (Eventually.of_forall fun ω => by
    have := Complex.abs_im_le_norm (g ω); simp only [Pi.neg_apply]; linarith [neg_abs_le (g ω).im])
  have n2 := condExp_neg (m := 𝒢) (μ := P) (fun ω => (g ω).re)
  have n4 := condExp_neg (m := 𝒢) (μ := P) (fun ω => (g ω).im)
  filter_upwards [hre, him, m1, m2, m3, m4, n2, n4] with ω e1 e2 h1 h2 h3 h4 h5 h6
  have er : ((P[g | 𝒢]) ω).re = (P[fun ω => (g ω).re | 𝒢]) ω := by
    have := e1; simp only [Function.comp] at this; exact this
  have ei : ((P[g | 𝒢]) ω).im = (P[fun ω => (g ω).im | 𝒢]) ω := by
    have := e2; simp only [Function.comp] at this; exact this
  rw [h5, Pi.neg_apply] at h2
  rw [h6, Pi.neg_apply] at h4
  calc ‖(P[g | 𝒢]) ω‖ ≤ |((P[g | 𝒢]) ω).re| + |((P[g | 𝒢]) ω).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * (P[fun ω => ‖g ω‖ | 𝒢]) ω := by
      rw [er, ei]
      have a1 : |(P[fun ω => (g ω).re | 𝒢]) ω| ≤ (P[fun ω => ‖g ω‖ | 𝒢]) ω := abs_le.2 ⟨by linarith, h1⟩
      have a2 : |(P[fun ω => (g ω).im | 𝒢]) ω| ≤ (P[fun ω => ‖g ω‖ | 𝒢]) ω := abs_le.2 ⟨by linarith, h3⟩
      linarith

/-- **Conditional dominated convergence, almost surely** (bounded case): if `‖f_n‖ ≤ 1`, `‖f‖ ≤ 1` and `f_n → f`
almost surely, then `E[f_n | 𝒢] → E[f | 𝒢]` almost surely. -/
theorem ae_tendsto_condExp_of_tendsto_bdd (h𝒢 : 𝒢 ≤ mΩ) {f : ℕ → Ω → ℂ} {g : Ω → ℂ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g) (hfb : ∀ n ω, ‖f n ω‖ ≤ 1) (hgb : ∀ ω, ‖g ω‖ ≤ 1)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (P[f n | 𝒢]) ω) atTop (𝓝 ((P[g | 𝒢]) ω)) := by
  -- the tail suprema
  set D : ℕ → Ω → ℝ := fun n ω => ⨆ k : ℕ, ‖f (n + k) ω - g ω‖ with hDdef
  have hdb : ∀ n k ω, ‖f (n + k) ω - g ω‖ ≤ 2 := fun n k ω =>
    (norm_sub_le _ _).trans (by linarith [hfb (n + k) ω, hgb ω])
  have hbdd : ∀ n ω, BddAbove (range fun k => ‖f (n + k) ω - g ω‖) := fun n ω =>
    ⟨2, by rintro _ ⟨k, rfl⟩; exact hdb n k ω⟩
  have hDm : ∀ n, Measurable (D n) := fun n =>
    Measurable.iSup fun k => ((hfm (n + k)).sub hgm).norm
  have hD0 : ∀ n ω, 0 ≤ D n ω := fun n ω => (norm_nonneg _).trans (le_ciSup (hbdd n ω) 0)
  have hD2 : ∀ n ω, D n ω ≤ 2 := fun n ω => ciSup_le fun k => hdb n k ω
  have hDi : ∀ n, Integrable (D n) P := fun n =>
    Integrable.of_bound (hDm n).aestronglyMeasurable 2 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 n ω)]; exact hD2 n ω)
  have hDanti : ∀ n ω, D (n + 1) ω ≤ D n ω := fun n ω => ciSup_le fun k => by
    have := le_ciSup (hbdd n ω) (k + 1)
    simp only [show n + (k + 1) = n + 1 + k by ring] at this
    exact this
  have hDlim : ∀ᵐ ω ∂P, Tendsto (fun n => D n ω) atTop (𝓝 0) := by
    filter_upwards [hlim] with ω hω
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hω (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD0 n ω)]
    refine lt_of_le_of_lt (ciSup_le fun k => ?_) (by linarith : ε / 2 < ε)
    have := hN (n + k) (by omega)
    rw [dist_eq_norm] at this
    exact this.le
  -- their conditional expectations decrease to `0`
  set C : ℕ → Ω → ℝ := fun n => P[D n | 𝒢] with hCdef
  have hCanti : ∀ᵐ ω ∂P, ∀ n, C (n + 1) ω ≤ C n ω := ae_all_iff.2 fun n =>
    condExp_mono (hDi (n + 1)) (hDi n) (Eventually.of_forall fun ω => hDanti n ω)
  have hC0 : ∀ᵐ ω ∂P, ∀ n, 0 ≤ C n ω := ae_all_iff.2 fun n => condExp_nonneg
    (Eventually.of_forall fun ω => hD0 n ω)
  have hint0 : Tendsto (fun n => ∫ ω, D n ω ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => (2 : ℝ))
      (fun n => (hDm n).aestronglyMeasurable) (integrable_const 2)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hD0 n ω)]; exact hD2 n ω) hDlim
    simpa using this
  set L : Ω → ℝ := fun ω => ⨅ n, C n ω with hLdef
  have hCL : ∀ᵐ ω ∂P, Tendsto (fun n => C n ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hCanti, hC0] with ω h1 h2
    exact tendsto_atTop_ciInf (antitone_nat_of_succ_le h1) ⟨0, by rintro _ ⟨n, rfl⟩; exact h2 n⟩
  have hL0 : ∀ᵐ ω ∂P, L ω = 0 := by
    have hLnn : ∀ᵐ ω ∂P, 0 ≤ L ω := by
      filter_upwards [hC0] with ω h
      exact le_ciInf h
    have hLle : ∀ n, ∫ ω, L ω ∂P ≤ ∫ ω, D n ω ∂P := by
      intro n
      rw [← integral_condExp (m := 𝒢) h𝒢 (f := D n)]
      have hLm : AEStronglyMeasurable L P := by
        refine aestronglyMeasurable_of_tendsto_ae atTop (fun n => ?_) hCL
        exact (stronglyMeasurable_condExp.mono h𝒢).aestronglyMeasurable
      refine integral_mono_of_nonneg hLnn integrable_condExp ?_
      filter_upwards [hCanti, hC0] with ω h1 h2
      exact ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact h2 k⟩ n
    have hLi : ∫ ω, L ω ∂P ≤ 0 := ge_of_tendsto' hint0 hLle
    have hLm : AEStronglyMeasurable L P :=
      aestronglyMeasurable_of_tendsto_ae atTop
        (fun n => (stronglyMeasurable_condExp.mono h𝒢).aestronglyMeasurable) hCL
    have hC2 : ∀ᵐ ω ∂P, C 0 ω ≤ 2 := by
      have h := condExp_mono (m := 𝒢) (hDi 0) (integrable_const (2 : ℝ))
        (Eventually.of_forall fun ω => hD2 0 ω)
      rw [condExp_const h𝒢] at h
      exact h
    have hLint : Integrable L P := by
      refine Integrable.of_bound hLm 2 ?_
      filter_upwards [hLnn, hC0, hC2] with ω h1 h2 hc
      rw [Real.norm_eq_abs, abs_of_nonneg h1]
      exact (ciInf_le ⟨0, by rintro _ ⟨k, rfl⟩; exact h2 k⟩ 0).trans hc
    have := (integral_eq_zero_iff_of_nonneg_ae hLnn hLint).1 (le_antisymm hLi (integral_nonneg_of_ae hLnn))
    exact this
  -- the bound
  have hfi : ∀ n, Integrable (f n) P := fun n => Integrable.of_bound (hfm n).aestronglyMeasurable 1
    (Eventually.of_forall (hfb n))
  have hgi : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall hgb)
  have hsub : ∀ n, P[f n - g | 𝒢] =ᵐ[P] P[f n | 𝒢] - P[g | 𝒢] := fun n => condExp_sub (hfi n) hgi 𝒢
  have hnorm : ∀ n, ∀ᵐ ω ∂P, ‖(P[f n - g | 𝒢]) ω‖ ≤ 2 * (P[fun ω => ‖(f n - g) ω‖ | 𝒢]) ω := fun n =>
    ae_norm_condExp_le ((hfi n).sub hgi)
  have hmono : ∀ n, ∀ᵐ ω ∂P, (P[fun ω => ‖(f n - g) ω‖ | 𝒢]) ω ≤ C n ω := fun n =>
    condExp_mono ((hfi n).sub hgi).norm (hDi n) (Eventually.of_forall fun ω => by
      have := le_ciSup (hbdd n ω) 0
      simpa using this)
  filter_upwards [hCL, hL0, ae_all_iff.2 hsub, ae_all_iff.2 hnorm, ae_all_iff.2 hmono] with ω h1 h2 h3 h4 h5
  rw [h2] at h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using h1.const_mul 2)
  have e := h3 n
  rw [Pi.sub_apply] at e
  rw [← e]
  exact (h4 n).trans (mul_le_mul_of_nonneg_left (h5 n) (by norm_num))

end DCT

/-! ### The median bound for an arbitrary σ-algebra -/

section Median

variable {Ω : Type*} {𝒜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **The residual `X − M` is conditionally symmetric**: its law restricted to `G ∈ 𝒜` has the real characteristic
function `t ↦ ∫_G e^{−t² q/2}`. -/
theorem charFun_residual_of_condCharFun (h𝒜 : 𝒜 ≤ mΩ) {X M q : Ω → ℝ} (hXm : Measurable X)
    (hMm : Measurable[𝒜] M)
    (hcf : ∀ t : ℝ, P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒜] =ᵐ[P]
      fun ω => cexp (I * ((t * M ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * q ω)) : ℝ) : ℂ))
    {G : Set Ω} (hG : MeasurableSet[𝒜] G) (t : ℝ) :
    charFun ((P.restrict G).map fun ω => X ω - M ω) t =
      ((∫ ω in G, Real.exp (-(1 / 2) * (t ^ 2 * q ω)) ∂P : ℝ) : ℂ) := by
  have hDm : Measurable fun ω => X ω - M ω := hXm.sub (hMm.mono h𝒜 le_rfl)
  rw [charFun_apply_real, integral_map hDm.aemeasurable (by fun_prop)]
  set Wf : Ω → ℂ := fun ω => cexp (-(I * ((t * M ω : ℝ) : ℂ)))
  have hWm : StronglyMeasurable[𝒜] Wf :=
    (Complex.measurable_exp.comp ((measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul hMm))).neg)).stronglyMeasurable
  have hWb : ∀ ω, ‖Wf ω‖ ≤ 1 := fun ω => by
    simp only [Wf, neg_mul_eq_mul_neg, ← Complex.ofReal_neg, Complex.norm_exp_I_mul_ofReal]; rfl
  have e1 : ∀ ω, cexp (((t : ℝ) : ℂ) * ((X ω - M ω : ℝ) : ℂ) * I) =
      Wf ω * cexp (I * ((t * X ω : ℝ) : ℂ)) := fun ω => by
    simp only [Wf, ← Complex.exp_add]
    congr 1
    push_cast; ring
  simp_rw [e1]
  have hF : Integrable (fun ω => cexp (I * ((t * X ω : ℝ) : ℂ))) P := by
    refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun ω => by rw [Complex.norm_exp_I_mul_ofReal])
    exact (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      (measurable_const.mul hXm)))).aestronglyMeasurable
  have hWi : StronglyMeasurable[𝒜] (G.indicator Wf) := hWm.indicator hG
  have hWib : ∀ ω, ‖G.indicator Wf ω‖ ≤ 1 := fun ω => by
    by_cases hω : ω ∈ G
    · rw [indicator_of_mem hω]; exact hWb ω
    · rw [indicator_of_notMem hω, norm_zero]; exact zero_le_one
  have hpull := LocalSets.integral_mul_condExp_of_bdd (P := P) h𝒜 hWi hWib hF
  have e2 : ∫ ω in G, Wf ω * cexp (I * ((t * X ω : ℝ) : ℂ)) ∂P =
      ∫ ω, G.indicator Wf ω * cexp (I * ((t * X ω : ℝ) : ℂ)) ∂P := by
    rw [← integral_indicator (h𝒜 _ hG)]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ G <;> simp [hω]
  rw [e2, hpull, ← integral_complex_ofReal]
  rw [← integral_indicator (h𝒜 _ hG)]
  refine integral_congr_ae ?_
  filter_upwards [hcf t] with ω h1
  rw [h1]
  by_cases hω : ω ∈ G
  · simp only [indicator_of_mem hω, Wf, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
      Complex.exp_zero, one_mul]
  · simp [indicator_of_notMem hω]

/-- **The median bound**: `P(G) ≤ 2 P(G ∩ {|M| ≤ |X|})` for `G ∈ 𝒜`. -/
theorem measure_le_two_mul_abs_le_of_condCharFun (h𝒜 : 𝒜 ≤ mΩ) {X M q : Ω → ℝ} (hXm : Measurable X)
    (hMm : Measurable[𝒜] M)
    (hcf : ∀ t : ℝ, P[fun ω => cexp (I * ((t * X ω : ℝ) : ℂ)) | 𝒜] =ᵐ[P]
      fun ω => cexp (I * ((t * M ω : ℝ) : ℂ)) * ((Real.exp (-(1 / 2) * (t ^ 2 * q ω)) : ℝ) : ℂ))
    {G : Set Ω} (hG : MeasurableSet[𝒜] G) :
    P G ≤ 2 * P (G ∩ {ω | |M ω| ≤ |X ω|}) := by
  have hDm : Measurable fun ω => X ω - M ω := hXm.sub (hMm.mono h𝒜 le_rfl)
  -- conditional symmetry on every `G' ∈ 𝒜`
  have hsym2 : ∀ G' : Set Ω, MeasurableSet[𝒜] G' →
      P G' ≤ 2 * P ({ω | M ω ≤ X ω} ∩ G') ∧ P G' ≤ 2 * P ({ω | X ω ≤ M ω} ∩ G') := by
    intro G' hG'
    set ν : Measure ℝ := (P.restrict G').map fun ω => X ω - M ω
    have hsym : ν = ν.map Neg.neg := by
      refine Measure.ext_of_charFun (funext fun t => ?_)
      have e1 : charFun (ν.map Neg.neg) t = charFun ν (-t) := by
        rw [charFun_apply_real, charFun_apply_real, integral_map measurable_neg.aemeasurable
          (by fun_prop)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Complex.ofReal_neg]; ring_nf
      rw [e1, charFun_residual_of_condCharFun h𝒜 hXm hMm hcf hG', charFun_residual_of_condCharFun h𝒜 hXm hMm hcf hG',
        neg_sq]
    have hIci : ν (Ici 0) = ν (Iic 0) := by
      conv_lhs => rw [hsym]
      rw [Measure.map_apply measurable_neg measurableSet_Ici]
      congr 1
      ext x; simp
    have huniv : ν univ ≤ 2 * ν (Ici 0) := by
      calc ν univ ≤ ν (Ici 0 ∪ Iic 0) := measure_mono fun x _ => (le_total 0 x).elim
            (fun h => Or.inl h) (fun h => Or.inr h)
        _ ≤ ν (Ici 0) + ν (Iic 0) := measure_union_le _ _
        _ = 2 * ν (Ici 0) := by rw [← hIci, two_mul]
    have hνu : ν univ = P G' := by
      rw [Measure.map_apply hDm MeasurableSet.univ, preimage_univ, Measure.restrict_apply_univ]
    have hν1 : ν (Ici 0) = P ({ω | M ω ≤ X ω} ∩ G') := by
      rw [Measure.map_apply hDm measurableSet_Ici, Measure.restrict_apply (hDm measurableSet_Ici)]
      congr 1; ext ω; simp [sub_nonneg]
    have hν2 : ν (Iic 0) = P ({ω | X ω ≤ M ω} ∩ G') := by
      rw [Measure.map_apply hDm measurableSet_Iic, Measure.restrict_apply (hDm measurableSet_Iic)]
      congr 1; ext ω; simp
    refine ⟨?_, ?_⟩
    · rw [← hνu, ← hν1]; exact huniv
    · rw [← hνu, ← hν2, ← hIci]; exact huniv
  have hG1 : MeasurableSet[𝒜] ({ω | 0 ≤ M ω} ∩ G) := (measurableSet_le measurable_const hMm).inter hG
  have hG2 : MeasurableSet[𝒜] ({ω | M ω < 0} ∩ G) := (measurableSet_lt hMm measurable_const).inter hG
  have hsplit : P G = P ({ω | 0 ≤ M ω} ∩ G) + P ({ω | M ω < 0} ∩ G) := by
    rw [← measure_union _ (h𝒜 _ hG2)]
    · congr 1; ext ω; simp only [mem_union, mem_inter_iff, mem_ofPred_eq]
      constructor
      · intro h1; rcases le_or_gt 0 (M ω) with h2 | h2
        · exact Or.inl ⟨h2, h1⟩
        · exact Or.inr ⟨h2, h1⟩
      · rintro (⟨-, h1⟩ | ⟨-, h1⟩) <;> exact h1
    · exact Set.disjoint_left.2 fun ω h1 h2 => by
        simp only [mem_inter_iff, mem_ofPred_eq] at h1 h2; linarith [h1.1, h2.1]
  have h1 := (hsym2 _ hG1).1
  have h2 := (hsym2 _ hG2).2
  have hsub1 : {ω | M ω ≤ X ω} ∩ ({ω | 0 ≤ M ω} ∩ G) ⊆
      (G ∩ {ω | |M ω| ≤ |X ω|}) ∩ {ω | 0 ≤ M ω} := by
    rintro ω ⟨ha, hb, hc⟩
    simp only [mem_ofPred_eq] at ha hb
    refine ⟨⟨hc, ?_⟩, hb⟩
    simp only [mem_ofPred_eq]
    rw [abs_of_nonneg hb]; exact ha.trans (le_abs_self _)
  have hsub2 : {ω | X ω ≤ M ω} ∩ ({ω | M ω < 0} ∩ G) ⊆
      (G ∩ {ω | |M ω| ≤ |X ω|}) \ {ω | 0 ≤ M ω} := by
    rintro ω ⟨ha, hb, hc⟩
    simp only [mem_ofPred_eq] at ha hb
    refine ⟨⟨hc, ?_⟩, by simp only [mem_ofPred_eq, not_le]; exact hb⟩
    simp only [mem_ofPred_eq]
    rw [abs_of_neg hb]
    have := neg_le_abs (X ω)
    linarith
  have hmeasD : MeasurableSet {ω | 0 ≤ M ω} := measurableSet_le measurable_const (hMm.mono h𝒜 le_rfl)
  calc P G = P ({ω | 0 ≤ M ω} ∩ G) + P ({ω | M ω < 0} ∩ G) := hsplit
    _ ≤ 2 * P ((G ∩ {ω | |M ω| ≤ |X ω|}) ∩ {ω | 0 ≤ M ω}) +
        2 * P ((G ∩ {ω | |M ω| ≤ |X ω|}) \ {ω | 0 ≤ M ω}) :=
      add_le_add (h1.trans (mul_le_mul' le_rfl (measure_mono hsub1)))
        (h2.trans (mul_le_mul' le_rfl (measure_mono hsub2)))
    _ = 2 * P (G ∩ {ω | |M ω| ≤ |X ω|}) := by
      rw [← mul_add, measure_inter_add_sdiff _ hmeasD]

/-- **Boundedness of the conditional means.** If every `M_n` satisfies the median bound against `X_n` on `𝒜` and
`|X_n|` is almost surely bounded, then `|M_n|` is almost surely bounded. -/
theorem ae_bddAbove_of_median (h𝒜 : 𝒜 ≤ mΩ) {X M : ℕ → Ω → ℝ} (hXm : ∀ n, Measurable (X n))
    (hMm : ∀ n, Measurable[𝒜] (M n))
    (hmed : ∀ n (G : Set Ω), MeasurableSet[𝒜] G → P G ≤ 2 * P (G ∩ {ω | |M n ω| ≤ |X n ω|}))
    (hX : ∀ᵐ ω ∂P, BddAbove (range fun n => |X n ω|)) :
    ∀ᵐ ω ∂P, BddAbove (range fun n => |M n ω|) := by
  set B : ℕ → Set Ω := fun a => ⋃ n, {ω | (a : ℝ) < |M n ω|} with hBdef
  set E : ℕ → Set Ω := fun a => ⋃ n, {ω | (a : ℝ) < |X n ω|} with hEdef
  have hEm : ∀ a, MeasurableSet (E a) := fun a =>
    MeasurableSet.iUnion fun n => measurableSet_lt measurable_const (continuous_abs.measurable.comp (hXm n))
  have hBE : ∀ a, P (B a) ≤ 2 * P (E a) := by
    intro a
    set S : ℕ → Set Ω := fun n => {ω | (a : ℝ) < |M n ω|}
    have hS : ∀ n, MeasurableSet[𝒜] (S n) := fun n =>
      measurableSet_lt measurable_const (continuous_abs.measurable.comp (hMm n))
    have hD : ∀ n, MeasurableSet[𝒜] (disjointed S n) := fun n => MeasurableSet.disjointed hS n
    have hB : B a = ⋃ n, disjointed S n := (iUnion_disjointed).symm
    have hdisj : Pairwise (Function.onFun Disjoint (disjointed S)) := disjoint_disjointed S
    rw [hB, measure_iUnion hdisj fun n => h𝒜 _ (hD n)]
    calc ∑' n, P (disjointed S n) ≤ ∑' n, 2 * P (disjointed S n ∩ E a) := by
          refine ENNReal.tsum_le_tsum fun n => (hmed n _ (hD n)).trans ?_
          refine mul_le_mul' le_rfl (measure_mono fun ω hω => ⟨hω.1, ?_⟩)
          refine mem_iUnion.2 ⟨n, ?_⟩
          have h1 : (a : ℝ) < |M n ω| := disjointed_subset S n hω.1
          exact lt_of_lt_of_le h1 hω.2
      _ = 2 * P (⋃ n, disjointed S n ∩ E a) := by
          rw [ENNReal.tsum_mul_left, measure_iUnion
            (fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left)
            fun n => (h𝒜 _ (hD n)).inter (hEm a)]
      _ ≤ 2 * P (E a) := mul_le_mul' le_rfl (measure_mono (iUnion_subset fun n => inter_subset_right))
  have hEanti : Antitone E := fun a b hab => iUnion_mono fun n ω hω => by
    show (a : ℝ) < |X n ω|
    exact lt_of_le_of_lt (by exact_mod_cast hab) hω
  have hE0 : P (⋂ a, E a) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hX] with ω ⟨C, hC⟩ hω
    obtain ⟨a, ha⟩ := exists_nat_ge C
    obtain ⟨n, hn⟩ := mem_iUnion.1 (mem_iInter.1 hω a)
    have := hC ⟨n, rfl⟩
    simp only [mem_ofPred_eq] at hn
    linarith
  have hlim : Tendsto (fun a => P (E a)) atTop (𝓝 0) := by
    rw [← hE0]
    exact tendsto_measure_iInter_atTop (fun a => (hEm a).nullMeasurableSet) hEanti ⟨0, measure_ne_top _ _⟩
  have hB0 : P (⋂ a, B a) = 0 := by
    have h2 := ENNReal.Tendsto.const_mul hlim (a := 2) (Or.inr ENNReal.ofNat_ne_top)
    rw [mul_zero] at h2
    exact le_antisymm (ge_of_tendsto' h2 fun a => (measure_mono (iInter_subset B a)).trans (hBE a)) zero_le
  rw [measure_eq_zero_iff_ae_notMem] at hB0
  filter_upwards [hB0] with ω hω
  simp only [mem_iInter, not_forall] at hω
  obtain ⟨a, ha⟩ := hω
  refine ⟨a, ?_⟩
  rintro _ ⟨n, rfl⟩
  by_contra hlt
  exact ha (mem_iUnion.2 ⟨n, lt_of_not_ge hlt⟩)

end Median

/-! ### Bounded sequences with convergent characters -/

/-- **A bounded real sequence whose characters `e^{icμ_n}` converge for every rational `c` converges.** -/
theorem tendsto_of_bdd_of_tendsto_exp {μ : ℕ → ℝ} (hb : BddAbove (range fun n => |μ n|))
    (hc : ∀ c : ℚ, ∃ L : ℂ, Tendsto (fun n => cexp (I * (((c : ℝ) * μ n : ℝ) : ℂ))) atTop (𝓝 L)) :
    ∃ ℓ : ℝ, Tendsto μ atTop (𝓝 ℓ) := by
  obtain ⟨C, hC⟩ := hb
  have hmem : ∀ n, μ n ∈ Icc (-C) C := fun n => by
    have := hC ⟨n, rfl⟩
    exact ⟨by linarith [neg_abs_le (μ n)], (le_abs_self _).trans this⟩
  obtain ⟨ℓ, hℓ, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_Icc (-C) C) hmem
  refine ⟨ℓ, isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hmem)
    fun ℓ' _ hcl => ?_⟩
  by_contra hne
  -- characters at a cluster point equal the limit
  have hchar : ∀ c : ℚ, cexp (I * (((c : ℝ) * ℓ' : ℝ) : ℂ)) = cexp (I * (((c : ℝ) * ℓ : ℝ) : ℂ)) := by
    intro c
    obtain ⟨L, hL⟩ := hc c
    have hcont : Continuous fun x : ℝ => cexp (I * (((c : ℝ) * x : ℝ) : ℂ)) := by fun_prop
    have h1 : cexp (I * (((c : ℝ) * ℓ : ℝ) : ℂ)) = L :=
      tendsto_nhds_unique ((hcont.tendsto ℓ).comp hlim) (hL.comp hφ.tendsto_atTop)
    have h2 : MapClusterPt (cexp (I * (((c : ℝ) * ℓ' : ℝ) : ℂ))) atTop
        ((fun x : ℝ => cexp (I * (((c : ℝ) * x : ℝ) : ℂ))) ∘ μ) := hcl.tendsto_comp (hcont.tendsto ℓ')
    have h3 : cexp (I * (((c : ℝ) * ℓ' : ℝ) : ℂ)) = L := eq_of_nhds_neBot (ClusterPt.mono h2 hL)
    rw [h1, h3]
  -- a small rational `c` separates `ℓ` and `ℓ'`
  have hd : 0 < |ℓ' - ℓ| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨c, hc0, hc1⟩ := exists_rat_btwn (show (0 : ℝ) < Real.pi / |ℓ' - ℓ| by positivity)
  have e := hchar c
  have e2 : cexp (I * (((c : ℝ) * (ℓ' - ℓ) : ℝ) : ℂ)) = 1 := by
    have : I * (((c : ℝ) * (ℓ' - ℓ) : ℝ) : ℂ) = I * (((c : ℝ) * ℓ' : ℝ) : ℂ) - I * (((c : ℝ) * ℓ : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.exp_sub, e, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 e2
  have hre : (c : ℝ) * (ℓ' - ℓ) = n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc0
  have habs : |(c : ℝ) * (ℓ' - ℓ)| < Real.pi := by
    rw [abs_mul, abs_of_pos hcpos]
    calc (c : ℝ) * |ℓ' - ℓ| < Real.pi / |ℓ' - ℓ| * |ℓ' - ℓ| := mul_lt_mul_of_pos_right hc1 hd
      _ = Real.pi := div_mul_cancel₀ _ hd.ne'
  rcases eq_or_ne n 0 with hn0 | hn0
  · rw [hn0, Int.cast_zero, zero_mul] at hre
    rcases mul_eq_zero.1 hre with h | h
    · exact hcpos.ne' h
    · exact hne (sub_eq_zero.1 h)
  · have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at habs
    nlinarith [Real.pi_pos]

end WholeField

end InteractingSLE

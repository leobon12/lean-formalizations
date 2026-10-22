import HigherDimLQGMetric.Main.Probability
import HigherDimLQGMetric.Main.LFPPMedian
import HigherDimLQGMetric.LfppTight.MedianBasics
import HigherDimLQGMetric.Field.Basic

/-!
# The canonical median-one limit and real-cutoff convergence

The finite-cutoff normalizer is the lower median of one point distance.  The
subsequence theorem and uniqueness then identify every limit by that median.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

/-- The LFPP normalizer is positive. -/
theorem l10a_aEps_pos {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) : 0 < aEps κ ξ ε := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  have hXm : AEMeasurable (fun g : DistRd d => lfppDist κ ξ ε g (0, e₁ d))
      (normLGFLaw d) := l10a_aemeasurable_lfppPoint hd κ hκ ξ (normLGFLaw d) id hn hε
  have hc := l10a_ae_continuous_convMollify hd κ hκ (normLGFLaw d) id hn hε
  have hXp : ∀ᵐ g ∂(normLGFLaw d), 0 < lfppDist κ ξ ε g (0, e₁ d) := by
    filter_upwards [hc] with g hg
    exact HigherDimLFPP.lfppDistOn_pos hg
      (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
      ((HigherDimLFPP.pcwJoined_cube d).mono (subset_univ _))
  rw [l6a_aEps_eq_lowerMedian]
  exact l6a_lowerMedian_pos (normLGFLaw d)
    (fun g => lfppDist κ ξ ε g (0, e₁ d)) hXm hXp

/-- The frozen normalizer is a median of the original LFPP point distance. -/
theorem l10a_isMedian_aEps {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => lfppDist κ ξ ε g (0, e₁ d)))
      (aEps κ ξ ε) := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hm : AEMeasurable (fun g : DistRd d => lfppDist κ ξ ε g (0, e₁ d))
      (normLGFLaw d) :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ (normLGFLaw d) id
      (normLGFLaw_spec_holds d hd).2.1 hε
  rw [aEps, LQGMetric.lowerMedian_eq_lowerMedianLaw hm]
  exact LQGMetric.isMedian_lowerMedianLaw

/-- Scaling by the reciprocal normalizer gives median one. -/
theorem l10a_isMedian_scaled_aEps {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g =>
        (aEps κ ξ ε)⁻¹ * lfppDist κ ξ ε g (0, e₁ d))) 1 := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have ha := l10a_aEps_pos hd hκ ξ hε
  have hm := l10a_isMedian_aEps hd hκ ξ hε
  have hXm : AEMeasurable (fun g : DistRd d => lfppDist κ ξ ε g (0, e₁ d))
      (normLGFLaw d) :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ (normLGFLaw d) id
      (normLGFLaw_spec_holds d hd).2.1 hε
  have hscale := LQGMetric.IsMedian.map_monotone
    (monotone_mul_left_of_nonneg (inv_nonneg.mpr ha.le))
    (measurable_const_mul (aEps κ ξ ε)⁻¹) hm
  rw [AEMeasurable.map_map_of_aemeasurable
    (measurable_const_mul (aEps κ ξ ε)⁻¹).aemeasurable hXm] at hscale
  simpa only [Function.comp_def, inv_mul_cancel₀ ha.ne'] using hscale

/-- Any subsequential LFPP limit has median one at `(0,e₁)` under the
normalized LGF law. -/
theorem l10a_subseq_limit_median_one {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) (εs : ℕ → ℝ) (hε : ∀ n, 0 < εs n)
    {D : DistRd d → ContMetric d}
    (hconv : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusBddCont h P →
        TendstoInProbLU P
          (fun n ω => (aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω))
          atTop (fun ω => (D (h ω)).1)) :
    LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => (D g).1 (0, e₁ d))) 1 := by
  letI : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hn : IsNormalizedLGF id (normLGFLaw d) := (normLGFLaw_spec_holds d hd).2.1
  have hC := hconv (normLGFLaw d) id hn.1.isLGFPlusBddCont
  have hp : (0, e₁ d) ∈ Metric.closedBall (0 : Rd d) 2 ×ˢ
      Metric.closedBall (0 : Rd d) 2 := by
    constructor
    · simp
    · simp [Metric.mem_closedBall, HigherDimLFPP.norm_e₁ (by omega : 0 < d)]
  have hlim : TendstoInMeasure (normLGFLaw d)
      (fun n g => (aEps κ ξ (εs n))⁻¹ * lfppDist κ ξ (εs n) g (0, e₁ d))
      atTop (fun g => (D g).1 (0, e₁ d)) := by
    simpa only [id_eq, Pi.smul_apply, smul_eq_mul] using
      (l10a_tendstoInMeasure_eval (R := 2) (p := (0, e₁ d)) (by norm_num) hp hC)
  have hXm : ∀ n, AEMeasurable
      (fun g : DistRd d =>
        (aEps κ ξ (εs n))⁻¹ * lfppDist κ ξ (εs n) g (0, e₁ d))
      (normLGFLaw d) := by
    intro n
    exact (l10a_aemeasurable_lfppPoint hd κ hκ ξ (normLGFLaw d) id hn
      (hε n)).const_mul _
  exact LQGMetric.IsMedian.of_tendstoInMeasure hlim hXm tendsto_const_nhds
    (Filter.Eventually.of_forall fun n => l10a_isMedian_scaled_aEps hd hκ ξ (hε n))

/-- Two weak assignments with median one coincide on LGF inputs. -/
theorem l10a_weak_eq_of_median_one (h14 : Theorem14Stmt)
    (hE2 : Theorem16Shape) (h103 : Lemma103Shape)
    {d : ℕ} (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ)
    (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {D D' : DistRd d → ContMetric d} {c c' : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) (hD' : IsWeakExpMetric d ξ D' c')
    (hm : LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => (D g).1 (0, e₁ d))) 1)
    (hm' : LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => (D' g).1 (0, e₁ d))) 1) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsLGFPlusCont h P →
        ∀ᵐ ω ∂P, ∀ f : C(Rd d, ℝ), ∀ u v : Rd d,
          (D' (addFun (h ω) f)).1 (u, v) = (D (addFun (h ω) f)).1 (u, v) := by
  obtain ⟨C, hC, H⟩ := h14 d ξ hd hξ hsub D D' c c' hD hD'
  letI : IsProbabilityMeasure (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).1
  have hn : IsNormalizedLGF id (normLGFLaw d) :=
    (normLGFLaw_spec_holds d (by omega : 2 ≤ d)).2.1
  have hId := H (normLGFLaw d) id hn.1.isLGFPlusCont
  have hpoint : ∀ᵐ g ∂(normLGFLaw d),
      (D' g).1 (0, e₁ d) = C * (D g).1 (0, e₁ d) := by
    filter_upwards [hId] with g hg
    simpa only [id_eq, addFun_zero] using hg 0 0 (e₁ d)
  have hDm : Measurable (fun g : DistRd d => (D g).1 (0, e₁ d)) :=
    ((continuous_eval_const (0, e₁ d)).comp continuous_subtype_val).measurable.comp
      hD.measurable
  have hD'm : Measurable (fun g : DistRd d => (D' g).1 (0, e₁ d)) :=
    ((continuous_eval_const (0, e₁ d)).comp continuous_subtype_val).measurable.comp
      hD'.measurable
  have hmap : (normLGFLaw d).map (fun g => (D' g).1 (0, e₁ d)) =
      ((normLGFLaw d).map (fun g => (D g).1 (0, e₁ d))).map (fun x => C * x) := by
    rw [Measure.map_map (measurable_const_mul C) hDm]
    exact Measure.map_congr hpoint
  have hmC : LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => (D' g).1 (0, e₁ d))) C := by
    rw [hmap]
    simpa only [mul_one] using
      (LQGMetric.IsMedian.map_monotone
        (monotone_mul_left_of_nonneg hC.le) (measurable_const_mul C) hm)
  have hC1 : C = 1 := by
    let μ : Measure ℝ := (normLGFLaw d).map
      (fun g => (D' g).1 (0, e₁ d))
    haveI : IsProbabilityMeasure μ :=
      (Measure.isProbabilityMeasure_map_iff hD'm.aemeasurable).2 inferInstance
    have hsharp : IsSharpWeakExpMetric d ξ (distExp d ξ) D' :=
      (hE2 d hd hξ hsub hD').2
    have hU : LQGMetric.lowerMedianLaw μ = LQGMetric.upperMedianLaw μ := by
      apply LQGMetric.lowerMedianLaw_eq_upperMedianLaw_of_noGap
      intro a b hab hCDF
      have ha : 0 < a := by
        by_contra hna
        have hnonpos : a ≤ 0 := le_of_not_gt hna
        have he : {g : DistRd d | (D' g).1 (0, e₁ d) ≤ a} = ∅ := by
          apply Set.eq_empty_of_forall_notMem
          intro g hg
          have hp : 0 < (D' g).1 (0, e₁ d) :=
            (D' g).apply_pos (HigherDimLFPP.e₁_ne_zero (by omega : 0 < d)).symm
          exact (not_le.mpr (lt_of_le_of_lt hnonpos hp)) hg
        rw [Measure.map_apply hD'm measurableSet_Iic] at hCDF
        change 0 < (normLGFLaw d) {g | (D' g).1 (0, e₁ d) ≤ a} at hCDF
        rw [he, measure_empty] at hCDF
        exact (lt_irrefl 0) hCDF
      have hsupport := h103 d hd hξ hsub hsharp (normLGFLaw d) id hn ha hab
      rw [Measure.map_apply hD'm measurableSet_Ioo]
      exact hsupport
    exact LQGMetric.IsMedian.eq_of_unique hU hmC hm'
  intro Ω _ P _ h hh
  simpa only [hC1, one_mul] using H P h hh

/-- Corollary 10.4: one median-one strong assignment is the probability
limit of normalized LFPP for every admissible kernel and every real cutoff. -/
theorem cor104_of_inputs (hB3 : B3Goal)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ),
      DGZ.RealEpsAdapterShape d κ ξ Q)
    (hE2 : Theorem16Shape) (h14s : Theorem14SharpStmt)
    (h102 : Cor102SharpShape) (h103 : Lemma103Shape)
    (hShell : ShellDecouplingFun) :
    ∀ (d : ℕ) (ξ : ℝ), 3 ≤ d → 0 < ξ →
      Real.sqrt (2 * d) < distExp d ξ →
      ∃ (D : DistRd d → ContMetric d) (c : ℝ → ℝ),
        IsWeakExpMetric d ξ D c ∧
        IsStrongExpMetric d ξ (distExp d ξ) D ∧
        LQGMetric.IsMedian
          ((normLGFLaw d).map (fun g => (D g).1 (0, e₁ d))) 1 ∧
        ∀ κ : Rd d → ℝ, HigherDimLFPP.IsLFPPKernel κ →
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistRd d), IsLGFPlusBddCont h P →
              TendstoInProbLU P
                (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω))
                (𝓝[>] 0) (fun ω => (D (h ω)).1) := by
  intro d ξ hd hξ hsub
  have hd2 : 2 ≤ d := by omega
  let ε₀ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε₀pos : ∀ n, 0 < ε₀ n := fun n => by dsimp [ε₀]; positivity
  have hε₀lim : Tendsto ε₀ atTop (𝓝 0) := by
    simpa only [ε₀] using tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨κ₀, hκ₀⟩ := HigherDimLFPP.exists_isLFPPKernel d
  obtain ⟨φ₀, D₀, c₀, hφ₀, hD₀, hconv₀⟩ :=
    (l10a_l8_of_inputs hB3 hB2 hShell hd2 hκ₀ hξ hsub)
      ε₀ hε₀pos hε₀lim
  have hm₀ : LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => (D₀ g).1 (0, e₁ d))) 1 :=
    l10a_subseq_limit_median_one hd2 hκ₀ ξ (ε₀ ∘ φ₀)
      (fun n => hε₀pos (φ₀ n)) hconv₀
  have hstrong : IsStrongExpMetric d ξ (distExp d ξ) D₀ :=
    h102 d hd hξ hsub (hE2 d hd hξ hsub hD₀).2
  refine ⟨D₀, c₀, hD₀, hstrong, hm₀, ?_⟩
  intro κ hκ Ω _ P _ h hh
  let X : ℝ → Ω → Rd d × Rd d → ℝ :=
    fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)
  apply l10a_subseq_principle P X (fun ω => (D₀ (h ω)).1)
  intro εs hεs hεslim
  obtain ⟨φ, D', c', hφ, hD', hconv'⟩ :=
    (l10a_l8_of_inputs hB3 hB2 hShell hd2 hκ hξ hsub)
      εs hεs hεslim
  have hm' : LQGMetric.IsMedian
      ((normLGFLaw d).map (fun g => (D' g).1 (0, e₁ d))) 1 :=
    l10a_subseq_limit_median_one hd2 hκ ξ (εs ∘ φ)
      (fun n => hεs (φ n)) hconv'
  have hEq := l10a_weak_eq_of_median_one
    (theorem14_of_inputs hE2 h14s) hE2 h103 hd hξ hsub hD₀ hD' hm₀ hm'
      P h hh.isLGFPlusCont
  have hAE : ∀ᵐ ω ∂P,
      (⇑(D' (h ω)).1 : Rd d × Rd d → ℝ) =
      (⇑(D₀ (h ω)).1 : Rd d × Rd d → ℝ) := by
    filter_upwards [hEq] with ω hω
    funext p
    simpa only [addFun_zero] using hω 0 p.1 p.2
  refine ⟨φ, hφ, ?_⟩
  exact l10a_tip_congr P (fun n => X (εs (φ n))) atTop
    (hconv' P h hh) hAE

end HigherDimLQGMetric

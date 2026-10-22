import HigherDimLQGMetric.Determ.CopyMeas
import LQGMetric.Papers.LM.T1_7V12

/-! Internal ball distance as a function of all cell observations, jointly in the shift. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open LQGMetric
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

variable {dim : ℕ}

theorem determ_l53_joint (ν : Measure (ContMetric dim)) [IsProbabilityMeasure ν]
    (hL : ∀ᵐ d ∂ν, d.IsLength) {C : ℝ} (hC : 0 ≤ C)
    (hcopy : ∀ᵐ p ∂ν.prod ν, ∀ z w : Rd dim, p.2.1 (z, w) ≤ C * p.1.1 (z, w))
    {m : ℕ} {R : ℝ} (hmR : (m : ℝ) ≤ R) {z w : Rd dim} (hz : ‖z‖ < m) (hw : ‖w‖ < m)
    {ε : ℝ} (hε : 0 < ε) :
    LQGMetric.AEDeterminedBy (fun p : (Fin dim → ℝ) × ContMetric dim => (determF m z w p.2).toReal)
      (fun p => (p.1, determY ε p.1 (determFixedBox (d := dim) ε R) p.2)) ((determShiftLaw dim).prod ν) := by
  set s := determFixedBox (d := dim) ε R
  set μ := (determShiftLaw dim).prod ν with hμ
  set X : (Fin dim → ℝ) × ContMetric dim → (Fin dim → ℝ) × (s → ℕ → ℝ≥0∞) :=
    fun p => (p.1, determY ε p.1 s p.2) with hXdef
  have hX : Measurable X := measurable_fst.prodMk (determ_measurable_gridY ε s)
  set F : ContMetric dim → ℝ := fun d => (determF m z w d).toReal with hFdef
  have hFm : Measurable F := (determ_measurableF m z w).ennreal_toReal
  letI : Nonempty (ContMetric dim) := nonempty_of_isProbabilityMeasure ν
  refine LQGMetric.LM.t17v_aeDet_comp (μ := μ) hX measurable_snd hFm ?_
  set Q := condCopyMeasure Prod.snd X μ hX with hQ
  have hμsnd : μ.map Prod.snd = ν := by
    rw [hμ, Measure.map_snd_prod, measure_univ, one_smul]
  have hQ1 : Q.map (fun q => q.1.2) = ν := by
    rw [show (fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => q.1.2) = Prod.snd ∘ Prod.fst
      from rfl, ← Measure.map_map measurable_snd measurable_fst, hQ, condCopyMeasure_fst, hμsnd]
  have hQ2 : Q.map Prod.snd = ν := by
    have h2 := congrArg (fun π : Measure (((Fin dim → ℝ) × (s → ℕ → ℝ≥0∞)) × ContMetric dim) =>
      π.map Prod.snd) (condCopyMeasure_map_snd (μ := μ) (Y := Prod.snd) hX measurable_snd)
    rw [Measure.map_map measurable_snd (show Measurable fun p : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim =>
        (X p.1, p.2) from (hX.comp measurable_fst).prodMk measurable_snd),
      Measure.map_map measurable_snd (show Measurable fun ω : (Fin dim → ℝ) × ContMetric dim =>
        (X ω, ω.2) from hX.prodMk measurable_snd)] at h2
    exact h2.trans hμsnd
  obtain ⟨M, hM, hML, hνM⟩ := determ_measurable_ae_subset ν hL
  have g1 : ∀ᵐ q ∂Q, q.1.2 ∈ M := by
    have h : ∀ᵐ y ∂(Q.map fun q => q.1.2), y ∈ M := by rw [hQ1]; exact hνM
    exact ae_of_ae_map (f := fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => q.1.2)
      (measurable_snd.comp measurable_fst).aemeasurable h
  have g2 : ∀ᵐ q ∂Q, q.2 ∈ M := ae_of_ae_map measurable_snd.aemeasurable (by rw [hQ2]; exact hνM)
  have hpm : Measurable fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => (q.1.2, q.2) :=
    (measurable_snd.comp measurable_fst).prodMk measurable_snd
  have g3 : ∀ᵐ q ∂Q, ∀ x y : Rd dim, q.2.1 (x, y) ≤ C ^ 2 * q.1.2.1 (x, y) := by
    have h1 : (Q.map fun q => (q.1.2, q.2)).map Prod.fst = ν := by
      rw [Measure.map_map measurable_fst hpm]; exact hQ1
    have h2 : (Q.map fun q => (q.1.2, q.2)).map Prod.snd = ν := by
      rw [Measure.map_map measurable_snd hpm]; exact hQ2
    exact ae_of_ae_map hpm.aemeasurable (determ_bilip_any_coupling hC hcopy h1 h2)
  have g4 : ∀ᵐ q ∂Q, X (q.1.1, q.2) = X q.1 := by
    have hset : MeasurableSet {t : ((Fin dim → ℝ) × (s → ℕ → ℝ≥0∞)) × ContMetric dim | X (t.1.1, t.2) = t.1} :=
      measurableSet_eq_fun (hX.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
        measurable_fst
    have hm2 : Measurable fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => (X q.1, q.2) :=
      (hX.comp measurable_fst).prodMk measurable_snd
    have h0 : ∀ᵐ t ∂(Q.map fun q => (X q.1, q.2)), X (t.1.1, t.2) = t.1 := by
      rw [condCopyMeasure_map_snd (μ := μ) (Y := Prod.snd) hX measurable_snd]
      exact (ae_map_iff (hX.prodMk measurable_snd).aemeasurable hset).2
        (Filter.Eventually.of_forall fun ω => rfl)
    exact ae_of_ae_map hm2.aemeasurable h0
  -- the bad event
  set p := TopologicalSpace.denseSeq (Rd dim × Rd dim)
  set E : Set (((Fin dim → ℝ) × ContMetric dim) × ContMetric dim) := {q | F q.1.2 < F q.2 ∧ q.2 ∈ M ∧
    q.1.2 ∈ M ∧ X (q.1.1, q.2) = X q.1 ∧ ∀ n, q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} with hEdef
  have hev : ∀ n, Measurable fun d : ContMetric dim => d.1 (p n) := fun n =>
    (continuous_eval_const _).measurable.comp measurable_subtype_coe
  have hB : MeasurableSet {q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim |
      ∀ n, q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} := by
    have : {q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim | ∀ n, q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} =
        ⋂ n, {q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim | q.2.1 (p n) ≤ C ^ 2 * q.1.2.1 (p n)} := by
      ext q; simp
    rw [this]
    exact MeasurableSet.iInter fun n => measurableSet_le ((hev n).comp measurable_snd)
      (measurable_const.mul ((hev n).comp (measurable_snd.comp measurable_fst)))
  have hE : MeasurableSet E :=
    (measurableSet_lt (hFm.comp (measurable_snd.comp measurable_fst))
      (hFm.comp measurable_snd)).inter ((measurable_snd hM).inter
      (((measurable_snd.comp measurable_fst) hM).inter ((measurableSet_eq_fun
      (hX.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
      (hX.comp measurable_fst)).inter hB)))
  have hQE : Q E = 0 := by
    rw [hQ, condCopyMeasure, Measure.compProd_apply hE]
    refine (lintegral_prod_symm (μ := determShiftLaw dim) (ν := ν) _
      ((condCopyKernel Prod.snd X μ hX).measurable_kernel_prodMk_left hE).aemeasurable).trans ?_
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hνM] with d hdM
    have hd := hML hdM
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [ae_restrict_of_ae (determ_l53_perD hd (c := C ^ 2) (sq_nonneg C) hmR hz hw hε),
      ae_restrict_mem (MeasurableSet.univ_pi fun _ => measurableSet_Ico)] with θ hθ hθm
    refine (measure_mono_null (fun d' hd' => ?_) measure_empty)
    obtain ⟨hlt, hd'M, -, hXeq, hbil⟩ := hd'
    exfalso
    have hd' := hML hd'M
    have hS : ∀ k ∈ s, ∀ u ∈ determCube ε θ k, ∀ v ∈ determCube ε θ k,
        d.internal (determCube ε θ k) u v = d'.internal (determCube ε θ k) u v := by
      intro k hk
      have h2 := congrArg Prod.snd hXeq
      have henc : determ_enc (determCube ε θ k) d' = determ_enc (determCube ε θ k) d :=
        congrFun h2 ⟨k, hk⟩
      exact determ_internal_eq_of_enc hd hd' (determ_isOpen_cube ε θ k) henc
    have hle := hθ hθm d' (determ_le_of_dense hbil) hS
    have hfin : determF m z w d ≠ ⊤ := by
      rw [determF, ← d.internal_eq_chainInf hd Metric.isOpen_ball]
      exact d.internal_ne_top_of_isPreconnected hd Metric.isOpen_ball (convex_ball _ _).isPreconnected
        (mem_ball_zero_iff.2 hz) (mem_ball_zero_iff.2 hw)
    exact absurd (ENNReal.toReal_mono hfin hle) (not_le.2 hlt)
  have hle : ∀ᵐ q ∂Q, F q.2 ≤ F q.1.2 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hQE, g1, g2, g3, g4] with q hq h1 h2 h3 h4
    by_contra hc
    exact hq ⟨not_le.1 hc, h2, h1, h4, fun n => h3 _ _⟩
  have hmap : Q.map (fun q => F q.2) = Q.map (fun q => F q.1.2) := by
    rw [show (fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => F q.2) = F ∘ Prod.snd from rfl,
      show (fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => F q.1.2) = F ∘ fun q => q.1.2 from rfl,
      ← Measure.map_map hFm measurable_snd,
      ← Measure.map_map (g := F) (f := fun q : ((Fin dim → ℝ) × ContMetric dim) × ContMetric dim => q.1.2) hFm
        (measurable_snd.comp measurable_fst), hQ1, hQ2]
  filter_upwards [LQGMetric.LM.t17v_ae_eq_of_le_of_map_eq (hFm.comp measurable_snd)
    (hFm.comp (measurable_snd.comp measurable_fst)) hle hmap] with q hq
  exact hq.symm

end HigherDimLQGMetric

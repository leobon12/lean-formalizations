import HigherDimLQGMetric.Determ.KernelProd
import LQGMetric.Prob.CondCopies
import LQGMetric.Papers.DFGPS.L2_19

/-! A local metric comparable to a conditionally independent copy is field determined. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open HigherDimLFPP (Rd)
open scoped ENNReal

namespace HigherDimLQGMetric

theorem l7e_of_measurable_copy {d : ℕ} {ξ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (D D' : Ω → ContMetric d) (C : ℝ)
    (hh : IsNormalizedLGF h P) (hloc : IsXiAdditiveRd ξ P h D D)
    (hD'm : Measurable D')
    (hci : LQGMetric.CondIndepEv (fullSigmaRd h)
      (MeasurableSpace.comap D inferInstance)
      (MeasurableSpace.comap D' inferInstance) P)
    (hlaw : P.map (fun ω => (h ω, D ω)) = P.map (fun ω => (h ω, D' ω)))
    (hbound : ∀ᵐ ω ∂P, ∀ x y : Rd d,
      (D' ω).1 (x, y) ≤ C * (D ω).1 (x, y)) :
    LQGMetric.AEDeterminedBy D h P := by
  haveI : Nonempty Ω := ⟨(nonempty_of_measure_ne_zero
    (show P (Set.univ : Set Ω) ≠ 0 by simp)).choose⟩
  haveI : Nonempty (ContMetric d) := ⟨D (Classical.choice ‹Nonempty Ω›)⟩
  have hm := hh.1.measurable
  have hDm := hloc.1
  have hlen : ∀ᵐ ω ∂P, (D ω).IsLength := hloc.2.2.1.mono fun _ hω => hω.1
  let C' : ℝ := max C 2
  have hC1 : 1 < C' := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right C 2)
  have hbound' : ∀ᵐ ω ∂P, ∀ x y : Rd d,
      (D' ω).1 (x, y) ≤ C' * (D ω).1 (x, y) := by
    filter_upwards [hbound] with ω hω x y
    exact (hω x y).trans (mul_le_mul_of_nonneg_right (le_max_left C 2)
      ((D ω).nonneg x y))
  have hcopy := determ_fiber_copy_bound P h D D' C' hm hDm hD'm hci hlaw hbound'
  have hL := determ_kernel_length P h D hm hDm hlen
  have hprod := determ_kernel_prod hh hloc
  let κ := condDistrib D h P
  let p : ℕ → Rd d × Rd d := TopologicalSpace.denseSeq (Rd d × Rd d)
  have hB : ∀ᵐ g ∂P.map h, ∀ᵐ E ∂κ g, ∀ k,
      E.1 (p k) = ∫ E', E'.1 (p k) ∂κ g := by
    have H := ae_all_iff.2 fun k : ℕ => by
      filter_upwards [hL, hcopy, hprod] with g hgL hgcopy hgprod
      exact determ_const_measure (κ g) hgL C' hC1 hgcopy hgprod (p k).1 (p k).2
    filter_upwards [H] with g hg
    exact ae_all_iff.2 fun k => hg k
  let T : Set (DistRd d × ContMetric d × ContMetric d) :=
    {t | ∀ k, t.2.1.1 (p k) = t.2.2.1 (p k)}
  have hmp (q : Rd d × Rd d) : Measurable fun E : ContMetric d => E.1 q :=
    (continuous_eval_const q).measurable.comp measurable_subtype_coe
  have hT : MeasurableSet T := by
    dsimp [T]
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurableSet_eq_fun
      ((hmp (p k)).comp (measurable_fst.comp measurable_snd))
      ((hmp (p k)).comp (measurable_snd.comp measurable_snd))
  have hQ : ∀ᵐ t ∂(P.map h ⊗ₘ (κ ×ₖ κ)), ∀ k,
      t.2.1.1 (p k) = t.2.2.1 (p k) := by
    rw [Measure.ae_compProd_iff hT]
    filter_upwards [hB] with g hg
    rw [Kernel.prod_apply]
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := κ g) (ν := κ g)).ae hg
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := κ g) (ν := κ g)).ae hg
    filter_upwards [h1, h2] with q hq1 hq2
    exact fun k => (hq1 k).trans (hq2 k).symm
  rw [show κ = condDistrib D h P from rfl,
    ← LQGMetric.condCopyMeasure_map_triple hm hDm] at hQ
  have hmcopy : Measurable fun q : Ω × ContMetric d => (h q.1, D q.1, q.2) :=
    (hm.comp measurable_fst).prodMk ((hDm.comp measurable_fst).prodMk measurable_snd)
  have hQ' := ae_of_ae_map hmcopy.aemeasurable hQ
  refine LQGMetric.aeDeterminedBy_of_condCopy_ae_eq hm hDm ?_
  filter_upwards [hQ'] with q hq
  exact Subtype.ext (DFunLike.coe_injective (Continuous.ext_on
    (TopologicalSpace.denseRange_denseSeq (Rd d × Rd d))
    (D q.1).1.continuous q.2.1.continuous
    (by rintro _ ⟨k, rfl⟩; exact hq k)))

/-- The exact L7e interface, including the case where the putative copy is not measurable.
In that case its `Measure.map` is Mathlib's fallback Dirac law; equality of joint laws
forces the original metric to be almost surely constant. -/
theorem l7e_measurable : L7e_measurable := by
  classical
  intro d ξ Ω _ P _ h D D' C hh hloc hci hlaw hC hbound
  have hm : Measurable h := hh.1.measurable
  have hDm : Measurable D := hloc.1
  let f : Ω → DistRd d × ContMetric d := fun ω => (h ω, D' ω)
  by_cases hf : AEMeasurable f P
  · have hD'ae : AEMeasurable D' P := measurable_snd.comp_aemeasurable hf
    let E : Ω → ContMetric d := hD'ae.mk D'
    have hEm : Measurable E := hD'ae.measurable_mk
    have he : D' =ᵐ[P] E := hD'ae.ae_eq_mk
    have hciE : LQGMetric.CondIndepEv (fullSigmaRd h)
        (MeasurableSpace.comap D inferInstance)
        (MeasurableSpace.comap E inferInstance) P :=
      LQGMetric.GM.Bilip.CondIndepEv.of_le_aeClosure hci
        (LQGMetric.GM.Bilip.le_aeClosure _)
        (LQGMetric.DFGPS.L219.comap_le_aeClosure_of_ae_eq
          (comap_measurable D') he.symm)
    have hlawE : P.map (fun ω => (h ω, D ω)) =
        P.map (fun ω => (h ω, E ω)) :=
      hlaw.trans (Measure.map_congr (he.mono fun ω hω => congrArg (fun e => (h ω, e)) hω))
    have hboundE : ∀ᵐ ω ∂P, ∀ x y : Rd d,
        (E ω).1 (x, y) ≤ C * (D ω).1 (x, y) := by
      filter_upwards [he, hbound] with ω heω hb x y
      simpa only [← heω] using hb x y
    exact l7e_of_measurable_copy P h D E C hh hloc hEm hciE hlawE hboundE
  · have hP : P ≠ 0 := by
      intro h0
      have h1 : P (Set.univ : Set Ω) = (1 : ℝ≥0∞) := measure_univ
      simp [h0] at h1
    haveI : Nonempty Ω := ⟨(nonempty_of_measure_ne_zero
      (show P (Set.univ : Set Ω) ≠ 0 by simp)).choose⟩
    haveI : Nonempty (DistRd d × ContMetric d) :=
      ⟨f (Classical.choice ‹Nonempty Ω›)⟩
    let a : DistRd d × ContMetric d := Classical.ofNonempty
    have hdir : P.map f = Measure.dirac a :=
      Measure.map_of_not_aemeasurable_of_ne_zero hf hP
    have hgm : Measurable (fun ω => (h ω, D ω)) := hm.prodMk hDm
    have hmeasure : P.map (fun ω => (h ω, D ω)) = Measure.dirac a :=
      hlaw.trans hdir
    have hmass : P {ω | (h ω, D ω) ≠ a} = 0 := by
      have hS : MeasurableSet ({a}ᶜ : Set (DistRd d × ContMetric d)) :=
        (measurableSet_singleton a).compl
      change P ((fun ω => (h ω, D ω)) ⁻¹' ({a}ᶜ)) = 0
      rw [← Measure.map_apply hgm hS, hmeasure]
      simp
    have hae : ∀ᵐ ω ∂P, D ω = a.2 := by
      rw [ae_iff]
      have hsub : {ω | D ω ≠ a.2} ⊆ {ω | (h ω, D ω) ≠ a} := by
        intro ω hω hcontra
        exact hω (congrArg Prod.snd hcontra)
      exact measure_mono_null hsub hmass
    exact ⟨fun _ => a.2, measurable_const, hae⟩

end HigherDimLQGMetric

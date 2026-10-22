import HigherDimLQGMetric.Locality.FiberSigma
import HigherDimLQGMetric.Locality.SecondConsistency
import HigherDimLQGMetric.Locality.JointIndep
import LQGMetric.Papers.DFGPS.L2_17Step4

/-! Conditional independence of finite internal families from the two
intrinsic arrays and the Weyl relation on a standard Borel coupling. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open LQGMetric.GM.Bilip
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l7a_limit_finite_ci
    {d : ℕ} (ξ : ℝ)
    {ι κ' : Type} (S : Finset ι) (T : Finset κ')
    (W : ι → TopologicalSpace.Opens (Rd d))
    (W' : κ' → TopologicalSpace.Opens (Rd d))
    {E : Type} [mE : MeasurableSpace E] [StandardBorelSpace E]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (D₁ D₂ : E → ContMetric d) (hD₁ : Measurable D₁)
    (F : E → C(Rd d, ℝ)) (hF : Measurable F)
    (J₁ : E → L7aFiniteArray S W) (hJ₁ : Measurable J₁)
    (J₂ : E → L7aFiniteArray T W') (hJ₂ : Measurable J₂)
    (G R : MeasurableSpace E) (hG : G ≤ mE)
    (hR : R ≤ mE)
    (hFdet : MeasurableSpace.comap F inferInstance ≤ aeClosure Q G)
    (hgood : ∀ᵐ e ∂Q,
      (D₁ e).IsLength ∧
      (∀ i : S, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun (J₁ e i),
        ∀ u v : (W i.1 : Set (Rd d)),
          (D₁ e).internal (W i.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e i) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e i) hJ v)) ∧
      (∀ j : T, ∃ hJ : LQGMetric.MetricGeometry.IsMetricFun (J₂ e j),
        ∀ u v : (W' j.1 : Set (Rd d)),
          (D₂ e).internal (W' j.1 : Set (Rd d)) u.1 v.1 =
          LQGMetric.MetricGeometry.internalEDist univ
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e j) hJ u)
            (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e j) hJ v)) ∧
      (∀ u v : Rd d,
        ENNReal.ofReal ((D₁ e).1 (u,v)) = weylScale ξ (F e) (D₂ e) u v))
    (hind : Indep (G ⊔ MeasurableSpace.comap J₁ inferInstance)
      (R ⊔ MeasurableSpace.comap J₂ inferInstance) Q)
    (H : MeasurableSpace E)
    (hH : H ≤ aeClosure Q (R ⊔ G)) :
    LQGMetric.CondIndepEv G
      (⨆ i ∈ S, MeasurableSpace.comap
        (fun e => (D₁ e).chainInf (W i : Set (Rd d))) inferInstance)
      (H ⊔ ⨆ j ∈ T, MeasurableSpace.comap
        (fun e => (D₁ e).chainInf (W' j : Set (Rd d))) inferInstance) Q := by
  letI : MeasurableSpace E := mE
  have hA : (⨆ i ∈ S, MeasurableSpace.comap
      (fun e => (D₁ e).chainInf (W i : Set (Rd d))) inferInstance) ≤
      aeClosure Q (MeasurableSpace.comap J₁ inferInstance ⊔ G) := by
    refine iSup₂_le fun i hi => ?_
    have hJ : Measurable (fun e => J₁ e ⟨i, hi⟩) := by
      simpa only [Function.comp_def] using
        (show Measurable (fun f : L7aFiniteArray S W => f (⟨i, hi⟩ : S)) from
          measurable_pi_apply (⟨i, hi⟩ : S)).comp hJ₁
    have hzero : ∀ᵐ e ∂Q,
        (D₁ e).IsLength ∧
        (∃ hE : LQGMetric.MetricGeometry.IsMetricFun (J₁ e ⟨i, hi⟩),
          ∀ u v : (W i : Set (Rd d)),
            (D₁ e).internal (W i : Set (Rd d)) u.1 v.1 =
              LQGMetric.MetricGeometry.internalEDist univ
                (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e ⟨i, hi⟩) hE u)
                (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₁ e ⟨i, hi⟩) hE v)) ∧
        (∀ u v : Rd d, ENNReal.ofReal ((D₁ e).1 (u,v)) =
          weylScale 0 (0 : C(Rd d, ℝ)) (D₁ e) u v) := by
      filter_upwards [hgood] with e he
      refine ⟨he.1, he.2.1 ⟨i, hi⟩, ?_⟩
      intro u v
      simpa only [ContinuousMap.const_zero, zero_mul, Real.exp_zero,
        ENNReal.ofReal_one, one_mul] using
        (weylScale_const_of_isLength he.1 0 0 u v).symm
    have h0 := l7a_weyl_internal_comap_le_aeClosure (ξ := 0)
      (W i).isOpen Q D₁ D₁ hD₁ (fun _ => (0 : C(Rd d, ℝ)))
      measurable_const (fun e => J₁ e ⟨i, hi⟩) hJ hzero
    exact h0.trans (aeClosure_mono (show MeasurableSpace.comap
      (fun e => ((0 : C(Rd d, ℝ)), J₁ e ⟨i, hi⟩)) inferInstance ≤
      MeasurableSpace.comap J₁ inferInstance ⊔ G by
        have hm : Measurable[MeasurableSpace.comap J₁ inferInstance]
            (fun e => ((0 : C(Rd d, ℝ)), J₁ e ⟨i, hi⟩)) :=
          measurable_const.prodMk (by
            simpa only [Function.comp_def] using
              (show Measurable
                (fun f : L7aFiniteArray S W => f (⟨i, hi⟩ : S)) from
                measurable_pi_apply (⟨i, hi⟩ : S)).comp (comap_measurable J₁))
        exact hm.comap_le.trans le_sup_left))
  have hB : H ⊔ (⨆ j ∈ T, MeasurableSpace.comap
      (fun e => (D₁ e).chainInf (W' j : Set (Rd d))) inferInstance) ≤
      aeClosure Q ((R ⊔ MeasurableSpace.comap J₂ inferInstance) ⊔ G) := by
    apply sup_le
    · exact hH.trans (aeClosure_mono (sup_le
        (le_sup_left.trans le_sup_left) le_sup_right))
    · refine iSup₂_le fun j hj => ?_
      have hJ : Measurable (fun e => J₂ e ⟨j, hj⟩) := by
        simpa only [Function.comp_def] using
          (show Measurable (fun f : L7aFiniteArray T W' => f (⟨j, hj⟩ : T)) from
            measurable_pi_apply (⟨j, hj⟩ : T)).comp hJ₂
      have hgood' : ∀ᵐ e ∂Q,
          (D₁ e).IsLength ∧
          (∃ hE : LQGMetric.MetricGeometry.IsMetricFun (J₂ e ⟨j, hj⟩),
            ∀ u v : (W' j : Set (Rd d)),
              (D₂ e).internal (W' j : Set (Rd d)) u.1 v.1 =
                LQGMetric.MetricGeometry.internalEDist univ
                  (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e ⟨j, hj⟩) hE u)
                  (LQGMetric.MetricGeometry.MetricFunSpace.pt (J₂ e ⟨j, hj⟩) hE v)) ∧
          (∀ u v : Rd d, ENNReal.ofReal ((D₁ e).1 (u,v)) =
            weylScale ξ (F e) (D₂ e) u v) := by
        filter_upwards [hgood] with e he
        exact ⟨he.1, he.2.2.1 ⟨j, hj⟩, he.2.2.2⟩
      have h0 := l7a_weyl_internal_comap_le_aeClosure ξ
        (W' j).isOpen Q D₁ D₂ hD₁ F hF
        (fun e => J₂ e ⟨j, hj⟩) hJ hgood'
      have hJle : MeasurableSpace.comap (fun e => J₂ e ⟨j, hj⟩)
          inferInstance ≤ MeasurableSpace.comap J₂ inferInstance := by
        have hm : Measurable[MeasurableSpace.comap J₂ inferInstance]
            (fun e => J₂ e ⟨j, hj⟩) := by
          simpa only [Function.comp_def] using
            (show Measurable (fun f : L7aFiniteArray T W' => f (⟨j, hj⟩ : T)) from
              measurable_pi_apply (⟨j, hj⟩ : T)).comp (comap_measurable J₂)
        exact hm.comap_le
      have hpair : MeasurableSpace.comap (fun e => (F e, J₂ e ⟨j, hj⟩))
          inferInstance ≤ MeasurableSpace.comap F inferInstance ⊔
            MeasurableSpace.comap J₂ inferInstance := by
        have hm : Measurable[MeasurableSpace.comap F inferInstance ⊔
            MeasurableSpace.comap J₂ inferInstance]
            (fun e => (F e, J₂ e ⟨j, hj⟩)) :=
          ((comap_measurable F).mono le_sup_left le_rfl).prodMk
            ((comap_measurable _).mono
              (hJle.trans le_sup_right) le_rfl)
        exact hm.comap_le
      have hJtarget : MeasurableSpace.comap J₂ inferInstance ≤
          (R ⊔ MeasurableSpace.comap J₂ inferInstance) ⊔ G :=
        (le_sup_right : MeasurableSpace.comap J₂ inferInstance ≤
          R ⊔ MeasurableSpace.comap J₂ inferInstance).trans le_sup_left
      have hJcl : MeasurableSpace.comap J₂ inferInstance ≤
          aeClosure Q ((R ⊔ MeasurableSpace.comap J₂ inferInstance) ⊔ G) :=
        hJtarget.trans (le_aeClosure _)
      have hsup : MeasurableSpace.comap F inferInstance ⊔
          MeasurableSpace.comap J₂ inferInstance ≤
          aeClosure Q ((R ⊔ MeasurableSpace.comap J₂ inferInstance) ⊔ G) :=
        sup_le (hFdet.trans (aeClosure_mono le_sup_right)) hJcl
      exact h0.trans ((aeClosure_mono (hpair.trans hsup)).trans
        (aeClosure_aeClosure_le _))
  exact LQGMetric.DFGPS.L217.condIndepEv_of_indep_of_le hG
    (Measurable.comap_le hJ₁) (sup_le hR hJ₂.comap_le)
    (by rw [sup_comm]; exact hind) hA hB

end HigherDimLQGMetric

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafVersionFAssembly

/-!
# Nonzero state samples on every live interval

A force point cannot coincide with the driver on an interval, by the
zero-volume collision clause. With no force points the driver is a positive
multiple of Brownian motion, whose positive dyadic marginals have no atom at zero.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.StoppedExtendWF Restart.FlowStopIdentG

/-- A continuous path vanishing at every dyadic point of an open interval
vanishes throughout that interval. This uses the existing dyadic approximation. -/
theorem eq_zero_on_Ioo_of_dyadic {E : Type*} [TopologicalSpace E] [T2Space E] [Zero E]
    {f : ℝ≥0 → E} {a b : ℝ≥0} (hc : ContinuousOn f (Ioo a b))
    (hz : ∀ p, dyadicTime p ∈ Ioo a b → f (dyadicTime p) = 0) :
    ∀ t ∈ Ioo a b, f t = 0 := by
  intro t ht
  have htend := tendsto_dyadicTime_upperDyadic t
  have hin := htend.eventually (isOpen_Ioo.mem_nhds ht)
  have hf := (hc.continuousWithinAt ht).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨htend, hin⟩)
  have he : (fun n => f (dyadicTime (upperDyadic t n))) =ᶠ[atTop] fun _ => 0 :=
    hin.mono fun n hn => hz _ hn
  exact tendsto_nhds_unique hf (tendsto_const_nhds.congr' he.symm)

/-- An interval of collisions contradicts the local SLE path's zero-volume clause. -/
theorem false_of_collision_interval {w v : ℝ≥0 → ℝ} {τ : ℝ≥0∞} {a b : ℝ≥0}
    (hab : a < b) (hb : (b : ℝ≥0∞) < τ)
    (hvol : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = v s.toNNReal} = 0)
    (he : ∀ t ∈ Ioo a b, w t = v t) : False := by
  have hsub : Ioo (a : ℝ) (b : ℝ) ⊆
      {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < τ ∧ w s.toNNReal = v s.toNNReal} := by
    intro s hs
    have hs0 : 0 ≤ s := a.property.trans hs.1.le
    have hsm : s.toNNReal ∈ Ioo a b := by
      change a < s.toNNReal ∧ s.toNNReal < b
      rw [← NNReal.coe_lt_coe, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0]
      exact hs
    exact ⟨hs0, (ENNReal.coe_lt_coe.2 hsm.2).trans hb, he _ hsm⟩
  have hz := measure_mono_null hsub hvol
  have hp : (0 : ℝ≥0∞) < volume (Ioo (a : ℝ) (b : ℝ)) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 (NNReal.coe_lt_coe.2 hab))
  exact hp.ne' hz

/-- Positive dyadic Brownian evaluations are nonzero on a single conull event. -/
theorem ae_brownian_dyadic_ne_zero {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ p, 0 < dyadicTime p → B (dyadicTime p) ω ≠ 0 := by
  apply ae_all_iff.2
  intro p
  by_cases hp : 0 < dyadicTime p
  · have : NullSingletonClass (gaussianReal 0 (dyadicTime p)) :=
      nullSingletonClass_gaussianReal hp.ne'
    have hz : P ((B (dyadicTime p)) ⁻¹' ({0} : Set ℝ)) = 0 := by
      rw [← Measure.map_apply_of_aemeasurable (hB.toIsPreBrownianReal.aemeasurable _) (measurableSet_singleton 0),
        (hB.hasLaw_eval _).map_eq, measure_singleton]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hz] with ω hω _
    exact hω
  · exact ae_of_all _ fun _ h => (hp h).elim

/-- A local SLE state has a nonzero dyadic sample in each pre-lifetime interval. -/
theorem exists_nonzero_dyadic_of_slePath
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b τ)
    (hb : ∀ p, 0 < dyadicTime p → b (dyadicTime p) ≠ 0)
    {a c : ℝ≥0} (hac : a < c) (hc : (c : ℝ≥0∞) < τ) :
    ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧
      (w (dyadicTime p), (fun i => vL i (dyadicTime p)), fun i => vR i (dyadicTime p)) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz : ∀ p, dyadicTime p ∈ Ioo a c →
      (w (dyadicTime p), (fun i => vL i (dyadicTime p)), fun i => vR i (dyadicTime p)) = 0 :=
    fun p h => hn p h.1 h.2
  have hcont := (continuousOn_state_of_isSLEPathUpTo hp).mono
    (fun (t : ℝ≥0) (ht : t ∈ Ioo a c) => (ENNReal.coe_lt_coe.2 ht.2).trans hc)
  have hzero := eq_zero_on_Ioo_of_dyadic hcont hz
  cases nL with
  | succ n =>
      apply false_of_collision_interval hac hc (hp.volume_collisionL ⟨0, Nat.zero_lt_succ n⟩)
      intro t ht
      have he := congrArg (fun x : DrivingValue (n + 1) nR => x.1 - x.2.1 ⟨0, Nat.zero_lt_succ n⟩)
        (hzero t ht)
      exact sub_eq_zero.1 (by simpa only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, sub_self] using he)
  | zero =>
      cases nR with
      | succ n =>
          apply false_of_collision_interval hac hc (hp.volume_collisionR ⟨0, Nat.zero_lt_succ n⟩)
          intro t ht
          have he := congrArg (fun x : DrivingValue 0 (n + 1) => x.1 - x.2.2 ⟨0, Nat.zero_lt_succ n⟩)
            (hzero t ht)
          exact sub_eq_zero.1 (by simpa only [Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, sub_self] using he)
      | zero =>
          obtain ⟨p, hpa, hpc⟩ := exists_dyadicTime_btwn (ENNReal.coe_lt_coe.2 hac)
          have hpt : (dyadicTime p : ℝ≥0∞) < τ := hpc.trans hc
          have hw : w (dyadicTime p) = 0 := congrArg Prod.fst (hz p ⟨ENNReal.coe_lt_coe.1 hpa, ENNReal.coe_lt_coe.1 hpc⟩)
          have he := hp.w_eq hpt
          simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, hw] at he
          exact hb p (lt_of_le_of_lt (zero_le) (ENNReal.coe_lt_coe.1 hpa))
            ((mul_eq_zero.1 he.symm).resolve_left (Real.sqrt_pos.2 hκ).ne')

/-- Through-coupling histories have nonzero samples in every strictly live interval. -/
theorem ae_nonzero_dyadic_killedHistory
    {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ V : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hC : IsCouplingThrough κ xL xR ρL ρR P 𝓕 W VL VR B ζ V h) :
    ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0 := by
  filter_upwards [hC.1.isSLEEvolutionUpTo.ae_path, ae_brownian_dyadic_ne_zero hC.1.1.1] with ω hp hb
  intro a c hac hc
  obtain ⟨p, hpa, hpc, hp0⟩ := exists_nonzero_dyadic_of_slePath hκ hp hb hac (hc.trans_le (hC.2.1 ω))
  refine ⟨p, hpa, hpc, ?_⟩
  have hpV := (ENNReal.coe_lt_coe.2 hpc).trans hc
  simpa only [killedHistory, hpV, ↓reduceIte] using hp0

end InteractingSLE.WFS

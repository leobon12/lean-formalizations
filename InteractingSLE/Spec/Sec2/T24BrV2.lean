import InteractingSLE.Spec.Sec2.T24BrRegular
import InteractingSLE.Spec.Sec2.T24BrEvolution
import InteractingSLE.Spec.Sec2.T24BrAdapted
import InteractingSLE.Spec.Sec2.T24BrImage
import InteractingSLE.Spec.Sec2.T24BrDefs

/-!
# Theorem 2.4 forward adapters for candidate v2

The image predicates and threshold below unfold to the candidate v2 formulas. They
remain scoped implementation copies until the statement audit is complete.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical

namespace InteractingSLE.Sec2.T24Bridge.V2

open MartChar Sec7.PocketTraversal

/-- The right-image relation on the candidate's valid source carrier. -/
def IsRightForceImage (w : ℝ≥0 → ℝ) (x : ℝ) (v : ℝ≥0 → ℝ) : Prop :=
  Continuous w ∧ w 0 = 0 ∧ 0 ≤ x ∧ ∀ t, v t = rightForceImage w x t

/-- The left-image relation on the candidate's valid source carrier. -/
def IsLeftForceImage (w : ℝ≥0 → ℝ) (x : ℝ) (v : ℝ≥0 → ℝ) : Prop :=
  Continuous w ∧ w 0 = 0 ∧ x ≤ 0 ∧ ∀ t, v t = leftForceImage w x t

/-- The candidate v2 continuation threshold, with the coordinate processes explicit. -/
def continuationThreshold {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : ForceWord.ThresholdCondition ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)),
    (t : ℝ≥0∞)

/-- The coordinate infimum agrees with the landed threshold time. -/
theorem continuationThreshold_eq_thresholdTime {nL nR : ℕ}
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) :
    continuationThreshold ρL ρR w vL vR = thresholdTime ρL ρR w vL vR := by
  classical
  unfold continuationThreshold thresholdTime
  split_ifs with h
  · rw [ENNReal.coe_sInf h]
    rfl
  · rw [Set.not_nonempty_iff_eq_empty] at h
    refine iInf_eq_top.2 fun t => iInf_eq_top.2 fun ht => ?_
    have hm : t ∈ thresholdSet ρL ρR w vL vR := ht
    rw [h] at hm
    exact absurd hm (Set.notMem_empty t)

/-- The certified relation supplies the stochastic right-coordinate identity. -/
theorem right_eq_geom {Ω : Type*} {nR : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {xR : Fin nR → ℝ} {ω : Ω} {j : Fin nR}
    (h : IsRightForceImage (W · ω) (xR j) (VR j · ω)) (t : ℝ≥0) :
    VR j t ω = geomRW W (fun _ => xR) j t ω :=
  (h.2.2.2 t).trans
    (right_force_image_eq_geomRW (xR := fun _ => xR) h.1 h.2.1 j h.2.2.1 t)

/-- The certified relation supplies the stochastic left-coordinate identity. -/
theorem left_eq_geom {Ω : Type*} {nL : ℕ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {xL : Fin nL → ℝ} {ω : Ω} {i : Fin nL}
    (h : IsLeftForceImage (W · ω) (xL i) (VL i · ω)) (t : ℝ≥0) :
    VL i t ω = geomLW W (fun _ => xL) i t ω :=
  (h.2.2.2 t).trans
    (left_force_image_eq_geomLW (xL := fun _ => xL) h.1 h.2.1 i h.2.2.1 t)

/-- The v2 local-martingale predicate is vacuous on an empty live interval. -/
theorem isContLocalMartingaleBeforeV2_zero {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : ℝ≥0 → Ω → ℝ) :
    IsContLocalMartingaleBeforeV2 𝓕 P (fun _ => 0) X := by
  refine ⟨Eventually.of_forall fun ω => ?_, (fun _ _ => 0),
    fun _ => isStoppingTime_const 𝓕 0, fun _ _ => Or.inl rfl,
    Eventually.of_forall fun ω r hr => (not_lt_of_ge (zero_le : (0 : WithTop ℝ≥0) ≤ r) hr).elim,
    fun n => ?_⟩
  · have he : {t : ℝ≥0 | (t : WithTop ℝ≥0) < 0} = ∅ := by
      ext t
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
      exact zero_le
    rw [he]
    exact continuousOn_empty _
  · convert (martingale_zero ℝ 𝓕 P : Martingale (0 : ℝ≥0 → Ω → ℝ) 𝓕 P) using 1
    funext t ω
    simp [stoppedProcess, Set.indicator]

end InteractingSLE.Sec2.T24Bridge.V2

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2Root2Chart

/-!
# Record dependence of GW2's repaired relative capacity

Packet PROVE-T14-GW2ROOT2. Equality of the complete stopped stage records
determines the prefix image and every capacity used in its running maximum.
This verifies the deterministic part of the regularized-driver repair.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord)
  (c₀ : BoundaryWord) {Ω : Type u}
  (h : Ω → DistOn upperHalfPlaneOpens)

/-- Appending a switch leaves every earlier prescribed stopped record unchanged. -/
theorem stopRec_schedSpec_append (x : ℝ) {l : List (ℝ × ℝ≥0)}
    (y : ℝ × ℝ≥0) {j : ℕ} (hj : j < l.length) (ω : Ω) :
    stopRec hκ h12p βA c₀ h (schedSpec x (l ++ [y])) j ω =
      stopRec hκ h12p βA c₀ h (schedSpec x l) j ω := by
  exact canonRec_congr₂ hκ h12p βA c₀ x (h ω)
    (fun i hi => specAngle_schedSpec_append x y (lt_of_le_of_lt hi hj))
    (fun i hi => specDelta_schedSpec_append x y (lt_of_le_of_lt hi hj))

/-- Equal complete records of an extended schedule give equal earlier records. -/
theorem stageMap_eq_of_append_eq (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (x : ℝ) (l : List (ℝ × ℝ≥0)) (y : ℝ × ℝ≥0)
    {ω ω' : Ω}
    (hs : stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x (l ++ [y]))
        (l ++ [y]).length ω =
      stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x (l ++ [y]))
        (l ++ [y]).length ω') :
    stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x l) l.length ω =
      stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x l) l.length ω' := by
  apply Prod.ext
  · change cfRec s W' ζ' ω = cfRec s W' ζ' ω'
    exact congrArg Prod.fst hs
  · funext j
    have hj : j.val < (l ++ [y]).length := by
      rw [List.length_append, List.length_singleton]
      exact Nat.lt_succ_of_lt j.isLt
    have hrec := congrFun (congrArg Prod.snd hs) ⟨j.val, hj⟩
    change stopRec hκ h12p βA c₀ h (schedSpec x (l ++ [y])) j ω =
      stopRec hκ h12p βA c₀ h (schedSpec x (l ++ [y])) j ω' at hrec
    rw [stopRec_schedSpec_append hκ h12p βA c₀ h x y j.isLt ω,
      stopRec_schedSpec_append hκ h12p βA c₀ h x y j.isLt ω'] at hrec
    exact hrec

variable (b : ℝ → ℝ) (jumps : Finset ℝ)

/-- The prefix image in the regularized joint chart is constant on stage-record
fibres. This includes exceptional samples and stopped schedules. -/
theorem prefixImage_regW_eq_of_stageMap_eq (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (x : ℝ) (l : List (ℝ × ℝ≥0)) {ω ω' : Ω}
    (hs : stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x l) l.length ω =
      stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x l) l.length ω') :
    prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s x l ω =
      prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ') s x l ω' := by
  have hp := prefixSet_eq_of_stopRec_eq hκ h12p βA b jumps c₀ h x l
    (fun j hj => congrFun (congrArg Prod.snd hs) ⟨j, hj⟩)
  have hc : EqOn (fun r : ℝ => regW s W' ζ' r.toNNReal ω)
        (fun r : ℝ => regW s W' ζ' r.toNNReal ω') (Icc 0 (s : ℝ)) ∧
      QuantumZipper.fwdHull (fun r : ℝ => regW s W' ζ' r.toNNReal ω) s =
        QuantumZipper.fwdHull (fun r : ℝ => regW s W' ζ' r.toNNReal ω') s :=
    driver_hull_eq_of_recOf_eq
    (StagedReg.isRegularDriver_regularize _ _)
    (StagedReg.isRegularDriver_regularize _ _) (congrArg Prod.fst hs)
  have hm : (GW2JointKernel.jointChart
        (fun r : ℝ => regW s W' ζ' r.toNNReal ω) s).1 =
      (GW2JointKernel.jointChart
        (fun r : ℝ => regW s W' ζ' r.toNNReal ω') s).1 := by
    funext z
    rw [GW2JointKernel.jointChart_fst, GW2JointKernel.jointChart_fst]
    unfold Supp8.GB6.relMap
    rw [Ito.fwdMap_congr_of_eqOn hc.1]
  unfold prefixImage
  rw [hp, hm, hc.2]

/-- The capacity of one admissible prefix image is determined by its stage record. -/
theorem capV_regW_eq_of_stageMap_eq (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (Θ : Set ℝ) (Q : Set ℝ≥0) (x : ℝ)
    (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) {ω ω' : Ω}
    (hs : stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x (schedOf e₀ xs))
        (xs.length + 1) ω =
      stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x (schedOf e₀ xs))
        (xs.length + 1) ω') :
    capV hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q x e₀ xs ω =
      capV hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q x e₀ xs ω' := by
  have hp : prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ')
        s x (schedOf e₀ xs) ω =
      prefixImage hκ h12p βA b jumps c₀ h (regW s W' ζ')
        s x (schedOf e₀ xs) ω' := by
    apply prefixImage_regW_eq_of_stageMap_eq
    exact (length_schedOf e₀ xs).symm ▸ hs
  unfold capV
  rw [hp]

/-- The running maximum of prefix capacities is also determined by the complete
stopped stage record; equal records of shorter schedules follow by truncation. -/
theorem schedCap_regW_eq_of_stageMap_eq (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (Θ : Set ℝ) (Q : Set ℝ≥0) (x : ℝ)
    (e₀ : ℝ × ℝ≥0) (xs : List (ℝ × ℝ≥0)) {ω ω' : Ω} :
    stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x (schedOf e₀ xs))
        (xs.length + 1) ω =
      stageMap hκ h12p βA c₀ h s W' ζ' (schedSpec x (schedOf e₀ xs))
        (xs.length + 1) ω' →
    schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q x e₀ xs ω =
      schedCap hκ h12p βA b jumps c₀ h (regW s W' ζ') s Θ Q x e₀ xs ω' := by
  induction xs with
  | nil =>
    intro hs
    exact capV_regW_eq_of_stageMap_eq hκ h12p βA c₀ h b jumps s W' ζ' Θ Q x e₀ [] hs
  | cons y xs ih =>
    intro hs
    have hs' : stageMap hκ h12p βA c₀ h s W' ζ'
          (schedSpec x (schedOf e₀ xs ++ [y])) (schedOf e₀ xs ++ [y]).length ω =
        stageMap hκ h12p βA c₀ h s W' ζ'
          (schedSpec x (schedOf e₀ xs ++ [y])) (schedOf e₀ xs ++ [y]).length ω' := by
      rw [schedOf_cons] at hs
      have hl : (y :: xs).length + 1 = (schedOf e₀ xs ++ [y]).length := by
        rw [List.length_append, List.length_singleton, length_schedOf, List.length_cons]
      exact hl ▸ hs
    have hprev := stageMap_eq_of_append_eq hκ h12p βA c₀ h s W' ζ'
      x (schedOf e₀ xs) y hs'
    have hcap := ih (length_schedOf e₀ xs ▸ hprev)
    change max _ _ = max _ _
    rw [hcap, capV_regW_eq_of_stageMap_eq hκ h12p βA c₀ h b jumps
      s W' ζ' Θ Q x e₀ (y :: xs) hs]

/-- The repaired scaled capacity `capR` is exactly constant on the fibres of
the map generating `rootSigma`. No almost-sure regularity assumption is used. -/
theorem capR_eq_of_stageMap_eq (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) {Θ : Set ℝ} {Q : Set ℝ≥0}
    (r : ScaledRootIdx Θ Q) (l : List (EntryIdx Θ Q)) {ω ω' : Ω}
    (hs : stageMap hκ h12p βA c₀ h s W' ζ' (schedSpecOf r.1 l)
        ((entryList l).length + 1) ω =
      stageMap hκ h12p βA c₀ h s W' ζ' (schedSpecOf r.1 l)
        ((entryList l).length + 1) ω') :
    capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω =
      capR hκ h12p βA b jumps c₀ h W' ζ' s r l ω' := by
  exact congrArg (fun a : ℝ => 4 ^ r.2 * a)
    (schedCap_regW_eq_of_stageMap_eq hκ h12p βA c₀ h b jumps s W' ζ'
      Θ Q (rootPt r.1) (rootEntry r.1) (entryList l) hs)

/-- Measurability of the repaired capacity in the retained stage record is
equivalent to its ambient measurability. The substantive capacity-measurability
question is thus separated from the already proved record dependence. -/
theorem measurable_capR_iff [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (hβA : Measurable βA) (hh : Measurable h) {P : Measure Ω}
    (s : ℝ≥0) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    {Θ : Set ℝ} {Q : Set ℝ≥0} (r : ScaledRootIdx Θ Q)
    (l : List (EntryIdx Θ Q)) :
    Measurable[rootSigma hκ h12p βA c₀ h W' ζ' s r l]
        (capR hκ h12p βA b jumps c₀ h W' ζ' s r l) ↔
      Measurable (capR hκ h12p βA b jumps c₀ h W' ζ' s r l) := by
  have hle : rootSigma hκ h12p βA c₀ h W' ζ' s r l ≤ mΩ :=
    stageSigma_le hβA hh hcf s _ _
  constructor
  · intro hc
    exact hc.mono hle le_rfl
  · intro hc
    have hm : Measurable (stageMap hκ h12p βA c₀ h s W' ζ'
        (schedSpecOf r.1 l) ((entryList l).length + 1)) :=
      Measurable.of_comap_le hle
    exact measurable_comap_of_saturated hm hc
      (fun _ _ hs => capR_eq_of_stageMap_eq hκ h12p βA c₀ h b jumps s W' ζ' r l hs)

end InteractingSLE.Theorem14.GW2TipSystem

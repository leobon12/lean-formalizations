/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdoLaunch
import InteractingSLE.Spec.Supplement.SB2VrBad
import InteractingSLE.Spec.Supplement.SB2WfNoThr

/-!
# GW2's `noThreshold`, route (M): the threshold transfers through a dilation at the level of data

Packet PROVE-GW2-NOTHR (round 2, decision D38). SDE's `GW2Sdo.not_threshold_stage_of_launch` transfers the
continuation threshold from a launch chart to a stage chart when the launch WORD is the dilated stage word. The
stage-start identity of PROVE-GW2-STAGEMEAN identifies the two words only through their boundary DATA, off a finite
set. A threshold only reads the data: the right marks that collide with the driver at time `u` are exactly the marks up
to some point (the collided set `{x | rightImg D x u = D u}` is down-closed), and their weight sum is the cumulative
weight there, which is `cumWeightRight` of the right limit of the data (`SB.Vr.cumWeightRight_rightLim_flowLine`).

* `sum_downClosed_eq` (combinatorial core): sums over the marks in a down-closed set agree for two mark families whose
  cumulative sums agree through a dilation `y ↦ λ y` off a finite set;
* **`rightSum_eq_of_dil`**, **`leftSum_eq_of_dil`**: the collided right (left) weight sums of two flow-line words
  whose data agree through the dilation, along `D` at `u` and along `WL = scD λ D` at `λ² u`;
* **`thresholdCondition_iff_of_dil`**: the continuation thresholds agree;
* **`not_threshold_of_dil`**: the data-level form of `GW2Sdo.not_threshold_stage_of_launch`.

Deterministic; no named input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset Filter Topology

namespace InteractingSLE.Theorem14.GW2Nt

open MartChar.RealFlow Sec5.CrossCond.StagedRepLater
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-! ### The combinatorial core -/

open Classical in
/-- **Sums over a down-closed set through a dilation.** If the cumulative sums of two nonnegative mark families agree
through `y ↦ λ y` at every `y > 0` off a finite set, then their sums over the marks lying in a down-closed set `C`
(the second family read through `x ↦ x / λ`) agree. -/
theorem sum_downClosed_eq {C : Set ℝ} (hC : ∀ x x' : ℝ, x ≤ x' → x' ∈ C → x ∈ C) {lam : ℝ} (hlam : 0 < lam)
    {n₁ n₂ : ℕ} {x₁ ρ₁ : Fin n₁ → ℝ} {x₂ ρ₂ : Fin n₂ → ℝ} (hx₁ : ∀ i, 0 ≤ x₁ i) (hx₂ : ∀ j, 0 ≤ x₂ j)
    {G : Set ℝ} (hG : G.Finite)
    (hcum : ∀ y : ℝ, 0 < y → y ∉ G →
      ∑ j ∈ univ.filter (fun j => x₂ j ≤ y), ρ₂ j = ∑ i ∈ univ.filter (fun i => x₁ i ≤ lam * y), ρ₁ i) :
    ∑ j ∈ univ.filter (fun j => x₂ j ∈ C), ρ₂ j = ∑ i ∈ univ.filter (fun i => x₁ i / lam ∈ C), ρ₁ i := by
  set T : Finset ℝ := ((univ.filter fun j => x₂ j ∈ C).image x₂) ∪
    ((univ.filter fun i => x₁ i / lam ∈ C).image fun i => x₁ i / lam) with hT
  by_cases hTne : T.Nonempty
  · set y := T.max' hTne with hy
    have hyT : y ∈ T := T.max'_mem hTne
    have hyC : y ∈ C := by
      rcases Finset.mem_union.1 hyT with h | h
      · obtain ⟨j, hj, hjy⟩ := Finset.mem_image.1 h
        rw [← hjy]
        exact (Finset.mem_filter.1 hj).2
      · obtain ⟨i, hi, hiy⟩ := Finset.mem_image.1 h
        rw [← hiy]
        exact (Finset.mem_filter.1 hi).2
    have hy0 : 0 ≤ y := by
      rcases Finset.mem_union.1 hyT with h | h
      · obtain ⟨j, -, hjy⟩ := Finset.mem_image.1 h
        rw [← hjy]
        exact hx₂ j
      · obtain ⟨i, -, hiy⟩ := Finset.mem_image.1 h
        rw [← hiy]
        exact div_nonneg (hx₁ i) hlam.le
    have hf₂ : univ.filter (fun j => x₂ j ∈ C) = univ.filter (fun j => x₂ j ≤ y) := by
      refine Finset.filter_congr fun j _ => ⟨fun h => T.le_max' _ ?_, fun h => hC _ _ h hyC⟩
      exact Finset.mem_union_left _ (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩)
    have hf₁ : univ.filter (fun i => x₁ i / lam ∈ C) = univ.filter (fun i => x₁ i ≤ lam * y) := by
      refine Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => hC _ _ ?_ hyC⟩
      · have hle : x₁ i / lam ≤ y := T.le_max' _
          (Finset.mem_union_right _ (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩))
        rw [div_le_iff₀ hlam] at hle
        linarith
      · rw [div_le_iff₀ hlam]
        linarith
    obtain ⟨a₂, ha₂, hg₂⟩ := SB.Wf.exists_gap_right x₂ y
    obtain ⟨a₁, ha₁, hg₁⟩ := SB.Wf.exists_gap_right (fun i => x₁ i / lam) y
    obtain ⟨y', ⟨hy'1, hy'2⟩, hy'G⟩ := ((Set.Ioo_infinite (lt_min ha₁ ha₂)).sdiff hG).nonempty
    have hs₂ : univ.filter (fun j => x₂ j ≤ y) = univ.filter (fun j => x₂ j ≤ y') := by
      refine Finset.filter_congr fun j _ => ⟨fun h => h.trans hy'1.le, fun h => ?_⟩
      by_contra hn
      exact hg₂ j ⟨lt_of_not_ge hn, lt_of_le_of_lt h (lt_of_lt_of_le hy'2 (min_le_right _ _))⟩
    have hs₁ : univ.filter (fun i => x₁ i ≤ lam * y) = univ.filter (fun i => x₁ i ≤ lam * y') := by
      refine Finset.filter_congr fun i _ =>
        ⟨fun h => h.trans (mul_le_mul_of_nonneg_left hy'1.le hlam.le), fun h => ?_⟩
      by_contra hn
      have h1 : y < x₁ i / lam := by
        rw [lt_div_iff₀ hlam]
        linarith [lt_of_not_ge hn]
      have h2 : x₁ i / lam ≤ y' := by
        rw [div_le_iff₀ hlam]
        linarith
      exact hg₁ i ⟨h1, lt_of_le_of_lt h2 (lt_of_lt_of_le hy'2 (min_le_left _ _))⟩
    rw [hf₂, hf₁, hs₂, hs₁]
    exact hcum y' (lt_of_le_of_lt hy0 hy'1) hy'G
  · have hT0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.1 hTne
    obtain ⟨h2, h1⟩ := Finset.union_eq_empty.1 hT0
    rw [Finset.image_eq_empty.1 h2, Finset.image_eq_empty.1 h1, Finset.sum_empty, Finset.sum_empty]

/-! ### The collided set and the dilation -/

/-- The collided set of a driver at a time is down-closed. -/
theorem rightImg_eq_of_le {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) {x x' : ℝ} (hxx : x ≤ x')
    (h : rightImg w x' t = w t) : rightImg w x t = w t :=
  le_antisymm ((rightImg_mono_index hw ht hxx).trans h.le) (le_rightImg hw x ht)

/-- **Collisions along the dilated driver** are the dilated collisions. -/
theorem rightImg_dil_iff {D WL : ℝ → ℝ} (hD : Continuous D) {lam : ℝ} (hlam : 0 < lam) {u : ℝ} (hu : 0 ≤ u)
    (hW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), WL v = scD lam D v) (x : ℝ) :
    rightImg WL x (lam ^ 2 * u) = WL (lam ^ 2 * u) ↔ rightImg D (x / lam) u = D u := by
  have ht : 0 ≤ lam ^ 2 * u := mul_nonneg (sq_nonneg _) hu
  have hsc := continuous_scD hD lam
  have hWt : WL (lam ^ 2 * u) = lam * D u := by
    rw [hW _ ⟨ht, le_rfl⟩]
    simp only [scD]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero 2 hlam.ne')]
  have hR : rightImg WL x (lam ^ 2 * u) = lam * rightImg D (x / lam) u := by
    rw [Supp8.GB6.rightImg_congr hsc ht hW, ← rightImg_scale hD hlam (x / lam) hu,
      mul_div_cancel₀ x hlam.ne']
  rw [hR, hWt]
  exact ⟨fun h => mul_left_cancel₀ hlam.ne' h, fun h => by rw [h]⟩

/-! ### The collided sums of two flow-line words through a dilation -/

section Sums

variable {κ : ℝ} (hκ : 0 < κ) {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ}
  (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁) (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) {θ₁ θ₂ lam : ℝ}
  (hlam : 0 < lam) {F : Set ℝ} (hF : F.Finite)
  (hdata : ∀ y, y ∉ F → b₂ y + θ₂ * QuantumZipper.chiC κ = b₁ (lam * y) + θ₁ * QuantumZipper.chiC κ)
  {D WL : ℝ → ℝ} (hD : Continuous D) {u : ℝ} (hu : 0 ≤ u)
  (hW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), WL v = scD lam D v)

include hκ hb₁ hb₂ hlam hF hdata hD hu hW

open Classical in
/-- **The collided right weight sums agree** for two flow-line words whose data agree through the dilation. -/
theorem rightSum_eq_of_dil :
    ∑ j ∈ Finset.univ.filter (fun j => rightImg D (flowLineXR b₂ J₂ 0 j) u = D u), flowLineRhoR κ b₂ J₂ 0 θ₂ j =
      ∑ i ∈ Finset.univ.filter (fun i => rightImg WL (flowLineXR b₁ J₁ 0 i) (lam ^ 2 * u) = WL (lam ^ 2 * u)),
        flowLineRhoR κ b₁ J₁ 0 θ₁ i := by
  set C : Set ℝ := {x | rightImg D x u = D u} with hCdef
  have hC : ∀ x x' : ℝ, x ≤ x' → x' ∈ C → x ∈ C := fun x x' hxx h => rightImg_eq_of_le hD hu hxx h
  have h1 : Finset.univ.filter (fun i => rightImg WL (flowLineXR b₁ J₁ 0 i) (lam ^ 2 * u) = WL (lam ^ 2 * u)) =
      Finset.univ.filter (fun i => flowLineXR b₁ J₁ 0 i / lam ∈ C) :=
    Finset.filter_congr fun i _ => rightImg_dil_iff hD hlam hu hW _
  rw [h1]
  set G : Set ℝ := F ∪ (↑J₂ : Set ℝ) ∪ (fun y => lam * y) ⁻¹' (↑J₁ : Set ℝ) with hG
  have hGf : G.Finite := (hF.union J₂.finite_toSet).union
    (J₁.finite_toSet.preimage (mul_right_injective₀ hlam.ne').injOn)
  refine sum_downClosed_eq hC hlam (Restart.FlowStopIdentCMI.flowLineXR_nonneg' b₁ J₁ 0)
    (Restart.FlowStopIdentCMI.flowLineXR_nonneg' b₂ J₂ 0) hGf fun y hy hyG => ?_
  have hyF : y ∉ F := fun h => hyG (Or.inl (Or.inl h))
  have hyJ₂ : y ∉ J₂ := fun h => hyG (Or.inl (Or.inr (Finset.mem_coe.2 h)))
  have hyJ₁ : lam * y ∉ J₁ := fun h => hyG (Or.inr (Finset.mem_coe.2 h))
  have e2 := SB.Vr.cumWeightRight_rightLim_flowLine hκ hb₂ 0 θ₂ hy
  have e1 := SB.Vr.cumWeightRight_rightLim_flowLine hκ hb₁ 0 θ₁ (mul_pos hlam hy)
  rw [add_zero, Exist.StagedLaw.rightLim_eq_of_notMem hb₂ hyJ₂] at e2
  rw [add_zero, Exist.StagedLaw.rightLim_eq_of_notMem hb₁ hyJ₁] at e1
  change SB.Vq.wR _ _ y = SB.Vq.wR _ _ (lam * y)
  rw [← e2, ← e1, hdata y hyF]

open Classical in
/-- **The collided left weight sums agree** for two flow-line words whose data agree through the dilation. -/
theorem leftSum_eq_of_dil :
    ∑ i ∈ Finset.univ.filter (fun i => -rightImg (fun v => -D v) (-flowLineXL b₂ J₂ 0 i) u = D u),
        flowLineRhoL κ b₂ J₂ 0 θ₂ i =
      ∑ i ∈ Finset.univ.filter (fun i => -rightImg (fun v => -WL v) (-flowLineXL b₁ J₁ 0 i) (lam ^ 2 * u) =
        WL (lam ^ 2 * u)), flowLineRhoL κ b₁ J₁ 0 θ₁ i := by
  set D' : ℝ → ℝ := fun v => -D v with hD'
  have hD'c : Continuous D' := hD.neg
  have hW' : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), (fun v => -WL v) v = scD lam D' v := fun v hv => by
    simp only [hD', scD, hW v hv]
    ring
  set C : Set ℝ := {x | rightImg D' x u = D' u} with hCdef
  have hC : ∀ x x' : ℝ, x ≤ x' → x' ∈ C → x ∈ C := fun x x' hxx h => rightImg_eq_of_le hD'c hu hxx h
  have h2 : Finset.univ.filter (fun i => -rightImg (fun v => -D v) (-flowLineXL b₂ J₂ 0 i) u = D u) =
      Finset.univ.filter (fun i => -flowLineXL b₂ J₂ 0 i ∈ C) :=
    Finset.filter_congr fun i _ => by
      simp only [hCdef, Set.mem_ofPred_eq, hD']
      constructor <;> intro h <;> linarith
  have h1 : Finset.univ.filter (fun i => -rightImg (fun v => -WL v) (-flowLineXL b₁ J₁ 0 i) (lam ^ 2 * u) =
      WL (lam ^ 2 * u)) = Finset.univ.filter (fun i => -flowLineXL b₁ J₁ 0 i / lam ∈ C) :=
    Finset.filter_congr fun i _ => by
      have e := rightImg_dil_iff hD'c hlam hu hW' (-flowLineXL b₁ J₁ 0 i)
      change _ ↔ rightImg D' (-flowLineXL b₁ J₁ 0 i / lam) u = D' u
      rw [← e]
      constructor <;> intro h <;> linarith
  rw [h1, h2]
  set G : Set ℝ := (fun y => -y) ⁻¹' F ∪ (fun y => -y) ⁻¹' (↑J₂ : Set ℝ) ∪
    (fun y => -(lam * y)) ⁻¹' (↑J₁ : Set ℝ) with hG
  have hinj : Function.Injective fun y : ℝ => -(lam * y) :=
    neg_injective.comp (mul_right_injective₀ hlam.ne')
  have hGf : G.Finite := ((hF.preimage neg_injective.injOn).union
    (J₂.finite_toSet.preimage neg_injective.injOn)).union (J₁.finite_toSet.preimage hinj.injOn)
  refine sum_downClosed_eq (x₁ := fun i => -flowLineXL b₁ J₁ 0 i) (x₂ := fun i => -flowLineXL b₂ J₂ 0 i) hC hlam
    (fun i => neg_nonneg.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' b₁ J₁ 0 i))
    (fun i => neg_nonneg.2 (Restart.FlowStopIdentCMI.flowLineXL_nonpos' b₂ J₂ 0 i)) hGf fun y hy hyG => ?_
  have hyF : -y ∉ F := fun h => hyG (Or.inl (Or.inl h))
  have hyJ₂ : -y ∉ J₂ := fun h => hyG (Or.inl (Or.inr (Finset.mem_coe.2 h)))
  have hyJ₁ : -(lam * y) ∉ J₁ := fun h => hyG (Or.inr (Finset.mem_coe.2 h))
  have e2 := SB.Vr.cumWeightLeft_leftLim_flowLine hκ hb₂ 0 θ₂ (neg_neg_of_pos hy)
  have e1 := SB.Vr.cumWeightLeft_leftLim_flowLine hκ hb₁ 0 θ₁ (neg_neg_of_pos (mul_pos hlam hy))
  rw [add_zero, Exist.StagedLaw.leftLim_eq_of_notMem hb₂ hyJ₂] at e2
  rw [add_zero, Exist.StagedLaw.leftLim_eq_of_notMem hb₁ hyJ₁] at e1
  have f2 : Finset.univ.filter (fun i => -flowLineXL b₂ J₂ 0 i ≤ y) =
      Finset.univ.filter (fun i => -y ≤ flowLineXL b₂ J₂ 0 i) := Finset.filter_congr fun i _ => neg_le
  have f1 : Finset.univ.filter (fun i => -flowLineXL b₁ J₁ 0 i ≤ lam * y) =
      Finset.univ.filter (fun i => -(lam * y) ≤ flowLineXL b₁ J₁ 0 i) := Finset.filter_congr fun i _ => neg_le
  rw [f2, f1]
  change SB.Vq.wL _ _ (-y) = SB.Vq.wL _ _ (-(lam * y))
  rw [← e2, ← e1, hdata (-y) hyF, mul_neg]

/-- **The continuation thresholds agree** for two flow-line words whose data agree through the dilation, along `D`
at `u` and along `WL = scD λ D` at `λ² u`. -/
theorem thresholdCondition_iff_of_dil :
    ForceWord.ThresholdCondition (flowLineRhoL κ b₂ J₂ 0 θ₂) (flowLineRhoR κ b₂ J₂ 0 θ₂) (D u)
        (fun i => -rightImg (fun v => -D v) (-flowLineXL b₂ J₂ 0 i) u)
        (fun j => rightImg D (flowLineXR b₂ J₂ 0 j) u) ↔
      ForceWord.ThresholdCondition (flowLineRhoL κ b₁ J₁ 0 θ₁) (flowLineRhoR κ b₁ J₁ 0 θ₁) (WL (lam ^ 2 * u))
        (fun i => -rightImg (fun v => -WL v) (-flowLineXL b₁ J₁ 0 i) (lam ^ 2 * u))
        (fun j => rightImg WL (flowLineXR b₁ J₁ 0 j) (lam ^ 2 * u)) := by
  classical
  unfold ForceWord.ThresholdCondition
  rw [leftSum_eq_of_dil hκ hb₁ hb₂ hlam hF hdata hD hu hW, rightSum_eq_of_dil hκ hb₁ hb₂ hlam hF hdata hD hu hW]

end Sums

/-- **No threshold transfers from the dilated chart, at the level of data** (the data-level form of
`GW2Sdo.not_threshold_stage_of_launch`): words `c₁` (angle `θ₁`, along `WL = scD λ D` at `λ² u`) and `c₂` (angle
`θ₂`, along `D` at `u`) with `c₂(y) + θ₂χ = c₁(λ y) + θ₁χ` off a finite set. -/
theorem not_threshold_of_dil {κ : ℝ} (hκ : 0 < κ) {c₁ c₂ : Restart.BoundaryWord} {θ₁ θ₂ lam : ℝ} (hlam : 0 < lam)
    {F : Set ℝ} (hF : F.Finite)
    (hdata : ∀ y, y ∉ F → c₂.fn y + θ₂ * QuantumZipper.chiC κ = c₁.fn (lam * y) + θ₁ * QuantumZipper.chiC κ)
    {D WL : ℝ → ℝ} (hD : Continuous D) {u : ℝ} (hu : 0 ≤ u)
    (hW : ∀ v ∈ Icc (0 : ℝ) (lam ^ 2 * u), WL v = scD lam D v)
    (hn : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c₁.fn c₁.jumps 0 θ₁) (flowLineRhoR κ c₁.fn c₁.jumps 0 θ₁)
      (WL (lam ^ 2 * u)) (fun i => -rightImg (fun v => -WL v) (-flowLineXL c₁.fn c₁.jumps 0 i) (lam ^ 2 * u))
      (fun j => rightImg WL (flowLineXR c₁.fn c₁.jumps 0 j) (lam ^ 2 * u))) :
    ¬ ForceWord.ThresholdCondition (flowLineRhoL κ c₂.fn c₂.jumps 0 θ₂) (flowLineRhoR κ c₂.fn c₂.jumps 0 θ₂) (D u)
      (fun i => -rightImg (fun v => -D v) (-flowLineXL c₂.fn c₂.jumps 0 i) u)
      (fun j => rightImg D (flowLineXR c₂.fn c₂.jumps 0 j) u) :=
  fun h => hn ((thresholdCondition_iff_of_dil hκ c₁.isPiecewiseConstantBoundaryData
    c₂.isPiecewiseConstantBoundaryData hlam hF hdata hD hu hW).1 h)

end InteractingSLE.Theorem14.GW2Nt

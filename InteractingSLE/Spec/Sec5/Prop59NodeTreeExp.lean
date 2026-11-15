/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeActive
import InteractingSLE.Spec.Sec5.Prop59NodeTreeWord

/-!
# The ingredients of a node experiment: dilation, bounded images, far gaps

Packet PROVE-PROP59-NODETREE.

* `nodeLam`: the dilation `3 / min(−m_L, m_R)` from the far marks at the node tip (`1` if a far gap fails);
  `nodeLam_mul_le`;
* **`isBounded_nodeImage`**: the joint-chart images of the node points are bounded when Proposition 5.13's node target
  is (the prefix points form a compact arc on the event that the node prefix is pre-contact; the descendant points are
  in the target, PROVE-PROP59-PIECES' `revChart_eq_ownComponentChart`);
* `isSpine_nodeData`: the node prefix is a spine of the node tree (`Prop59NodeTreeMarks`);
* **`ae_farGaps_nodeData`**: almost surely, if the node prefix is pre-contact at a positive time `r`, both far gaps at
  the node tip are strictly positive (the root junction gaps, `ae_cfHistory_mem_goodSet49`, transported along the
  simple image arc, `TreeData.farGaps_spine`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu WangWu.ImgWord LawUnique Prop59System Prop59Stage
open Prop59Pieces
open Sec7.Lemma71C (capClock)

/-! ### The dilation -/

open scoped Classical in
/-- **The dilation of a node experiment**: `3 / min(−m_L, m_R)` for far marks `m_L < 0 < m_R`, `1` otherwise. -/
def nodeLam (mL mR : ℝ) : ℝ := if 0 < -mL ∧ 0 < mR then 3 / min (-mL) mR else 1

theorem nodeLam_pos (mL mR : ℝ) : 0 < nodeLam mL mR := by
  classical
  unfold nodeLam
  split_ifs with hj
  · exact div_pos (by norm_num) (lt_min hj.1 hj.2)
  · exact one_pos

theorem measurable_nodeLam {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable fun x => nodeLam (f x) (g x) := by
  classical
  refine Measurable.ite ?_ (measurable_const.div (hf.neg.min hg)) measurable_const
  exact (measurableSet_lt measurable_const hf.neg).inter (measurableSet_lt measurable_const hg)

/-- **The dilated far marks are beyond `∓3`.** -/
theorem nodeLam_mul_le {mL mR : ℝ} (hL : mL < 0) (hR : 0 < mR) :
    nodeLam mL mR * mL ≤ -3 ∧ 3 ≤ nodeLam mL mR * mR := by
  classical
  have hjL : 0 < -mL := neg_pos.2 hL
  simp only [nodeLam, hjL, hR, and_self, ↓reduceIte]
  set μ := min (-mL) mR
  have hμ : 0 < μ := lt_min hjL hR
  have hμL : μ ≤ -mL := min_le_left _ _
  have hμR : μ ≤ mR := min_le_right _ _
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ hμ]
    nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
    nlinarith

/-! ### The node tree as a spine, bounded images, far gaps -/

section Node

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} {E : Schedule → ℕ → Ω → Driver} {s : Schedule}
  {nL₀ nR₀ : ℕ} {r : ℝ≥0} {xL0 : Ω → Fin nL₀ → ℝ} {xR0 : Ω → Fin nR₀ → ℝ}
  {noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ}

/-- The last switch of a node-admissible list of length at most the node length is not after the node's. -/
theorem qLast_le_of_nodeValid {k : ℕ} {t : Fin k → ℝ≥0} (hk : k ≤ nodeLen s) (hv : NodeValid s k t) :
    qLast k t ≤ qLast (nodeLen s) (nodePre s) := by
  rw [← lastO_eq hv.1, ← lastO_eq isValid_nodePre]
  cases k with
  | zero => exact_mod_cast lastO_nonneg isValid_nodePre
  | succ k =>
    have e : t (Fin.last k) = nodePre s ⟨k, by omega⟩ := hv.2 (Fin.last k) (by simp only [Fin.val_last]; omega)
    have h1 := oTime_le_lastO (isValid_nodePre (s := s)) ⟨k, by omega⟩
    show ((oTime (t (Fin.last k)) : ℚ) : ℝ) ≤ _
    rw [e]
    exact_mod_cast h1

theorem nodeData_Gc_eq {k : ℕ} {t : Fin k → ℝ≥0} (hv : NodeValid s k t) :
    (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).Gc k t =
      (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).Gc (nodeLen s) (nodePre s) := by
  ext ω
  exact ⟨fun h' => ⟨nodeValid_nodePre, h'.2⟩, fun h' => ⟨hv, h'.2⟩⟩

/-- **The node prefix is a spine of the node tree** (all its prefixes share the node path). -/
theorem isSpine_nodeData {ω : Ω}
    (hA : ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).alive (nodeLen s) (nodePre s)) :
    IsSpine (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise) (nodeLen s) (nodePre s) ω where
  valid := nodeValid_nodePre
  alive := hA
  img k t hk hv := by
    have e1 := nodeData_Gc_eq x₀ h44 hκ hκ4 hb (P := P) (h := h) (W := W) (ζ := ζ) (r := r) (xL0 := xL0) (xR0 := xR0)
      (noise := noise) hv
    have e2 : (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).α k t =
        (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).α (nodeLen s) (nodePre s) := by
      show nodeAlpha x₀ h44 hκ hκ4 hb h s k t = nodeAlpha x₀ h44 hκ hκ4 hb h s (nodeLen s) (nodePre s)
      rw [nodeAlpha_of_le _ _ _ _ _ hk, nodeAlpha_of_le _ _ _ _ _ le_rfl]
    simp only [TreeData.img, e1, e2]
  pre k t hk hv := by
    have e1 := nodeData_Gc_eq x₀ h44 hκ hκ4 hb (P := P) (h := h) (W := W) (ζ := ζ) (r := r) (xL0 := xL0) (xR0 := xR0)
      (noise := noise) hv
    have e2 : (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).α k t =
        (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).α (nodeLen s) (nodePre s) := by
      show nodeAlpha x₀ h44 hκ hκ4 hb h s k t = nodeAlpha x₀ h44 hκ hκ4 hb h s (nodeLen s) (nodePre s)
      rw [nodeAlpha_of_le _ _ _ _ _ hk, nodeAlpha_of_le _ _ _ _ _ le_rfl]
    simp only [TreeData.pre, e1, e2]
  qle k t hk hv := qLast_le_of_nodeValid hk hv

omit mΩ in
/-- The root far marks of the counterflow chart are on their sides on histories with strict junction gaps. -/
theorem rootXL_farL_neg {y : HistorySpace 0 0} (hy : y ∈ goodSet49 r) :
    rootXL hκ hb x₀ r y (farL (rootNL_pos _)) < 0 ∧ 0 < rootXR hκ hb x₀ r y (farR (rootNR_pos _)) := by
  obtain ⟨-, hgL, hgR⟩ := hy
  rw [farL_rootNL, rootXL, Fin.snoc_last, farR_rootNR, rootXR, Fin.snoc_last]
  constructor
  · have : 0 < -junL (cfDrv0 r y) r := by
      unfold junL; rw [neg_div, neg_neg]; exact one_div_pos.2 hgL
    linarith
  · unfold junR; rw [neg_div]; exact neg_pos.2 (div_neg_of_pos_of_neg one_pos hgR)

variable [IsProbabilityMeasure P]

/-- **The far gaps at the node tip are strictly positive** almost surely when the node prefix is pre-contact at a
positive time. -/
theorem ae_farGaps_nodeData (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) (hr : 0 < r)
    (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r (fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
        (fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) noise).alive (nodeLen s) (nodePre s) →
      ((nodeData x₀ h44 hκ hκ4 hb P h W ζ s r (fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
        (fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) noise).marks (nodeLen s) (nodePre s) ω).1
          (farL (Nat.lt_of_lt_of_le (rootNL_pos _) (Nat.le_add_right _ _))) < 0 ∧
      0 < ((nodeData x₀ h44 hκ hκ4 hb P h W ζ s r (fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
        (fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) noise).marks (nodeLen s) (nodePre s) ω).2
          (farR (Nat.lt_of_lt_of_le (rootNR_pos _) (Nat.le_add_right _ _))) := by
  have hhm : Measurable h := hG.1
  have hD := isReg_nodeData x₀ h44 hκ hκ4 hb (s := s) (r := r) (noise := noise)
    (xL0 := fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
    (xR0 := fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) hhm hcf
    ((measurable_rootXL (x₀ := x₀) hκ hb r).comp (measurable_cfHistory_of_strip hcf))
    ((measurable_rootXR (x₀ := x₀) hκ hb r).comp (measurable_cfHistory_of_strip hcf))
  have hT := isTree_nodeData x₀ h44 hκ hκ4 hb (P := P) (h := h) (W := W) (ζ := ζ) (s := s) (r := r)
    (xL0 := fun ω => rootXL hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω))
    (xR0 := fun ω => rootXR hκ hb x₀ r (Cond44Ref.cfHistory W ζ ω)) (noise := noise)
  filter_upwards [ae_cfHistory_mem_goodSet49 hA hκ hκ4 hb hG hcf hr] with ω hω hAl
  have hS := isSpine_nodeData x₀ h44 hκ hκ4 hb hAl
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, -⟩ :=
    ((hD.isKilledFamily (nodeLen s) (nodePre s)).arc ω).exists_kPath_trace (TreeData.startCap_lt_kLife hD hAl)
  have hj := rootXL_farL_neg x₀ hκ hb hω
  have hq0 : 0 < qLast (nodeLen s) (nodePre s) := by
    rw [← lastO_eq isValid_nodePre, lastO_nodePre]
    exact_mod_cast terminalRat_pos s
  exact TreeData.farGaps_spine hD hT hS hw hEq htS.le hw0 (rootNL_pos _) (rootNR_pos _) hj.1.le hj.2.le hq0

end Node

section Image

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {E : Schedule → ℕ → Ω → Driver}
  {nL₀ nR₀ : ℕ} {xL0 : Ω → Fin nL₀ → ℝ} {xR0 : Ω → Fin nR₀ → ℝ}
  {noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ}

/-- The node tree's image curves are killed arcs at every sample (no measurability needed). -/
theorem isKilledArc_nodeData {s : Schedule} {r : ℝ≥0} {k : ℕ} {t : Fin k → ℝ≥0} (hv : NodeValid s k t) (ω : Ω) :
    IsKilledArc ((nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).img k t ω)
      ((nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).pre k t ω) := by
  refine isKilledArc_tImg (fun ω' hω' => ⟨cfGood_of_mem_goodHitSet (nodeGood_spec x₀ h44 hκ hκ4 hb hω'.2).1.1 r, ?_⟩)
    (fun _ => one_pos) ω
  show IsProperArc (nodeAlpha x₀ h44 hκ hκ4 hb h s k t ω')
  by_cases hj : k ≤ nodeLen s
  · rw [nodeAlpha_of_le _ _ _ _ _ hj]
    exact (nodeGood_spec x₀ h44 hκ hκ4 hb hω'.2).2 _ _ isValid_nodePre
  · rw [nodeAlpha_of_lt _ _ _ _ _ (not_le.1 hj)]
    exact (nodeGood_spec x₀ h44 hκ hκ4 hb hω'.2).2 k t hv.1

/-- **The node images are bounded when Proposition 5.13's node target is** (at every sample). -/
theorem isBounded_nodeImage (n : ℕ) (q : ℚ) (ω : Ω)
    (hDb : Bornology.IsBounded (nodeTarget W
      (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n) q ω)) :
    Bornology.IsBounded
      ((nodeData x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n) (q : ℝ).toNNReal xL0 xR0 noise).imageG
        (nodeZ (nodeData x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n) (q : ℝ).toNNReal xL0 xR0 noise)
          (nodePre (scheduleAt n)) (descPts E n)) ω) := by
  classical
  set D := nodeData x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n) (q : ℝ).toNNReal xL0 xR0 noise with hDdef
  by_cases hG : ω ∈ D.G
  · simp only [TreeData.imageG, hG, ↓reduceIte]
    obtain ⟨⟨hy, hζ, hw⟩, -⟩ := nodeGood_spec x₀ h44 hκ hκ4 hb hG
    have hcg := cfGood_of_mem_goodHitSet hy (q : ℝ).toNNReal
    have hGc : ω ∈ D.Gc (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) := ⟨nodeValid_nodePre, hG⟩
    set K : Set ℂ := if ω ∈ D.alive (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) then
      D.img (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) ω '' Icc 0 (qLast (nodeLen (scheduleAt n))
        (nodePre (scheduleAt n))) else ∅ with hKdef
    have hKb : Bornology.IsBounded K := by
      by_cases hA : ω ∈ D.alive (nodeLen (scheduleAt n)) (nodePre (scheduleAt n))
      · simp only [hKdef, hA, ↓reduceIte]
        have hγ := isKilledArc_nodeData x₀ h44 hκ hκ4 hb (P := P) (h := h) (W := W) (ζ := ζ) (s := scheduleAt n)
          (r := (q : ℝ).toNNReal)
          (xL0 := xL0) (xR0 := xR0) (noise := noise) nodeValid_nodePre ω
        exact (isCompact_Icc.image_of_continuousOn (hγ.cont.mono (hγ.icc _ hA.2))).isBounded
      · simp only [hKdef, hA, ↓reduceIte]
        exact Bornology.isBounded_empty
    refine (hKb.union hDb).subset ?_
    rintro _ ⟨z, hz, hzH, hzK, rfl⟩
    rcases hz with hz | hz
    · left
      by_cases hA : ω ∈ D.alive (nodeLen (scheduleAt n)) (nodePre (scheduleAt n))
      · simp only [hA, ↓reduceIte, mem_ofPred_eq] at hz
        simp only [hKdef, hA, ↓reduceIte]
        obtain ⟨q', hq0, hqτ, rfl⟩ := hz
        refine ⟨q', ⟨hq0.le, hqτ⟩, ?_⟩
        rw [TreeData.img, tImg_of_mem hGc]
        beta_reduce
        rw [imgCurve_of_pos hq0]
      · simp only [hA, ↓reduceIte, mem_empty_iff_false] at hz
    · right
      obtain ⟨m', t', ht', rfl⟩ := mem_iUnion.1 hz
      obtain ⟨hR, hK⟩ := revChart_eq_ownComponentChart (r := q) hy hζ hw (driverTree E (descendantIndex n m') ω t')
      refine ⟨negInv (driverTree E (descendantIndex n m') ω t'), ⟨mem_iUnion.2 ⟨m', t', ht', rfl⟩,
        negInv_mem_H hzH, fun hmem => hzK ?_⟩, ?_⟩
      · show driverTree E (descendantIndex n m') ω t' ∈ cfHullQ ((q : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω)
        rw [hcg.2]
        refine ⟨negInv (driverTree E (descendantIndex n m') ω t'), ?_, negInv_negInv' _⟩
        show negInv (driverTree E (descendantIndex n m') ω t') ∈
          fwdHull (cfDrv0 ((q : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω)) ((q : ℝ).toNNReal)
        rw [hK]; exact hmem
      · show _ = ((fun _ => (1 : ℝ)) ω : ℂ) * revChart (cfDrv0 ((q : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω))
          (((q : ℝ).toNNReal : ℝ≥0) : ℝ) (driverTree E (descendantIndex n m') ω t')
        rw [hR, Complex.ofReal_one, one_mul]
  · simp only [TreeData.imageG, hG, ↓reduceIte]
    exact Bornology.isBounded_empty

end Image

end InteractingSLE.Sec5.Prop59NodeTree

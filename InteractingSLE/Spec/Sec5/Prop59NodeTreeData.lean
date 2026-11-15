/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreePath
import InteractingSLE.Spec.Sec5.Prop59NodeTreeScale
import InteractingSLE.Spec.Sec5.Prop59PiecesMarks

/-!
# The tree of pieces of a node experiment

Packet PROVE-PROP59-NODETREE. In the setting of PROVE-PROP513C's assembly, for an extreme-angle schedule `s` (a node
of Proposition 5.13's tree) and a counterflow time `r`, the node experiment's candidate pieces are the joint-chart
images of the candidate paths of the node tree (`Prop59NodeTreePath`: the node's own schedule `s`, then the
alternating angles, `+π/2` first), read after their last switch and killed at their first new contact
(PROVE-PROP59-PIECES' `TreeData`):

* `nodeAlpha`: the paths (at depths up to the node length, the node path itself);
* `nodeGood`, `ae_mem_nodeGood`: a measurable good set of full measure;
* **`nodeData`**, `isReg_nodeData`, `isTree_nodeData`: the tree data (undilated joint chart, root marks of the
  counterflow chart);
* `prefixPts`, `descPts`, `nodeZ`: the node prefix points and the descendant points of `s` (chart `Q`);
* **`isChainAll_subFam_nodeData`**: the subtree after the node prefix has gap-free chain data in the joint-chart
  image of the prefix and descendant points (`ae_mem_nodeZ`: positions at positive rational times are such points);
* **`isBounded_nodeImage`**: that image set is bounded whenever Proposition 5.13's node target is.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces
open Prop59Nodes
open Sec7.StripWall (goodPathSet)

/-! ### Lists along the node prefix -/

theorem init_append {α : Type*} {m j : ℕ} (a : Fin m → α) (b : Fin (j + 1) → α) :
    Fin.init (Fin.append a b : Fin (m + (j + 1)) → α) = Fin.append a (Fin.init b) := by
  funext i
  refine Fin.addCases (fun i₁ => ?_) (fun i₂ => ?_) i
  · simp only [Fin.init]
    have e : (Fin.castAdd j i₁).castSucc = Fin.castAdd (j + 1) i₁ := Fin.ext rfl
    rw [e, Fin.append_left, Fin.append_left]
  · simp only [Fin.init]
    have e : (Fin.natAdd m i₂).castSucc = Fin.natAdd m i₂.castSucc := Fin.ext rfl
    rw [e, Fin.append_right, Fin.append_right]
    rfl

theorem append_elim0 {α : Type*} {m : ℕ} (a : Fin m → α) : (Fin.append a Fin.elim0 : Fin (m + 0) → α) = a := by
  rw [Fin.append_elim0]
  rfl

/-- The appended lists of a node extension are node-admissible as soon as they are admissible. -/
theorem nodeValid_append {s : Schedule} {j : ℕ} {t : Fin j → ℝ≥0}
    (hv : IsValid (nodeLen s + j) (Fin.append (nodePre s) t)) :
    NodeValid s (nodeLen s + j) (Fin.append (nodePre s) t) :=
  ⟨hv, fun i hi => Fin.append_left (nodePre s) t ⟨i, hi⟩⟩

/-! ### The node tree -/

section Setting

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{u}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens)
  (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (s : Schedule)

/-- **The paths of the node tree**: the node path (the schedule `s` continued at `+π/2`) at depths up to the node
length, the candidate paths of the node flags beyond. -/
def nodeAlpha (j : ℕ) (t : Fin j → ℝ≥0) : Ω → ℝ → ℂ :=
  if j ≤ nodeLen s then
    qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) (nodeLen s) (nodePre s)
  else qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) j t

/-- **The good samples of a node experiment**: the counterflow is good and every admissible candidate path of the node
flags is a simple proper arc. -/
def NodeGood (ω : Ω) : Prop :=
  (Cond44Ref.cfHistory W ζ ω ∈ goodHitSet ∧ ζ ω = ⊤ ∧ Continuous (fun t => W t ω)) ∧ ∀ j t, IsValid j t →
    IsProperArc (qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) j t ω)

/-- A measurable set of good samples (of full measure, `ae_mem_nodeGood`). -/
def nodeGood : Set Ω := (toMeasurable P {ω | ¬ NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω})ᶜ

variable {nL₀ nR₀ : ℕ}

/-- **The tree data of the node experiment** at the counterflow time `r`: the node tree's paths in the undilated joint
chart, the counterflow history, the node-admissible lists, the given root marks and noises. -/
def nodeData (r : ℝ≥0) (xL0 : Ω → Fin nL₀ → ℝ) (xR0 : Ω → Fin nR₀ → ℝ)
    (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) : TreeData Ω nL₀ nR₀ where
  r := r
  y := Cond44Ref.cfHistory W ζ
  lam := fun _ => 1
  G := nodeGood x₀ h44 hκ hκ4 hb P h W ζ s
  α := nodeAlpha x₀ h44 hκ hκ4 hb h s
  valid := NodeValid s
  xL0 := xL0
  xR0 := xR0
  noise := noise

variable {P h W ζ s} {r : ℝ≥0} {xL0 : Ω → Fin nL₀ → ℝ} {xR0 : Ω → Fin nR₀ → ℝ}
  {noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ}

theorem nodeGood_spec {ω : Ω} (hω : ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s) :
    NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω := by
  by_contra hn
  exact hω (subset_toMeasurable _ _ hn)

omit mΩ in
theorem nodeAlpha_of_le {j : ℕ} (hj : j ≤ nodeLen s) (t : Fin j → ℝ≥0) :
    nodeAlpha x₀ h44 hκ hκ4 hb h s j t =
      qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) (nodeLen s) (nodePre s) := by
  simp only [nodeAlpha, hj, ↓reduceIte]

omit mΩ in
theorem nodeAlpha_of_lt {j : ℕ} (hj : nodeLen s < j) (t : Fin j → ℝ≥0) :
    nodeAlpha x₀ h44 hκ hκ4 hb h s j t =
      qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) j t := by
  simp only [nodeAlpha, not_le.2 hj, ↓reduceIte]

omit mΩ in
/-- On the subtree, the paths are the candidate paths of the appended lists. -/
theorem nodeAlpha_append (j : ℕ) (t : Fin j → ℝ≥0) :
    nodeAlpha x₀ h44 hκ hκ4 hb h s (nodeLen s + j) (Fin.append (nodePre s) t) =
      qPathF h44 hκ hκ4 (sourceWord (x₀ := x₀) hκ hb) (qField x₀ κ h) (nodeFlag s) (nodeLen s + j)
        (Fin.append (nodePre s) t) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have ht : t = Fin.elim0 := funext fun i => i.elim0
    subst ht
    rw [nodeAlpha_of_le _ _ _ _ _ (by omega : nodeLen s + 0 ≤ nodeLen s), append_elim0]
    rfl
  · exact nodeAlpha_of_lt _ _ _ _ _ (by omega) _

/-- **The node tree data are regular.** -/
theorem isReg_nodeData (hhm : Measurable h) (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hxL : Measurable xL0) (hxR : Measurable xR0) :
    (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).IsReg where
  y := measurable_cfHistory_of_strip hcf
  lam := measurable_const
  lam_pos _ := one_pos
  G := (measurableSet_toMeasurable _ _).compl
  good ω hω := by
    refine ⟨cfGood_of_mem_goodHitSet (nodeGood_spec x₀ h44 hκ hκ4 hb hω).1.1 r, fun j t hv => ?_⟩
    show IsProperArc (nodeAlpha x₀ h44 hκ hκ4 hb h s j t ω)
    by_cases hj : j ≤ nodeLen s
    · rw [nodeAlpha_of_le _ _ _ _ _ hj]
      exact (nodeGood_spec x₀ h44 hκ hκ4 hb hω).2 _ _ isValid_nodePre
    · rw [nodeAlpha_of_lt _ _ _ _ _ (not_le.1 hj)]
      exact (nodeGood_spec x₀ h44 hκ hκ4 hb hω).2 j t hv.1
  α j t u := by
    have hF := (measurable_targetField κ (Real.exp (π * x₀)) (Real.exp_pos _)).comp hhm
    show Measurable fun ω => nodeAlpha x₀ h44 hκ hκ4 hb h s j t ω u
    by_cases hj : j ≤ nodeLen s
    · rw [nodeAlpha_of_le _ _ _ _ _ hj]; exact measurable_qPathF h44 hκ hκ4 _ _ _ hF _ _ u
    · rw [nodeAlpha_of_lt _ _ _ _ _ (not_le.1 hj)]; exact measurable_qPathF h44 hκ hκ4 _ _ _ hF _ _ u
  xL0 := hxL
  xR0 := hxR
  qrat j t hv := ⟨lastO j t, (lastO_eq hv.1).symm⟩

/-- **The node tree data form a tree.** -/
theorem isTree_nodeData : (nodeData x₀ h44 hκ hκ4 hb P h W ζ s r xL0 xR0 noise).IsTree where
  init j t hv := ⟨NodeValid.init hv, qLast_init_le hv.1, (hv.1.2 _).2.1⟩
  pfx j t hv ω u _ hu := by
    show nodeAlpha x₀ h44 hκ hκ4 hb h s (j + 1) t ω u = nodeAlpha x₀ h44 hκ hκ4 hb h s j (Fin.init t) ω u
    by_cases hj : j + 1 ≤ nodeLen s
    · rw [nodeAlpha_of_le _ _ _ _ _ hj, nodeAlpha_of_le _ _ _ _ _ (by omega)]
    · rw [nodeAlpha_of_lt _ _ _ _ _ (by omega)]
      rw [qPathF_pfx h44 hκ hκ4 _ _ hv.1 ω hu]
      by_cases hj' : j ≤ nodeLen s
      · obtain rfl : j = nodeLen s := by omega
        rw [nodeAlpha_of_le _ _ _ _ _ le_rfl, (NodeValid.init hv).eq_nodePre]
      · rw [nodeAlpha_of_lt _ _ _ _ _ (by omega)]
  qnonneg j t hv := by
    show 0 ≤ qLast j t
    rw [← lastO_eq hv.1]; exact_mod_cast lastO_nonneg hv.1

variable [StandardBorelSpace Ω] [IsProbabilityMeasure P] {γ : Ω → ℝ≥0 → ℂ} {E : Schedule → ℕ → Ω → Driver}

/-- **The good set has full measure.** -/
theorem ae_mem_nodeGood (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s)) :
    ∀ᵐ ω ∂P, ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s := by
  have hg := ae_all_valid (P := P) fun j t (_ : IsValid j t) =>
    ae_codeGood h44 hκ hκ4 hb hG hE hR (candSchedF (nodeFlag s) j t)
  have hae : ∀ᵐ ω ∂P, NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω := by
    filter_upwards [hg, ae_cfHistory_mem_goodHitSet hA hκ hκ4 hb hG hcf htr] with ω hgω hcω
    exact ⟨hcω, fun j t hv => (isProperArc_qPathF_of h44 hκ hκ4 _ _ (hgω j t hv)).1⟩
  rw [ae_iff]
  have e : {ω | ¬ ω ∈ nodeGood x₀ h44 hκ hκ4 hb P h W ζ s} =
      toMeasurable P {ω | ¬ NodeGood x₀ h44 hκ hκ4 hb h W ζ s ω} := by
    ext ω; simp [nodeGood]
  rw [e, measure_toMeasurable]
  exact ae_iff.1 hae

end Setting

end InteractingSLE.Sec5.Prop59NodeTree

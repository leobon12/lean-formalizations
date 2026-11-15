/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodeTreeMarks
import InteractingSLE.Spec.Sec5.Lemma57Visit

/-!
# A node experiment is reached before the node's first visit

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.9 (p. 143: "work on the event that `r`
precedes its first hit of the initial stopped flow-line exploration"), proof of Proposition 5.13 (p. 151, `L_z`,
`T_z`). On the event `r < T_z` (PROVE-PROP59T4's `nodeActive`), the node prefix ending at `z` does not meet the
revealed counterflow hull: by Lemma 5.7 (PROVE-PROP513C's `TargetLemma57Statement`, from the reverse-visit law) every
point of the prefix is visited by the counterflow, but not by time `r` (the points of the prefix are visited in
reverse chronological order, after `z`), and a point of `K_r` off the trace `γ([0, r])` lies in the interior of `K_r`,
which a generating trace never visits later (`notMem_interior_fwdHull_of_lt`).

* `mem_interior_of_isFilling`: a point of a filling off the filled closed set is interior;
* `false_of_visit_mem_fwdHull`: a point of `K_r` in `ℍ` visited by the trace, but not by time `r`, does not exist;
* **`ae_alive_of_nodeActive`**: almost surely on `{r < T_z}` the node prefix is pre-contact at `r` (the node
  experiment's root candidate is alive).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage Prop59Pieces
open Prop513Wire (StripReverseVisitLaw)

/-! ### Interior points of a hull -/

/-- A point of a filling `K` of a closed set `A`, in `ℍ` and off `A`, is an interior point of `K`. -/
theorem mem_interior_of_isFilling {K A : Set ℂ} (hK : IsFilling K A) (hA : IsClosed A) {p : ℂ} (hpH : p ∈ H)
    (hpK : p ∈ K) (hpA : p ∉ A) : p ∈ interior K := by
  obtain ⟨⟨z, -, hz⟩, -⟩ := hK
  have hU : IsOpen (H \ A) := QuantumZipper.isOpen_H.sdiff hA
  have hC : IsOpen (connectedComponentIn (H \ A) p) := hU.connectedComponentIn
  have hsub : connectedComponentIn (H \ A) p ⊆ K := by
    intro q hq
    by_contra hqK
    have hqH : q ∈ H := (connectedComponentIn_subset _ _ hq).1
    have hq' : q ∈ connectedComponentIn (H \ A) z := by rw [hz]; exact ⟨hqH, hqK⟩
    have e1 := connectedComponentIn_eq hq
    have e2 := connectedComponentIn_eq hq'
    have hp : p ∈ connectedComponentIn (H \ A) z := by
      rw [e2, ← e1]; exact mem_connectedComponentIn ⟨hpH, hpA⟩
    rw [hz] at hp
    exact hp.2 hpK
  exact interior_mono hsub (hC.mem_nhds (mem_connectedComponentIn ⟨hpH, hpA⟩) |> mem_interior_iff_mem_nhds.2)

/-- **No late first visit to the hull**: a point of `K_r` in `ℍ` that the trace visits but not by time `r` does not
exist. -/
theorem false_of_visit_mem_fwdHull {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsGeneratingTrace w ⊤ η) {r v : ℝ≥0} {p : ℂ} (hpH : p ∈ H)
    (hpK : p ∈ fwdHull (fun s : ℝ => w s.toNNReal) r) (hv : η v = p) (hno : ∀ u ≤ r, η u ≠ p) : False := by
  have hηc := continuous_of_isGeneratingTrace_top hη
  have hA : IsClosed (η '' Icc 0 r) := (isCompact_Icc.image hηc).isClosed
  have hpA : p ∉ η '' Icc 0 r := by
    rintro ⟨u, hu, hue⟩
    exact hno u hu.2 hue
  have hin := mem_interior_of_isFilling (hη.2.2 r ENNReal.coe_lt_top) hA hpH hpK hpA
  have hrv : r < v := by
    by_contra hle
    exact hno v (not_lt.1 hle) hv
  have := notMem_interior_fwdHull_of_lt hw hw0 hη hrv
  rw [hv] at this
  exact this hin

/-! ### The node experiment is reached -/

section Active

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
  {E : Schedule → ℕ → Ω → Driver}

/-- **On the event `r < T_z`, the node prefix ending at `z` is pre-contact at `r`** (almost surely): the root
candidate of the node experiment is alive. -/
theorem ae_alive_of_nodeActive (hA : PartAInputsSixteenDiv)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ) (n : ℕ) (r : ℚ) {nL₀ nR₀ : ℕ}
    (xL0 : Ω → Fin nL₀ → ℝ) (xR0 : Ω → Fin nR₀ → ℝ) (noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ω ∈ nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n) r →
      ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ (scheduleAt n) (r : ℝ).toNNReal xL0 xR0 noise).alive
        (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) := by
  set s := scheduleAt n with hsdef
  let c := sourceWord (x₀ := x₀) hκ hb
  have hc : ExtremeHeights κ c := sourceWord_extreme hκ hb
  have hhQ := sourceWord_gff hκ hb hG
  have hreg := Prop513Wire.fig51_trace_mem_H_of_partA hA hκ hκ4 hb hG hcf
  have hζ := hreg.mono fun _ hω => hω.1
  have htrTop : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [htr, hζ] with ω hω hζω
    rwa [hζω] at hω
  have hH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H := by
    filter_upwards [hreg, htrTop] with ω hω hγω
    exact hω.2 _ hγω
  have hi := Prop513Wire.ae_driverTree_interior h44 hκ hκ4 c hc hhQ hE hR
  have h57 := Prop513Wire.targetLemma57_of_stripReverseVisit (Real.exp_pos _) (htrTop.mono fun _ hω => hω.1) hH
    hi hVisit
  have hg := ae_codeGood h44 hκ hκ4 hb hG hE hR (candSchedF (nodeFlag s) (nodeLen s) (nodePre s))
  obtain ⟨b₀, J₀, _, _, hfl, _⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hW0 : ∀ᵐ ω ∂P, W 0 ω = 0 := hC.1.ae_isIntegratedSLEPath.mono fun _ hp => hp.1
  filter_upwards [ae_mem_nodeGood x₀ h44 hκ hκ4 hb (s := s) hA hG hcf htr hE hR, h57, hi, hg,
    ae_prefixDriver_eq_joined h44 hκ hκ4 hb hG hE hR, htrTop, hW0] with ω hgood h57ω hiω hgω hpω hγω hw0 hact
  obtain ⟨⟨hy, hζω, hw⟩, -⟩ := nodeGood_spec x₀ h44 hκ hκ4 hb hgood
  have hcg := cfGood_of_mem_goodHitSet hy (r : ℝ).toNNReal
  obtain ⟨-, hK⟩ := revChart_eq_ownComponentChart (r := r) hy hζω hw 0
  have hGc : ω ∈ (nodeData x₀ h44 hκ hκ4 hb P h W ζ s (r : ℝ).toNNReal xL0 xR0 noise).Gc (nodeLen s) (nodePre s) :=
    ⟨nodeValid_nodePre, hgood⟩
  have hτ : qLast (nodeLen s) (nodePre s) = (treeTime n : ℝ) := by
    rw [← lastO_eq isValid_nodePre, lastO_nodePre, treeTime_eq]
  refine ⟨hGc, ?_⟩
  show qLast (nodeLen s) (nodePre s) ∈ tPre _ _ _ _ ω
  rw [tPre_of_mem hGc]
  refine ⟨by rw [hτ]; exact (treeTime_pos n).le, fun u hu => ?_⟩
  show nodeAlpha x₀ h44 hκ hκ4 hb h s (nodeLen s) (nodePre s) ω u ∉ _
  rw [nodeAlpha_of_le _ _ _ _ _ le_rfl, hτ] at *
  have hu' : u ∈ Icc 0 (terminal s : ℝ) := hu
  rw [← prefixTrace_node_eq_qPathF h44 hκ hκ4 c (qField x₀ κ h) hgω (hpω s) hu']
  change driverTree E n ω u ∉ cfHullQ (r : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω)
  rw [hcg.2]
  rintro ⟨p, hpK, hpe⟩
  rw [hK] at hpK
  have hpH : p ∈ H := hpK.1
  have hzH : negInv p ∈ H := negInv_mem_H hpH
  rw [hpe] at hzH
  rcases hu.1.eq_or_lt with hu0 | hu0
  · rw [← hu0, (hiω n).1] at hzH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hzH)
  · have hp : capacityTree (driverTree E) n ω u = p := by
      show -(driverTree E n ω u)⁻¹ = p
      rw [← hpe]
      simp [negInv]
    obtain ⟨v', -, hv', -⟩ := h57ω n (u / 2) u (by linarith) (by linarith) hu.2
    rw [hp] at hv'
    have hno : ∀ w ≤ (r : ℝ).toNNReal, γ ω w ≠ p := by
      intro w hw'
      rcases (zero_le : (0 : ℝ≥0) ≤ w).eq_or_lt with hw0' | hwpos
      · rw [← hw0', hγω.1]
        intro h0
        rw [← h0] at hpH
        exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hpH)
      have hwr : (w : ℝ) ≤ r := by
        have h1 := NNReal.coe_le_coe.2 hw'
        rw [Real.coe_toNNReal'] at h1
        have h2 : (0 : ℝ) < w := NNReal.coe_pos.2 hwpos
        rcases le_total (r : ℝ) 0 with hr0 | hr0
        · rw [max_eq_right hr0] at h1; linarith
        · rwa [max_eq_left hr0] at h1
      rcases hu.2.lt_or_eq with hlt | heq
      · obtain ⟨v, -, hvz, hvne⟩ := h57ω n u (treeTime n) hu0 hlt le_rfl
        have hTv := traceFirstVisit_le hvz
        have hwv : w ≤ v := by
          have h1 : (r : ℝ) < traceFirstVisit (γ ω) _ := hact
          have h2 : (w : ℝ) < traceFirstVisit (γ ω) (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω) :=
            lt_of_le_of_lt hwr h1
          exact (NNReal.coe_lt_coe.1 (lt_of_lt_of_le h2 (NNReal.coe_le_coe.2 hTv))).le
        rw [← hp]
        exact hvne w hwv
      · have h1 : (r : ℝ) < traceFirstVisit (γ ω) _ := hact
        have h2 : w < traceFirstVisit (γ ω) (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n ω) :=
          NNReal.coe_lt_coe.1 (lt_of_le_of_lt hwr h1)
        rw [← hp, heq]
        exact apply_ne_of_lt_traceFirstVisit h2
    exact false_of_visit_mem_fwdHull hw hw0 hγω hpH hpK hv' hno

end Active

end InteractingSLE.Sec5.Prop59NodeTree

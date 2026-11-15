/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedNTrCausal

/-!
# Prop 5.9's node experiment on `Gam` only reads the node path up to its last switch

Packet PROVE-STAGED-NODETRANSFER (towards `NodeGluePast`). From the tree causality (`TreeData.causal`): at two points
of `Gam` with the same counterflow chart and the same node path up to the last switch of an admissible extension
`nodePre ++ t`, if the node candidate `(j, t)` is reached at the first point (and its tree candidate is alive there),
then every canonical node past event of `(j, t)` contains both points or neither.

* `PieceUpTo.reindex`, `PieceUpTo.scale`, `candInv_scaleFam`, **`CanonUpTo.subFam`**, **`CanonUpTo.scaleFam`**: the
  agreement up to the switching times passes to the dilated subtree;
* `sepSigma`: the events not separating two points (a σ-algebra); **`canonQ_le_sepSigma`**;
* **`gamNode_causal`**.

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedNTr

open WangWu WangWu.ImgWord Prop59System Prop59Stage Prop59Pieces Prop59Nodes Prop59NodeTree StagedCand StagedRepJ
open GlueCond Cond44Ref CrossCond.Word49 LawUnique StagedRepLater
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Sec7.Lemma71C (capClock)

/-! ### Agreement up to the switching times under reindexing and dilation -/

section Transport

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {ω : Ω} {ω' : Ω'}

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
theorem PieceUpTo.reindex {a b c d : ℕ} (h₁ : a = b) (h₂ : c = d) {p : Piece Ω a c} {p' : Piece Ω' a c}
    {T : ℝ≥0} (h : PieceUpTo p p' ω ω' T) : PieceUpTo (reindexPiece h₁ h₂ p) (reindexPiece h₁ h₂ p') ω ω' T :=
  ⟨h.W, fun _ => h.VL _, fun _ => h.VR _, h.lt, h.clk⟩

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
theorem PieceUpTo.scale {nL nR : ℕ} {p : Piece Ω nL nR} {p' : Piece Ω' nL nR} {T : ℝ≥0}
    (h : PieceUpTo p p' ω ω' T) {c : Ω → ℝ≥0} {c' : Ω' → ℝ≥0} (hc : c ω = c' ω') (hc0 : 0 < c ω) :
    PieceUpTo (scalePiece c p) (scalePiece c' p') ω ω' (c ω ^ 2 * T) := by
  have hc2 : 0 < c ω ^ 2 := pow_pos hc0 2
  have hle : ∀ u ≤ c ω ^ 2 * T, u / c ω ^ 2 ≤ T := fun u hu => by
    rw [div_le_iff₀ hc2, mul_comm]; exact hu
  refine ⟨fun u hu => ?_, fun i u hu => ?_, fun k u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · simp only [scalePiece, ← hc, h.W _ (hle u hu)]
  · simp only [scalePiece, ← hc, h.VL _ _ (hle u hu)]
  · simp only [scalePiece, ← hc, h.VR _ _ (hle u hu)]
  · obtain ⟨h1, h2⟩ := h.lt _ (hle u hu)
    refine ⟨(coe_lt_scale_iff hc0).2 h1, ?_⟩
    show (u : ℝ≥0∞) < ((c' ω' ^ 2 : ℝ≥0) : ℝ≥0∞) * p'.ζ ω'
    rw [← hc]
    exact (coe_lt_scale_iff hc0).2 h2
  · simp only [scalePiece, ← hc, h.clk _ (hle u hu)]

/-- The clock inverse of a dilated family is the dilated clock inverse. -/
theorem candInv_scaleFam {nL₀ nR₀ : ℕ} {cand : CandFam Ω nL₀ nR₀} (hfam : IsRegFam cand) {c : Ω → ℝ≥0}
    (hc0 : 0 < c ω) (j : ℕ) (t : Fin j → ℝ≥0) (g : ℝ≥0) :
    candInv (scaleFam c cand) j t g ω = c ω ^ 2 * candInv cand j t g ω :=
  StagedNode.clkInv_dilate hc0 (fun _ => rfl) ((hfam j t).clk_mono ω) g

omit [MeasurableSpace Ω'] in
/-- **Agreement up to the switching times passes to the dilated family.** -/
theorem CanonUpTo.scaleFam {nL₀ nR₀ : ℕ} {cand : CandFam Ω nL₀ nR₀} {cand' : CandFam Ω' nL₀ nR₀}
    (hfam : IsRegFam cand) {c : Ω → ℝ≥0} {c' : Ω' → ℝ≥0} (hc : c ω = c' ω') (hc0 : 0 < c ω) :
    ∀ j t, CanonUpTo cand cand' ω ω' j t → CanonUpTo (Prop59NodeTree.scaleFam c cand)
      (Prop59NodeTree.scaleFam c' cand') ω ω' j t
  | 0, _, _ => trivial
  | j + 1, t, h => by
    refine ⟨CanonUpTo.scaleFam hfam hc hc0 j (Fin.init t) h.1, ?_⟩
    rw [candInv_scaleFam hfam hc0]
    exact h.2.scale hc hc0

omit [MeasurableSpace Ω] [MeasurableSpace Ω'] in
/-- **Agreement up to the switching times passes to the subtree after a prefix.** -/
theorem CanonUpTo.subFam {nL₀ nR₀ : ℕ} {cand : CandFam Ω nL₀ nR₀} {cand' : CandFam Ω' nL₀ nR₀} {m : ℕ}
    (pre : Fin m → ℝ≥0) :
    ∀ j t, CanonUpTo cand cand' ω ω' (m + j) (Fin.append pre t) →
      CanonUpTo (Prop59Nodes.subFam cand m pre) (Prop59Nodes.subFam cand' m pre) ω ω' j t
  | 0, _, _ => trivial
  | j + 1, t, h => by
    have h' : CanonUpTo cand cand' ω ω' (m + j + 1) (Fin.append pre t : Fin (m + (j + 1)) → ℝ≥0) := h
    obtain ⟨h1, h2⟩ := h'
    rw [init_append] at h1 h2
    rw [StagedNode.append_last] at h2
    exact ⟨CanonUpTo.subFam pre j (Fin.init t) h1, h2.reindex _ _⟩

end Transport

/-! ### Events not separating two points -/

section Sep

variable {Γ : Type*}

/-- **The events not separating `γ` and `γ'`** (a σ-algebra). -/
@[instance_reducible]
def sepSigma (γ γ' : Γ) : MeasurableSpace Γ where
  MeasurableSet' M := γ ∈ M ↔ γ' ∈ M
  measurableSet_empty := by simp only [mem_empty_iff_false]
  measurableSet_compl M h := by simp only [mem_compl_iff, h]
  measurableSet_iUnion f hf := by simp only [mem_iUnion]; exact exists_congr hf

theorem measurableSet_sepSigma_iff {γ γ' : Γ} {M : Set Γ} : MeasurableSet[sepSigma γ γ'] M ↔ (γ ∈ M ↔ γ' ∈ M) :=
  Iff.rfl

variable {𝓑 : MeasurableSpace Γ} [mΓ : MeasurableSpace Γ] {nL₀ nR₀ : ℕ} {cand : CandFam Γ nL₀ nR₀}
  {y₀ : Γ → Start (nL₀ + 0) (nR₀ + 0)} {G : ℕ → ℕ → ℝ≥0} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {R₀ : Set Γ} {γ γ' : Γ}

omit mΓ in
/-- The canonical reached events are inside the root event. -/
theorem canonR_subset (j : ℕ) (t : Fin j → ℝ≥0) : canonR cand G hnL hnR y₀ R₀ j t ⊆ R₀ := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact fun x hx => ih (Fin.init t) hx.1

/-- **The canonical pasts do not separate two points** where the list is reached at the first and the candidate
pieces agree up to the switching times (with agreeing root data and base). -/
theorem canonQ_le_sepSigma (hfam : IsRegFam cand) (hy₀ : Measurable y₀) (hG : ∀ n, Monotone (G n))
    (hy : y₀ γ = y₀ γ') (hR : γ ∈ R₀ → γ' ∈ R₀) (h𝓑 : 𝓑 ≤ sepSigma γ γ') :
    ∀ j t, γ ∈ canonR cand G hnL hnR y₀ R₀ j t → CanonUpTo cand cand γ γ' j t →
      canonQ 𝓑 cand G hnL hnR y₀ j t ≤ sepSigma γ γ'
  | 0, _, _, _ => h𝓑
  | j + 1, t, hγ, hc => by
    refine sup_le (canonQ_le_sepSigma hfam hy₀ hG hy hR h𝓑 j (Fin.init t) hγ.1 hc.1)
      (MeasurableSpace.generateFrom_le ?_)
    rintro _ ⟨n, m, S, hnm, -, rfl⟩
    exact mem_swGen_upTo hfam hfam hy₀ hy₀ hG hy hR hγ hc hnm S

end Sep

/-! ### The node experiment on `Gam` -/

theorem monotone_ratGrid (n : ℕ) : Monotone (Prop59System.ratGrid n) := by
  intro a b hab
  rw [ratGrid_eq, ratGrid_eq]
  refine Real.toNNReal_le_toNNReal (div_le_div_of_nonneg_right ?_ (by positivity))
  have : (a : ℝ) ≤ b := by exact_mod_cast hab
  linarith

section Node

variable (h44 : Theorem12ParamCond44Statement.{0}) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b') (n : ℕ) (r : ℝ≥0)

/-- **Two points of `Gam` with the same stopped counterflow history and good** see the same node tree data. -/
theorem treeSameAt_gamNodeData {γ γ' : Gam} (hy : cfStop r γ.2 = cfStop r γ'.2)
    (hG : γ ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n))
    (hG' : γ' ∈ gamNodeGood h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n)) :
    TreeSameAt (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r) γ γ' where
  lam := rfl
  drv := by
    show cfDrv0 r γ.2 = cfDrv0 r γ'.2
    rw [← cfDrv0_cfStop r γ.2, hy, cfDrv0_cfStop]
  hull := by
    show cfHullQ r γ.2 = cfHullQ r γ'.2
    rw [← cfHullQ_cfStop r γ.2, hy, cfHullQ_cfStop]
  xL0 := by
    show rootXL hκ hb x₀ r γ.2 = rootXL hκ hb x₀ r γ'.2
    rw [← rootXL_cfStop x₀ hκ hb r γ.2, hy, rootXL_cfStop]
  xR0 := by
    show rootXR hκ hb x₀ r γ.2 = rootXR hκ hb x₀ r γ'.2
    rw [← rootXR_cfStop x₀ hκ hb r γ.2, hy, rootXR_cfStop]
  G := hG
  G' := hG'

theorem qLast_pos_of_nodeValid {s : Schedule} {k : ℕ} {t : Fin (k + 1) → ℝ≥0} (hv : NodeValid s (k + 1) t) :
    0 < qLast (k + 1) t := by
  have h0 := (hv.1.2 (Fin.last k)).1
  have h1 := (hv.1.2 (Fin.last k)).2.1
  show 0 < decode (t (Fin.last k))
  exact div_pos (NNReal.coe_pos.2 h0) (sub_pos.2 (by exact_mod_cast h1))

/-- **Causality of the node experiment on `Gam`.** At two points with the same node tree data (`TreeSameAt`) and the
same node path up to the last switch of an admissible extension `nodePre ++ t`, if the node candidate `(j, t)` is
reached at the first point and its tree candidate is alive there, then no canonical node past event of `(j, t)`
separates the two points. -/
theorem gamNode_causal {j : ℕ} {t : Fin j → ℝ≥0} {γ γ' : Gam}
    (hs : TreeSameAt (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r) γ γ')
    (hα : EqOn (gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) γ)
      (gamNodeAlpha h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) (nodeLen (scheduleAt n) + j)
        (Fin.append (nodePre (scheduleAt n)) t) γ')
      (Icc 0 (qLast (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t))))
    (hR : γ ∈ gamNodeR h44 hκ hκ4 (x₀ := x₀) hb n r j t)
    (hal : γ ∈ (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).alive (nodeLen (scheduleAt n) + j)
      (Fin.append (nodePre (scheduleAt n)) t)) :
    ∀ M, MeasurableSet[gamNodeQ h44 hκ hκ4 (x₀ := x₀) hb n r j t] M → (γ ∈ M ↔ γ' ∈ M) := by
  have hD := isReg_gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r
  have hT := isTree_gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r
  have hpos : ∀ k t', (gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).valid (k + 1) t' →
      0 < qLast (k + 1) t' := fun _ _ hv => qLast_pos_of_nodeValid hv
  obtain ⟨-, -, -, hcanon⟩ := TreeData.causal hD hT hpos hs _ _ hal hα
  -- the node tip
  have halm := TreeData.IsTree.alive_append hD hT (nodePre (scheduleAt n)) j t hal
  have hvm := TreeData.IsTree.qLast_append_le hT (nodePre (scheduleAt n)) j t hal.1.1
  have hαm : EqOn ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).α (nodeLen (scheduleAt n))
      (nodePre (scheduleAt n)) γ) ((gamNodeData h44 hκ hκ4 (x₀ := x₀) hb (scheduleAt n) r).α
      (nodeLen (scheduleAt n)) (nodePre (scheduleAt n)) γ') (Icc 0 (qLast _ (nodePre (scheduleAt n)))) := by
    intro u hu
    rw [← Prop59NodeTree.TreeData.IsTree.α_append hT (nodePre (scheduleAt n)) j t hal.1.1 γ u hu.1 hu.2,
      ← Prop59NodeTree.TreeData.IsTree.α_append hT (nodePre (scheduleAt n)) j t hal.1.1 γ' u hu.1 hu.2]
    exact hα ⟨hu.1, hu.2.trans hvm.2⟩
  obtain ⟨halm', hmk, -, -⟩ := TreeData.causal hD hT hpos hs _ _ halm hαm
  have hmarks : gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n r γ = gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n r γ' := hmk
  have hscale : gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ = gamNodeScale h44 hκ hκ4 (x₀ := x₀) hb n r γ' := by
    simp only [gamNodeScale, hmarks]
  have hstart : gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r γ = gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r γ' := by
    simp only [gamNodeStart, hmarks, hscale]
  have hR0γ : γ ∈ gamNodeR0 h44 hκ hκ4 (x₀ := x₀) hb n r := canonR_subset j t hR
  have hR0 : γ ∈ gamNodeR0 h44 hκ hκ4 (x₀ := x₀) hb n r → γ' ∈ gamNodeR0 h44 hκ hκ4 (x₀ := x₀) hb n r :=
    fun h0 => ⟨halm', by rw [← hmarks]; exact h0.2.1, by rw [← hmarks]; exact h0.2.2⟩
  have hcN : CanonUpTo (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r) (gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r)
      γ γ' j t :=
    CanonUpTo.scaleFam (Prop59Nodes.IsRegFam.subFam hD.isRegFam _ _) hscale
      (gamNodeScale_pos h44 hκ hκ4 (x₀ := x₀) hb n r γ)
      j t (CanonUpTo.subFam (nodePre (scheduleAt n)) j t hcanon)
  have hbase : gamNodeBase h44 hκ hκ4 (x₀ := x₀) hb n r ≤ sepSigma γ γ' := by
    refine sup_le (MeasurableSpace.generateFrom_le ?_) ?_
    · rintro _ hB
      rw [mem_singleton_iff.1 hB]
      exact iff_of_true hR0γ (hR0 hR0γ)
    · rintro _ ⟨S, -, rfl⟩
      show γ ∈ gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n r ⁻¹' S ↔ γ' ∈ gamNodeMarks h44 hκ hκ4 (x₀ := x₀) hb n r ⁻¹' S
      simp only [mem_preimage, hmarks]
  intro M hM
  exact canonQ_le_sepSigma (𝓑 := gamNodeBase h44 hκ hκ4 (x₀ := x₀) hb n r)
    (isRegFam_gamNodeCand h44 hκ hκ4 (x₀ := x₀) hb n r)
    (measurable_gamNodeStart h44 hκ hκ4 (x₀ := x₀) hb n r)
    monotone_ratGrid hstart hR0 hbase j t hR hcN M hM

end Node

end InteractingSLE.Sec5.CrossCond.StagedNTr

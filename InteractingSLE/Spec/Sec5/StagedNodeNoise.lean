/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Objects

/-!
# Proposition 5.9's node experiments: the recovered node noise and the stage objects

Packet PROVE-STAGED-NODE. PROVE-STAGED-S4's concrete stage objects `s4Objects` carry the placeholder node noise `0`.
Clause 1 of a node's killed stage law (`Wire.Night.NodeLaw`) asks that the node candidate's processes solve
Definition 2.1's equations with the candidate's noise `B`, so the noise must be the candidate's **recovered noise**
(PROVE-STAGED-REP2's `recNoise`; the processes do not read the noise parameter). Here:

* `subW`: weights of a subtree read at the full depth of the tree (`subW_add`: at depth `m + j` it is the subtree
  weight at depth `j`);
* **`nodeNoise`**: the recovered noise of the node tree's candidates (full depth, undilated), with the node words
  `stageρL κ (nodeρL κ c s)`;
* **`nodeCand_B_eq`**: the noise `B` of every node candidate (dilated subtree after the node prefix) is the recovered
  noise of that candidate's own processes, started from its own marks at time `0` (Brownian scaling of `recNoise`);
* **`nodeObjects`**: `s4Objects` with the node noise replaced by `nodeNoise`; **`rootPathOn_nodeObjects`**,
  **`nodeBaseOn_nodeObjects`**, and `rootLaterOn_nodeObjects_iff` (the root leaves do not read the node noise).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Function
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedNode

open Sec4 (IsStripGFF IsStripCounterflowDriver)
open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged Sec7.AdmCode Restart
open Prop59System Prop59Stage Prop59Pieces Prop59Nodes Prop59Sched StagedKCand StagedKill StagedRep StagedRepLater
open Wire.Night LawUnique WangWu GlueCond Word49 Prop59NodeTree StagedS4

/-! ### Subtree weights at the full depth -/

section SubW

variable {n₀ : ℕ}

/-- **The weights of a subtree read at the full depth `j'` of the tree**: the subtree weight at depth `j' − m`
(`0` above the subtree). -/
def subW (m : ℕ) (ρ : (j : ℕ) → Fin (n₀ + m + j) → ℝ) (j' : ℕ) : Fin (n₀ + j') → ℝ :=
  fun i => if h : m ≤ j' then ρ (j' - m) (Fin.cast (by omega) i) else 0

theorem dep_cast_eq (ρ : (j : ℕ) → Fin (n₀ + j) → ℝ) {a b : ℕ} (h : a = b) (i : Fin (n₀ + a)) :
    ρ a i = ρ b (Fin.cast (by omega) i) := by
  subst h
  rfl

/-- At the full depth `m + j` the subtree weights are the subtree's weights at depth `j`. -/
theorem subW_add (m : ℕ) (ρ : (j : ℕ) → Fin (n₀ + m + j) → ℝ) (j : ℕ) (i : Fin (n₀ + m + j)) :
    subW m ρ (m + j) (Fin.cast (by omega) i) = ρ j i := by
  simp only [subW, show m ≤ m + j by omega, ↓reduceDIte]
  rw [dep_cast_eq (n₀ := n₀ + m) ρ (show m + j - m = j by omega)]
  rfl

end SubW

/-! ### The recovered noise is invariant under the subtree reindexing and Brownian scaling -/

section Scale

variable {Ω : Type*} {a b : ℕ}

/-- Reindexing a weighted sum along an equality of index counts. -/
theorem sum_cast_eq (h : a = b) (ρ : Fin b → ℝ) (f : Fin b → ℝ) :
    ∑ i : Fin a, ρ (Fin.cast h i) * f (Fin.cast h i) = ∑ i : Fin b, ρ i * f i :=
  Fintype.sum_equiv (finCongr h) _ _ fun _ => rfl

/-- **Brownian scaling of the recovered noise** with reindexed marks: `c · recNoise(w, v)(u/c²)` is the recovered
noise of `(c w(·/c²), c v(·/c²))` started from `c v(0)`. -/
theorem recNoise_scale {κ : ℝ} {nL nR nL' nR' : ℕ} (hL : nL = nL') (hR : nR = nR') (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (ρL' : Fin nL' → ℝ) (ρR' : Fin nR' → ℝ) (hρL : ∀ i, ρL' (Fin.cast hL i) = ρL i)
    (hρR : ∀ k, ρR' (Fin.cast hR k) = ρR k) (w : ℝ≥0 → ℝ) (vL : Fin nL' → ℝ≥0 → ℝ) (vR : Fin nR' → ℝ≥0 → ℝ)
    (c : ℝ≥0) (u : ℝ≥0) :
    (c : ℝ) * recNoise κ ρL' ρR' (fun i => vL i 0) (fun k => vR k 0) w vL vR (u / c ^ 2) =
      recNoise κ ρL ρR (fun i => (c : ℝ) * vL (Fin.cast hL i) (0 / c ^ 2))
        (fun k => (c : ℝ) * vR (Fin.cast hR k) (0 / c ^ 2)) (fun s => (c : ℝ) * w (s / c ^ 2))
        (fun i s => (c : ℝ) * vL (Fin.cast hL i) (s / c ^ 2)) (fun k s => (c : ℝ) * vR (Fin.cast hR k) (s / c ^ 2))
        u := by
  subst hL hR
  have eL : ∀ i, ρL' i = ρL i := fun i => hρL i
  have eR : ∀ k, ρR' k = ρR k := fun k => hρR k
  simp only [recNoise, zero_div, Fin.cast_eq_self, eL, eR]
  have sL : ∑ i, ρL i * ((c : ℝ) * vL i (u / c ^ 2) - (c : ℝ) * vL i 0) =
      (c : ℝ) * ∑ i, ρL i * (vL i (u / c ^ 2) - vL i 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have sR : ∑ k, ρR k * ((c : ℝ) * vR k (u / c ^ 2) - (c : ℝ) * vR k 0) =
      (c : ℝ) * ∑ k, ρR k * (vR k (u / c ^ 2) - vR k 0) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [sL, sR]
  ring

end Scale

/-! ### The candidates' processes do not read the noise -/

section NoiseFree

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **The marks along a tree do not read its noise.** -/
theorem marks_with_noise (D : TreeData Ω nL₀ nR₀) (ν : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0), ({D with noise := ν} : TreeData Ω nL₀ nR₀).marks j t = D.marks j t
  | 0, _ => rfl
  | j + 1, t => by
    funext ω
    rw [TreeData.marks, TreeData.marks, marks_with_noise D ν j (Fin.init t)]
    rfl

end NoiseFree

section NodeNoiseFree

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
  (ν ν' : ℕ → ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ)

theorem nodeD_marks_noise (n : ℕ) (q : ℚ) :
    (nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q).marks = (nodeD x₀ h44 hκ hκ4 hb P h W ζ ν' n q).marks := by
  funext j t
  exact marks_with_noise (nodeD x₀ h44 hκ hκ4 hb P h W ζ ν' n q) (ν n q) j t

theorem nodeMarks_noise (n : ℕ) (q : ℚ) :
    nodeMarks x₀ h44 hκ hκ4 hb P h W ζ ν n q = nodeMarks x₀ h44 hκ hκ4 hb P h W ζ ν' n q := by
  unfold nodeMarks
  rw [nodeD_marks_noise x₀ h44 hκ hκ4 hb P h W ζ ν ν']

theorem nodeScale_noise (n : ℕ) (q : ℚ) :
    nodeScale x₀ h44 hκ hκ4 hb P h W ζ ν n q = nodeScale x₀ h44 hκ hκ4 hb P h W ζ ν' n q := by
  unfold nodeScale
  rw [nodeMarks_noise x₀ h44 hκ hκ4 hb P h W ζ ν ν']

theorem nodeD_cand_VL_noise (n : ℕ) (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) :
    ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q).cand j t).VL = ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν' n q).cand j t).VL := by
  show arcVL _ _ _ _ (fun ω => ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q).marks j t ω).1) =
    arcVL _ _ _ _ (fun ω => ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν' n q).marks j t ω).1)
  rw [nodeD_marks_noise x₀ h44 hκ hκ4 hb P h W ζ ν ν']
  rfl

theorem nodeD_cand_VR_noise (n : ℕ) (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) :
    ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q).cand j t).VR = ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν' n q).cand j t).VR := by
  show arcVR _ _ _ _ (fun ω => ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν n q).marks j t ω).2) =
    arcVR _ _ _ _ (fun ω => ((nodeD x₀ h44 hκ hκ4 hb P h W ζ ν' n q).marks j t ω).2)
  rw [nodeD_marks_noise x₀ h44 hκ hκ4 hb P h W ζ ν ν']
  rfl

end NodeNoiseFree

/-! ### The recovered node noise -/

section Noise

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa]
  (P : Measure Ω) (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- The node tree of the node `n` at the counterflow time `q` with the noise `0`. -/
abbrev nodeD0 (n : ℕ) (q : ℚ) :
    TreeData Ω (rootNL (sourceWord (x₀ := x₀) hκ hb)) (rootNR (sourceWord (x₀ := x₀) hκ hb)) :=
  nodeD x₀ h44 hκ hκ4 hb P h W ζ (fun _ _ _ _ _ _ => 0) n q

/-- The left node weights at the full depth `j'` of the node tree of `n`. -/
abbrev nodeWL (n j' : ℕ) : Fin (rootNL (sourceWord (x₀ := x₀) hκ hb) + j') → ℝ :=
  subW (nodeLen (scheduleAt n)) (fun j => stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) j'

/-- The right node weights at the full depth `j'` of the node tree of `n`. -/
abbrev nodeWR (n j' : ℕ) : Fin (rootNR (sourceWord (x₀ := x₀) hκ hb) + j') → ℝ :=
  subW (nodeLen (scheduleAt n)) (fun j => stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) j'

/-- **The recovered noise of the node candidates** (full depth `j'` of the node tree of `n`, undilated): the noise
that makes the candidate's processes solve Definition 2.1's equations with the node word. The candidate's
processes do not read the noise parameter, so it is defined from the node tree with noise `0`. -/
def nodeNoise (n : ℕ) (q : ℚ) (j' : ℕ) (t' : Fin j' → ℝ≥0) (u : ℝ≥0) (ω : Ω) : ℝ :=
  recNoise κ (nodeWL x₀ hκ hb n j') (nodeWR x₀ hκ hb n j')
    (fun i => ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand j' t').VL i 0 ω)
    (fun k => ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand j' t').VR k 0 ω)
    (fun s => ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand j' t').W s ω)
    (fun i s => ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand j' t').VL i s ω)
    (fun k s => ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand j' t').VR k s ω) u

omit [MeasurableSpace Ωa] in
/-- **The node candidates' noise is their recovered noise**: for every node `n`, time `q`, list `(j, t)` and sample,
the noise of the node candidate (the dilated subtree after the node prefix) is the recovered noise of its own
processes with the node word at depth `j`, started from its own marks at time `0`. -/
theorem nodeCand_B_eq (n : ℕ) (q : ℚ) (j : ℕ) (t : Fin j → ℝ≥0) (u : ℝ≥0) (ω' : Ω × Ωa) :
    (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q j t).B u ω' =
      recNoise κ (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j)
        (fun i => (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q j t).VL i 0 ω')
        (fun k => (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q j t).VR k 0 ω')
        (fun s => (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q j t).W s ω')
        (fun i s =>
          (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q j t).VL i s ω')
        (fun k s =>
          (nodeCand (Ωa := Ωa) x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) n q j t).VR k s ω')
        u := by
  have hL : rootNL (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j) =
      rootNL (sourceWord (x₀ := x₀) hκ hb) + nodeLen (scheduleAt n) + j := by omega
  have hR : rootNR (sourceWord (x₀ := x₀) hκ hb) + (nodeLen (scheduleAt n) + j) =
      rootNR (sourceWord (x₀ := x₀) hκ hb) + nodeLen (scheduleAt n) + j := by omega
  have hrec := recNoise_scale (κ := κ) hL.symm hR.symm
    (stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb) (scheduleAt n)) j) (stageρR κ (nodeρR κ (sourceWord (x₀ := x₀)
        hκ hb) (scheduleAt n)) j)
    (nodeWL x₀ hκ hb n (nodeLen (scheduleAt n) + j)) (nodeWR x₀ hκ hb n (nodeLen (scheduleAt n) + j))
    (fun i => subW_add (nodeLen (scheduleAt n)) (fun j => stageρL κ (nodeρL κ (sourceWord (x₀ := x₀) hκ hb)
        (scheduleAt n)) j) j i)
    (fun k => subW_add (nodeLen (scheduleAt n)) (fun j => stageρR κ (nodeρR κ (sourceWord (x₀ := x₀) hκ hb)
        (scheduleAt n)) j) j k)
    (fun s => ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre
        (scheduleAt n)) t)).W s ω'.1)
    (fun i s =>
      ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n))
          t)).VL i s ω'.1)
    (fun k s =>
      ((nodeD0 x₀ h44 hκ hκ4 hb P h W ζ n q).cand (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n))
          t)).VR k s ω'.1)
    (nodeScale x₀ h44 hκ hκ4 hb P h W ζ (fun _ _ _ _ _ _ => 0) n q ω'.1) u
  have hs := nodeScale_noise x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ) (fun _ _ _ _ _ _ => 0) n q
  have hVL := nodeD_cand_VL_noise x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ)
    (fun _ _ _ _ _ _ => 0) n q (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)
  have hVR := nodeD_cand_VR_noise x₀ h44 hκ hκ4 hb P h W ζ (nodeNoise x₀ h44 hκ hκ4 hb P h W ζ)
    (fun _ _ _ _ _ _ => 0) n q (nodeLen (scheduleAt n) + j) (Fin.append (nodePre (scheduleAt n)) t)
  simp only [nodeCand, liftFam, liftPiece, scaleFam, scalePiece, subFam, reindexPiece, hs, hVL, hVR]
  exact hrec

end Noise

/-! ### The stage objects with the recovered node noise -/

/-- **Concrete stage objects with the recovered node noise**: PROVE-STAGED-S4's `s4Objects` (noise space `(ℝ, δ₀)`,
the recovered root noise, node bases `⊥`) with the node noise `nodeNoise`. -/
def nodeObjects (h44 : Theorem12ParamCond44Statement.{0}) : StageObjectsOn :=
  fun {_ x₀ _ _ _ _} hκ hκ4 hb {_} _ _ P _ h W ζ _ _ _ _ =>
    { Ωa := ℝ
      measure := Measure.dirac 0
      rootNoise := rootNoise x₀ h44 hκ hκ4 hb P h W ζ
      nodeNoise := nodeNoise x₀ h44 hκ hκ4 hb P h W ζ
      nodeBase := fun _ _ => ⊥ }

/-- **The node-base leaf** for the stage objects with the recovered node noise. -/
theorem nodeBaseOn_nodeObjects (h44 : Theorem12ParamCond44Statement.{0}) : NodeBaseOn h44 (nodeObjects h44) := by
  intro κ x₀ a b a' b' hκ hκ4 hb Ω _ _ P _ h W ζ γ hG hcf htr d n q
  exact (bot_le : (⊥ : MeasurableSpace (Ω × ℝ)) ≤ _)

/-- **The root path leaf** for the stage objects with the recovered node noise (the root path clause does not read
the node noise: PROVE-STAGED-S4's `rootPathOn_s4Objects`). -/
theorem rootPathOn_nodeObjects (h44 : Theorem12ParamCond44Statement.{0}) (hA : PartAInputsSixteenDivOfClearance) :
    RootPathOn h44 (nodeObjects h44) :=
  rootPathOn_s4Objects h44 hA

/-- The later-root leaf does not read the node noise: it holds for `nodeObjects` iff it holds for `s4Objects`. -/
theorem rootLaterOn_nodeObjects_iff (h44 : Theorem12ParamCond44Statement.{0}) :
    RootLaterOn h44 (nodeObjects h44) ↔ RootLaterOn h44 (s4Objects h44) :=
  Iff.rfl

end InteractingSLE.Sec5.CrossCond.StagedNode

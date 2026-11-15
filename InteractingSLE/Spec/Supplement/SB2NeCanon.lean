/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NeHull
import InteractingSLE.Spec.Supplement.SB2NdVer
import InteractingSLE.Spec.Supplement.SB2JyEnd
import InteractingSLE.Spec.Supplement.SB2QxHull

/-!
# The canonical relative curve pulls back to the joint fill; B's capped stage set

Packet PROVE-AUX61-NOJUMP (round 22, component D), deterministic.

* **`mem_closure_goodU`**: good relative times are dense (`Nc.exists_rat_good`);
* **`inv_canonCurve_eq`**: where the canonical curve is in `ℍ`, the inverse chart reads the piece back;
* **`H_diff_fillH_union_canon`**: `ℍ ∖ fill (X ∪ p[0, cTime U]) = Φ⁻¹(ℍ ∖ fill canonCurve[0, U])`;
* **`tipSet_stopped_launch`**: a launched piece stopped at `S ≤ ζ` has physical set `pcPt[0, S]`;
* **`stageSet_capSpec_succ_eq`**: B's capped stage set through `ℓ` is the stage set before `ℓ` and `pcPt[0, min τ ζ]`
  (in `ℍ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Ne

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C LuM GW1W GW1Bookkeep Lk Dv
  WalkSide

/-! ### The canonical curve -/

section Canon

variable {X : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}

/-- **Good relative times are dense.** -/
theorem mem_closure_goodU (hXo : IsOpen (H \ fillH X)) (hL : L ≠ 0) (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L})
    (hdr : IsDrivenCurve (canonCurve X x₀ p L)) {v : ℝ} (hv : 0 ≤ v) :
    v ∈ closure {v' : ℝ | 0 ≤ v' ∧ Nc.cTime L v' ∈ canonGood X p L} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨q, -, hqd, hqg⟩ := Nc.exists_rat_good hXo hL hpc hdr v.toNNReal hε
  refine ⟨((q : ℝ).toNNReal : ℝ), ⟨NNReal.coe_nonneg _, hqg⟩, ?_⟩
  rw [dist_comm]
  have e : dist (((q : ℝ).toNNReal : ℝ)) v = dist ((q : ℝ).toNNReal) v.toNNReal := by
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hv, Real.dist_eq]
  rw [e]; exact hqd

/-- **The canonical curve at a good time is the chart image.** -/
theorem canonCurve_eq_fwd (hL : L ≠ 0) {v : ℝ} (hv : 0 ≤ v) (hd : p (Nc.cTime L v) ∈ H \ fillH X) :
    canonCurve X x₀ p L v = (Mo.hullChart (fillH X) x₀).1 (p (Nc.cTime L v)) := by
  classical
  rw [Nc.canonCurve_eq]
  have hg : Nc.cTime L v ∈ canonGood X p L := ⟨Nc.cTime_le hL hv, hd⟩
  unfold canonVal
  simp only [hg, ↓reduceIte]

/-- **The inverse chart reads the piece back** wherever the canonical curve is in `ℍ`. -/
theorem inv_canonCurve_eq (hA : IsHPHull (fillH X)) (hL : L ≠ 0) (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L})
    (hdr : IsDrivenCurve (canonCurve X x₀ p L)) {v : ℝ} (hv : 0 ≤ v) (hH : canonCurve X x₀ p L v ∈ H) :
    (Mo.hullChart (fillH X) x₀).2.1 (canonCurve X x₀ p L v) = p (Nc.cTime L v) := by
  set G : Set ℝ := {v' : ℝ | 0 ≤ v' ∧ Nc.cTime L v' ∈ canonGood X p L} with hG
  have hcl := mem_closure_goodU (x₀ := x₀) hA.2.2.1 hL hpc hdr hv
  have : (𝓝[G] v).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hGs : G ⊆ Ici 0 := fun v' hv' => hv'.1
  have h1 : Tendsto (canonCurve X x₀ p L) (𝓝[G] v) (𝓝 (canonCurve X x₀ p L v)) :=
    (hdr.continuousOn v hv).tendsto.mono_left (nhdsWithin_mono _ hGs)
  have h2 : Tendsto (fun v' => (Mo.hullChart (fillH X) x₀).2.1 (canonCurve X x₀ p L v')) (𝓝[G] v)
      (𝓝 ((Mo.hullChart (fillH X) x₀).2.1 (canonCurve X x₀ p L v))) :=
    ((continuousOn_hullChart_inv hA x₀).continuousAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hH)).tendsto.comp h1
  have h3 : Tendsto (fun v' => p (Nc.cTime L v')) (𝓝[G] v) (𝓝 (p (Nc.cTime L v))) := by
    have hct : Tendsto (Nc.cTime L) (𝓝[G] v) (𝓝 (Nc.cTime L v)) :=
      (Nc.continuousOn_cTime v hv).tendsto.mono_left (nhdsWithin_mono _ hGs)
    have hev : ∀ᶠ v' in 𝓝[G] v, Nc.cTime L v' ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L} :=
      eventually_nhdsWithin_of_forall fun v' hv' => Nc.cTime_le hL hv'.1
    exact (hpc _ (Nc.cTime_le hL hv)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hct, hev⟩)
  have h4 : ∀ v' ∈ G, (Mo.hullChart (fillH X) x₀).2.1 (canonCurve X x₀ p L v') = p (Nc.cTime L v') := by
    intro v' hv'
    rw [canonCurve_eq_fwd hL hv'.1 hv'.2.2]
    exact (hullChart_fwd_spec hA x₀ hv'.2.2).2
  exact tendsto_nhds_unique (h2.congr' (eventually_nhdsWithin_of_forall h4)) h3

/-- **The canonical relative curve pulls back to the joint fill.** -/
theorem H_diff_fillH_union_canon (hXc : IsCompact X) (hA : IsHPHull (fillH X)) (hL : L ≠ 0)
    (hpc : ContinuousOn p {t | (t : ℝ≥0∞) ≤ L}) (hdr : IsDrivenCurve (canonCurve X x₀ p L)) {U : ℝ} (hU : 0 ≤ U) :
    H \ fillH (X ∪ p '' Icc 0 (Nc.cTime L U)) =
      (Mo.hullChart (fillH X) x₀).2.1 '' (H \ fillH (canonCurve X x₀ p L '' Icc 0 U)) := by
  have hI : IsCompact (Icc (0 : ℝ) U) := isCompact_Icc
  have hpc' : ContinuousOn (fun v => p (Nc.cTime L v)) (Icc 0 U) :=
    hpc.comp (Nc.continuousOn_cTime.mono Icc_subset_Ici_self) fun v hv => Nc.cTime_le hL hv.1
  have h := H_diff_fillH_union_eq hXc hA x₀ hI hpc' (hdr.continuousOn.mono Icc_subset_Ici_self)
    (fun v hv hH => inv_canonCurve_eq hA hL hpc hdr hv.1 hH) fun v hv hd => canonCurve_eq_fwd hL hv.1 hd
  have e : (fun v => p (Nc.cTime L v)) '' Icc 0 U = p '' Icc 0 (Nc.cTime L U) := by
    rw [show (fun v => p (Nc.cTime L v)) = p ∘ Nc.cTime L from rfl, image_comp, Nc.image_cTime_Icc hL hU]
  rw [← e]; exact h

end Canon

/-! ### B's capped stage set -/

section Stage

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A launched piece stopped at `S ≤ ζ`** has physical set `pcPt[0, S]`. -/
theorem tipSet_stopped_launch {D : ℕ → Drv} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    {S : ℝ≥0∞} (hS : S ≤ (D n).2) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n).2.2.2.2.1.tipSet
        (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) S).toNNReal) S =
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S} := by
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hcc := isConformal_runChart_of_reg (boundaryWalkSpec b jumps θ true) hP n
  have hcb := (GW1P.isClosed_pieces_run (boundaryWalkSpec b jumps θ true) D hP n).1
  obtain ⟨g, -, -, -, hgt⟩ := Lw.exists_bdryMap_of_hasProperBdryExt hcc hcb
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) t).im := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hval : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t = g (trOf (D n) t) :=
    fun t ht => bdVal_eq_of_tendsto (hαH t ht) (hgt _ (hαH t ht))
  have hgen : IsGeneratingTrace (D n).1 S (trOf (D n)) := by
    have := WalkInf.isGeneratingTrace_min hα S
    rwa [min_eq_left hS] at this
  have hWc : ContinuousOn (D n).1 {t | (t : ℝ≥0∞) ≤ S} := hPR.2.1.mono fun t ht => le_trans ht hS
  rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hgen hWc hPR.1 fun t ht => hgt _ (hαH t (ht.trans hS)),
    image_image]
  exact (image_congr fun t ht => hval t (le_trans ht hS)).symm

/-- **B's capped stage set through `ℓ`** is the stage set before `ℓ` and the piece's points up to `min τ ζ`. -/
theorem stageSet_capSpec_succ_eq {Ω : Type*} {E : ℕ → Ω → Drv} {ω : Ω}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) fun j => E j ω) {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none)
    (τ : ℝ≥0∞) :
    WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps θ true) ℓ θ τ) E (ℓ + 1) ω =
      WalkLaw.stageSet κ b jumps (boundaryWalkSpec b jumps θ true) E ℓ ω ∪
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) (fun j => E j ω) ℓ) (E ℓ ω) ''
          {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min τ (E ℓ ω).2} ∩ H := by
  obtain ⟨-, hlen⟩ := Qx.walk_instr_of_launch hl
  rw [WalkLaw.stageSet_succ, WalkInf.stageSet_capSpec_of_le hlen.le ω le_rfl, Qx.pieceSet_capSpec_eq κ b jumps hl,
    tipSet_stopped_launch (D := fun j => E j ω) hP hl (min_le_right _ _)]

end Stage

end InteractingSLE.Theorem14.SB.Ne

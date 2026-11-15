/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Supplement.SBLuDense
import InteractingSLE.Spec.Supplement.SBLxStep
import InteractingSLE.Spec.Supplement.SBLxWalk

/-!
# The run-chart domain identity for walks

Packet PROVE-T14-SB2LIFT (round 6, step (i-d) of handoff §R6.2). For a boundary walk (`boundaryWalkSpec`) run with
regular launches, as long as every launched piece has a finite lifetime, the inverse run chart maps `ℍ` onto the
unbounded domain of the physical prefix:

  `(stChart (run n)).2.1 '' ℍ = ℍ \ fill (prefixPhysSet n)`.

**`image_runChart_walk`** carries a compact set `K` that agrees with the prefix off the real line. Connectors are
real, so they change neither `ℍ \ ·` nor the filling (`fillH_eq_of_union_im`). Steps:

* a step without a launch recentres the chart by a real number: `chart_run_succ_of_noLaunch`, image unchanged;
* at a launch the chart is the Loewner chart of the stopped driver: `chart_launch`, `RS.image_fwdMapInv_H`. Its hull
  at the lifetime is the filling of the closed trace (`fwdHull_eq_fillH_horizon`). Lemma (T)
  (`image_H_diff_fillH_of_chart`) moves it through the old chart. The new physical piece is the image of the closed
  trace under the old chart's boundary map (`Lx.prefixPhysSet_succ_eq_image`).

**`image_runChart_walk_eq`** is the corollary in terms of `prefixPhysSet`. After a launch with infinite lifetime the
chart is no longer updated while the prefix grows, so the identity is stated up to the first such launch.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

/-- **Real points do not change the filling.** -/
theorem fillH_eq_of_union_im {K K' : Set ℂ} (h : K ∪ {z : ℂ | z.im = 0} = K' ∪ {z : ℂ | z.im = 0}) :
    fillH K = fillH K' := by
  have hR : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have hRH : ∀ z ∈ H, z ∉ {z : ℂ | z.im = 0} := fun z hz h => by
    have : (0 : ℝ) < z.im := hz
    rw [show z.im = 0 from h] at this
    exact lt_irrefl _ this
  have key : ∀ S : Set ℂ, closure S ∩ H = closure (S ∪ {z : ℂ | z.im = 0}) ∩ H := fun S => by
    rw [closure_union, hR.closure_eq]
    ext z
    simp only [mem_inter_iff, mem_union]
    exact ⟨fun h => ⟨Or.inl h.1, h.2⟩, fun h => ⟨h.1.resolve_right (hRH z h.2), h.2⟩⟩
  exact fillH_congr (by rw [key K, key K', h])

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- **The run-chart domain identity for walks** (with a compact set agreeing with the prefix off `ℝ`). -/
theorem image_runChart_walk {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) :
    ∀ n, (∀ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤) →
      ∃ K : Set ℂ, IsCompact K ∧
        K ∪ {z : ℂ | z.im = 0} =
          SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n ∪ {z : ℂ | z.im = 0} ∧
        (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1 '' H = H \ fillH K
  | 0, _ => by
    refine ⟨{(0 : ℂ)}, isCompact_singleton, ?_, ?_⟩
    · simp [SB.prefixPhysSet, ExplState.run, ExplState.init, boundaryWalkSpec]
    · have h0 : fillH ({(0 : ℂ)} : Set ℂ) = ∅ :=
        YuanCharacterisation.fillH_eq_empty_of_subset fun z hz => by
          rw [mem_singleton_iff.1 hz]
          simp
      rw [h0, sdiff_empty]
      ext z
      simp [ExplState.run, ExplState.init, Chart.id, Chart.recenter, boundaryWalkSpec]
  | n + 1, hfin => by
    classical
    obtain ⟨K, hK, hKR, himg⟩ := image_runChart_walk hP n fun j hj => hfin j (Nat.lt_succ_of_lt hj)
    have hstep := prefixPhysSet_succ_walk hP n
    have harcR : ((↑) : ℝ → ℂ) '' GW2aCont.arcAt κ b jumps (boundaryWalkSpec b jumps θ right) D n ⊆
        {z : ℂ | z.im = 0} := by
      rintro _ ⟨x, -, rfl⟩
      simp
    rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · -- no launch: the chart is recentred, the prefix grows by a real connector
      have hnp : newPiece κ b jumps θ right D n = ∅ := by
        ext z
        simp only [newPiece, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun h => absurd hl h
      obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps)
        (boundaryWalkSpec b jumps θ right) D hl
      refine ⟨K, hK, ?_, ?_⟩
      · rw [hstep, hnp, union_empty, hKR, union_assoc, union_eq_right.2 harcR]
      · show (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.2.1.2.1 '' H = _
        rw [ha, ← himg]
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨z + a, show 0 < (z + a).im by simpa using (show (0 : ℝ) < z.im from hz), rfl⟩
        · rintro ⟨z, hz, rfl⟩
          refine ⟨z - a, show 0 < (z - a).im by simpa using (show (0 : ℝ) < z.im from hz), ?_⟩
          show (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1 (z - a + a) = _
          rw [sub_add_cancel]
    · -- a launch with a finite lifetime
      set spec := boundaryWalkSpec b jumps θ right with hspec
      set s₀ := ExplState.run κ b jumps spec D n with hs₀
      have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
      have hPR := pieceRegular_of_launch hP hlne
      have hfinn : (D n).2 ≠ ⊤ := hfin n (Nat.lt_succ_self n) hlne
      obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
      have hmin : min (⊤ : ℝ≥0∞) (D n).2 = (D n).2 := min_eq_right le_top
      have hch := chart_launch s₀ n (D n) θ' ⊤ (by rw [hmin]; exact hfinn)
      rw [hmin] at hch
      set T : ℝ≥0 := (D n).2.toNNReal with hTdef
      have hT : ((T : ℝ≥0) : ℝ≥0∞) = (D n).2 := ENNReal.coe_toNNReal hfinn
      set w : ℝ≥0 → ℝ := fun r => (D n).1 (min (r : ℝ≥0∞) (D n).2).toNNReal with hwdef
      have hwc : Continuous w := CounterflowRange.continuous_stopped hPR.2.1
      have hw0 : w 0 = 0 := by
        have := hPR.continuous_stoppedReal.2
        simpa [hwdef] using this
      set α := trOf (D n) with hαdef
      have hα := isGeneratingTrace_trOf hPR
      have hαs : IsGeneratingTrace w (T : ℝ≥0∞) α := by
        rw [hT]
        exact CounterflowRange.isGeneratingTrace_stopped hα
      have hhull := fwdHull_eq_fillH_horizon hwc hw0 hαs
      have hW : Continuous (fun s : ℝ => w s.toNNReal) := hwc.comp continuous_real_toNNReal
      have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa using hw0
      have himgL := QuantumZipper.RS.image_fwdMapInv_H hW hW0 T.coe_nonneg
      -- the old chart and its boundary map
      have hcc := isConformal_runChart_of_reg spec hP n
      obtain ⟨hbe, -⟩ := GW1P.isClosed_pieces_run spec D hP n
      obtain ⟨f, C, hf, hC⟩ := hbe
      have hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im} := GW1P.continuousOn_of_tendsto hf
      have hfeq : EqOn f (stChart s₀).2.1 H := fun z hz => by
        have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
        exact tendsto_nhds_unique (hf z (QuantumZipper.H_subset_Hbar hz))
          ((hcc.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left
            nhdsWithin_le_nhds)
      have hinj : InjOn (stChart s₀).2.1 H := fun z hz z' hz' h => by
        rw [← hcc.2.2 z hz, h, hcc.2.2 z' hz']
      have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (α t).im := fun t ht =>
        im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
      have hIcc : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (D n).2} = Icc 0 T := by
        ext t
        simp only [mem_ofPred_eq, mem_Icc, zero_le, true_and]
        rw [← hT, ENNReal.coe_le_coe]
      have hAc : IsCompact (α '' Icc 0 T) := isCompact_Icc.image_of_continuousOn
        (hα.2.1.mono fun t ht => by rw [← hT]; exact ENNReal.coe_le_coe.2 ht.2)
      have hAH : α '' Icc 0 T ⊆ Hbar := by
        rintro _ ⟨t, ht, rfl⟩
        exact hαH t (by rw [← hT]; exact ENNReal.coe_le_coe.2 ht.2)
      have hTT := image_H_diff_fillH_of_chart hcc.1 hinj hfc (hfeq.mono subset_rfl) hC hK himg hAc hAH
      have hpre := Lx.prefixPhysSet_succ_eq_image D hlne hfc hfeq hα hPR.2.1 hPR.1 hαH
      rw [hIcc] at hpre
      refine ⟨K ∪ f '' (α '' Icc 0 T), hK.union (hAc.image_of_continuousOn (hfc.mono hAH)), ?_, ?_⟩
      · rw [hpre, union_right_comm, hKR, union_right_comm]
      · show (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.2.1 '' H = _
        rw [he, hch, ← hTT, ← hhull, ← himgL, image_image]
        rfl

/-- **The run-chart domain identity for walks**: up to the first launch with an infinite lifetime, the inverse run
chart maps `ℍ` onto `ℍ \ fill (prefixPhysSet n)`. -/
theorem image_runChart_walk_eq {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ right) D) {n : ℕ}
    (hfin : ∀ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤) :
    (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)).2.1 '' H =
      H \ fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D n) := by
  obtain ⟨K, -, hKR, himg⟩ := image_runChart_walk hP n hfin
  rw [himg, fillH_eq_of_union_im hKR]

end InteractingSLE.Theorem14.SB.Lk

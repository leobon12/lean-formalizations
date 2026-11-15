/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XbLock
import InteractingSLE.Spec.Supplement.SB2XzArc

/-!
# (L1) and `FillCorr` inside the lockstep, connector form

Packet PROVE-T14-SB2LIFT (round 30; the corrected T bundle, handoff §R29.3): `l1_fillCorr_of_liftsW`.
The statements and proofs are those of the landed originals, with `tail` replaced by its connector form
`TailArc` (`SB2XzArc`); the full `tail` is false (handoff §R29.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

/-- **(L1) and the fill correspondence at every pair of corresponding launches, from the lifts.** The hypotheses are
those of `stCorr_run_strong2` without `hL1` and `hF`, together with the piece lifts, the per-time lifts of the finite
pieces, the actual walk's chain facts, the curve data and the lift identity of the start states. -/
theorem l1_fillCorr_of_liftsW (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (o a₀ i₀ N : ℕ) (ha₀ : a₀ ≤ i₀) (hi₀N : i₀ ≤ N)
    (hfin₁ : ∀ j, j + 1 < N + o → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none
        → (D₁ j).2 ≠ ⊤)
    (hfin₂₀ : ∀ j, j < i₀ → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none → (D₂
        j).2 ≠ ⊤)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hlm₂₀ : ∀ j, j < i₀ → NoLeftMove κ b₂ J₂ θ D₂ j) (hlh₂₀ : ∀ j, j < i₀ → NoLeftHit κ b₂ J₂ θ D₂ j)
    (hinv₀ : InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hallow : ∀ k, i₀ + o ≤ k → AllowedSt κ b₁ (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k))
    (hexit₁ : ∀ k, i₀ + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ ⊤ → (D₁ k).2 ≠ 0 →
      ∃ x : ℝ, stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) < x ∧ lHit (stChart (ExplState.run
          κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k)) ⊤ (D₁ k) x)
    (hpar : o % 2 = 0) (hi₀ : i₀ % 2 = 0)
    (hlen : ∀ i, a₀ ≤ i → i < N → i + o < (boundaryWalkSpec b₁ J₁ θ true).2.2.length ∧
      i < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
    (hNlen : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hnz₁ : ∀ k, i₀ + o ≤ k → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none →
        (D₁ k).2 ≠ 0)
    (hp₀ : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))) (hs₀ : FlowSt R
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o))) (h₀ : StCorr ι R (ExplState.run κ b₁ J₁
        (boundaryWalkSpec b₁ J₁ θ true) D₁ (i₀ + o)) (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i₀))
    (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁) (hβ : Supp9B.IsProperCurve β₀) (hγp : Supp9B.IsProperCurve γ)
    (hD : LiftCurveData β₀ γ tL R ι)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβ0 : β₀ 0 = 0)
    (hhead : ∀ t ≤ tL, ∀ x : ℝ, β₀ t = x → x ≤ R) (htail : TailArc κ θ b₁ J₁ D₁ R β₀ tL)
    (hRmem : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (a₀ + o))
    (hca₀ : StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (a₀ + o)) (ExplState.run κ b₂ J₂
        (boundaryWalkSpec b₂ J₂ θ true) D₂ a₀))
    (hstart : statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ a₀) =
      liftImage β₀ tL γ (statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (a₀ + o))))
    (hpre : ∀ i, a₀ ≤ i → i < i₀ → StCorr ι R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) →
      StepOK κ θ b₁ J₁ R ι R (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i) ∧
        StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i +
            o)) (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (hpc : ∀ i, i₀ ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0) (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i +
          o)) (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + o)) (D₂ i))
    (htr : ∀ i, i₀ ≤ i → i < N → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i +
        o) ≠ none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ (i + o)).2 ≠ ⊤ →
      (∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ (i + o)) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ i) ∧
        bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) '' (trOf (D₂ i) '' Icc 0
            r'.toNNReal) =
          liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) ''
              (trOf (D₁ (i + o)) '' Icc 0 r.toNNReal))) ∧
      (∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ i) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ (i + o)) ∧
        bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i)) '' (trOf (D₂ i) '' Icc 0
            r'.toNNReal) =
          liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o))) ''
              (trOf (D₁ (i + o)) '' Icc 0 r.toNNReal)))) :
    (∀ i, i₀ ≤ i → i < N → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠
        none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0)) ∧
    (∀ i, i₀ ≤ i → i < N → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠
        none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
      (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι) := by
  have key : ∀ M, i₀ ≤ M → M ≤ N →
      (∀ i, i₀ ≤ i → i < M → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠
          none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
        ((D₂ i).2 = ⊤ ↔ (D₁ (i + o)).2 = ⊤) ∧ ((D₂ i).2 = 0 ↔ (D₁ (i + o)).2 = 0)) ∧
      (∀ i, i₀ ≤ i → i < M → (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + o + 1)).2.2.2.1 (i + o) ≠
          none → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (i + 1)).2.2.2.1 i ≠ none →
        (D₁ (i + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (i + o) b₂ J₂ D₂ i ι) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => intro _; exact ⟨fun i h1 h2 => absurd h2 (by omega), fun i h1 h2 => absurd h2 (by omega)⟩
    | succ M hM ih =>
      intro hMN
      obtain ⟨hL1M, hFM⟩ := ih (by omega)
      have hMlen := hlen M (by omega) (by omega)
      obtain ⟨hcM, hokM, hlm₂M, hlh₂M, -⟩ := stCorr_run_strong2 hι hcont le_rfl hP₁ hP₂ hreg₂ o i₀ M
        (fun j hj => hfin₁ j (by omega)) hfin₂₀ hlm₁ hlh₁ hlm₂₀ hlh₂₀ hinv₀ hallow hexit₁ hpar hi₀
        (fun i h1 h2 => hlen i (by omega) (by omega)) hMlen.1.le hnz₁ hp₀ hs₀ h₀ hL1M hFM M hM le_rfl
      have hstageM : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o + 1)).2.2.2.1 (M + o) ≠ none →
          (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (M + 1)).2.2.2.1 M ≠ none →
          (((D₂ M).2 = ⊤ ↔ (D₁ (M + o)).2 = ⊤) ∧ ((D₂ M).2 = 0 ↔ (D₁ (M + o)).2 = 0)) ∧
          ((D₁ (M + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (M + o) b₂ J₂ D₂ M ι) := by
        intro hl₁ hl₂
        obtain ⟨hev₂, hk₂⟩ := GW1W.even_of_launches_walk hl₂
        have hev₁ : (M + o) % 2 = 0 := by omega
        obtain ⟨hRa, hflM, -⟩ := status_run_le hP₁ (i₀ + o) (N + o) hfin₁ hlm₁ hlh₁ hNlen (by omega) hnz₁ hp₀ hs₀
          (M + o) (by omega) (by omega)
        have hc := hcM M hM le_rfl
        have hst₂ := arcM_of_corr_launch hc hk₂ hev₂ (hflM hev₁) hl₂
        have hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) = GW1W.stArcM true :=
            hc.2.1.symm.trans hst₂
        have hadm := admissible_of_launched_arcM hMlen.1 hev₁ hst₁ hl₁
        have hLR : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) (D₁ (M +
            o))) (newPc (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) (D₂ M)) :=
          hpc M hM (by omega) (decide_eq_true hev₂) hst₁ hadm
        obtain ⟨⟨c₁, θ₁⟩, hl₁'⟩ := Option.ne_none_iff_exists'.1 hl₁
        obtain ⟨⟨c₂, θ₂⟩, hl₂'⟩ := Option.ne_none_iff_exists'.1 hl₂
        have hpr₁ := pieceRegular_of_launch hP₁ hl₁
        have hpr₂ := pieceRegular_of_launch hP₂ hl₂
        have hrange : (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) (D₁ (M + o))).1.tipSet
            (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) (D₁ (M + o))).2.1
            (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) (D₁ (M + o))).2.2 ⊆ range β₀ := by
          rw [hβr]
          refine Subset.trans ?_ (prefix_subset_physSet D₁ (n := M + o + 1) (by omega))
          rw [prefixPhysSet_succ_of_launch hl₁']
          exact subset_union_right
        have htop : (D₂ M).2 = ⊤ ↔ (D₁ (M + o)).2 = ⊤ :=
          top_iff_of_liftRel' hβ hγp (GW1P.isClosed_pieces_run _ D₁ hP₁ (M + o)).1
            (GW1P.isClosed_pieces_run _ D₂ hP₂ M).1 (by rw [min_top_left]; exact hpr₁)
            (by rw [min_top_left]; exact hpr₂) hrange hLR
        have hnz := hnz₁ (M + o) (by omega) hl₁
        have hF : (D₁ (M + o)).2 ≠ ⊤ → FillCorr κ θ b₁ J₁ D₁ (M + o) b₂ J₂ D₂ M ι := by
          intro hfin
          have hfin₂ : (D₂ M).2 ≠ ⊤ := fun h => hfin (htop.1 h)
          obtain ⟨htr₁, htr₂⟩ := htr M hM (by omega) hl₁ hl₂ hfin
          have hfin₂M : ∀ j, j < M → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠
              none → (D₂ j).2 ≠ ⊤ := by
            intro j hj hlj
            by_cases hji : j < i₀
            · exact hfin₂₀ j hji hlj
            · have hjM : j + 1 < M := by
                obtain ⟨hevj, -⟩ := GW1W.even_of_launches_walk hlj
                omega
              exact fin_rel_of_corr hι le_rfl hP₁ o i₀ M (fun j hj => hfin₁ j (by omega)) hlm₁ hlh₁ hpar hi₀
                (fun i h1 h2 => hlen i (by omega) (by omega)) hMlen.1.le hnz₁ hp₀ hs₀ hL1M (by omega) hjM
                (hcM j (by omega) (by omega)) hlj
          have hrec₂ : ∀ k, k ≤ M → RecInv κ b₂ J₂ θ D₂ k := fun k hk =>
            (recInv_ptRec_run_le' hP₂ hfin₂M hlm₂M hlh₂M k hk).1
          have hrec₁ := recInv_of_not_done hP₁ hlm₁ hlh₁ (WalkIntRunChron.not_done_of_launch _ D₁ hl₁')
          have hacc := accCorr_run_of_steps (L := LiftRel β₀ tL γ) hι le_rfl o a₀ M hpar
            (fun i h1 h2 => hlen i h1 (by omega)) hca₀ (fun i h1 h2 hci => by
              rcases Nat.lt_or_ge i i₀ with hi | hi
              · exact hpre i h1 hi hci
              · exact ⟨hokM i hi h2, hpc i hi (by omega)⟩) M (by omega) le_rfl
          have hstage : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M =
              liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)) := by
            show statePhysicalSet 0 (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) = liftImage β₀ tL γ
                (statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o)))
            refine statePhysicalSet_eq_liftImage_of_accCorr hacc hstart fun X hX a ha => ?_
            refine liftImage_ofRealW hβ.2.1 hD.base hD.zero hι.map_base hhead
              (htail.of_mem (n := M + o) (hX ▸ List.mem_append_right _ ha)) hD.ray fun x hx _ => ?_
            rw [hβr]
            refine prefix_subset_physSet D₁ (n := M + o) hMlen.1.le ?_
            show (x : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))
            exact Or.inr (mem_iUnion₂.2 ⟨a, hX ▸ List.mem_append_right _ ha, x, hx, rfl⟩)
          have hL : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o) :=
            WalkIntRunChron.prefixPhysSet_mono _ D₁ (by omega : a₀ + o ≤ M + o) hRmem
          have hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ M) = ι (stRecR (ExplState.run
              κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (M + o))) := by rw [hc.2.2.2, max_eq_left hRa]
          exact fillCorr_of_stage_lt hι hβ hD hβr hβ0 hRa hrecc hP₁ hW₁ hl₁' hfin hrec₁ (fun k _ => hlm₁ k)
            (by omega) hL hP₂ hl₂' hfin₂ hrec₂ hlm₂M hstage hLR htr₁ htr₂
        refine ⟨⟨htop, iff_of_false ?_ hnz⟩, hF⟩
        intro h0
        by_cases hfin : (D₁ (M + o)).2 = ⊤
        · rw [htop.2 hfin] at h0
          exact ENNReal.top_ne_zero h0
        · obtain ⟨htr₁, -⟩ := htr M hM (by omega) hl₁ hl₂ hfin
          have hpos : (0 : ℝ) < stopTime ⊤ (D₁ (M + o)) := by
            simp only [stopTime, min_top_left]
            exact NNReal.coe_pos.2 (ENNReal.toNNReal_pos hnz hfin)
          obtain ⟨r', hr'0, hr', -⟩ := htr₁ 0 le_rfl hpos
          have h0' : stopTime ⊤ (D₂ M) = 0 := by simp [stopTime, h0]
          linarith
      refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge i M with h | h
        · exact hL1M i h1 h
        · obtain rfl : i = M := by omega
          exact fun hl₁ hl₂ => (hstageM hl₁ hl₂).1
      · rcases Nat.lt_or_ge i M with h | h
        · exact hFM i h1 h
        · obtain rfl : i = M := by omega
          exact fun hl₁ hl₂ => (hstageM hl₁ hl₂).2
  exact key N hi₀N le_rfl

end InteractingSLE.Theorem14.SB.Lk

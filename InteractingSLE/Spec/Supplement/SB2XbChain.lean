/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MdLift

/-!
# The fill correspondence with no left moves only before the stage

Packet PROVE-T14-SB2LIFT (round 23). The chain behind `fillCorr_of_stage` (rounds 17-18) asks for no left moves of
both walks at **every** step, but uses them only before the launch: connectors recorded before stage `n` lie left of
the record (`arcs_subset_Iic_run`). In the lockstep induction the relative walk's moves are known only before the
current stage. This file restates the chain with the bounded hypothesis `∀ k, k < n → NoLeftMove … k` (same proofs):
`arcs_subset_Iic_run_lt`, `notMem_prefix_of_beyond_lt`, `mem_closure_prefix_succ_of_mem_lt`,
`mem_closure_partPrefix_of_mem_lt`, `onSegFill_prefix_succ_lt`, `onSegFill_partPrefix_lt`, `fillCorr_of_runs_lt`,
`fillCorr_of_chain_lt` and **`fillCorr_of_stage_lt`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

section SB2McRun

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Before the walk is done, all connectors lie left of the record.** -/
theorem arcs_subset_Iic_run_lt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {N : ℕ}
    (hrec : ∀ k, k < N → RecInv κ b jumps θ D k) (hlm : ∀ k, k < N → NoLeftMove κ b jumps θ D k) :
    ∀ n, n ≤ N → stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone →
      ∀ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n).2.1,
        a ⊆ Iic (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
  | 0, _, _ => by
    intro a ha
    simp [ExplState.run, ExplState.init] at ha
  | n + 1, hn, hst => by
    set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hsdef
    have hst' : stStatus s ≠ stDone := fun h =>
      hst (by rw [GW1WalkFinish.done_run_succ _ D h]; exact h)
    have ih := arcs_subset_Iic_run_lt hP hrec hlm n (by omega) hst'
    have hmono := stRecR_run_le_succ' hP (hrec n (by omega))
    have hold : ∀ a ∈ s.2.1, a ⊆ Iic (stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) :=
      fun a ha => (ih a ha).trans (Iic_subset_Iic.2 hmono)
    by_cases hk : n < (boundaryWalkSpec b jumps θ true).2.2.length
    · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
      · have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true)
          (D := D) hk hev
        have harcs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.1 = s.2.1 := by
          rw [hstep]
          rcases flowStep_trichotomy (κ := κ) (b := b) false s n (D n) θ ⊤ with e | e | e
          · rw [e]
          · rw [e, arcs_setDead]
          · rw [e, Lx.arcs_launch']
        rw [harcs]
        exact hold
      · have hstep := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true)
          (D := D) hk hodd
        rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) s none true with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩
        · rw [hstep, e] at hold ⊢
          exact hold
        · rw [hstep, e, arcs_setDead]
          rw [hstep, e] at hold
          exact hold
        · cases r
          · exact absurd (hstep.trans e) (hlm n (by omega) x m)
          · rw [hstep, e, moveAlong_arcs_true]
            rw [hstep, e] at hold
            intro a ha
            rcases List.mem_append.1 ha with ha | ha
            · exact hold a ha
            · rw [List.mem_singleton.1 ha]
              rw [GW1W.stRecR_moveAlong_true]
              exact fun z hz => le_max_of_le_right hz.2
        · exfalso
          apply hst
          rw [hstep, e]
          exact stStatus_moveToEnd'' s r
    · have e : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) = s := by
        rw [run_succ]
        have : (boundaryWalkSpec b jumps θ true).2.2[n]? = none := List.getElem?_eq_none (not_lt.1 hk)
        rw [this]
      rw [e]
      exact ih

/-- **Before the walk is done, the prefix has no real point beyond the record.** -/
theorem notMem_prefix_of_beyond_lt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k) (hlm : ∀ k, k < n → NoLeftMove κ b jumps θ D k)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) {x : ℝ}
    (hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x) :
    (x : ℂ) ∉ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n := by
  have hrec' : ∀ k, k < n → RecInv κ b jumps θ D k := fun k hk => hrec k hk.le
  have hmono : ∀ j, j ≤ n → stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D j) ≤
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := fun j hj =>
    stRecR_run_mono hP hrec' hj le_rfl
  have h0 : (0 : ℝ) ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) := by
    have := hmono 0 (Nat.zero_le n)
    rwa [stRecR_run_zero] at this
  unfold SB.prefixPhysSet
  simp only [mem_union, mem_singleton_iff, mem_iUnion]
  rintro ((h | ⟨p, hp, hxp⟩) | ⟨a, ha, y, hy, hyx⟩)
  · -- the root
    have : x = 0 := by
      have h' : (x : ℂ) = ((0 : ℝ) : ℂ) := by rw [h]; simp [boundaryWalkSpec]
      exact_mod_cast h'
    linarith
  · -- an old piece
    obtain ⟨j, hj, hlne, rfl⟩ := exists_launch_of_mem_pieces n p hp
    have hokn := hrec n le_rfl x hx
    obtain ⟨hfinj, halive⟩ := hokn.1 j hj hlne
    have hokj := hrec j hj.le x ((hmono j hj.le).trans_lt hx)
    obtain ⟨⟨c, θ'⟩, hl⟩ := Option.ne_none_iff_exists'.1 hlne
    exact not_lAlive_of_mem_tip hP hl hfinj hokj hxp halive
  · -- a connector
    have hy' : y = x := by exact_mod_cast hyx
    have := arcs_subset_Iic_run_lt hP hrec' hlm n le_rfl hst a ha (hy' ▸ hy)
    exact absurd this (not_le.2 hx)

/-- **At a launch, a real point of the new prefix beyond the record lies in the closed fill of the new prefix.** -/
theorem mem_closure_prefix_succ_of_mem_lt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k) (hlm : ∀ k, k < n → NoLeftMove κ b jumps θ D k)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) {x : ℝ}
    (hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x)
    (hmem : (x : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) :
    (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) := by
  have hok := hrec n le_rfl x hx
  have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none := by
    rw [hl]; simp
  have hdead : ¬ lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ⊤ (D n) x := by
    have hold := notMem_prefix_of_beyond_lt hP hrec hlm hst hx
    obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hl
    rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
    simp only [SB.prefixPhysSet] at hmem hold
    rw [GW1Bookkeep.pieces_run_succ_of_launch hlne, he, Lx.arcs_launch'] at hmem
    simp only [mem_union, mem_singleton_iff, mem_iUnion, List.mem_append, List.mem_singleton] at hmem hold
    rcases hmem with (h | ⟨p, hp, hxp⟩) | h
    · exact absurd (Or.inl (Or.inl h)) hold
    · rcases hp with hp | rfl
      · exact absurd (Or.inl (Or.inr ⟨p, hp, hxp⟩)) hold
      · exact not_lAlive_of_mem_tip hP hl hfin hok hxp
    · exact absurd (Or.inr h) hold
  by_contra hcl
  exact hdead ((lAlive_run_iff hP hl hfin x hok.1 hok.2.1 hok.2.2.1 hok.2.2.2).2 hcl)

end SB2McRun

section SB2McPart

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **At a launch, a real point beyond the record of the prefix with the new piece up to `r` lies in its closed
fill.** -/
theorem mem_closure_partPrefix_of_mem_lt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k) (hlm : ∀ k, k < n → NoLeftMove κ b jumps θ D k)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) {x : ℝ}
    (hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x) {r : ℝ} (hr0 : 0 ≤ r)
    (hrT : r ≤ stopTime ⊤ (D n)) (hmem : (x : ℂ) ∈ partPrefix κ b jumps θ D n r) :
    (x : ℂ) ∈ closure (fillH (partPrefix κ b jumps θ D n r)) := by
  have hold := notMem_prefix_of_beyond_lt hP hrec hlm hst hx
  have hok := hrec n le_rfl x hx
  obtain ⟨hlaunch, hoff, hbd, hne⟩ := hok
  unfold partPrefix at hmem ⊢
  set spec := boundaryWalkSpec b jumps θ true with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  have hcc := isConformal_runChart_of_reg spec hP n
  have hinj : InjOn (stChart s₀).2.1 H := fun w hw w' hw' h => by rw [← hcc.2.2 w hw, h, hcc.2.2 w' hw']
  obtain ⟨hbe, -⟩ := GW1P.isClosed_pieces_run spec D hP n
  obtain ⟨ĝ, C, hf, hC⟩ := hbe
  have hĝ : ContinuousOn ĝ {z : ℂ | 0 ≤ z.im} := GW1P.continuousOn_of_tendsto hf
  have hgg : EqOn ĝ (stChart s₀).2.1 H := fun z hz => by
    have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H (QuantumZipper.H_subset_Hbar hz)
    exact tendsto_nhds_unique (hf z (QuantumZipper.H_subset_Hbar hz))
      ((hcc.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hz)).tendsto.mono_left nhdsWithin_le_nhds)
  have hbdV : ∀ p ∈ Hbar, bdVal (stChart s₀) p = ĝ p := fun p hp => bdVal_eq_of_tendsto hp (hf p hp)
  have hfin' : ∀ j < n, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤ :=
    fun j hj hj' => (hlaunch j hj hj').1
  obtain ⟨K, hKc, hKR, hDK⟩ := image_runChart_walk hP n hfin'
  obtain ⟨hfc, hre⟩ := continuousWithinAt_runChart_fwd hP x n hlaunch hoff
  have hyH : (stChart s₀).1 x ∈ Hbar := show 0 ≤ ((stChart s₀).1 x).im by rw [hre]
  have hyx : ĝ ((stChart s₀).1 x) = x := by
    have : (𝓝[H] ((stChart s₀).1 x)).NeBot := GW1P.neBot_nhdsWithin_H hyH
    exact tendsto_nhds_unique (hf _ hyH) hbd
  have hinjy := injAt_of_continuousWithinAt hcc.2.1 hcc.2.2 hĝ hgg (by simp) hyx hfc rfl
  have hfKP : fillH K = fillH (SB.prefixPhysSet κ b jumps spec D n) := fillH_eq_of_union_im hKR
  have hy0 : ĝ ((stChart s₀).1 x) ∉ closure (fillH K) := by rw [hyx, hfKP]; exact hoff n le_rfl
  -- the trace up to `r`
  have hα := isGeneratingTrace_trOf hPR
  have hαH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 → 0 ≤ (trOf (D n) t).im := fun t ht =>
    im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  have hrle : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (D n).2 := by
    obtain ⟨-, -, htime⟩ := stopDrv_eq_and_isGeneratingTrace hPR hfin
    rw [← ENNReal.coe_toNNReal hfin, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, Real.coe_toNNReal _ hr0]
    rw [htime] at hrT
    exact hrT
  have hAr : IsCompact (trOf (D n) '' Icc 0 r.toNNReal) := isCompact_Icc.image_of_continuousOn
    (hα.2.1.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans hrle)
  have hArH : trOf (D n) '' Icc 0 r.toNNReal ⊆ Hbar := by
    rintro _ ⟨t, ht, rfl⟩
    exact hαH t ((ENNReal.coe_le_coe.2 ht.2).trans hrle)
  have hDr := image_H_diff_fillH_of_chart hcc.1 hinj hĝ hgg hC hKc hDK hAr hArH
  have hiff := mem_closure_fillH_iff_of_chart hinj hĝ hgg hDK hDr hAr hyH hy0 hinjy
  have hfill : fillH (K ∪ ĝ '' (trOf (D n) '' Icc 0 r.toNNReal)) =
      fillH (SB.prefixPhysSet κ b jumps spec D n ∪ bdVal (stChart s₀) '' (trOf (D n) '' Icc 0 r.toNNReal)) := by
    have himg : bdVal (stChart s₀) '' (trOf (D n) '' Icc 0 r.toNNReal) =
        ĝ '' (trOf (D n) '' Icc 0 r.toNNReal) := image_congr fun p hp => hbdV p (hArH hp)
    rw [himg]
    refine fillH_eq_of_union_im ?_
    rw [union_right_comm, hKR, union_right_comm]
  rw [hyx, hfill] at hiff
  -- the chart point is a trace point at a positive time
  have hc : (stChart s₀).1 x ∈ closure (fillH (trOf (D n) '' Icc 0 r.toNNReal)) := by
    rcases hmem with hmem | ⟨p, ⟨t, ht, rfl⟩, hpx⟩
    · exact absurd hmem hold
    · have htD : (t : ℝ≥0∞) ≤ (D n).2 := (ENNReal.coe_le_coe.2 ht.2).trans hrle
      rw [hbdV _ (hαH t htD)] at hpx
      have heq : trOf (D n) t = (stChart s₀).1 x := hinjy _ (hαH t htD) (by rw [hpx, hyx])
      have ht0 : 0 < t := pos_iff_ne_zero.2 fun h => hne (by rw [← heq, h]; exact hα.1)
      set w : ℝ≥0 → ℝ := fun r => (D n).1 (min (r : ℝ≥0∞) (D n).2).toNNReal with hwdef
      have hwc : Continuous w := CounterflowRange.continuous_stopped hPR.2.1
      have hw0 : w 0 = 0 := by
        have := hPR.continuous_stoppedReal.2
        simpa [hwdef] using this
      have hαr := isGeneratingTrace_mono (CounterflowRange.isGeneratingTrace_stopped hα) hrle
      rw [← heq]
      exact trace_mem_closure_fillH hαr hwc hw0 (fun u hu => hαH u (hu.trans hrle)) ht0 ht.2
  exact hiff.1 hc


end SB2McPart

section SB2McPart2

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`OnSegFill` for the actual prefix after a pair of corresponding launches.** -/
theorem onSegFill_prefix_succ_lt {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : StrictMonoOn ι (Ici R)) (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, k < n₁ → NoLeftMove κ b₁ J₁ θ D₁ k)
    (hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ≠ stDone)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, k < n₂ → NoLeftMove κ b₂ J₂ θ D₂ k)
    (hst₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ≠ stDone)
    (hP₂eq : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1))) :
    OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
      (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)) := by
  intro x hx
  refine ⟨mem_closure_prefix_succ_of_mem_lt hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hx, fun hm => ?_⟩
  rw [← hP₂eq] at hm ⊢
  have hx₂ : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) < ι x := by
    rw [hrecc]
    exact hι (mem_Ici.2 hRa) (mem_Ici.2 (hRa.trans hx.le)) hx
  exact mem_closure_prefix_succ_of_mem_lt hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hx₂ hm

/-- **`OnSegFill` for the actual prefix at a time of the piece**, when the relative prefix at a matching time is its
lift image. -/
theorem onSegFill_partPrefix_lt {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : StrictMonoOn ι (Ici R)) (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, k < n₁ → NoLeftMove κ b₁ J₁ θ D₁ k)
    (hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ≠ stDone)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, k < n₂ → NoLeftMove κ b₂ J₂ θ D₂ k)
    (hst₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ≠ stDone)
    {r r' : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ stopTime ⊤ (D₁ n₁)) (hr0' : 0 ≤ r') (hrT' : r' ≤ stopTime ⊤ (D₂ n₂))
    (heq : partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
      (partPrefix κ b₁ J₁ θ D₁ n₁ r) := by
  intro x hx
  refine ⟨mem_closure_partPrefix_of_mem_lt hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hx hr0 hrT, fun hm => ?_⟩
  rw [← heq] at hm ⊢
  have hx₂ : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) < ι x := by
    rw [hrecc]
    exact hι (mem_Ici.2 hRa) (mem_Ici.2 (hRa.trans hx.le)) hx
  exact mem_closure_partPrefix_of_mem_lt hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hx₂ hr0' hrT' hm

end SB2McPart2

section SB2McFill

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`FillCorr` at a pair of corresponding launches from the two runs.** -/
theorem fillCorr_of_runs_lt {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, k < n₁ → NoLeftMove κ b₁ J₁ θ D₁ k)
    (hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ≠ stDone)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, k < n₂ → NoLeftMove κ b₂ J₂ θ D₂ k)
    (hst₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ≠ stDone)
    (hseg : IsWalkSeg β₀ tL (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hP₂eq : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hsegp : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → IsWalkSeg β₀ tL (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hmatch₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hmatch₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  have hon : ∀ (r r' : ℝ), 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) →
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r) →
      OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
        (partPrefix κ b₁ J₁ θ D₁ n₁ r) := fun r r' hr0 hr hr0' hr' heq =>
    onSegFill_partPrefix_lt hι.mono hRa hrecc hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hr0 hr.le
      hr0' hr'.le heq
  refine fillCorr_of_liftImage hι hβ hD hRa hseg hP₂eq
    (onSegFill_prefix_succ_lt hι.mono hRa hrecc hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hP₂eq)
    (fun r hr0 hr => ?_) (fun r' hr0' hr' => ?_)
  · obtain ⟨r', hr0', hr', heq⟩ := hmatch₁ r hr0 hr
    exact ⟨hsegp r hr0 hr, hon r r' hr0 hr hr0' hr' heq, r', hr0', hr', heq⟩
  · obtain ⟨r, hr0, hr, heq⟩ := hmatch₂ r' hr0' hr'
    exact ⟨r, hr0, hr, hsegp r hr0 hr, hon r r' hr0 hr hr0' hr' heq, heq⟩

end SB2McFill

section SB2MdFill

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`FillCorr` from GW1's chain facts, the run facts of both walks and the lift images.** -/
theorem fillCorr_of_chain_lt {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβ0 : β₀ 0 = 0)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, k < n₁ → NoLeftMove κ b₁ J₁ θ D₁ k) (hn₁ : n₁ + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, k < n₂ → NoLeftMove κ b₂ J₂ θ D₂ k)
    (hP₂eq : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)))
    (hmatch₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r))
    (hmatch₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  have hst₁ := WalkIntRunChron.not_done_of_launch _ D₁ hl₁
  have hst₂ := WalkIntRunChron.not_done_of_launch _ D₂ hl₂
  have hseg := isWalkSeg_prefix_succ_of_chain hW₁ hl₁ hfin₁ hn₁ hβr hβ0
    (GW1Z.prefixPhysSet_subset_succ _ D₁ n₁ hL)
  exact fillCorr_of_runs_lt hι hβ hD hRa hrecc hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hseg hP₂eq
    (fun r hr0 hr => isWalkSeg_partPrefix_of_chain hP₁ hW₁ hl₁ hfin₁ hn₁ hr0 hr.le hβr hβ0 hL) hmatch₁ hmatch₂

end SB2MdFill

section SB2MdLift

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {ι : ℝ → ℝ} {R : ℝ}

/-- **`FillCorr` from the stage identity before the launches, the lift relation of the new pieces and their lift at
matching times** (`fillCorr_of_chain_lt` with `hP₂eq`, `hmatch₁`, `hmatch₂` discharged). -/
theorem fillCorr_of_stage_lt {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hβ : Supp9B.IsProperCurve β₀) (hD : LiftCurveData β₀ γ tL R ι)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hβ0 : β₀ 0 = 0)
    (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, k < n₁ → NoLeftMove κ b₁ J₁ θ D₁ k) (hn₁ : n₁ + 1 ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hL : β₀ tL ∈ SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, k < n₂ → NoLeftMove κ b₂ J₂ θ D₂ k)
    (hstage : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂ =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hpc : LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) (D₁ n₁))
      (newPc (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) (D₂ n₂)))
    (htr₁ : ∀ r : ℝ, 0 ≤ r → r < stopTime ⊤ (D₁ n₁) → ∃ r' : ℝ, 0 ≤ r' ∧ r' < stopTime ⊤ (D₂ n₂) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
          (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
          (trOf (D₁ n₁) '' Icc 0 r.toNNReal)))
    (htr₂ : ∀ r' : ℝ, 0 ≤ r' → r' < stopTime ⊤ (D₂ n₂) → ∃ r : ℝ, 0 ≤ r ∧ r < stopTime ⊤ (D₁ n₁) ∧
      bdVal (stChart (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂)) ''
          (trOf (D₂ n₂) '' Icc 0 r'.toNNReal) =
        liftImage β₀ tL γ (bdVal (stChart (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)) ''
          (trOf (D₁ n₁) '' Icc 0 r.toNNReal))) :
    FillCorr κ θ b₁ J₁ D₁ n₁ b₂ J₂ D₂ n₂ ι := by
  refine fillCorr_of_chain_lt hι hβ hD hβr hβ0 hRa hrecc hP₁ hW₁ hl₁ hfin₁ hrec₁ hlm₁ hn₁ hL hP₂ hl₂ hfin₂ hrec₂ hlm₂
    (prefix_succ_eq_liftImage_of_launch hl₁ hl₂ hstage hpc) (fun r hr0 hr => ?_) (fun r' hr0' hr' => ?_)
  · obtain ⟨r', hr0', hr', h⟩ := htr₁ r hr0 hr
    exact ⟨r', hr0', hr', partPrefix_eq_liftImage hstage h⟩
  · obtain ⟨r, hr0, hr, h⟩ := htr₂ r' hr0' hr'
    exact ⟨r, hr0, hr, partPrefix_eq_liftImage hstage h⟩

end SB2MdLift

end InteractingSLE.Theorem14.SB.Lk

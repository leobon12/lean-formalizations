/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2McRun

/-!
# Real points of the prefix at times of the piece, and `OnSegFill`

Packet PROVE-T14-SB2LIFT (round 17; `OnSegFill`, the third input of `fillCorr_of_liftImage`, handoff §R16.2 1(c)).

* `isGeneratingTrace_mono`: a generating trace generates on every shorter life;
* **`mem_closure_partPrefix_of_mem`**: at a launch, a real point beyond the record of the prefix with the new piece up
  to a time `r ≤` its stop lies in the closed fill of that set. The point lies on the trace up to `r` (it is not on the
  old prefix, `notMem_prefix_of_beyond`), its chart point is a trace point (boundary injectivity), it lies in the
  closed fill of the trace (`trace_mem_closure_fillH`), and the chart transports this (`image_H_diff_fillH_of_chart`,
  `mem_closure_fillH_iff_of_chart`, as in `lHit_run_iff`);
* **`onSegFill_prefix_succ`**, **`onSegFill_partPrefix`**: `OnSegFill` for the actual prefix after a launch, and at a
  time of the piece, when the relative prefix (at a matching time) is its lift image and the records correspond under
  `ι`. Both halves come from the two runs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A generating trace generates on every shorter life. -/
theorem isGeneratingTrace_mono {w : ℝ≥0 → ℝ} {T T' : ℝ≥0∞} {η : ℝ≥0 → ℂ} (h : IsGeneratingTrace w T η)
    (hT : T' ≤ T) : IsGeneratingTrace w T' η :=
  ⟨h.1, h.2.1.mono fun _ ht => le_trans ht hT, fun t ht => h.2.2 t (lt_of_lt_of_le ht hT)⟩

/-- **At a launch, a real point beyond the record of the prefix with the new piece up to `r` lies in its closed
fill.** -/
theorem mem_closure_partPrefix_of_mem {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hrec : ∀ k, k ≤ n → RecInv κ b jumps θ D k) (hlm : ∀ k, NoLeftMove κ b jumps θ D k)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone) {x : ℝ}
    (hx : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x) {r : ℝ} (hr0 : 0 ≤ r)
    (hrT : r ≤ stopTime ⊤ (D n)) (hmem : (x : ℂ) ∈ partPrefix κ b jumps θ D n r) :
    (x : ℂ) ∈ closure (fillH (partPrefix κ b jumps θ D n r)) := by
  have hold := notMem_prefix_of_beyond hP hrec hlm hst hx
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

variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {R : ℝ} {ι : ℝ → ℝ}

/-- **`OnSegFill` for the actual prefix after a pair of corresponding launches.** -/
theorem onSegFill_prefix_succ {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : StrictMonoOn ι (Ici R)) (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k)
    (hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ≠ stDone)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, NoLeftMove κ b₂ J₂ θ D₂ k)
    (hst₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ≠ stDone)
    (hP₂eq : SB.prefixPhysSet κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1) =
      liftImage β₀ tL γ (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1))) :
    OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
      (SB.prefixPhysSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)) := by
  intro x hx
  refine ⟨mem_closure_prefix_succ_of_mem hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hx, fun hm => ?_⟩
  rw [← hP₂eq] at hm ⊢
  have hx₂ : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) < ι x := by
    rw [hrecc]
    exact hι (mem_Ici.2 hRa) (mem_Ici.2 (hRa.trans hx.le)) hx
  exact mem_closure_prefix_succ_of_mem hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hx₂ hm

/-- **`OnSegFill` for the actual prefix at a time of the piece**, when the relative prefix at a matching time is its
lift image. -/
theorem onSegFill_partPrefix {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n₁ n₂ : ℕ} {c₁ c₂ : Chart} {θ₁ θ₂ : ℝ}
    (hι : StrictMonoOn ι (Ici R)) (hRa : R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
    (hrecc : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) =
      ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁)))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hl₁ : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (n₁ + 1)).2.2.2.1 n₁ = some (c₁, θ₁))
    (hfin₁ : (D₁ n₁).2 ≠ ⊤) (hrec₁ : ∀ k, k ≤ n₁ → RecInv κ b₁ J₁ θ D₁ k)
    (hlm₁ : ∀ k, NoLeftMove κ b₁ J₁ θ D₁ k)
    (hst₁ : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁) ≠ stDone)
    (hP₂ : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂)
    (hl₂ : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (n₂ + 1)).2.2.2.1 n₂ = some (c₂, θ₂))
    (hfin₂ : (D₂ n₂).2 ≠ ⊤) (hrec₂ : ∀ k, k ≤ n₂ → RecInv κ b₂ J₂ θ D₂ k)
    (hlm₂ : ∀ k, NoLeftMove κ b₂ J₂ θ D₂ k)
    (hst₂ : stStatus (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) ≠ stDone)
    {r r' : ℝ} (hr0 : 0 ≤ r) (hrT : r ≤ stopTime ⊤ (D₁ n₁)) (hr0' : 0 ≤ r') (hrT' : r' ≤ stopTime ⊤ (D₂ n₂))
    (heq : partPrefix κ b₂ J₂ θ D₂ n₂ r' = liftImage β₀ tL γ (partPrefix κ b₁ J₁ θ D₁ n₁ r)) :
    OnSegFill β₀ γ tL ι (stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ n₁))
      (partPrefix κ b₁ J₁ θ D₁ n₁ r) := by
  intro x hx
  refine ⟨mem_closure_partPrefix_of_mem hP₁ hl₁ hfin₁ hrec₁ hlm₁ hst₁ hx hr0 hrT, fun hm => ?_⟩
  rw [← heq] at hm ⊢
  have hx₂ : stRecR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ n₂) < ι x := by
    rw [hrecc]
    exact hι (mem_Ici.2 hRa) (mem_Ici.2 (hRa.trans hx.le)) hx
  exact mem_closure_partPrefix_of_mem hP₂ hl₂ hfin₂ hrec₂ hlm₂ hst₂ hx₂ hr0' hrT' hm

end InteractingSLE.Theorem14.SB.Lk

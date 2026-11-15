/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1PieceSimpleProof
import InteractingSLE.Spec.Supplement.G7ClockCluster
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.Supplement.GW6Reduction

/-!
# Lemma GW1: the continuous inverse chart is injective away from the old boundary fibres

Packet PROVE-T14-GW1Z. Lemma GW1, proof (`source/spec/p577-624.md` L957, p. 619): "The continuous inverse chart is
injective away from those old boundary fibers." This file proves `ChartFiberStatement` (deterministic): along a run
whose launched pieces are regular, the boundary-limit map `f` of the inverse of the chart at a launch identifies two
points of `ℍ̄` only at points of the old union (`SB.prefixPhysSet`).

* **One Loewner step** (`eq_of_extendFrom_eq`): let `F̄` be the boundary extension of `F_T = g_T⁻¹(· + W_T)` and
  `K_T = fill(A)` with `A` closed. If `F̄(x) = F̄(y) = b ∉ A`, then `x = y`. A disc `B(b, δ)` misses `A`; its upper half
  is connected and meets `ℍ \ K_T` (`b` is a limit of `F_T`-values), so it lies in the unbounded component, i.e. in
  `ℍ \ K_T`. There `g_T` is continuous and bounded near `b`, and `F̄ ∘ g_T = id`; by the cluster-set lemma
  (`Supp7.exists_tendsto_of_tendsto_comp_filter`) `g_T` has a limit `ξ` at `b` along `ℍ`. Since `F_T(z) → b` as
  `z → x` and `g_T(F_T(z)) = z`, `x = ξ`; likewise `y = ξ`.
* **Along the run** (`chartFiber_run`): the root chart is a translation; a step without launch recentres; a launch with
  infinite stop keeps the chart; a launch with finite stop `T` composes with `F̄_T`, whose fibres lie on the piece's
  trace `α([0, T])` (`K_T = fill(α[0, T])`, PROVE-TRACECLOSE), whose image `f(α[0, T])` is the new piece's
  `Chart.tipSet`, part of the new old union. The old union only grows (`prefixPhysSet_subset_succ`).
* **`chartFiberStatement`**: `GW1Z.ChartFiberStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE

namespace Theorem14

namespace GW1Z

/-! ### One Loewner step -/

section Step

variable {W : ℝ → ℝ} {T : ℝ}

/-- **The fibres of one Loewner step lie on its hull's generating set.** If `K_T = fill(A)` with `A` closed and the
boundary extension `F̄` of `F_T` takes the same value `b ∉ A` at `x, y ∈ ℍ̄`, then `x = y`. -/
theorem eq_of_extendFrom_eq (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 ≤ T)
    (hB : HasBdryLimits (fwdMapInv W T)) {A : Set ℂ} (hA : IsClosed A) (hfill : fwdHull W T = fillH A)
    {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar)
    (hxy : extendFrom H (fwdMapInv W T) x = extendFrom H (fwdMapInv W T) y)
    (hnot : extendFrom H (fwdMapInv W T) x ∉ A) : x = y := by
  set F : ℂ → ℂ := fwdMapInv W T with hFdef
  set Fb : ℂ → ℂ := extendFrom H F with hFbdef
  have hFlim : ∀ p ∈ Hbar, Tendsto F (𝓝[H] p) (𝓝 (Fb p)) := fun p hp => hB.tendsto hp
  have hFK : ∀ z ∈ H, F z ∈ H \ fwdHull W T := fun z hz =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 hT hz
  have hgF : ∀ z ∈ H, fwdMap W T (F z) = z := fun z hz => QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 hT hz
  have hFg : ∀ z ∈ H \ fwdHull W T, F (fwdMap W T z) = z := fun z hz =>
    QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 hT hz
  have hFbeq : ∀ z ∈ H, Fb z = F z := fun z hz => ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hT hz
  have hgc : ContinuousOn (fwdMap W T) (H \ fwdHull W T) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hT).continuousOn
  have hopen : IsOpen (H \ fwdHull W T) := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hT
  -- a limit of the forward map at `F̄ p` along `ℍ` is `p`
  have key : ∀ p ∈ Hbar, ∀ ξ : ℂ, Tendsto (fwdMap W T) (𝓝[H] (Fb p)) (𝓝 ξ) → p = ξ := by
    intro p hp ξ hξ
    have h1 : Tendsto F (𝓝[H] p) (𝓝[H] (Fb p)) :=
      tendsto_nhdsWithin_iff.2 ⟨hFlim p hp, eventually_nhdsWithin_of_forall fun z hz => (hFK z hz).1⟩
    have h2 : Tendsto (fun z => fwdMap W T (F z)) (𝓝[H] p) (𝓝 ξ) := hξ.comp h1
    have h3 : Tendsto (fun z => fwdMap W T (F z)) (𝓝[H] p) (𝓝 p) :=
      (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr'
        (eventually_nhdsWithin_of_forall fun z hz => (hgF z hz).symm)
    have := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique h3 h2
  -- the continuity case: `g_T` is continuous at points of `ℍ \ K_T`
  have hcont : ∀ w ∈ H \ fwdHull W T, Tendsto (fwdMap W T) (𝓝[H] w) (𝓝 (fwdMap W T w)) := fun w hw =>
    ((hgc.continuousAt (hopen.mem_nhds hw)).tendsto).mono_left nhdsWithin_le_nhds
  set b := Fb x with hbdef
  have hbH : b ∈ Hbar := GW1P.mem_Hbar_of_tendsto hx (fun z hz => (hFK z hz).1) (hFlim x hx)
  -- a half-disc around `b` lies in `ℍ \ K_T`
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hA.isOpen_compl b hnot
  set D : Set ℂ := ball b δ ∩ H with hDdef
  have hDpre : IsPreconnected D := ((convex_ball b δ).inter convex_H).isPreconnected
  have hbcl : b ∈ closure (H \ fwdHull W T) := by
    have := GW1P.neBot_nhdsWithin_H hx
    exact mem_closure_of_tendsto (hFlim x hx) (eventually_nhdsWithin_of_forall fun z hz => hFK z hz)
  obtain ⟨w₀, hw₀K, hw₀b⟩ := Metric.mem_closure_iff.1 hbcl δ hδ
  have hDsub : D ⊆ H \ A := fun z hz => ⟨hz.2, hball hz.1⟩
  have hw₀D : w₀ ∈ D := ⟨by rw [mem_ball, dist_comm]; exact hw₀b, hw₀K.1⟩
  have hDK : D ⊆ H \ fwdHull W T := by
    intro z hz
    refine ⟨hz.2, fun hzK => ?_⟩
    rw [hfill] at hzK
    have hzC : z ∈ connectedComponentIn (H \ A) w₀ := hDpre.subset_connectedComponentIn hw₀D hDsub hz
    have hceq := connectedComponentIn_eq hzC
    rcases hzK.2 with hzA | hzb
    · rw [hA.closure_eq] at hzA
      exact (hDsub hz).2 hzA
    · rw [hA.closure_eq] at hzb
      refine hw₀K.2 ?_
      rw [hfill]
      refine ⟨hw₀K.1, Or.inr ?_⟩
      rw [hA.closure_eq, hceq]
      exact hzb
  -- the cluster-set lemma gives a limit of `g_T` at `b`
  have hDev : ∀ᶠ w in 𝓝[H] b, w ∈ D :=
    Filter.mem_of_superset (inter_mem_nhdsWithin H (ball_mem_nhds b hδ)) fun w hw => ⟨hw.2, hw.1⟩
  obtain ⟨CF, hCF⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hT
  have hR : ∀ x' : ℂ, x'.im = 0 → Fb x' ∉ Fb '' H := by
    intro x' hx' hmem
    rw [ZhanGT4.extendFrom_image_H hW hW0 hT] at hmem
    have hx'H : x' ∈ Hbar := show 0 ≤ x'.im by rw [hx']
    have he := key x' hx'H _ (hcont _ hmem)
    have hpos : 0 < (fwdMap W T (Fb x')).im := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT hmem
    rw [← he, hx'] at hpos
    exact lt_irrefl _ hpos
  have := GW1P.neBot_nhdsWithin_H hbH
  obtain ⟨ξ, -, -, hξ⟩ := Supp7.exists_tendsto_of_tendsto_comp_filter (F := Fb) (G := fwdMap W T)
    ((QuantumZipper.RS.differentiableOn_fwdMapInv hW hW0 hT).congr hFbeq) hB.continuousOn
    ((QuantumZipper.RS.injOn_fwdMapInv_H hW hW0 hT).congr fun z hz => (hFbeq z hz).symm) hR
    (l := 𝓝[H] b) (R := ‖b‖ + δ + CF)
    (hDev.mono fun w hw => le_of_lt (show (0 : ℝ) < (fwdMap W T w).im from
      QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT (hDK hw)))
    (hDev.mono fun w hw => by
      have h1 := hCF _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT (hDK hw))
      rw [show fwdMapInv W T (fwdMap W T w) = w from hFg w (hDK hw)] at h1
      have h2 : ‖w‖ ≤ ‖b‖ + δ := by
        have := hw.1
        rw [mem_ball, dist_eq_norm] at this
        have h3 := norm_sub_norm_le w b
        linarith
      have h4 := norm_sub_norm_le (fwdMap W T w) w
      rw [norm_sub_rev] at h1
      linarith)
    (fun U hU => by
      obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
      refine ⟨ball b (min ε δ) ∩ H, Filter.mem_of_superset (inter_mem_nhdsWithin H
        (ball_mem_nhds b (lt_min hε hδ))) fun w hw => ⟨hw.2, hw.1⟩, ?_, ?_, ?_⟩
      · exact fun z hz => hεU ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
      · exact ((convex_ball b _).inter convex_H).isPreconnected
      · exact hgc.mono fun z hz => hDK ⟨ball_subset_ball (min_le_right _ _) hz.1, hz.2⟩)
    (v := b) ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (hDev.mono fun w hw => by
      show w = Fb (fwdMap W T w)
      rw [hFbeq _ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hT (hDK hw)), hFg w (hDK hw)]))
  exact (key x hx ξ hξ).trans (key y hy ξ (by rw [← hxy]; exact hξ)).symm

end Step

/-! ### The fibre invariant of a chart -/

/-- **A good chart whose boundary fibres lie in `A`**: its inverse has the boundary-limit map `f` from inside `ℍ`,
moving points by at most `C`, and two points of `ℍ̄` with the same image outside `A` coincide. -/
def FiberGood (c : Chart) (A : Set ℂ) : Prop :=
  ∃ (f : ℂ → ℂ) (C : ℝ), (∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (f p))) ∧ (∀ p ∈ Hbar, ‖f p - p‖ ≤ C) ∧
    ∀ x ∈ Hbar, ∀ y ∈ Hbar, f x = f y → f x ∉ A → x = y

theorem FiberGood.mono {c : Chart} {A A' : Set ℂ} (h : FiberGood c A) (hAA' : A ⊆ A') : FiberGood c A' := by
  obtain ⟨f, C, hf, hC, hfib⟩ := h
  exact ⟨f, C, hf, hC, fun x hx y hy hxy hA => hfib x hx y hy hxy fun h' => hA (hAA' h')⟩

/-- The recentred identity chart: a translation. -/
theorem fiberGood_recenter_id (x : ℝ) (A : Set ℂ) : FiberGood (Chart.id.recenter x) A := by
  refine ⟨fun z => z + (x : ℂ), |x|, fun p _ => ?_, fun p _ => ?_, fun y _ z _ h _ => add_right_cancel h⟩
  · rw [CounterflowRange.recenter_id_inv]
    exact ((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds
  · simp

/-- Real recentring keeps the fibre invariant. -/
theorem FiberGood.recenter {c : Chart} {A : Set ℂ} (h : FiberGood c A) (a : ℝ) : FiberGood (c.recenter a) A := by
  obtain ⟨f, C, hf, hC, hfib⟩ := h
  have hmem : ∀ p ∈ Hbar, p + (a : ℂ) ∈ Hbar := fun p hp => by
    have hp' : 0 ≤ p.im := hp
    show 0 ≤ (p + (a : ℂ)).im
    simpa using hp'
  refine ⟨fun p => f (p + (a : ℂ)), C + |a|, fun p hp => ?_, fun p hp => ?_, fun x hx y hy hxy hA => ?_⟩
  · have hT : Tendsto (fun z : ℂ => z + (a : ℂ)) (𝓝[H] p) (𝓝[H] (p + (a : ℂ))) := by
      refine tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto p).mono_left
        nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : 0 < z.im := hz
      show 0 < (z + (a : ℂ)).im
      simpa using hz'
    exact (hf _ (hmem p hp)).comp hT
  · calc ‖f (p + (a : ℂ)) - p‖ = ‖(f (p + (a : ℂ)) - (p + (a : ℂ))) + (a : ℂ)‖ := by ring_nf
      _ ≤ ‖f (p + (a : ℂ)) - (p + (a : ℂ))‖ + ‖(a : ℂ)‖ := norm_add_le _ _
      _ ≤ C + |a| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        linarith [hC _ (hmem p hp)]
  · exact add_right_cancel (hfib _ (hmem x hx) _ (hmem y hy) hxy hA)

/-- **A Loewner step after a regular piece stopped at a finite time keeps the fibre invariant**, for any `A`
containing the piece's physical points. -/
theorem FiberGood.loewner_stopped {c : Chart} {A : Set ℂ} (h : FiberGood c A) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (hr : GW1P.PieceRegular W S) (hS : S ≠ ⊤)
    (hA : c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S ⊆ A) :
    FiberGood (c.loewner (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal)
      ((S.toNNReal : ℝ≥0) : ℝ)) A := by
  obtain ⟨f, C, hf, hC, hfib⟩ := h
  obtain ⟨hU, hU0⟩ := hr.continuous_stoppedReal
  set U : ℝ → ℝ := fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal with hUdef
  set T : ℝ≥0 := S.toNNReal with hTdef
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hB := hr.hasBdryLimits hS
  obtain ⟨CF, hCF⟩ := exists_norm_fwdMapInv_sub_le hU hU0 hT0
  set Fb : ℂ → ℂ := extendFrom H (fwdMapInv U T) with hFbdef
  have hFH : ∀ z ∈ H, fwdMapInv U T z ∈ H := fun z hz => QuantumZipper.RS.fwdMapInv_mem_H hU hU0 hT0 hz
  have hFmem : ∀ p ∈ Hbar, Fb p ∈ Hbar := fun p hp => GW1P.mem_Hbar_of_tendsto hp hFH (hB.tendsto hp)
  refine ⟨fun p => f (Fb p), C + CF, fun p hp => ?_, fun p hp => ?_, fun x hx y hy hxy hnA => ?_⟩
  · exact CounterflowRange.tendsto_loewner_inv hU hU0 hT0 (hB.tendsto hp) (hf _ (hFmem p hp))
  · have hle : ‖Fb p - p‖ ≤ CF := by
      have := GW1P.neBot_nhdsWithin_H hp
      have hlim : Tendsto (fun z => ‖fwdMapInv U T z - z‖) (𝓝[H] p) (𝓝 ‖Fb p - p‖) :=
        ((hB.tendsto hp).sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
      refine le_of_tendsto hlim ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hCF z hz
    calc ‖f (Fb p) - p‖ = ‖(f (Fb p) - Fb p) + (Fb p - p)‖ := by ring_nf
      _ ≤ ‖f (Fb p) - Fb p‖ + ‖Fb p - p‖ := norm_add_le _ _
      _ ≤ C + CF := add_le_add (hC _ (hFmem p hp)) hle
  have hFxy : Fb x = Fb y := hfib _ (hFmem x hx) _ (hFmem y hy) hxy hnA
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ T) with hT | hTpos
  · -- a zero stop: `F̄_0` is the identity on `ℍ̄`
    have hT' : ((T : ℝ≥0) : ℝ) = 0 := NNReal.coe_eq_zero.2 hT.symm
    have hid : ∀ p ∈ Hbar, Fb p = p := by
      intro p hp
      refine extendFrom_eq (by rw [closure_H]; exact hp) ?_
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [hT']
      exact (fwdMapInv_zero_time hU hU0 hz).symm
    rw [← hid x hx, ← hid y hy]
    exact hFxy
  · -- a positive stop: the fibres of `F̄_T` lie on the trace
    obtain ⟨hw0, hwc, α, hα, -⟩ := hr
    have hST : ((T : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hS
    have hα' : IsGeneratingTrace (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) (T : ℝ≥0∞) α := by
      rw [hST]; exact CounterflowRange.isGeneratingTrace_stopped hα
    have hη := CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace hα'
    have hησ : ContinuousOn (fun s : ℝ => α s.toNNReal) (Icc 0 (T : ℝ)) :=
      hα'.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
        ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    have hfill := TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT hη hU hU0 (by exact_mod_cast hTpos) hησ
    have hAc : IsClosed ((fun s : ℝ => α s.toNNReal) '' Icc 0 (T : ℝ)) :=
      (isCompact_Icc.image_of_continuousOn hησ).isClosed
    refine eq_of_extendFrom_eq hU hU0 hT0 hB hAc hfill hx hy hFxy ?_
    rintro ⟨s, hs, hsx⟩
    apply hnA
    show f (Fb x) ∈ A
    have hWlt : ContinuousOn W {s | (s : ℝ≥0∞) < S} :=
      hwc.mono fun s (hs : (s : ℝ≥0∞) < S) => (le_of_lt hs : (s : ℝ≥0∞) ≤ S)
    have hsS : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S := by
      rw [← hST]; exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    refine hA ?_
    rw [CounterflowRange.tipSet_stopped_eq_of_tendsto hα hwc hw0 fun t ht =>
      hf _ (Sec7.IsGeneratingTrace.mem_Hbar hα hWlt hw0 ht)]
    exact ⟨α s.toNNReal, ⟨s.toNNReal, hsS, rfl⟩, congrArg f hsx⟩

/-! ### Along a run -/

section Run

open Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- A step of a run only appends to the recorded pieces and connectors. -/
theorem mem_lists_run_succ (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    (∀ p ∈ (ExplState.run κ b jumps spec D n).1, p ∈ (ExplState.run κ b jumps spec D (n + 1)).1) ∧
      ∀ a ∈ (ExplState.run κ b jumps spec D n).2.1, a ∈ (ExplState.run κ b jumps spec D (n + 1)).2.1 := by
  have hp := GW1P.pieces_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D (k := n)
  refine ⟨fun p hpm => ?_, fun a ha => ?_⟩
  · rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · rw [hp hl]; exact hpm
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [he, CounterflowRange.pieces_launch]
      exact List.mem_append_left _ hpm
  · rw [run_succ]
    cases hk : spec.2.2[n]? with
    | none => exact ha
    | some ins =>
      rcases ins with ⟨θ', t⟩ | pref | ⟨v, pref⟩
      · change a ∈ (ExplState.flowStep κ b spec.2.1 (ExplState.run κ b jumps spec D n) n (D n) θ' t).2.1
        rw [arcs_flowStep]
        exact ha
      all_goals
        change a ∈ (ExplState.contStep κ b jumps (ExplState.run κ b jumps spec D n) _ pref).2.1
        rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (ExplState.run κ b jumps spec D n) _ pref
          with e | e | ⟨r, x, m, e⟩ | ⟨r, e⟩ <;> rw [e]
        · exact ha
        · exact ha
        · rw [arcs_moveAlong]; exact List.mem_append_left _ ha
        · rw [arcs_moveToEnd]; exact List.mem_append_left _ ha

/-- **The old union only grows along a run.** -/
theorem prefixPhysSet_subset_succ (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    SB.prefixPhysSet κ b jumps spec D n ⊆ SB.prefixPhysSet κ b jumps spec D (n + 1) := by
  obtain ⟨hp, ha⟩ := mem_lists_run_succ (κ := κ) (b := b) (jumps := jumps) spec D n
  intro z hz
  simp only [SB.prefixPhysSet, mem_union, mem_iUnion, exists_prop] at hz ⊢
  rcases hz with (hz | ⟨p, hpm, hzp⟩) | ⟨a, ham, hza⟩
  · exact Or.inl (Or.inl hz)
  · exact Or.inl (Or.inr ⟨p, hp p hpm, hzp⟩)
  · exact Or.inr ⟨a, ha a ham, hza⟩

/-- **The piece launched at `n` is part of the old union after it.** -/
theorem tipSet_subset_prefixPhysSet_succ (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ} {c : Chart}
    {θ : ℝ} (hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n = some (c, θ)) :
    c.tipSet (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) (min (instrTime spec n) (D n).2)).toNNReal)
      (min (instrTime spec n) (D n).2) ⊆ SB.prefixPhysSet κ b jumps spec D (n + 1) := by
  obtain ⟨-, he, hc⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
  intro z hz
  have hmem : (c, (fun r : ℝ≥0 => (D n).1 (min (r : ℝ≥0∞) (min (instrTime spec n) (D n).2)).toNNReal),
      min (instrTime spec n) (D n).2) ∈ (ExplState.run κ b jumps spec D (n + 1)).1 := by
    rw [he, CounterflowRange.pieces_launch, ← hc]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  simp only [SB.prefixPhysSet, mem_union, mem_iUnion, exists_prop]
  exact Or.inl (Or.inr ⟨_, hmem, hz⟩)

/-- **The fibre invariant along a run whose launched pieces are regular.** -/
theorem chartFiber_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ (k : ℕ) (c : Chart) (θ : ℝ), (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ) →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ) :
    FiberGood (ExplState.run κ b jumps spec D n).2.2.2.2.1 (SB.prefixPhysSet κ b jumps spec D n) := by
  induction n with
  | zero => exact fiberGood_recenter_id spec.1 _
  | succ n ih =>
    have ih' := ih.mono (prefixPhysSet_subset_succ (κ := κ) (b := b) (jumps := jumps) spec D n)
    rcases hl : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
      rw [ha]
      exact ih'.recenter a
    · have hr := hreg n c θ hl
      have hsub := tipSet_subset_prefixPhysSet_succ (κ := κ) (b := b) (jumps := jumps) spec D hl
      obtain ⟨-, he, hc⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
      rcases eq_or_ne (min (instrTime spec n) (D n).2) ⊤ with htop | htop
      · rw [he, GW1P.chart_launch_of_top _ _ _ _ _ htop]
        exact ih'
      · rw [he, chart_launch _ _ _ _ _ htop]
        rw [hc] at hsub
        exact ih'.loewner_stopped hr htop hsub

/-- **`ChartFiberStatement`** (GW1, p. 619: "The continuous inverse chart is injective away from those old boundary
fibers"). -/
theorem chartFiberStatement : ChartFiberStatement := by
  intro κ b jumps spec D hreg k c θ hl
  have h := chartFiber_run (κ := κ) (b := b) (jumps := jumps) spec D hreg k
  rw [(eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl).2.2]
  exact h

end Run

/-! ### The per-piece statement with the fibre statement discharged -/

universe u

/-- **GW1, per piece, for both walks** (p. 619), from GB6's restart law, Theorem 1.3 and GW1's induction data 2–3
at every launch (`WalkLaunchClockStatement`): the fibre statement is `chartFiberStatement`, and GW0's forward
implication follows from Theorem 1.3 (`BR3Ref.gw0ForwardStatement_of_theorem13`). -/
theorem gw1PieceSimpleStatement_of_walkClock (hGB6 : Supp8.GB6.GB6RestartStatement.{u})
    (hT13 : Exist.Theorem13Statement.{u}) (hT13₀ : Exist.Theorem13Statement.{0})
    (hD : WalkLaunchClockStatement.{u}) : GW1PieceSimpleStatement.{u} :=
  gw1PieceSimpleStatement_of_clock hGB6 (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hT13 hD chartFiberStatement

end GW1Z

end Theorem14

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermClock
import InteractingSLE.Spec.Supplement.SB2BqCfg
import InteractingSLE.Spec.Supplement.SBLvPinch

/-!
# The entry chart of a completed path (builder frame)

Packet PROVE-RC-TERM, second run (ruling R124). SB2(1)'s configuration builder
(`Theorem14.SB.Bq.exists_relConfig_bridgePath_noTip`) works in the frame where the explorer starts at `0` and the
retained path `q` starts at a real point `d ≥ 0` on its right. Its chart input is a *left entry chart* of the retained
path at `0`, with a continuous boundary inverse with finite fibres and `LiftRealOn`. This file supplies them for a
retained path that is a completed Loewner trace `ξ` of a driver `V` ending at a freshly reached real tip
(`Term.IsFreshRealTip`), translated by `d`:

* `IsEntryData V T ξ p d`: the hypotheses (fresh real tip, the path in `ℍ̄`, injective, `d ≥ 0`, real points of the
  path at least `−d`);
* `entryPath ξ T d`: the path `s ↦ ξ (s T) + d` on `[0, 1]`;
* `entryChart V T d`: the centred Loewner chart at the horizon, read from `d` and recentred at the left image
  `markPosL V T (−d)` of the explorer's seed; `entryInv V T d`: the boundary extension of its inverse;
* `continuousAt_fwdMap_of_alive`, `tendsto_re_fwdMap_markPos`, `tendsto_re_fwdMap_markPosL`: the real flow at alive
  points and its one-sided limits at a mark;
* **`IsEntryData.isLeftEntryChart`**, **`IsEntryData.continuousOn_entryInv`**, `entryInv_eqOn`,
  **`IsEntryData.finite_fibre`**, **`liftRealOn_entryChart`**, and the path facts (`continuousOn_entryPath`,
  `entryPath_zero`, `im_entryPath_nonneg`, `real_entryPath_nonneg`).

Deterministic; R48-neutral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open Exist.StagedLaw (markPos markPosL)
open Theorem14 Theorem14.SB

/-! ### The real flow at alive points -/

section Flow

variable {w : ℝ → ℝ} {T : ℝ}

/-- The centred Loewner map is continuous at every point alive at the horizon. -/
theorem continuousAt_fwdMap_of_alive (hw : Continuous w) (hT : 0 ≤ T) {z : ℂ} {u : ℝ → ℂ}
    (hu : IsForwardSol w z T u) : ContinuousAt (fwdMap w T) z := by
  obtain ⟨δ, hδ, hlow, hzz⟩ := ZhanGT4.exists_aliveDisc_self hu hT
  exact (ZhanGT4.hasDerivAt_fwdMap_aliveDisc hw hu hδ hlow hzz ⟨hT, le_rfl⟩).continuousAt

/-- The forward value of an alive real point is real. -/
theorem fwdMap_ofReal_real (hw : Continuous w) (hT : 0 ≤ T) {y : ℝ} (hy : ∃ u, IsForwardSol w (y : ℂ) T u) :
    fwdMap w T (y : ℂ) = ((fwdMap w T (y : ℂ)).re : ℂ) := by
  obtain ⟨u, hu⟩ := hy
  have h1 : fwdMap w T (y : ℂ) = u T := QuantumZipper.F1.fwdMap_eq_of_isForwardSol hu ⟨hT, le_rfl⟩
  have h2 := fwdMap_ofReal_eq hw hT hu
  rw [← h1] at h2
  exact h2

/-- **The right limit of the real flow at a mark**: if every real point right of `x ≥ 0` is alive, the flow tends to
`markPos w T x` from the right. -/
theorem tendsto_re_fwdMap_markPos (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x)
    (hal : ∀ y : ℝ, x < y → ∃ u, IsForwardSol w (y : ℂ) T u) :
    Tendsto (fun y : ℝ => (fwdMap w T (y : ℂ)).re) (𝓝[>] x) (𝓝 (markPos w T x)) := by
  have hH := GW1W.isRealHalf_of hw hw0 hT
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · refine eventually_nhdsWithin_of_forall fun y (hy : x < y) => ?_
    exact lt_of_lt_of_le ha ((GW1W.markPos_le_iff hw hw0 hT hx (hx.trans_lt hy) (hal y hy)).2 hy.le)
  · have hex : ∃ q : ℚ, x < q ∧ (fwdMap w T ((q : ℝ) : ℂ)).re < b := by
      by_contra hne
      push Not at hne
      exact absurd (GW1W.le_markPos hw hw0 hT fun q hxq _ => hne q hxq) (not_le.2 hb)
    obtain ⟨q, hxq, hqb⟩ := hex
    filter_upwards [Ioo_mem_nhdsGT hxq] with y hy
    exact lt_trans (hH.2.2.2.2.1 y q (hx.trans_lt hy.1) hy.2 (hal y hy.1) (hal q hxq)) hqb

/-- **The left limit of the real flow at a left mark**: if every real point left of `x ≤ 0` is alive, the flow tends
to `markPosL w T x` from the left. -/
theorem tendsto_re_fwdMap_markPosL (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : x ≤ 0)
    (hal : ∀ y : ℝ, y < x → ∃ u, IsForwardSol w (y : ℂ) T u) :
    Tendsto (fun y : ℝ => (fwdMap w T (y : ℂ)).re) (𝓝[<] x) (𝓝 (markPosL w T x)) := by
  have hw' : Continuous (-w) := hw.neg
  have hw0' : (-w) 0 = 0 := by simp [hw0]
  have hal' : ∀ y : ℝ, -x < y → ∃ u, IsForwardSol (-w) (y : ℂ) T u := fun y hy =>
    (Exist.StagedLaw.alive_neg_iff w T y).2 (hal (-y) (by linarith))
  have h1 := tendsto_re_fwdMap_markPos hw' hw0' hT (neg_nonneg.2 hx) hal'
  have hneg : Tendsto (fun y : ℝ => -y) (𝓝[<] x) (𝓝[>] (-x)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(continuous_neg.tendsto x).mono_left nhdsWithin_le_nhds, ?_⟩
    exact eventually_nhdsWithin_of_forall fun y (hy : y < x) => show -x < -y by linarith
  have h2 := (h1.comp hneg).neg
  have e : markPosL w T x = -markPos (-w) T (-x) := rfl
  rw [e]
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply]
  rw [QuantumZipper.F1.fwdMap_reflect_ofReal w hT y, Complex.neg_re, neg_neg]

end Flow

/-! ### The entry data, path and chart -/

/-- **The entry data of a completed retained path in the builder frame**: a Loewner trace `ξ` of `V` through the
horizon `T`, ending at a freshly reached real tip `p`, in the closed half-plane and injective, with the explorer's
seed at `−d ≤ 0` weakly left of all its real points. -/
structure IsEntryData (V : ℝ → ℝ) (T : ℝ) (ξ : ℝ → ℂ) (p d : ℝ) : Prop where
  tip : IsFreshRealTip V T ξ p
  hbar : MapsTo ξ (Icc 0 T) Hbar
  inj : InjOn ξ (Icc 0 T)
  seed : 0 ≤ d
  real : ∀ s ∈ Icc (0 : ℝ) T, (ξ s).im = 0 → -d ≤ (ξ s).re

/-- The retained path of the builder: `s ↦ ξ (s T) + d` on `[0, 1]`. -/
def entryPath (ξ : ℝ → ℂ) (T d : ℝ) (s : ℝ) : ℂ := ξ (s * T) + (d : ℂ)

/-- **The entry chart**: the centred Loewner chart of `V` at the horizon read from `d`, recentred at the left image
of the explorer's seed. -/
def entryChart (V : ℝ → ℝ) (T d : ℝ) : Chart :=
  ((Chart.id.recenter d).loewner V T).recenter (markPosL V T (-d))

/-- The boundary extension of the inverse of the entry chart. -/
def entryInv (V : ℝ → ℝ) (T d : ℝ) (z : ℂ) : ℂ :=
  extendFrom H (fwdMapInv V T) (z + (markPosL V T (-d) : ℂ)) + (d : ℂ)

variable {V : ℝ → ℝ} {T : ℝ} {ξ : ℝ → ℂ} {p d : ℝ}

theorem entryChart_fst (V : ℝ → ℝ) (T d : ℝ) (z : ℂ) :
    (entryChart V T d).1 z = fwdMap V T (z - (d : ℂ)) - (markPosL V T (-d) : ℂ) := rfl

theorem entryChart_inv (V : ℝ → ℝ) (T d : ℝ) (z : ℂ) :
    (entryChart V T d).2.1 z = fwdMapInv V T (z + (markPosL V T (-d) : ℂ)) + (d : ℂ) := rfl

theorem entryChart_lift (V : ℝ → ℝ) (T d : ℝ) (z : ℂ) :
    (entryChart V T d).2.2 z = (logDerivFwd V T (z - (d : ℂ))).im + 0 := rfl

theorem isConformal_entryChart (hV : Continuous V) (hV0 : V 0 = 0) (hT : 0 ≤ T) (d : ℝ) :
    (entryChart V T d).IsConformal :=
  ((Chart.isConformal_id.recenter d).loewner hV hV0 hT).recenter _

/-! ### The path -/

theorem image_entryPath (ξ : ℝ → ℂ) {T : ℝ} (hT : 0 < T) (d : ℝ) :
    entryPath ξ T d '' Icc 0 1 = (fun z : ℂ => z + (d : ℂ)) '' (ξ '' Icc 0 T) := by
  ext z
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨ξ (s * T), ⟨s * T, ⟨mul_nonneg hs.1 hT.le, by nlinarith [hs.2]⟩, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨t / T, ⟨div_nonneg ht.1 hT.le, (div_le_one hT).2 ht.2⟩, ?_⟩
    simp only [entryPath, div_mul_cancel₀ t hT.ne']

theorem IsEntryData.continuousOn_entryPath (h : IsEntryData V T ξ p d) :
    ContinuousOn (entryPath ξ T d) (Icc 0 1) := by
  have hT := h.tip.pos
  refine ContinuousOn.add (h.tip.traceCont.comp (continuous_id.mul continuous_const).continuousOn fun s hs => ?_)
    continuousOn_const
  exact ⟨mul_nonneg hs.1 hT.le, by nlinarith [hs.2]⟩

theorem IsEntryData.entryPath_zero (h : IsEntryData V T ξ p d) : entryPath ξ T d 0 = (d : ℂ) := by
  simp only [entryPath, zero_mul, h.tip.trace.1, zero_add]

theorem IsEntryData.im_entryPath_nonneg (h : IsEntryData V T ξ p d) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ (entryPath ξ T d s).im := by
  have hT := h.tip.pos
  have hm : s * T ∈ Icc (0 : ℝ) T := ⟨mul_nonneg hs.1 hT.le, by nlinarith [hs.2]⟩
  have h1 : 0 ≤ (ξ (s * T)).im := h.hbar hm
  simpa only [entryPath, add_im, ofReal_im, add_zero] using h1

theorem IsEntryData.real_entryPath_nonneg (h : IsEntryData V T ξ p d) {y : ℝ}
    (hy : (y : ℂ) ∈ entryPath ξ T d '' Icc 0 1) : 0 ≤ y := by
  obtain ⟨s, hs, hsy⟩ := hy
  have hT := h.tip.pos
  have hm : s * T ∈ Icc (0 : ℝ) T := ⟨mul_nonneg hs.1 hT.le, by nlinarith [hs.2]⟩
  have him : (ξ (s * T)).im = 0 := by
    have := congrArg Complex.im hsy
    simpa only [entryPath, add_im, ofReal_im, add_zero] using this
  have hre : (ξ (s * T)).re + d = y := by
    have := congrArg Complex.re hsy
    simpa only [entryPath, add_re, ofReal_re] using this
  have := h.real _ hm him
  linarith

theorem IsEntryData.injOn_entryPath (h : IsEntryData V T ξ p d) : InjOn (entryPath ξ T d) (Icc 0 1) := by
  have hT := h.tip.pos
  intro s hs t ht hst
  have hms : s * T ∈ Icc (0 : ℝ) T := ⟨mul_nonneg hs.1 hT.le, by nlinarith [hs.2]⟩
  have hmt : t * T ∈ Icc (0 : ℝ) T := ⟨mul_nonneg ht.1 hT.le, by nlinarith [ht.2]⟩
  have h1 : ξ (s * T) = ξ (t * T) := add_right_cancel hst
  exact mul_right_cancel₀ hT.ne' (h.inj hms hmt h1)

/-! ### Alive points left of the seed -/

theorem IsEntryData.fwdHull_eq (h : IsEntryData V T ξ p d) : fwdHull V T = fillH (ξ '' Icc 0 T) :=
  TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT h.tip.trace h.tip.cont h.tip.zero h.tip.pos h.tip.traceCont

/-- Real points left of the explorer's seed are off the closed hull. -/
theorem IsEntryData.notMem_closure_of_lt (h : IsEntryData V T ξ p d) {x : ℝ} (hx : x < -d) :
    (x : ℂ) ∉ closure (fwdHull V T) := by
  intro hmem
  rw [h.fwdHull_eq] at hmem
  have hZ : IsCompact (ξ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn h.tip.traceCont
  obtain ⟨_, ⟨s, hs, rfl⟩, him, hre⟩ := Sec7.R6Fd.exists_real_le_of_mem_closure_fillH hZ
    (fun _ ⟨s, hs, hz⟩ => hz ▸ h.hbar hs) hmem
  have := h.real s hs him
  linarith

/-- Real points left of the explorer's seed are alive at the horizon. -/
theorem IsEntryData.alive_of_lt (h : IsEntryData V T ξ p d) {x : ℝ} (hx : x < -d) :
    ∃ v, IsForwardSol V (x : ℂ) T v :=
  Aux10.exists_isForwardSol_of_notMem_closure h.tip.cont h.tip.zero h.tip.pos.le
    (ne_of_lt (lt_of_lt_of_le hx (neg_nonpos.2 h.seed))) (h.notMem_closure_of_lt hx)

/-! ### The chart is a left entry chart -/

theorem IsEntryData.fillH_entryPath (h : IsEntryData V T ξ p d) :
    fillH (entryPath ξ T d '' Icc 0 1) = (fun z : ℂ => z + (d : ℂ)) '' fwdHull V T := by
  rw [image_entryPath ξ h.tip.pos d, Restart.fillH_image_add_real, h.fwdHull_eq]

theorem IsEntryData.isDomainChart (h : IsEntryData V T ξ p d) :
    IsDomainChart (H \ fillH (entryPath ξ T d '' Icc 0 1)) (entryChart V T d) := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  rw [h.fillH_entryPath, ← image_add_real_H_diff]
  refine ⟨isConformal_entryChart hV hV0 hT d, ?_, fun z => logDerivFwd V T (z - (d : ℂ)), ⟨?_, fun z hz => ?_⟩,
    fun z _ => ?_⟩
  · -- the image of the inverse
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv0 : 0 < v.im := hv
      have hvm : v + (markPosL V T (-d) : ℂ) ∈ H := by
        show 0 < (v + (markPosL V T (-d) : ℂ)).im
        simpa only [add_im, ofReal_im, add_zero] using hv0
      refine ⟨fwdMapInv V T (v + (markPosL V T (-d) : ℂ)), ?_, rfl⟩
      rw [← QuantumZipper.RS.image_fwdMapInv_H hV hV0 hT]
      exact ⟨_, hvm, rfl⟩
    · rintro ⟨z₀, hz₀, rfl⟩
      rw [← QuantumZipper.RS.image_fwdMapInv_H hV hV0 hT] at hz₀
      obtain ⟨v, hv, rfl⟩ := hz₀
      have hv0 : 0 < v.im := hv
      refine ⟨v - (markPosL V T (-d) : ℂ), ?_, ?_⟩
      · show 0 < (v - (markPosL V T (-d) : ℂ)).im
        simpa only [sub_im, ofReal_im, sub_zero] using hv0
      · rw [entryChart_inv, sub_add_cancel]
  · -- the logarithm is holomorphic
    have h1 := (isDerivLog_fwdMap hV hT).1
    refine h1.comp ((differentiable_id.sub_const _).differentiableOn) fun z hz => ?_
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    simpa only [id, add_sub_cancel_right] using hz₀
  · -- it is a logarithm of the derivative
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have h2 := (isDerivLog_fwdMap hV hT).2 z₀ hz₀
    have hopen : IsOpen (H \ fwdHull V T) := by
      rw [← QuantumZipper.RS.image_fwdMapInv_H hV hV0 hT]
      exact (Chart.isConformal_id.loewner hV hV0 hT).isOpen_image
    have hd : HasDerivAt (fwdMap V T) (deriv (fwdMap V T) z₀) z₀ :=
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hV hT).differentiableAt (hopen.mem_nhds hz₀)).hasDerivAt
    have hd' : HasDerivAt (entryChart V T d).1 (deriv (fwdMap V T) z₀) (z₀ + (d : ℂ)) := by
      have hc : HasDerivAt (fun z : ℂ => fwdMap V T (z - (d : ℂ))) (deriv (fwdMap V T) z₀) (z₀ + (d : ℂ)) :=
        HasDerivAt.comp_sub_const (z₀ + (d : ℂ)) (d : ℂ) (by simpa only [add_sub_cancel_right] using hd)
      exact hc.sub_const _
    rw [hd'.deriv]
    simpa only [add_sub_cancel_right] using h2
  · -- the lift
    rw [entryChart_lift, add_zero]

/-- The forward map at a real point left of the seed, along `ℍ`. -/
theorem IsEntryData.tendsto_fwd_real (h : IsEntryData V T ξ p d) {x : ℝ} (hx : x < 0) :
    Tendsto (entryChart V T d).1 (𝓝[H] (x : ℂ))
      (𝓝 (((fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d) : ℝ) : ℂ)) := by
  have hV := h.tip.cont
  have hT := h.tip.pos.le
  have hal := h.alive_of_lt (x := x - d) (by linarith)
  obtain ⟨u, hu⟩ := hal
  have hc := continuousAt_fwdMap_of_alive hV hT hu
  have hs : Tendsto (fun z : ℂ => z - (d : ℂ)) (𝓝[H] (x : ℂ)) (𝓝 (((x - d : ℝ)) : ℂ)) := by
    have : Tendsto (fun z : ℂ => z - (d : ℂ)) (𝓝 (x : ℂ)) (𝓝 ((x : ℂ) - (d : ℂ))) :=
      (continuous_id.sub continuous_const).tendsto _
    rw [← ofReal_sub] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun z : ℂ => fwdMap V T (z - (d : ℂ))) (𝓝[H] (x : ℂ))
      (𝓝 (fwdMap V T ((x - d : ℝ) : ℂ))) := hc.tendsto.comp hs
  rw [fwdMap_ofReal_real hV hT ⟨u, hu⟩] at h1
  have h2 := h1.sub (tendsto_const_nhds (x := (markPosL V T (-d) : ℂ)))
  rw [← ofReal_sub] at h2
  exact h2

/-- The real boundary values of the forward map tend to `0` at the seed. -/
theorem IsEntryData.tendsto_entry_zero (h : IsEntryData V T ξ p d) :
    Tendsto (fun x : ℝ => (fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d)) (𝓝[<] 0) (𝓝 0) := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  have h1 := tendsto_re_fwdMap_markPosL hV hV0 hT (neg_nonpos.2 h.seed) fun y hy => h.alive_of_lt hy
  have hsh : Tendsto (fun x : ℝ => x - d) (𝓝[<] 0) (𝓝[<] (-d)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun x (hx : x < 0) =>
      show x - d < -d by linarith⟩
    have : Tendsto (fun x : ℝ => x - d) (𝓝 0) (𝓝 (0 - d)) := (continuous_id.sub continuous_const).tendsto _
    rw [zero_sub] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h2 := (h1.comp hsh).sub (tendsto_const_nhds (x := markPosL V T (-d)))
  rw [sub_self] at h2
  exact h2

/-- **The entry chart is a left entry chart of the retained path at `0`.** -/
theorem IsEntryData.isLeftEntryChart (h : IsEntryData V T ξ p d) :
    IsLeftEntryChart (entryPath ξ T d '' Icc 0 1) 0 (entryChart V T d) := by
  have hV := h.tip.cont
  have hV0 := h.tip.zero
  have hT := h.tip.pos.le
  refine ⟨h.isDomainChart, ⟨fun x => (fwdMap V T ((x - d : ℝ) : ℂ)).re - markPosL V T (-d),
    fun x hx => h.tendsto_fwd_real hx, h.tendsto_entry_zero⟩, ?_, fun x hx => ?_⟩
  · -- infinity goes to infinity
    obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hV hV0 hT
    rw [h.fillH_entryPath, ← image_add_real_H_diff]
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(C + |d| + |markPosL V T (-d)|))
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨z₀, hz₀, rfl⟩ := hz
    have h1 := hC z₀ hz₀
    rw [entryChart_fst, add_sub_cancel_right]
    have e : z₀ + (d : ℂ) = (fwdMap V T z₀ - (markPosL V T (-d) : ℂ)) - (fwdMap V T z₀ - z₀) + (d : ℂ) +
        (markPosL V T (-d) : ℂ) := by ring
    have h3 : ‖z₀ + (d : ℂ)‖ ≤ ‖fwdMap V T z₀ - (markPosL V T (-d) : ℂ)‖ + ‖fwdMap V T z₀ - z₀‖ + ‖(d : ℂ)‖ +
        ‖(markPosL V T (-d) : ℂ)‖ := by
      calc ‖z₀ + (d : ℂ)‖ = ‖(fwdMap V T z₀ - (markPosL V T (-d) : ℂ)) - (fwdMap V T z₀ - z₀) + (d : ℂ) +
            (markPosL V T (-d) : ℂ)‖ := by rw [← e]
        _ ≤ ‖(fwdMap V T z₀ - (markPosL V T (-d) : ℂ)) - (fwdMap V T z₀ - z₀) + (d : ℂ)‖ +
            ‖(markPosL V T (-d) : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖(fwdMap V T z₀ - (markPosL V T (-d) : ℂ)) - (fwdMap V T z₀ - z₀)‖ + ‖(d : ℂ)‖ +
            ‖(markPosL V T (-d) : ℂ)‖ := by gcongr; exact norm_add_le _ _
        _ ≤ ‖fwdMap V T z₀ - (markPosL V T (-d) : ℂ)‖ + ‖fwdMap V T z₀ - z₀‖ + ‖(d : ℂ)‖ +
            ‖(markPosL V T (-d) : ℂ)‖ := by gcongr; exact norm_sub_le _ _
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h3
    linarith
  · -- the lift at the free real points
    have hx' : (((x - d : ℝ)) : ℂ) ∉ closure (fwdHull V T) := h.notMem_closure_of_lt (by linarith)
    have h1 := Supp8.BHMean.tendsto_im_logDerivFwd_of_notMem_closure hV hV0 hT hx'
    have hs : Tendsto (fun z : ℂ => z - (d : ℂ)) (𝓝[H] (x : ℂ)) (𝓝[H] (((x - d : ℝ)) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z (hz : 0 < z.im) => ?_⟩
      · have : Tendsto (fun z : ℂ => z - (d : ℂ)) (𝓝 (x : ℂ)) (𝓝 ((x : ℂ) - (d : ℂ))) :=
          (continuous_id.sub continuous_const).tendsto _
        rw [← ofReal_sub] at this
        exact this.mono_left nhdsWithin_le_nhds
      · show 0 < (z - (d : ℂ)).im
        simpa only [sub_im, ofReal_im, sub_zero] using hz
    refine (h1.comp hs).congr fun z => ?_
    simp only [Function.comp_apply, entryChart_lift, add_zero]

/-! ### The boundary inverse -/

theorem IsEntryData.hasBdryLimits (h : IsEntryData V T ξ p d) : HasBdryLimits (fwdMapInv V T) :=
  TraceClose.hasBdryLimits_of_isLoewnerTraceLT h.tip.trace h.tip.cont h.tip.zero h.tip.pos h.tip.traceCont

/-- The boundary inverse is continuous on the closed half-plane. -/
theorem IsEntryData.continuousOn_entryInv (h : IsEntryData V T ξ p d) :
    ContinuousOn (entryInv V T d) {z | 0 ≤ z.im} := by
  have hc : ContinuousOn (extendFrom H (fwdMapInv V T)) Hbar := h.hasBdryLimits.continuousOn
  refine ContinuousOn.add (hc.comp (continuous_id.add continuous_const).continuousOn fun z (hz : 0 ≤ z.im) => ?_)
    continuousOn_const
  show 0 ≤ (z + (markPosL V T (-d) : ℂ)).im
  simpa only [add_im, ofReal_im, add_zero] using hz

/-- On `ℍ` the boundary inverse is the inverse of the entry chart. -/
theorem entryInv_eqOn (hV : Continuous V) (hV0 : V 0 = 0) (hT : 0 ≤ T) (d : ℝ) :
    EqOn (entryInv V T d) (entryChart V T d).2.1 H := by
  intro z hz
  have hz0 : 0 < z.im := hz
  have hzm : z + (markPosL V T (-d) : ℂ) ∈ H := by
    show 0 < (z + (markPosL V T (-d) : ℂ)).im
    simpa only [add_im, ofReal_im, add_zero] using hz0
  rw [entryInv, extendFrom_fwdMapInv_of_mem hV hV0 hT hzm, entryChart_inv]

/-- **The boundary inverse has finite fibres on the closed half-plane.** -/
theorem IsEntryData.finite_fibre (h : IsEntryData V T ξ p d) (z : ℂ) :
    (entryInv V T d ⁻¹' {z} ∩ {v | 0 ≤ v.im}).Finite := by
  refine Lv.finite_fibre_of_isLeftEntryChart h.continuousOn_entryPath ?_ (fun z' => ?_) h.isLeftEntryChart
    h.continuousOn_entryInv (entryInv_eqOn h.tip.cont h.tip.zero h.tip.pos.le d) z
  · rw [h.entryPath_zero, ofReal_im]
  · refine (subsingleton_of_forall_eq_iff_inj h).finite
where
  subsingleton_of_forall_eq_iff_inj {z' : ℂ} (h : IsEntryData V T ξ p d) :
      (entryPath ξ T d ⁻¹' {z'} ∩ Icc 0 1).Subsingleton := fun s hs t ht =>
    h.injOn_entryPath hs.2 ht.2 (hs.1.trans ht.1.symm)

/-- **The entry chart keeps the lift's boundary value `0` at free real points.** -/
theorem liftRealOn_entryChart (hV : Continuous V) (hV0 : V 0 = 0) (hT : 0 ≤ T) (d : ℝ) :
    FinRel.LiftRealOn (entryChart V T d) :=
  FinRel.liftRealOn_recenter (FinRel.liftRealOn_loewner (Chart.isConformal_id.recenter d)
    (GW1P.hasProperBdryExt_recenter_id d) (FinRel.liftRealOn_id_recenter d) hV hV0 hT) _

end Term

end InteractingSLE.RealContact

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermAssemble
import InteractingSLE.Spec.Supplement.GW1ActiveWord
import InteractingSLE.Spec.Supplement.GW2SdpHeight
import InteractingSLE.Spec.Supplement.SB2WdLaunch
import InteractingSLE.Spec.Supplement.Aux10FullLocal
import InteractingSLE.Spec.Sec7.R6FdLand

/-!
# The terminal retained pair: the marks at a freshly reached real tip (deterministic)

Packet PROVE-RC-TERM (ruling R124), steps P1.1–P1.2 and the word clause of P2 of
`planning/handoffs/PROVE-RC-POCKET.md`. At a freshly reached negative real tip `q` of a trace `γ ⊆ ℍ̄`
(`Term.IsFreshRealTip`, with `γ(s) ≠ q` before the horizon):

* **`IsFreshRealTip.alive_of_lt`** (P1.1): every real point left of the tip is alive at the horizon. A dead point
  `p < q` would be adherent to the hull, so the trace would have a real point `≤ p`, reached before the horizon; then
  the tip lies strictly between two real trace points of an earlier hull, hence in its closure — not fresh;
* **`IsFreshRealTip.markPos_pos`**: the chart position of every right mark is positive (the seed position of the first
  path). If alive points right of `0` had images tending to `0`, the continuous boundary extension of the inverse map
  would send them to the tip `q < 0`;
* **`IsFreshRealTip.markPosL_neg_of_lt`**, **`IsFreshRealTip.markPosL_tip`** (P1.2, "the left marks swallowed by the
  lifetime merge into the driver"): the left mark started at a point left of the tip stays strictly left of the
  driver, and the left mark started at the tip (or right of it) is at the driver at the horizon.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.RealContact

namespace Term

open Exist.Staged Exist.StagedLaw

variable {U : ℝ → ℝ} {T : ℝ} {γ : ℝ → ℂ} {q : ℝ}

/-- The forward value of an alive real point is real. -/
theorem fwdMap_ofReal_eq {p : ℝ} (hU : Continuous U) (hT : 0 ≤ T) {v : ℝ → ℂ} (hv : IsForwardSol U (p : ℂ) T v) :
    v T = ((fwdMap U T (p : ℂ)).re : ℂ) := by
  have h1 : fwdMap U T (p : ℂ) = v T := QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨hT, le_rfl⟩
  have h2 : (v T).im = 0 := QuantumZipper.im_isForwardSol_real hU hT hv T ⟨hT, le_rfl⟩
  rw [h1]
  exact Complex.ext (by simp) (by simp [h2])

/-- The boundary extension of the inverse map sends the forward value of an alive real point back to the point. -/
theorem IsFreshRealTip.extendFrom_fwdMap (h : IsFreshRealTip U T γ q) {p : ℝ} {v : ℝ → ℂ}
    (hv : IsForwardSol U (p : ℂ) T v) :
    extendFrom H (fwdMapInv U T) ((fwdMap U T (p : ℂ)).re : ℂ) = p := by
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT h.trace h.cont h.zero h.pos h.traceCont
  have h1 := Sec7.SideHeight.extendFrom_eq_of_isForwardSol' hB h.cont h.zero h.pos.le
    (show (p : ℂ) ∈ Hbar by simp [Hbar]) hv
  rwa [fwdMap_ofReal_eq h.cont h.pos.le hv] at h1

/-- **Real points left of a freshly reached real tip are alive at the horizon.** -/
theorem IsFreshRealTip.alive_of_lt (h : IsFreshRealTip U T γ q) (hq : q < 0) (hγH : MapsTo γ (Icc 0 T) Hbar)
    (hne : ∀ s, 0 ≤ s → s < T → γ s ≠ q) {p : ℝ} (hp : p < q) : ∃ v, IsForwardSol U (p : ℂ) T v := by
  refine Aux10.exists_isForwardSol_of_notMem_closure h.cont h.zero h.pos.le (ne_of_lt (hp.trans hq)) fun hmem => ?_
  rw [TraceClose.fwdHull_eq_fillH_of_isLoewnerTraceLT h.trace h.cont h.zero h.pos h.traceCont] at hmem
  have hZ : IsCompact (γ '' Icc 0 T) := isCompact_Icc.image_of_continuousOn h.traceCont
  obtain ⟨_, ⟨s, hs, rfl⟩, him, hre⟩ := Sec7.R6Fd.exists_real_le_of_mem_closure_fillH hZ
    (fun _ ⟨s, hs, hz⟩ => hz ▸ hγH hs) hmem
  have hsT : s < T := by
    rcases hs.2.lt_or_eq with hlt | heq
    · exact hlt
    · exfalso
      rw [heq, h.tip, Complex.ofReal_re] at hre
      exact absurd hp (not_lt.2 hre)
  have hfresh := h.fresh s hs.1 hsT
  rw [h.trace.2.2 s hs.1 hsT] at hfresh
  refine hfresh (YuanCharacterisation.mem_closure_fillH_of_lt_of_lt
    (h.traceCont.mono (Icc_subset_Icc_right hsT.le)) (fun t ht => hγH ⟨ht.1, ht.2.trans hsT.le⟩)
    (u₁ := s) (u₂ := 0) ⟨hs.1, le_rfl⟩ ⟨le_rfl, hs.1⟩ him (by rw [h.trace.1, Complex.zero_im])
    (hre.trans_lt hp) (by rw [h.trace.1, Complex.zero_re]; exact hq) ?_)
  rintro ⟨t, ht, htq⟩
  exact hne t ht.1 (ht.2.trans_lt hsT) htq

/-- **The right marks stay strictly right of the driver** at a freshly reached negative real tip. -/
theorem IsFreshRealTip.markPos_pos (h : IsFreshRealTip U T γ q) (hq : q < 0) {x : ℝ} (hx : 0 ≤ x) :
    0 < markPos U T x := by
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT h.trace h.cont h.zero h.pos h.traceCont
  have h0 : extendFrom H (fwdMapInv U T) 0 = (q : ℂ) := by
    rw [TraceClose.extendFrom_zero_eq h.trace h.cont h.zero h.pos h.traceCont, h.tip]
  have hc := hB.continuousOn 0 (show (0 : ℂ) ∈ Hbar by simp [Hbar])
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδc⟩ := hc (-q) (by linarith)
  refine lt_of_lt_of_le hδ (Theorem14.GW1W.le_markPos h.cont h.zero h.pos.le fun p hxp hal => ?_)
  obtain ⟨v, hv⟩ := hal
  by_contra hlt
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt hx hxp
  have hre : 0 < (fwdMap U T ((p : ℝ) : ℂ)).re := by
    have h1 := re_pos_of_isForwardSol h.cont h.zero hp0 hv (s := T) ⟨h.pos.le, le_rfl⟩
    rwa [← QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨h.pos.le, le_rfl⟩] at h1
  have hdist : dist (((fwdMap U T ((p : ℝ) : ℂ)).re : ℝ) : ℂ) 0 < δ := by
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hre]
    exact not_le.1 hlt
  have h2 := hδc (show (((fwdMap U T ((p : ℝ) : ℂ)).re : ℝ) : ℂ) ∈ Hbar by simp [Hbar]) hdist
  rw [h.extendFrom_fwdMap hv, h0, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2
  have h3 : (p : ℝ) - q ≤ |(p : ℝ) - q| := le_abs_self _
  linarith

/-- The forward value of an alive negative real point is nonpositive. -/
theorem re_fwdMap_nonpos (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 ≤ T) {p : ℝ} (hp : p < 0)
    (hal : ∃ v, IsForwardSol U (p : ℂ) T v) : (fwdMap U T (p : ℂ)).re ≤ 0 :=
  ((Theorem14.GW1W.le_markPosL_iff hU hU0 hT hp.le hp hal).2 le_rfl).trans
    (Theorem14.GW1W.markPosL_nonpos hU hU0 hT hp.le)

/-- **A left mark started left of the tip stays strictly left of the driver.** -/
theorem IsFreshRealTip.markPosL_neg_of_lt (h : IsFreshRealTip U T γ q) (hq : q < 0)
    (hγH : MapsTo γ (Icc 0 T) Hbar) (hne : ∀ s, 0 ≤ s → s < T → γ s ≠ q) {p : ℝ} (hp : p < q) :
    markPosL U T p < 0 := by
  obtain ⟨p', hp1, hp2⟩ := exists_between hp
  have hal := h.alive_of_lt hq hγH hne hp2
  have hp'0 : p' < 0 := hp2.trans hq
  have h1 : ¬ (fwdMap U T (p' : ℂ)).re ≤ markPosL U T p := fun hle =>
    absurd ((Theorem14.GW1W.le_markPosL_iff h.cont h.zero h.pos.le (hp.trans hq).le hp'0 hal).1 hle)
      (not_le.2 hp1)
  exact (not_le.1 h1).trans_le (re_fwdMap_nonpos h.cont h.zero h.pos.le hp'0 hal)

/-- **The left mark started at the tip is at the driver at the horizon** (the left end of the image of the hull is
the driving point). -/
theorem IsFreshRealTip.markPosL_tip (h : IsFreshRealTip U T γ q) (hq : q < 0) (hγH : MapsTo γ (Icc 0 T) Hbar)
    (hne : ∀ s, 0 ≤ s → s < T → γ s ≠ q) : markPosL U T q = 0 := by
  have hU := h.cont
  have hU0 := h.zero
  have hT := h.pos.le
  refine le_antisymm (Theorem14.GW1W.markPosL_nonpos hU hU0 hT hq.le) (le_of_not_gt fun hneg => ?_)
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT h.trace hU hU0 h.pos h.traceCont
  obtain ⟨C, hC⟩ := exists_norm_fwdMap_sub_le hU hU0 hT
  -- alive points increasing to the tip, and their forward values
  set p : ℕ → ℝ := fun n => q - 1 / ((n : ℝ) + 1) with hp
  have hpq : ∀ n, p n < q := fun n => by
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hp]; linarith
  have hal : ∀ n, ∃ v, IsForwardSol U ((p n : ℝ) : ℂ) T v := fun n => h.alive_of_lt hq hγH hne (hpq n)
  set y : ℕ → ℂ := fun n => (((fwdMap U T ((p n : ℝ) : ℂ)).re : ℝ) : ℂ) with hy
  have hyle : ∀ n, (y n).re ≤ markPosL U T q := fun n => by
    simp only [hy, Complex.ofReal_re]
    exact (Theorem14.GW1W.le_markPosL_iff hU hU0 hT hq.le ((hpq n).trans hq) (hal n)).2 (hpq n).le
  have hFy : ∀ n, extendFrom H (fwdMapInv U T) (y n) = (p n : ℂ) := fun n => by
    obtain ⟨v, hv⟩ := hal n
    exact h.extendFrom_fwdMap hv
  -- the forward values stay in a compact set of real points away from `0`
  have hpn : ∀ n, |p n| ≤ |q| + 1 := fun n => by
    have h1 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
    rw [abs_le]
    have h3 := neg_abs_le q
    have h4 := le_abs_self q
    simp only [hp]
    constructor <;> linarith
  have hyn : ∀ n, ‖y n‖ ≤ |q| + 1 + C := fun n => by
    obtain ⟨v, hv⟩ := hal n
    have hmem : ((p n : ℝ) : ℂ) ∉ closure (fwdHull U T) :=
      Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hU hT hv
    have h1 : fwdMap U T ((p n : ℝ) : ℂ) = y n := by
      rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨hT, le_rfl⟩, fwdMap_ofReal_eq hU hT hv]
    have h2 : ‖y n - (p n : ℂ)‖ ≤ C := by
      rw [← h1]
      exact norm_fwdMap_sub_le_of_alive hU hU0 hT hC hv
    have h3 : ‖y n‖ ≤ ‖y n - (p n : ℂ)‖ + ‖((p n : ℝ) : ℂ)‖ := by
      have := norm_add_le (y n - (p n : ℂ)) (p n : ℂ)
      rwa [sub_add_cancel] at this
    have h4 : ‖((p n : ℝ) : ℂ)‖ = |p n| := by rw [Complex.norm_real, Real.norm_eq_abs]
    linarith [hpn n]
  have hScl : IsClosed {z : ℂ | z.im = 0 ∧ z.re ≤ markPosL U T q} :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hScomp : IsCompact ({z : ℂ | z.im = 0 ∧ z.re ≤ markPosL U T q} ∩ closedBall (0 : ℂ) (|q| + 1 + C)) :=
    (isCompact_closedBall _ _).inter_left hScl
  have hyS : ∀ n, y n ∈ {z : ℂ | z.im = 0 ∧ z.re ≤ markPosL U T q} ∩ closedBall (0 : ℂ) (|q| + 1 + C) :=
    fun n => ⟨⟨by simp only [hy, Complex.ofReal_im], hyle n⟩, mem_closedBall_zero_iff.2 (hyn n)⟩
  obtain ⟨a, haS, φ, hφ, hlim⟩ := hScomp.tendsto_subseq hyS
  have haH : a ∈ Hbar := by
    show 0 ≤ a.im
    rw [haS.1.1]
  have hl1 : Tendsto (fun n => extendFrom H (fwdMapInv U T) (y (φ n))) atTop
      (𝓝 (extendFrom H (fwdMapInv U T) a)) := by
    have hw : Tendsto (y ∘ φ) atTop (𝓝[Hbar] a) :=
      tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => by
        show 0 ≤ (y (φ n)).im
        simp only [hy, Complex.ofReal_im, le_refl]⟩
    exact (hB.continuousOn a haH).tendsto.comp hw
  have hl2 : Tendsto (fun n => extendFrom H (fwdMapInv U T) (y (φ n))) atTop (𝓝 (q : ℂ)) := by
    have e : (fun n => extendFrom H (fwdMapInv U T) (y (φ n))) = fun n => ((p (φ n) : ℝ) : ℂ) :=
      funext fun n => hFy (φ n)
    rw [e]
    have h1 : Tendsto (fun n : ℕ => q - 1 / ((n : ℝ) + 1)) atTop (𝓝 (q - 0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at h1
    exact (Complex.continuous_ofReal.tendsto q).comp (h1.comp hφ.tendsto_atTop)
  have ha0 : a = 0 := h.eq_zero_of_extendFrom_eq haH (tendsto_nhds_unique hl1 hl2)
  have hare := haS.1.2
  rw [ha0, Complex.zero_re] at hare
  exact absurd hneg (not_lt.2 hare)
where
  norm_fwdMap_sub_le_of_alive {U : ℝ → ℝ} {T C : ℝ} (hU : Continuous U) (hU0 : U 0 = 0) (hT : 0 ≤ T)
      (hC : ∀ z ∈ H \ fwdHull U T, ‖fwdMap U T z - z‖ ≤ C) {p : ℝ} {v : ℝ → ℂ}
      (hv : IsForwardSol U (p : ℂ) T v) : ‖fwdMap U T (p : ℂ) - (p : ℂ)‖ ≤ C := by
    have hlim : Tendsto (fwdMap U T) (𝓝[H] (p : ℂ)) (𝓝 (v T)) :=
      tendsto_fwdMap_of_isForwardSol hU hT hv
    have hmem : ((p : ℝ) : ℂ) ∉ closure (fwdHull U T) :=
      Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hU hT hv
    have hev : ∀ᶠ z in 𝓝[H] (p : ℂ), z ∈ H \ fwdHull U T := by
      have h1 : ∀ᶠ z in 𝓝[H] (p : ℂ), z ∈ (closure (fwdHull U T))ᶜ :=
        mem_nhdsWithin_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hmem)
      filter_upwards [h1, self_mem_nhdsWithin] with z hz hzH
      exact ⟨hzH, fun hK => hz (subset_closure hK)⟩
    have hNe : (𝓝[H] (p : ℂ)).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; simp [Hbar])
    have hdiff : Tendsto (fun z => ‖fwdMap U T z - z‖) (𝓝[H] (p : ℂ)) (𝓝 ‖v T - (p : ℂ)‖) :=
      (hlim.sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm
    rw [QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨hT, le_rfl⟩]
    exact le_of_tendsto hdiff (hev.mono fun z hz => hC z hz)

/-! ### The word just left of the driver -/

open Restart in
/-- **The stop word left of the driver**: at a non-jump `z < 0` it is the original word at any non-jump `y < 0` which
has the same left marks to its right (the marks whose positions at the horizon lie right of `z`). -/
theorem fn_stopWord_eq_of_iff {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) (r : RecData) {z y : ℝ}
    (hz : z < 0) (hzJ : z ∉ (stopWord κ (c, θ, r)).jumps) (hy : y < 0) (hyJ : y ∉ c.jumps)
    (hiff : ∀ i : Fin (flowLineNL c.fn c.jumps 0), y < flowLineXL c.fn c.jumps 0 i ↔
      z < markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i)) :
    (stopWord κ (c, θ, r)).fn z = c.fn y := by
  classical
  have hb := c.isPiecewiseConstantBoundaryData
  have hfn : (stopWord κ (c, θ, r)).fn z =
      -sleLambda κ * (1 + ∑ i ∈ Finset.univ.filter
        (fun i => z < markPosL (rdrv r) (rtime r) (flowLineXL c.fn c.jumps 0 i)),
          flowLineRhoL κ c.fn c.jumps 0 θ i) - θ * QuantumZipper.chiC κ := by
    have h := fn_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2
      (θ * QuantumZipper.chiC κ) (Theorem14.GW1W.isMarkOrder_stopWord c r) hzJ hz.ne
    refine h.trans ?_
    rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hz]
    simp only [padFL_fst_fst_fin, padFL_snd_fst_fin]
  have h1 := Exist.forceBoundaryData_flowLine_seed hκ hb 0 θ hy.ne (by simpa using hyJ)
  rw [Sec4.forceBoundaryData_of_neg _ _ _ _ hy, add_zero] at h1
  rw [hfn, Finset.filter_congr fun i _ => (hiff i).symm]
  linarith

open Restart PiecewiseConstantBoundaryData in
/-- **The word of the chart field just left of the driver is the original word just left of the tip** (the left
marks at or right of the tip have merged into the driver; those left of it have not). -/
theorem IsFreshRealTip.leftLim_stopWord {κ : ℝ} (hκ : 0 < κ) (c : BoundaryWord) (θ : ℝ) {r : RecData}
    (h : IsFreshRealTip (rdrv r) (rtime r) γ q) (hq : q < 0) (hγH : MapsTo γ (Icc 0 (rtime r)) Hbar)
    (hne : ∀ s, 0 ≤ s → s < rtime r → γ s ≠ q) :
    leftLim (stopWord κ (c, θ, r)).fn 0 = leftLim c.fn q := by
  classical
  have hU := continuous_rdrv r
  have hU0 := rdrv_zero r
  have hT := rtime_nonneg r
  set xL := flowLineXL c.fn c.jumps 0 with hxL
  have hxL0 : ∀ i, xL i ≤ 0 := fun i => Restart.FlowStopIdentCMI.flowLineXL_nonpos' c.fn c.jumps 0 i
  -- a point `y₀ < q` right of every left mark which is left of the tip
  set S : Finset ℝ := insert (q - 1) ((Finset.univ.image xL).filter (· < q)) with hS
  have hSne : S.Nonempty := ⟨q - 1, Finset.mem_insert_self _ _⟩
  have hSlt : ∀ s ∈ S, s < q := fun s hs => by
    rcases Finset.mem_insert.1 hs with rfl | hs'
    · linarith
    · exact (Finset.mem_filter.1 hs').2
  have hmax : S.max' hSne < q := hSlt _ (Finset.max'_mem S hSne)
  set y₀ : ℝ := (S.max' hSne + q) / 2 with hy₀
  have hy₀q : y₀ < q := by rw [hy₀]; linarith
  have hy₀0 : y₀ ≤ 0 := (hy₀q.trans hq).le
  have hmarks : ∀ i, xL i < q → xL i < y₀ := fun i hi => by
    have hmem : xL i ∈ S := Finset.mem_insert_of_mem
      (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩, hi⟩)
    have := Finset.le_max' S _ hmem
    rw [hy₀]; linarith
  have hm : markPosL (rdrv r) (rtime r) y₀ < 0 := h.markPosL_neg_of_lt hq hγH hne hy₀q
  have htip : markPosL (rdrv r) (rtime r) q = 0 := h.markPosL_tip hq hγH hne
  -- the key identity
  have hkey : ∀ z ∈ Ioo (markPosL (rdrv r) (rtime r) y₀) 0, z ∉ (stopWord κ (c, θ, r)).jumps →
      ∀ t ∈ Ioo y₀ q, t ∉ c.jumps → (stopWord κ (c, θ, r)).fn z = c.fn t := by
    intro z hz hzJ t ht htJ
    refine fn_stopWord_eq_of_iff hκ c θ r hz.2 hzJ (ht.2.trans hq) htJ fun i => ⟨fun hti => ?_, fun hzi => ?_⟩
    · have hqi : q ≤ xL i := by
        by_contra hcon
        exact absurd (hti.trans ((hmarks i (not_le.1 hcon)).trans ht.1)) (lt_irrefl _)
      have h1 := Sec7.StripSideHeightProb.markPosL_anti hU hU0 hT (hxL0 i) hqi
      rw [htip] at h1
      exact hz.2.trans_le h1
    · by_contra hcon
      have hiq : xL i < q := by
        by_contra hcon'
        exact hcon (ht.2.trans_le (not_lt.1 hcon'))
      have h1 := Sec7.StripSideHeightProb.markPosL_anti hU hU0 hT hy₀0 (hmarks i hiq).le
      exact absurd (hzi.trans_le h1) (not_lt.2 hz.1.le)
  obtain ⟨t₀, ht₀1, ht₀2, ht₀J⟩ := Sec4.exists_mem_Ioo_not_mem c.jumps hy₀q
  obtain ⟨z₀, hz₀1, hz₀2, hz₀J⟩ := Sec4.exists_mem_Ioo_not_mem (stopWord κ (c, θ, r)).jumps hm
  have e1 : leftLim (stopWord κ (c, θ, r)).fn 0 = c.fn t₀ :=
    Sec4.leftLim_eq_of_forall_notMem (stopWord κ (c, θ, r)).jumps hm fun z hz hzJ =>
      hkey z hz hzJ t₀ ⟨ht₀1, ht₀2⟩ ht₀J
  have e2 : leftLim c.fn q = c.fn t₀ :=
    Sec4.leftLim_eq_of_forall_notMem c.jumps hy₀q fun t ht htJ =>
      (hkey z₀ ⟨hz₀1, hz₀2⟩ hz₀J t ht htJ).symm.trans (hkey z₀ ⟨hz₀1, hz₀2⟩ hz₀J t₀ ⟨ht₀1, ht₀2⟩ ht₀J)
  rw [e1, e2]

end Term

end InteractingSLE.RealContact

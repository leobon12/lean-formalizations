/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YfMain
import InteractingSLE.Spec.Supplement.SB2YgPiece
import InteractingSLE.Spec.Supplement.SB2YhSeed
import InteractingSLE.Spec.Supplement.SB2YhRel
import InteractingSLE.Spec.Supplement.SB2YhGood
import InteractingSLE.Spec.Sec5.CrossRestartKernelSlitBase
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Supplement.GW2GmJ32Shift

/-!
# `Om.IsStageS2` at a tail stage, at one sample

Packet PROVE-T14-SB2LIFT (round 32, D38). **`isStageS2_tail`**: GEOM2's S2 record for B's stage chart `c` (the run
chart at a tail stage `n ≥ 1` whose start state contains `R = max (A ∩ ℝ)`), the canonical chart
`Φ = Mo.hullChart (fill X) x₀` of the retained union `X = A ∪ P_n` and B's piece stopped at a time `t ∈ (0, ζ)`, from

* the walk facts at the sample (those of CORNER's `Dv.isDrivenCurve_walkStage_old`);
* the tip of B's piece at `t` in `ℍ` (B's stage coordinates; almost sure at a fixed time, `SB2YhTip`);
* `x₀` the right entry value of `Φ` at `realMax X` (NOJUMP's `StageGoodAt.entry`);
* a relative version at the sample: a continuous driver `W` from `0` with Loewner trace `ηV`, a continuous monotone
  clock `a` from `0` with `0 < a t < ∞`, and the trace identity `ηV (a s) = Φ.1 (pc s)` for `s ≤ t` with `pc s` in
  `Φ`'s domain, `pc` B's physical piece (`Na.StageVersionG.trace` with `t_L = 0`).

The clock is strictly increasing on `[0, t]` (B's piece is injective and its times off `fill X` are dense), the link
holds at those times, and `Sx.isStageS2_of_dense` assembles the record. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **A piece point read off the domain is the chart inverse of an interior trace point.** -/
theorem trOf_mem_H_of_good {c : Chart} {Y : Set ℂ} (hcD : IsDomainChart (H \ Y) c) (hYo : IsOpen (H \ Y))
    {gc : ℂ → ℂ} (hgc : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (gc q))) {z : ℂ} (hz : z ∈ Hbar)
    (hgood : LuM.bdVal c z ∈ H \ Y) : z ∈ H ∧ LuM.bdVal c z = c.2.1 z := by
  have hcont : ContinuousOn c.2.1 H := hcD.isConformal.1.continuousOn
  by_cases hzH : z ∈ H
  · exact ⟨hzH, LuM.bdVal_eq_of_mem_H hcont hzH⟩
  exfalso
  have hzre : z.im = 0 := le_antisymm (not_lt.1 hzH) hz
  have hb : LuM.bdVal c z = gc z := LuM.bdVal_eq_of_tendsto hz (hgc z hz)
  rw [hb] at hgood
  have : (𝓝[H] z).NeBot := GW1P.neBot_nhdsWithin_H hz
  have hfc : ContinuousAt c.1 (gc z) :=
    (hcD.differentiableOn_fwd.differentiableAt (hYo.mem_nhds hgood)).continuousAt
  have h1 : Tendsto (fun w => c.1 (c.2.1 w)) (𝓝[H] z) (𝓝 (c.1 (gc z))) := hfc.tendsto.comp (hgc z hz)
  have h2 : Tendsto (fun w => c.1 (c.2.1 w)) (𝓝[H] z) (𝓝 z) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun w hw => (hcD.fwd_inv hw).symm)
  have he : c.1 (gc z) = z := tendsto_nhds_unique h1 h2
  have hmem := hcD.fwd_mem hgood
  rw [he] at hmem
  exact hzH hmem

/-- **GEOM2's S2 record at a tail stage, at one sample.** -/
theorem isStageS2_tail {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ} (hn : 0 < n)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hpinv : LuM.PInv 0 (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    {pA : ℝ → ℂ} (hpc : ContinuousOn pA (Icc 0 1)) (hp0 : pA 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (pA s).im) (hpv : LuM.PInv 0 (pA '' Icc 0 1))
    {β : ℝ≥0 → ℂ} (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hβr : range β = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hS1 : pA '' Icc 0 1 ⊆ InteractingSLE.closedLeftSide β)
    (hR : (realMax (pA '' Icc 0 1) : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ
      true) D n))
    (hS3 : ∀ tR : ℝ≥0, β tR = (realMax (pA '' Icc 0 1) : ℂ) →
      ∀ s₁ s₂ : ℝ≥0, tR ≤ s₁ → s₁ < s₂ → ¬ β '' Ioo s₁ s₂ ⊆ pA '' Icc 0 1 ∩ H)
    {t : ℝ≥0} (ht0 : 0 < t) (htζ : (t : ℝ≥0∞) < (D n).2) (htip : LP.traceAt t (D n).1 ∈ H) {x₀ : ℝ}
    (hent : IsRightEntryChart (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
      (realMax (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ((Mo.hullChart
      (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) 0).recenter x₀))
    {W : ℝ≥0 → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0) {a : ℝ≥0 → ℝ≥0∞} (hac : Continuous a)
    (ham : Monotone a) (ha0 : a 0 = 0) (hat : 0 < a t) (hatop : a t ≠ ⊤) {ηV : ℝ → ℂ}
    (hηV : IsLoewnerTrace (fun s : ℝ => W s.toNNReal) ηV)
    (hlink : ∀ s : ℝ≥0, s ≤ t → pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s ∈
      ((Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
      x₀).dom : Set ℂ) →
      ηV (a s).toReal = (Mo.hullChart (fillH (pA '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ
        true) D n)) x₀).1 (pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) s)) :
    Om.IsStageS2 (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) (Mo.hullChart (fillH (pA
      '' Icc 0 1 ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) x₀) (fillH (pA '' Icc 0 1 ∪
      SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n))
      (fun x : ℝ => (D n).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t : ℝ≥0∞) (D n).2)).toNNReal) (t : ℝ)
      (fun s : ℝ => W s.toNNReal) ((a t).toNNReal : ℝ) := by
  classical
  set w := boundaryWalkSpec b jumps θ true with hw
  set s := ExplState.run κ b jumps w D n with hs
  set Pn := SB.prefixPhysSet κ b jumps w D n with hPn
  set X := pA '' Icc 0 1 ∪ Pn with hXdef
  set c := stChart s with hc
  set Φ := Mo.hullChart (fillH X) x₀ with hΦ
  obtain ⟨⟨c', θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnd : stStatus s ≠ GW1Conn.stDone := WalkIntRunChron.not_done_of_launch w D hl'
  have hpos : (D n).2 ≠ 0 := ne_bot_of_gt htζ
  have hPR : GW1P.PieceRegular (D n).1 (D n).2 := by
    have h := hP n c' θ' hl'
    rwa [Lx.instrTime_boundaryWalk_of_launch hl', min_eq_right le_top] at h
  -- the retained union, the seed and the stage chart
  obtain ⟨hXc, hXh, hRx, hXle, ⟨gX, hgX, hgXf⟩, hden⟩ :=
    stage_good_facts hP hW hlm hlh hl hpos hpinv hpc hp0 hpH hpv hβ hβ0 hβr hS1 hR hS3
  obtain ⟨-, e, gc, Cc, -, -, hgc, -, hCc, -, hgpos, hgre⟩ := stage_seed_facts hP hlm hlh hn hl
  obtain ⟨s₀, LY, -, -, hcD, hY, hmap, hLY, hlift, -, -⟩ := stageChart_facts w D hP n hnd
  have hYB : fillH Pn ⊆ fillH X := fillH_mono subset_union_right
  -- the canonical chart's boundary map
  have hΦinv : ∀ y, Φ.2.1 y = (Mo.hullChart (fillH X) 0).2.1 (y + (x₀ : ℂ)) := fun y => by
    simp only [hΦ, Mo.hullChart_inv, Complex.ofReal_zero, add_zero]
  have hgΦ : ∀ p ∈ Hbar, Tendsto Φ.2.1 (𝓝[H] p) (𝓝 (gX (p + (x₀ : ℂ)))) := fun p hp => by
    have hsh : Tendsto (fun y : ℂ => y + (x₀ : ℂ)) (𝓝[H] p) (𝓝[H] (p + (x₀ : ℂ))) :=
      tendsto_nhdsWithin_iff.2 ⟨((continuous_id.add continuous_const).tendsto p).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun y hy => by
          have hy' : 0 < y.im := hy
          show 0 < (y + (x₀ : ℂ)).im
          simpa using hy'⟩
    have hp' : p + (x₀ : ℂ) ∈ Hbar := by
      have hp'' : 0 ≤ p.im := hp
      show 0 ≤ (p + (x₀ : ℂ)).im
      simpa using hp''
    exact ((hgX _ hp').comp hsh).congr fun y => (hΦinv y).symm
  have hgΦf : ∀ z, ((fun p : ℂ => gX (p + (x₀ : ℂ))) ⁻¹' {z} ∩ {w : ℂ | 0 ≤ w.im}).Finite := fun z => by
    have := (hgXf z).preimage (f := fun p : ℂ => p + (x₀ : ℂ)) (add_left_injective _).injOn
    refine this.subset ?_
    rintro p ⟨hp, hpim⟩
    refine ⟨hp, ?_⟩
    show 0 ≤ (p + (x₀ : ℂ)).im
    simpa using hpim
  -- the free line and the normalization
  have hfree := free_pullHull hgc hgpos hXc hXle
  have hentΦ : ∃ eΦ : ℝ → ℝ, (∀ x : ℝ, stPt s < x → Tendsto Φ.1 (𝓝[H] (x : ℂ)) (𝓝 (eΦ x : ℂ))) ∧
      Tendsto eΦ (𝓝[>] (stPt s)) (𝓝 0) := by
    obtain ⟨-, ⟨eΦ, heΦ, heΦ0⟩, -, -⟩ := hent
    rw [hRx] at heΦ heΦ0
    refine ⟨eΦ, fun x hx => ?_, heΦ0⟩
    have hfun : Φ.1 = ((Mo.hullChart (fillH X) 0).recenter x₀).1 := by
      funext z
      simp only [hΦ, Chart.recenter, Mo.hullChart_fwd, Complex.ofReal_zero, sub_zero]
    rw [hfun]
    exact heΦ x hx
  have hnorm := norm_pullChart hcD.isConformal hgc hgpos hgre hentΦ
  -- the version's trace, reflected, and its clock
  set ηr : ℝ → ℂ := fun r => LP.reflectC (ηV r) with hηrdef
  have hηr : IsLoewnerTrace (fun r => -(fun s : ℝ => W s.toNNReal) r) ηr :=
    Sec5.CrossRestart.isLoewnerTrace_reflect_of_isLoewnerTrace hηV
  have hWc' : Continuous fun s : ℝ => W s.toNNReal := hWc.comp continuous_real_toNNReal
  have hW0' : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simp [hW0]
  set τ : ℝ → ℝ := fun r => (a r.toNNReal).toReal with hτdef
  have hle_t : ∀ r ∈ Icc (0 : ℝ) t, r.toNNReal ≤ t := fun r hr => (Real.toNNReal_le_iff_le_coe).2 hr.2
  have hfinA : ∀ r ∈ Icc (0 : ℝ) t, a r.toNNReal ≠ ⊤ := fun r hr =>
    ne_top_of_le_ne_top hatop (ham (hle_t r hr))
  have hτc : ContinuousOn τ (Icc 0 t) :=
    ENNReal.continuousOn_toReal.comp (hac.comp continuous_real_toNNReal).continuousOn fun r hr => hfinA r hr
  have hτ0 : τ 0 = 0 := by simp [hτdef, ha0]
  have hτs : τ t = ((a t).toNNReal : ℝ) := by
    show (a (t : ℝ).toNNReal).toReal = _
    rw [Real.toNNReal_coe]
    rfl
  have hu : (0 : ℝ) < ((a t).toNNReal : ℝ) := ENNReal.toReal_pos hat.ne' hatop
  have hηrH : ∀ r ∈ Icc (0 : ℝ) t, 0 ≤ (ηr (τ r)).im := fun r hr => by
    have h := GW2TipSystem.Gm.loewnerTrace_mem_Hbar hηV hWc' hW0' (ENNReal.toReal_nonneg (a := a r.toNNReal))
    have h' : 0 ≤ (ηV (τ r)).im := h
    simpa [hηrdef, LP.reflectC] using h'
  -- B's stopped piece
  obtain ⟨hwBc, hwB0, η, hη, hηeq⟩ := stopTrace_facts hPR ht0 htζ
  have hgen := isGeneratingTrace_trOf hPR
  have hcont0 : ContinuousOn (D n).1 {r : ℝ≥0 | (r : ℝ≥0∞) < (D n).2} := hPR.2.1.mono fun r (hr : (r : ℝ≥0∞) < (D
    n).2) => (show (r : ℝ≥0∞) ≤ (D n).2 from hr.le)
  have htrH : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (D n).2 → trOf (D n) r ∈ Hbar := fun r hr =>
    Sec7.IsGeneratingTrace.mem_Hbar hgen hcont0 hPR.1 hr
  have hinj := pcPt_injOn_launch hP hW hl
  have hltζ : ∀ r ∈ Icc (0 : ℝ) t, ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2 := fun r hr =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hle_t r hr)) htζ
  have htrinj : InjOn (trOf (D n)) {r : ℝ≥0 | (r : ℝ≥0∞) < (D n).2} := fun r₁ h₁ r₂ h₂ he =>
    hinj h₁ h₂ (by unfold pcPt; rw [he])
  have hηinj : InjOn η (Icc 0 t) := by
    intro r₁ h₁ r₂ h₂ he
    rw [hηeq r₁ h₁, hηeq r₂ h₂] at he
    have he' : trOf (D n) r₁.toNNReal = trOf (D n) r₂.toNNReal := by
      have := congrArg LP.reflectC he
      simpa only [LP.reflectC_reflectC] using this
    have h' := htrinj (hltζ r₁ h₁) (hltζ r₂ h₂) he'
    exact (Real.toNNReal_eq_toNNReal_iff h₁.1 h₂.1).1 h'
  have hηH : η t ∈ H := by
    rw [hηeq t ⟨NNReal.coe_nonneg t, le_rfl⟩, Real.toNNReal_coe]
    refine LP.reflectC_mem_H_iff.2 ?_
    rw [← LP.traceAt_eq_of_isGeneratingTrace hgen hcont0 hPR.1 htζ]
    exact htip
  -- the good times
  set G : Set ℝ := {r | r ∈ Icc (0 : ℝ) t ∧ pcPt s (D n) r.toNNReal ∈ H \ fillH X} with hGdef
  have hGs : G ⊆ Icc 0 t := fun r hr => hr.1
  have hGd0 : Ico (0 : ℝ) t ⊆ closure G := by
    intro r hr
    have hr0 : 0 ≤ r := hr.1
    have hrt : r.toNNReal < t := (Real.toNNReal_lt_iff_lt_coe hr0).2 hr.2
    have hrζ : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < (D n).2 := lt_trans (ENNReal.coe_lt_coe.2 hrt) htζ
    have h1 := hden r.toNNReal hrζ
    have h2 := map_mem_closure NNReal.continuous_coe h1 (mapsTo_image _ _)
    rw [Real.coe_toNNReal r hr0] at h2
    have h3 := isOpen_Iio.inter_closure ⟨hr.2, h2⟩
    refine closure_mono ?_ h3
    rintro _ ⟨hlt, t', ⟨-, ht'g⟩, rfl⟩
    exact ⟨⟨NNReal.coe_nonneg t', hlt.le⟩, by rwa [Real.toNNReal_coe]⟩
  have hGd : Icc (0 : ℝ) t ⊆ closure G := by
    have h := closure_minimal hGd0 isClosed_closure
    rwa [closure_Ico (ne_of_lt (show (0 : ℝ) < t from ht0))] at h
  -- the trace at the good times
  have hYo : IsOpen (H \ fillH Pn) := hY.2.2.1
  have hgoodtr : ∀ r ∈ G, trOf (D n) r.toNNReal ∈ H ∧
      pcPt s (D n) r.toNNReal = c.2.1 (trOf (D n) r.toNNReal) := fun r hr => by
    have hgY : LuM.bdVal c (trOf (D n) r.toNNReal) ∈ H \ fillH Pn := ⟨hr.2.1, fun h => hr.2.2 (hYB h)⟩
    exact trOf_mem_H_of_good hcD hYo hgc (htrH _ (hltζ r hr.1).le) hgY
  have hnoarc : interior {r ∈ Ioo (0 : ℝ) t | (η r).im = 0} = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun r hr => ?_
    obtain ⟨V, hVsub, hVo, hrV⟩ := mem_interior.1 hr
    have hrI : r ∈ Icc (0 : ℝ) t := Ioo_subset_Icc_self (hVsub hrV).1
    obtain ⟨g, hgV, hgG⟩ := mem_closure_iff.1 (hGd hrI) V hVo hrV
    have hg := hVsub hgV
    have him : (η g).im = 0 := hg.2
    rw [hηeq g (hGs hgG)] at him
    have hH := LP.reflectC_mem_H_iff.2 (hgoodtr g hgG).1
    exact (ne_of_gt hH) him
  -- the clock is strictly increasing
  have hΦD : IsDomainChart (H \ fillH X) Φ := Mo.isDomainChart_hullChart hXh x₀
  have hdom : (Φ.dom : Set ℂ) = H \ fillH X := Mo.coe_dom_hullChart hXh x₀
  have hlinkG : ∀ r ∈ G, ηV (τ r) = Φ.1 (pcPt s (D n) r.toNNReal) := fun r hr =>
    hlink r.toNNReal (hle_t r hr.1) (by rw [hdom]; exact hr.2)
  have hτm : StrictMonoOn τ (Icc 0 t) := by
    intro r₁ h₁ r₂ h₂ hlt
    have hmono : ∀ x y, x ∈ Icc (0 : ℝ) t → y ∈ Icc (0 : ℝ) t → x ≤ y → τ x ≤ τ y := fun x y _ hy hxy =>
      ENNReal.toReal_mono (hfinA y hy) (ham (Real.toNNReal_le_toNNReal hxy))
    refine lt_of_le_of_ne (hmono r₁ r₂ h₁ h₂ hlt.le) fun heq => ?_
    have hI : ∀ x ∈ Ioo r₁ r₂, x ∈ Icc (0 : ℝ) t := fun x hx => ⟨h₁.1.trans hx.1.le, hx.2.le.trans h₂.2⟩
    have hconst : ∀ x ∈ Ioo r₁ r₂, τ x = τ r₁ := fun x hx =>
      le_antisymm (heq ▸ hmono x r₂ (hI x hx) h₂ hx.2.le) (hmono r₁ x h₁ (hI x hx) hx.1.le)
    have hm : (r₁ + r₂) / 2 ∈ Ioo r₁ r₂ := ⟨by linarith, by linarith⟩
    obtain ⟨g₁, hg₁, hg₁G⟩ := mem_closure_iff.1 (hGd (hI _ hm)) (Ioo r₁ r₂) isOpen_Ioo hm
    have hm' : (g₁ + r₂) / 2 ∈ Ioo g₁ r₂ := ⟨by linarith [hg₁.2], by linarith [hg₁.2]⟩
    have hsub : Ioo g₁ r₂ ⊆ Ioo r₁ r₂ := Ioo_subset_Ioo_left hg₁.1.le
    obtain ⟨g₂, hg₂, hg₂G⟩ := mem_closure_iff.1 (hGd (hI _ (hsub hm'))) (Ioo g₁ r₂) isOpen_Ioo hm'
    have he : Φ.1 (pcPt s (D n) g₁.toNNReal) = Φ.1 (pcPt s (D n) g₂.toNNReal) := by
      rw [← hlinkG g₁ hg₁G, ← hlinkG g₂ hg₂G, hconst g₁ hg₁, hconst g₂ (hsub hg₂)]
    have he' : pcPt s (D n) g₁.toNNReal = pcPt s (D n) g₂.toNNReal := by
      rw [← hΦD.inv_fwd hg₁G.2, he, hΦD.inv_fwd hg₂G.2]
    have h' := hinj (hltζ g₁ (hGs hg₁G)) (hltζ g₂ (hGs hg₂G)) he'
    have := (Real.toNNReal_eq_toNNReal_iff (hGs hg₁G).1 (hGs hg₂G).1).1 h'
    linarith [hg₂.1]
  -- the relative chart and the link at the good times
  obtain ⟨_, _, _, -, -, -, -, -, hcr, -⟩ :=
    stageChartPkg hcD hY hXh hYB hmap hLY hlift hgc hCc hgΦ hgΦf hfree hnorm
  have hcrc : ContinuousOn (Lf.reflChart (Mn.pullChart c Φ)).2.1 H := hcr.1.isConformal.1.continuousOn
  have hlinkT : ∀ r ∈ G,
      Tendsto (Lf.reflChart (Mn.pullChart c Φ)).2.1 (𝓝[H] (ηr (τ r))) (𝓝 (η r)) := fun r hr => by
    obtain ⟨htrH', hpcEq⟩ := hgoodtr r hr
    have hpt : ηr (τ r) = LP.reflectC (Φ.1 (pcPt s (D n) r.toNNReal)) := by
      simp only [hηrdef, hlinkG r hr]
    have hwH : ηr (τ r) ∈ H := by rw [hpt]; exact LP.reflectC_mem_H_iff.2 (hΦD.fwd_mem hr.2)
    have hval : (Lf.reflChart (Mn.pullChart c Φ)).2.1 (ηr (τ r)) = η r := by
      rw [hpt, hηeq r (hGs hr)]
      show Supp9B.refl (c.1 (Φ.2.1 (Supp9B.refl (LP.reflectC (Φ.1 (pcPt s (D n) r.toNNReal)))))) =
        LP.reflectC (trOf (D n) r.toNNReal)
      rw [Lf.refl_eq_reflectC, LP.reflectC_reflectC, hΦD.inv_fwd hr.2, hpcEq, hcD.fwd_inv htrH']
    have h := ((hcrc _ hwH).continuousAt (QuantumZipper.isOpen_H.mem_nhds hwH)).tendsto
    rw [hval] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact isStageS2_of_dense hcD hY hXh hYB hmap hLY hlift hgc hCc hgΦ hgΦf hfree hnorm hWc' hW0' hηr
    (show (0 : ℝ) < t from ht0) hu hτc hτm hτ0 hτs hηrH hwBc hwB0 hη hηinj hnoarc hηH hGs hGd hlinkT

end InteractingSLE.Theorem14.SB.Sx

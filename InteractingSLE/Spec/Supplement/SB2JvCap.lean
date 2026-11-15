/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JvRootAS
import InteractingSLE.Spec.Supplement.G7ClockGeom
import InteractingSLE.Spec.Supplement.SB2MoPhys
import InteractingSLE.Spec.Supplement.GW2RootC11Capacity
import InteractingSLE.Spec.Supplement.SB2XhFill
import InteractingSLE.Spec.Supplement.SB2XlDom
import InteractingSLE.Spec.Supplement.SB2XtSample

/-!
# SB2(2): capacity through a domain chart (toward the infinite relative root)

Packet PROVE-SB2-LIFTSET (round 18). At an infinite relative root the relative facts need the stage curve's capacity
lifetime to be infinite. Capacity is additive through a domain chart (`Supp7.IsDomChart.hcapSet_fillH_eq_add`, the
composition rule of G7); this file turns the walk's charts into such charts:

* **`isDomChart_of_domainChart`**: a domain chart of `ℍ ∖ fill K` whose inverse has a continuous boundary map within
  bounded distance of the identity is, after the translation of `Mo.exists_hullChart_translate`, a G7 domain chart
  `(mapOut (fill K) − x₀, ĝ)` of `K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

/-- **A walk chart as a G7 domain chart.** -/
theorem isDomChart_of_domainChart {K : Set ℂ} (hK : IsHPHull (fillH K)) {c : Chart}
    (hc : IsDomainChart (H \ fillH K) c) {ĝ : ℂ → ℂ} (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H)
    (hlim : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q))) {C : ℝ} (hC : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ C) :
    ∃ x₀ : ℝ, Supp7.IsDomChart K (fun z => ConformalImage.mapOut (fillH K) z - (x₀ : ℂ))
        (fun w => if 0 ≤ w.im then ĝ w else 0) ∧
      ∀ z ∈ H \ fillH K, c.1 z = ConformalImage.mapOut (fillH K) z - (x₀ : ℂ) := by
  classical
  have hb : ∀ y ∈ H, ‖c.2.1 y - y‖ ≤ C := fun y hy => by
    rw [← hgg hy]; exact hC y (show y ∈ Hbar from le_of_lt (show (0 : ℝ) < y.im from hy))
  obtain ⟨x₀, hx₀⟩ := Mo.exists_hullChart_translate hK hc hb
  have hx₀' : ∀ z ∈ H \ fillH K, c.1 z = ConformalImage.mapOut (fillH K) z - (x₀ : ℂ) := fun z hz => by
    rw [hx₀ z hz]; rfl
  set g := ConformalImage.mapOut (fillH K) with hgdef
  have hg := ConformalImage.isMapOut_mapOut hK
  set ψ : ℂ → ℂ := fun w => if 0 ≤ w.im then ĝ w else 0 with hψdef
  have hψH : EqOn ψ c.2.1 H := fun w hw => by
    simp only [hψdef, le_of_lt (show 0 < w.im from hw), ↓reduceIte]; exact hgg hw
  have hψHb : EqOn ψ ĝ Hbar := fun w hw => by
    simp only [hψdef, show 0 ≤ w.im from hw, ↓reduceIte]
  have hoff := bdryOff_of_ext hc.1 hĝ hgg hlim
  have hinj : InjOn c.2.1 H := fun a ha a' ha' e => by rw [← hc.1.2.2 a ha, e, hc.1.2.2 a' ha']
  refine ⟨x₀, ⟨⟨fun z hz => ?_, fun z hz z' hz' e => ?_, fun w hw => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hx₀'⟩
  · -- maps `ℍ ∖ fill K` into `ℍ`
    exact sub_ofReal_mem_H (hg.1.2.mapsTo hz) x₀
  · exact hg.1.2.injOn hz hz' (sub_left_inj.1 e)
  · obtain ⟨z, hz, hze⟩ := hg.1.2.surjOn (Mo.add_ofReal_mem_H hw x₀)
    exact ⟨z, hz, by show ConformalImage.mapOut (fillH K) z - (x₀ : ℂ) = w; rw [hze]; ring⟩
  · exact hg.1.1.sub_const _
  · -- the forward map tends to `∞`
    rw [← tendsto_norm_atTop_iff_cobounded]
    have h1 : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH K)) atTop :=
      tendsto_norm_cobounded_atTop.mono_left inf_le_left
    have h2 := hg.2
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-(1 + |x₀|)) h1)
    filter_upwards [h2.eventually (closedBall_mem_nhds (0 : ℂ) one_pos)] with z hz
    rw [dist_zero_right] at hz
    have h3 : ‖z‖ ≤ ‖g z - (x₀ : ℂ)‖ + ‖g z - z‖ + ‖(x₀ : ℂ)‖ := by
      calc ‖z‖ = ‖(g z - (x₀ : ℂ)) - (g z - z) + (x₀ : ℂ)‖ := by ring_nf
        _ ≤ ‖(g z - (x₀ : ℂ)) - (g z - z)‖ + ‖(x₀ : ℂ)‖ := norm_add_le _ _
        _ ≤ ‖g z - (x₀ : ℂ)‖ + ‖g z - z‖ + ‖(x₀ : ℂ)‖ := by gcongr; exact norm_sub_le _ _
    rw [Complex.norm_real, Real.norm_eq_abs] at h3
    linarith
  · -- the inverse is a bijection `ℍ → ℍ ∖ fill K`
    have hbij : BijOn c.2.1 H (H \ fillH K) := ⟨fun w hw => hc.2.1 ▸ mem_image_of_mem _ hw, hinj,
      fun z hz => by rw [← hc.2.1] at hz; exact hz⟩
    exact hbij.congr hψH.symm
  · intro w hw
    rw [hψH hw, ← hx₀' _ (hc.2.1 ▸ mem_image_of_mem _ hw)]
    exact hc.1.2.2 w hw
  · intro w hw
    by_cases him : 0 ≤ w.im
    · simp only [hψdef, him, ↓reduceIte]
      have hw0 : w.im = 0 := le_antisymm (not_lt.1 hw) him
      rw [← hc.2.1]
      exact hoff w hw0 _ (hlim w him)
    · simp only [hψdef, him, ↓reduceIte]
      intro h
      have h0 : (0 : ℝ) < (0 : ℂ).im := h.1
      simp at h0
  · exact hc.1.1.congr fun w hw => hψH hw
  · exact hĝ.congr hψHb
  · exact ⟨C, fun w hw => by rw [hψHb hw]; exact hC w hw⟩

/-- **The fill of a union of two sets with hull fills is a hull** (real points do not matter, `fillH_inter_H'`). -/
theorem isHPHull_fillH_union_of {X Y : Set ℂ} (hX : IsHPHull (fillH X)) (hY : IsHPHull (fillH Y)) :
    IsHPHull (fillH (X ∪ Y)) := by
  have hX' : IsHPHull (fillH (X ∩ H)) := by rw [Lw.fillH_inter_H']; exact hX
  have hY' : IsHPHull (fillH (Y ∩ H)) := by rw [Lw.fillH_inter_H']; exact hY
  have h1 := WalkIntFill.fillH_union_filled inter_subset_right inter_subset_right hX' hY'
  rw [Lw.fillH_inter_H', Lw.fillH_inter_H', ← union_inter_distrib_right, Lw.fillH_inter_H'] at h1
  rw [← h1]
  exact WalkIntFill.isHPHull_fillH_union hX hY

/-- The filling of a path started on `ℝ` (parametrized by `ℝ≥0`) is a hull. -/
theorem isHPHull_fillH_image_nn {ζ : ℝ≥0 → ℂ} {T : ℝ≥0} (hζ : ContinuousOn ζ (Icc 0 T)) (h0 : (ζ 0).im = 0) :
    IsHPHull (fillH (ζ '' Icc 0 T)) := by
  refine isHPHull_fillH_of_isPreconnected (isCompact_Icc.image_of_continuousOn hζ).isBounded ?_
  refine IsPreconnected.union (ζ 0) ⟨0, ⟨le_rfl, zero_le⟩, rfl⟩ ?_ (isPreconnected_Icc.image _ hζ)
    isPreconnected_lowerHalf
  show (ζ 0).im ≤ 0
  rw [h0]

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1P in
/-- **The walk chart as a G7 chart, with the piece's boundary values** (at a launch). -/
theorem exists_isDomChart_run {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    IsHPHull (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
      ∃ (x₀ : ℝ) (ψ : ℂ → ℂ),
        Supp7.IsDomChart (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)
          (fun z => ConformalImage.mapOut (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) z
            - (x₀ : ℂ)) ψ ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ (D n).2 →
          ψ (trOf (D n) t) = pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) t := by
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnot := Lx.stStatus_ne_done_of_launches _ D hl'
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  have hdom := Lw.isDomainChart_runChart (boundaryWalkSpec b jumps θ true) D hP n hnot
  obtain ⟨M, hM⟩ := Lw.exists_hullModel_fill (boundaryWalkSpec b jumps θ true) D hP n hnot
  have hHull : IsHPHull (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) :=
    hM ▸ M.isHull
  obtain ⟨f, C, hf, hC, -⟩ := GW1Z.chartFiber_run (boundaryWalkSpec b jumps θ true) D hP n
  have hB : HasBdryLimits (stChart s).2.1 := fun p hp => ⟨f p, hf p hp⟩
  have hfe : EqOn f (extendFrom H (stChart s).2.1) Hbar := fun p hp => by
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique (hf p hp) (hB.tendsto hp)
  have hfc : ContinuousOn f Hbar := hB.continuousOn.congr hfe
  have hcc := hdom.1
  have hfH : EqOn f (stChart s).2.1 H := fun p hp => by
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H (le_of_lt (show (0 : ℝ) < p.im from hp))
    exact tendsto_nhds_unique (hf p (le_of_lt (show (0 : ℝ) < p.im from hp)))
      ((hcc.1.continuousOn.continuousWithinAt hp).mono_left le_rfl)
  obtain ⟨x₀, hD, -⟩ := isDomChart_of_domainChart hHull hdom hfc hfH hf hC
  refine ⟨hHull, x₀, _, hD, fun t ht => ?_⟩
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have him : 0 ≤ (trOf (D n) t).im := im_nonneg_of_isGeneratingTrace_le hα hPR.2.1 hPR.1 ht
  simp only [him, ↓reduceIte]
  exact (bdVal_eq_of_tendsto him (hf _ him)).symm

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1P in
/-- **The capacity of the prefix with an infinite piece grows like twice the piece's time** (G7 additivity through
the walk chart; the piece's hull in the chart is the Loewner hull of its driver). -/
theorem hcap_prefix_piece {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → Drv}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) (hW : WalkChainFacts κ b jumps θ D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (htop : (D n).2 = ⊤) (T : ℝ≥0) :
    IsHPHull (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n ∪
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) '' Icc 0 T)) ∧
      ConformalImage.hcapSet (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n ∪
        pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) (D n) '' Icc 0 T)) =
      2 * T + ConformalImage.hcapSet (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n)) := by
  obtain ⟨⟨c₀, θ₀⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hnot := Lx.stStatus_ne_done_of_launches _ D hl'
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  set Kp := SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n with hKp
  obtain ⟨hHull, x₀, ψ, hD, hψ⟩ := exists_isDomChart_run hP hl
  have hPR := pieceRegular_of_launch hP hl
  have hα := isGeneratingTrace_trOf hPR
  have hle : ∀ r : ℝ≥0, (r : ℝ≥0∞) ≤ (D n).2 := fun r => by rw [htop]; exact le_top
  have hpc := continuousOn_pcPt_launch hP hl
  have hpcT : ContinuousOn (pcPt s (D n)) (Icc 0 T) := hpc.mono fun r _ => hle r
  have hΓc : ContinuousOn (trOf (D n)) (Icc 0 T) := hα.2.1.mono fun r _ => hle r
  have h0 : (pcPt s (D n) 0).im = 0 := by
    rw [pcPt_zero_launch hP hW hl (by rw [htop]; exact ENNReal.top_ne_zero)]; simp
  have hpath := isHPHull_fillH_image_nn hpcT h0
  have hPh := isHPHull_fillH_union_of hHull hpath
  have hPc : IsCompact (Kp ∪ pcPt s (D n) '' Icc 0 T) :=
    (Lx.isCompact_prefixPhysSet_run _ D hP n hnot).union (isCompact_Icc.image_of_continuousOn hpcT)
  have hPK : Kp ∪ pcPt s (D n) '' Icc 0 T ⊆ Kp ∪ ψ '' (trOf (D n) '' Icc 0 T) := by
    rintro z (hz | ⟨r, hr, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨trOf (D n) r, ⟨r, hr, rfl⟩, hψ r (hle r)⟩
  have hΓ0 : (trOf (D n) 0).im ≤ 0 := by rw [hα.1]; simp
  have hΓP : ∀ r ∈ Icc 0 T, ψ (trOf (D n) r) ∈ Kp ∪ pcPt s (D n) '' Icc 0 T := fun r hr => by
    rw [hψ r (hle r)]; exact Or.inr ⟨r, hr, rfl⟩
  have hadd := hD.hcapSet_fillH_eq_add (g := ConformalImage.mapOut (fillH Kp)) (x₀ := (x₀ : ℂ))
    (ConformalImage.isMapOut_mapOut hHull) (fun z => rfl) (by simp) hHull hPh hPc
    (fillH_mono subset_union_left) hPK hΓc hΓ0 hΓP
  -- the trace's fill is the Loewner hull, of capacity `2 T`
  have hWc : Continuous fun r : ℝ => (D n).1 r.toNNReal := by
    have h1 : Continuous (D n).1 := by
      rw [← continuousOn_univ]
      exact hPR.2.1.mono fun r _ => hle r
    exact h1.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => (D n).1 r.toNNReal) 0 = 0 := by
    simp only [Real.toNNReal_zero]; exact hPR.1
  have hfill := hα.2.2 T (by rw [htop]; exact ENNReal.coe_lt_top)
  have hcl : IsCompact (trOf (D n) '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hΓc
  have heq := (isFilling_iff_inter_H_eq_fillH hcl.isBounded hcl.isClosed).1 hfill
  have hhull := isHPHull_fwdHull hWc T.2
  have heq' : QuantumZipper.fwdHull (fun r : ℝ => (D n).1 r.toNNReal) T = fillH (trOf (D n) '' Icc 0 T) := by
    rw [← heq]; exact (inter_eq_left.2 hhull.1).symm
  have hcapT : ConformalImage.hcapSet (fillH (trOf (D n) '' Icc 0 T)) = 2 * T := by
    rw [← heq']
    exact (ConformalImage.hcapSet_eq hhull).trans (hcap_fwdHull hWc hW0 T.2)
  refine ⟨hPh, ?_⟩
  rw [hadd, hcapT]

/-- **Capacity through the upper chart along the tail lift**: `hcap (fill (A ∪ β₀ (t_L + [0, s]))) =
hcap (fill ((γ − m) [0, s])) + hcap (fill A)`. -/
theorem hcap_upper_tail {A : Set ℂ} (hAh : IsHPHull (fillH A)) (hAc : IsCompact A) {c : Chart}
    (hdom : IsDomainChart (H \ fillH A) c) {ĝ : ℂ → ℂ} (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H)
    (hlim : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q))) {C : ℝ} (hC : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ C)
    {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβc : Continuous β₀) (s : ℝ≥0) :
    IsHPHull (fillH (A ∪ (fun s' => β₀ (tL + s')) '' Icc 0 s)) ∧
      ConformalImage.hcapSet (fillH (A ∪ (fun s' => β₀ (tL + s')) '' Icc 0 s)) =
        ConformalImage.hcapSet (fillH ((fun s' => γ s' - (m : ℂ)) '' Icc 0 s)) + ConformalImage.hcapSet (fillH A) := by
  classical
  obtain ⟨x₀, hD, -⟩ := isDomChart_of_domainChart hAh hdom hĝ hgg hlim hC
  have hψ : ∀ s', (fun w => if 0 ≤ w.im then ĝ w else 0) (γ s' - (m : ℂ)) = β₀ (tL + s') := fun s' => by
    have him : 0 ≤ (γ s' - (m : ℂ)).im := by simpa using hγ.2.1.2.2.1 s'
    simp only [him, ↓reduceIte]
    have : (𝓝[H] (γ s' - (m : ℂ))).NeBot := GW1P.neBot_nhdsWithin_H him
    exact tendsto_nhds_unique (hlim _ him) (hγ.2.2.2 s')
  have hζc : ContinuousOn (fun s' => β₀ (tL + s')) (Icc 0 s) :=
    (hβc.comp (continuous_const.add continuous_id)).continuousOn
  have hζ0 : ((fun s' => β₀ (tL + s')) 0).im = 0 := by simp only [add_zero, hγ.1]; simp
  have hPh := isHPHull_fillH_union_of hAh (isHPHull_fillH_image_nn hζc hζ0)
  have hPc : IsCompact (A ∪ (fun s' => β₀ (tL + s')) '' Icc 0 s) :=
    hAc.union (isCompact_Icc.image_of_continuousOn hζc)
  have hΓc : ContinuousOn (fun s' => γ s' - (m : ℂ)) (Icc 0 s) :=
    (hγ.2.1.1.sub continuous_const).continuousOn
  have hΓ0 : ((fun s' => γ s' - (m : ℂ)) 0).im ≤ 0 := by simp [hγ.2.2.1]
  have hPK : A ∪ (fun s' => β₀ (tL + s')) '' Icc 0 s ⊆
      A ∪ (fun w => if 0 ≤ w.im then ĝ w else 0) '' ((fun s' => γ s' - (m : ℂ)) '' Icc 0 s) := by
    rintro z (hz | ⟨r, hr, rfl⟩)
    · exact Or.inl hz
    · exact Or.inr ⟨γ r - (m : ℂ), ⟨r, hr, rfl⟩, hψ r⟩
  have hΓP : ∀ r ∈ Icc 0 s, (fun w => if 0 ≤ w.im then ĝ w else 0) ((fun s' => γ s' - (m : ℂ)) r) ∈
      A ∪ (fun s' => β₀ (tL + s')) '' Icc 0 s := fun r hr => by
    show (fun w => if 0 ≤ w.im then ĝ w else 0) (γ r - (m : ℂ)) ∈ _
    rw [hψ r]; exact Or.inr ⟨r, hr, rfl⟩
  exact ⟨hPh, hD.hcapSet_fillH_eq_add (g := ConformalImage.mapOut (fillH A)) (x₀ := (x₀ : ℂ))
    (ConformalImage.isMapOut_mapOut hAh) (fun z => rfl) (by simp) hAh hPh hPc (fillH_mono subset_union_left) hPK
    hΓc hΓ0 hΓP⟩

/-- The image of `[0, a]` under a continuous increasing map from `0` is `[0, σ a]`. -/
theorem image_Icc_of_strictMonoOn {σ : ℝ≥0 → ℝ≥0} {a : ℝ≥0} (hc : ContinuousOn σ (Icc 0 a))
    (hm : StrictMonoOn σ (Icc 0 a)) (h0 : σ 0 = 0) : σ '' Icc 0 a = Icc 0 (σ a) := by
  refine Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨zero_le, hm.monotoneOn hx ⟨zero_le, le_rfl⟩ hx.2⟩
  · have := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ a) hc
    rwa [h0] at this

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}

open Supp9B Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal Sec7.Lemma71C in
/-- **The infinite root has an infinite capacity lifetime** (deterministic): the stage curve is the tail lift
reparametrized onto `[0, ∞)`; through the upper chart its capacity is that of `A` with the tail minus that of `A`, and
the tail eventually contains the actual prefix with any initial part of the infinite start piece, whose capacity grows
like twice its time. -/
theorem capLife_root_top (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hcH : ContinuousOn c.2.1 H)
    (hc1 : ∀ w ∈ H, c.1 (c.2.1 w) = w) (hoff : BdryOff c) {p : ℝ≥0 → ℂ} {s₂ : ExplState}
    (hs₂ : ∀ z, (stChart s₂).1 z = z) (hPc : Continuous p) (hinj : Function.Injective p) (hp0 : p 0 = β₀ tL)
    (htl : ∀ t, p t ∈ β₀ '' Ici tL) (hgd : ∀ t, t ∈ closure (goodTp c p ⊤))
    (htrp : Tendsto (fun t => ‖p t‖) atTop atTop)
    {A : Set ℂ} (hAh : IsHPHull (fillH A)) (hAc : IsCompact A) (hdom : IsDomainChart (H \ fillH A) c) {ĝ : ℂ → ℂ}
    (hĝ : ContinuousOn ĝ Hbar) (hgg : EqOn ĝ c.2.1 H) (hlim : ∀ q ∈ Hbar, Tendsto c.2.1 (𝓝[H] q) (𝓝 (ĝ q)))
    {C : ℝ} (hC : ∀ q ∈ Hbar, ‖ĝ q - q‖ ≤ C) (hhead : β₀ '' Icc 0 tL ⊆ hullK A) {Kp : Set ℂ} {q : ℝ≥0 → ℂ}
    (hKpc : IsCompact Kp) (hKpr : Kp ⊆ range β₀) (hqc : Continuous q) (hqr : ∀ t, q t ∈ range β₀)
    (hcapK : ∀ T : ℝ≥0, IsHPHull (fillH (Kp ∪ q '' Icc 0 T)) ∧
      ConformalImage.hcapSet (fillH (Kp ∪ q '' Icc 0 T)) = 2 * T + ConformalImage.hcapSet (fillH Kp)) :
    capLife (stCurvep c m p ⊤ s₂) = ⊤ := by
  have hS : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun t => mem_ofPred.2 (le_top (a := (t : ℝ≥0∞)))
  obtain ⟨σ, hσc, hσ⟩ := exists_tailTime hβ (hS ▸ hPc.continuousOn) (S := {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤})
    (fun t _ => htl t)
  have hσall : ∀ t, β₀ (tL + σ t) = p t := fun t => hσ t (by rw [hS]; trivial)
  have h0 : σ 0 = 0 := tailTime_zero hβ (by rw [hσall 0, hp0])
  have hval := stValp_eq_tail hγ hcH hc1 hoff hs₂ hσc hσ (fun t _ => hgd t)
  have hσcont : Continuous σ := by rw [← continuousOn_univ, ← hS]; exact hσc
  have hσinj : Function.Injective σ := fun a b e => hinj (by rw [← hσall a, ← hσall b, e])
  have hσmono : ∀ a : ℝ≥0, StrictMonoOn σ (Icc 0 a) := fun a =>
    hσcont.continuousOn.strictMonoOn_of_injOn_Icc zero_le (by rw [h0]; exact zero_le) hσinj.injOn
  set ρ := stCurvep c m p ⊤ s₂ with hρdef
  have hρv : ∀ u : ℝ, 0 ≤ u → ρ u = γ (σ u.toNNReal) := fun u _ => by
    rw [hρdef, stCurvep_of_top rfl, hval _ ENNReal.coe_lt_top]
  -- the hulls of the stage curve are those of `γ` up to the tail time
  have himg : ∀ u : ℝ, 0 ≤ u → ρ '' Icc 0 u = γ '' Icc 0 (σ u.toNNReal) := fun u hu => by
    rw [image_congr fun v hv => hρv v hv.1, ← image_Icc_of_strictMonoOn hσcont.continuousOn (hσmono _) h0,
      image_image]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨v, hv, rfl⟩
      exact ⟨v.toNNReal, ⟨zero_le, Real.toNNReal_le_toNNReal hv.2⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨x, ⟨x.2, ?_⟩, by simp only [Real.toNNReal_coe]⟩
      have := hx.2
      rwa [← NNReal.coe_le_coe, Real.coe_toNNReal _ hu] at this
  -- the capacity of `γ`'s hulls is unbounded
  have hβe := isClosedEmbedding_of_isProperCurve hβ
  have hcl : IsClosed (β₀ '' Ici tL) := hβe.isClosedMap _ isClosed_Ici
  have hγh : ∀ S : ℝ≥0, IsHPHull (fillH (γ '' Icc 0 S)) := fun S =>
    isHPHull_fillH_image_nn hγ.2.1.1.continuousOn (by rw [hγ.2.2.1]; simp)
  have hunb : ∀ T : ℝ≥0, ∃ S₀ : ℝ≥0, ∀ S ≥ S₀, 2 * (T : ℝ) + ConformalImage.hcapSet (fillH Kp) -
      ConformalImage.hcapSet (fillH A) ≤ ConformalImage.hcapSet (fillH (γ '' Icc 0 S)) := by
    intro T
    set B := Kp ∪ q '' Icc 0 T with hBdef
    have hBc : IsCompact B := hKpc.union (isCompact_Icc.image_of_continuousOn hqc.continuousOn)
    have hBr : B ⊆ range β₀ := union_subset hKpr (by rintro _ ⟨t, -, rfl⟩; exact hqr t)
    obtain ⟨M, hM⟩ := (hβe.isCompact_preimage hBc).isBounded.subset_closedBall 0
    refine ⟨M.toNNReal, fun S hS => ?_⟩
    have hsub : B ∩ β₀ '' Ici tL ⊆ (fun s' => β₀ (tL + s')) '' Icc 0 S := by
      rintro _ ⟨hzB, x, hx, rfl⟩
      refine ⟨x - tL, ⟨zero_le, ?_⟩, by simp only [add_tsub_cancel_of_le (show tL ≤ x from hx)]⟩
      have hxM := hM (show x ∈ β₀ ⁻¹' B from hzB)
      rw [mem_closedBall, NNReal.dist_eq, NNReal.coe_zero, sub_zero] at hxM
      have hx' : (x : ℝ) ≤ M := (le_abs_self _).trans hxM
      exact tsub_le_self.trans ((NNReal.coe_le_coe.1 (hx'.trans (Real.le_coe_toNNReal M))).trans hS)
    have hfill : fillH B ⊆ fillH (A ∪ (fun s' => β₀ (tL + s')) '' Icc 0 S) := by
      calc fillH B ⊆ fillH (A ∪ B) := fillH_mono subset_union_right
        _ = fillH (A ∪ (B ∩ β₀ '' Ici tL)) := (Mn.fillH_tail_eq hβ.1 hAc hBc hBr hhead hcl).symm
        _ ⊆ _ := fillH_mono (union_subset_union_right _ hsub)
    obtain ⟨hPh, hadd⟩ := hcap_upper_tail hAh hAc hdom hĝ hgg hlim hC hγ hβ.1 S
    obtain ⟨hBh, hcapB⟩ := hcapK T
    have hmono := HPHull.hcap_mono (A := ⟨_, hBh⟩) (B := ⟨_, hPh⟩) hfill
    rw [← ConformalImage.hcapSet_eq hBh, ← ConformalImage.hcapSet_eq hPh, hcapB, hadd] at hmono
    have htr : (fun s' => γ s' - (m : ℂ)) '' Icc 0 S = affHomeo 1 one_pos (-m) '' (γ '' Icc 0 S) := by
      rw [image_image]
      refine image_congr fun s' _ => ?_
      rw [coe_affHomeo]; push_cast; ring
    rw [htr, GW2TipSystem.RootC11.hcapSet_fillH_affine (hγh S) one_pos, one_pow, one_mul] at hmono
    linarith
  -- the tail time tends to `∞`
  have hσinf : Tendsto σ atTop atTop := by
    rw [Filter.tendsto_atTop]
    intro M
    obtain ⟨B, hB⟩ := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := tL + M)).image hβ.1).isBounded.subset_closedBall 0
    filter_upwards [htrp.eventually_gt_atTop B] with t ht
    by_contra hlt
    push Not at hlt
    have hmem : p t ∈ closedBall (0 : ℂ) B := by
      rw [← hσall t]
      exact hB ⟨tL + σ t, ⟨zero_le, add_le_add_right hlt.le tL⟩, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hmem
    linarith
  -- conclude
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set K₀ := ConformalImage.hcapSet (fillH Kp) - ConformalImage.hcapSet (fillH A) with hK₀
  obtain ⟨S₀, hS₀⟩ := hunb ((r : ℝ) + |K₀|).toNNReal
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (Filter.tendsto_atTop.1 hσinf S₀)
  set n : ℕ := ⌈(N : ℝ)⌉₊ with hn
  have hnN : N ≤ ((n : ℝ)).toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (Nat.cast_nonneg n)]
    exact Nat.le_ceil _
  have hcap := hS₀ _ (hN _ hnN)
  have hclk : capClock ρ n = ConformalImage.hcapSet (fillH (γ '' Icc 0 (σ ((n : ℝ)).toNNReal))) / 2 := by
    unfold capClock; rw [himg _ (Nat.cast_nonneg n)]
  have hT : ((((r : ℝ) + |K₀|).toNNReal : ℝ≥0) : ℝ) = (r : ℝ) + |K₀| :=
    Real.coe_toNNReal _ (add_nonneg r.2 (abs_nonneg _))
  have hrle : (r : ℝ) ≤ capClock ρ n := by
    rw [hclk]
    rw [hT] at hcap
    have h1 := neg_abs_le K₀
    have h2 := abs_nonneg K₀
    linarith
  calc (r : ℝ≥0∞) = ENNReal.ofReal (r : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
    _ ≤ ENNReal.ofReal (capClock ρ n) := ENNReal.ofReal_le_ofReal hrle
    _ ≤ capLife ρ := le_iSup (fun k : ℕ => ENNReal.ofReal (capClock ρ k)) n

section AS

open MeasureTheory ProbabilityTheory
open Supp9B Lx Lu Leaf FlowDilate Sec4 Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep GW1P
open Sec7.PocketTraversal Sec7.Lemma71C

universe u

/-- **The infinite relative root has an infinite capacity lifetime, almost surely** (Theorems 1.2–1.3). -/
theorem sb2LowerRootCap (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
        rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
            (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lR κ b jumps E u l k ω₀) ≠ 0 →
        (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω))).2 = ⊤ →
        ∀ s₂ : ExplState, stChart s₂ = Chart.id.recenter 0 →
          capLife (stCurvep c m
            (rootPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lR κ b jumps E u l k ω₀))
            (rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
                (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lR κ b jumps E u l k ω₀)) s₂) = ⊤ := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  have hsp : IsBoundaryContinuedProgram (upperSpec u l).2.2 := isBoundaryContinuedProgram_upperSpec hlθ
  have hm𝒢 := (hE _ hsp).2.1 k
  have hβex := KernelTower.ae_ae_condExpKernel_of_ae hm𝒢
    (Mn.rightWalkProperReg_of_thms h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER)
  filter_upwards [hβex, GW1W.regLaunches_of_stagedPiecesRegular (hER _ hsp),
    sb2LowerTailLiftCurve h13 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerUpperChart κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerHeadHull κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerAllowed h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerRunExit h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerCompletion h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft,
    sb2LowerActualInputs h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerStage0Act h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hβ₀ hup hT₀ hU₀ hK₀ hA₀ hX₀ hD₀ hI₀ hS₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm
  obtain ⟨-, ⟨hcH, hc1, hoff⟩, -⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨hdom, hAc, ĝ, Cg, hĝl, hCg⟩ := Mn.upperChart_facts hup hlaunch
  -- the upper hull
  have hnotU := Lx.stStatus_ne_done_of_launches _ _ hlaunch
  obtain ⟨MU, hMU⟩ := Lw.exists_hullModel_fill (Lu.upperSpec u l) _ hup k hnotU
  have hAh : IsHPHull (fillH (upperPrefix κ b jumps E u l k ω₀)) := by
    show IsHPHull (fillH (SB.prefixPhysSet κ b jumps (Lu.upperSpec u l) (fun j => E (Lu.upperSpec u l) j ω₀) k ∪
      ((↑) : ℝ → ℂ) '' Icc u 0))
    rw [Lw.fillH_union_real, ← hMU]; exact MU.isHull
  have hBU : HasBdryLimits c.2.1 := fun p hp => ⟨ĝ p, hĝl p hp⟩
  have hge : EqOn ĝ (extendFrom H c.2.1) Hbar := fun p hp => by
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
    exact tendsto_nhds_unique (hĝl p hp) (hBU.tendsto hp)
  have hĝc : ContinuousOn ĝ Hbar := hBU.continuousOn.congr hge
  have hgH : EqOn ĝ c.2.1 H := fun p hp => by
    have hp' : p ∈ Hbar := le_of_lt (show (0 : ℝ) < p.im from hp)
    have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp'
    exact tendsto_nhds_unique (hĝl p hp') ((hcH.continuousWithinAt hp).mono_left le_rfl)
  filter_upwards [hβ₀, hT₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hK₀ c θ hlaunch b' J' h' hb' hT' hG',
    hA₀ c θ hlaunch b' J' h' hb' hT' hG', hX₀ c θ hlaunch b' J' h' hb' hT' hG',
    hD₀ c θ hlaunch b' J' h' hb' hT' hG', hI₀ c θ hlaunch b' J' h' hb' hT' hG',
    hS₀ c θ hlaunch b' J' h' hb' hT' hG'] with ω hβω hTω hKω hAω hXω hDω hIω hSω
  intro hZ hL0 htop s₂ hs₂
  obtain ⟨β₀, hβ, hβ0, hβr⟩ := hβω
  obtain ⟨tL, γ, hγ⟩ := hTω β₀ hβ hβ0 hβr
  obtain ⟨hP₁, hW₁, hn⟩ := hIω
  set R := lR κ b jumps E u l k ω₀ with hRdef
  set D₁ := lD₁ b jumps E ω with hD₁
  set o := relOff κ (-(Real.pi / 2)) b jumps R D₁ with ho
  set s₁ := wRun κ (-(Real.pi / 2)) b jumps D₁ o with hs₁
  have hR : (R : ℂ) ∈ ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D₁ := by
    rw [← hγ.1, ← hβr]; exact mem_range_self tL
  obtain ⟨hl, hseed⟩ := launch_seed_of_not_zeroRoot hb hXω hP₁ hW₁ (fun j => (hn j).1) (fun j => (hn j).2.1) hAω hDω
    hR hZ
  have hpos : (D₁ o).2 ≠ 0 := by rw [htop]; exact ENNReal.top_ne_zero
  have hsh : (D₁ o).2 - shiftD κ (-(Real.pi / 2)) b jumps R D₁ 0 ≠ 0 := by rw [shiftD_zero]; exact hL0
  have hact := hSω β₀ hβ hβ0 hβr tL hγ.1 m hZ hl hpos hsh
  rw [shiftD_zero] at hact
  have hact' : Stage0Act c m β₀ tL s₁ (D₁ o) (rootPt s₁ (D₁ o) R) (rootLife s₁ (D₁ o) R) := hact
  have hK := hKω β₀ hβ hβ0 hβr tL hγ.1
  obtain ⟨-, -, hDom⟩ := hU₀ c θ hlaunch b' J' h' hb' hT' hG'
  obtain ⟨hPc, hinj, hp0, htl, htrp⟩ := rootInputs hP₁ hW₁ hl hpos hβ hβr hK hDom hγ.1
    (mem_succ_of_not_zeroRoot hR hZ) hseed hact'.2.1 hL0
  have hLtop : rootLife s₁ (D₁ o) R = ⊤ := by
    simp only [rootLife, htop]; exact ENNReal.top_sub_coe
  obtain ⟨hs₁', -, -, -, -⟩ := root_chart_facts hs₂
  set p := rootPt s₁ (D₁ o) R with hpdef
  rw [hLtop] at hPc hinj htl hact' ⊢
  have hS : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun t => le_top (a := (t : ℝ≥0∞))
  have hS' : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun t => ENNReal.coe_lt_top (r := t)
  have hPc' : Continuous p := by rw [← continuousOn_univ, ← hS]; exact hPc
  have hinj' : Function.Injective p := by rw [← injOn_univ, ← hS']; exact hinj
  have htl' : ∀ t, p t ∈ β₀ '' Ici tL := fun t => htl t (le_top (a := (t : ℝ≥0∞)))
  have hgd' : ∀ t : ℝ≥0, t ∈ closure (goodTp c p ⊤) := fun t => hact'.2.1 (ENNReal.coe_lt_top (r := t))
  -- the actual prefix and the full start piece
  have hlen := lt_length_of_launch (κ := κ) (b := b) (jumps := jumps) _ D₁ hl
  have hnot := Lx.stStatus_ne_done_of_launches _ D₁ (Option.ne_none_iff_exists'.1 hl).choose_spec
  have hKpc := Lx.isCompact_prefixPhysSet_run _ D₁ hP₁ o hnot
  have hKpr : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D₁ o ⊆ range β₀ := by
    rw [hβr]; exact statePhysicalSet_subset_physSet hlen.le
  have hpc := continuousOn_pcPt_launch hP₁ hl
  have hqc : Continuous (pcPt s₁ (D₁ o)) := by
    rw [← continuousOn_univ]; exact hpc.mono fun r _ => by rw [mem_ofPred_eq, htop]; exact le_top
  obtain ⟨-, -, -, -, htip⟩ := tipSet_newPc_launch hP₁ hl
  have hqr : ∀ t, pcPt s₁ (D₁ o) t ∈ range β₀ := fun t => by
    rw [hβr]
    refine tipSet_subset_physSet_launch hl ?_
    rw [htip]; exact ⟨t, show (t : ℝ≥0∞) ≤ (D₁ o).2 by rw [htop]; exact le_top, rfl⟩
  exact capLife_root_top hγ hβ hcH hc1 hoff hs₁' hPc' hinj' hp0 htl' hgd' (htrp htop) hAh hAc hdom hĝc hgH hĝl hCg
    hK hKpc hKpr hqc hqr fun T => hcap_prefix_piece hP₁ hW₁ hl htop T

/-- **The relative root, almost surely, complete** (Theorems 1.2–1.3): off a zero root and at a positive shifted
lifetime, the root's stage curve (any root state with the identity chart) is driven, and every regular relative
driver generating it has the relative facts `StageRelP` (finite and infinite pieces). -/
theorem sb2LowerRootFull (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    Lf.SB2LowerSetting.{u} fun κ b jumps _ _ _ P _ E u l k ω₀ c _ _ _ =>
      ∀ m : ℝ, m = -upperEntry κ b jumps E u l k ω₀ →
      ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps (upperSpec u l) (E (upperSpec u l)) k) ω₀),
        ¬ ZeroRoot κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) →
        rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
            (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
          (lR κ b jumps E u l k ω₀) ≠ 0 →
        ∀ s₂ : ExplState, stChart s₂ = Chart.id.recenter 0 →
          let p := rootPt (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lR κ b jumps E u l k ω₀)
          let L := rootLife (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
            (lR κ b jumps E u l k ω₀)
          IsDrivenCurve (stCurvep c m p L s₂) ∧
          ∀ e₂ : Drv, IsRegularDriver e₂ → e₂.2 = capLife (stCurvep c m p L s₂) →
            (∀ T < capLife (stCurvep c m p L s₂), IsGeneratingTrace e₂.1 T (capTrace (stCurvep c m p L s₂))) →
            StageRelP c m p L s₂ e₂ ∧ Mn.StageFacts c m (wRun κ (-(Real.pi / 2)) b jumps (lD₁ b jumps E ω)
              (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (lD₁ b jumps E ω (relOff κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω)))
              (shiftD κ (-(Real.pi / 2)) b jumps (lR κ b jumps E u l k ω₀) (lD₁ b jumps E ω) 0) s₂ e₂ := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft
  filter_upwards [sb2LowerRoot h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL
      hleft,
    sb2LowerRootCap h12 h13 h12₀ h13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hlp hlθ hL hleft]
    with ω₀ hR₀ hC₀
  intro c θ hlaunch b' J' h' hb' hT' hG' m hm
  filter_upwards [hR₀ c θ hlaunch b' J' h' hb' hT' hG' m hm, hC₀ c θ hlaunch b' J' h' hb' hT' hG' m hm]
    with ω hRω hCω
  intro hZ hL0 s₂ hs₂ p L
  obtain ⟨hgd, htr, hdr, hrel⟩ := hRω hZ hL0 s₂ hs₂
  refine ⟨hdr, fun e₂ hreg he₂ hgen => ?_⟩
  have hrelP : StageRelP c m p L s₂ e₂ := ⟨(hrel e₂ hreg he₂ hgen).1, fun hLt => by
    refine (hrel e₂ hreg he₂ hgen).2 hLt (hCω hZ hL0 ?_ s₂ hs₂)
    by_contra hne
    exact ENNReal.sub_ne_top hne hLt⟩
  refine ⟨hrelP, ?_⟩
  rw [shiftD_zero]
  refine ⟨hdr, he₂, hgen, hrelP, hgd, hL0, ?_⟩
  refine pieceRegular_of_stageRelP hrelP he₂ hgen hreg.2.1 fun hLt htop => ?_
  have hcap : capLife (stCurvep c m p L s₂) = ⊤ := by rw [← he₂]; exact htop
  exact tendsto_norm_capTrace hdr hcap (htr hLt)

end AS

end InteractingSLE.Theorem14.SB.Lk

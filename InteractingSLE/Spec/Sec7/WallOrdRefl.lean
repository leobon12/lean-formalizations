/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.WallOrdReflBase
import InteractingSLE.Spec.Sec7.WallOrdSide
import InteractingSLE.Spec.Sec7.R5RefCurrent
import InteractingSLE.Spec.Sec7.R5RefFamily
import InteractingSLE.Spec.Sec7.R5OutWallOrder
import InteractingSLE.Spec.Sec7.PocketSideInSyncClock

/-!
# R.5's outer collars land in the reference hull (`R5Lift.R7OuterRefl`, bounded pocket)

Packet PROVE-WALL-ORDER, target (3). Bounded reverse-contained change pocket `C` (`IsCfPocketConfig`), current chart
`cur` at the live capacity `q` (domain `C ∖ K_T`, `T = T⁰(q)`), an exposed coordinate `ξ` landing at `p` off the
exceptional set (the time-`T` attachments and `0`), and a reference chart `old` at an interior visit time `s` with
`c(s) ≤ q` (domain `C ∖ K_s`), carrying a collar at `x` for `(ξ, p)` with `p ∈ K_s`. Then every old landing near `x`
lies in `K_s` (**`outerRefl_pathwise`**, hence **`r7OuterRefl_of_cfg`**).

Proof. `p` is a limit of `ℍ ∖ K_s` and lies in `K_s`, so it is visited by `s ≤ T`
(`mem_closure_of_mem_fillH_of_mem_closure_compl`); not being a time-`T` attachment, the walls near `p` are visited by
`T` (`R5Out.exists_ball_frontier_subset_range_of_wallOrder`). Let `u` be real near `x` and `z = F̄(u)` its old landing.
If `z ∈ C`, it is a boundary point of `C ∖ K_s` in `C`, hence in `K_s`. Otherwise `z` is a wall point near `p`, visited
by `T`; if `z ∉ K_s`, it is first visited at `t_z ∈ (s, T]`, and the counterflow reaches it through the pocket
(`mem_closure_pocket_visits_cfgR/L`, Aux. 37). Near `z` the pocket is inside the old domain, `ψ(z)` is a real point off
the closed relative hull, and the old chart is continuous at `z` with limit `u` (`tendsto_loewner_fwd_of_alive`, and
`F̄` near `u`). So pocket visits `η(t)`, `t < t_z`, close to `z` lie in the collar `old⁻¹(ℍ ∩ B(x, ε)) ⊆ C ∖ K_T`,
although they are in `K_T`. Contradiction.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.WallOrd

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase R5Ref
open Wire.Current.SideTest (rationalOriginalTime)

/-- The walls of a two-arc pocket lie in `ℍ` away from `0`. -/
theorem mem_H_of_mem_frontier {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} (hC : IsCfPocket C α₁ α₂) {z : ℂ}
    (hz : z ∈ frontier C) (hz0 : z ≠ 0) : z ∈ H := by
  rw [hC.frontier_eq] at hz
  rcases hz with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩
  · rcases hv.2.lt_or_eq with hlt | h1
    · exact hC.mem_H₁ v ⟨hv.1, hlt⟩
    · subst h1
      exact hC.mem_y.resolve_right hz0
  · rcases hv.2.lt_or_eq with hlt | h1
    · exact hC.mem_H₂ v ⟨hv.1, hlt⟩
    · subst h1
      rw [hC.seed] at hz0 ⊢
      exact hC.mem_y.resolve_right hz0

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {A : Set Ω}
  {c : Ω → Chart} {ω : Ω}

/-- **The contradiction step**: an old landing `F̄(u)` (with `u` in the collar disc) that is a wall point visited by
`T` but not by `s` and lies off `K_s` cannot exist — the counterflow reaches it through the pocket, and near it the
pocket is in the collar's image, which misses `K_T`. -/
theorem outerRefl_contra {W' : ℝ≥0 → Ω → ℝ}
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q qs : ℝ≥0} {s : ℝ} (hs0 : 0 ≤ s) (hqs_live : (qs : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (holddom : ((relChart c (travAll R L r η ψ) qs ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 s)))
    (hcurdom : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) =
      cfPocket (R ω) (L ω) r ∩ (H \ fillH (η ω '' Icc 0 (leftStop R L r η ψ q ω))))
    (hTσ : leftStop R L r η ψ q ω < firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) {ξ : ℝ} {p : ℂ} {x ε : ℝ}
    (hcol : IsRefCollar (relChart c (travAll R L r η ψ) qs ω) (relChart c (travAll R L r η ψ) q ω) ξ p x ε)
    {F : ℂ → ℂ} (hlimF : ∀ u : ℝ, Tendsto (relChart c (travAll R L r η ψ) qs ω).2.1 (𝓝[H] (u : ℂ)) (𝓝 (F u)))
    (hNe : ∀ u : ℝ, (𝓝[H] (u : ℂ)).NeBot) {u : ℝ} (hzF : F u ∈ frontier (cfPocket (R ω) (L ω) r))
    (hzH : F u ∈ H) (hzK : F u ∉ fillH (η ω '' Icc 0 s))
    (hzT : F u ∈ η ω '' Icc 0 (leftStop R L r η ψ q ω)) (hzs : F u ∉ η ω '' Icc 0 s)
    (hsI : s ∈ Ioo (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
    (hux : (u : ℂ) ∈ ball (x : ℂ) ε) : False := by
  set C := cfPocket (R ω) (L ω) r with hCdef
  set old := relChart c (travAll R L r η ψ) qs ω with holddef
  obtain ⟨hP, hJ⟩ := pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have h0 := zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded
  have hTopo := hcfg.conf.isCfPocket h0
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hηc : ContinuousOn (η ω) (Ici 0) := hcfg.trace.2.1
  have hCH : C ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  have hold : old.IsConformal := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hqs_live hc
  -- the first visit of the landing, in `(s, T]`
  obtain ⟨htz0, htz, hfresh⟩ := firstHit_spec hηc
    (⟨leftStop R L r η ψ q ω, hzT⟩ : ∃ t, F u ∈ η ω '' Icc 0 t)
  have htzT : firstHit (η ω) (F u) ≤ leftStop R L r η ψ q ω := by
    obtain ⟨t₀, ht₀, hηt₀⟩ := hzT
    exact (csInf_le (s := {v ∈ Ici (0 : ℝ) | η ω v = F u}) ⟨0, fun _ h => h.1⟩ ⟨ht₀.1, hηt₀⟩).trans ht₀.2
  have hstz : s < firstHit (η ω) (F u) := lt_of_not_ge fun h => hzs ⟨_, ⟨htz0, h⟩, htz⟩
  have htzσ : firstHit (η ω) (F u) < firstHit (η ω) (cfArcR (R ω) (L ω) r 0) := htzT.trans_lt hTσ
  -- the counterflow reaches it through the pocket (Aux. 37)
  have hvis : F u ∈ closure (η ω '' {t | t ∈ Ico s (firstHit (η ω) (F u)) ∧ η ω t ∈ C}) := by
    have hzF' := hzF
    rw [hTopo.frontier_eq] at hzF'
    rcases hzF' with ⟨v, hv, hve⟩ | ⟨v, hv, hve⟩
    · have := mem_closure_pocket_visits_cfgR hcfg hv (htz.trans hve.symm) (by rw [hve]; exact hfresh) hsI.1.le
        hstz htzσ
      rwa [hve] at this
    · have := mem_closure_pocket_visits_cfgL hcfg hv (htz.trans hve.symm) (by rw [hve]; exact hfresh) hsI.1.le
        hstz htzσ
      rwa [hve] at this
  -- near the landing the pocket lies in the old domain
  have hKo : IsOpen (H \ fillH (η ω '' Icc 0 s)) := by
    rw [← hcfg.trace.2.2 s hs0]
    exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull hcfg.continuous_W hs0
  obtain ⟨δ, hδ, hδK⟩ := Metric.isOpen_iff.1 hKo (F u) ⟨hzH, hzK⟩
  have hloc : ∀ w ∈ C ∩ ball (F u) δ, w ∈ (old.dom : Set ℂ) := fun w hw => by
    rw [holddom]; exact ⟨hw.1, hδK hw.2⟩
  -- the old chart is continuous at the landing (its pocket coordinate is alive)
  obtain ⟨Wc, hWc, hWc0, -, -, -, hrel0⟩ := exists_relChart_eq_loewner (c := c) (γ := travAll R L r η ψ) hγ hqs_live
  have hrel : old = (c ω).loewner Wc qs := hrel0
  have hx₀C : cfArcR (R ω) (L ω) r 0 ∉ C := by
    rw [PocketCoord.IsChangeConfigInc.cfArcR_zero]; exact hcfg.conf.cfPt_openPt_notMem
  have hzx₀ : F u ≠ cfArcR (R ω) (L ω) r 0 := fun h => hP.fresh_x ⟨_, ⟨htz0, htzσ⟩, htz.trans h⟩
  have hzC' : F u ∈ closure C \ {cfArcR (R ω) (L ω) r 0} := ⟨frontier_subset_closure hzF, hzx₀⟩
  have hψc : Tendsto (ψ ω) (𝓝[C] (F u)) (𝓝 (ψ ω (F u))) :=
    ((hJ.1 _ hzC').mono fun w hw => ⟨subset_closure hw, fun h => hx₀C (h ▸ hw)⟩).tendsto
  have hψim : (ψ ω (F u)).im = 0 := hJ.2.2.2.2.1 _ ⟨hzF, hzx₀⟩
  have hψX : ψ ω (F u) = ((ψ ω (F u)).re : ℂ) := Complex.ext (by simp) (by simp [hψim])
  have hy₀C : cfArcR (R ω) (L ω) r 1 ∈ closure C \ {cfArcR (R ω) (L ω) r 0} := by
    refine ⟨frontier_subset_closure ?_, fun h => one_ne_zero (hTopo.inj₁ ⟨zero_le_one, le_rfl⟩
      ⟨le_rfl, zero_le_one⟩ h)⟩
    rw [hTopo.frontier_eq]
    exact Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
  have hX0 : (ψ ω (F u)).re ≠ 0 := by
    intro hX
    have h1 : ψ ω (F u) = ψ ω (cfArcR (R ω) (L ω) r 1) := by
      rw [hψX, hX, hJ.2.2.2.2.2.1]; simp
    have h2 := hJ.2.1 hzC' hy₀C h1
    exact hzs ⟨_, ⟨hP.nonneg, hsI.1.le⟩, hP.first_y.trans h2.symm⟩
  have hXK : (((ψ ω (F u)).re : ℝ) : ℂ) ∉ closure (fwdHull Wc qs) := by
    rw [← hψX]
    refine R6Fc.notMem_closure_of_ball_subset hJ hTopo.isBounded hx₀C ((QuantumZipper.fwdHull_mono (W := Wc)).2 _)
      hzC' hδ fun w hw => ⟨hw.1, ?_⟩
    have hwd := hloc w hw
    rw [hrel] at hwd
    have := (fwd_mem_compl_of_mem_dom_loewner hc hWc hWc0 qs.coe_nonneg hwd).1
    rwa [heq hw.1] at this
  obtain ⟨y, hy⟩ := tendsto_loewner_fwd_of_alive hc hdom heq hWc hWc0 qs.coe_nonneg
    (by rw [← hψX]; exact hψc) hX0 hXK
  rw [← hrel] at hy
  -- its limit is `u`
  have hinv : Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝[(old.dom : Set ℂ)] (F u)) :=
    tendsto_nhdsWithin_iff.2 ⟨hlimF u, eventually_nhdsWithin_of_forall fun w hw => hold.inv_mem_dom hw⟩
  have hyu : (y : ℂ) = u := by
    have := hNe u
    refine tendsto_nhds_unique (hy.comp hinv) ?_
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun w hw => ?_)
    exact (hold.2.2 w hw).symm
  -- a pocket visit near the landing is in the collar image, hence off `K_T`
  set Pv := η ω '' {t | t ∈ Ico s (firstHit (η ω) (F u)) ∧ η ω t ∈ C} with hPv
  have hzPv : F u ∈ closure (Pv ∩ ball (F u) δ) := by
    rw [Metric.mem_closure_iff] at hvis ⊢
    intro e he
    obtain ⟨b, hb, hbd⟩ := hvis (min e δ) (lt_min he hδ)
    exact ⟨b, ⟨hb, by rw [mem_ball, dist_comm]; exact lt_of_lt_of_le hbd (min_le_right _ _)⟩,
      lt_of_lt_of_le hbd (min_le_left _ _)⟩
  have : (𝓝[Pv ∩ ball (F u) δ] (F u)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzPv
  have hPvC : ∀ w ∈ Pv, w ∈ C := by
    rintro _ ⟨t, ht, rfl⟩
    exact ht.2
  have hle : 𝓝[Pv ∩ ball (F u) δ] (F u) ≤ 𝓝[(old.dom : Set ℂ)] (F u) :=
    nhdsWithin_mono _ fun w hw => hloc w ⟨hPvC w hw.1, hw.2⟩
  have hball : ball (x : ℂ) ε ∈ 𝓝 (y : ℂ) := by
    rw [hyu]; exact isOpen_ball.mem_nhds hux
  have h1 : ∀ᶠ w in 𝓝[Pv ∩ ball (F u) δ] (F u), old.1 w ∈ ball (x : ℂ) ε := (hy.mono_left hle) hball
  obtain ⟨w, hw1, hw2⟩ := (h1.and self_mem_nhdsWithin).exists
  obtain ⟨⟨t, ⟨htI, htC⟩, rfl⟩, hwb⟩ := hw2
  have hwd := hloc _ ⟨htC, hwb⟩
  have hcm : old.2.1 (old.1 (η ω t)) ∈ ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) :=
    hcol.2.1 ⟨_, ⟨hold.fwd_mem hwd, hw1⟩, rfl⟩
  rw [hold.inv_fwd hwd, hcurdom] at hcm
  exact hcm.2.2 ⟨hCH htC, Or.inl (subset_closure ⟨t, ⟨hs0.trans htI.1, htI.2.le.trans htzT⟩, rfl⟩)⟩

/-- **The outer collars' old landings lie in the reference hull** (one sample, bounded reverse-contained pocket). -/
theorem outerRefl_pathwise {W' : ℝ≥0 → Ω → ℝ} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {ξ : ℝ}
    (hpX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ R5Wall.outerExc R L r η ψ q ω)
    {s : ℝ} (hs0 : 0 ≤ s) (hsC : η ω s ∈ cfPocket (R ω) (L ω) r)
    (hsq : (visitCap R L r η ψ ω s).toNNReal ≤ q) {x ε : ℝ}
    (hcol : IsRefCollar (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
      (relChart c (travAll R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε)
    (hpK : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ fwdHull (fun t : ℝ => W' t.toNNReal ω) s) :
    ∃ ρ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (x : ℂ) ρ →
      extendFrom H (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).2.1 u ∈
        fwdHull (fun t : ℝ => W' t.toNNReal ω) s := by
  set C := cfPocket (R ω) (L ω) r with hCdef
  set qs := (visitCap R L r η ψ ω s).toNNReal with hqsdef
  set cur := relChart c (travAll R L r η ψ) q ω with hcurdef
  set old := relChart c (travAll R L r η ψ) qs ω with holddef
  set p := extendFrom H cur.2.1 ξ with hpdef
  set T := leftStop R L r η ψ q ω with hTdef
  obtain ⟨hP, hJ⟩ := pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hAC := hcfg.attach
  have h0 := zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded
  have hTopo := hcfg.conf.isCfPocket h0
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hηc : ContinuousOn (η ω) (Ici 0) := hcfg.trace.2.1
  have hfill : ∀ t : ℝ, 0 ≤ t → fwdHull (fun t : ℝ => W' t.toNNReal ω) t = fillH (η ω '' Icc 0 t) :=
    fun t ht => hcfg.trace.2.2 t ht
  have hCH : C ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  -- the reference time is an interior visit, its capacity is live, and `T⁰(c(s)) = s ≤ T`
  have hsI : s ∈ Ioo (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    hP.mem_Ioo_of_mem hs0 hsC
  have hrc0 : 0 ≤ visitCap R L r η ψ ω s :=
    (isDrivenCurve_relCurve_of_isReversePocket hP hAC hJ).capClock_nonneg (relTime_nonneg hP hAC ⟨hsI.1.le, hsI.2⟩)
  have hqs : (qs : ℝ) = visitCap R L r η ψ ω s := Real.coe_toNNReal _ hrc0
  have hsq' : visitCap R L r η ψ ω s ≤ q := by rw [← hqs]; exact_mod_cast hsq
  have hqs_live : (qs : ℝ≥0∞) < capLife (travAll R L r η ψ ω) := lt_of_le_of_lt (by exact_mod_cast hsq) hq
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) C (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]; exact hq
  have hrs' : ENNReal.ofReal (visitCap R L r η ψ ω s) < capLife (trav (η ω) C
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [← hqs, ENNReal.ofReal_coe_nnreal]; exact hqs_live
  have hvis_s : ambTime0 (η ω) C (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
      (ψ ω) (visitCap R L r η ψ ω s) = s := ambTime0_relCap_of_visit hP hAC hJ ⟨hsI, hsC⟩
  have hTs : leftStop R L r η ψ qs ω = s := by
    show ambTime0 _ _ _ _ _ (qs : ℝ) = s
    rw [hqs]; exact hvis_s
  have hT_mem : T ∈ Ico (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) :=
    ambTime0_mem_Ico hP hAC hJ q.coe_nonneg hq'
  have hsT : s ≤ T := by
    have h1 := (ambTime0_le_iff hP hAC hJ q.coe_nonneg hq' hT_mem).1 le_rfl
    have h2 := (ambTime0_le_iff hP hAC hJ hrc0 hrs' hT_mem).2 (hsq'.trans h1)
    rwa [hvis_s] at h2
  -- the two domains
  have hcurdom : (cur.dom : Set ℂ) = C ∩ (H \ fillH (η ω '' Icc 0 T)) :=
    current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq
  have holddom : (old.dom : Set ℂ) = C ∩ (H \ fillH (η ω '' Icc 0 s)) := by
    rw [← hTs]; exact current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hqs_live
  have hKsT : fillH (η ω '' Icc 0 s) ⊆ fillH (η ω '' Icc 0 T) := fillH_mono (image_mono (Icc_subset_Icc_right hsT))
  -- the current landing `p` is visited by `s`
  obtain ⟨-, -, hpfr⟩ := current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq ξ
  have hpKs : p ∈ fillH (η ω '' Icc 0 s) := by rw [← hfill s hs0]; exact hpK
  have hpcl : p ∈ closure (H \ fillH (η ω '' Icc 0 s)) :=
    closure_mono (fun z (hz : z ∈ C ∩ (H \ fillH (η ω '' Icc 0 T))) =>
      (⟨hz.2.1, fun h => hz.2.2 (hKsT h)⟩ : z ∈ H \ fillH (η ω '' Icc 0 s))) (frontier_subset_closure hpfr)
  have hcpt : ∀ t, IsClosed (η ω '' Icc 0 t) := fun t =>
    (isCompact_Icc.image_of_continuousOn (hηc.mono fun u hu => hu.1)).isClosed
  have hpS : p ∈ η ω '' Icc 0 s := by
    have := mem_closure_of_mem_fillH_of_mem_closure_compl hpKs hpcl
    rwa [(hcpt s).closure_eq] at this
  have hpT : p ∈ η ω '' Icc 0 T := image_mono (Icc_subset_Icc_right hsT) hpS
  -- `p` is neither a time-`T` attachment nor `0`
  simp only [R5Wall.outerExc, mem_insert_iff, mem_singleton_iff, not_or] at hpX
  obtain ⟨hA₁, hA₂, hp0⟩ := hpX
  -- near `p` the walls are visited by `T`
  have hrevR := R7StopIn.cfArcR_rev hcfg.conf h0 hcfg.trace.1 hcfg.revR
  have hrevL := R7StopIn.cfArcL_rev hcfg.conf h0 hcfg.trace.1 hcfg.revL
  obtain ⟨r₁, hr₁, hball₁⟩ := R5Out.exists_ball_frontier_subset_range_of_wallOrder hTopo hrevR hrevL
    ⟨_, ⟨hP.nonneg, hT_mem.1⟩, hP.first_y⟩ hpT hA₁ hA₂
  -- the old chart and its inverse extension
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_of_jordan_cases
    (jordan_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ) hc hdom heq
  obtain ⟨F, hF, hFc, hFD⟩ := exists_relative_inverse_extension (c := c) (γ := travAll R L r η ψ) hγ hqs_live hE hEc
  have hold : old.IsConformal := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hqs_live hc
  have hxbar : ∀ u : ℝ, (u : ℂ) ∈ Hbar := fun u => mem_Hbar_of_im_eq_zero (by simp)
  have hlimF : ∀ u : ℝ, Tendsto old.2.1 (𝓝[H] (u : ℂ)) (𝓝 (F u)) := fun u =>
    (((hFc _ (hxbar u)).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hw => hF hw)
  have hcl : ∀ u : ℝ, (u : ℂ) ∈ closure H := fun u => by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact hxbar u
  have hNe : ∀ u : ℝ, (𝓝[H] (u : ℂ)).NeBot := fun u => mem_closure_iff_nhdsWithin_neBot.1 (hcl u)
  have hFx : F x = p := by
    have := hNe x
    exact tendsto_nhds_unique (hlimF x) (tendsto_nhdsWithin_iff.1 hcol.2.2.2.1).1
  have hext : ∀ u : ℝ, extendFrom H old.2.1 u = F u := fun u => extendFrom_eq (hcl u) (hlimF u)
  have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
  obtain ⟨ρ₀, hρ₀, hρF⟩ := Metric.continuousWithinAt_iff.1 (hFc _ (hxbar x)) (min r₁ ‖p‖) (lt_min hr₁ hpn)
  refine ⟨min ρ₀ ε, lt_min hρ₀ hcol.1, fun u hu => ?_⟩
  rw [hext, hfill s hs0]
  have hux : dist (u : ℂ) x < ρ₀ := lt_of_lt_of_le (mem_ball.1 hu) (min_le_left _ _)
  have hzb : dist (F u) p < min r₁ ‖p‖ := by
    have := hρF (hxbar u) hux
    rwa [hFx] at this
  have hzC : F u ∈ closure C := by
    obtain ⟨y, hy, hFy⟩ := hFD (hxbar u)
    exact hFy ▸ hED hy
  have hzfr : F u ∉ (old.dom : Set ℂ) := by
    have := inverse_real_landing_mem_frontier hold (hlimF u)
    rw [old.dom.isOpen.frontier_eq] at this
    exact this.2
  rw [holddom] at hzfr
  by_cases hzinC : F u ∈ C
  · by_contra hzK
    exact hzfr ⟨hzinC, hCH hzinC, hzK⟩
  -- a wall point near `p`, visited by `T`
  have hzF : F u ∈ frontier C := ⟨hzC, by rwa [hTopo.isOpen.interior_eq]⟩
  have hzT : F u ∈ η ω '' Icc 0 T := hball₁ ⟨hzF, lt_of_lt_of_le hzb (min_le_left _ _)⟩
  have hz0 : F u ≠ 0 := fun h => by
    have := lt_of_lt_of_le hzb (min_le_right _ _)
    rw [h, dist_zero_left] at this
    exact lt_irrefl _ this
  have hzH : F u ∈ H := mem_H_of_mem_frontier hTopo hzF hz0
  by_contra hzK
  have hzs : F u ∉ η ω '' Icc 0 s := fun h => hzK ⟨hzH, Or.inl (subset_closure h)⟩
  exact outerRefl_contra hcfg hψ hc hdom heq hs0 hqs_live holddom hcurdom hT_mem.2 hcol hlimF hNe hzF hzH hzK
    hzT hzs hsI (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 hu) (min_le_right _ _)))

/-- **`R5Lift.R7OuterRefl` holds on every bounded reverse-contained pocket test** (target (3), bounded shape): the
outer collars' old landings lie in `K_s` whenever the exceptional set contains the time-`T` attachments and `0`. -/
theorem r7OuterRefl_of_cfg [MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {X : Ω → Set ℂ} {q : ℝ≥0}
    (hcfg : ∀ ω ∈ A, IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : ∀ ω ∈ A, (c ω).IsConformal)
    (hdom : ∀ ω ∈ A, ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r)
    (heq : ∀ ω ∈ A, EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hX : ∀ ω ∈ A, R5Wall.outerExc R L r η ψ q ω ⊆ X ω) :
    R5Lift.R7OuterRefl P A R L r η ψ xL xR c W' ζ' X q := by
  refine Eventually.of_forall fun ω hω hq ξ _ hpX _ i x ε hev hsC hcol hpK => ?_
  have hpK' : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
      fwdHull (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i) := by
    rw [← hev.2.2.2.2]; exact hpK
  exact outerRefl_pathwise hω (hcfg ω hω) (hψ ω hω) (hc ω hω) (hdom ω hω) (heq ω hω) hq
    (fun h => hpX (hX ω hω h)) (rationalOriginalTime i).coe_nonneg hsC hev.2.2.2.1 hcol hpK'

end InteractingSLE.Sec7.WallOrd

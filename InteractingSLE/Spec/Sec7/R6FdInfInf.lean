/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdWireInf
import InteractingSLE.Spec.Sec7.R6FcWireInfInf

/-!
# R.6's non-corner input when both pockets open at the flow seed, from the inner hit

Packet PROVE-R6-FACE3. `R6Fc.R6NonCornerMixedInfInfRemaining` (outer pocket `C` and contained pocket `U` both opening
at the flow seed; `U` has no finite outgoing corner, so the landing has only the two conjuncts of
`R6Fc.IsNonCornerLandingInf`) from the named input `R6InnerSharedHitMixedInfInfRemaining` (the inner traversal at
infinity hits its open shared arc immediately). Because `U`'s outgoing corner is `∞`, no wall-visit order is needed:
the landing lies between the coordinate of the visited point of `U`'s open shared arc and that of a visited point of
`C`'s shared wall, and every such point is on `U`'s open shared arc.

* `erasedPath_mem_closure_visitsInf`, `exists_outer_relTipInf_eq_of_inner_hitInf` (bridge);
* `sharedArcInf`, `R6InnerSharedHitMixedInfInfRemaining` (**named, unproved**);
* `isClosed_image_Ici_of_tendsto`, `nonCorner_of_left_openInf`, `nonCorner_of_right_openInf`;
* `nonCornerLandingInfInf_left/_right`, **`r6NonCornerMixedInfInfRemaining_of_innerHit`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Fd

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen
  PocketStopWallsFin PocketStopSide R7StopIn
open WangWu (chartAL chartAR)

universe u

/-! ### Erased paths at infinity are limits of visits -/

section EraseInf

variable {η : ℝ → ℂ} {C : Set ℂ} {y₀ : ℂ} {τ : ℝ}

/-- **A point of the erased path (junction at infinity) at a positive clock value `v ≤ ℓ(T)` (`T` a visit time) is a
limit of the trace at visit times `≤ T`.** -/
theorem erasedPath_mem_closure_visitsInf (hP : IsErasurePocketInf η C y₀ τ) {T : ℝ} (hT : T ∈ visitSetInf η C τ)
    {v : ℝ} (hv0 : 0 < v) (hvT : v ≤ pocketClockInf η C τ T) :
    erasedPathInf η C τ v ∈ closure (η '' {t | t ∈ visitSetInf η C τ ∧ t ≤ T}) := by
  have hTe := hP.clock_lt_clockEnd_of_mem hT
  have hTI : pocketClockInf η C τ T ∈ Ico 0 (clockEnd η C τ) := ⟨hP.clock_nonneg hT.1.le, hTe⟩
  have hvI : v ∈ Ico 0 (clockEnd η C τ) := ⟨hv0.le, hvT.trans_lt hTe⟩
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨ρ, hρ, hρE⟩ := Metric.continuousWithinAt_iff.1 (hP.continuousOn_erasedPath v hvI) δ hδ
  set v₁ := max (v - ρ / 2) 0 with hv₁
  have hv₁v : v₁ < v := max_lt (by linarith) hv0
  have hv₁I : v₁ ∈ Ico 0 (clockEnd η C τ) := ⟨le_max_right _ _, hv₁v.trans hvI.2⟩
  set a := pocketFibreInf η C τ v₁
  set b := pocketFibreInf η C τ v
  have ha := hP.clock_fibre hv₁I
  have hb := hP.clock_fibre hvI
  have hab : a < b := lt_of_le_of_ne (hP.monotoneOn_fibre hv₁I hvI hv₁v.le) fun he => by
    have : pocketClockInf η C τ a = pocketClockInf η C τ b := by rw [he]
    rw [ha, hb] at this
    exact hv₁v.ne this
  obtain ⟨t, ht, htI⟩ := hP.exists_mem_of_clock_lt hab (by rw [ha, hb]; exact hv₁v.ne)
  have hta := hP.monotone_clock ht.1.le
  have htb := hP.monotone_clock ht.2.le
  rw [ha] at hta
  rw [hb] at htb
  have htT : t ≤ T := by
    have h1 : b ≤ pocketFibreInf η C τ (pocketClockInf η C τ T) := hP.monotoneOn_fibre hvI hTI hvT
    rw [hP.fibre_clock_of_mem hT] at h1
    exact ht.2.le.trans h1
  refine ⟨η t, ⟨t, ⟨htI, htT⟩, rfl⟩, ?_⟩
  have he : erasedPathInf η C τ (pocketClockInf η C τ t) = η t := by
    show η (pocketFibreInf η C τ (pocketClockInf η C τ t)) = η t
    rw [hP.fibre_clock_of_mem htI]
  rw [← he, dist_comm]
  refine hρE ⟨(le_max_right _ _).trans hta, htb.trans_lt hvI.2⟩ ?_
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith [le_max_left (v - ρ / 2) 0]

end EraseInf

section Bridge

variable {Ω : Type*}

/-- **The bridge, both pockets opening at the flow seed** (pathwise). -/
theorem exists_outer_relTipInf_eq_of_inner_hitInf {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ω : Ω} (hcf : IsOuterCfgInf (R ω) (L ω) r W (η ω))
    (hcfg' : IsCfPocketConfigInf (R' ω) (L' ω) r' W (η ω))
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r) {u : ℝ} (hu0 : 0 ≤ u)
    (hrel : relTipInf R L r η u ω ∈ cfPocket (R' ω) (L' ω) r') :
    ∃ ε > 0, ∀ u' ∈ Ioo 0 ε, ∃ u₁ : ℝ, 0 ≤ u₁ ∧ u₁ ≤ u ∧ relTipInf R L r η u₁ ω = relTipInf R' L' r' η u' ω := by
  have hPC := hcf.erase
  set L₀ := clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) with hL₀def
  have hL₀ : 0 < L₀ := hPC.clockEnd_pos
  have hPU := hcfg'.isReversePocketInf
  have hEU := isErasurePocketInf_of_isReversePocketInf hPU hcfg'.attach
  set LU := clockEnd (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0)) with hLUdef
  have hLU : 0 < LU := hEU.clockEnd_pos
  have hvC := clockOf_mem_Ico hL₀ hu0
  set T := pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
    (clockOf L₀ u) with hTdef
  have hT0 : 0 ≤ T := hPC.fibre_nonneg hvC
  have hηT : η ω T ∈ cfPocket (R' ω) (L' ω) r' := hrel
  have hTU : T ∈ visitSetInf (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0)) :=
    ⟨hPU.mem_Ioi_of_mem hT0 hηT, hηT⟩
  set vT := pocketClockInf (η ω) (cfPocket (R' ω) (L' ω) r') (firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0)) T
    with hvTdef
  have hvT0 : 0 < vT := SideVis.erasureInf_clock_pos_of_visit hEU hTU
  have hvTL : vT < LU := hEU.clock_lt_clockEnd_of_mem hTU
  refine ⟨vT / (LU - vT), div_pos hvT0 (sub_pos.2 hvTL), fun u' hu' => ?_⟩
  have hcT := PocketLife.clockOf_div_sub hLU hvTL
  have hmonoU := strictMonoOn_clockOf hLU
  have hv'0 : 0 < clockOf LU u' := by
    have := hmonoU (mem_Ici.2 le_rfl) (mem_Ici.2 hu'.1.le) hu'.1
    rwa [clockOf_zero] at this
  have hv'T : clockOf LU u' < vT := by
    have := hmonoU (mem_Ici.2 hu'.1.le) (mem_Ici.2 (div_pos hvT0 (sub_pos.2 hvTL)).le) hu'.2
    rwa [hcT] at this
  have hcl := erasedPath_mem_closure_visitsInf hEU hTU hv'0 hv'T.le
  have hsubV : η ω '' {t | t ∈ visitSetInf (η ω) (cfPocket (R' ω) (L' ω) r')
      (firstHit (η ω) (cfArcRInf (R' ω) (L' ω) r' 0)) ∧ t ≤ T} ⊆
      η ω '' {t | t ∈ visitSetInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) ∧
        t ≤ T} := by
    rintro _ ⟨t, ⟨htI, htT⟩, rfl⟩
    exact ⟨t, ⟨hPC.mem_visitSet (hEU.nonneg.trans htI.1.le) (hsub htI.2), htT⟩, rfl⟩
  obtain ⟨w, hw, hwe⟩ := closure_visits_subset_imageInf hPC hvC (closure_mono hsubV hcl)
  have hwL : w < L₀ := hw.2.trans_lt hvC.2
  refine ⟨w / (L₀ - w), div_nonneg hw.1 (sub_pos.2 hwL).le, ?_, ?_⟩
  · by_contra hlt
    push Not at hlt
    have := strictMonoOn_clockOf hL₀ (mem_Ici.2 hu0) (mem_Ici.2 (div_nonneg hw.1 (sub_pos.2 hwL).le)) hlt
    rw [PocketLife.clockOf_div_sub hL₀ hwL] at this
    linarith [hw.2]
  · show erasedPathInf _ _ _ (clockOf L₀ (w / (L₀ - w))) = _
    rw [PocketLife.clockOf_div_sub hL₀ hwL, hwe]
    rfl

end Bridge

/-! ### Points of the open shared arc of an inner pocket at infinity -/

/-- The image of `[0, ∞)` under a continuous curve tending to `∞` is closed. -/
theorem isClosed_image_Ici_of_tendsto {α : ℝ → ℂ} (hc : ContinuousOn α (Ici 0))
    (ht : Tendsto (fun v => ‖α v‖) atTop atTop) : IsClosed (α '' Ici 0) := by
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨V, hV⟩ := Filter.eventually_atTop.1 (ht.eventually_ge_atTop (‖x‖ + 1))
  set V' := max V 0
  have hsplit : α '' Ici 0 ⊆ α '' Icc 0 V' ∪ {z : ℂ | ‖x‖ + 1 ≤ ‖z‖} := by
    rintro _ ⟨v, hv, rfl⟩
    rcases le_total v V' with h | h
    · exact Or.inl ⟨v, ⟨hv, h⟩, rfl⟩
    · exact Or.inr (hV v ((le_max_left V 0).trans h))
  have hA : IsClosed (α '' Icc 0 V') :=
    (isCompact_Icc.image_of_continuousOn (hc.mono Icc_subset_Ici_self)).isClosed
  have hB : IsClosed {z : ℂ | ‖x‖ + 1 ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  have := closure_mono hsplit hx
  rw [(hA.union hB).closure_eq] at this
  rcases this with h | h
  · exact image_mono Icc_subset_Ici_self h
  · exact absurd (show ‖x‖ + 1 ≤ ‖x‖ from h) (by linarith)

/-- **A point of the open left arc of an inner pocket opening at the flow seed is a non-corner point** (the two
conjuncts of `R6Fc.IsNonCornerLandingInf`). -/
theorem nonCorner_of_left_openInf {R L R' : ℝ≥0 → ℂ} {r r' : ℝ≥0} (h : IsChangeConfigInc R L r)
    (hU : IsChangeConfigInc R' L r') (hU0 : rightLo R' L r' = 0) {θ : ℝ} (hθ : θ ∈ Ioo 0 (leftHi R' L r')) :
    wallPt L θ ∈ frontier (cfPocket R' L r') ∧
      wallPt L θ ∉ closure (frontier (cfPocket R' L r') ∩ cfPocket R L r) := by
  have hUc := hU.isCfPocketInf hU0
  obtain ⟨-, -, -, -, hb', -, -, -⟩ := hU.changeCorner_props
  have hhi : 0 < leftHi R' L r' := hθ.1.trans hθ.2
  set v := leftHi R' L r' / θ - 1 with hvdef
  have hv : 0 < v := by rw [hvdef, sub_pos, lt_div_iff₀ hθ.1, one_mul]; exact hθ.2
  have hpt : cfArcLInf R' L r' v = wallPt L θ := by
    show cfPt (WangWu.toDisc (Lemma71I.realPath L) (leftHi R' L r' / (1 + v))) = _
    rw [hvdef, add_sub_cancel, div_div_cancel₀ hhi.ne']
  have hnotR : ∀ w ∈ Ici (0 : ℝ), cfArcRInf R' L r' w ≠ wallPt L θ := by
    intro w hw he
    rw [← hpt] at he
    rcases (mem_Ici.1 hw).lt_or_eq with hw0 | hw0
    · exact hUc.sides w hw0 v hv he
    · rw [← hw0, ← hUc.seed] at he
      have := hUc.inj₂ (mem_Ici.2 le_rfl) (mem_Ici.2 hv.le) he
      linarith
  have hfrU : frontier (cfPocket R' L r') ∩ cfPocket R L r ⊆ cfArcRInf R' L r' '' Ici 0 := by
    rintro z ⟨hz, hzC⟩
    rw [hUc.frontier_eq] at hz
    rcases hz with hz | ⟨w, hw, rfl⟩
    · exact hz
    · exfalso
      have hm := div_one_add_mem hhi hw
      exact wallPt_notMem h (Or.inr rfl) ⟨hm.1, hm.2.trans hb'.2⟩ hzC
  have hcl := isClosed_image_Ici_of_tendsto hUc.cont₁ hUc.tendsto₁
  refine ⟨?_, fun hm => ?_⟩
  · rw [hUc.frontier_eq]; exact Or.inr ⟨v, mem_Ici.2 hv.le, hpt⟩
  · obtain ⟨w, hw, hwe⟩ := hcl.closure_subset_iff.2 hfrU hm
    exact hnotR w hw hwe

/-- **A point of the open right arc of an inner pocket opening at the flow seed is a non-corner point.** -/
theorem nonCorner_of_right_openInf {R L L' : ℝ≥0 → ℂ} {r r' : ℝ≥0} (h : IsChangeConfigInc R L r)
    (hU : IsChangeConfigInc R L' r') (hU0 : rightLo R L' r' = 0) {s : ℝ} (hs : s ∈ Ioo 0 (rightHi R L' r')) :
    wallPt R s ∈ frontier (cfPocket R L' r') ∧
      wallPt R s ∉ closure (frontier (cfPocket R L' r') ∩ cfPocket R L r) := by
  have hUc := hU.isCfPocketInf hU0
  obtain ⟨-, hv', -, -, -, -, -, -⟩ := hU.changeCorner_props
  have hhi : 0 < rightHi R L' r' := hs.1.trans hs.2
  set v := rightHi R L' r' / s - 1 with hvdef
  have hv : 0 < v := by rw [hvdef, sub_pos, lt_div_iff₀ hs.1, one_mul]; exact hs.2
  have hpt : cfArcRInf R L' r' v = wallPt R s := by
    show cfPt (WangWu.toDisc (Lemma71I.realPath R) (rightHi R L' r' / (1 + v))) = _
    rw [hvdef, add_sub_cancel, div_div_cancel₀ hhi.ne']
  have hnotL : ∀ w ∈ Ici (0 : ℝ), cfArcLInf R L' r' w ≠ wallPt R s := by
    intro w hw he
    rw [← hpt] at he
    rcases (mem_Ici.1 hw).lt_or_eq with hw0 | hw0
    · exact hUc.sides v hv w hw0 he.symm
    · rw [← hw0, hUc.seed] at he
      have := hUc.inj₁ (mem_Ici.2 le_rfl) (mem_Ici.2 hv.le) he
      linarith
  have hfrU : frontier (cfPocket R L' r') ∩ cfPocket R L r ⊆ cfArcLInf R L' r' '' Ici 0 := by
    rintro z ⟨hz, hzC⟩
    rw [hUc.frontier_eq] at hz
    rcases hz with ⟨w, hw, rfl⟩ | hz
    · exfalso
      have hm := div_one_add_mem hhi hw
      exact wallPt_notMem h (Or.inl rfl) ⟨hm.1, hm.2.trans hv'.2⟩ hzC
    · exact hz
  have hcl := isClosed_image_Ici_of_tendsto hUc.cont₂ hUc.tendsto₂
  refine ⟨?_, fun hm => ?_⟩
  · rw [hUc.frontier_eq]; exact Or.inl ⟨v, mem_Ici.2 hv.le, hpt⟩
  · obtain ⟨w, hw, hwe⟩ := hcl.closure_subset_iff.2 hfrU hm
    exact hnotL w hw hwe

/-! ### One realization, both pockets opening at the flow seed -/

section Path

variable {Ω : Type*}

/-- **The non-corner landing of the right seed coordinate, both pockets opening at the flow seed** (shared wall `L`;
one realization). -/
theorem nonCornerLandingInfInf_left {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {R' : ℝ≥0 → ℂ} {r r' : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) (hcfg' : IsCfPocketConfigInf R' (L ω) r' (W ω) (η ω))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket R' (L ω) r' ⊆ cfPocket (R ω) (L ω) r)
    {u : ℝ} (hu0 : 0 ≤ u) (hcap : capClock (travAllInf R L r η ψ ω) u = q)
    (hrel : relTipInf R L r η u ω ∈ cfPocket R' (L ω) r')
    {u₁ : ℝ} (hu₁0 : 0 ≤ u₁) (hcap₁ : capClock (travAllInf R L r η ψ ω) u₁ ≤ q)
    (harc : relTipInf R L r η u₁ ω ∈ cfArcLInf R' (L ω) r' '' Ioi 0) :
    R6Fc.IsNonCornerLandingInf (R6Fc.curChartInf A R L r η ψ n q ω) (R6Fc.seedRInf R L r η ψ q ω)
      (cfPocket R' (L ω) r') (cfPocket (R ω) (L ω) r) := by
  classical
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, -, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    R6Fc.chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht₁
  obtain ⟨-, -, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAllInf R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hcapq : capInv (travAllInf R L r η ψ ω) (q : ℝ) = u := by rw [← hcap]; exact hγ.capInv_eq hu0
  have htr : ∀ t ∈ Icc (0 : ℝ) q, ηC t = ψ ω (relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t) ω) ∧
      0 ≤ capInv (travAllInf R L r η ψ ω) t ∧ capInv (travAllInf R L r η ψ ω) t ≤ u := fun t ht => by
    refine ⟨hηCeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le)), ?_, hγ.capInv_le hu0 ht.1 (ht.2.trans hcap.ge)⟩
    refine (hγ.capInv_spec ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) ?_)).1
    rwa [ENNReal.ofReal_coe_nnreal]
  have hηCq : ηC q = ψ ω (relTipInf R L r η u ω) := by rw [(htr q ⟨hq0'.le, le_rfl⟩).1, hcapq]
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCq]
    exact (hψc ω hω).2.mapsTo (hsub hrel)
  have hlt : chartAL WC q < chartAR WC q :=
    (R6Fc.chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC).trans
      (R6Fc.chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC)
  have hC := hcf.conf
  have hC0 := hcf.seed
  have hor := hcf.oriented
  have hU := hcfg'.conf
  have hU0 := hcfg'.seed
  have hCc := hC.isCfPocketInf hC0
  have hUc := hU.isCfPocketInf hU0
  obtain ⟨hu, hv, huv, ha, hbC, hab, hLa, hLb⟩ := hC.changeCorner_props
  have hhiR : 0 < rightHi (R ω) (L ω) r := hC0 ▸ huv
  have hhiL : 0 < leftHi (R ω) (L ω) r := (hC.leftLo_eq_zero_of_rightLo_eq_zero hC0) ▸ hab
  have hs₁c : capClock (travAllInf R L r η ψ ω) u₁ ∈ Icc (0 : ℝ) q := ⟨hγ.capClock_nonneg hu₁0, hcap₁⟩
  have hvR : R6Fc.seedRInf R L r η ψ q ω = chartAR WC q := R6Fc.seedR_eq hWC hWCq
  obtain ⟨hb, ⟨t₂, ht₂, ht₂im, ht₂le⟩, hall⟩ := landR_spec hηC hWC hWC0 hq0' hlt
  have hland : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedRInf R L r η ψ q ω : ℂ) =
      E₀ (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)) := by
    have hvcl : ((chartAR WC q : ℝ) : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar _
    rw [hvR]
    exact extendFrom_eq hvcl (R6Fc.tendsto_of_extension hOE hOEc (chartAR WC q))
  obtain ⟨-, -, -, -, hb', hab', -, hLb'⟩ := hU.changeCorner_props
  have hhi' : 0 < leftHi R' (L ω) r' := (hU.leftLo_eq_zero_of_rightLo_eq_zero hU0) ▸ hab'
  -- the lower witness
  obtain ⟨v₁, hv₁, hv₁e⟩ := harc
  set θ₁ := leftHi R' (L ω) r' / (1 + v₁) with hθ₁def
  have hθ₁ : θ₁ ∈ Ioo 0 (leftHi R' (L ω) r') :=
    ⟨div_pos hhi' (by linarith [mem_Ioi.1 hv₁]), div_lt_self hhi' (by linarith [mem_Ioi.1 hv₁])⟩
  have hθ₁e : relTipInf R L r η u₁ ω = wallPt (L ω) θ₁ := hv₁e.symm
  have hUcl : ∀ θ ∈ Ioc 0 (leftHi R' (L ω) r'), wallPt (L ω) θ ∈ closure (cfPocket (R ω) (L ω) r) := by
    intro θ hθ
    obtain ⟨v, hv, hve⟩ := exists_div_one_add_eq hθ
    refine closure_mono hsub (frontier_subset_closure ?_)
    rw [hUc.frontier_eq]
    exact Or.inr ⟨v, hv, by rw [← hve]; rfl⟩
  have hθ₁01 : θ₁ ∈ Ioc (0 : ℝ) 1 := ⟨hθ₁.1, hθ₁.2.le.trans hb'.2⟩
  have hhiU : leftHi R' (L ω) r' ≤ leftHi (R ω) (L ω) r :=
    le_leftHi_of_mem_closureInf hC hC0 ⟨hhi', hb'.2⟩ (hUcl _ ⟨hhi', le_rfl⟩)
  have hθ₁C : θ₁ ∈ Ioc 0 (leftHi (R ω) (L ω) r) := ⟨hθ₁.1, hθ₁.2.le.trans hhiU⟩
  obtain ⟨hfacts, hcont, hanti⟩ := left_arc_factsInf hC hC0 hor hJ
  have hηC₁ : ηC (capClock (travAllInf R L r η ψ ω) u₁) = ψ ω (wallPt (L ω) θ₁) := by
    rw [(htr _ hs₁c).1, hγ.capInv_eq hu₁0, hθ₁e]
  have hb₁ : (ψ ω (wallPt (L ω) θ₁)).re ≤ (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re := by
    have := hall _ hs₁c (by rw [hηC₁]; exact (hfacts θ₁ hθ₁C).2)
    rwa [hηC₁] at this
  have hpos₁ : 0 < (ψ ω (wallPt (L ω) θ₁)).re := (SideAnc.jordanInf_sides hC hC0 hor hJ).2 θ₁
    (by rw [hC.leftLo_eq_zero_of_rightLo_eq_zero hC0]; exact ⟨hθ₁.1, hθ₁.2.trans_le hhiU⟩)
  -- the upper witness
  obtain ⟨hcI₂, hcI₂0, hcI₂u⟩ := htr t₂ ht₂
  set p₂ := relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t₂) ω with hp₂def
  have hf₂ := relTip_factsInf hcf hcI₂0 hcI₂u
  have hp₂re : (ψ ω p₂).im = 0 := by rw [← hcI₂]; exact ht₂im
  have hp₂fr : p₂ ∈ frontier (cfPocket (R ω) (L ω) r) := by
    refine ⟨hf₂.1, fun hin => ?_⟩
    rw [(hCo ω hω).interior_eq] at hin
    have := (hψc ω hω).2.mapsTo hin
    exact (ne_of_gt (show (0 : ℝ) < (ψ ω p₂).im from this)) hp₂re
  have hb₂ : (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re ≤ (ψ ω p₂).re := by rw [← hcI₂]; exact ht₂le
  rw [hCc.frontier_eq] at hp₂fr
  rcases hp₂fr with ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · exfalso
    have hsI := div_one_add_mem hhiR hw
    obtain ⟨-, -, hmono⟩ := right_arc_factsInf hC hC0 hor hJ
    have hle := hmono.monotoneOn hsI ⟨hhiR, le_rfl⟩ hsI.2
    have h0 : (ψ ω (wallPt (R ω) (rightHi (R ω) (L ω) r))).re = 0 := by
      have : wallPt (R ω) (rightHi (R ω) (L ω) r) = cfPt (closePt (R ω) (L ω) r) := rfl
      rw [this, hJ.2.2.2.2.2.1]; rfl
    have hp₂R : ψ ω p₂ = ψ ω (wallPt (R ω) (rightHi (R ω) (L ω) r / (1 + w))) := by rw [← hwe]; rfl
    have : (ψ ω p₂).re ≤ 0 := by rw [hp₂R]; exact hle.trans h0.le
    linarith
  · set θ₂ := leftHi (R ω) (L ω) r / (1 + w) with hθ₂def
    have hθ₂C := div_one_add_mem hhiL hw
    have hp₂e : p₂ = wallPt (L ω) θ₂ := hwe.symm
    rw [hp₂e] at hb₂
    have h21 : θ₂ ≤ θ₁ := by
      by_contra hlt'
      push Not at hlt'
      have := hanti hθ₁C hθ₂C hlt'
      linarith
    have hcI : ContinuousOn (fun θ => (ψ ω (wallPt (L ω) θ)).re) (Icc θ₂ θ₁) :=
      (Complex.continuous_re.comp_continuousOn hcont).mono fun θ hθ => ⟨hθ₂C.1.trans_le hθ.1, hθ.2.trans hθ₁C.2⟩
    obtain ⟨θ, hθ, he⟩ := intermediate_value_Icc' h21 hcI ⟨hb₁, hb₂⟩
    have hθC : θ ∈ Ioc 0 (leftHi (R ω) (L ω) r) := ⟨hθ₂C.1.trans_le hθ.1, hθ.2.trans hθ₁C.2⟩
    have hθU : θ ∈ Ioo 0 (leftHi R' (L ω) r') := ⟨hθ₂C.1.trans_le hθ.1, hθ.2.trans_lt hθ₁.2⟩
    have hψθ : ψ ω (wallPt (L ω) θ) = ((extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]; exact he) (by rw [Complex.ofReal_im]; exact (hfacts θ hθC).2)
    have hpF : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedRInf R L r η ψ q ω : ℂ) =
        wallPt (L ω) θ := by
      rw [hland, hb, ← hψθ]
      exact extension_psi_eqInf hJ hE₀ hE₀c (hfacts θ hθC).1
    obtain ⟨h1, h2⟩ := nonCorner_of_left_openInf hC hU hU0 hθU
    exact ⟨hpF ▸ h1, hpF ▸ h2⟩

/-- **The non-corner landing of the left seed coordinate, both pockets opening at the flow seed** (shared wall `R`;
one realization). -/
theorem nonCornerLandingInfInf_right {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {L' : ℝ≥0 → ℂ} {r r' : ℝ≥0}
    {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) (hcfg' : IsCfPocketConfigInf (R ω) L' r' (W ω) (η ω))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) L' r' ⊆ cfPocket (R ω) (L ω) r)
    {u : ℝ} (hu0 : 0 ≤ u) (hcap : capClock (travAllInf R L r η ψ ω) u = q)
    (hrel : relTipInf R L r η u ω ∈ cfPocket (R ω) L' r')
    {u₁ : ℝ} (hu₁0 : 0 ≤ u₁) (hcap₁ : capClock (travAllInf R L r η ψ ω) u₁ ≤ q)
    (harc : relTipInf R L r η u₁ ω ∈ cfArcRInf (R ω) L' r' '' Ioi 0) :
    R6Fc.IsNonCornerLandingInf (R6Fc.curChartInf A R L r η ψ n q ω) (R6Fc.seedLInf R L r η ψ q ω)
      (cfPocket (R ω) L' r') (cfPocket (R ω) (L ω) r) := by
  classical
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, -, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    R6Fc.chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht₁
  obtain ⟨-, -, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAllInf R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hcapq : capInv (travAllInf R L r η ψ ω) (q : ℝ) = u := by rw [← hcap]; exact hγ.capInv_eq hu0
  have htr : ∀ t ∈ Icc (0 : ℝ) q, ηC t = ψ ω (relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t) ω) ∧
      0 ≤ capInv (travAllInf R L r η ψ ω) t ∧ capInv (travAllInf R L r η ψ ω) t ≤ u := fun t ht => by
    refine ⟨hηCeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le)), ?_, hγ.capInv_le hu0 ht.1 (ht.2.trans hcap.ge)⟩
    refine (hγ.capInv_spec ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) ?_)).1
    rwa [ENNReal.ofReal_coe_nnreal]
  have hηCq : ηC q = ψ ω (relTipInf R L r η u ω) := by rw [(htr q ⟨hq0'.le, le_rfl⟩).1, hcapq]
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCq]
    exact (hψc ω hω).2.mapsTo (hsub hrel)
  have hlt : chartAL WC q < chartAR WC q :=
    (R6Fc.chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC).trans
      (R6Fc.chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC)
  have hC := hcf.conf
  have hC0 := hcf.seed
  have hor := hcf.oriented
  have hU := hcfg'.conf
  have hU0 := hcfg'.seed
  have hCc := hC.isCfPocketInf hC0
  have hUc := hU.isCfPocketInf hU0
  obtain ⟨hu, hv, huv, ha, hbC, hab, hLa, hLb⟩ := hC.changeCorner_props
  have hhiR : 0 < rightHi (R ω) (L ω) r := hC0 ▸ huv
  have hhiL : 0 < leftHi (R ω) (L ω) r := (hC.leftLo_eq_zero_of_rightLo_eq_zero hC0) ▸ hab
  have hs₁c : capClock (travAllInf R L r η ψ ω) u₁ ∈ Icc (0 : ℝ) q := ⟨hγ.capClock_nonneg hu₁0, hcap₁⟩
  have hvL : R6Fc.seedLInf R L r η ψ q ω = chartAL WC q := R6Fc.seedL_eq hWC hWCq
  obtain ⟨hb, ⟨t₂, ht₂, ht₂im, ht₂le⟩, hall⟩ := landL_spec hηC hWC hWC0 hq0' hlt
  have hland : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedLInf R L r η ψ q ω : ℂ) =
      E₀ (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)) := by
    have hvcl : ((chartAL WC q : ℝ) : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar _
    rw [hvL]
    exact extendFrom_eq hvcl (R6Fc.tendsto_of_extension hOE hOEc (chartAL WC q))
  obtain ⟨-, hv', huv', -, -, -, -, -⟩ := hU.changeCorner_props
  have hhi' : 0 < rightHi (R ω) L' r' := hU0 ▸ huv'
  obtain ⟨v₁, hv₁, hv₁e⟩ := harc
  set s₁ := rightHi (R ω) L' r' / (1 + v₁) with hs₁def
  have hs₁ : s₁ ∈ Ioo 0 (rightHi (R ω) L' r') :=
    ⟨div_pos hhi' (by linarith [mem_Ioi.1 hv₁]), div_lt_self hhi' (by linarith [mem_Ioi.1 hv₁])⟩
  have hs₁e : relTipInf R L r η u₁ ω = wallPt (R ω) s₁ := hv₁e.symm
  have hUcl : ∀ s ∈ Ioc 0 (rightHi (R ω) L' r'), wallPt (R ω) s ∈ closure (cfPocket (R ω) (L ω) r) := by
    intro s hs
    obtain ⟨v, hv0, hve⟩ := exists_div_one_add_eq hs
    refine closure_mono hsub (frontier_subset_closure ?_)
    rw [hUc.frontier_eq]
    exact Or.inl ⟨v, hv0, by rw [← hve]; rfl⟩
  have hhiU : rightHi (R ω) L' r' ≤ rightHi (R ω) (L ω) r :=
    le_rightHi_of_mem_closureInf hC hC0 ⟨hhi', hv'.2⟩ (hUcl _ ⟨hhi', le_rfl⟩)
  have hs₁C : s₁ ∈ Ioc 0 (rightHi (R ω) (L ω) r) := ⟨hs₁.1, hs₁.2.le.trans hhiU⟩
  obtain ⟨hfacts, hcont, hmono⟩ := right_arc_factsInf hC hC0 hor hJ
  have hηC₁ : ηC (capClock (travAllInf R L r η ψ ω) u₁) = ψ ω (wallPt (R ω) s₁) := by
    rw [(htr _ hs₁c).1, hγ.capInv_eq hu₁0, hs₁e]
  have hb₁ : (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re ≤ (ψ ω (wallPt (R ω) s₁)).re := by
    have := hall _ hs₁c (by rw [hηC₁]; exact (hfacts s₁ hs₁C).2)
    rwa [hηC₁] at this
  have hneg₁ : (ψ ω (wallPt (R ω) s₁)).re < 0 := (SideAnc.jordanInf_sides hC hC0 hor hJ).1 s₁
    (by rw [hC0]; exact ⟨hs₁.1, hs₁.2.trans_le hhiU⟩)
  obtain ⟨hcI₂, hcI₂0, hcI₂u⟩ := htr t₂ ht₂
  set p₂ := relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t₂) ω with hp₂def
  have hf₂ := relTip_factsInf hcf hcI₂0 hcI₂u
  have hp₂re : (ψ ω p₂).im = 0 := by rw [← hcI₂]; exact ht₂im
  have hp₂fr : p₂ ∈ frontier (cfPocket (R ω) (L ω) r) := by
    refine ⟨hf₂.1, fun hin => ?_⟩
    rw [(hCo ω hω).interior_eq] at hin
    have := (hψc ω hω).2.mapsTo hin
    exact (ne_of_gt (show (0 : ℝ) < (ψ ω p₂).im from this)) hp₂re
  have hb₂ : (ψ ω p₂).re ≤ (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re := by rw [← hcI₂]; exact ht₂le
  rw [hCc.frontier_eq] at hp₂fr
  rcases hp₂fr with ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · set s₂ := rightHi (R ω) (L ω) r / (1 + w) with hs₂def
    have hs₂C := div_one_add_mem hhiR hw
    have hp₂e : p₂ = wallPt (R ω) s₂ := hwe.symm
    rw [hp₂e] at hb₂
    have h21 : s₂ ≤ s₁ := by
      by_contra hlt'
      push Not at hlt'
      have := hmono hs₁C hs₂C hlt'
      linarith
    have hcI : ContinuousOn (fun s => (ψ ω (wallPt (R ω) s)).re) (Icc s₂ s₁) :=
      (Complex.continuous_re.comp_continuousOn hcont).mono fun s hs => ⟨hs₂C.1.trans_le hs.1, hs.2.trans hs₁C.2⟩
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc h21 hcI ⟨hb₂, hb₁⟩
    have hsC : s ∈ Ioc 0 (rightHi (R ω) (L ω) r) := ⟨hs₂C.1.trans_le hs.1, hs.2.trans hs₁C.2⟩
    have hsU : s ∈ Ioo 0 (rightHi (R ω) L' r') := ⟨hs₂C.1.trans_le hs.1, hs.2.trans_lt hs₁.2⟩
    have hψs : ψ ω (wallPt (R ω) s) = ((extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re : ℂ) :=
      Complex.ext (by rw [Complex.ofReal_re]; exact he) (by rw [Complex.ofReal_im]; exact (hfacts s hsC).2)
    have hpF : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedLInf R L r η ψ q ω : ℂ) =
        wallPt (R ω) s := by
      rw [hland, hb, ← hψs]
      exact extension_psi_eqInf hJ hE₀ hE₀c (hfacts s hsC).1
    obtain ⟨h1, h2⟩ := nonCorner_of_right_openInf hC hU hU0 hsU
    exact ⟨hpF ▸ h1, hpF ▸ h2⟩
  · exfalso
    have hθI := div_one_add_mem hhiL hw
    obtain ⟨-, -, hanti⟩ := left_arc_factsInf hC hC0 hor hJ
    have hge := hanti.antitoneOn hθI ⟨hhiL, le_rfl⟩ hθI.2
    have h0 : (ψ ω (wallPt (L ω) (leftHi (R ω) (L ω) r))).re = 0 := by
      have : wallPt (L ω) (leftHi (R ω) (L ω) r) = cfPt (closePt (R ω) (L ω) r) := by
        show cfPt (WangWu.toDisc _ _) = cfPt _; rw [hLb]
      rw [this, hJ.2.2.2.2.2.1]; rfl
    have hp₂L : ψ ω p₂ = ψ ω (wallPt (L ω) (leftHi (R ω) (L ω) r / (1 + w))) := by rw [← hwe]; rfl
    have : 0 ≤ (ψ ω p₂).re := by rw [hp₂L]; exact h0.ge.trans hge
    linarith

end Path

/-! ### The named input and the wiring -/

/-- **The open shared arc of an inner pocket opening at the flow seed**: its open left arc at infinity when the shared
wall is the left wall (`d < r_L`), its open right arc otherwise. -/
def sharedArcInf (k rL : ℝ) (R' L' : ℝ≥0 → ℂ) (r' : ℝ≥0) : Set ℂ :=
  if k / 2 - 4 < rL then cfArcLInf R' L' r' '' Ioi 0 else cfArcRInf R' L' r' '' Ioi 0

/-- **Named, unproved: the inner pocket's traversal at infinity hits its open shared arc immediately** (both pockets
opening at the flow seed; the analogue of `R6InnerSharedHitMixedRemaining` for `IsCfPocketConfigInf`): almost surely
on the inner test, the erased traversal of `U` lies on `U`'s open shared arc at relative times in `(0, ε)` for every
`ε > 0` (shared-side weight `≤ κ′/2 − 4 < κ′/2 − 2`: Bessel dimension `< 2` from `0`). -/
def R6InnerSharedHitMixedInfInfRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (A' : Set Ω) (s : ℚ),
      (∀ ω ∈ A', IsCfPocketConfigInf (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω)) →
      ∀ᵐ ω ∂P, ω ∈ A' → ∀ ε : ℝ, 0 < ε → ∃ u' ∈ Ioo 0 ε,
        relTipInf (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η u' ω ∈
          sharedArcInf k rL (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)

/-- **R.6's non-corner input when both pockets open at the flow seed, from the inner traversal's immediate
shared-side hit**: `R6InnerSharedHitMixedInfInfRemaining → R6Fc.R6NonCornerMixedInfInfRemaining`. -/
theorem r6NonCornerMixedInfInfRemaining_of_innerHit {k rL rR c c' : ℝ}
    (hI : R6InnerSharedHitMixedInfInfRemaining.{u} k rL rR c c') :
    R6Fc.R6NonCornerMixedInfInfRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML r A A' ψ ψ' n s q hA hA'
  filter_upwards [hI hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML A' s
    fun ω hω => (hA' ω hω).1] with ω hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  obtain ⟨ε, hε, hall⟩ := exists_outer_relTipInf_eq_of_inner_hitInf (hA ω hωA).1 (hA' ω hωA').1 hsub hu0 hrel
  obtain ⟨u', hu', hhit⟩ := hω hωA' ε hε
  obtain ⟨u₁, hu₁0, hu₁u, he⟩ := hall u' hu'
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := ((hA ω hωA).1.props (hA ω hωA).2).1
  have harc : relTipInf R L r η u₁ ω ∈
      sharedArcInf k rL (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by rw [he]; exact hhit
  have hcap₁ : capClock (travAllInf R L r η ψ ω) u₁ ≤ q := by
    rw [← hcap]
    exact hγ.strictMonoOn_capClock.monotoneOn (mem_Ici.2 hu₁0) (mem_Ici.2 hu0) hu₁u
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hU := (hA' ω hωA').1
  rcases hmix with ⟨hdL, hdR⟩ | ⟨hdL, hdR⟩
  · have eR : innerRight k rL R MR ω = MR ω := by simp only [innerRight, hdL, ↓reduceIte]
    have eL : innerLeft k rR L ML ω = L ω := by simp only [innerLeft, not_lt.2 hdR, ↓reduceIte]
    simp only [sharedArcInf, hdL, ↓reduceIte] at harc
    simp only [hdL, ↓reduceIte]
    rw [eR, eL] at hU hsub hrel harc ⊢
    exact nonCornerLandingInfInf_left (W := fun ω t => W' t.toNNReal ω) (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hωA hU hq0' hqlive hsub hu0 (by rw [hrtq]; exact hcap) hrel hu₁0
      (by rw [hrtq]; exact hcap₁) harc
  · have eR : innerRight k rL R MR ω = R ω := by simp only [innerRight, not_lt.2 hdL, ↓reduceIte]
    have eL : innerLeft k rR L ML ω = ML ω := by simp only [innerLeft, hdR, ↓reduceIte]
    simp only [sharedArcInf, not_lt.2 hdL, ↓reduceIte] at harc
    simp only [not_lt.2 hdL, ↓reduceIte]
    rw [eR, eL] at hU hsub hrel harc ⊢
    exact nonCornerLandingInfInf_right (W := fun ω t => W' t.toNNReal ω) (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hωA hU hq0' hqlive hsub hu0 (by rw [hrtq]; exact hcap) hrel hu₁0
      (by rw [hrtq]; exact hcap₁) harc

end InteractingSLE.Sec7.R6Fd

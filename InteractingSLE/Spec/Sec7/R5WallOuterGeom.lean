/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallOuterHeight
import InteractingSLE.Spec.Sec7.R5LiftSeed
import InteractingSLE.Spec.Sec7.ReverseArcModel

/-!
# R.5's exposed coordinates landing on the pocket wall: the pathwise geometry (bounded change pocket; ruling R86a)

Packet PROVE-R5-WALL (second round). At relative capacity `q > 0`, let `ξ` be a current coordinate in the open exposed
interval whose landing `p` lies outside the open pocket `C` (on a wall), off the two **attachments** at the left stop
and off `0`. Then:

* `p` lies on the counterflow trace before the left stop (`mem_range_of_seed_interval_landing`: the landing of an
  exposed coordinate is in the current fill — R5-LIFT's `landing_mem_hull_of_mem_seed_interval` — and a fill point
  that is a limit of unfilled points is on the trace);
* near `p` the whole pocket frontier is on that trace (`exists_ball_frontier_subset_range`: the walls are visited in
  reverse order, so off the attachments every wall point near a visited one is visited);
* a rational interior visit `s` before the left stop carries an unfilled collar and the trace after `s` avoids a ball
  about `p` (`exists_visit_collar_tail`, R5-REFCHART's construction keeping its tail-avoidance ball), so the pocket
  frontier near `p` is in the hull `K_s`;
* hence the current approach eventually stays in a component of `(ℍ ∖ K_s) ∩ B(p, r)` contained in `C`, i.e. missing
  the pocket exterior (`eventually_mem_freeNear`) — the hypothesis of the per-prime-end Proposition 3.8.

Ruling R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Wall

open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase R5Ref
open Theorem14.SB.FinRel (freeNear)
open MartChar.RealFlow
open Wire.Current.SideTest (rationalOriginalTime)

/-! ### Generic topology -/

/-- **The `freeNear` criterion**: if near `p` the frontier of the open set `C` (inside `ℍ`) lies in `K`, every approach
that eventually lies in `ℍ ∩ (C ∖ K)` eventually lies in a component of `(ℍ ∖ K) ∩ B(p, r)` contained in `C`, hence
missing any set `E` disjoint from `C`. -/
theorem eventually_mem_freeNear {C K E : Set ℂ} (hCo : IsOpen C) (hE : ∀ z ∈ C, z ∉ E) {p : ℂ} {r : ℝ}
    (hfr : frontier C ∩ ball p r ∩ H ⊆ K) {α : Type*} {l : Filter α} {f : α → ℂ} (hf : Tendsto f l (𝓝 p))
    (hfC : ∀ᶠ y in l, f y ∈ H ∩ (C \ K)) (hr : 0 < r) : ∀ᶠ y in l, f y ∈ freeNear E K p r := by
  filter_upwards [hfC, hf (ball_mem_nhds p hr)] with y hy hyb
  have hmem : f y ∈ (H \ K) ∩ ball p r := ⟨⟨hy.1, hy.2.2⟩, hyb⟩
  refine ⟨hmem, ?_⟩
  set S := connectedComponentIn ((H \ K) ∩ ball p r) (f y) with hS
  have hSsub : S ⊆ (H \ K) ∩ ball p r := connectedComponentIn_subset _ _
  have hSC : S ⊆ C := by
    refine subset_of_isPreconnected_of_disjoint_frontier isPreconnected_connectedComponentIn hCo
      ⟨f y, mem_connectedComponentIn hmem, hy.2.1⟩ ?_
    refine Set.disjoint_left.2 fun z hzS hzF => ?_
    have hz := hSsub hzS
    exact hz.1.2 (hfr ⟨⟨hzF, hz.2⟩, hz.1.1⟩)
  exact Set.disjoint_left.2 fun z hzS hzE => hE z (hSC hzS) hzE

/-- **Off the attachments, the pocket frontier near a visited point is visited** (reverse pocket): if `p` is on the
trace up to `T ≥ τ` and is neither first-visit attachment at `T`, some ball about `p` meets the frontier of `C` only in
the trace up to `T`. -/
theorem exists_ball_frontier_subset_range {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ}
    (hP : IsReversePocket W η C α₁ α₂ β τ σ) {T : ℝ} (hτT : τ ≤ T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (h₁ : p ≠ α₁ (firstVisit (fun t => η '' Icc 0 t) α₁ T))
    (h₂ : p ≠ α₂ (firstVisit (fun t => η '' Icc 0 t) α₂ T)) :
    ∃ r > 0, frontier C ∩ ball p r ⊆ η '' Icc 0 T := by
  have hyR : α₁ 1 ∈ η '' Icc 0 T := ⟨τ, ⟨hP.nonneg, hτT⟩, hP.first_y⟩
  -- one wall at a time
  have key : ∀ (α : ℝ → ℂ), ContinuousOn α (Icc 0 1) → InjOn α (Icc 0 1) →
      R16.IsReverseVisitOrder α (fun t => η '' Icc 0 t) → α 1 ∈ η '' Icc 0 T →
      p ≠ α (firstVisit (fun t => η '' Icc 0 t) α T) →
      IsCompact (α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T)) ∧
        p ∉ α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T) ∧
        ∀ w ∈ Icc (0 : ℝ) 1, α w ∉ α '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α T) →
          α w ∈ η '' Icc 0 T := by
    intro α hαc hαi hrev h1 hp
    set V := {v ∈ Icc (0 : ℝ) 1 | α v ∈ η '' Icc 0 T} with hV
    have h1V : (1 : ℝ) ∈ V := ⟨⟨zero_le_one, le_rfl⟩, h1⟩
    have hne : V.Nonempty := ⟨1, h1V⟩
    have hbdd : BddBelow V := ⟨0, fun v hv => hv.1.1⟩
    have hu1 : sInf V ≤ 1 := csInf_le hbdd h1V
    have hu0 : 0 ≤ sInf V := le_csInf hne fun v hv => hv.1.1
    have hfv : firstVisit (fun t => η '' Icc 0 t) α T = sInf V := rfl
    rw [hfv] at hp ⊢
    refine ⟨isCompact_Icc.image_of_continuousOn (hαc.mono (Icc_subset_Icc_right hu1)), ?_, ?_⟩
    · rintro ⟨w, hw, hpw⟩
      have hwV : w ∈ V := ⟨⟨hw.1, hw.2.trans hu1⟩, hpw ▸ hpR⟩
      have hwu : w = sInf V := le_antisymm hw.2 (csInf_le hbdd hwV)
      exact hp (by rw [← hpw, hwu])
    · intro w hw hnot
      have hlt : sInf V < w := by
        by_contra hle
        exact hnot ⟨w, ⟨hw.1, not_lt.1 hle⟩, rfl⟩
      obtain ⟨v₀, hv₀, hv₀w⟩ := exists_lt_of_csInf_lt hne hlt
      exact hrev T v₀ hv₀.1 w hw hv₀w.le hv₀.2
  obtain ⟨hK₁, hp₁, hv₁⟩ := key α₁ hP.cont₁ hP.inj₁ hP.rev₁ hyR h₁
  obtain ⟨hK₂, hp₂, hv₂⟩ := key α₂ hP.cont₂ hP.inj₂ hP.rev₂ (hP.seed ▸ hyR) h₂
  have hKc : IsClosed ((α₁ '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α₁ T)) ∪
      α₂ '' Icc 0 (firstVisit (fun t => η '' Icc 0 t) α₂ T)) := (hK₁.union hK₂).isClosed
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl p (by
    rintro (h | h)
    · exact hp₁ h
    · exact hp₂ h)
  refine ⟨r, hr, fun z ⟨hzF, hzb⟩ => ?_⟩
  have hzK := hball hzb
  rw [hP.frontier_eq] at hzF
  rcases hzF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hv₁ w hw fun h => hzK (Or.inl h)
  · exact hv₂ w hw fun h => hzK (Or.inr h)

/-! ### The bounded change pocket -/

section Bounded

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

/-- **An exposed coordinate landing in `ℍ` outside the pocket lands on the trace before the left stop** (bounded
change pocket, seeds at `0`): its landing is in the current fill (R5-LIFT), and a fill point that is a limit of
current points is on the trace. -/
theorem mem_range_of_seed_interval_landing (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
        segDriver (travAll R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q))
    (hpH : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ H) :
    extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ η ω '' Icc 0 (leftStop R L r η ψ q ω) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨E, hE, hEc⟩ := hcExt
  have hland := (current_landing hω hcfg hψ hc hdom heq hq ξ).1
  have hdomEq := current_dom_eq hω hcfg hψ hc hdom heq hq
  have hRc : IsCompact (η ω '' Icc 0 (leftStop R L r η ψ q ω)) :=
    isCompact_Icc.image_of_continuousOn (hcfg.trace.2.1.mono fun t ht => ht.1)
  have hKo := isOpen_H_diff_fillH hRc.isBounded
  have hK := R5Lift.landing_mem_hull_of_mem_seed_interval (iL := 0) (iR := 0) hxL hxR hc hγ hq hq0 hE hEc hdom hKo
    hdomEq hξ hland hpH
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hcl : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈
      closure (H \ fillH (η ω '' Icc 0 (leftStop R L r η ψ q ω))) := by
    have := R5Lift.nhdsWithin_H_neBot ξ
    refine mem_closure_of_tendsto hland (eventually_nhdsWithin_of_forall fun y hy => ?_)
    have h1 : (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
        ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) := hNow.inv_mem_dom hy
    rw [hdomEq] at h1
    exact h1.2
  exact ReverseArc.mem_of_mem_fillH_of_mem_closure hRc.isClosed hK hcl

/-- **Lemma R.5's unfilled visit collar with its tail-avoidance ball** (bounded change pocket): R5-REFCHART's
`exists_visit_collar`, keeping the ball about the landing that the trace avoids after the selected visit. -/
theorem exists_visit_collar_tail (hω : ω ∈ A) (hcfg : IsCfPocketConfig (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hNotTip : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ η ω (leftStop R L r η ψ q ω))
    (hNotExit : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ≠ cfPt (openPt (R ω) (L ω) r)) :
    ∃ s : ℚ, 0 ≤ (s : ℝ) ∧ η ω s ∈ cfPocket (R ω) (L ω) r ∧ (visitCap R L r η ψ ω s).toNNReal ≤ q ∧
      η ω s ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∧ (s : ℝ) < leftStop R L r η ψ q ω ∧
      (∃ ρ > 0, Disjoint (η ω '' Icc (s : ℝ) (leftStop R L r η ψ q ω))
        (closedBall (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) ρ)) ∧
      ∃ x ε : ℝ, IsRefCollar (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω)
        (relChart c (travAll R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hT0 : 0 < leftStop R L r η ψ q ω :=
    hP.nonneg.trans_lt (lt_ambTime0 hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq')
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨-, -, hFrontier⟩ := current_landing hω hcfg hψ hc hdom heq hq ξ
  obtain ⟨a, ha0, -, haT, hAway⟩ := exists_old_interval_excluding_current_frontier hcfg.trace.2.1 hP.isOpen hCH
    le_rfl hT0 hFrontier hNotTip
  obtain ⟨s₁, has₁, hs₁T, ρ, hρ, hTail₁⟩ := exists_rat_terminal_trace_avoids hcfg.trace.2.1 ha0 haT hNotTip
  obtain ⟨s, hs₁s, hsT, hsv⟩ :=
    exists_rat_visit_lt_ambTime0 hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq' hs₁T
  have hs0 : 0 ≤ (s : ℝ) := ha0.trans (has₁.le.trans hs₁s.le)
  replace hsT : (s : ℝ) < leftStop R L r η ψ q ω := hsT
  have hTail : Disjoint (η ω '' Icc (s : ℝ) (leftStop R L r η ψ q ω))
      (closedBall (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) ρ) :=
    hTail₁.mono_left (image_mono (Icc_subset_Icc_left hs₁s.le))
  have hQ := visitCap_le_of_lt_leftStop hcfg hψ hq hsv hsT
  obtain ⟨-, hOld, hOldDom⟩ := visit_chart hω hcfg hψ hc hdom heq hs0 hsv.2
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hNowDom := current_dom_eq hω hcfg hψ hc hdom heq hq
  have hBoundary : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom := fun h =>
    hAway s (has₁.trans hs₁s) (by rw [← hOldDom]; exact h)
  obtain ⟨x, hTransition, hOldLanding⟩ :=
    exists_old_access hω hcfg hψ hc hdom heq hq hs0 hsT.le hsv.2 hBoundary hNotExit
  have hIncident := old_access_mem_closure_of_current_transition hNow hTransition
  rw [hNowDom] at hIncident
  obtain ⟨ε, hε, -, hCur, -⟩ := exists_old_trace_halfDisc_in_current_domain hcfg.trace.2.1 hs0 hsT.le hOld
    hOldDom hOldLanding hIncident hρ hTail
  rw [← hNowDom] at hCur
  have hIncl : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆
      (relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω s).toNNReal ω).dom := by
    rw [hNowDom, hOldDom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono (image_mono (Icc_subset_Icc_right hsT.le)) h)⟩
  have hCollar := halfDisc_subset_transition_of_inverse_image hOld hNow hIncl hCur
  have hne : η ω s ≠ extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ := fun h =>
    disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hsT.le⟩, rfl⟩ (h ▸ mem_closedBall_self hρ.le)
  exact ⟨s, hs0, hsv.2, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hε, hCur, hTransition,
    tendsto_old_inverse_within_current_of_halfDisc hOldLanding hε hCur,
    disjoint_currentPocketContacts_of_halfDisc hOld hNow hIncl hCollar, hCollar⟩

/-- **The exceptional points of the exposed landings on the walls** (bounded change pocket): the two first-visit
attachments at the left stop and `0`. -/
def outerExc (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  {cfArcR (R ω) (L ω) r (firstVisit (fun t => η ω '' Icc 0 t) (cfArcR (R ω) (L ω) r) (leftStop R L r η ψ q ω)),
    cfArcL (R ω) (L ω) r (firstVisit (fun t => η ω '' Icc 0 t) (cfArcL (R ω) (L ω) r) (leftStop R L r η ψ q ω)), 0}

theorem outerExc_finite (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) :
    (outerExc R L r η ψ q ω).Finite :=
  ((Set.finite_singleton _).insert _).insert _

/-- At capacity `0` the open exposed interval of a word with seeds at `0` is empty. -/
theorem notMem_seed_interval_zero {γ : Ω → ℝ → ℂ} (hγ : IsDrivenCurve (γ ω))
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0)
    (ξ : ℝ) : ξ ∉ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 0 ω - segDriver (γ ω) 0)
      (geomRW (fun t ω => segDriver (γ ω) t) xR 0 0 ω - segDriver (γ ω) 0) := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ ω) := by
    rw [ENNReal.coe_zero]
    exact PocketPhaseMeans.capLife_pos hγ
  obtain ⟨V, hV, hV0, q', hqq', hEq, -⟩ := exists_relChart_eq_loewner (c := fun _ => (default : Chart)) hγ h0
  have hEqq : EqOn (fun u : ℝ => (fun t ω => segDriver (γ ω) t) u.toNNReal ω) V (Icc 0 ((0 : ℝ≥0) : ℝ)) :=
    fun u hu => hEq u ⟨hu.1, hu.2.trans hqq'.le⟩
  obtain ⟨hL, hR⟩ := geom_positions_eq_of_driver_eqOn (fun t ω => segDriver (γ ω) t) xL xR hV hEqq
  have h1 := congrFun hL 0
  have h2 := congrFun hR 0
  have hnV : (fun u => -V u) 0 = 0 := by simp only [hV0, neg_zero]
  rw [hxL, neg_zero, NNReal.coe_zero, rightImg_seed_zero_time hnV, hV0] at h1
  rw [hxR, NNReal.coe_zero, rightImg_seed_zero_time hV0, hV0] at h2
  rw [h1, h2]
  simp

/-- **The pathwise geometry of an exposed landing on the wall** (bounded change pocket, seeds at `0`): at a live
capacity, a current coordinate in the open exposed interval whose landing `p` lies outside the pocket, off
`refExc ∪ outerExc`, has a rational interior-visit reference `i` with its pair event and an unfilled collar, `p` in its
hull `K_s`, the current approach eventually in a component of `(ℍ ∖ K_s) ∩ B(p, ρ)` missing the pocket exterior, and an
ambient image `x′` off the ambient jumps reached by `f_s` along the current and the old approach. -/
theorem exists_outer_cover {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfig (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hζ : ζ' ω = ⊤) {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL' i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) t)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω)
    (hO : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ outerExc R L r η ψ q ω)
    (hS : exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ) :
    ∃ (i : ℕ) (x ε x' ρ : ℝ),
      ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧ 0 < ρ ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
        freeNear (R5Same.pocketExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) ω) (refHull W' ζ' i ω)
          (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) ρ) ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChart c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  set p := extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ with hpdef
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨hP, hψ'⟩ := pocket_of_cfg (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, hpcl, -⟩ :=
    current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq ξ
  have hexp : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAll R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q) :=
    not_not.1 hS.1
  have hpC : p ∉ cfPocket (R ω) (L ω) r := hS.2
  -- positive capacity
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · have h0 := notMem_seed_interval_zero (γ := travAll R L r η ψ) (ω := ω) hγ hxL hxR ξ
      rw [h] at h0
      exact absurd hexp h0
    · exact h
  -- the landing is a wall point of `ℍ`
  have hpF : p ∈ frontier (cfPocket (R ω) (L ω) r) := by
    rw [hP.isOpen.frontier_eq]
    exact ⟨hpcl, hpC⟩
  simp only [outerExc, mem_insert_iff, mem_singleton_iff, not_or] at hO
  obtain ⟨hA₁, hA₂, hp0⟩ := hO
  have hpH : p ∈ H := by
    have hpF' := hpF
    rw [hP.frontier_eq] at hpF'
    rcases hpF' with ⟨v, hv, hpv⟩ | ⟨v, hv, hpv⟩
    · rcases hv.2.lt_or_eq with hlt | h1
      · exact hpv ▸ hP.mem_H₁ v ⟨hv.1, hlt⟩
      · subst h1
        rcases hP.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
    · rcases hv.2.lt_or_eq with hlt | h1
      · exact hpv ▸ hP.mem_H₂ v ⟨hv.1, hlt⟩
      · subst h1
        rw [hP.seed] at hpv
        rcases hP.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
  -- the landing is on the trace before the left stop, and near it the walls are visited
  have hR := mem_range_of_seed_interval_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq
    hcExt hq0 hq hxL hxR hexp hpH
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (trav (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hτT : firstHit (η ω) (cfArcR (R ω) (L ω) r 1) ≤ leftStop R L r η ψ q ω :=
    (lt_ambTime0 hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq').le
  obtain ⟨r₁, hr₁, hball₁⟩ := exists_ball_frontier_subset_range hP hτT hR hA₁ hA₂
  -- the reference
  simp only [refExc, mem_insert_iff, mem_singleton_iff, not_or] at hX
  obtain ⟨s, hs0, hv, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hcol⟩ :=
    exists_visit_collar_tail (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX.1 hX.2
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCap R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ p := by rw [hti]; exact hne
  have htT : (t : ℝ) ≤ leftStop R L r η ψ q ω := by rw [hti]; exact hsT.le
  have hcol' : IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ p x ε := by
    simp only [refChart, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨hOld0, hIncl0, -⟩ :=
    reference_chart_at_visit (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hv' hHull hq hQ'
  have hOld : (refChart c R L r η ψ i ω).IsConformal := hOld0
  have hIncl : ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChart c R L r η ψ i ω).dom := hIncl0
  obtain ⟨-, -, hOldDom⟩ :=
    visit_chart (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hfill := hcfg.trace.2.2 t t.coe_nonneg
  have hOldDom' : ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆ H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    change ((relChart c (travAll R L r η ψ) (visitCap R L r η ψ ω t).toNNReal ω).dom : Set ℂ) ⊆ _
    rw [hOldDom, hfill]
    exact fun z hz => hz.2
  -- the trace near `p` is before `t`, so the walls near `p` and `p` itself are in the hull `K_t`
  have hnear : ∀ z ∈ η ω '' Icc 0 (leftStop R L r η ψ q ω), z ∈ closedBall p ρ → z ∈ η ω '' Icc 0 (t : ℝ) := by
    rintro z ⟨u, hu, rfl⟩ hzb
    by_cases hut : u ≤ t
    · exact ⟨u, ⟨hu.1, hut⟩, rfl⟩
    · exact absurd hzb (Set.disjoint_left.1 hTail ⟨u, ⟨by rw [← hti]; exact (not_le.1 hut).le, hu.2⟩, rfl⟩)
  have hmemK : ∀ z, z ∈ H → z ∈ η ω '' Icc 0 (t : ℝ) → z ∈ fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    fun z hz hzR => by
      rw [hfill]
      exact ⟨hz, Or.inl (subset_closure hzR)⟩
  have hpK : p ∈ fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    hmemK p hpH (hnear p hR (mem_closedBall_self hρ.le))
  -- the approach stays in a component missing the pocket exterior
  have hρ' : 0 < min r₁ ρ := lt_min hr₁ hρ
  have hfrK : frontier (cfPocket (R ω) (L ω) r) ∩ ball p (min r₁ ρ) ∩ H ⊆ refHull W' ζ' i ω := by
    rintro z ⟨⟨hzF, hzb⟩, hzH⟩
    rw [hHull]
    exact hmemK z hzH (hnear z (hball₁ ⟨hzF, ball_subset_ball (min_le_left _ _) hzb⟩)
      (ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hzb)))
  have hE : ∀ z ∈ cfPocket (R ω) (L ω) r,
      z ∉ R5Same.pocketExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) ω := by
    intro z hz hzE
    have h1 := H_diff_liveExt_zero (γ := travAll R L r η ψ) (C := fun ω => cfPocket (R ω) (L ω) r)
      (F := fun _ => ∅) hω hγ
    have h2 : z ∈ H \ liveExt A (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 ω := by
      rw [h1]
      exact ⟨hz, hCH hz, Set.notMem_empty z⟩
    exact h2.2 hzE
  have hNowDom := current_dom_eq (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq
  have hfC : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAll R L r η ψ) q ω).2.1 y ∈
      H ∩ (cfPocket (R ω) (L ω) r \ refHull W' ζ' i ω) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 : (relChart c (travAll R L r η ψ) q ω).2.1 y ∈ ((relChart c (travAll R L r η ψ) q ω).dom : Set ℂ) :=
      hNow.inv_mem_dom hy
    rw [hNowDom] at h1
    refine ⟨h1.2.1, h1.1, fun hK => h1.2.2 ?_⟩
    rw [hHull, hfill] at hK
    exact fillH_mono (image_mono (Icc_subset_Icc_right htT)) hK
  have hfree := eventually_mem_freeNear hP.isOpen hE hfrK hLanding hfC hρ'
  -- the ambient image
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChart c R L r η ψ i ω).1 ((relChart c (travAll R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChart c R L r η ψ i ω).2.1 ((refChart c R L r η ψ i ω).1
      ((relChart c (travAll R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAll R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL' xR'
    hx'p hpH (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL' j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', min r₁ ρ, ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', by rw [hHull]; exact hpK,
    hLanding, hρ', hfree, ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump

end Bounded

end InteractingSLE.Sec7.R5Wall

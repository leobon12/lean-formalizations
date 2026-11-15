/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5WallOuterGeom

/-!
# R.5's exposed coordinates landing on the pocket wall: the pathwise geometry (pocket opening at the flow seed)

Packet PROVE-R5-WALL (second round; ruling R86a). The twin of `R5WallOuterGeom` for the change pocket opening at the
flow seed: walls `α_i : [0, ∞) → ℂ` from the common point `y₀` to `∞`, first visited from `y₀` outwards, the
attachments `α_i(u_i)` at the **last** visited parameters `u_i = max {v : α_i(v) ∈ η[0, T⁰]}`
(`exists_ball_frontier_subset_rangeInf`; the walls are proper, so only a compact piece of each meets a ball), and
`exists_outer_coverInf`, the selection of a reference, its hull at the landing, the `freeNear` approach and the
ambient image.

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

/-- **Off the attachments, the pocket frontier near a visited point is visited** (reverse pocket opening at the flow
seed): if `p` is on the trace up to `T ≥ τ` and is neither last-visit attachment at `T`, some ball about `p` meets
the frontier of `C` only in the trace up to `T`. -/
theorem exists_ball_frontier_subset_rangeInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ : ℝ → ℂ} {τ : ℝ}
    (hP : IsReversePocketInf W η C α₁ α₂ τ) {T : ℝ} (hτT : τ ≤ T) {p : ℂ} (hpR : p ∈ η '' Icc 0 T)
    (h₁ : p ≠ α₁ (lastVisit (fun t => η '' Icc 0 t) α₁ T))
    (h₂ : p ≠ α₂ (lastVisit (fun t => η '' Icc 0 t) α₂ T)) :
    ∃ r > 0, frontier C ∩ ball p r ⊆ η '' Icc 0 T := by
  have hyR : α₁ 0 ∈ η '' Icc 0 T := ⟨τ, ⟨hP.nonneg, hτT⟩, hP.first_y⟩
  have hRb : Bornology.IsBounded (η '' Icc 0 T) :=
    (isCompact_Icc.image_of_continuousOn (hP.trace.2.1.mono fun t ht => ht.1)).isBounded
  obtain ⟨M, hM⟩ := hRb.exists_norm_le
  have key : ∀ (α : ℝ → ℂ), ContinuousOn α (Ici 0) → Tendsto (fun v => ‖α v‖) atTop atTop →
      IsReverseVisitOrderInf α (fun t => η '' Icc 0 t) → α 0 ∈ η '' Icc 0 T →
      p ≠ α (lastVisit (fun t => η '' Icc 0 t) α T) →
      ∃ Vp : ℝ, IsCompact (α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp) ∧
        p ∉ α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp ∧
        ∀ w ∈ Ici (0 : ℝ), ‖α w‖ < ‖p‖ + 1 →
          α w ∉ α '' Icc (lastVisit (fun t => η '' Icc 0 t) α T) Vp → α w ∈ η '' Icc 0 T := by
    intro α hαc hαt hrev h0 hp
    set V := {v ∈ Ici (0 : ℝ) | α v ∈ η '' Icc 0 T} with hV
    have h0V : (0 : ℝ) ∈ V := ⟨show (0 : ℝ) ≤ 0 from le_rfl, h0⟩
    have hne : V.Nonempty := ⟨0, h0V⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hαt.eventually_gt_atTop M)
    have hbdd : BddAbove V := ⟨N, fun v hv => by
      by_contra hlt
      exact absurd (hM _ hv.2) (not_le.2 (hN v (not_le.1 hlt).le))⟩
    have hu0 : 0 ≤ sSup V := le_csSup hbdd h0V
    obtain ⟨N', hN'⟩ := eventually_atTop.1 (hαt.eventually_gt_atTop (‖p‖ + 1))
    have hlv : lastVisit (fun t => η '' Icc 0 t) α T = sSup V := rfl
    rw [hlv] at hp ⊢
    refine ⟨max (sSup V) N', isCompact_Icc.image_of_continuousOn (hαc.mono fun v hv => hu0.trans hv.1), ?_, ?_⟩
    · rintro ⟨w, hw, hpw⟩
      have hwV : w ∈ V := ⟨hu0.trans hw.1, hpw ▸ hpR⟩
      have hwu : w = sSup V := le_antisymm (le_csSup hbdd hwV) hw.1
      exact hp (by rw [← hpw, hwu])
    · intro w hw hwn hnot
      have hwN : w < N' := by
        by_contra hle
        exact absurd hwn (not_lt.2 (hN' w (not_lt.1 hle)).le)
      have hlt : w < sSup V := by
        by_contra hle
        exact hnot ⟨w, ⟨not_lt.1 hle, hwN.le.trans (le_max_right _ _)⟩, rfl⟩
      obtain ⟨v₀, hv₀, hwv₀⟩ := exists_lt_of_lt_csSup hne hlt
      exact hrev T w hw v₀ hv₀.1 hwv₀.le hv₀.2
  obtain ⟨V₁, hK₁, hp₁, hv₁⟩ := key α₁ hP.cont₁ hP.tendsto₁ hP.rev₁ hyR h₁
  obtain ⟨V₂, hK₂, hp₂, hv₂⟩ := key α₂ hP.cont₂ hP.tendsto₂ hP.rev₂ (hP.seed ▸ hyR) h₂
  have hKc : IsClosed ((α₁ '' Icc (lastVisit (fun t => η '' Icc 0 t) α₁ T) V₁) ∪
      α₂ '' Icc (lastVisit (fun t => η '' Icc 0 t) α₂ T) V₂) := (hK₁.union hK₂).isClosed
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.1 hKc.isOpen_compl p (by
    rintro (h | h)
    · exact hp₁ h
    · exact hp₂ h)
  refine ⟨min r₀ 1, lt_min hr₀ one_pos, fun z ⟨hzF, hzb⟩ => ?_⟩
  have hzK := hball (ball_subset_ball (min_le_left _ _) hzb)
  have hzn : ‖z‖ < ‖p‖ + 1 := by
    have h1 : dist z p < 1 := lt_of_lt_of_le hzb (min_le_right _ _)
    have h2 := norm_le_norm_add_norm_sub' z p
    rw [dist_eq_norm] at h1
    linarith [norm_sub_rev z p]
  rw [hP.frontier_eq] at hzF
  rcases hzF with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩
  · exact hv₁ w hw hzn fun h => hzK (Or.inl h)
  · exact hv₂ w hw hzn fun h => hzK (Or.inr h)

section Inf

variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : Ω → ℝ → ℝ} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

/-- **An exposed coordinate landing in `ℍ` outside the pocket lands on the trace before the left stop** (pocket
opening at
the flow seed, seeds at `0`): its landing is in the current fill (R5-LIFT), and a fill point that is a limit of
current points is on the trace. -/
theorem mem_range_of_seed_interval_landingInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar) {q : ℝ≥0} (hq0 : 0 < q)
    (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
        segDriver (travAllInf R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q))
    (hpH : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ H) :
    extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ η ω '' Icc 0 (leftStopInf R L r η ψ q ω) := by
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨E, hE, hEc⟩ := hcExt
  have hland := (current_landingInf hω hcfg hψ hc hdom heq hq ξ).1
  have hdomEq := current_dom_eqInf hω hcfg hψ hc hdom heq hq
  have hRc : IsCompact (η ω '' Icc 0 (leftStopInf R L r η ψ q ω)) :=
    isCompact_Icc.image_of_continuousOn (hcfg.trace.2.1.mono fun t ht => ht.1)
  have hKo := isOpen_H_diff_fillH hRc.isBounded
  have hK := R5Lift.landing_mem_hull_of_mem_seed_interval (iL := 0) (iR := 0) hxL hxR hc hγ hq hq0 hE hEc hdom hKo
    hdomEq hξ hland hpH
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hcl : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈
      closure (H \ fillH (η ω '' Icc 0 (leftStopInf R L r η ψ q ω))) := by
    have := R5Lift.nhdsWithin_H_neBot ξ
    refine mem_closure_of_tendsto hland (eventually_nhdsWithin_of_forall fun y hy => ?_)
    have h1 : (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
        ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) := hNow.inv_mem_dom hy
    rw [hdomEq] at h1
    exact h1.2
  exact ReverseArc.mem_of_mem_fillH_of_mem_closure hRc.isClosed hK hcl

/-- **Lemma R.5's unfilled visit collar with its tail-avoidance ball** (pocket opening at the flow seed): R5-REFCHART's
`exists_visit_collar`, keeping the ball about the landing that the trace avoids after the selected visit. -/
theorem exists_visit_collar_tailInf (hω : ω ∈ A) (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (W ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hNotTip : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ≠ η ω (leftStopInf R L r η ψ q ω)) :
    ∃ s : ℚ, 0 ≤ (s : ℝ) ∧ η ω s ∈ cfPocket (R ω) (L ω) r ∧ (visitCapInf R L r η ψ ω s).toNNReal ≤ q ∧
      η ω s ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∧ (s : ℝ) < leftStopInf R L r η ψ q ω ∧
      (∃ ρ > 0, Disjoint (η ω '' Icc (s : ℝ) (leftStopInf R L r η ψ q ω))
        (closedBall (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) ρ)) ∧
      ∃ x ε : ℝ, IsRefCollar (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω)
        (relChart c (travAllInf R L r η ψ) q ω) ξ (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε := by
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf hcfg hψ
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hγ := (hcfg.isDrivenCurve hψ).1
  have hT0 : 0 < leftStopInf R L r η ψ q ω :=
    hP.nonneg.trans_lt (lt_ambTime0Inf hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq')
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨-, -, hFrontier⟩ := current_landingInf hω hcfg hψ hc hdom heq hq ξ
  obtain ⟨a, ha0, -, haT, hAway⟩ := exists_old_interval_excluding_current_frontier hcfg.trace.2.1 hP.isOpen hCH
    le_rfl hT0 hFrontier hNotTip
  obtain ⟨s₁, has₁, hs₁T, ρ, hρ, hTail₁⟩ := exists_rat_terminal_trace_avoids hcfg.trace.2.1 ha0 haT hNotTip
  obtain ⟨s, hs₁s, hsT, hsv⟩ :=
    exists_rat_visitInf_lt_ambTime0Inf hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq' hs₁T
  have hs0 : 0 ≤ (s : ℝ) := ha0.trans (has₁.le.trans hs₁s.le)
  replace hsT : (s : ℝ) < leftStopInf R L r η ψ q ω := hsT
  have hTail : Disjoint (η ω '' Icc (s : ℝ) (leftStopInf R L r η ψ q ω))
      (closedBall (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) ρ) :=
    hTail₁.mono_left (image_mono (Icc_subset_Icc_left hs₁s.le))
  have hQ := visitCapInf_le_of_lt_leftStopInf hcfg hψ hq hsv hsT
  obtain ⟨-, hOld, hOldDom⟩ := visit_chartInf hω hcfg hψ hc hdom heq hs0 hsv.2
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hNowDom := current_dom_eqInf hω hcfg hψ hc hdom heq hq
  have hBoundary : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom := fun h =>
    hAway s (has₁.trans hs₁s) (by rw [← hOldDom]; exact h)
  obtain ⟨x, hTransition, hOldLanding⟩ :=
    exists_old_accessInf hω hcfg hψ hc hdom heq hq hs0 hsT.le hsv.2 hBoundary
  have hIncident := old_access_mem_closure_of_current_transition hNow hTransition
  rw [hNowDom] at hIncident
  obtain ⟨ε, hε, -, hCur, -⟩ := exists_old_trace_halfDisc_in_current_domain hcfg.trace.2.1 hs0 hsT.le hOld
    hOldDom hOldLanding hIncident hρ hTail
  rw [← hNowDom] at hCur
  have hIncl : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆
      (relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω s).toNNReal ω).dom := by
    rw [hNowDom, hOldDom]
    exact fun z hz => ⟨hz.1, hz.2.1, fun h => hz.2.2 (fillH_mono (image_mono (Icc_subset_Icc_right hsT.le)) h)⟩
  have hCollar := halfDisc_subset_transition_of_inverse_image hOld hNow hIncl hCur
  have hne : η ω s ≠ extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ := fun h =>
    disjoint_left.1 hTail ⟨(s : ℝ), ⟨le_rfl, hsT.le⟩, rfl⟩ (h ▸ mem_closedBall_self hρ.le)
  exact ⟨s, hs0, hsv.2, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hε, hCur, hTransition,
    tendsto_old_inverse_within_current_of_halfDisc hOldLanding hε hCur,
    disjoint_currentPocketContacts_of_halfDisc hOld hNow hIncl hCollar, hCollar⟩

/-- **The exceptional points of the exposed landings on the walls** (pocket opening at the flow seed): the two
first-visit
attachments at the left stop and `0`. -/
def outerExcInf (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : Set ℂ :=
  {cfArcRInf (R ω) (L ω) r (lastVisit (fun t => η ω '' Icc 0 t) (cfArcRInf (R ω) (L ω) r) (leftStopInf R L r η ψ q ω)),
    cfArcLInf (R ω) (L ω) r (lastVisit (fun t => η ω '' Icc 0 t) (cfArcLInf (R ω) (L ω) r)
      (leftStopInf R L r η ψ q ω)), 0}

theorem outerExcInf_finite (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) :
    (outerExcInf R L r η ψ q ω).Finite :=
  ((Set.finite_singleton _).insert _).insert _

/-- **The pathwise geometry of an exposed landing on the wall** (pocket opening at the flow seed, seeds at `0`): at a
live
capacity, a current coordinate in the open exposed interval whose landing `p` lies outside the pocket, off
`refExcInf ∪ outerExc`, has a rational interior-visit reference `i` with its pair event and an unfilled collar, `p` in
its
hull `K_s`, the current approach eventually in a component of `(ℍ ∖ K_s) ∩ B(p, ρ)` missing the pocket exterior, and an
ambient image `x′` off the ambient jumps reached by `f_s` along the current and the old approach. -/
theorem exists_outer_coverInf {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hω : ω ∈ A)
    (hcfg : IsCfPocketConfigInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hcExt : ∃ E : ℂ → ℂ, EqOn E (c ω).2.1 H ∧ ContinuousOn E Hbar)
    (hζ : ζ' ω = ⊤) {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL' i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) t)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω)
    (hO : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ outerExcInf R L r η ψ q ω)
    (hS : exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ) :
    ∃ (i : ℕ) (x ε x' ρ : ℝ),
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧ 0 < ρ ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
        freeNear (R5Same.pocketExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) ω) (refHull W' ζ' i ω)
          (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) ρ) ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChartInf c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  set p := extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ with hpdef
  have hγ := (hcfg.isDrivenCurve hψ).1
  obtain ⟨hP, hψ'⟩ := pocket_of_cfgInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, hpcl, -⟩ :=
    current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq ξ
  have hexp : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q) :=
    not_not.1 hS.1
  have hpC : p ∉ cfPocket (R ω) (L ω) r := hS.2
  -- positive capacity
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · have h0 := notMem_seed_interval_zero (γ := travAllInf R L r η ψ) (ω := ω) hγ hxL hxR ξ
      rw [h] at h0
      exact absurd hexp h0
    · exact h
  -- the landing is a wall point of `ℍ`
  have hpF : p ∈ frontier (cfPocket (R ω) (L ω) r) := by
    rw [hP.isOpen.frontier_eq]
    exact ⟨hpcl, hpC⟩
  simp only [outerExcInf, mem_insert_iff, mem_singleton_iff, not_or] at hO
  obtain ⟨hA₁, hA₂, hp0⟩ := hO
  have hpH : p ∈ H := by
    have hpF' := hpF
    rw [hP.frontier_eq] at hpF'
    rcases hpF' with ⟨v, hv, hpv⟩ | ⟨v, hv, hpv⟩
    · rcases (show (0 : ℝ) ≤ v from hv).lt_or_eq with hlt | h0
      · exact hpv ▸ hP.mem_H₁ v hlt
      · subst h0
        rcases hP.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
    · rcases (show (0 : ℝ) ≤ v from hv).lt_or_eq with hlt | h0
      · exact hpv ▸ hP.mem_H₂ v hlt
      · subst h0
        rw [hP.seed] at hpv
        rcases hP.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
  -- the landing is on the trace before the left stop, and near it the walls are visited
  have hR := mem_range_of_seed_interval_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq
    hcExt hq0 hq hxL hxR hexp hpH
  have hq' : ENNReal.ofReal (q : ℝ) < capLife (travInf (η ω) (cfPocket (R ω) (L ω) r)
      (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0)) (ψ ω)) := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact hq
  have hτT : firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0) ≤ leftStopInf R L r η ψ q ω :=
    (lt_ambTime0Inf hP hcfg.attach hψ' (NNReal.coe_pos.2 hq0) hq').le
  obtain ⟨r₁, hr₁, hball₁⟩ := exists_ball_frontier_subset_rangeInf hP hτT hR hA₁ hA₂
  -- the reference
  simp only [refExcInf, mem_singleton_iff] at hX
  obtain ⟨s, hs0, hv, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hcol⟩ :=
    exists_visit_collar_tailInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCapInf R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ p := by rw [hti]; exact hne
  have htT : (t : ℝ) ≤ leftStopInf R L r η ψ q ω := by rw [hti]; exact hsT.le
  have hcol' : IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ p x ε := by
    simp only [refChartInf, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨hOld0, hIncl0, -⟩ :=
    reference_chart_at_visitInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hv' hHull hq hQ'
  have hOld : (refChartInf c R L r η ψ i ω).IsConformal := hOld0
  have hIncl : ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) ⊆ (refChartInf c R L r η ψ i ω).dom := hIncl0
  obtain ⟨-, -, hOldDom⟩ :=
    visit_chartInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hfill := hcfg.trace.2.2 t t.coe_nonneg
  have hOldDom' : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆ H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t := by
    change ((relChart c (travAllInf R L r η ψ) (visitCapInf R L r η ψ ω t).toNNReal ω).dom : Set ℂ) ⊆ _
    rw [hOldDom, hfill]
    exact fun z hz => hz.2
  -- the trace near `p` is before `t`, so the walls near `p` and `p` itself are in the hull `K_t`
  have hnear : ∀ z ∈ η ω '' Icc 0 (leftStopInf R L r η ψ q ω), z ∈ closedBall p ρ → z ∈ η ω '' Icc 0 (t : ℝ) := by
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
      z ∉ R5Same.pocketExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) ω := by
    intro z hz hzE
    have h1 := H_diff_liveExt_zero (γ := travAllInf R L r η ψ) (C := fun ω => cfPocket (R ω) (L ω) r)
      (F := fun _ => ∅) hω hγ
    have h2 : z ∈ H \ liveExt A (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) (fun _ => ∅) 0 ω := by
      rw [h1]
      exact ⟨hz, hCH hz, Set.notMem_empty z⟩
    exact h2.2 hzE
  have hNowDom := current_dom_eqInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq
  have hfC : ∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈
      H ∩ (cfPocket (R ω) (L ω) r \ refHull W' ζ' i ω) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    have h1 : (relChart c (travAllInf R L r η ψ) q ω).2.1 y ∈ ((relChart c (travAllInf R L r η ψ) q ω).dom : Set ℂ) :=
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
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChartInf c R L r η ψ i ω).1 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChartInf c R L r η ψ i ω).2.1 ((refChartInf c R L r η ψ i ω).1
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)
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

end Inf

end InteractingSLE.Sec7.R5Wall

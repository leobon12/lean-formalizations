/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJw
import InteractingSLE.Spec.Supplement.SB2WfSwal

/-!
# The junction invariant through a launch

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). Let the walk launch a piece with a finite positive stop
`τ`, driver `W` and trace `γ` (continuous on `[0, τ]`) from a state `s` with the junction invariant. A junction `r₁`
of the new chart (old lower-side height on its right) with real read-back `p` is handled as follows (`jw_launch`):

* `r₁ ≥ 0`: by the right-ray hypothesis `hRay` (there the chart is the untouched right ray);
* `r₁ < 0`: the new boundary map is `g ∘ G` with `G` the boundary map of the piece's inverse Loewner map
  (`bdry_comp_loewner`), and `z = G r₁` is real (the old inverse maps `ℍ` into `ℍ`). By `bdry_cases`:
  * `z` alive: `r₁ = f(z)`, the old word right of `z` is the new word right of `r₁` (`stopWord_fn_fwdMap`), `z` is right
    of the old left-ray image (`LLeft.exists_eq`, `lt_stRecL_launch_of_alive`), and the old invariant applies;
  * `z` a real trace point: the base (`hB`), a right touch before the stop (`hR`), the landing (excluded:
    `eq_zero_of_extendFrom_eq_tip` would give `r₁ = 0`; freshness by `trace_end_ne_of_mem_closure_fill`), or a left
    touch (`hL`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdMapInv fwdHull IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- **The boundary map of a Loewner chart** is the old boundary map after the boundary map of the inverse. -/
theorem bdry_comp_loewner {c : Chart} {g g₁ : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T)
    (hB : HasBdryLimits (fwdMapInv W T)) (hg₁c : ContinuousOn g₁ {z | 0 ≤ z.im})
    (hg₁i : EqOn g₁ (c.loewner W T).2.1 H) :
    (∀ w ∈ Hbar, extendFrom H (fwdMapInv W T) w ∈ Hbar) ∧
      EqOn g₁ (fun w => g (extendFrom H (fwdMapInv W T) w)) {z | 0 ≤ z.im} := by
  set G := extendFrom H (fwdMapInv W T) with hG
  have hGc : ContinuousOn G Hbar := hB.continuousOn
  have hGH : ∀ w ∈ H, G w = fwdMapInv W T w := fun w hw => ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hT.le hw
  have hmaps : ∀ w ∈ Hbar, G w ∈ Hbar := by
    intro w hw
    have hcl : w ∈ closure H := by rwa [closure_H]
    have hHsub : H ⊆ Hbar := fun v (hv : v ∈ H) => show v ∈ Hbar from (show (0 : ℝ) < v.im from hv).le
    have h1 : G w ∈ closure (G '' H) := ((hGc w hw).mono hHsub).mem_closure_image hcl
    have h2 : G '' H ⊆ Hbar := by
      rintro _ ⟨v, hv, rfl⟩
      rw [hGH v hv]
      exact (show (0 : ℝ) < (fwdMapInv W T v).im from QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT.le hv).le
    have h3 : IsClosed Hbar := isClosed_le continuous_const Complex.continuous_im
    exact closure_minimal h2 h3 h1
  refine ⟨hmaps, Vn.eqOn_closedH_of_eqOn_H hg₁c (hgc.comp hGc hmaps) fun w hw => ?_⟩
  rw [hg₁i hw]
  show c.2.1 (fwdMapInv W T w) = g (G w)
  rw [hGH w hw, hgi (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT.le hw)]

variable {κ θ ψ u : ℝ} {b : ℝ → ℝ}

/-- **The alive case of a launch**: a junction of the new chart whose old boundary value is an alive real point
`y₀` (`r₁ = f(y₀)`) transfers from the old invariant. -/
theorem jw_alive (hκ : 0 < κ) {β : BoundaryWord} {s : ExplState} (hc : IsRealChart (stChart s))
    (hs : LLeft s) (hI : JW κ θ ψ u b β s) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) {r₁ y₀ : ℝ} (hz0 : y₀ ≠ 0) {v : ℝ → ℂ}
    (hv : IsForwardSol (rdrv (recOf ⊤ D)) (y₀ : ℂ) (rtime (recOf ⊤ D)) v) (hvτ : v (rtime (recOf ⊤ D)) = r₁)
    (hr₁ : ∀ x, x < stRecL (ExplState.launch s k D θ ⊤) →
      rProf (stChart (ExplState.launch s k D θ ⊤)) x < r₁)
    (hlow₁ : ∃ ε > 0, ∀ y ∈ Ioo r₁ (r₁ + ε), y ∉ (stopWord κ (β, θ, recOf ⊤ D)).jumps →
      (stopWord κ (β, θ, recOf ⊤ D)).fn y = -sleLambda κ - θ * chiC κ)
    {p : ℝ} (hgz : g (y₀ : ℂ) = p) :
    stRecL (ExplState.launch s k D θ ⊤) ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)) := by
  classical
  set r := recOf ⊤ D with hr
  set W := rdrv r with hWdef
  set T := rtime r with hTdef
  set c := stChart s with hcdef
  set s₁ := ExplState.launch s k D θ ⊤ with hs₁
  set β₁ := stopWord κ (β, θ, r) with hβ₁
  have hW : Continuous W := continuous_rdrv r
  have hW0 : W 0 = 0 := rdrv_zero r
  have hT0 : 0 ≤ T := rtime_nonneg r
  obtain ⟨-, -, hrelL⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  have hL₁ : stRecL s₁ ≤ stRecL s := by
    by_contra hlt
    push Not at hlt
    have h1 := (hrelL ((stRecL s + stRecL s₁) / 2) (by linarith)).1
    linarith
  set f : ℝ → ℝ := fun y => (fwdMap W T y).re with hf
  have hA0 : ¬ ∃ v, IsForwardSol W ((0 : ℝ) : ℂ) T v := by
    have := (isRealFlow_fwd hW hW0 hT0).1.1
    simpa using this
  have hy₀A : ∃ v, IsForwardSol W (y₀ : ℂ) T v := ⟨v, hv⟩
  have hfy₀ : f y₀ = r₁ := by
    show (fwdMap W T (y₀ : ℂ)).re = r₁
    rw [InteractingSLE.fwdMap_eq_of_isForwardSol hW hv ⟨hT0, le_rfl⟩, hvτ]
    simp
  -- right of the old left-ray image
  have hright : ∀ x, x < stRecL s → rProf c x < y₀ := by
    intro x hx
    by_contra hle
    push Not at hle
    obtain ⟨x', hx', -, hx'e⟩ := LLeft.exists_eq hs hx hle
    have hal : ∃ u, IsForwardSol W (rProf c x' : ℂ) T u := by rw [hx'e]; exact hy₀A
    have hx'1 := lt_stRecL_launch_of_alive hc hs k θ hreg hgood hfin hx' hal
    have h1 := hr₁ x' hx'1
    rw [(hrelL x' hx'1).2.2, hx'e] at h1
    have h2 : f y₀ < r₁ := h1
    linarith
  -- the old lower side right of `y₀`
  have hlow : ∃ ε > 0, ∀ y ∈ Ioo y₀ (y₀ + ε), y ∉ β.jumps → β.fn y = -sleLambda κ - θ * chiC κ := by
    obtain ⟨ε, hε, hεl⟩ := hlow₁
    have hcl := Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hW hT0 hv
    obtain ⟨ρ₁, hρ₁, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hcl
    have hcont : ContinuousAt f y₀ := by
      have h1 := ZhanGT4.A1G3L2.continuousAt_fwdMap_of_isForwardSol (show T < T + 1 by linarith) hT0
        hW.continuousOn hv
      exact Complex.continuous_re.continuousAt.comp (h1.comp Complex.continuous_ofReal.continuousAt)
    obtain ⟨ρ₂, hρ₂, hρ₂f⟩ := Metric.continuousAt_iff.1 hcont ε hε
    set ρ := min (min ρ₁ ρ₂) |y₀| with hρ
    have hρ0 : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) (abs_pos.2 hz0)
    -- points near `y₀` are alive
    have hnear : ∀ y : ℝ, |y - y₀| < ρ → ∃ v, IsForwardSol W (y : ℂ) T v := by
      intro y hy
      have hy0 : y ≠ 0 := by
        intro h
        rw [h, zero_sub, abs_neg] at hy
        exact absurd hy (not_lt.2 (min_le_right _ _))
      refine Supp8.BHMean.exists_isForwardSol_of_notMem_closure hW hW0 hT0 (fun hmem => ?_) hy0
      refine hball ?_ hmem
      rw [Metric.mem_ball, Complex.dist_of_im_eq (by simp), Complex.ofReal_re, Complex.ofReal_re,
        Real.dist_eq]
      exact lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))
    have hmono := strictMonoOn_re_fwdMap_alive hW hW0 hT0
    -- the exceptional points
    set Ex : Set ℝ := {y | |y - y₀| < ρ ∧ f y ∈ (β₁.jumps : Set ℝ)} with hEx
    have hExf : Ex.Finite := by
      refine Set.Finite.of_finite_image (f := f) (β₁.jumps.finite_toSet.subset ?_) ?_
      · rintro _ ⟨y, hy, rfl⟩; exact hy.2
      · exact hmono.injOn.mono fun y hy => hnear y hy.1
    obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem hExf.toFinset y₀
    refine ⟨min δ ρ, lt_min hδ hρ0, fun y hy hyJ => ?_⟩
    have hyρ : |y - y₀| < ρ := by
      rw [abs_of_pos (by linarith [hy.1])]
      linarith [hy.2, min_le_right δ ρ]
    have hyA := hnear y hyρ
    have hyEx : y ∉ Ex := fun hm => (hδJ y (hExf.mem_toFinset.2 hm)).1
      ⟨hy.1, lt_of_lt_of_le hy.2 (by linarith [min_le_left δ ρ])⟩
    have hfyJ : f y ∉ β₁.jumps := fun h => hyEx ⟨hyρ, h⟩
    have hfy1 : r₁ < f y := by rw [← hfy₀]; exact hmono hy₀A hyA hy.1
    have hfy2 : f y < r₁ + ε := by
      have h1 : dist y y₀ < ρ₂ := by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hyρ ((min_le_left _ _).trans (min_le_right _ _))
      have h2 := hρ₂f h1
      rw [Real.dist_eq, hfy₀] at h2
      linarith [(abs_lt.1 h2).2]
    have hy0 : y ≠ 0 := fun h => hA0 (h ▸ hyA)
    have heq := hεl (f y) ⟨hfy1, hfy2⟩ hfyJ
    rcases lt_or_gt_of_ne hy0 with hneg | hpos
    · rw [hβ₁, stopWord_fn_fwdMap_neg hκ β θ r hneg hyA hyJ hfyJ] at heq
      exact heq
    · rw [hβ₁, stopWord_fn_fwdMap hκ β θ r hpos hyA hyJ hfyJ] at heq
      exact heq
  obtain ⟨hrec, hbad⟩ := hI g hgc hgi y₀ hright hlow p hgz
  exact ⟨hL₁.trans hrec, hbad⟩

/-- **The junction invariant through a launch** (finite positive stop), from the hypotheses on the right ray of the new
state and on the physical points of the real trace points of the piece. -/
theorem jw_launch (hκ : 0 < κ) {β : BoundaryWord} {s : ExplState} (hc : IsRealChart (stChart s))
    (hcc : (stChart s).IsConformal) (hs : LLeft s) (hI : JW κ θ ψ u b β s) {g : ℂ → ℂ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H) (k : ℕ)
    {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D) (hgood : LocalExt.IsDrvGood (recHist (recOf ⊤ D)))
    (hfin : D.2 ≠ ⊤) {γ : ℝ → ℂ}
    (hγ : IsLoewnerTraceLT (rdrv (recOf ⊤ D)) (rtime (recOf ⊤ D)) γ)
    (hγc : ContinuousOn γ (Icc 0 (rtime (recOf ⊤ D))))
    (hRay : ∀ g₁ : ℂ → ℂ, ContinuousOn g₁ {z | 0 ≤ z.im} →
      EqOn g₁ (stChart (ExplState.launch s k D θ ⊤)).2.1 H → ∀ r₁ : ℝ, 0 ≤ r₁ →
      (∃ ε > 0, ∀ y ∈ Ioo r₁ (r₁ + ε), y ∉ (stopWord κ (β, θ, recOf ⊤ D)).jumps →
        (stopWord κ (β, θ, recOf ⊤ D)).fn y = -sleLambda κ - θ * chiC κ) →
      ∀ p : ℝ, g₁ (r₁ : ℂ) = p → stRecL (ExplState.launch s k D θ ⊤) ≤ p ∧
        (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)))
    (hB : 0 < rtime (recOf ⊤ D) → ∀ p : ℝ, g 0 = p → stRecL (ExplState.launch s k D θ ⊤) ≤ p ∧
      (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)))
    (hR : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ D) → (γ t₀).im = 0 → 0 < (γ t₀).re → ∀ p : ℝ, g (γ t₀) = p →
      stRecL (ExplState.launch s k D θ ⊤) ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ)))
    (hL : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < rtime (recOf ⊤ D) → (γ t₀).im = 0 → (γ t₀).re < 0 → ∀ p : ℝ, g (γ t₀) = p →
      stRecL (ExplState.launch s k D θ ⊤) ≤ p ∧ (u < p → -2 < Sec4.cumWeightRight κ (rightLim b p + ψ * chiC κ))) :
    JW κ θ ψ u b (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  classical
  set r := recOf ⊤ D with hr
  set W := rdrv r with hWdef
  set T := rtime r with hTdef
  set c := stChart s with hcdef
  set s₁ := ExplState.launch s k D θ ⊤ with hs₁
  set β₁ := stopWord κ (β, θ, r) with hβ₁
  have hW : Continuous W := continuous_rdrv r
  have hW0 : W 0 = 0 := rdrv_zero r
  have hT0 : 0 ≤ T := rtime_nonneg r
  have hWe : W = stopDrv ⊤ D := by rw [hWdef, rdrv_recOf]; exact recDrv_eq_stopDrv hreg hgood
  have hTe : T = stopTime ⊤ D := rtime_recOf ⊤ D
  have hch : stChart s₁ = c.loewner W T := by
    rw [hWe, hTe]; exact (launch_eq_of_ne_top s k D θ ⊤ (min_top_ne_top hfin)).1
  obtain ⟨-, -, hrelL⟩ := lLeft_launch hc hs k θ hreg hgood hfin
  have hL₁ : stRecL s₁ ≤ stRecL s := by
    by_contra hlt
    push Not at hlt
    have h1 := (hrelL ((stRecL s + stRecL s₁) / 2) (by linarith)).1
    linarith
  set f : ℝ → ℝ := fun y => (fwdMap W T y).re with hf
  have hA0 : ¬ ∃ v, IsForwardSol W ((0 : ℝ) : ℂ) T v := by
    have := (isRealFlow_fwd hW hW0 hT0).1.1
    simpa using this
  intro g₁ hg₁c hg₁i r₁ hr₁ hlow₁ p hp
  by_cases h0 : 0 ≤ r₁
  · exact hRay g₁ hg₁c hg₁i r₁ h0 hlow₁ p hp
  push Not at h0
  rw [hch] at hg₁i
  rcases hT0.eq_or_lt with hTz | hτ
  · -- a zero stop: the chart and its boundary map do not change
    have hid : EqOn g₁ g {z | 0 ≤ z.im} := Vn.eqOn_closedH_of_eqOn_H hg₁c hgc fun w hw => by
      rw [hg₁i hw, hgi hw]
      show c.2.1 (fwdMapInv W T w) = c.2.1 w
      rw [← hTz, fwdMapInv_zero_time hW hW0 hw]
    have hpg : g (r₁ : ℂ) = p := by rw [← hid (show (0 : ℝ) ≤ ((r₁ : ℂ)).im by simp)]; exact hp
    have hr0 : ((r₁ : ℝ) : ℂ) ≠ (W 0 : ℂ) := by rw [hW0]; exact_mod_cast h0.ne
    obtain ⟨v, hv⟩ := (exists_isForwardSol_zero_iff (W := W)).2 hr0
    rw [hTz] at hv
    have hvτ : v T = r₁ := by
      have h1 := InteractingSLE.fwdMap_eq_of_isForwardSol hW hv ⟨hT0, le_rfl⟩
      rw [← hTz, fwdMap_zero_time hW0] at h1
      rw [← hTz]
      exact_mod_cast h1.symm
    exact jw_alive hκ hc hs hI hgc hgi k hreg hgood hfin h0.ne hv hvτ hr₁ hlow₁ hpg
  have hBd := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hγ hW hW0 hτ hγc
  obtain ⟨hmaps, hcomp⟩ := bdry_comp_loewner hgc hgi hW hW0 hτ hBd hg₁c hg₁i
  set G := extendFrom H (fwdMapInv W T) with hG
  set z := G (r₁ : ℂ) with hz
  have hzbar : z ∈ Hbar := hmaps _ (show (0 : ℝ) ≤ ((r₁ : ℂ)).im by simp)
  have hgz : g z = p := by
    rw [← hp]; exact (hcomp (show (0 : ℝ) ≤ ((r₁ : ℂ)).im by simp)).symm
  -- the old boundary value is real
  have hzim : z.im = 0 := by
    by_contra hne
    have hzH : z ∈ H := lt_of_le_of_ne hzbar (Ne.symm hne)
    have h1 : g z ∈ H := by rw [hgi hzH]; exact hcc.2.1 hzH
    rw [hgz] at h1
    have h2 : (0 : ℝ) < ((p : ℂ)).im := h1
    simp at h2
  have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hzim])
  rcases bdry_cases hW hW0 hτ hγ hγc hzim with ⟨hz0, v, hv, hvτ⟩ | ⟨t₀, ht₀, hγt₀⟩
  · exact jw_alive hκ hc hs hI hgc hgi k hreg hgood hfin hz0 hv hvτ hr₁ hlow₁ (by rw [← hzr]; exact hgz)
  · -- a real trace point
    have hgz' : g (γ t₀) = p := by rw [hγt₀]; exact hgz
    have hzim' : (γ t₀).im = 0 := by rw [hγt₀]; exact hzim
    clear hgz hzim
    by_cases hearly : ∃ t₁, 0 ≤ t₁ ∧ t₁ < T ∧ γ t₁ = γ t₀
    · obtain ⟨t₁, ht₁0, ht₁T, ht₁e⟩ := hearly
      rw [← ht₁e] at hgz' hzim'
      rcases lt_trichotomy (γ t₁).re 0 with hneg | hzero | hpos
      · exact hL t₁ ht₁0 ht₁T hzim' hneg p hgz'
      · have h0' : γ t₁ = 0 := Complex.ext (by simp [hzero]) (by simp [hzim'])
        rw [h0'] at hgz'
        exact hB hτ p hgz'
      · exact hR t₁ ht₁0 ht₁T hzim' hpos p hgz'
    · exfalso
      push Not at hearly
      have ht₀T : t₀ = T := by
        rcases ht₀.2.lt_or_eq with hlt | heq
        · exact absurd rfl (hearly t₀ ht₀.1 hlt)
        · exact heq
      subst ht₀T
      set q := (γ T).re with hq
      have hγq : γ T = (q : ℂ) := Complex.ext (by simp [hq]) (by simp [hzim'])
      have hq0 : q ≠ 0 := by
        intro h0q
        refine hearly 0 le_rfl hτ ?_
        rw [hγ.1, hγq, h0q, Complex.ofReal_zero]
      have hfresh : ∀ t, 0 ≤ t → t < T → (q : ℂ) ∉ closure (fwdHull W t) := by
        intro t ht htT hmem
        have hnotA : (q : ℂ) ∉ γ '' Icc 0 t := by
          rintro ⟨t₂, ht₂, he⟩
          exact hearly t₂ ht₂.1 (lt_of_le_of_lt ht₂.2 htT) (he.trans hγq.symm)
        have hK : fwdHull W t = fillH (γ '' Icc 0 t) := hγ.2.2 t ht htT
        rw [hK] at hmem
        exact trace_end_ne_of_mem_closure_fill hγc ht htT
          (fun T' _ hT'T => ⟨W, hW, hW0, Vo.isLoewnerTraceLT_mono hγ hT'T.le⟩) hnotA hmem hγq
      have hx : extendFrom H (fwdMapInv W T) (r₁ : ℂ) = γ T := hγt₀.symm
      have := eq_zero_of_extendFrom_eq_tip hW hW0 hτ hγ hγc hγq hq0 hfresh hx
      linarith

end InteractingSLE.Theorem14.SB.Wf

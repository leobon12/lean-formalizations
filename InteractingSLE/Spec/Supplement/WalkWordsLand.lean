/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsFiber
import InteractingSLE.Spec.Supplement.WalkIntBridgePrefix
import InteractingSLE.Spec.Sec7.PocketSideInReachLocal
import InteractingSLE.Spec.Sec7.Aux37SideReflect

/-!
# Incident-side identification of a chart landing on a fresh arc

Packet PROVE-WALK-WORDS (the prime-end access of Theorem 1.4's walk charts). Let `c` be a conformal chart whose
inverse lands, along the real points `x` near `x₀`, at points `Λ(x)` of a fresh arc `c₀⁻¹(η)` of a Loewner chart
`c₀` (`η` a trace simple up to `τ`, in `ℍ` on `[t, τ]`), with `Λ(x₀) = c₀⁻¹(η(t))`, and suppose that near `x₀` the
inverse of `c` maps into the domain of the prefix chart `c' = c₀.loewner W τ`. Then:

* `exists_transition_extension`: the transition `c'.fwd ∘ c.inv` extends from a half-disc at `x₀` to a map `m`,
  continuous up to the diameter, real there, conformal (`R16.IsRealBoundaryConformal`), with `F̄_τ ∘ m = c₀.fwd ∘ Λ`
  on the diameter (the cluster-set lemma `Sec7.PocketStopSide.exists_tendsto_of_tendsto_comp_local`; a trace point
  is not a value of `F̄_τ` on `ℍ`, so the limits are real);
* **`nonempty_sideIdentification_of_later`**: if `Λ` moves to **later** points of `η` right of `x₀`, then
  `m(x₀)` is the **left** side point (any negative preimage `y` of `η(t)`): `SideIdentification c c' x₀ y`;
* **`nonempty_sideIdentification_of_earlier`**: if `Λ` moves to **earlier** fresh points right of `x₀`, then
  `m(x₀)` is the **right** side point (any positive preimage).

## The side

`m(x₀)` is a real preimage of `η(t)` and `t ↦ m(t)` is strictly increasing (Schwarz reflection,
`Sec7.Aux37Side.strictMonoOn_re`). Later case: if `m(x₀) > 0`, a point `x > x₀` gives a positive preimage
`m(x) > m(x₀)` of a later point `η(s')`; the cut lemma at `s'` on `[0, m(x₀)]` (`WalkNorm.exists_eq_of_cut`) gives a
positive preimage of `η(s')` below `m(x₀)`, and the fibre lemma `eq_of_extendFrom_eq_of_same_side` identifies the two.
Earlier case: if `m(x₀) < 0`, by continuity `m(x) < 0` for `x > x₀` close to `x₀`, a negative preimage of an earlier
point `η(s')`; the cut lemma at `t` on `[m(x), 0]` gives a negative preimage of `η(t)` above `m(x) > m(x₀)`, against
the fibre lemma. The value `0` is the tip `η(τ)`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.WalkWords

section Land

variable {c c₀ : Chart} {W : ℝ → ℝ} {η : ℝ → ℂ} {τ x₀ : ℝ} {Λ : ℂ → ℂ}

/-- **The extended transition of a chart landing on a trace.** -/
theorem exists_transition_extension (hc : c.IsConformal) (hc₀ : c₀.IsConformal) (hη : IsLoewnerTrace W η)
    (hW : Continuous W) (hW0 : W 0 = 0) (hτ0 : 0 ≤ τ)
    (hland : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)))
    (htrace : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Icc 0 τ, η s ∈ H ∧ Λ x = c₀.2.1 (η s))
    (hdom : ∃ δ > 0, ∀ z ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 z ∈ (c₀.loewner W τ).2.1 '' H) :
    ∃ (δ : ℝ) (m : ℂ → ℂ), 0 < δ ∧ R16.IsRealBoundaryConformal m x₀ δ ∧
      (∀ z ∈ H ∩ ball (x₀ : ℂ) δ, m z ∈ H ∧ c.2.1 z = (c₀.loewner W τ).2.1 (m z)) ∧
      ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), (m x).im = 0 ∧ extendFrom H (fwdMapInv W τ) (m x) = c₀.1 (Λ x) := by
  classical
  set F : ℂ → ℂ := extendFrom H (fwdMapInv W τ) with hFdef
  set c' : Chart := c₀.loewner W τ with hc'def
  obtain ⟨hFd, hFc, hFi, hFR⟩ := hη.fiber_hyps hW hW0 hτ0
  have hc' : c'.IsConformal := hc₀.loewner hW hW0 hτ0
  obtain ⟨δ₁, hδ₁, hland'⟩ := hland
  obtain ⟨δ₂, hδ₂, htrace'⟩ := htrace
  obtain ⟨δ₃, hδ₃, hdom'⟩ := hdom
  set δ : ℝ := min δ₁ (min δ₂ δ₃) with hδdef
  have hδ : 0 < δ := lt_min hδ₁ (lt_min hδ₂ hδ₃)
  have hδ1 : δ ≤ δ₁ := min_le_left _ _
  have hδ2 : δ ≤ δ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ δ₃ := (min_le_right _ _).trans (min_le_right _ _)
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hIoo : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∀ δ', δ ≤ δ' → x ∈ Ioo (x₀ - δ') (x₀ + δ') := fun x hx δ' h =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  -- the transition on the half-disc
  set T : ℂ → ℂ := fun w => c'.1 (c.2.1 w) with hTdef
  have hT : ∀ w ∈ H ∩ ball (x₀ : ℂ) δ, T w ∈ H ∧ c'.2.1 (T w) = c.2.1 w := by
    intro w hw
    obtain ⟨w', hw', he⟩ := hdom' w ⟨hw.1, ball_subset_ball hδ3 hw.2⟩
    show c'.1 (c.2.1 w) ∈ H ∧ c'.2.1 (c'.1 (c.2.1 w)) = c.2.1 w
    rw [← he, hc'.2.2 w' hw']
    exact ⟨hw', rfl⟩
  have hTL : ∀ w ∈ H ∩ ball (x₀ : ℂ) δ, fwdMapInv W τ (T w) = c₀.1 (c.2.1 w) := by
    intro w hw
    obtain ⟨h1, h2⟩ := hT w hw
    have h3 : c₀.2.1 (fwdMapInv W τ (T w)) = c.2.1 w := h2
    have h4 := congrArg c₀.1 h3
    rw [hc₀.2.2 _ (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hτ0 h1)] at h4
    exact h4
  have hTmaps : MapsTo c.2.1 (H ∩ ball (x₀ : ℂ) δ) (c'.dom : Set ℂ) := fun w hw => by
    rw [hc'.coe_dom]
    obtain ⟨h3, h4⟩ := hT w hw
    exact ⟨_, h3, h4⟩
  have hTdiff : DifferentiableOn ℂ T (H ∩ ball (x₀ : ℂ) δ) :=
    hc'.differentiableOn_fwd.comp (hc.1.mono inter_subset_left) hTmaps
  have hTcont : ContinuousOn T (H ∩ ball (x₀ : ℂ) δ) := hTdiff.continuousOn
  have hOpen : IsOpen (H ∩ ball (x₀ : ℂ) δ) := QuantumZipper.isOpen_H.inter isOpen_ball
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hτ0
  -- the real limits
  have hlim : ∀ x : ℝ, x ∈ Ioo (x₀ - δ) (x₀ + δ) → ∃ ξ : ℂ, ξ.im = 0 ∧
      F ξ = c₀.1 (Λ x) ∧ Tendsto T (𝓝[H] (x : ℂ)) (𝓝 ξ) := by
    intro x hx
    have hxb : (x : ℂ) ∈ ball (x₀ : ℂ) δ := by
      rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hx.1, hx.2]
    set r : ℝ := δ - ‖(x : ℂ) - x₀‖ with hrdef
    have hr : 0 < r := by rw [mem_ball, dist_eq_norm] at hxb; rw [hrdef]; linarith
    have hballsub : ball (x : ℂ) r ⊆ ball (x₀ : ℂ) δ := by
      intro w hw
      rw [mem_ball, dist_eq_norm] at hw ⊢
      calc ‖w - x₀‖ ≤ ‖w - x‖ + ‖(x : ℂ) - x₀‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < δ := by rw [hrdef] at hw; linarith
    obtain ⟨s, hs, hsH, hse⟩ := htrace' x (hIoo x hx δ₂ hδ2)
    set v : ℂ := c₀.1 (Λ x) with hvdef
    have hv : v = η s := by rw [hvdef, hse, hc₀.2.2 _ hsH]
    have hcomp : Tendsto (fun w => F (T w)) (𝓝[H] (x : ℂ)) (𝓝 v) := by
      have hmemL : Λ x ∈ c₀.2.1 '' H := ⟨_, hsH, hse.symm⟩
      have hc₀c : ContinuousAt c₀.1 (Λ x) :=
        (hc₀.differentiableOn_fwd.differentiableAt (by
          rw [hc₀.coe_dom]; exact hc₀.isOpen_image.mem_nhds hmemL)).continuousAt
      have h3 := hc₀c.tendsto.comp (hland' x (hIoo x hx δ₁ hδ1))
      refine h3.congr' ?_
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr)] with w hwH hwb
      have hw : w ∈ H ∩ ball (x₀ : ℂ) δ := ⟨hwH, hballsub hwb⟩
      show c₀.1 (c.2.1 w) = F (T w)
      rw [hFdef, ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hτ0 (hT w hw).1, hTL w hw]
    have hbdd : ∀ᶠ w in 𝓝[H] (x : ℂ), ‖T w‖ ≤ ‖v‖ + 1 + C := by
      filter_upwards [hcomp.eventually (ball_mem_nhds v one_pos), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr)] with w hw1 hwH hwb
      have hw : w ∈ H ∩ ball (x₀ : ℂ) δ := ⟨hwH, hballsub hwb⟩
      have hTH := (hT w hw).1
      have e1 : F (T w) = fwdMapInv W τ (T w) := ZhanGT4.extendFrom_eq_fwdMapInv hW hW0 hτ0 hTH
      have h1 := hC _ hTH
      rw [dist_eq_norm, e1] at hw1
      have h2 := norm_sub_le (fwdMapInv W τ (T w)) (fwdMapInv W τ (T w) - T w)
      rw [sub_sub_cancel] at h2
      have h3 : ‖fwdMapInv W τ (T w)‖ ≤ ‖v‖ + 1 := by
        have := norm_le_norm_add_norm_sub' (fwdMapInv W τ (T w)) v
        linarith
      linarith
    have hGc : ContinuousOn T (H ∩ ball (x : ℂ) r) := hTcont.mono fun w hw => ⟨hw.1, hballsub hw.2⟩
    have hGH : MapsTo T (H ∩ ball (x : ℂ) r) Hbar := fun w hw =>
      QuantumZipper.H_subset_Hbar (hT w ⟨hw.1, hballsub hw.2⟩).1
    obtain ⟨ξ, hξ, hFξ, hξlim⟩ :=
      Sec7.PocketStopSide.exists_tendsto_of_tendsto_comp_local hFd hFc hFi hFR hr hGc hGH hbdd hcomp
    refine ⟨ξ, ?_, hFξ, hξlim⟩
    by_contra hξim
    have hξH : ξ ∈ H := lt_of_le_of_ne hξ (Ne.symm hξim)
    exact trace_notMem_image_H hη hW hW0 hτ0 hs ⟨ξ, hξH, hFξ.trans hv⟩
  choose! ξf hξf using hlim
  -- the extended transition
  have hreal_mem : ∀ z ∈ ball (x₀ : ℂ) δ, z.im = 0 → z = (z.re : ℂ) ∧ z.re ∈ Ioo (x₀ - δ) (x₀ + δ) := by
    intro z hz hz0
    have he : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
    refine ⟨he, ?_⟩
    rw [he, mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt] at hz
    exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hTat : ∀ w ∈ H ∩ ball (x₀ : ℂ) δ, Tendsto T (𝓝[H] w) (𝓝 (T w)) := fun w hw =>
    ((hTcont w hw).continuousAt (hOpen.mem_nhds hw)).tendsto.mono_left nhdsWithin_le_nhds
  set m : ℂ → ℂ := extendFrom H T with hmdef
  have hmT : ∀ w ∈ H ∩ ball (x₀ : ℂ) δ, m w = T w := fun w hw =>
    extendFrom_eq (subset_closure hw.1) (hTat w hw)
  have hmξ : ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), m x = ξf x := fun x hx => by
    refine extendFrom_eq ?_ (hξf x hx).2.2
    rw [closure_H]; exact hreal x
  have hmc : ContinuousOn m (Hbar ∩ ball (x₀ : ℂ) δ) := by
    refine continuousOn_extendFrom (fun w hw => by rw [closure_H]; exact hw.1) fun w hw => ?_
    by_cases hwH : w ∈ H
    · exact ⟨_, hTat w ⟨hwH, hw.2⟩⟩
    · have hw0 : w.im = 0 := le_antisymm (not_lt.1 hwH) hw.1
      obtain ⟨he, hx⟩ := hreal_mem w hw.2 hw0
      rw [he]
      exact ⟨_, (hξf _ hx).2.2⟩
  have hmreal : ∀ z ∈ ball (x₀ : ℂ) δ, z.im = 0 → (m z).im = 0 := by
    intro z hz hz0
    obtain ⟨he, hx⟩ := hreal_mem z hz hz0
    rw [he, hmξ _ hx]
    exact (hξf _ hx).1
  have hmH : MapsTo m (H ∩ ball (x₀ : ℂ) δ) H := fun w hw => by rw [hmT w hw]; exact (hT w hw).1
  have hRBC : R16.IsRealBoundaryConformal m x₀ δ := by
    refine ⟨hTdiff.congr fun w hw => hmT w hw, hmc, hmreal, hmH, fun w hw w' hw' he => ?_⟩
    rw [hmT w hw, hmT w' hw'] at he
    have := (hT w hw).2.symm.trans ((congrArg c'.2.1 he).trans (hT w' hw').2)
    exact hc.injOn hw.1 hw'.1 this
  refine ⟨δ, m, hδ, hRBC, fun z hz => ⟨hmH hz, by rw [hmT z hz]; exact (hT z hz).2.symm⟩, fun x hx => ?_⟩
  rw [hmξ x hx]
  exact ⟨(hξf x hx).1, (hξf x hx).2.1⟩

/-- **Left side: a chart landing on later points of a fresh arc sees its left side.** -/
theorem nonempty_sideIdentification_of_later (hc : c.IsConformal) (hc₀ : c₀.IsConformal)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) (htτ : t < τ)
    (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Icc t τ, η s ∈ H) {y : ℝ} (hy : y < 0)
    (hFy : extendFrom H (fwdMapInv W τ) y = η t)
    (hland : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)))
    (htrace : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Icc 0 τ, η s ∈ H ∧ Λ x = c₀.2.1 (η s))
    (hdom : ∃ δ > 0, ∀ z ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 z ∈ (c₀.loewner W τ).2.1 '' H)
    (hp : Λ x₀ = c₀.2.1 (η t))
    (hlater : ∃ ε > 0, ∀ x ∈ Ioo x₀ (x₀ + ε), ∃ s ∈ Ioo t τ, Λ x = c₀.2.1 (η s)) :
    Nonempty (WalkIntBridge.SideIdentification c (c₀.loewner W τ) x₀ y) := by
  have hτ0 : 0 ≤ τ := ht.trans htτ.le
  set F : ℂ → ℂ := extendFrom H (fwdMapInv W τ) with hFdef
  obtain ⟨δ, m, hδ, hRBC, hinv, hbd⟩ := exists_transition_extension hc hc₀ hη hW hW0 hτ0 hland htrace hdom
  obtain ⟨ε, hε, hlater'⟩ := hlater
  have hx₀ : x₀ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have htH : η t ∈ H := hH t ⟨le_rfl, htτ.le⟩
  obtain ⟨h0im, hF0⟩ := hbd x₀ hx₀
  rw [hp, hc₀.2.2 _ htH] at hF0
  set a : ℝ := (m x₀).re with hadef
  have hma : m x₀ = (a : ℂ) := Complex.ext (by simp [hadef]) (by simp [h0im])
  have hFa : F a = η t := by rw [← hma]; exact hF0
  have htip : F 0 = η τ := hη.loewnerTip_eq hW hW0 hτ0
  have hat : m x₀ = y := by
    rw [hma]
    congr 1
    rcases lt_trichotomy a 0 with ha | ha | ha
    · exact eq_of_extendFrom_eq_of_same_side hη hW hW0 ht htτ hinj htH (mul_pos_of_neg_of_neg ha hy) hFa hFy
    · exfalso
      rw [ha, ofReal_zero, htip] at hFa
      exact htτ.ne' (hinj ⟨hτ0, le_rfl⟩ ⟨ht, htτ.le⟩ hFa)
    · exfalso
      have hmono := Sec7.Aux37Side.strictMonoOn_re hRBC
      set x : ℝ := x₀ + min δ ε / 2 with hxdef
      have hmin1 : min δ ε ≤ δ := min_le_left _ _
      have hmin2 : min δ ε ≤ ε := min_le_right _ _
      have hmin0 : 0 < min δ ε := lt_min hδ hε
      have hxmem : x ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
      have hxlt : (m x₀).re < (m x).re := hmono hx₀ hxmem (by linarith)
      obtain ⟨s, hs, hsx⟩ := hlater' x ⟨by linarith, by linarith⟩
      have hsH : η s ∈ H := hH s ⟨hs.1.le, hs.2.le⟩
      obtain ⟨hxim, hFx⟩ := hbd x hxmem
      rw [hsx, hc₀.2.2 _ hsH] at hFx
      set b : ℝ := (m x).re with hbdef
      have hmxb : m x = (b : ℂ) := Complex.ext (by simp [hbdef]) (by simp [hxim])
      have hFb : F b = η s := by rw [← hmxb]; exact hFx
      obtain ⟨y', hy', hFy'⟩ := WalkNorm.exists_eq_of_cut hη hW hW0 (ht.trans hs.1.le) hs.2.le hinj
        (fun r hr => hH r ⟨hs.1.le.trans hr.1, hr.2⟩) (a := a) (c := 0)
        (Or.inr ⟨t, ⟨ht, hs.1.le⟩, hFa.symm⟩) (by rw [ofReal_zero]; exact htip)
      rw [uIcc_of_ge ha.le] at hy'
      have hy0 : y' ≠ 0 := by
        rintro rfl
        have h' : F ((0 : ℝ) : ℂ) = η s := hFy'
        rw [ofReal_zero, htip] at h'
        exact hs.2.ne' (hinj ⟨hτ0, le_rfl⟩ ⟨ht.trans hs.1.le, hs.2.le⟩ h')
      have hya : y' ≠ a := by
        rintro rfl
        have h' : F (a : ℂ) = η s := hFy'
        rw [hFa] at h'
        exact hs.1.ne (hinj ⟨ht, htτ.le⟩ ⟨ht.trans hs.1.le, hs.2.le⟩ h')
      have hy0' : 0 < y' := lt_of_le_of_ne hy'.1 (Ne.symm hy0)
      have hya' : y' < a := lt_of_le_of_ne hy'.2 hya
      have hyb := eq_of_extendFrom_eq_of_same_side hη hW hW0 (ht.trans hs.1.le) hs.2 hinj hsH
        (mul_pos hy0' (by linarith)) hFy' hFb
      linarith
  exact ⟨⟨δ, hδ, m, hRBC.2.1, hRBC.2.2.1, hat, hinv⟩⟩

/-- **Right side: a chart landing on earlier points of a fresh arc sees its right side.** -/
theorem nonempty_sideIdentification_of_earlier (hc : c.IsConformal) (hc₀ : c₀.IsConformal)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s₀ t : ℝ} (hs₀ : 0 ≤ s₀) (hs₀t : s₀ < t)
    (htτ : t < τ) (hinj : InjOn η (Icc 0 τ)) (hH : ∀ s ∈ Icc t τ, η s ∈ H) {y : ℝ} (hy : 0 < y)
    (hFy : extendFrom H (fwdMapInv W τ) y = η t)
    (hland : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (Λ x)))
    (htrace : ∃ δ > 0, ∀ x ∈ Ioo (x₀ - δ) (x₀ + δ), ∃ s ∈ Icc 0 τ, η s ∈ H ∧ Λ x = c₀.2.1 (η s))
    (hdom : ∃ δ > 0, ∀ z ∈ H ∩ ball (x₀ : ℂ) δ, c.2.1 z ∈ (c₀.loewner W τ).2.1 '' H)
    (hp : Λ x₀ = c₀.2.1 (η t))
    (hearlier : ∃ ε > 0, ∀ x ∈ Ioo x₀ (x₀ + ε), ∃ s ∈ Ioo s₀ t, η s ∈ H ∧ Λ x = c₀.2.1 (η s)) :
    Nonempty (WalkIntBridge.SideIdentification c (c₀.loewner W τ) x₀ y) := by
  have ht : 0 ≤ t := hs₀.trans hs₀t.le
  have hτ0 : 0 ≤ τ := ht.trans htτ.le
  set F : ℂ → ℂ := extendFrom H (fwdMapInv W τ) with hFdef
  obtain ⟨δ, m, hδ, hRBC, hinv, hbd⟩ := exists_transition_extension hc hc₀ hη hW hW0 hτ0 hland htrace hdom
  obtain ⟨ε, hε, hearlier'⟩ := hearlier
  have hx₀ : x₀ ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
  have htH : η t ∈ H := hH t ⟨le_rfl, htτ.le⟩
  obtain ⟨h0im, hF0⟩ := hbd x₀ hx₀
  rw [hp, hc₀.2.2 _ htH] at hF0
  set a : ℝ := (m x₀).re with hadef
  have hma : m x₀ = (a : ℂ) := Complex.ext (by simp [hadef]) (by simp [h0im])
  have hFa : F a = η t := by rw [← hma]; exact hF0
  have htip : F 0 = η τ := hη.loewnerTip_eq hW hW0 hτ0
  have hat : m x₀ = y := by
    rw [hma]
    congr 1
    rcases lt_trichotomy a 0 with ha | ha | ha
    · exfalso
      have hmono := Sec7.Aux37Side.strictMonoOn_re hRBC
      -- `m` stays negative just right of `x₀`
      obtain ⟨d, hd, hdcont⟩ := Metric.continuousWithinAt_iff.1
        (hRBC.2.1 (x₀ : ℂ) ⟨show (0 : ℝ) ≤ ((x₀ : ℂ)).im by simp, mem_ball_self hδ⟩) (-a) (by linarith)
      set e : ℝ := min (min δ ε) d with hedef
      have he0 : 0 < e := lt_min (lt_min hδ hε) hd
      have he1 : e ≤ δ := (min_le_left _ _).trans (min_le_left _ _)
      have he2 : e ≤ ε := (min_le_left _ _).trans (min_le_right _ _)
      have he3 : e ≤ d := min_le_right _ _
      set x : ℝ := x₀ + e / 2 with hxdef
      have hxmem : x ∈ Ioo (x₀ - δ) (x₀ + δ) := ⟨by linarith, by linarith⟩
      have hxlt : (m x₀).re < (m x).re := hmono hx₀ hxmem (by linarith)
      have hxd : dist (x : ℂ) (x₀ : ℂ) < d := by
        rw [dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      have hxball : (x : ℂ) ∈ ball (x₀ : ℂ) δ := by
        rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
        constructor <;> linarith
      have hneg : (m x).re < 0 := by
        have h1 := hdcont ⟨show (0 : ℝ) ≤ ((x : ℂ)).im by simp, hxball⟩ hxd
        rw [dist_eq_norm] at h1
        have h2 := Complex.abs_re_le_norm (m x - m x₀)
        rw [sub_re] at h2
        have h3 : (m x₀).re = a := rfl
        linarith [le_abs_self ((m x).re - (m x₀).re)]
      obtain ⟨s, hs, hsH, hsx⟩ := hearlier' x ⟨by linarith, by linarith⟩
      have hs0 : 0 ≤ s := hs₀.trans hs.1.le
      obtain ⟨hxim, hFx⟩ := hbd x hxmem
      rw [hsx, hc₀.2.2 _ hsH] at hFx
      set b : ℝ := (m x).re with hbdef
      have hmxb : m x = (b : ℂ) := Complex.ext (by simp [hbdef]) (by simp [hxim])
      have hFb : F b = η s := by rw [← hmxb]; exact hFx
      obtain ⟨y', hy', hFy'⟩ := WalkNorm.exists_eq_of_cut hη hW hW0 ht htτ.le hinj hH (a := b) (c := 0)
        (Or.inr ⟨s, ⟨hs0, hs.2.le⟩, hFb.symm⟩) (by rw [ofReal_zero]; exact htip)
      rw [uIcc_of_le hneg.le] at hy'
      have hy0 : y' ≠ 0 := by
        rintro rfl
        have h' : F ((0 : ℝ) : ℂ) = η t := hFy'
        rw [ofReal_zero, htip] at h'
        exact htτ.ne' (hinj ⟨hτ0, le_rfl⟩ ⟨ht, htτ.le⟩ h')
      have hyb : y' ≠ b := by
        rintro rfl
        have h' : F (b : ℂ) = η t := hFy'
        rw [hFb] at h'
        exact hs.2.ne (hinj ⟨hs0, hs.2.le.trans htτ.le⟩ ⟨ht, htτ.le⟩ h')
      have hy0' : y' < 0 := lt_of_le_of_ne hy'.2 hy0
      have hyb' : b < y' := lt_of_le_of_ne hy'.1 (Ne.symm hyb)
      have hya := eq_of_extendFrom_eq_of_same_side hη hW hW0 ht htτ hinj htH
        (mul_pos_of_neg_of_neg hy0' ha) hFy' hFa
      have : (m x₀).re = a := rfl
      linarith
    · exfalso
      rw [ha, ofReal_zero, htip] at hFa
      exact htτ.ne' (hinj ⟨hτ0, le_rfl⟩ ⟨ht, htτ.le⟩ hFa)
    · exact eq_of_extendFrom_eq_of_same_side hη hW hW0 ht htτ hinj htH (mul_pos ha hy) hFa hFy
  exact ⟨⟨δ, hδ, m, hRBC.2.1, hRBC.2.2.1, hat, hinv⟩⟩

end Land

end InteractingSLE.Theorem14.WalkWords

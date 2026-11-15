import InteractingSLE.Foundations.Loewner.YuanCharacterisationArc
import QuantumZipper.Proofs.Complex.KoebeCovering

/-!
# The boundary interval of a hull touching `ℝ` at one point, and its size

Packet PROVE-YUAN-M23, inputs of [Law05, Proposition 3.76] for simple paths. Let `B` be a compact
`ℍ`-hull with mapping-out function `g`, let `F` be the continuous extension to `ℍ̄` of `g⁻¹`
(`IsBdryExt`), and assume that the closure of `B` meets `ℝ` only at one point `U`.

## Main results

* `bdrySet B F = {x ∈ ℝ | F(x) ∈ closure B}` (the real points whose prime ends lie on `B`) is a
  compact interval `[a, b]` (`bdrySet_eq_Icc`), nonempty when `B ≠ ∅`, and `F` is real on
  `ℝ \ [a, b]`.
* `norm_sub_le_of_mem`: **[Law05, (3.13)], upper half**: every two points of `B` are at distance
  at most `12 (b − a)`. Proof: the reflection `F̂` of `F` across `ℝ \ [a, b]` is a conformal map
  of `ℂ \ [a, b]` omitting `B`; composed with the Joukowski map `w ↦ c + ℓ (w + 1/w)`,
  `4ℓ ≥ b − a`, and inverted, it gives a univalent function on the unit disc to which Koebe's
  covering theorem (QuantumZipper's constant `1/48`) applies.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace YuanCharacterisation

/-- `F` is a **boundary extension** of the inverse of the mapping-out function `g` of the hull
`B`: on `ℍ` it is `g⁻¹`, it is continuous on `ℍ̄`, sends real points to the boundary of `ℍ \ B`,
and stays at bounded distance from the identity. -/
structure IsBdryExt (B : Set ℂ) (g F : ℂ → ℂ) : Prop where
  hull : IsHPHull B
  isMapOut : IsMapOut B g
  mem : ∀ w ∈ H, F w ∈ H \ B ∧ g (F w) = w
  differentiableOn : DifferentiableOn ℂ F H
  continuousOn : ContinuousOn F Hbar
  frontier_mem : ∀ x : ℝ, F x ∈ frontier (H \ B)
  bdd : ∃ M : ℝ, ∀ w ∈ Hbar, ‖F w - w‖ ≤ M

/-- The real points whose image under `F` lies on the closure of `B`. -/
def bdrySet (B : Set ℂ) (F : ℂ → ℂ) : Set ℝ := {x : ℝ | F x ∈ closure B}

namespace IsBdryExt

variable {B : Set ℂ} {g F : ℂ → ℂ}

theorem injOn (h : IsBdryExt B g F) : InjOn F H := fun w hw w' hw' hww' => by
  rw [← (h.mem w hw).2, ← (h.mem w' hw').2, hww']

theorem ofReal_mem_Hbar (x : ℝ) : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp

/-- Off the closure of `B`, real points are sent to real points. -/
theorem im_eq_zero (h : IsBdryExt B g F) {x : ℝ} (hx : F x ∉ closure B) : (F x).im = 0 := by
  have hfr := h.frontier_mem x
  rw [h.hull.isOpen.frontier_eq] at hfr
  obtain ⟨hcl, hnot⟩ := hfr
  have hHbar : F x ∈ Hbar := by
    have : closure (H \ B) ⊆ Hbar :=
      closure_minimal (fun z hz => H_subset_Hbar hz.1) isClosed_Hbar
    exact this hcl
  by_contra hne
  have hH : F x ∈ H := lt_of_le_of_ne (show 0 ≤ (F x).im from hHbar) (Ne.symm hne)
  exact hnot ⟨hH, fun hB => hx (subset_closure hB)⟩

/-- `g` has a limit at every real point outside the closure of `B`, equal to the parameter of
every real point mapped there by `F`; hence `F` is injective on the real points it sends off
`closure B`. -/
theorem eq_of_eq (h : IsBdryExt B g F) {x x' : ℝ} (hx : F x ∉ closure B)
    (hxx' : F x = F x') : x = x' := by
  have hx' : F x' ∉ closure B := hxx' ▸ hx
  set p := F x with hp
  have hpim : p.im = 0 := h.im_eq_zero hx
  have hpeq : p = (p.re : ℂ) := eq_ofReal_re_of_im_eq_zero hpim
  obtain ⟨ρ, hρ, hρB⟩ := Metric.mem_nhds_iff.1 (isClosed_closure.isOpen_compl.mem_nhds hx)
  have hd : Disjoint (ball (p.re : ℂ) ρ) B := Set.disjoint_left.2 fun z hz hzB => by
    rw [← hpeq] at hz
    exact hρB hz (subset_closure hzB)
  obtain ⟨L, -, hL⟩ := h.isMapOut.exists_tendsto_of_disjoint h.hull hd
    (x := p) (by rw [← hpeq]; exact mem_ball_self (by positivity)) hpim
  -- `g ∘ F` along the vertical at `y` converges both to `y` and to `L`
  have key : ∀ y : ℝ, F y = p → L = y := by
    intro y hy
    set φ : ℝ → ℂ := fun τ => (y : ℂ) + (τ : ℂ) * I with hφ
    have hφH : ∀ τ > 0, φ τ ∈ H := fun τ hτ => by
      show 0 < (φ τ).im; simp [hφ, hτ]
    have hφlim : Tendsto φ (𝓝[>] 0) (𝓝[Hbar] (y : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto φ (𝓝 0) (𝓝 (φ 0)) := (by fun_prop : Continuous φ).tendsto 0
        simpa [hφ] using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        exact H_subset_Hbar (hφH τ hτ)
    have hFφ : Tendsto (fun τ => F (φ τ)) (𝓝[>] 0) (𝓝 p) := by
      rw [← hy]; exact (h.continuousOn _ (ofReal_mem_Hbar y)).tendsto.comp hφlim
    have hFφ' : Tendsto (fun τ => F (φ τ)) (𝓝[>] 0) (𝓝[ball (p.re : ℂ) (ρ / 2) ∩ H] p) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hFφ, ?_⟩
      have hb : ∀ᶠ τ in 𝓝[>] 0, F (φ τ) ∈ ball (p.re : ℂ) (ρ / 2) := by
        rw [← hpeq]; exact hFφ (ball_mem_nhds p (by positivity))
      filter_upwards [hb, self_mem_nhdsWithin] with τ hτb hτ
      exact ⟨hτb, (h.mem _ (hφH τ hτ)).1.1⟩
    have h1 : Tendsto (fun τ => g (F (φ τ))) (𝓝[>] 0) (𝓝 L) := hL.comp hFφ'
    have h2 : Tendsto (fun τ => g (F (φ τ))) (𝓝[>] 0) (𝓝 (y : ℂ)) := by
      have : Tendsto φ (𝓝[>] 0) (𝓝 (y : ℂ)) := hφlim.mono_right nhdsWithin_le_nhds
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact ((h.mem _ (hφH τ hτ)).2).symm
    exact tendsto_nhds_unique h1 h2
  have e1 := key x rfl
  have e2 := key x' hxx'.symm
  exact_mod_cast e1.symm.trans e2

theorem isClosed_bdrySet (h : IsBdryExt B g F) : IsClosed (bdrySet B F) := by
  have hc : Continuous fun x : ℝ => F x :=
    continuous_iff_continuousAt.2 fun x =>
      ((h.continuousOn _ (ofReal_mem_Hbar x)).comp continuous_ofReal.continuousWithinAt
        (fun y _ => ofReal_mem_Hbar y)).continuousAt univ_mem
  exact isClosed_closure.preimage hc

theorem isBounded_bdrySet (h : IsBdryExt B g F) : Bornology.IsBounded (bdrySet B F) := by
  obtain ⟨M, hM⟩ := h.bdd
  obtain ⟨r, hr⟩ := h.hull.2.1.closure.exists_norm_le
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨r + M, fun x hx => ?_⟩
  have h1 := hM x (ofReal_mem_Hbar x)
  have h2 := hr _ hx
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  have : ‖(x : ℂ)‖ ≤ ‖F x‖ + ‖F x - x‖ := by
    calc ‖(x : ℂ)‖ = ‖F x - (F x - x)‖ := by ring_nf
      _ ≤ ‖F x‖ + ‖F x - x‖ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_eq_abs] at this
  linarith

end IsBdryExt

/-- The Schwarz reflection of `F` across `ℝ`. -/
def reflExt (F : ℂ → ℂ) (z : ℂ) : ℂ := if 0 ≤ z.im then F z else conj (F (conj z))

theorem reflExt_of_nonneg {F : ℂ → ℂ} {z : ℂ} (hz : 0 ≤ z.im) : reflExt F z = F z := by
  simp only [reflExt, hz, ite_true]

theorem reflExt_of_neg {F : ℂ → ℂ} {z : ℂ} (hz : z.im < 0) : reflExt F z = conj (F (conj z)) := by
  simp only [reflExt, not_le.2 hz, ite_false]

namespace IsBdryExt

variable {B : Set ℂ} {g F : ℂ → ℂ}

theorem conj_mem_H {z : ℂ} (hz : z.im < 0) : conj z ∈ H := show 0 < (conj z).im by
  rw [conj_im]; linarith

theorem norm_reflExt_sub_le (h : IsBdryExt B g F) : ∃ M : ℝ, ∀ z : ℂ, ‖reflExt F z - z‖ ≤ M := by
  obtain ⟨M, hM⟩ := h.bdd
  refine ⟨M, fun z => ?_⟩
  rcases le_or_gt 0 z.im with hz | hz
  · rw [reflExt_of_nonneg hz]; exact hM z hz
  · rw [reflExt_of_neg hz]
    have := hM (conj z) (H_subset_Hbar (conj_mem_H hz))
    calc ‖conj (F (conj z)) - z‖ = ‖conj (F (conj z) - conj z)‖ := by simp
      _ = ‖F (conj z) - conj z‖ := Complex.norm_conj _
      _ ≤ M := this

theorem differentiableAt_reflExt_of_im_ne (h : IsBdryExt B g F) {z : ℂ} (hz : z.im ≠ 0) :
    DifferentiableAt ℂ (reflExt F) z := by
  rcases lt_or_gt_of_ne hz with hz | hz
  · have hev : reflExt F =ᶠ[𝓝 z] (conj ∘ F ∘ conj) := by
      filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz] with w hw
      exact reflExt_of_neg hw
    have hd : DifferentiableAt ℂ F (conj z) :=
      h.differentiableOn.differentiableAt (QuantumZipper.isOpen_H.mem_nhds (conj_mem_H hz))
    have := hd.conj_conj
    rw [conj_conj] at this
    exact this.congr_of_eventuallyEq hev
  · have hev : reflExt F =ᶠ[𝓝 z] F := by
      filter_upwards [QuantumZipper.isOpen_H.mem_nhds (show z ∈ H from hz)] with w hw
      exact reflExt_of_nonneg (le_of_lt hw)
    exact (h.differentiableOn.differentiableAt
      (QuantumZipper.isOpen_H.mem_nhds (show z ∈ H from hz))).congr_of_eventuallyEq hev

/-- Schwarz reflection across real points whose neighbourhood avoids `bdrySet`. -/
theorem differentiableAt_reflExt_of_real (h : IsBdryExt B g F) {x r : ℝ} (hr : 0 < r)
    (hx : ∀ y : ℝ, |y - x| < r → y ∉ bdrySet B F) : DifferentiableAt ℂ (reflExt F) x := by
  have hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (F z).im = 0 := by
    intro z hz hz0
    have hzeq : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    rw [hzeq]
    refine h.im_eq_zero (hx z.re ?_)
    rw [mem_ball, hzeq, dist_eq_norm, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hz
    exact hz
  obtain ⟨G, hGd, hGeq, hGconj⟩ := QuantumZipper.CA.exists_reflection_extension
    (h.differentiableOn.mono inter_subset_left) (h.continuousOn.mono inter_subset_left) hreal
  have hev : reflExt F =ᶠ[𝓝 (x : ℂ)] G := by
    filter_upwards [ball_mem_nhds (x : ℂ) hr] with z hz
    rcases le_or_gt 0 z.im with hz0 | hz0
    · rw [reflExt_of_nonneg hz0, hGeq ⟨hz0, hz⟩]
    · rw [reflExt_of_neg hz0]
      have hcz : conj z ∈ ball (x : ℂ) r := QuantumZipper.CA.conj_mem_ball_ofReal hz
      rw [← hGeq ⟨H_subset_Hbar (conj_mem_H hz0), hcz⟩, hGconj z hz, conj_conj]
  exact (hGd.differentiableAt (ball_mem_nhds _ hr)).congr_of_eventuallyEq hev

/-- The values of the reflection: `Im F̂(z)` has the sign of `Im z`, off the boundary set. -/
theorem im_reflExt_pos (h : IsBdryExt B g F) {z : ℂ} (hz : 0 < z.im) :
    0 < (reflExt F z).im := by
  rw [reflExt_of_nonneg hz.le]; exact (h.mem z hz).1.1

theorem im_reflExt_neg (h : IsBdryExt B g F) {z : ℂ} (hz : z.im < 0) :
    (reflExt F z).im < 0 := by
  rw [reflExt_of_neg hz, conj_im]
  exact neg_lt_zero.2 (h.mem _ (conj_mem_H hz)).1.1

theorem reflExt_notMem (h : IsBdryExt B g F) {z : ℂ}
    (hz : ∀ x : ℝ, z = x → x ∉ bdrySet B F) : reflExt F z ∉ B := by
  intro hB
  have hBH := h.hull.1 hB
  rcases lt_trichotomy z.im 0 with hz0 | hz0 | hz0
  · exact absurd (show (0 : ℝ) < _ from hBH) (not_lt.2 (h.im_reflExt_neg hz0).le)
  · have hzeq : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hz0
    rw [reflExt_of_nonneg hz0.ge] at hB
    exact hz z.re hzeq (show F z.re ∈ closure B by rw [← hzeq]; exact subset_closure hB)
  · rw [reflExt_of_nonneg hz0.le] at hB
    exact (h.mem z hz0).1.2 hB

theorem reflExt_injOn (h : IsBdryExt B g F) :
    InjOn (reflExt F) {z : ℂ | ∀ x : ℝ, z = x → x ∉ bdrySet B F} := by
  intro z hz z' hz' heq
  rcases lt_trichotomy z.im 0 with h1 | h1 | h1 <;> rcases lt_trichotomy z'.im 0 with h2 | h2 | h2
  · rw [reflExt_of_neg h1, reflExt_of_neg h2] at heq
    have := h.injOn (conj_mem_H h1) (conj_mem_H h2) ((starRingEnd ℂ).injective heq)
    exact (starRingEnd ℂ).injective this
  · have := h.im_reflExt_neg h1
    rw [heq, reflExt_of_nonneg h2.ge] at this
    have hz'eq : z' = (z'.re : ℂ) := eq_ofReal_re_of_im_eq_zero h2
    rw [hz'eq, h.im_eq_zero (hz' z'.re hz'eq)] at this
    exact absurd this (lt_irrefl _)
  · exact absurd (heq ▸ h.im_reflExt_pos h2) (not_lt.2 (h.im_reflExt_neg h1).le)
  · have := h.im_reflExt_neg h2
    rw [← heq, reflExt_of_nonneg h1.ge] at this
    have hzeq : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero h1
    rw [hzeq, h.im_eq_zero (hz z.re hzeq)] at this
    exact absurd this (lt_irrefl _)
  · have hzeq : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero h1
    have hz'eq : z' = (z'.re : ℂ) := eq_ofReal_re_of_im_eq_zero h2
    rw [reflExt_of_nonneg h1.ge, reflExt_of_nonneg h2.ge, hzeq, hz'eq] at heq
    rw [hzeq, hz'eq, h.eq_of_eq (hz z.re hzeq) heq]
  · have := h.im_reflExt_pos h2
    rw [← heq, reflExt_of_nonneg h1.ge] at this
    have hzeq : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero h1
    rw [hzeq, h.im_eq_zero (hz z.re hzeq)] at this
    exact absurd this (lt_irrefl _)
  · exact absurd (heq ▸ h.im_reflExt_neg h2) (not_lt.2 (h.im_reflExt_pos h1).le)
  · have := h.im_reflExt_pos h1
    rw [heq, reflExt_of_nonneg h2.ge] at this
    have hz'eq : z' = (z'.re : ℂ) := eq_ofReal_re_of_im_eq_zero h2
    rw [hz'eq, h.im_eq_zero (hz' z'.re hz'eq)] at this
    exact absurd this (lt_irrefl _)
  · rw [reflExt_of_nonneg h1.le, reflExt_of_nonneg h2.le] at heq
    exact h.injOn h1 h2 heq

/-- A nonempty hull has a nonempty boundary set (otherwise the reflection is entire, at bounded
distance from the identity, hence a real translation by Liouville's theorem). -/
theorem bdrySet_nonempty (h : IsBdryExt B g F) (hB : B.Nonempty) : (bdrySet B F).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hx : ∀ y : ℝ, y ∉ bdrySet B F := fun y => by rw [hne]; exact notMem_empty y
  have hdiff : Differentiable ℂ (fun z => reflExt F z - z) := by
    intro z
    refine DifferentiableAt.sub ?_ differentiableAt_id
    by_cases hz : z.im = 0
    · have hzeq : z = (z.re : ℂ) := eq_ofReal_re_of_im_eq_zero hz
      rw [hzeq]
      exact h.differentiableAt_reflExt_of_real one_pos fun y _ => hx y
    · exact h.differentiableAt_reflExt_of_im_ne hz
  obtain ⟨M, hM⟩ := h.norm_reflExt_sub_le
  have hbd : Bornology.IsBounded (range fun z => reflExt F z - z) :=
    (Metric.isBounded_iff_subset_closedBall 0).2 ⟨M, by
      rintro _ ⟨z, rfl⟩; rw [mem_closedBall, dist_zero_right]; exact hM z⟩
  have hconst : ∀ z, reflExt F z - z = reflExt F 0 - 0 := fun z =>
    hdiff.apply_eq_apply_of_bounded hbd z 0
  set c := reflExt F 0 with hc
  have hcim : c.im = 0 := by
    rw [hc, reflExt_of_nonneg (by simp)]
    have := h.im_eq_zero (x := 0) (hx 0)
    simpa using this
  obtain ⟨b, hb⟩ := hB
  have hbH : b ∈ H := h.hull.1 hb
  have hw : b - c ∈ H := show 0 < (b - c).im by rw [sub_im, hcim, sub_zero]; exact hbH
  have h1 := hconst (b - c)
  rw [sub_zero, reflExt_of_nonneg (le_of_lt hw)] at h1
  have h2 : F (b - c) = b := by linear_combination h1
  have h3 : F (b - c) ∈ B := by rw [h2]; exact hb
  exact (h.mem _ hw).1.2 h3

/-- **The boundary set is an interval**, when `closure B` meets `ℝ` only at one point. -/
theorem bdrySet_eq_Icc (h : IsBdryExt B g F) (hB : B.Nonempty) {U : ℝ}
    (hU : ∀ z ∈ closure B, z.im = 0 → z = U) :
    bdrySet B F = Icc (sInf (bdrySet B F)) (sSup (bdrySet B F)) := by
  set X := bdrySet B F with hX
  have hXc := h.isClosed_bdrySet
  have hXb := h.isBounded_bdrySet
  have hXne := h.bdrySet_nonempty hB
  refine Subset.antisymm (fun x hx => ⟨csInf_le hXb.bddBelow hx, le_csSup hXb.bddAbove hx⟩) ?_
  intro x hx
  by_contra hxX
  -- the gap `(x₁, x₂)` of `X` around `x`
  set X₁ := X ∩ Iic x with hX₁
  set X₂ := X ∩ Ici x with hX₂
  have hX₁ne : X₁.Nonempty := ⟨sInf X, ⟨hXc.csInf_mem hXne hXb.bddBelow, hx.1⟩⟩
  have hX₂ne : X₂.Nonempty := ⟨sSup X, ⟨hXc.csSup_mem hXne hXb.bddAbove, hx.2⟩⟩
  have hX₁c : IsClosed X₁ := hXc.inter isClosed_Iic
  have hX₂c : IsClosed X₂ := hXc.inter isClosed_Ici
  set x₁ := sSup X₁ with hx₁
  set x₂ := sInf X₂ with hx₂
  have hx₁m : x₁ ∈ X₁ := hX₁c.csSup_mem hX₁ne ⟨x, fun y hy => hy.2⟩
  have hx₂m : x₂ ∈ X₂ := hX₂c.csInf_mem hX₂ne ⟨x, fun y hy => hy.2⟩
  have hx₁x : x₁ < x := lt_of_le_of_ne hx₁m.2 fun he => hxX (he ▸ hx₁m.1)
  have hxx₂ : x < x₂ := lt_of_le_of_ne hx₂m.2 fun he => hxX (he.symm ▸ hx₂m.1)
  have hgap : ∀ y ∈ Ioo x₁ x₂, y ∉ X := by
    intro y hy hyX
    rcases le_total y x with hyx | hyx
    · have hmem : y ∈ X₁ := ⟨hyX, hyx⟩
      exact absurd (le_csSup (⟨x, fun z hz => hz.2⟩ : BddAbove X₁) hmem) (not_le.2 hy.1)
    · have hmem : y ∈ X₂ := ⟨hyX, hyx⟩
      exact absurd (csInf_le (⟨x, fun z hz => hz.2⟩ : BddBelow X₂) hmem) (not_le.2 hy.2)
  -- `f = Re ∘ F` on `[x₁, x₂]`
  have hFc : ContinuousOn (fun y : ℝ => F y) (Icc x₁ x₂) :=
    (h.continuousOn.comp continuous_ofReal.continuousOn fun y _ => ofReal_mem_Hbar y)
  have hreal : ∀ y ∈ Icc x₁ x₂, (F y).im = 0 := by
    intro y hy
    have hcl : Icc x₁ x₂ ⊆ closure (Ioo x₁ x₂) := by
      rw [closure_Ioo (by linarith : x₁ ≠ x₂)]
    have hcont : ContinuousOn (fun y : ℝ => (F y).im) (Icc x₁ x₂) :=
      continuous_im.comp_continuousOn hFc
    have hzero : EqOn (fun y : ℝ => (F y).im) 0 (Ioo x₁ x₂) := fun y hy =>
      h.im_eq_zero (hgap y hy)
    exact (hzero.of_subset_closure hcont continuousOn_const Ioo_subset_Icc_self hcl hy)
  have hU₁ : F x₁ = U := hU _ hx₁m.1 (hreal x₁ ⟨le_rfl, (hx₁x.trans hxx₂).le⟩)
  have hU₂ : F x₂ = U := hU _ hx₂m.1 (hreal x₂ ⟨(hx₁x.trans hxx₂).le, le_rfl⟩)
  set f : ℝ → ℝ := fun y => (F y).re with hf
  have hfc : ContinuousOn f (Icc x₁ x₂) := continuous_re.comp_continuousOn hFc
  have hFf : ∀ y ∈ Icc x₁ x₂, F y = f y := fun y hy =>
    eq_ofReal_re_of_im_eq_zero (hreal y hy)
  have hf₁ : f x₁ = U := by simp [hf, hU₁]
  have hf₂ : f x₂ = U := by simp [hf, hU₂]
  have hfx : f x ≠ U := by
    intro he
    apply hxX
    show F x ∈ closure B
    rw [hFf x ⟨hx₁x.le, hxx₂.le⟩, he, ← hU₁]
    exact hx₁m.1
  have hinj : ∀ y ∈ Ioo x₁ x₂, ∀ y' ∈ Ioo x₁ x₂, f y = f y' → y = y' := by
    intro y hy y' hy' hyy'
    refine h.eq_of_eq (hgap y hy) ?_
    rw [hFf y (Ioo_subset_Icc_self hy), hFf y' (Ioo_subset_Icc_self hy'), hyy']
  set c := (U + f x) / 2 with hc
  have hc1 : c ≠ U := by intro he; apply hfx; linarith
  have hc2 : c ≠ f x := by intro he; apply hfx; linarith
  have hcmem : c ∈ uIcc U (f x) := by
    rw [mem_uIcc]
    rcases le_total U (f x) with hle | hle
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  obtain ⟨y₁, hy₁, hfy₁⟩ : ∃ y₁ ∈ Icc x₁ x, f y₁ = c := by
    have := intermediate_value_uIcc (a := x₁) (b := x) (f := f)
      (hfc.mono (by rw [uIcc_of_le hx₁x.le]; exact Icc_subset_Icc_right hxx₂.le))
    rw [hf₁, uIcc_of_le hx₁x.le] at this
    exact this hcmem
  obtain ⟨y₂, hy₂, hfy₂⟩ : ∃ y₂ ∈ Icc x x₂, f y₂ = c := by
    have := intermediate_value_uIcc (a := x₂) (b := x) (f := f)
      (hfc.mono (by rw [uIcc_of_ge hxx₂.le]; exact Icc_subset_Icc_left hx₁x.le))
    rw [hf₂, uIcc_of_ge hxx₂.le] at this
    exact this hcmem
  have hy₁' : y₁ ∈ Ioo x₁ x :=
    ⟨lt_of_le_of_ne hy₁.1 fun he => hc1 (by rw [← hfy₁, ← he]; exact hf₁),
      lt_of_le_of_ne hy₁.2 fun he => hc2 (by rw [← hfy₁, he])⟩
  have hy₂' : y₂ ∈ Ioo x x₂ :=
    ⟨lt_of_le_of_ne hy₂.1 fun he => hc2 (by rw [← hfy₂, ← he]),
      lt_of_le_of_ne hy₂.2 fun he => hc1 (by rw [← hfy₂, he]; exact hf₂)⟩
  have := hinj y₁ ⟨hy₁'.1, hy₁'.2.trans hxx₂⟩ y₂ ⟨hx₁x.trans hy₂'.1, hy₂'.2⟩
    (hfy₁.trans hfy₂.symm)
  linarith [hy₁'.2, hy₂'.1]

end IsBdryExt

/-! ### The Koebe bound -/

/-- The Joukowski map `w ↦ c + ℓ (w + 1/w)`. -/
def jouk (c ℓ : ℝ) (w : ℂ) : ℂ := (c : ℂ) + (ℓ : ℂ) * (w + w⁻¹)

theorem jouk_notMem {c ℓ : ℝ} (hℓ : 0 < ℓ) {w : ℂ} (hw : 1 < ‖w‖) {x : ℝ}
    (hx : jouk c ℓ w = x) : 2 * ℓ < |x - c| := by
  have hw0 : w ≠ 0 := fun h => by rw [h, norm_zero] at hw; linarith
  have hns : 1 < normSq w := by
    rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  have him : w.im = 0 := by
    have h1 := congrArg Complex.im hx
    simp only [jouk, add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add,
      inv_im] at h1
    have h2 : ℓ * (w.im * (1 - 1 / normSq w)) = 0 := by
      rw [← h1]; field_simp; ring
    have h3 : 0 < 1 - 1 / normSq w := by
      rw [sub_pos, div_lt_one (by linarith)]; exact hns
    rcases mul_eq_zero.1 h2 with h | h
    · linarith
    · rcases mul_eq_zero.1 h with h' | h'
      · exact h'
      · linarith
  have hweq : w = (w.re : ℂ) := eq_ofReal_re_of_im_eq_zero him
  set r := w.re with hr
  have hr1 : 1 < |r| := by
    have : ‖w‖ = |r| := by rw [hweq, Complex.norm_real, Real.norm_eq_abs]
    rwa [this] at hw
  have hx' : x - c = ℓ * (r + r⁻¹) := by
    have h1 := congrArg Complex.re hx
    rw [hweq] at h1
    simp only [jouk, add_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero] at h1
    rw [← ofReal_inv, ofReal_re] at h1
    linarith
  have hrr : 2 < |r + r⁻¹| := by
    rcases lt_or_gt_of_ne (show r ≠ 0 by intro h0; rw [h0, abs_zero] at hr1; linarith) with h | h
    · have hr' : r < -1 := by
        rw [abs_of_neg h] at hr1; linarith
      have : r + r⁻¹ < -2 := by
        have h4 : r⁻¹ < 0 := inv_lt_zero.2 h
        have h5 : (r + 1) ^ 2 > 0 := by nlinarith
        have hr0 : r ≠ 0 := ne_of_lt h
        have h6 : r * (r + r⁻¹) = r ^ 2 + 1 := by field_simp
        nlinarith
      rw [abs_of_neg (by linarith)]; linarith
    · have hr' : 1 < r := by rwa [abs_of_pos h] at hr1
      have : 2 < r + r⁻¹ := by
        have h5 : (r - 1) ^ 2 > 0 := by nlinarith
        have hr0 : r ≠ 0 := ne_of_gt h
        have h6 : r * (r + r⁻¹) = r ^ 2 + 1 := by field_simp
        nlinarith
      rw [abs_of_pos (by linarith)]; linarith
  rw [hx', abs_mul, abs_of_pos hℓ]
  nlinarith

theorem jouk_injOn {c ℓ : ℝ} (hℓ : 0 < ℓ) : InjOn (jouk c ℓ) {w : ℂ | 1 < ‖w‖} := by
  intro w hw w' hw' heq
  have hw0 : w ≠ 0 := fun h => by
    have : (1 : ℝ) < ‖w‖ := hw; rw [h, norm_zero] at this; linarith
  have hw0' : w' ≠ 0 := fun h => by
    have : (1 : ℝ) < ‖w'‖ := hw'; rw [h, norm_zero] at this; linarith
  have h1 : w + w⁻¹ = w' + w'⁻¹ := by
    simp only [jouk] at heq
    have hℓ' : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
    exact mul_left_cancel₀ hℓ' (add_left_cancel heq)
  have h2 : (w - w') * (w * w' - 1) = 0 := by
    have : (w - w') * (w * w' - 1) = (w + w⁻¹ - (w' + w'⁻¹)) * (w * w') := by
      field_simp; ring
    rw [this, h1, sub_self, zero_mul]
  rcases mul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.1 h
  · exfalso
    have : ‖w * w'‖ = 1 := by rw [sub_eq_zero.1 h, norm_one]
    rw [norm_mul] at this
    have h3 : (1 : ℝ) < ‖w‖ := hw
    have h4 : (1 : ℝ) < ‖w'‖ := hw'
    nlinarith

namespace IsBdryExt

variable {B : Set ℂ} {g F : ℂ → ℂ}

/-- **Koebe bound, with slack**: if `bdrySet B F ⊆ [a, b]` and `b − a ≤ 4ℓ`, every two points of
`B` are at distance at most `48 ℓ`. -/
theorem norm_sub_le_of_le (h : IsBdryExt B g F) {a b ℓ : ℝ} (hX : bdrySet B F ⊆ Icc a b)
    (hℓ : 0 < ℓ) (hab : b - a ≤ 4 * ℓ) {e e' : ℂ} (he : e ∈ B) (he' : e' ∈ B) :
    ‖e' - e‖ ≤ 48 * ℓ := by
  rcases eq_or_ne e' e with hee | hee
  · rw [hee, sub_self, norm_zero]; positivity
  obtain ⟨M, hM⟩ := h.norm_reflExt_sub_le
  set c₀ : ℝ := (a + b) / 2 with hc₀
  set J := jouk c₀ ℓ with hJ
  set G : ℂ → ℂ := fun w => reflExt F (J w) with hG
  -- the Joukowski image avoids the boundary set
  have hJout : ∀ w : ℂ, 1 < ‖w‖ → ∀ x : ℝ, J w = x → x ∉ bdrySet B F := by
    intro w hw x hx hxX
    have h1 := jouk_notMem hℓ hw hx
    have h2 := hX hxX
    have : |x - c₀| ≤ 2 * ℓ := abs_le.2 ⟨by linarith [h2.1, h2.2], by linarith [h2.1, h2.2]⟩
    linarith
  have hGd : ∀ w : ℂ, 1 < ‖w‖ → DifferentiableAt ℂ G w := by
    intro w hw
    have hw0 : w ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw; linarith
    have hJd : DifferentiableAt ℂ J w :=
      (differentiableAt_const _).add ((differentiableAt_const _).mul
        (differentiableAt_id.add (differentiableAt_inv hw0)))
    show DifferentiableAt ℂ (reflExt F ∘ J) w
    refine DifferentiableAt.comp w ?_ hJd
    by_cases him : (J w).im = 0
    · have hJeq : J w = ((J w).re : ℂ) := eq_ofReal_re_of_im_eq_zero him
      have hnot := hJout w hw _ hJeq
      have hout : (J w).re < a ∨ b < (J w).re := by
        by_contra hc
        push Not at hc
        have h1 := jouk_notMem hℓ hw hJeq
        have : |(J w).re - c₀| ≤ 2 * ℓ :=
          abs_le.2 ⟨by linarith [hc.1, hc.2], by linarith [hc.1, hc.2]⟩
        linarith
      rw [hJeq]
      rcases hout with ho | ho
      · refine h.differentiableAt_reflExt_of_real (r := a - (J w).re) (by linarith)
          fun y hy hyX => ?_
        have := (hX hyX).1
        rw [abs_lt] at hy
        linarith
      · refine h.differentiableAt_reflExt_of_real (r := (J w).re - b) (by linarith)
          fun y hy hyX => ?_
        have := (hX hyX).2
        rw [abs_lt] at hy
        linarith
    · exact h.differentiableAt_reflExt_of_im_ne him
  have hGinj : InjOn G {w : ℂ | 1 < ‖w‖} := fun w hw w' hw' heq =>
    jouk_injOn hℓ hw hw' (h.reflExt_injOn (hJout w hw) (hJout w' hw') heq)
  have hGB : ∀ w : ℂ, 1 < ‖w‖ → G w ∉ B := fun w hw => h.reflExt_notMem (hJout w hw)
  set K := M + |c₀| + ℓ + ‖e‖ with hK
  have hGbd : ∀ w : ℂ, 1 < ‖w‖ → ‖G w - e - ℓ * w‖ ≤ K := by
    intro w hw
    have hw0 : w ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw; linarith
    have h1 := hM (J w)
    have h2 : ‖w⁻¹‖ ≤ 1 := by rw [norm_inv]; exact inv_le_one_of_one_le₀ hw.le
    calc ‖G w - e - ℓ * w‖ = ‖(reflExt F (J w) - J w) + (c₀ : ℂ) + ℓ * w⁻¹ - e‖ := by
          simp only [hG, hJ, jouk]; ring_nf
      _ ≤ ‖reflExt F (J w) - J w‖ + ‖(c₀ : ℂ)‖ + ‖(ℓ : ℂ) * w⁻¹‖ + ‖e‖ := by
          refine (norm_sub_le _ _).trans ?_
          gcongr
          refine (norm_add_le _ _).trans ?_
          gcongr
          exact norm_add_le _ _
      _ ≤ K := by
          have hℓn : ‖(ℓ : ℂ)‖ = ℓ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hℓ]
          have hcn : ‖(c₀ : ℂ)‖ = |c₀| := by rw [Complex.norm_real, Real.norm_eq_abs]
          rw [norm_mul, hℓn, hcn]
          have : ℓ * ‖w⁻¹‖ ≤ ℓ := by nlinarith
          linarith
  -- the inverted map
  set f : ℂ → ℂ := fun ξ => if ξ = 0 then 0 else (G ξ⁻¹ - e)⁻¹ with hf
  have hξ : ∀ ξ : ℂ, ξ ∈ ball (0 : ℂ) 1 → ξ ≠ 0 → 1 < ‖ξ⁻¹‖ := fun ξ hξ hξ0 => by
    rw [norm_inv]
    exact one_lt_inv₀ (norm_pos_iff.2 hξ0) |>.2 (mem_ball_zero_iff.1 hξ)
  have hne : ∀ ξ : ℂ, ξ ∈ ball (0 : ℂ) 1 → ξ ≠ 0 → G ξ⁻¹ - e ≠ 0 := fun ξ hξ' hξ0 h0 =>
    hGB _ (hξ ξ hξ' hξ0) (by rw [sub_eq_zero.1 h0]; exact he)
  have hfd : DifferentiableOn ℂ f (ball 0 1 \ {0}) := by
    intro ξ hξ'
    have hξ0 : ξ ≠ 0 := hξ'.2
    have hev : f =ᶠ[𝓝 ξ] fun ξ => (G ξ⁻¹ - e)⁻¹ := by
      filter_upwards [isOpen_ne.mem_nhds hξ0] with ζ hζ
      simp [hf, hζ]
    refine (DifferentiableAt.congr_of_eventuallyEq ?_ hev).differentiableWithinAt
    refine ((DifferentiableAt.comp ξ (hGd _ (hξ ξ hξ'.1 hξ0)) (differentiableAt_inv hξ0)).sub_const
      e).inv (hne ξ hξ'.1 hξ0)
  have hderiv : HasDerivAt f (ℓ : ℂ)⁻¹ 0 := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
    have hlim : Tendsto (fun ξ : ℂ => ξ * (G ξ⁻¹ - e)) (𝓝[≠] 0) (𝓝 (ℓ : ℂ)) := by
      have hsmall : Tendsto (fun ξ : ℂ => ξ * (G ξ⁻¹ - e - ℓ * ξ⁻¹)) (𝓝[≠] 0) (𝓝 0) := by
        have hK0 : Tendsto (fun ξ : ℂ => ‖ξ‖ * K) (𝓝[≠] 0) (𝓝 0) := by
          have : Tendsto (fun ξ : ℂ => ‖ξ‖ * K) (𝓝 0) (𝓝 (‖(0 : ℂ)‖ * K)) :=
            (continuous_norm.mul continuous_const).tendsto 0
          rw [norm_zero, zero_mul] at this
          exact this.mono_left nhdsWithin_le_nhds
        refine squeeze_zero_norm' ?_ hK0
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) one_pos)]
          with ξ hξ0 hξb
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hGbd _ (hξ ξ hξb hξ0)) (norm_nonneg _)
      have hcongr : ∀ᶠ ξ in 𝓝[≠] (0 : ℂ), ξ * (G ξ⁻¹ - e) = ξ * (G ξ⁻¹ - e - ℓ * ξ⁻¹) + ℓ := by
        filter_upwards [self_mem_nhdsWithin] with ξ hξ0
        have hξ0' : ξ ≠ 0 := hξ0
        rw [mul_sub, mul_sub, mul_sub, ← mul_assoc, mul_comm ξ (ℓ : ℂ), mul_assoc,
          mul_inv_cancel₀ hξ0']
        ring
      have := hsmall.add_const (ℓ : ℂ)
      rw [zero_add] at this
      exact this.congr' (hcongr.mono fun ξ h => h.symm)
    refine (hlim.inv₀ hℓ0).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ξ hξ0
    have hξ0' : ξ ≠ 0 := hξ0
    have hf0 : f 0 = 0 := by simp [hf]
    have hfξ : f ξ = (G ξ⁻¹ - e)⁻¹ := by simp [hf, hξ0']
    rw [slope_def_field, hf0, hfξ, sub_zero, sub_zero, mul_inv, div_eq_mul_inv, mul_comm]
  have hfD : DifferentiableOn ℂ f (ball 0 1) :=
    (differentiableOn_compl_singleton_and_continuousAt_iff (ball_mem_nhds (0 : ℂ) one_pos)).1
      ⟨hfd, hderiv.continuousAt⟩
  have hfinj : InjOn f (ball 0 1) := by
    intro ξ hξ' ζ hζ heq
    by_cases hξ0 : ξ = 0 <;> by_cases hζ0 : ζ = 0
    · rw [hξ0, hζ0]
    · simp only [hf, hξ0, hζ0, ite_true, ite_false] at heq
      exact absurd heq.symm (inv_ne_zero (hne ζ hζ hζ0))
    · simp only [hf, hξ0, hζ0, ite_true, ite_false] at heq
      exact absurd heq (inv_ne_zero (hne ξ hξ' hξ0))
    · simp only [hf, hξ0, hζ0, ite_false] at heq
      have h1 := inv_injective heq
      have h2 : G ξ⁻¹ = G ζ⁻¹ := by linear_combination h1
      have := hGinj (hξ ξ hξ' hξ0) (hξ ζ hζ hζ0) h2
      exact inv_injective this
  have hkoebe := QuantumZipper.CA.Koebe.ball_subset_image_koebe hfD hfinj
  rw [hderiv.deriv, show f 0 = 0 by simp [hf], norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hℓ, QuantumZipper.CA.Koebe.koebeCovConst] at hkoebe
  have hnot : (e' - e)⁻¹ ∉ f '' ball 0 1 := by
    rintro ⟨ξ, hξb, hfξ⟩
    by_cases hξ0 : ξ = 0
    · simp only [hf, hξ0, ite_true] at hfξ
      exact inv_ne_zero (sub_ne_zero.2 hee) hfξ.symm
    · simp only [hf, hξ0, ite_false] at hfξ
      have h1 := inv_injective hfξ
      exact hGB _ (hξ ξ hξb hξ0) (by rw [show G ξ⁻¹ = e' by linear_combination h1]; exact he')
  have hfar : ¬ ‖(e' - e)⁻¹‖ < 1 / 48 * 1 * ℓ⁻¹ := fun hlt =>
    hnot (hkoebe (mem_ball_zero_iff.2 hlt))
  push Not at hfar
  rw [norm_inv] at hfar
  have hpos : 0 < ‖e' - e‖ := norm_pos_iff.2 (sub_ne_zero.2 hee)
  rw [mul_one, ← div_eq_mul_inv, div_le_iff₀ hℓ] at hfar
  rw [inv_mul_eq_div, le_div_iff₀ hpos] at hfar
  linarith

/-- **Koebe bound** ([Law05, (3.13)]): if `bdrySet B F ⊆ [a, b]`, every two points of `B` are at
distance at most `12 (b − a)`. -/
theorem norm_sub_le (h : IsBdryExt B g F) {a b : ℝ} (hX : bdrySet B F ⊆ Icc a b) (hab : a ≤ b)
    {e e' : ℂ} (he : e ∈ B) (he' : e' ∈ B) : ‖e' - e‖ ≤ 12 * (b - a) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := h.norm_sub_le_of_le hX (ℓ := (b - a) / 4 + ε / 48) (by positivity) (by linarith) he he'
  linarith

end IsBdryExt

end YuanCharacterisation

end InteractingSLE

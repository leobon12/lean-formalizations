/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSelFull

/-!
# §7.4, Aux. lemma 117 before a stopping lifetime: the local Tanaka step and the cover argument

Packet PROVE-STRIPSYS5 (specification §7.4, Aux. lemma 117, `source/spec/p337-384.md` L897–L939, and Aux. lemma 122,
whose hypotheses hold only before the stopping lifetime `T` of the trace).

The driver decomposes as `W = a β − ½ ∑ ρ (V − x)` with a Brownian motion `β` only **up to a stopping time `ς`**
(after the lifetime, `β` is the independent continuation of `PhaseSelFullLevy`), and the initial word `x` is random.

* `ae_forceDefect_const_of_group_before`: the landed local Tanaka step
  (`MartChar.ae_forceDefect_const_of_group`), localized at `ς` — the decomposition is used only on `[s, t ∧ ς]`;
* `GroupConstBefore`, `forceDefect_eq_zero_of_groupConstBefore_of_colliderNe`: the cover argument of Aux. lemma 117
  (`Aux117.forceDefect_eq_zero_of_groupConst_of_colliderNe`) using the group constancy only before a time `e`;
* `ae_forceDefect_left_eq_zero_before`, `ae_forceDefect_right_eq_zero_before`: almost surely, no singular motion at
  any time `T < ς` before which every colliding group has total weight `≠ −2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSelFull

open MartChar Aux117

/-- `IsTanakaPathOn` depends on the Brownian path only on `[s, e]`. -/
theorem isTanakaPathOn_congr_β {a c : ℝ} {s e : ℝ≥0} {x β β' j b ψ : ℝ≥0 → ℝ}
    (h : LocalTime.IsTanakaPathOn a c s e x β j b ψ) (hβ : ∀ u ∈ Icc s e, β u = β' u) :
    LocalTime.IsTanakaPathOn a c s e x β' j b ψ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h1, h2.congr fun u hu => (hβ u hu).symm, h3, h4, h5, fun u hu => ?_, h7, h8, h9⟩
  have hs : s ∈ Icc s e := ⟨le_rfl, hu.1.trans hu.2⟩
  rw [← hβ u hu, ← hβ s hs]
  exact h6 u hu

section Tanaka

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}

/-- **The local Tanaka step up to a stopping time `ς`** (the landed `MartChar.ae_forceDefect_const_of_group` with the
decomposition `W = a β − ½ ∑ ρ (V − x)` assumed only up to `ς`, and a random initial word `x`): almost surely, on the
group event at `s`, the defect of the nearest left point is constant on `[s, u]` for every `u ≤ t ∧ ς` before which
the group does not change and no right point meets the driver. -/
theorem ae_forceDefect_const_of_group_before {P : Measure Ω} [IsProbabilityMeasure P] {a : ℝ}
    (ha : a ≠ 0) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    {β : ℝ≥0 → Ω → ℝ} (hβ : IsFilteredPreBrownian β 𝓕 P)
    {ς : Ω → WithTop ℝ≥0} (hς : IsStoppingTime 𝓕 ς)
    (hW : ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ ς ω → W t ω = a * β t ω
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL ω i)) + ∑ j, ρR j * (VR j t ω - xR ω j)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hpL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hantiL : ∀ ω i, Antitone fun t => VL i t ω)
    (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hmerge : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    {i₀ : Fin nL} (hi₀ : ∀ ω t i, VL i t ω ≤ VL i₀ t ω) (S : Finset (Fin nL))
    (hS : 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0) {s t : ℝ≥0} (hst : s ≤ t) :
    ∀ᵐ ω ∂P, (∀ i, VL i s ω = VL i₀ s ω ↔ i ∈ S) → ∀ u, s ≤ u → u ≤ t → (u : WithTop ℝ≥0) ≤ ς ω →
      (∀ r, s ≤ r → r ≤ u → (∀ i ∉ S, VL i r ω ≠ VL i₀ r ω) ∧ ∀ j, VR j r ω ≠ W r ω) →
      forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u
        = forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) s := by
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpL ω i).1
  have hVRc : ∀ j ω, Continuous fun t => VR j t ω := fun j ω => (hpR ω j).1
  set τ₀ := groupStop W VL VR i₀ S s with hτ₀def
  have hτ₀ : IsStoppingTime 𝓕 τ₀ := isStoppingTime_groupStop hWc hVLc hVRc hWa hVLa hVRa i₀ S s
  set τ : Ω → WithTop ℝ≥0 := fun ω => min (τ₀ ω) (ς ω) with hτdef
  have hτ : IsStoppingTime 𝓕 τ := hτ₀.min hς
  have hgc := continuous_groupStopProc hWc hVLc hVRc i₀ S
  have hX : ∀ u, Measurable[𝓕 u] fun ω => W u ω - VL i₀ u ω := fun u =>
    (hWa u).measurable.sub (hVLa i₀ u).measurable
  have hJ : ∀ u, Measurable[𝓕 u] fun ω => -forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u :=
    fun u => (measurable_forceDefect hWc (hVLc i₀) hWa (hVLa i₀) u).neg
  have hψ : ∀ u, Measurable[𝓕 u] fun ω =>
      groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ u := fun u => by
    simp only [groupDom]
    exact ((Finset.measurable_sum _ fun i _ => ((hVLa i u).measurable.neg.const_mul _)).add
      (Finset.measurable_sum _ fun j _ => ((hVRa j u).measurable.const_mul _))).sub
        (hVLa i₀ u).measurable
  have hP : ∀ᵐ ω ∂P, (s : WithTop ℝ≥0) ≤ τ ω →
      LocalTime.IsTanakaPathOn a (1 + (1 / 2) * ∑ i ∈ S, ρL i) s (LocalTime.stopEnd τ t ω)
        ((fun u ω => W u ω - VL i₀ u ω) · ω) (β · ω)
        ((fun u ω => -forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u) · ω)
        ((fun u ω => groupDrift ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) i₀ u) · ω)
        ((fun u ω => groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ u) · ω) := by
    refine Eventually.of_forall fun ω hsτω => ?_
    classical
    have heς : (LocalTime.stopEnd τ t ω : WithTop ℝ≥0) ≤ ς ω :=
      (LocalTime.coe_stopEnd_le τ t ω).trans (min_le_right _ _)
    set β' : ℝ≥0 → ℝ := fun u => (W u ω + (1 / 2) * ((∑ i, ρL i * (VL i u ω - xL ω i)) +
      ∑ j, ρR j * (VR j u ω - xR ω j))) / a with hβ'
    have hw' : ∀ u, W u ω = a * β' u
        - (1 / 2) * ((∑ i, ρL i * (VL i u ω - xL ω i)) + ∑ j, ρR j * (VR j u ω - xR ω j)) := fun u => by
      simp only [hβ']; field_simp; ring
    have hβ'c : Continuous β' := by
      simp only [hβ']
      have h1 := hWc ω
      have h2 := fun i => hVLc i ω
      have h3 := fun j => hVRc j ω
      fun_prop
    have hββ' : ∀ u ∈ Icc s (LocalTime.stopEnd τ t ω), β' u = β u ω := fun u hu => by
      have h := hW u ω ((WithTop.coe_le_coe.2 hu.2).trans heς)
      simp only [hβ']
      rw [div_eq_iff ha]
      linarith
    refine isTanakaPathOn_congr_β ?_ hββ'
    by_cases hE : ω ∈ groupEvent VL i₀ S s
    · have hτω : τ₀ ω = zeroHit (groupStopProc W VL VR i₀ S) s ω := by
        rw [hτ₀def, groupStop, Set.piecewise_eq_of_mem _ _ _ hE]
      have hlt : ∀ u, u < LocalTime.stopEnd τ t ω → (u : WithTop ℝ≥0) < τ₀ ω := fun u hu =>
        (WithTop.coe_lt_coe.2 hu).trans_le ((LocalTime.coe_stopEnd_le τ t ω).trans (min_le_left _ _))
      have hne : ∀ u, s ≤ u → u < LocalTime.stopEnd τ t ω →
          (∀ i ∉ S, VL i u ω ≠ VL i₀ u ω) ∧ ∀ j, VR j u ω ≠ W u ω := fun u hsu hu =>
        (groupStopProc_ne_zero_iff i₀ S u ω).1
          (ne_zero_of_lt_zeroHit hgc hsu (hτω ▸ hlt u hu))
      exact isTanakaPathOn_group (xL := xL ω) (xR := xR ω) hw' hβ'c (hWc ω)
        (hpL ω) (hpR ω) (hordL ω) (hantiL ω) (hmonoR ω) (hmerge ω) (hi₀ ω)
        (LocalTime.s_le_stopEnd hst hsτω) (fun i hi => (hE i).2 hi)
        (fun u hsu hu => (hne u hsu hu).1) (fun u hsu hu => (hne u hsu hu).2)
    · have hτω : τ₀ ω = (s : WithTop ℝ≥0) := by
        rw [hτ₀def, groupStop, Set.piecewise_eq_of_notMem _ _ _ hE]
      have hτs : τ ω = (s : WithTop ℝ≥0) :=
        le_antisymm ((min_le_left _ _).trans hτω.le) hsτω
      have he : LocalTime.stopEnd τ t ω = s := by
        simp only [LocalTime.stopEnd, hτs]
        exact min_eq_right hst
      rw [he]
      exact isTanakaPathOn_self _ _ _ _ _ _ _ _
  have hnn : ∀ᵐ ω ∂P, (s : WithTop ℝ≥0) ≤ τ ω →
      ∀ u ∈ Icc s (LocalTime.stopEnd τ t ω), 0 ≤ W u ω - VL i₀ u ω :=
    Eventually.of_forall fun ω _ u _ => sub_nonneg.2 (hordL ω u i₀)
  have hrec : ∀ᵐ ω ∂P, (s : WithTop ℝ≥0) ≤ τ ω →
      IntervalIntegrable (fun r : ℝ => (W r.toNNReal ω - VL i₀ r.toNNReal ω)⁻¹) volume s
        (LocalTime.stopEnd τ t ω) ∧
      ∀ u ∈ Icc s (LocalTime.stopEnd τ t ω), ∫ r in (s : ℝ)..u,
        (W r.toNNReal ω - VL i₀ r.toNNReal ω)⁻¹
          ≤ groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ u
            - groupDom ρL ρR (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ s :=
    Eventually.of_forall fun ω hsτω => intervalIntegrable_inv_and_le_groupDom (hpL ω) (hordL ω)
      (hantiL ω) (hmonoR ω) i₀ (LocalTime.s_le_stopEnd hst hsτω)
  have hmain := LocalTime.ae_singular_const_stopped hβ hst hτ hX hJ hψ ha hS hP hnn hrec
  filter_upwards [hmain] with ω hω hE u hsu hut huς hgood
  classical
  have hE' : ω ∈ groupEvent VL i₀ S s := hE
  have hτω : τ₀ ω = zeroHit (groupStopProc W VL VR i₀ S) s ω := by
    rw [hτ₀def, groupStop, Set.piecewise_eq_of_mem _ _ _ hE']
  have hu : (u : WithTop ℝ≥0) ≤ τ₀ ω := by
    rw [hτω]
    exact (lt_zeroHit_of_forall_ne hgc fun r hsr hru =>
      (groupStopProc_ne_zero_iff i₀ S r ω).2 (hgood r hsr hru)).le
  exact neg_inj.1 (hω u hsu hut (le_min hu huς))

end Tanaka

section Cover


variable {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}

/-- The pathwise conclusion of the local Tanaka steps before the time `e` (`MartChar.GroupConst` for `u ≤ e`). -/
def GroupConstBefore (ρL : Fin nL → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin nR → ℝ≥0 → ℝ) (i₀ : Fin nL) (e : WithTop ℝ≥0) : Prop :=
  ∀ S : Finset (Fin nL), 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0 → ∀ q : ℚ, 0 ≤ q →
    (∀ i, vL i (q : ℝ).toNNReal = vL i₀ (q : ℝ).toNNReal ↔ i ∈ S) → ∀ u, (q : ℝ).toNNReal ≤ u →
    (u : WithTop ℝ≥0) ≤ e →
    (∀ r, (q : ℝ).toNNReal ≤ r → r ≤ u → (∀ i ∉ S, vL i r ≠ vL i₀ r) ∧ ∀ j, vR j r ≠ w r) →
    forceDefect w (vL i₀) u = forceDefect w (vL i₀) (q : ℝ).toNNReal

/-- **The cover argument before a time `e`** (the pathwise `Aux117.forceDefect_eq_zero_of_groupConst_of_colliderNe`
using the group constancy only up to `e`): the nearest left point has no singular motion up to `T ≤ e` while every
colliding left group has total weight `≠ −2`. -/
theorem forceDefect_eq_zero_of_groupConstBefore_of_colliderNe (hwc : Continuous w)
    (hpL : ∀ i, IsForcePath w (vL i)) (hpR : ∀ j, IsForcePath w (vR j))
    (hmerge : ∀ i j s t, s ≤ t → vL i s = vL j s → vL i t = vL j t) {i₀ : Fin nL}
    (hsep : ∀ t, 0 < t → vL i₀ t = w t → ∀ j, vR j t ≠ w t)
    {e : WithTop ℝ≥0} (hgood : GroupConstBefore ρL w vL vR i₀ e) {T : ℝ≥0} (hTe : (T : WithTop ℝ≥0) ≤ e)
    (hT : ∀ u, 0 < u → u ≤ T → ColliderNe ρL w vL u) :
    forceDefect w (vL i₀) T = 0 := by
  have hcL : ∀ i, Continuous (vL i) := fun i => (hpL i).1
  have hcR : ∀ j, Continuous (vR j) := fun j => (hpR j).1
  set f : ℝ → ℝ := fun y => forceDefect w (vL i₀) y.toNNReal with hf
  set m : Fin nL → ℝ := fun i => ((sInf {r : ℝ≥0 | vL i r = vL i₀ r} : ℝ≥0) : ℝ) with hm
  have hFc : (insert (0 : ℝ) (range m)).Countable := (countable_range m).insert 0
  have hfc : Continuous f := (hpL i₀).continuous_forceDefect.comp continuous_real_toNNReal
  have hd : ∀ x ∈ Ioo (0 : ℝ) T \ insert (0 : ℝ) (range m), HasDerivAt f 0 x := by
    rintro x ⟨⟨hx0, hxT⟩, hxF⟩
    have hxm : ∀ i, m i ≠ x := fun i h => hxF (Or.inr ⟨i, h⟩)
    set u := x.toNNReal with hu
    have hux : (u : ℝ) = x := Real.coe_toNNReal _ hx0.le
    have huT : u ≤ T := Real.toNNReal_le_iff_le_coe.2 hxT.le
    have hu0 : 0 < u := Real.toNNReal_pos.2 hx0
    have hcont : ∀ g : ℝ≥0 → ℝ, Continuous g → ContinuousAt (fun y : ℝ => g y.toNNReal) x :=
      fun g hg => (hg.comp continuous_real_toNNReal).continuousAt
    have hne2 : ∀ g₁ g₂ : ℝ≥0 → ℝ, Continuous g₁ → Continuous g₂ → g₁ u ≠ g₂ u →
        ∀ᶠ y in 𝓝 x, g₁ y.toNNReal ≠ g₂ y.toNNReal := fun g₁ g₂ h1 h2 h =>
      (((hcont _ h1).sub (hcont _ h2)).eventually_ne
        (sub_ne_zero.2 h : g₁ x.toNNReal - g₂ x.toNNReal ≠ 0)).mono fun y hy => sub_ne_zero.1 hy
    by_cases hcol : vL i₀ u = w u
    · -- a collision: use the local Tanaka step on a group interval
      set S := Finset.univ.filter fun i => vL i u = vL i₀ u with hSdef
      have hSw : (Finset.univ.filter fun i => vL i u = w u) = S :=
        Finset.filter_congr fun i _ => by rw [hcol]
      have hc : 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0 := by
        have h : (∑ i ∈ S, ρL i) ≠ -2 := by
          have := hT u hu0 huT
          rwa [ColliderNe, hSw] at this
        intro h0
        exact h (by linarith)
      have hsepu := hsep u hu0 hcol
      have hE1 : ∀ᶠ y in 𝓝 x, ∀ j, vR j y.toNNReal ≠ w y.toNNReal :=
        Filter.eventually_all.2 fun j => hne2 _ _ (hcR j) hwc (hsepu j)
      have hE2 : ∀ᶠ y in 𝓝 x, ∀ i ∉ S, vL i y.toNNReal ≠ vL i₀ y.toNNReal := by
        refine Filter.eventually_all.2 fun i => ?_
        by_cases hi : i ∈ S
        · exact Eventually.of_forall fun y h => absurd hi h
        · have hne : vL i u ≠ vL i₀ u := by simpa [hSdef] using hi
          exact (hne2 _ _ (hcL i) (hcL i₀) hne).mono fun y hy _ => hy
      have hE3 : ∀ᶠ y in 𝓝 x, ∀ i ∈ S, vL i y.toNNReal = vL i₀ y.toNNReal := by
        refine Filter.eventually_all.2 fun i => ?_
        by_cases hi : i ∈ S
        · have hiu : vL i u = vL i₀ u := by simpa [hSdef] using hi
          have hle : sInf {r : ℝ≥0 | vL i r = vL i₀ r} ≤ u := csInf_le (OrderBot.bddBelow _) hiu
          have hlt : sInf {r : ℝ≥0 | vL i r = vL i₀ r} < u := by
            refine lt_of_le_of_ne hle fun h => hxm i ?_
            simp only [hm, h, hux]
          obtain ⟨r, hr, hru⟩ := exists_lt_of_csInf_lt ⟨u, hiu⟩ hlt
          have hrx : (r : ℝ) < x := by rw [← hux]; exact_mod_cast hru
          filter_upwards [Ioi_mem_nhds hrx] with y hy _
          exact hmerge i i₀ r _ ((Real.le_toNNReal_iff_coe_le
            ((NNReal.coe_nonneg r).trans hy.le)).2 hy.le) hr
        · exact Eventually.of_forall fun y h => absurd h hi
      obtain ⟨ε, hε, hP⟩ := exists_pos_forall_of_eventually
        (p := fun r => (∀ j, vR j r ≠ w r) ∧ (∀ i ∉ S, vL i r ≠ vL i₀ r) ∧
          ∀ i ∈ S, vL i r = vL i₀ r) (hE1.and (hE2.and hE3))
      set ε' := min (min ε x) ((T : ℝ) - x) with hε'
      have hε'1 : ε' ≤ ε := (min_le_left _ _).trans (min_le_left _ _)
      have hε'2 : ε' ≤ x := (min_le_left _ _).trans (min_le_right _ _)
      have hε'3 : ε' ≤ (T : ℝ) - x := min_le_right _ _
      refine hasDerivAt_toNNReal_of_const (ε := ε') hx0 (lt_min (lt_min hε hx0) (sub_pos.2 hxT))
        fun a b hab ha hb => ?_
      have hbT : (b : WithTop ℝ≥0) ≤ e := by
        refine (WithTop.coe_le_coe.2 ?_).trans hTe
        have : (b : ℝ) ≤ T := by linarith [(abs_lt.1 hb).2]
        exact_mod_cast this
      have haT : (a : WithTop ℝ≥0) ≤ e := (WithTop.coe_le_coe.2 hab).trans hbT
      have ha' : x - ε' < a := by linarith [(abs_lt.1 ha).1]
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha'
      have hq0 : (0 : ℝ) ≤ q := by linarith
      set s := (q : ℝ).toNNReal with hsdef
      have hqs : (s : ℝ) = q := Real.coe_toNNReal _ hq0
      have hPr : ∀ r : ℝ≥0, s ≤ r → r ≤ b → (∀ j, vR j r ≠ w r) ∧ (∀ i ∉ S, vL i r ≠ vL i₀ r) ∧
          ∀ i ∈ S, vL i r = vL i₀ r := fun r h1 h2 => by
        refine hP r (abs_lt.2 ⟨?_, ?_⟩)
        · have : (q : ℝ) ≤ r := hqs ▸ NNReal.coe_le_coe.2 h1
          linarith
        · have : (r : ℝ) ≤ b := h2
          linarith [(abs_lt.1 hb).2]
      have hsa : s ≤ a := NNReal.coe_le_coe.1 (hqs ▸ hq2.le)
      have hgrp : ∀ i, vL i s = vL i₀ s ↔ i ∈ S := fun i => by
        obtain ⟨-, h2, h3⟩ := hPr s le_rfl (hsa.trans hab)
        refine ⟨fun h => ?_, h3 i⟩
        by_contra hi
        exact h2 i hi h
      have hq0' : (0 : ℚ) ≤ q := by exact_mod_cast hq0
      have hb' := hgood S hc q hq0' hgrp b (hsa.trans hab) hbT
        fun r h1 h2 => ⟨(hPr r h1 h2).2.1, (hPr r h1 h2).1⟩
      have ha'' := hgood S hc q hq0' hgrp a hsa haT
        fun r h1 h2 => ⟨(hPr r h1 (h2.trans hab)).2.1, (hPr r h1 (h2.trans hab)).1⟩
      exact ha''.trans hb'.symm
    · -- no collision: the defect is locally constant
      have hev := hne2 _ _ (hcL i₀) hwc hcol
      obtain ⟨ε, hε, hP⟩ := exists_pos_forall_of_eventually (p := fun r => vL i₀ r ≠ w r) hev
      refine hasDerivAt_toNNReal_of_const hx0 hε fun a b hab ha hb => ?_
      exact ((hpL i₀).forceDefect_eq_of_forall_ne hab fun r hr =>
        hP r (abs_sub_lt_of_mem_Icc ha hb hr.1 hr.2)).symm
  have hint := integral_eq_of_hasDerivAt_off_countable_of_le f (fun _ => (0 : ℝ))
    (NNReal.coe_nonneg T) hFc hfc.continuousOn hd intervalIntegrable_const
  simp only [intervalIntegral.integral_zero, hf, Real.toNNReal_coe, Real.toNNReal_zero] at hint
  have h0 : forceDefect w (vL i₀) 0 = 0 := by simp [forceDefect]
  linarith

end Cover

section AlmostSure

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {β W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ}


/-- **Aux. lemma 117 before a stopping time `ς`, the singular motions vanish: left side** ((NC9.5) with `r ≠ −2`;
the decomposition of the driver is assumed only up to `ς`, the initial word is random). -/
theorem ae_forceDefect_left_eq_zero_before {a : ℝ} (ha : a ≠ 0)
    (hβ : IsFilteredPreBrownian β 𝓕 P) {ς : Ω → WithTop ℝ≥0} (hς : IsStoppingTime 𝓕 ς)
    (hW : ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ ς ω → W t ω = a * β t ω
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL ω i)) + ∑ j, ρR j * (VR j t ω - xR ω j)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hpL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω))
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hantiL : ∀ ω i, Antitone fun t => VL i t ω)
    (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hmerge : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω)
    (hidxL : ∀ ω t, Antitone fun i => VL i t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : WithTop ℝ≥0) ≤ ς ω →
      (∀ u, 0 < u → u ≤ T → ColliderNe ρL (fun t => W t ω) (fun i t => VL i t ω) u) →
      ∀ i, forceDefect (fun t => W t ω) (fun t => VL i t ω) T = 0 := by
  rcases Nat.eq_zero_or_pos nL with hn | hn
  · subst hn
    exact Eventually.of_forall fun ω T _ _ i => i.elim0
  set i₀ : Fin nL := ⟨0, hn⟩ with hi₀def
  have hi₀ : ∀ ω t i, VL i t ω ≤ VL i₀ t ω := fun ω t i =>
    hidxL ω t (show i₀ ≤ i from Nat.zero_le _)
  have hloc : ∀ (S : Finset (Fin nL)) (q : ℚ) (t : ℕ), ∀ᵐ ω ∂P,
      1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0 → 0 ≤ q →
      (∀ i, VL i (q : ℝ).toNNReal ω = VL i₀ (q : ℝ).toNNReal ω ↔ i ∈ S) →
      ∀ u, (q : ℝ).toNNReal ≤ u → u ≤ t → (u : WithTop ℝ≥0) ≤ ς ω →
      (∀ r, (q : ℝ).toNNReal ≤ r → r ≤ u →
        (∀ i ∉ S, VL i r ω ≠ VL i₀ r ω) ∧ ∀ j, VR j r ω ≠ W r ω) →
      forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u
        = forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) (q : ℝ).toNNReal := by
    intro S q t
    by_cases hS : 1 + (1 / 2) * ∑ i ∈ S, ρL i ≠ 0
    · by_cases hst : (q : ℝ).toNNReal ≤ (t : ℝ≥0)
      · filter_upwards [ae_forceDefect_const_of_group_before ha hβ hς hW hWc hWa hVLa hVRa hpL hpR
          hordL hantiL hmonoR hmerge hi₀ S hS hst] with ω hω _ _ hgrp u h1 h2 h3 h4
        exact hω hgrp u h1 h2 h3 h4
      · exact Eventually.of_forall fun ω _ _ _ u h1 h2 _ _ => absurd (h1.trans h2) hst
    · exact Eventually.of_forall fun ω h => absurd h hS
  have hall := ae_all_iff.2 fun S => ae_all_iff.2 fun q => ae_all_iff.2 fun t => hloc S q t
  filter_upwards [hall] with ω hω T hTς hT i
  have hgood : GroupConstBefore ρL (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) i₀ (ς ω) :=
    fun S hS q hq hgrp u hsu huς hcond => hω S q ⌈u⌉₊ hS hq hgrp u hsu (Nat.le_ceil u) huς hcond
  have h0 : ∀ u ≤ T, forceDefect (fun t => W t ω) (fun t => VL i₀ t ω) u = 0 := fun u hu =>
    forceDefect_eq_zero_of_groupConstBefore_of_colliderNe (ρL := ρL) (hWc ω) (hpL ω) (hpR ω) (hmerge ω)
      (fun t ht hcol j => hsep ω t ht i₀ j hcol) hgood ((WithTop.coe_le_coe.2 hu).trans hTς)
      fun v hv0 hv => hT v hv0 (hv.trans hu)
  exact forceDefect_eq_zero_of_nearest (hpL ω) (hordL ω) (hmerge ω) (hi₀ ω) h0 i

/-- **Aux. lemma 117 before a stopping time `ς`, the singular motions vanish: right side** (by reflection). -/
theorem ae_forceDefect_right_eq_zero_before {a : ℝ} (ha : a ≠ 0)
    (hβ : IsFilteredPreBrownian β 𝓕 P) {ς : Ω → WithTop ℝ≥0} (hς : IsStoppingTime 𝓕 ς)
    (hW : ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ ς ω → W t ω = a * β t ω
      - (1 / 2) * ((∑ i, ρL i * (VL i t ω - xL ω i)) + ∑ j, ρR j * (VR j t ω - xR ω j)))
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓕 W)
    (hVLa : ∀ i, StronglyAdapted 𝓕 (VL i)) (hVRa : ∀ j, StronglyAdapted 𝓕 (VR j))
    (hpL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω))
    (hpR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω))
    (hordR : ∀ ω t j, W t ω ≤ VR j t ω) (hantiL : ∀ ω i, Antitone fun t => VL i t ω)
    (hmonoR : ∀ ω j, Monotone fun t => VR j t ω)
    (hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω)
    (hidxR : ∀ ω t, Monotone fun j => VR j t ω)
    (hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : WithTop ℝ≥0) ≤ ς ω →
      (∀ u, 0 < u → u ≤ T → ColliderNe ρR (fun t => W t ω) (fun j t => VR j t ω) u) →
      ∀ j, forceDefect (fun t => W t ω) (fun t => VR j t ω) T = 0 := by
  have hW' : ∀ (t : ℝ≥0) ω, (t : WithTop ℝ≥0) ≤ ς ω → -W t ω = -a * β t ω
      - (1 / 2) * ((∑ j, ρR j * (-VR j t ω - -xR ω j)) + ∑ i, ρL i * (-VL i t ω - -xL ω i)) := by
    intro t ω htς
    have h1 : ∀ j, ρR j * (-VR j t ω - -xR ω j) = -(ρR j * (VR j t ω - xR ω j)) := fun j => by ring
    have h2 : ∀ i, ρL i * (-VL i t ω - -xL ω i) = -(ρL i * (VL i t ω - xL ω i)) := fun i => by ring
    rw [hW t ω htς]
    simp only [h1, h2, Finset.sum_neg_distrib]
    ring
  have h := ae_forceDefect_left_eq_zero_before (P := P) (a := -a) (neg_ne_zero.2 ha) (ρL := ρR)
    (ρR := ρL) (xL := fun ω j => -xR ω j) (xR := fun ω i => -xL ω i) (W := fun t ω => -W t ω)
    (VL := fun j t ω => -VR j t ω) (VR := fun i t ω => -VL i t ω) hβ hς hW'
    (fun ω => (hWc ω).neg) (fun t => (hWa t).neg) (fun j t => (hVRa j t).neg)
    (fun i t => (hVLa i t).neg) (fun ω j => (hpR ω j).neg) (fun ω i => (hpL ω i).neg)
    (fun ω t j => neg_le_neg (hordR ω t j)) (fun ω j => (hmonoR ω j).neg)
    (fun ω i => (hantiL ω i).neg)
    (fun ω i j s t hst h => by rw [neg_inj] at h ⊢; exact hmergeR ω i j s t hst h)
    (fun ω t => (hidxR ω t).neg)
    (fun ω t ht j i h1 h2 => hsep ω t ht i j (neg_inj.1 h2) (neg_inj.1 h1))
  filter_upwards [h] with ω hω T hTς hT j
  have := hω T hTς (fun u hu0 hu => (colliderNe_neg_iff ρR (fun t => W t ω) (fun j t => VR j t ω) u).2
    (hT u hu0 hu)) j
  rw [forceDefect_neg] at this
  exact neg_eq_zero.1 this

end AlmostSure

end PhaseSelFull

end Sec7

end InteractingSLE

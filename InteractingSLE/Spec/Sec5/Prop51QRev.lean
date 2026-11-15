/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418Side
import InteractingSLE.Spec.Sec5.Cond44RefSide

/-!
# Proposition 5.1 in the chart `Q`: the no-wrap step read in the flow line's own Loewner chart

Packet PROVE-SEC5-P. Specification §5, Proposition 5.1 and its proof (`source/spec/p097-144.md`, pp. 128–135), in
Lemma 4.5's chart `Q` (PROVE-SEC5-N, `Cond44Ref.Prop51QStatement`): the flow line `γ` (a simple proper arc from `0` to
`∞`) and the counterflow line `c` (from `∞` to `0`).

The conclusion of Proposition 5.1 is "`γ` passes to the left of `c`": no point of `c` lies on the left side
`leftSideOf (arcRange γ)` of `γ`. This file proves the deterministic step that turns a boundary-avoidance statement for
the counterflow, read in the Loewner chart `f_t = g_t − W_t` of the flow-line prefix `γ(0, t]`, into that conclusion.

**The left part of `∂(ℍ \ γ(0, t])`.** In the chart `f_t` the left side of the slit `γ(0, t]` is the interval
`(L_t − W_t, 0)` and `ℝ₋` is `(−∞, L_t − W_t)`; together they are the negative half-line. The line `c` **hits the left
part** along a filter `F` of times (`HitsLeftPartAlong`) when, along `F` restricted to the times at which `c` is off
the slit, `f_t ∘ c` has a negative real cluster point. `NoLeftPartHit W t c Z`: this never happens when approaching an
alive time from the past, nor at the end of the life (`u ↑ Z`).

**The no-wrap theorem** (`notMem_leftSideOf_of_noLeftPartHit`). Let `γ` be a simple proper Loewner trace of a
continuous driver `W` (`W 0 = 0`), and `c` a line which is continuous on its alive times and tends to `0` at the end
of its life. If for every positive rational `t` the line `c` never hits the left part of `∂(ℍ \ γ(0, t])`, then no
alive point of `c` lies on the left side of `γ`.

*Proof.* Suppose `c(u)` is on the left side `L`. Either `c` stays in `L` from `u` to the end of its life, or there is a
first time `v₁ > u` with `c(v₁) ∉ L`. In the second case `p = c(v₁)` is in `closure L \ L`, so it is a real point or a
point `γ(s)`, `s > 0` (`L` is a union of components of `ℍ \ γ`); take a rational `t > s` (any `t` for a real `p`). In
the first case `c → 0 = γ(0)`. In both cases `p` is off `ℍ \ γ(0, t]`, distinct from the tip `γ(t)`, and approached
from inside `L`. Along an ultrafilter of such an approach, `f_t` converges to a point `y` of `ℍ̄` with `F̄_t(y) = p`
(`WangWu.exists_tendsto_fwdMap_ultrafilter`). `y` is real (`F̄_t` maps `ℍ` into `ℍ \ γ(0, t]`), `y ≠ 0`
(`F̄_t(0) = γ(t)`), and `y` is adherent to `f_t(L)`, which lies on the left side of the mapped future
(`WangWu.fwdMap_mem_leftSideOf_futureArc`), so `y` is not positive. Hence `y < 0`: a hit of the left part. ∎

This is the counterflow-side reading of the no-wrap step. It replaces the strip argument of the source (pp. 134–135),
whose corrected form needs a terminal alternative not covered by PROVE-SEC5-K's correction (see the handoff of
PROVE-SEC5-P): the flow line may touch the left side of `K′_{τ′}`, pass around its tip without touching it and end at
`z₀` from the east, which no first-hit statement on the sides of `K′_{τ′}` excludes.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop51Q

open WangWu

/-! ### Alive times and the terminal filter -/

/-- The alive positive real times of a line with lifetime `Z`. -/
def aliveSet (Z : ℝ≥0∞) : Set ℝ := {u | 0 < u ∧ ENNReal.ofReal u < Z}

/-- The terminal filter `u ↑ Z` of real times (`u → ∞` when `Z = ∞`). -/
def termFilter (Z : ℝ≥0∞) : Filter ℝ := Filter.comap ENNReal.ofReal (𝓝[<] Z)

theorem isOpen_aliveSet (Z : ℝ≥0∞) : IsOpen (aliveSet Z) :=
  (isOpen_lt continuous_const continuous_id).inter (isOpen_lt ENNReal.continuous_ofReal continuous_const)

theorem ofReal_lt_of_le_of_mem_aliveSet {Z : ℝ≥0∞} {v w : ℝ} (hvw : v ≤ w) (hw : w ∈ aliveSet Z) :
    ENNReal.ofReal v < Z :=
  lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hvw) hw.2

/-- Past an alive time `u`, the alive times accumulate at the end of the life. -/
theorem termFilter_inf_neBot {Z : ℝ≥0∞} {u : ℝ} (hu : u ∈ aliveSet Z) :
    (termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici u)).NeBot := by
  rw [inf_principal_neBot_iff]
  intro s hs
  obtain ⟨T, hT, hTs⟩ := mem_comap.1 hs
  obtain ⟨l, hl, hlT⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' (lt_of_le_of_lt bot_le hu.2)).1 hT
  obtain ⟨r, -, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 (max_lt hl hu.2)
  have hur : ENNReal.ofReal u < ENNReal.ofReal r := lt_of_le_of_lt (le_max_right _ _) hr1
  have hur' : u < r := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hu.1.le).1 hur
  exact ⟨r, hTs (hlT ⟨lt_of_le_of_lt (le_max_left _ _) hr1, hr2⟩), ⟨hu.1.trans hur', hr2⟩, hur'.le⟩

/-! ### Hits of the left part of the boundary of `ℍ \ γ(0, t]` -/

/-- The line `c` **hits the left part** of the boundary of `ℍ \ K_t` (`K_t = fwdHull W t`; for a simple trace, the
slit `γ(0, t]`) along the filter `F` of times: along `F`, restricted to the times at which `c` is off `K_t`, the mapped
line `f_t ∘ c` has a negative real cluster point (a prime end on the left side of the slit or on `ℝ₋`). -/
def HitsLeftPartAlong (W : ℝ → ℝ) (t : ℝ) (c : ℝ → ℂ) (F : Filter ℝ) : Prop :=
  ∃ x : ℝ, x < 0 ∧ MapClusterPt (x : ℂ) (F ⊓ 𝓟 {u | c u ∈ H \ fwdHull W t}) fun u => fwdMap W t (c u)

/-- **The line `c` (lifetime `Z`) never hits the left part of `∂(ℍ \ K_t)`**: not when approaching an alive time from
the past, and not at the end of its life. -/
def NoLeftPartHit (W : ℝ → ℝ) (t : ℝ) (c : ℝ → ℂ) (Z : ℝ≥0∞) : Prop :=
  (∀ u₀ ∈ aliveSet Z, ¬ HitsLeftPartAlong W t c (𝓝[aliveSet Z ∩ Iio u₀] u₀)) ∧
    ¬ HitsLeftPartAlong W t c (termFilter Z ⊓ 𝓟 (aliveSet Z))

/-! ### The left side near its boundary -/

/-- The left side of a proper arc is relatively closed in the complement of the arc in `ℍ`. -/
theorem mem_leftSideOf_of_mem_closure {γ : ℝ → ℂ} (hγ : IsProperArc γ) {z : ℂ} (hzH : z ∈ H)
    (hzA : z ∉ arcRange γ) (hz : z ∈ closure (leftSideOf (arcRange γ))) : z ∈ leftSideOf (arcRange γ) := by
  have hO : IsOpen (H \ arcRange γ) := QuantumZipper.isOpen_H.sdiff hγ.isClosed_arcRange
  have hzC : z ∈ connectedComponentIn (H \ arcRange γ) z := mem_connectedComponentIn ⟨hzH, hzA⟩
  obtain ⟨w, hwC, hwL⟩ := _root_.mem_closure_iff.1 hz _ hO.connectedComponentIn hzC
  have hzw : z ∈ connectedComponentIn (H \ arcRange γ) w := by
    rw [← connectedComponentIn_eq hwC]
    exact hzC
  exact mem_leftSideOf_of_mem_connectedComponentIn hwL hzw

variable {W : ℝ → ℝ} {γ : ℝ → ℂ}

theorem leftSideOf_subset_H_diff_fwdHull (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) {t : ℝ} (ht : 0 ≤ t) :
    leftSideOf (arcRange γ) ⊆ H \ fwdHull W t := fun _ hw =>
  ⟨hw.1.1, fun hK => hw.1.2 (fwdHull_subset_arcRange hη hγ ht hK)⟩

/-- **Approaching a boundary point from the left side.** Let `γ` be a simple proper trace of `W`, `t > 0`, and `p` a
point off `ℍ \ γ(0, t]` other than the tip `γ(t)`. Along an ultrafilter converging to `p` inside the left side of
`γ`, the mapping-out function `f_t` converges to a negative real point. -/
theorem exists_neg_tendsto_fwdMap (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {p : ℂ} (hp : p ∉ H \ fwdHull W t) (hpt : p ≠ γ t)
    (U : Ultrafilter ℂ) (hU : (U : Filter ℂ) ≤ 𝓝[leftSideOf (arcRange γ)] p) :
    ∃ x : ℝ, x < 0 ∧ Tendsto (fwdMap W t) U (𝓝 (x : ℂ)) := by
  obtain ⟨y, hyH, hy, hFy⟩ :=
    exists_tendsto_fwdMap_ultrafilter hη hW hW0 ht.le (leftSideOf_subset_H_diff_fwdHull hη hγ ht.le) U hU
  have hyim : y.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => hp ?_) hyH
    have := (isConformalBijection_fwdMapInv hW hW0 ht.le).2.mapsTo (show y ∈ H from hpos)
    rwa [← extendFrom_fwdMapInv_eq hW hW0 ht.le hpos, hFy] at this
  have hyeq : y = ((y.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hyim])
  have hUL : ∀ᶠ w in (U : Filter ℂ), w ∈ leftSideOf (arcRange γ) := hU self_mem_nhdsWithin
  have hcl : y ∈ closure (leftSideOf (arcRange (futureArc W t))) :=
    mem_closure_of_tendsto hy (hUL.mono fun w hw => fwdMap_mem_leftSideOf_futureArc hη hγ hW hW0 ht.le hw)
  refine ⟨y.re, lt_of_le_of_ne (not_lt.1 fun hpos => ?_) fun h0 => ?_, hyeq ▸ hy⟩
  · exact (isProperArc_futureArc hη hγ hW hW0 ht.le).notMem_closure_leftSideOf_of_pos hpos (hyeq ▸ hcl)
  · apply hpt
    rw [← hFy, hyeq, h0, ofReal_zero, extendFrom_zero hη hW hW0 ht.le]

/-- **An approach from inside the left side is a hit of the left part.** If, along a nontrivial filter `G ≤ F` of
times, `c` tends to such a point `p` from inside the left side of `γ`, then `c` hits the left part along `F`. -/
theorem hitsLeftPartAlong_of_tendsto (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 < t) {p : ℂ} (hp : p ∉ H \ fwdHull W t) (hpt : p ≠ γ t) {c : ℝ → ℂ}
    {F G : Filter ℝ} [G.NeBot] (hGF : G ≤ F) (hc : Tendsto c G (𝓝 p))
    (hcL : ∀ᶠ u in G, c u ∈ leftSideOf (arcRange γ)) : HitsLeftPartAlong W t c F := by
  set U₀ := Ultrafilter.of G
  have hU₀ : (U₀ : Filter ℝ) ≤ G := Ultrafilter.of_le G
  have hcU : ((U₀.map c : Ultrafilter ℂ) : Filter ℂ) ≤ 𝓝[leftSideOf (arcRange γ)] p := by
    rw [Ultrafilter.coe_map]
    exact ((tendsto_nhdsWithin_iff.2 ⟨hc, hcL⟩).mono_left hU₀)
  obtain ⟨x, hx, hlim⟩ := exists_neg_tendsto_fwdMap hη hγ hW hW0 ht hp hpt (U₀.map c) hcU
  refine ⟨x, hx, mapClusterPt_iff_ultrafilter.2 ⟨U₀, le_inf (hU₀.trans hGF) (le_principal_iff.2 ?_), ?_⟩⟩
  · exact hU₀ (hcL.mono fun u hu => leftSideOf_subset_H_diff_fwdHull hη hγ ht.le hu)
  · rw [Ultrafilter.coe_map] at hlim
    exact Filter.tendsto_map'_iff.1 hlim

/-! ### The no-wrap theorem -/

/-- A boundary point of the left side gives a slit time: a positive rational `t` with `p` off `ℍ \ γ(0, t]` and
`p ≠ γ(t)`. -/
theorem exists_rat_of_mem_closure_leftSideOf (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) {p : ℂ}
    (hpL : p ∉ leftSideOf (arcRange γ)) (hpcl : p ∈ closure (leftSideOf (arcRange γ))) :
    ∃ t : ℚ, 0 < t ∧ p ∉ H \ fwdHull W t ∧ p ≠ γ t := by
  by_cases hpH : p ∈ H
  · have hpA : p ∈ arcRange γ := by
      by_contra hpA
      exact hpL (mem_leftSideOf_of_mem_closure hγ hpH hpA hpcl)
    obtain ⟨s, hs, rfl⟩ := hpA
    have hs0 : 0 < s := by
      refine lt_of_le_of_ne hs fun h => ?_
      rw [← h, hγ.zero] at hpH
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hpH)
    obtain ⟨t, ht⟩ := exists_rat_gt s
    have ht0 : (0 : ℝ) < t := hs0.trans ht
    refine ⟨t, by exact_mod_cast ht0, fun h => h.2 ?_, fun h => ?_⟩
    · rw [fwdHull_eq_image_Ioc hη hγ ht0.le]
      exact ⟨s, ⟨hs0, ht.le⟩, rfl⟩
    · have := hγ.inj (mem_Ici.2 hs) (mem_Ici.2 ht0.le) h
      linarith
  · refine ⟨1, one_pos, fun h => hpH h.1, fun h => hpH ?_⟩
    rw [h]
    exact hγ.mem_H _ (by norm_num)

/-- **The no-wrap theorem, in the flow line's own chart.** Let `γ` be a simple proper Loewner trace of a continuous
driver `W` with `W 0 = 0`, and let `c` be continuous on its alive times and tend to `0` at the end of its life `Z`.
If, for every positive rational `t`, `c` never hits the left part of `∂(ℍ \ γ(0, t])`, then no alive point of `c` lies
on the left side of `γ`. -/
theorem notMem_leftSideOf_of_noLeftPartHit (hη : IsLoewnerTrace W γ) (hγ : IsProperArc γ) (hW : Continuous W)
    (hW0 : W 0 = 0) {c : ℝ → ℂ} {Z : ℝ≥0∞} (hc : ContinuousOn c (aliveSet Z))
    (hterm : Tendsto c (termFilter Z ⊓ 𝓟 (aliveSet Z)) (𝓝 0))
    (hhit : ∀ t : ℚ, 0 < t → NoLeftPartHit W t c Z) {u : ℝ} (hu : u ∈ aliveSet Z) :
    c u ∉ leftSideOf (arcRange γ) := by
  intro hL
  set L := leftSideOf (arcRange γ) with hLdef
  have hLo : IsOpen L := Cond44Ref.isOpen_leftSideOf_arcRange hγ
  have hAo := isOpen_aliveSet Z
  set B := {v | v ∈ aliveSet Z ∧ u ≤ v ∧ c v ∉ L} with hBdef
  by_cases hB : B.Nonempty
  · -- the first exit time `v₁` from the left side after `u`
    set v₁ := sInf B with hv₁def
    have hBb : BddBelow B := ⟨u, fun v hv => hv.2.1⟩
    have huv₁ : u ≤ v₁ := le_csInf hB fun v hv => hv.2.1
    obtain ⟨b, hb⟩ := hB
    have hv₁A : v₁ ∈ aliveSet Z :=
      ⟨hu.1.trans_le huv₁, ofReal_lt_of_le_of_mem_aliveSet (csInf_le hBb hb) hb.1⟩
    have hcv₁ : ContinuousAt c v₁ := hc.continuousAt (hAo.mem_nhds hv₁A)
    have hbelow : ∀ v, u ≤ v → v < v₁ → c v ∈ L := fun v huv hvv₁ => by
      by_contra hv
      have hvA : v ∈ aliveSet Z := ⟨hu.1.trans_le huv, ofReal_lt_of_le_of_mem_aliveSet hvv₁.le hv₁A⟩
      exact absurd (csInf_le hBb ⟨hvA, huv, hv⟩) (not_le.2 hvv₁)
    have hv₁L : c v₁ ∉ L := by
      intro hv₁L
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hcv₁.preimage_mem_nhds (hLo.mem_nhds hv₁L))
      obtain ⟨a, ha, hav⟩ := exists_lt_of_csInf_lt ⟨b, hb⟩ (show v₁ < v₁ + ε by linarith)
      have hv₁a : v₁ ≤ a := csInf_le hBb ha
      refine ha.2.2 (hball ?_)
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have huv₁' : u < v₁ := lt_of_le_of_ne huv₁ fun h => hv₁L (h ▸ hL)
    have hGne : (𝓝[Ico u v₁] v₁).NeBot := by
      rw [nhdsWithin_Ico_eq_nhdsLT huv₁']
      infer_instance
    have hcG : Tendsto c (𝓝[Ico u v₁] v₁) (𝓝 (c v₁)) := hcv₁.tendsto.mono_left nhdsWithin_le_nhds
    have hcL : ∀ᶠ v in 𝓝[Ico u v₁] v₁, c v ∈ L :=
      eventually_nhdsWithin_of_forall fun v hv => hbelow v hv.1 hv.2
    have hGF : 𝓝[Ico u v₁] v₁ ≤ 𝓝[aliveSet Z ∩ Iio v₁] v₁ :=
      nhdsWithin_mono _ fun v hv => ⟨⟨hu.1.trans_le hv.1, ofReal_lt_of_le_of_mem_aliveSet hv.2.le hv₁A⟩, hv.2⟩
    obtain ⟨t, ht0, hp, hpt⟩ :=
      exists_rat_of_mem_closure_leftSideOf hη hγ hv₁L (mem_closure_of_tendsto hcG hcL)
    exact (hhit t ht0).1 v₁ hv₁A
      (hitsLeftPartAlong_of_tendsto hη hγ hW hW0 (by exact_mod_cast ht0) hp hpt hGF hcG hcL)
  · -- `c` stays on the left side up to the end of its life, and ends at `0 = γ(0)`
    have hall : ∀ v ∈ aliveSet Z, u ≤ v → c v ∈ L := fun v hv huv => by
      by_contra h
      exact hB ⟨v, hv, huv, h⟩
    have hGne := termFilter_inf_neBot hu
    have hGF : termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici u) ≤ termFilter Z ⊓ 𝓟 (aliveSet Z) :=
      inf_le_inf_left _ (principal_mono.2 inter_subset_left)
    have hcG : Tendsto c (termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici u)) (𝓝 0) := hterm.mono_left hGF
    have hcL : ∀ᶠ v in termFilter Z ⊓ 𝓟 (aliveSet Z ∩ Ici u), c v ∈ L :=
      mem_inf_of_right (mem_principal.2 fun v hv => hall v hv.1 hv.2)
    have h0L : (0 : ℂ) ∉ L := fun h => lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from h.1.1)
    obtain ⟨t, ht0, hp, hpt⟩ := exists_rat_of_mem_closure_leftSideOf hη hγ h0L (mem_closure_of_tendsto hcG hcL)
    exact (hhit t ht0).2 (hitsLeftPartAlong_of_tendsto hη hγ hW hW0 (by exact_mod_cast ht0) hp hpt hGF hcG hcL)

end InteractingSLE.Sec5.Prop51Q

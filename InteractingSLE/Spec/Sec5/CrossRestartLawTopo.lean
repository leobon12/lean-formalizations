/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartPack
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane
import InteractingSLE.Foundations.Topology.PathComplement
import InteractingSLE.Foundations.Loewner.HullFilling

/-!
# The counterflow is alive in the restart chart while its trace avoids the flow-line segment

Packet PROVE-SEC5-H, layer (iv) of the counterflow restart (`planning/handoffs/PROVE-SEC5-G.md`, "What remains" 1).
SEC5-G's canonical exit time `CrossRestart.restartExit` is the supremum of the times up to which the counterflow is
alive in the restart chart (`CrossRestart.IsRestartAlive`: three conditions on hulls and the trace staying in `ℍ`).
Hull conditions are hard to read off measurably. This file proves them **from conditions on the two traces alone**,
deterministically:

* a closed bounded set `F` meeting `{Im ≤ 0}` only at the real point `p` has a filling whose closure meets the real
  line only at `p` (`exists_ball_disjoint_fillH`, `closure_fillH_subset_insert`);
* for a flow-line segment `η([0, σ])` and a counterflow prefix `γ′([0, T])` both attached to `ℝ` at `0` only
  (`IsAttachedPath`), whose images in the exponential chart are disjoint (`m₁ = M_q⁻¹ ∘ …`, the Möbius map
  `w ↦ −(1 + q)/(w + 1)`), the two filled hulls are disjoint in that chart, and their closures too
  (`disjoint_fillH_image_fillH`, `disjoint_closure_fillH_insert`);
* hence **`isRestartAlive_of_attached`**: the four conditions of `IsRestartAlive` hold at `T`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal

open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Sec5

namespace CrossRestart

open HalfPlaneSep

/-! ### Fillings of sets attached to the real line at one point -/

section Attach

theorem isPreconnected_H_restart : IsPreconnected H :=
  (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0).isPreconnected

theorem not_isBounded_H_restart : ¬ IsBounded H := by
  intro hb
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hpos : 0 < |R| + 1 := by positivity
  have hmem : ((|R| + 1 : ℝ) : ℂ) * I ∈ H := by
    show 0 < (((|R| + 1 : ℝ) : ℂ) * I).im
    simpa using hpos
  have h1 := mem_closedBall_zero_iff.1 (hR hmem)
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos] at h1
  linarith [le_abs_self R]

/-- **A filling attached to the real line at one point.** If the closed bounded set `F` meets `{Im ≤ 0}` only at the
real point `p`, every real `x ≠ p` has a ball disjoint from `fillH F`. -/
theorem exists_ball_disjoint_fillH {F : Set ℂ} (hF : IsCompact F) {p : ℝ}
    (hFp : ∀ z ∈ F, z.im ≤ 0 → z = p) {x : ℝ} (hx : x ≠ p) :
    ∃ r > 0, Disjoint (ball (x : ℂ) r) (fillH F) := by
  set d : ℝ := |x - p| with hd
  have hd0 : 0 < d := abs_pos.2 (sub_ne_zero.2 hx)
  -- the part of `F` away from `p` has imaginary parts at least `δ > 0`
  obtain ⟨δ, hδ, hδF⟩ : ∃ δ > 0, ∀ z ∈ F, d / 2 ≤ ‖z - p‖ → δ ≤ z.im := by
    set F' := F ∩ {z : ℂ | d / 2 ≤ ‖z - p‖} with hF'
    have hF'c : IsCompact F' :=
      hF.inter_right (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
    rcases F'.eq_empty_or_nonempty with he | hne
    · refine ⟨1, one_pos, fun z hz hzp => ?_⟩
      have : z ∈ F' := ⟨hz, hzp⟩
      rw [he] at this
      exact this.elim
    · obtain ⟨z₀, hz₀, hmin⟩ := hF'c.exists_isMinOn hne continuous_im.continuousOn
      refine ⟨z₀.im, ?_, fun z hz hzp => hmin ⟨hz, hzp⟩⟩
      by_contra hle
      have h0 := hFp z₀ hz₀.1 (not_lt.1 hle)
      have := hz₀.2
      simp only [mem_ofPred_eq, h0, sub_self, norm_zero] at this
      linarith
  refine ⟨min δ (d / 2), lt_min hδ (by linarith), Set.disjoint_left.2 fun z hz hzF => ?_⟩
  have hzH : z ∈ H := hzF.1
  have hzx : ‖z - x‖ < min δ (d / 2) := by rw [← dist_eq_norm]; exact mem_ball.1 hz
  -- the region `X` of points just above the real axis, beyond `x` as seen from `p`
  set c : ℝ := (x - p) / d with hc
  have hc2 : c * c = 1 := by
    rw [hc, div_mul_div_comm, ← sq, ← sq, hd, sq_abs, div_self (pow_ne_zero 2 (sub_ne_zero.2 hx))]
  have hcabs : |c| = 1 := by
    have : |c| * |c| = 1 := by rw [← abs_mul, hc2, abs_one]
    nlinarith [abs_nonneg c]
  set X : Set ℂ := {w | 0 < w.im ∧ w.im < δ ∧ d / 2 + p * c < w.re * c} with hX
  have hXeq : X = {w : ℂ | 0 < w.im} ∩ {w : ℂ | w.im < δ} ∩ {w : ℂ | d / 2 + p * c < w.re * c} := by
    ext w; simp only [hX, mem_ofPred_eq, mem_inter_iff, and_assoc]
  have hXc : Convex ℝ X := by
    rw [hXeq]
    refine ((convex_halfSpace_gt (f := fun w : ℂ => w.im) Complex.imLm.isLinear 0).inter
      (convex_halfSpace_lt (f := fun w : ℂ => w.im) Complex.imLm.isLinear δ)).inter ?_
    exact convex_halfSpace_gt (f := fun w : ℂ => w.re * c)
      ⟨fun a b => by simp [add_mul], fun a b => by simp [mul_assoc]⟩ _
  have hXu : ¬ IsBounded X := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    set n : ℝ := |R| + |p| + d + 1 with hn
    set w : ℂ := ((p + n * c : ℝ) : ℂ) + ((δ / 2 : ℝ) : ℂ) * I with hw
    have hwre : w.re = p + n * c := by simp [hw]
    have hwim : w.im = δ / 2 := by simp [hw]
    have hwX : w ∈ X := by
      refine ⟨by rw [hwim]; linarith, by rw [hwim]; linarith, ?_⟩
      rw [hwre, add_mul, mul_assoc, hc2, mul_one]
      have : 0 ≤ |R| := abs_nonneg R
      have : 0 ≤ |p| := abs_nonneg p
      linarith
    have h1 := mem_closedBall_zero_iff.1 (hR hwX)
    have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
    rw [hwre] at h2
    have h3 : n ≤ |p + n * c| + |p| := by
      have := abs_add_le (p + n * c) (-p)
      rw [abs_neg, show p + n * c + -p = n * c by ring, abs_mul, hcabs, mul_one,
        abs_of_pos (by positivity : 0 < n)] at this
      linarith
    have : R ≤ |R| := le_abs_self R
    linarith
  have hXF : X ⊆ H \ F := by
    intro w hw
    refine ⟨hw.1, fun hwF => ?_⟩
    have hre : d / 2 < ‖w - p‖ := by
      have h1 : d / 2 < (w.re - p) * c := by linarith [hw.2.2]
      have h2 : (w.re - p) * c ≤ |w.re - p| := by
        calc (w.re - p) * c ≤ |(w.re - p) * c| := le_abs_self _
          _ = |w.re - p| := by rw [abs_mul, hcabs, mul_one]
      have h3 : |w.re - p| ≤ ‖w - p‖ := by
        have := Complex.abs_re_le_norm (w - p)
        simpa using this
      linarith
    linarith [hδF w hwF hre.le, hw.2.1]
  have hsub := subset_H_diff_fillH_of_not_isBounded hF.isClosed hXc.isPreconnected hXu hXF
  refine (hsub ?_).2 hzF
  have him : |z.im| ≤ ‖z - x‖ := by
    have := Complex.abs_im_le_norm (z - x)
    simpa using this
  have hre : |z.re - x| ≤ ‖z - x‖ := by
    have := Complex.abs_re_le_norm (z - x)
    simpa using this
  have hmin1 := min_le_left δ (d / 2)
  have hmin2 := min_le_right δ (d / 2)
  refine ⟨hzH, by linarith [le_abs_self z.im], ?_⟩
  have hxc : (x - p) * c = d := by
    rw [hc, mul_div_assoc', ← sq, hd, ← sq_abs, sq, mul_self_div_self]
  have hzc : |(z.re - x) * c| ≤ ‖z - x‖ := by rw [abs_mul, hcabs, mul_one]; exact hre
  have := neg_abs_le ((z.re - x) * c)
  nlinarith

/-- The closure of a filling attached to the real line at `p` adds at most `p`. -/
theorem closure_fillH_subset_insert {F : Set ℂ} (hF : IsCompact F) {p : ℝ}
    (hFp : ∀ z ∈ F, z.im ≤ 0 → z = p) : closure (fillH F) ⊆ insert (p : ℂ) (fillH F) := by
  intro z hz
  have hzim : 0 ≤ z.im := by
    have : closure (fillH F) ⊆ {w : ℂ | 0 ≤ w.im} :=
      closure_minimal (fun w hw => (show 0 < w.im from hw.1).le)
        (isClosed_le continuous_const continuous_im)
    exact this hz
  rcases hzim.lt_or_eq with hpos | hzero
  · by_contra hnot
    have hzO : z ∈ H \ fillH F := ⟨hpos, fun h => hnot (mem_insert_of_mem _ h)⟩
    obtain ⟨w, hwO, hwF⟩ := mem_closure_iff.1 hz _ (isOpen_H_diff_fillH hF.isBounded) hzO
    exact hwO.2 hwF
  · by_contra hnot
    have hzre : z = (z.re : ℂ) := Complex.ext rfl (by simp [hzero.symm])
    have hne : z.re ≠ p := fun h => hnot (by rw [hzre, h]; exact mem_insert _ _)
    obtain ⟨r, hr, hd⟩ := exists_ball_disjoint_fillH hF hFp hne
    obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.1 hz _ isOpen_ball (by rw [hzre]; exact mem_ball_self hr)
    exact Set.disjoint_left.1 hd hw1 hw2

/-- A nonempty preconnected subset of `ℍ \ closure A` lies in the filling of `A` or misses it. -/
theorem subset_fillH_or_disjoint_restart {A B : Set ℂ} (hB : IsPreconnected B) (hBne : B.Nonempty)
    (hBA : B ⊆ H \ closure A) : B ⊆ fillH A ∨ Disjoint B (fillH A) := by
  obtain ⟨z, hz⟩ := hBne
  set C := connectedComponentIn (H \ closure A) z with hC
  have hBC : B ⊆ C := hB.subset_connectedComponentIn hz hBA
  have hcomp : ∀ y ∈ B, connectedComponentIn (H \ closure A) y = C := fun y hy =>
    (connectedComponentIn_eq (hBC hy)).symm
  by_cases hCb : IsBounded C
  · exact Or.inl fun y hy => ⟨(hBA hy).1, Or.inr (by rw [hcomp y hy]; exact hCb)⟩
  · refine Or.inr (Set.disjoint_left.2 fun y hy hyF => ?_)
    rcases hyF.2 with h1 | h1
    · exact (hBA hy).2 h1
    · rw [hcomp y hy] at h1
      exact hCb h1

/-- A nonempty bounded component of an open subset `O` of `ℍ` has a frontier point in `ℍ \ O`. -/
theorem exists_frontier_mem_H_of_isBounded {O : Set ℂ} (hO : IsOpen O) (hOH : O ⊆ H) {w : ℂ} (hw : w ∈ O)
    (hb : IsBounded (connectedComponentIn O w)) :
    ∃ y ∈ H, y ∉ O ∧ y ∈ closure (connectedComponentIn O w) := by
  set C := connectedComponentIn O w with hC
  have hCo : IsOpen C := hO.connectedComponentIn
  by_contra hno
  push Not at hno
  -- `ℍ ⊆ C ∪ (closure C)ᶜ`
  have hcover : H ⊆ C ∪ (closure C)ᶜ := by
    intro y hy
    by_cases hyc : y ∈ closure C
    · left
      have hyO : y ∈ O := by
        by_contra hyO
        exact hno y hy hyO hyc
      -- the component of `y` is an open neighbourhood of `y` meeting `C`
      have hyC' : (connectedComponentIn O y ∩ C).Nonempty :=
        mem_closure_iff.1 hyc _ hO.connectedComponentIn (mem_connectedComponentIn hyO)
      obtain ⟨v, hv1, hv2⟩ := hyC'
      have h2 : v ∈ connectedComponentIn O w := hv2
      show y ∈ connectedComponentIn O w
      rw [connectedComponentIn_eq h2, ← connectedComponentIn_eq hv1]
      exact mem_connectedComponentIn hyO
    · exact Or.inr hyc
  have hdisj : Disjoint C (closure C)ᶜ := Set.disjoint_left.2 fun v hv hv' => hv' (subset_closure hv)
  rcases isPreconnected_H_restart.subset_or_subset hCo isClosed_closure.isOpen_compl hdisj hcover with h | h
  · exact not_isBounded_H_restart (hb.subset h)
  · exact h (hOH hw) (subset_closure (mem_connectedComponentIn hw))

end Attach

/-! ### Paths attached to the real line at `0` -/

/-- **A path attached to the real line at `0` on `[0, T]`**: continuous on `[0, T]`, starting at `0`, in `ℍ` at every
positive time up to `T`. -/
structure IsAttachedPath (γ : ℝ≥0 → ℂ) (T : ℝ≥0) : Prop where
  cont : ContinuousOn γ (Icc 0 T)
  zero : γ 0 = 0
  mem : ∀ t : ℝ≥0, 0 < t → t ≤ T → γ t ∈ H

namespace IsAttachedPath

variable {γ : ℝ≥0 → ℂ} {T : ℝ≥0}

theorem isCompact_image (hγ : IsAttachedPath γ T) : IsCompact (γ '' Icc 0 T) :=
  isCompact_Icc.image_of_continuousOn hγ.cont

theorem eq_zero_of_im_nonpos (hγ : IsAttachedPath γ T) {z : ℂ} (hz : z ∈ γ '' Icc 0 T) (him : z.im ≤ 0) :
    z = ((0 : ℝ) : ℂ) := by
  obtain ⟨t, ht, rfl⟩ := hz
  by_cases h0 : t = 0
  · rw [h0, hγ.zero, ofReal_zero]
  · have := hγ.mem t (pos_iff_ne_zero.2 h0) ht.2
    exact absurd him (not_le.2 this)

theorem mem_H_of_mem_Ioc (hγ : IsAttachedPath γ T) {t : ℝ≥0} (ht : t ∈ Ioc 0 T) : γ t ∈ H :=
  hγ.mem t ht.1 ht.2

theorem image_Icc_eq (hγ : IsAttachedPath γ T) : γ '' Icc 0 T = insert 0 (γ '' Ioc 0 T) := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    by_cases h0 : t = 0
    · rw [h0, hγ.zero]; exact mem_insert _ _
    · exact mem_insert_of_mem _ ⟨t, ⟨pos_iff_ne_zero.2 h0, ht.2⟩, rfl⟩
  · rintro (rfl | ⟨t, ht, rfl⟩)
    · exact ⟨0, ⟨le_rfl, zero_le⟩, hγ.zero⟩
    · exact ⟨t, Ioc_subset_Icc_self ht, rfl⟩

theorem isPreconnected_image_Ioc (hγ : IsAttachedPath γ T) : IsPreconnected (γ '' Ioc 0 T) :=
  isPreconnected_Ioc.image _ (hγ.cont.mono Ioc_subset_Icc_self)

theorem tendsto_zero (hγ : IsAttachedPath γ T) : Tendsto γ (𝓝[Ioc 0 T] 0) (𝓝 0) := by
  have h := (hγ.cont 0 ⟨le_rfl, zero_le⟩).mono (Ioc_subset_Icc_self (a := (0 : ℝ≥0)) (b := T))
  rw [ContinuousWithinAt, hγ.zero] at h
  exact h

theorem neBot (hT : 0 < T) : (𝓝[Ioc (0 : ℝ≥0) T] (0 : ℝ≥0)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hT.ne]
  exact ⟨le_rfl, zero_le⟩

end IsAttachedPath

/-! ### The exponential-chart Möbius map `m₁(w) = −(1 + q)/(w + 1)` and its inverse -/

section Mob

variable {q : ℝ}

theorem zero_notMem_H_restart : (0 : ℂ) ∉ H := fun h => by
  have : (0 : ℝ) < (0 : ℂ).im := h
  simp at this

theorem mob_det (hq : 0 < q) : (0 : ℝ) < 0 * 1 - (-(1 + q)) * 1 := by linarith

theorem mob_mem_H (hq : 0 < q) {z : ℂ} (hz : z ∈ H) : realMobius 0 (-(1 + q)) 1 1 z ∈ H :=
  QuantumZipper.CA.realMobius_mem_H (mob_det hq) hz

theorem mob_zero : realMobius 0 (-(1 + q)) 1 1 0 = ((-1 - q : ℝ) : ℂ) := by
  simp only [realMobius]; push_cast; ring

theorem continuousAt_mob {z : ℂ} (hz : z ≠ -1) : ContinuousAt (realMobius 0 (-(1 + q)) 1 1) z := by
  have hd : ((1 : ℝ) : ℂ) * z + ((1 : ℝ) : ℂ) ≠ 0 := by
    push_cast
    intro h
    exact hz (by linear_combination h)
  show ContinuousAt (fun z : ℂ => (((0 : ℝ) : ℂ) * z + ((-(1 + q) : ℝ) : ℂ)) / (((1 : ℝ) : ℂ) * z + ((1 : ℝ) : ℂ))) z
  exact ((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
    ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hd

theorem ne_neg_one_of_mem_H {z : ℂ} (hz : z ∈ H) : z ≠ -1 := fun h => by
  have : (0 : ℝ) < z.im := hz
  rw [h] at this
  simp at this

theorem continuousOn_mob_H : ContinuousOn (realMobius 0 (-(1 + q)) 1 1) H := fun _ hz =>
  (continuousAt_mob (ne_neg_one_of_mem_H hz)).continuousWithinAt

theorem mobInv_mob (hq : 0 < q) {z : ℂ} (hz : z ∈ H) :
    realMobius 1 (1 + q) (-1) 0 (realMobius 0 (-(1 + q)) 1 1 z) = z := by
  have := QuantumZipper.CA.realMobius_inv_apply (mob_det hq) hz
  simpa only [neg_neg] using this

theorem mobInv_det (hq : 0 < q) : (0 : ℝ) < 1 * 0 - (1 + q) * (-1) := by linarith

theorem mob_mobInv (hq : 0 < q) {w : ℂ} (hw : w ∈ H) :
    realMobius 0 (-(1 + q)) 1 1 (realMobius 1 (1 + q) (-1) 0 w) = w := by
  have := QuantumZipper.CA.realMobius_inv_apply (mobInv_det hq) hw
  simpa only [neg_neg] using this

theorem mobInv_mem_H (hq : 0 < q) {w : ℂ} (hw : w ∈ H) : realMobius 1 (1 + q) (-1) 0 w ∈ H :=
  QuantumZipper.CA.realMobius_mem_H (mobInv_det hq) hw

theorem continuousOn_mobInv_H : ContinuousOn (realMobius 1 (1 + q) (-1) 0) H := by
  intro w hw
  have hw0 : w ≠ 0 := fun h => zero_notMem_H_restart (h ▸ hw)
  have hd : ((-1 : ℝ) : ℂ) * w + ((0 : ℝ) : ℂ) ≠ 0 := by
    push_cast
    simpa using hw0
  show ContinuousWithinAt
    (fun w : ℂ => (((1 : ℝ) : ℂ) * w + ((1 + q : ℝ) : ℂ)) / (((-1 : ℝ) : ℂ) * w + ((0 : ℝ) : ℂ))) H w
  exact (((continuousAt_const.mul continuousAt_id).add continuousAt_const).div
    ((continuousAt_const.mul continuousAt_id).add continuousAt_const) hd).continuousWithinAt

theorem norm_mul_norm_mobInv {w : ℂ} (hw : w ≠ 0) :
    ‖w‖ * ‖realMobius 1 (1 + q) (-1) 0 w‖ = ‖w + ((1 + q : ℝ) : ℂ)‖ := by
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have h1 : ((-1 : ℝ) : ℂ) * w + ((0 : ℝ) : ℂ) = -w := by push_cast; ring
  have h2 : ((1 : ℝ) : ℂ) * w + ((1 + q : ℝ) : ℂ) = w + ((1 + q : ℝ) : ℂ) := by push_cast; ring
  rw [realMobius, h1, h2, norm_div, norm_neg]
  field_simp

end Mob

/-! ### The two filled hulls are disjoint in the exponential chart -/

section Disjoint

variable {q : ℝ} {η γ' : ℝ≥0 → ℂ} {σ T : ℝ≥0}

/-- **Step 1.** The `E`-image of the counterflow prefix at positive times lies in the unbounded domain of the
flow-line segment: it is preconnected, misses the segment, and accumulates at the start `−1 − q`, which is away from
the segment's filling. -/
theorem mob_image_Ioc_subset (hq : 0 < q) (hη : IsAttachedPath η σ) (hγ : IsAttachedPath γ' T)
    (hdisj : Disjoint (η '' Icc 0 σ) (realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Icc 0 T))) :
    realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Ioc 0 T) ⊆ H \ fillH (η '' Icc 0 σ) := by
  rcases eq_zero_or_pos T with rfl | hT
  · intro z hz
    obtain ⟨_, ⟨t, ht, -⟩, -⟩ := hz
    exact absurd (ht.1.trans_le ht.2) (lt_irrefl 0)
  set F₁ := η '' Icc 0 σ with hF₁
  set G := realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Ioc 0 T) with hG
  have hGH : G ⊆ H \ F₁ := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    refine ⟨mob_mem_H hq (hγ.mem_H_of_mem_Ioc ht), fun h => Set.disjoint_left.1 hdisj h ?_⟩
    exact ⟨γ' t, ⟨t, Ioc_subset_Icc_self ht, rfl⟩, rfl⟩
  have hGc : IsPreconnected G := by
    rw [hG, image_image]
    refine isPreconnected_Ioc.image _ ?_
    exact continuousOn_mob_H.comp (hγ.cont.mono Ioc_subset_Icc_self) fun t ht => hγ.mem_H_of_mem_Ioc ht
  obtain ⟨r, hr, hball⟩ := exists_ball_disjoint_fillH hη.isCompact_image
    (fun z hz him => hη.eq_zero_of_im_nonpos hz him) (x := -1 - q) (by linarith)
  have htend : Tendsto (fun t => realMobius 0 (-(1 + q)) 1 1 (γ' t)) (𝓝[Ioc 0 T] 0)
      (𝓝 ((-1 - q : ℝ) : ℂ)) := by
    rw [← mob_zero]
    exact (continuousAt_mob (by norm_num : (0 : ℂ) ≠ -1)).tendsto.comp hγ.tendsto_zero
  have := IsAttachedPath.neBot hT
  obtain ⟨t, htb, htI⟩ :=
    ((htend.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))).and self_mem_nhdsWithin).exists
  have hg : realMobius 0 (-(1 + q)) 1 1 (γ' t) ∈ H \ fillH F₁ :=
    ⟨mob_mem_H hq (hγ.mem_H_of_mem_Ioc htI), fun h => Set.disjoint_left.1 hball htb h⟩
  have hsub := hGc.subset_connectedComponentIn ⟨γ' t, ⟨t, htI, rfl⟩, rfl⟩ hGH
  exact hsub.trans (connectedComponentIn_subset_H_diff_fillH hη.isCompact_image.isClosed hg)

/-- **Step 2.** The flow-line segment at positive times lies in the `E`-image of the unbounded domain of the
counterflow prefix: its preimage under `m₁` is preconnected, misses the prefix and is unbounded (the start `0` of the
segment is the image of `∞`). -/
theorem image_Ioc_subset_mob_image (hq : 0 < q) (hη : IsAttachedPath η σ) (hγ : IsAttachedPath γ' T)
    (hdisj : Disjoint (η '' Icc 0 σ) (realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Icc 0 T))) :
    η '' Ioc 0 σ ⊆ realMobius 0 (-(1 + q)) 1 1 '' (H \ fillH (γ' '' Icc 0 T)) := by
  rcases eq_zero_or_pos σ with rfl | hσ
  · intro z hz
    obtain ⟨t, ht, -⟩ := hz
    exact absurd (ht.1.trans_le ht.2) (lt_irrefl 0)
  set G := realMobius 1 (1 + q) (-1) 0 '' (η '' Ioc 0 σ) with hG
  have hGH : G ⊆ H \ γ' '' Icc 0 T := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    have hH := hη.mem_H_of_mem_Ioc ht
    refine ⟨mobInv_mem_H hq hH, fun hmem => ?_⟩
    exact Set.disjoint_left.1 hdisj ⟨t, Ioc_subset_Icc_self ht, rfl⟩ ⟨_, hmem, mob_mobInv hq hH⟩
  have hGc : IsPreconnected G := by
    rw [hG, image_image]
    refine isPreconnected_Ioc.image _ ?_
    exact (continuousOn_mobInv_H (q := q)).comp (hη.cont.mono Ioc_subset_Icc_self) fun t ht =>
      hη.mem_H_of_mem_Ioc ht
  have hGu : ¬ IsBounded G := by
    intro hb
    obtain ⟨R, hR⟩ := hb.subset_closedBall 0
    have hR0 : 0 ≤ R := by
      exact (norm_nonneg _).trans
        (mem_closedBall_zero_iff.1 (hR ⟨η σ, ⟨σ, ⟨hσ, le_rfl⟩, rfl⟩, rfl⟩))
    set ε : ℝ := (1 + q) / (R + 2) with hε
    have hε0 : 0 < ε := by positivity
    have := IsAttachedPath.neBot hσ
    obtain ⟨t, htb, htI⟩ := ((hη.tendsto_zero.eventually
      (isOpen_ball.mem_nhds (mem_ball_self hε0))).and self_mem_nhdsWithin).exists
    set w := η t with hw
    have hwH := hη.mem_H_of_mem_Ioc htI
    have hw0 : w ≠ 0 := fun h => zero_notMem_H_restart (h ▸ hwH)
    have hwε : ‖w‖ < ε := by simpa using htb
    have hmR : ‖realMobius 1 (1 + q) (-1) 0 w‖ ≤ R :=
      mem_closedBall_zero_iff.1 (hR ⟨w, ⟨t, htI, rfl⟩, rfl⟩)
    have hkey := norm_mul_norm_mobInv (q := q) hw0
    have hlow : 1 + q - ‖w‖ ≤ ‖w + ((1 + q : ℝ) : ℂ)‖ := by
      have h1 := norm_sub_le (w + ((1 + q : ℝ) : ℂ)) w
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at h1
      linarith
    have hup : ‖w‖ * ‖realMobius 1 (1 + q) (-1) 0 w‖ ≤ ε * R :=
      mul_le_mul hwε.le hmR (norm_nonneg _) hε0.le
    have hεR : ε * (R + 2) = 1 + q := by rw [hε]; field_simp
    nlinarith [norm_nonneg w]
  have hsub := subset_H_diff_fillH_of_not_isBounded hγ.isCompact_image.isClosed hGc hGu hGH
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨_, hsub ⟨η t, ⟨t, ht, rfl⟩, rfl⟩, mob_mobInv hq (hη.mem_H_of_mem_Ioc ht)⟩

theorem mem_image_Ioc_of_mem_H (hγ : IsAttachedPath γ' T) {y : ℂ} (hy : y ∈ γ' '' Icc 0 T) (hyH : y ∈ H) :
    y ∈ γ' '' Ioc 0 T := by
  rw [hγ.image_Icc_eq] at hy
  rcases hy with rfl | h
  · exact absurd hyH zero_notMem_H_restart
  · exact h

/-- **Step 3.** The filled flow-line segment and the `E`-image of the filled counterflow prefix are disjoint. -/
theorem disjoint_fillH_mob_image_fillH (hq : 0 < q) (hη : IsAttachedPath η σ) (hγ : IsAttachedPath γ' T)
    (hdisj : Disjoint (η '' Icc 0 σ) (realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Icc 0 T))) :
    Disjoint (fillH (η '' Icc 0 σ)) (realMobius 0 (-(1 + q)) 1 1 '' fillH (γ' '' Icc 0 T)) := by
  set F₁ := η '' Icc 0 σ with hF₁
  set F₂ := γ' '' Icc 0 T with hF₂
  have hF₂c : IsClosed F₂ := hγ.isCompact_image.isClosed
  have hstep1 := mob_image_Ioc_subset hq hη hγ hdisj
  have hstep2 := image_Ioc_subset_mob_image hq hη hγ hdisj
  rw [Set.disjoint_left]
  rintro _ hz1 ⟨w, hw2, rfl⟩
  have hwH : w ∈ H := hw2.1
  by_cases hwF : w ∈ F₂
  · exact (hstep1 ⟨w, mem_image_Ioc_of_mem_H hγ hwF hwH, rfl⟩).2 hz1
  have hwb : IsBounded (connectedComponentIn (H \ F₂) w) := by
    rcases hw2.2 with h | h
    · exact absurd (hF₂c.closure_eq ▸ h) hwF
    · rwa [hF₂c.closure_eq] at h
  have hwO : w ∈ H \ F₂ := ⟨hwH, hwF⟩
  set C := connectedComponentIn (H \ F₂) w with hC
  have hO : IsOpen (H \ F₂) := QuantumZipper.isOpen_H.sdiff hF₂c
  have hCH : C ⊆ H := fun c hc => (connectedComponentIn_subset _ _ hc).1
  have hCfill : C ⊆ fillH F₂ := fun c hc => ⟨hCH hc, Or.inr (by
    rw [hF₂c.closure_eq, ← connectedComponentIn_eq hc]; exact hwb)⟩
  have hmC : realMobius 0 (-(1 + q)) 1 1 '' C ⊆ H \ closure F₁ := by
    rintro _ ⟨c, hc, rfl⟩
    refine ⟨mob_mem_H hq (hCH hc), fun hmem => ?_⟩
    rw [hη.isCompact_image.isClosed.closure_eq] at hmem
    have hmem' : realMobius 0 (-(1 + q)) 1 1 c ∈ η '' Ioc 0 σ :=
      mem_image_Ioc_of_mem_H hη hmem (mob_mem_H hq (hCH hc))
    obtain ⟨c', hc', hcc'⟩ := hstep2 hmem'
    have : c' = c := (QuantumZipper.CA.bijOn_realMobius_H (mob_det hq)).injOn hc'.1 (hCH hc) hcc'
    exact hc'.2 (this ▸ hCfill hc)
  have hmCc : IsPreconnected (realMobius 0 (-(1 + q)) 1 1 '' C) :=
    isPreconnected_connectedComponentIn.image _ (continuousOn_mob_H.mono hCH)
  rcases subset_fillH_or_disjoint_restart hmCc ⟨_, ⟨w, mem_connectedComponentIn hwO, rfl⟩⟩ hmC with
    hsub | hdis
  · obtain ⟨y, hyH, hyO, hycl⟩ := exists_frontier_mem_H_of_isBounded hO sdiff_subset hwO hwb
    have hyF : y ∈ F₂ := by
      by_contra h
      exact hyO ⟨hyH, h⟩
    have h1 := hstep1 ⟨y, mem_image_Ioc_of_mem_H hγ hyF hyH, rfl⟩
    have h2 : realMobius 0 (-(1 + q)) 1 1 y ∈ closure (fillH F₁) :=
      closure_mono hsub (mem_closure_image (continuousAt_mob (ne_neg_one_of_mem_H hyH)) hycl)
    rcases closure_fillH_subset_insert hη.isCompact_image (fun z hz him => hη.eq_zero_of_im_nonpos hz him) h2
      with h0 | h
    · exact absurd (h0 ▸ h1.1) (by rw [ofReal_zero]; exact zero_notMem_H_restart)
    · exact h1.2 h
  · exact Set.disjoint_left.1 hdis ⟨w, mem_connectedComponentIn hwO, rfl⟩ hz1

/-- The closure of the `E`-image of the filled counterflow prefix adds at most the start `−1 − q`. -/
theorem closure_mob_image_fillH_subset (hγ : IsAttachedPath γ' T) :
    closure (realMobius 0 (-(1 + q)) 1 1 '' fillH (γ' '' Icc 0 T)) ⊆
      insert ((-1 - q : ℝ) : ℂ) (realMobius 0 (-(1 + q)) 1 1 '' fillH (γ' '' Icc 0 T)) := by
  set S := fillH (γ' '' Icc 0 T) with hS
  have hcl : closure S ⊆ insert 0 S := by
    have := closure_fillH_subset_insert hγ.isCompact_image (fun z hz him => hγ.eq_zero_of_im_nonpos hz him)
    rwa [ofReal_zero] at this
  obtain ⟨R, hR, hball⟩ := hγ.isCompact_image.isBounded.subset_ball_lt 0 0
  have hSb : IsBounded S := (isBounded_ball (x := (0 : ℂ)) (r := R)).subset
    (fillH_subset_ball hR (by rw [hγ.isCompact_image.isClosed.closure_eq]; exact hball))
  have hcont : ContinuousOn (realMobius 0 (-(1 + q)) 1 1) (closure S) := fun z hz => by
    refine (continuousAt_mob ?_).continuousWithinAt
    rcases hcl hz with rfl | h
    · norm_num
    · exact ne_neg_one_of_mem_H h.1
  have hK := hSb.isCompact_closure.image_of_continuousOn hcont
  refine (closure_minimal (image_mono subset_closure) hK.isClosed).trans ?_
  refine (image_mono hcl).trans ?_
  rw [image_insert_eq, mob_zero]

/-- **The four sets are disjoint**: the filled flow-line segment with its start `0`, and the `E`-image of the filled
counterflow prefix with its start `−1 − q`. -/
theorem disjoint_insert_fillH_insert_mob (hq : 0 < q) (hη : IsAttachedPath η σ) (hγ : IsAttachedPath γ' T)
    (hdisj : Disjoint (η '' Icc 0 σ) (realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Icc 0 T))) :
    Disjoint (insert (0 : ℂ) (fillH (η '' Icc 0 σ)))
      (insert ((-1 - q : ℝ) : ℂ) (realMobius 0 (-(1 + q)) 1 1 '' fillH (γ' '' Icc 0 T))) := by
  have h3 := disjoint_fillH_mob_image_fillH hq hη hγ hdisj
  have hpH : ((-1 - q : ℝ) : ℂ) ∉ H := fun h => by
    have : (0 : ℝ) < ((-1 - q : ℝ) : ℂ).im := h
    simp at this
  rw [Set.disjoint_left]
  rintro z (rfl | hz1) (hz2 | hz2)
  · have := congrArg Complex.re hz2
    simp only [zero_re, ofReal_re] at this
    linarith
  · obtain ⟨w, hw, hw'⟩ := hz2
    exact zero_notMem_H_restart (hw' ▸ mob_mem_H hq hw.1)
  · exact hpH (hz2 ▸ hz1.1)
  · exact Set.disjoint_left.1 h3 hz1 hz2

end Disjoint

/-! ### The counterflow is alive in the restart chart while the two traces are disjoint -/

section Alive

open ConformalImage ConformalImageFull

/-- A Loewner hull that is the filling of a compact set is its `fillH`. -/
theorem fwdHull_eq_fillH_of_isFilling {W : ℝ → ℝ} {t : ℝ} {A : Set ℂ} (hA : IsCompact A)
    (h : IsFilling (QuantumZipper.fwdHull W t) A) : QuantumZipper.fwdHull W t = fillH A := by
  have := (isFilling_iff_inter_H_eq_fillH hA.isBounded hA.isClosed).1 h
  rwa [inter_eq_left.2 ((QuantumZipper.fwdHull_mono (W := W)).2 t)] at this

/-- **The counterflow is alive in the restart chart at time `T`** (`IsRestartAlive`), from conditions on the traces:
the flow-line segment `η([0, σ])` (hull `K^U_σ`, tip `η(σ)`) and the counterflow prefix `γ′([0, T])` (hull
`K′_T`) are attached to `ℝ` at `0` only, and the segment misses the `E`-image `m₁(γ′([0, T]))` of the prefix. -/
theorem isRestartAlive_of_attached {q : ℝ} (hq : 0 < q) {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0)
    {σ : ℝ≥0} {η : ℝ≥0 → ℂ} (hη : IsAttachedPath η σ)
    (hK₁ : QuantumZipper.fwdHull U σ = fillH (η '' Icc 0 σ))
    (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[H] 0) (𝓝 (η σ)))
    {w' : ℝ≥0 → ℝ} {γ' : ℝ≥0 → ℂ} {T : ℝ≥0} (hγ : IsAttachedPath γ' T)
    (hK₂ : cfHull w' T = fillH (γ' '' Icc 0 T))
    (hdisj : Disjoint (η '' Icc 0 σ) (realMobius 0 (-(1 + q)) 1 1 '' (γ' '' Icc 0 T))) :
    IsRestartAlive q U σ w' γ' T := by
  have hD := disjoint_insert_fillH_insert_mob hq hη hγ hdisj
  have hzero : ∀ {F : Set ℂ} {s : ℝ≥0} {f : ℝ≥0 → ℂ}, IsAttachedPath f s → F = f '' Icc 0 s →
      ∀ z ∈ F, z.im ≤ 0 → z = ((0 : ℝ) : ℂ) := by
    rintro F s f hf rfl z hz him
    exact hf.eq_zero_of_im_nonpos hz him
  refine ⟨?_, ?_, ?_, hγ.mem⟩
  · -- far₁
    rw [hK₂]
    obtain ⟨r, hr, h⟩ := exists_ball_disjoint_fillH hγ.isCompact_image (hzero hγ rfl) (x := -1) (by norm_num)
    refine ⟨r, hr, ?_⟩
    simpa using h
  · -- far₂
    rw [hK₁, hK₂]
    refine hD.mono ?_ (insert_subset_iff.2 ⟨mem_insert _ _, closure_mob_image_fillH_subset hγ⟩)
    have := closure_fillH_subset_insert hη.isCompact_image (hzero hη rfl)
    rwa [ofReal_zero] at this
  · -- far₃
    rw [hK₂]
    by_contra hno
    push Not at hno
    set S := realMobius 0 (-(1 + q)) 1 1 '' fillH (γ' '' Icc 0 T) with hS
    have hSK : S ⊆ H \ QuantumZipper.fwdHull U σ := by
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨mob_mem_H hq hw.1, fun h => ?_⟩
      rw [hK₁] at h
      exact Set.disjoint_left.1 hD (mem_insert_of_mem _ h) (mem_insert_of_mem _ ⟨w, hw, rfl⟩)
    have hseq : ∀ n : ℕ, ∃ y ∈ S, gmap U σ y ∈ ball (U σ : ℂ) (1 / ((n : ℝ) + 1)) := by
      intro n
      have := hno (1 / ((n : ℝ) + 1)) (by positivity)
      rw [Set.not_disjoint_iff] at this
      obtain ⟨v, hv, ⟨y, hy, rfl⟩⟩ := this
      exact ⟨y, hy, hv⟩
    choose y hyS hyb using hseq
    have hσ0 : (0 : ℝ) ≤ σ := NNReal.coe_nonneg σ
    have hf : Tendsto (fun n => QuantumZipper.fwdMap U σ (y n)) atTop (𝓝[H] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
        QuantumZipper.FwdHolo.mapsTo_fwdMap hU hσ0 (hSK (hyS n))⟩
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have h1 := mem_ball.1 (hyb n)
      rw [dist_eq_norm, gmap, add_sub_cancel_right] at h1
      rw [sub_zero]
      exact h1.le
    have hy : Tendsto y atTop (𝓝 (η σ)) :=
      (htip.comp hf).congr fun n => QuantumZipper.RS.fwdMapInv_fwdMap hU hU0 hσ0 (hSK (hyS n))
    have hcl : η σ ∈ closure S := mem_closure_of_tendsto hy (Eventually.of_forall hyS)
    have hmem := closure_mob_image_fillH_subset hγ hcl
    have hη' : η σ ∈ insert (0 : ℂ) (fillH (η '' Icc 0 σ)) := by
      by_cases h0 : σ = 0
      · rw [h0, hη.zero]
        exact mem_insert _ _
      · exact mem_insert_of_mem _ ⟨hη.mem σ (pos_iff_ne_zero.2 h0) le_rfl,
          Or.inl (subset_closure ⟨σ, ⟨zero_le, le_rfl⟩, rfl⟩)⟩
    exact Set.disjoint_left.1 hD hη' hmem

end Alive

end CrossRestart

end Sec5

end InteractingSLE

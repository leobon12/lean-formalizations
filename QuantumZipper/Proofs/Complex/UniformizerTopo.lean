/-
Copyright (c) 2026 The quantum-zipper authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: quantum-zipper (CA-H4U, EXT-CA node U1)
-/
import QuantumZipper.Loewner.Curves
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Topology of the left component of a simple chord (EXT-CA node U1)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "U", node U1.  Fix `η` with `IsSimpleChord η`, write
`K := chordSet η = η '' [0,∞)` and `Ω := slitH η = ℍ \ K`.

* `isClosed_chordSet`: `K` is closed (`‖η t‖ → ∞`, so near any point `K` is a compact arc piece);
  `eq_zero_of_mem_chordSet_of_im_nonpos`: `K` meets `{Im ≤ 0}` only at `0`.
* `leftComponent_eq`: `leftComponent η` is the connected component of `Ω` containing the point
  `zStar η = -1 + (rad η) i`.  Hence `leftComponent η` is open, preconnected and nonempty
  (`isOpen_leftComponent`, `isPreconnected_leftComponent`, `zStar_mem_leftComponent`), and
  `leftComponent_ne_univ`.
* `mem_leftComponent_of_mem_closure`: `leftComponent η` is relatively closed in `Ω` (so it is a
  component of `Ω`); `frontier_leftComponent_subset`: `frontier D ⊆ ℝ ∪ K`;
  `ofReal_mem_closure_leftComponent`, `zero_mem_closure_leftComponent`: `(-∞,0] ⊆ closure D`.

## Sources

Elementary plane topology; no published source is followed line by line.  The argument is the
one sketched in the blueprint (U1): every point of `D` connects, through its defining path, to a
thin strip above `(-∞, 0)` (here: to half-disks around negative reals, joined by horizontal
segments at height below the distance from a real segment `[x, -1]` to `K`).  **Own elementary
proof** (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open Set Metric Filter
open scoped Topology

namespace QuantumZipper.CA.Uniformizer

/-- The trace `η[0,∞)` of a chord. -/
def chordSet (η : ℝ → ℂ) : Set ℂ := η '' Ici (0 : ℝ)

/-- The slit half-plane `ℍ \ η[0,∞)`. -/
def slitH (η : ℝ → ℂ) : Set ℂ := H \ chordSet η

/-- The θ-set `ℝ ∪ η[0,∞)` containing the frontier of each complementary component. -/
def theta (η : ℝ → ℂ) : Set ℂ := {z | z.im = 0} ∪ chordSet η

variable {η : ℝ → ℂ}

theorem isClosed_chordSet (hη : IsSimpleChord η) : IsClosed (chordSet η) := by
  refine isClosed_of_closure_subset fun z hz => ?_
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hη.2.2.2.2.eventually_ge_atTop (‖z‖ + 1))
  have hC : IsCompact (η '' Icc 0 T) :=
    isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self)
  have hzC : z ∈ closure (η '' Icc 0 T) := by
    rw [Metric.mem_closure_iff] at hz ⊢
    intro ε hε
    obtain ⟨b, ⟨t, ht, rfl⟩, hb⟩ := hz (min ε 1) (lt_min hε one_pos)
    refine ⟨η t, ⟨t, ⟨ht, ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
    by_contra hlt
    push_neg at hlt
    have h1 := hT t hlt.le
    have h2 : dist z (η t) < 1 := lt_of_lt_of_le hb (min_le_right _ _)
    rw [dist_eq_norm] at h2
    have h3 := norm_sub_norm_le (η t) z
    rw [norm_sub_rev] at h3
    linarith
  rw [hC.isClosed.closure_eq] at hzC
  exact image_mono Icc_subset_Ici_self hzC

theorem eq_zero_of_mem_chordSet_of_im_nonpos (hη : IsSimpleChord η) {z : ℂ}
    (hz : z ∈ chordSet η) (h : z.im ≤ 0) : z = 0 := by
  obtain ⟨t, ht, rfl⟩ := hz
  rcases (mem_Ici.1 ht).eq_or_lt with h0 | hpos
  · rw [← h0]; exact hη.1
  · have := hη.2.2.2.1 t hpos
    simp only [H, mem_setOf_eq] at this
    linarith

theorem isOpen_slitH (hη : IsSimpleChord η) : IsOpen (slitH η) :=
  isOpen_H.sdiff (isClosed_chordSet hη)

theorem chordSet_nonempty : (chordSet η).Nonempty := ⟨η 0, 0, mem_Ici.2 le_rfl, rfl⟩

theorem zero_mem_chordSet (hη : IsSimpleChord η) : (0 : ℂ) ∈ chordSet η :=
  ⟨0, mem_Ici.2 le_rfl, hη.1⟩

/-- Half the (capped) distance from `-1` to the chord. -/
def rad (η : ℝ → ℂ) : ℝ := min 1 (infDist (-1 : ℂ) (chordSet η)) / 2

/-- The base point `-1 + (rad η) i` of the left component. -/
def zStar (η : ℝ → ℂ) : ℂ := -1 + (rad η : ℂ) * Complex.I

theorem infDist_neg_one_pos (hη : IsSimpleChord η) : 0 < infDist (-1 : ℂ) (chordSet η) := by
  refine ((isClosed_chordSet hη).notMem_iff_infDist_pos chordSet_nonempty).1 fun h => ?_
  have := eq_zero_of_mem_chordSet_of_im_nonpos hη h (by simp)
  norm_num at this

theorem rad_pos (hη : IsSimpleChord η) : 0 < rad η :=
  half_pos (lt_min one_pos (infDist_neg_one_pos hη))

theorem rad_lt (hη : IsSimpleChord η) : rad η < infDist (-1 : ℂ) (chordSet η) := by
  have h1 := infDist_neg_one_pos hη
  have h2 := min_le_right 1 (infDist (-1 : ℂ) (chordSet η))
  unfold rad
  linarith

theorem notMem_of_dist_lt_infDist {K : Set ℂ} {z c : ℂ} (h : dist z c < infDist c K) : z ∉ K :=
  fun hz => by
    have := infDist_le_dist_of_mem (x := c) hz
    rw [dist_comm] at this
    linarith

theorem segment_subset_H {u v : ℂ} (hu : u ∈ H) (hv : v ∈ H) : segment ℝ u v ⊆ H :=
  (convex_halfSpace_im_gt (r := 0)).segment_subset hu hv

/-- One step of a chain of segments inside `Ω`. -/
theorem mem_cc_of_segment {Ω : Set ℂ} {z u v : ℂ} (h : segment ℝ u v ⊆ Ω)
    (hv : v ∈ connectedComponentIn Ω z) : u ∈ connectedComponentIn Ω z := by
  rw [connectedComponentIn_eq hv]
  exact (convex_segment u v).isPreconnected.subset_connectedComponentIn
    (right_mem_segment ℝ u v) h (left_mem_segment ℝ u v)

/-- A component of an open set `Ω ⊆ ℂ` is relatively closed in `Ω`. -/
theorem mem_cc_of_mem_closure {Ω : Set ℂ} (hΩ : IsOpen Ω) {z w : ℂ}
    (hw : w ∈ closure (connectedComponentIn Ω z)) (hwΩ : w ∈ Ω) :
    w ∈ connectedComponentIn Ω z := by
  obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.1 hΩ w hwΩ
  obtain ⟨y, hyC, hyd⟩ := Metric.mem_closure_iff.1 hw r hr
  rw [connectedComponentIn_eq hyC]
  exact (convex_ball w r).isPreconnected.subset_connectedComponentIn
    (mem_ball.2 (by rwa [dist_comm])) hrΩ (mem_ball_self hr)

theorem zStar_mem_slitH (hη : IsSimpleChord η) : zStar η ∈ slitH η := by
  refine ⟨by simp [H, zStar, rad_pos hη], notMem_of_dist_lt_infDist (c := -1) ?_⟩
  have : dist (zStar η) (-1) = rad η := by
    simp [zStar, dist_eq_norm, abs_of_pos (rad_pos hη)]
  rw [this]
  exact rad_lt hη

/-- Points of `ℍ` close to a negative real `x` lie in the component of `Ω` through `zStar η`. -/
theorem exists_nhd_mem_cc (hη : IsSimpleChord η) {x : ℝ} (hx : x < 0) :
    ∃ δ > 0, ∀ w ∈ H, dist w (x : ℂ) < δ →
      w ∈ connectedComponentIn (slitH η) (zStar η) := by
  set K := chordSet η
  set S : Set ℂ := segment ℝ (x : ℂ) (-1 : ℂ)
  have hconv : Convex ℝ {w : ℂ | w.im = 0 ∧ w.re < 0} := by
    intro u hu v hv a b ha hb hab
    simp only [mem_setOf_eq, Complex.add_im, Complex.add_re, Complex.real_smul,
      Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at hu hv ⊢
    refine ⟨by rw [hu.1, hv.1]; ring, ?_⟩
    rcases ha.eq_or_lt with rfl | ha'
    · simp only [zero_add] at hab; subst hab; nlinarith [hv.2]
    · nlinarith [hu.2, hv.2]
  have hSK : S ⊆ Kᶜ := by
    intro w hw hwK
    have hw' : w.im = 0 ∧ w.re < 0 :=
      hconv.segment_subset ⟨by simp, by simpa using hx⟩ ⟨by simp, by norm_num⟩ hw
    have := eq_zero_of_mem_chordSet_of_im_nonpos hη hwK hw'.1.le
    rw [this] at hw'
    simp at hw'
  have hScpt : IsCompact S := by
    show IsCompact (segment ℝ (x : ℂ) (-1 : ℂ))
    rw [segment_eq_image_lineMap]
    exact isCompact_Icc.image AffineMap.lineMap_continuous
  obtain ⟨δ₀, hδ₀, hth⟩ := hScpt.exists_thickening_subset_open
    (isClosed_chordSet hη).isOpen_compl hSK
  have hr := rad_pos hη
  refine ⟨min δ₀ (rad η), lt_min hδ₀ hr, fun w hwH hwd => ?_⟩
  set b := w.im with hbdef
  have hb0 : 0 < b := hwH
  have hbw : b ≤ dist w x := by
    rw [dist_eq_norm]
    have := Complex.abs_im_le_norm (w - x)
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  have hbδ : b < min δ₀ (rad η) := lt_of_le_of_lt hbw hwd
  have hbδ₀ : b < δ₀ := lt_of_lt_of_le hbδ (min_le_left _ _)
  have hbr : b < rad η := lt_of_lt_of_le hbδ (min_le_right _ _)
  set p₁ : ℂ := (x : ℂ) + (b : ℂ) * Complex.I
  set p₂ : ℂ := -1 + (b : ℂ) * Complex.I
  have hp₁H : p₁ ∈ H := by simp [p₁, H, hb0]
  have hp₂H : p₂ ∈ H := by simp [p₂, H, hb0]
  have hzH : zStar η ∈ H := (zStar_mem_slitH hη).1
  -- step 3: vertical segment from `p₂` to `zStar η`
  have h3 : segment ℝ p₂ (zStar η) ⊆ slitH η := by
    intro q hq
    refine ⟨segment_subset_H hp₂H hzH hq, notMem_of_dist_lt_infDist (c := -1) ?_⟩
    have hball : segment ℝ p₂ (zStar η) ⊆ ball (-1 : ℂ) (infDist (-1 : ℂ) K) := by
      refine (convex_ball _ _).segment_subset ?_ ?_
      · rw [mem_ball]
        have : dist p₂ (-1) = b := by simp [p₂, dist_eq_norm, abs_of_pos hb0]
        rw [this]; linarith [rad_lt hη]
      · rw [mem_ball]
        have : dist (zStar η) (-1) = rad η := by
          simp [zStar, dist_eq_norm, abs_of_pos hr]
        rw [this]; exact rad_lt hη
    exact hball hq
  -- step 2: horizontal segment from `p₁` to `p₂`
  have h2 : segment ℝ p₁ p₂ ⊆ slitH η := by
    intro q hq
    refine ⟨segment_subset_H hp₁H hp₂H hq, fun hqK => ?_⟩
    have hseg : segment ℝ p₁ p₂ = (fun y => (b : ℂ) * Complex.I + y) '' S := by
      rw [segment_translate_image]
      congr 1 <;> simp only [p₁, p₂] <;> ring
    rw [hseg] at hq
    obtain ⟨y, hyS, rfl⟩ := hq
    have : (b : ℂ) * Complex.I + y ∈ thickening δ₀ S := by
      rw [mem_thickening_iff]
      refine ⟨y, hyS, ?_⟩
      simp [dist_eq_norm, abs_of_pos hb0, hbδ₀]
    exact hth this hqK
  -- step 1: segment from `w` to `p₁`
  have h1 : segment ℝ w p₁ ⊆ slitH η := by
    intro q hq
    refine ⟨segment_subset_H hwH hp₁H hq, fun hqK => ?_⟩
    have hball : segment ℝ w p₁ ⊆ ball (x : ℂ) δ₀ := by
      refine (convex_ball _ _).segment_subset ?_ ?_
      · exact mem_ball.2 (lt_of_lt_of_le hwd (min_le_left _ _))
      · rw [mem_ball]
        have : dist p₁ x = b := by simp [p₁, dist_eq_norm, abs_of_pos hb0]
        rw [this]; exact hbδ₀
    exact hth (ball_subset_thickening (left_mem_segment ℝ _ _) δ₀ (hball hq)) hqK
  exact mem_cc_of_segment h1 (mem_cc_of_segment h2
    (mem_cc_of_segment h3 (mem_connectedComponentIn (zStar_mem_slitH hη))))

theorem leftComponent_subset_cc (hη : IsSimpleChord η) :
    leftComponent η ⊆ connectedComponentIn (slitH η) (zStar η) := by
  rintro z ⟨_hzΩ, x, hx, p, hp⟩
  obtain ⟨δ, hδ, hball⟩ := exists_nhd_mem_cc hη hx
  obtain ⟨ε, hε, hcont⟩ := Metric.continuous_iff.1 p.continuous_extend 1 δ hδ
  set s : ℝ := 1 - min ε 1 / 2 with hsdef
  have hm1 := min_le_right ε 1
  have hm0 : 0 < min ε 1 := lt_min hε one_pos
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s < 1 := by linarith
  have hmemΩ : ∀ t ∈ Icc (0 : ℝ) s, p.extend t ∈ slitH η := by
    intro t ht
    rw [p.extend_apply ⟨ht.1, by linarith [ht.2]⟩]
    refine hp _ fun h => ?_
    have := congrArg Subtype.val h
    simp only [Set.Icc.coe_one] at this
    linarith [ht.2]
  have hps : p.extend s ∈ connectedComponentIn (slitH η) (zStar η) := by
    refine hball _ (hmemΩ s ⟨hs0, le_rfl⟩).1 ?_
    have hd : dist s 1 < ε := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [min_le_left ε 1]
    have := hcont s hd
    rwa [Path.extend_one] at this
  have hpre : IsPreconnected (p.extend '' Icc 0 s) :=
    isPreconnected_Icc.image _ p.continuous_extend.continuousOn
  rw [connectedComponentIn_eq hps]
  refine hpre.subset_connectedComponentIn ⟨s, ⟨hs0, le_rfl⟩, rfl⟩ ?_ ⟨0, ⟨le_rfl, hs0⟩, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩
    exact hmemΩ t ht
  · exact Path.extend_zero p

theorem lineMap_zStar_mem (hη : IsSimpleChord η) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1) :
    AffineMap.lineMap (zStar η) (((-1 : ℝ) : ℂ)) τ ∈ slitH η := by
  have hr := rad_pos hη
  have heq : AffineMap.lineMap (zStar η) (((-1 : ℝ) : ℂ)) τ
      = -1 + (((1 - τ) * rad η : ℝ) : ℂ) * Complex.I := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Complex.real_smul, zStar]
    push_cast
    ring
  have hpos : 0 < (1 - τ) * rad η := mul_pos (by linarith) hr
  rw [heq]
  refine ⟨by simp [H, hpos], notMem_of_dist_lt_infDist (c := -1) ?_⟩
  have : dist (-1 + (((1 - τ) * rad η : ℝ) : ℂ) * Complex.I) (-1) = (1 - τ) * rad η := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
  rw [this]
  have := rad_lt hη
  nlinarith

theorem cc_subset_leftComponent (hη : IsSimpleChord η) :
    connectedComponentIn (slitH η) (zStar η) ⊆ leftComponent η := by
  intro z hz
  have hΩ := isOpen_slitH hη
  have hzs := zStar_mem_slitH hη
  have hCΩ : connectedComponentIn (slitH η) (zStar η) ⊆ slitH η :=
    connectedComponentIn_subset _ _
  have hpc : IsPathConnected (connectedComponentIn (slitH η) (zStar η)) :=
    (hΩ.connectedComponentIn.isConnected_iff_isPathConnected).1
      (isConnected_connectedComponentIn_iff.2 hzs)
  have hj : JoinedIn (connectedComponentIn (slitH η) (zStar η)) z (zStar η) :=
    hpc.joinedIn z hz _ (mem_connectedComponentIn hzs)
  refine ⟨hCΩ hz, -1, by norm_num, hj.somePath.trans (Path.segment (zStar η) _), fun t ht => ?_⟩
  have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 fun h => ht (Subtype.ext h)
  rw [Path.trans_apply]
  split_ifs with h
  · exact hCΩ (hj.somePath_mem _)
  · rw [Path.segment_apply]
    exact lineMap_zStar_mem hη (by simp only; push_neg at h; linarith) (by simp only; linarith)

/-- **U1 (identification).** The left component is the component of `ℍ \ η[0,∞)` containing
`zStar η`. -/
theorem leftComponent_eq (hη : IsSimpleChord η) :
    leftComponent η = connectedComponentIn (slitH η) (zStar η) :=
  (leftComponent_subset_cc hη).antisymm (cc_subset_leftComponent hη)

theorem isOpen_leftComponent (hη : IsSimpleChord η) : IsOpen (leftComponent η) := by
  rw [leftComponent_eq hη]; exact (isOpen_slitH hη).connectedComponentIn

theorem isPreconnected_leftComponent (hη : IsSimpleChord η) :
    IsPreconnected (leftComponent η) := by
  rw [leftComponent_eq hη]; exact isPreconnected_connectedComponentIn

theorem zStar_mem_leftComponent (hη : IsSimpleChord η) : zStar η ∈ leftComponent η := by
  rw [leftComponent_eq hη]; exact mem_connectedComponentIn (zStar_mem_slitH hη)

theorem leftComponent_nonempty (hη : IsSimpleChord η) : (leftComponent η).Nonempty :=
  ⟨_, zStar_mem_leftComponent hη⟩

theorem leftComponent_subset_slitH (η : ℝ → ℂ) : leftComponent η ⊆ slitH η := fun _ hz => hz.1

theorem leftComponent_ne_univ (η : ℝ → ℂ) : leftComponent η ≠ univ := fun h => by
  have := leftComponent_subset_H η (h.symm ▸ mem_univ (0 : ℂ))
  simp [H] at this

/-- **U1 (relative closedness).** `leftComponent η` is closed in `ℍ \ η[0,∞)`. -/
theorem mem_leftComponent_of_mem_closure (hη : IsSimpleChord η) {w : ℂ}
    (hw : w ∈ closure (leftComponent η)) (hwΩ : w ∈ slitH η) : w ∈ leftComponent η := by
  rw [leftComponent_eq hη] at hw ⊢
  exact mem_cc_of_mem_closure (isOpen_slitH hη) hw hwΩ

theorem closure_subset_Hbar {D : Set ℂ} (hD : D ⊆ H) : closure D ⊆ Hbar :=
  closure_minimal (hD.trans H_subset_Hbar) isClosed_Hbar

/-- **U1 (frontier).** `frontier (leftComponent η) ⊆ ℝ ∪ η[0,∞)`. -/
theorem frontier_leftComponent_subset (hη : IsSimpleChord η) :
    frontier (leftComponent η) ⊆ theta η := by
  rw [(isOpen_leftComponent hη).frontier_eq]
  rintro w ⟨hwc, hwD⟩
  have hw0 : 0 ≤ w.im := closure_subset_Hbar (leftComponent_subset_H η) hwc
  by_cases hK : w ∈ chordSet η
  · exact Or.inr hK
  rcases hw0.eq_or_lt with h | h
  · exact Or.inl h.symm
  · exact absurd (mem_leftComponent_of_mem_closure hη hwc ⟨h, hK⟩) hwD

/-- **U1 (negative axis).** `(-∞, 0) ⊆ closure (leftComponent η)`. -/
theorem ofReal_mem_closure_leftComponent (hη : IsSimpleChord η) {x : ℝ} (hx : x < 0) :
    (x : ℂ) ∈ closure (leftComponent η) := by
  obtain ⟨δ, hδ, hball⟩ := exists_nhd_mem_cc hη hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  set h : ℝ := min ε δ / 2 with hhdef
  have hh0 : 0 < h := half_pos (lt_min hε hδ)
  have hdist : dist ((x : ℂ) + (h : ℂ) * Complex.I) x = h := by
    simp [dist_eq_norm, abs_of_pos hh0]
  refine ⟨(x : ℂ) + (h : ℂ) * Complex.I, ?_, ?_⟩
  · rw [leftComponent_eq hη]
    refine hball _ (by simp [H, hh0]) ?_
    rw [hdist, hhdef]
    linarith [min_le_right ε δ]
  · rw [dist_comm, hdist, hhdef]
    linarith [min_le_left ε δ]

/-- **U1 (base point).** `0 ∈ closure (leftComponent η)`. -/
theorem zero_mem_closure_leftComponent (hη : IsSimpleChord η) :
    (0 : ℂ) ∈ closure (leftComponent η) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx : -(ε / 2) < 0 := by linarith
  obtain ⟨b, hb, hbd⟩ :=
    Metric.mem_closure_iff.1 (ofReal_mem_closure_leftComponent hη hx) (ε / 2) (half_pos hε)
  refine ⟨b, hb, ?_⟩
  have : dist (0 : ℂ) ((-(ε / 2) : ℝ) : ℂ) = ε / 2 := by
    simp [dist_eq_norm, abs_of_pos hε]
  linarith [dist_triangle (0 : ℂ) ((-(ε / 2) : ℝ) : ℂ) b]

end QuantumZipper.CA.Uniformizer

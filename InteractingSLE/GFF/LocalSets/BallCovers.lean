import InteractingSLE.GFF.LocalSets.Characterization

/-!
# Finitely-valued covers of random sets in `ℍ`

Specification §3.2, proof of Lemma 3.6, (i) ⇒ (iii), p. 52 (square covers `Â_δ`) and the germ
identification, p. 50 ("nested dyadic square covers `C_n` of `A` such that each `C_n` has only
finitely many possible values, `A_{2^{-n}} ⊆ C_n ⊆ A_{(1+√2)2^{-n}}`, `C_n ↓ A`"). The source takes
`D` bounded; on the unbounded `ℍ` (ruling R19 (5)) the covers are truncated as the spherical
metric of p. 49 suggests (PROVE-LS-B handoff, item 1 (a)): the cover of level `j` of a set `S` is
`C_j(S) = ℍ ∖ W_j(S)`, where `W_j(S)` (`coverCompl j S`) is the union of those balls of a fixed
finite family (levels `k ≤ j`, radii `1/(k+2)`, covering `{3/(k+2) ≤ Im z, |z| ≤ k + 1}`) whose
`1/(j+2)`-thickening avoids `S`. Balls are used instead of squares (same role, simpler geometry).

## Main results

* `measurableSet_removedIdx_eq` : `C_j(S)` takes finitely many values, each on a hitting-measurable
  set of `S`;
* `coverCompl_mono`, `disjoint_coverCompl`, `iUnion_coverCompl` : `W_j(S)` increases to `ℍ ∖ S`;
* `isCompact_closure_coverOpen`, `coverOpen_subset_H` : `W_j(S)` is relatively compact in `ℍ`;
* `disjoint_germNbhd_coverCompl` : the germ neighbourhood of radius `1/(j+2)` lies in `C_j(S)`;
* `mem_germNbhd_of_dist_lt` : for `j ≥ ⌈6/δ⌉`, the `3δ/8`-neighbourhood of `C_j(S)` in `ℍ` lies in the
  germ neighbourhood of radius `δ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace Metric

namespace InteractingSLE
namespace LocalSets

open QuantumZipper

/-- The radius of the balls of level `k`. -/
def coverRad (k : ℕ) : ℝ := 1 / ((k : ℝ) + 2)

lemma coverRad_pos (k : ℕ) : 0 < coverRad k := by unfold coverRad; positivity

lemma coverRad_le_half (k : ℕ) : coverRad k ≤ 1 / 2 := by
  unfold coverRad
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])

lemma coverRad_anti {k j : ℕ} (h : k ≤ j) : coverRad j ≤ coverRad k := by
  unfold coverRad
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : k + 2 ≤ j + 2))

/-- The compact region covered at level `k`. -/
def coverRegion (k : ℕ) : Set ℂ := {w | 3 * coverRad k ≤ w.im ∧ ‖w‖ ≤ (k : ℝ) + 1}

lemma isCompact_coverRegion (k : ℕ) : IsCompact (coverRegion k) := by
  refine (isCompact_closedBall (0 : ℂ) ((k : ℝ) + 1)).of_isClosed_subset ?_ ?_
  · exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le continuous_norm continuous_const)
  · intro w hw
    simpa [mem_closedBall, dist_zero_right] using hw.2

lemma exists_centers (k : ℕ) : ∃ t : Finset ℂ, (↑t : Set ℂ) ⊆ coverRegion k ∧
    coverRegion k ⊆ ⋃ c ∈ t, ball c (coverRad k) := by
  obtain ⟨t, hts, htf, hcov⟩ := finite_cover_balls_of_compact (isCompact_coverRegion k)
    (coverRad_pos k)
  exact ⟨htf.toFinset, by simpa using hts, by simpa using hcov⟩

/-- Finitely many centers of level `k` whose balls cover the region of level `k`. -/
def centers (k : ℕ) : Finset ℂ := (exists_centers k).choose

lemma centers_subset (k : ℕ) : (↑(centers k) : Set ℂ) ⊆ coverRegion k :=
  (exists_centers k).choose_spec.1

lemma coverRegion_subset (k : ℕ) : coverRegion k ⊆ ⋃ c ∈ centers k, ball c (coverRad k) :=
  (exists_centers k).choose_spec.2

/-- The indices (level, center) of the balls of levels `≤ j`. -/
def coverIdx (j : ℕ) : Finset (ℕ × ℂ) :=
  (Finset.range (j + 1)).biUnion fun k => (centers k).image (Prod.mk k)

lemma mem_coverIdx {j : ℕ} {i : ℕ × ℂ} : i ∈ coverIdx j ↔ i.1 ≤ j ∧ i.2 ∈ centers i.1 := by
  obtain ⟨k, c⟩ := i
  simp only [coverIdx, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨k', hk', c', hc', rfl, rfl⟩; exact ⟨by omega, hc'⟩
  · rintro ⟨hk, hc⟩; exact ⟨k, by omega, c, hc, rfl, rfl⟩

lemma coverIdx_mono {j j' : ℕ} (h : j ≤ j') : coverIdx j ⊆ coverIdx j' := fun i hi => by
  rw [mem_coverIdx] at hi ⊢; exact ⟨hi.1.trans h, hi.2⟩

/-- The ball with index `i`. -/
def coverBall (i : ℕ × ℂ) : Set ℂ := ball i.2 (coverRad i.1)

/-- Points of a thickened ball of an index of `coverIdx j` lie in `ℍ`, at height `> coverRad i.1`
and in the disc of radius `j + 2`. -/
lemma mem_thickening_coverBall {j : ℕ} {i : ℕ × ℂ} (hi : i ∈ coverIdx j) {z : ℂ}
    (hz : z ∈ thickening (coverRad j) (coverBall i)) :
    coverRad i.1 < z.im ∧ ‖z‖ < (j : ℝ) + 2 := by
  rw [mem_coverIdx] at hi
  have hc := centers_subset i.1 hi.2
  have hrad := coverRad_anti hi.1
  have hd : dist z i.2 < 2 * coverRad i.1 := by
    have h1 : z ∈ ball i.2 (coverRad j + coverRad i.1) := by
      have := thickening_ball (coverRad_pos j) (coverRad_pos i.1) i.2
      unfold coverBall at hz; rw [this] at hz; exact hz
    rw [mem_ball] at h1; linarith
  have him : |z.im - i.2.im| ≤ dist z i.2 := by
    rw [Complex.dist_eq]; exact (Complex.abs_im_le_norm (z - i.2)).trans_eq' (by simp)
  have hnorm : ‖z‖ ≤ ‖i.2‖ + dist z i.2 := by
    rw [dist_eq_norm]; linarith [norm_le_insert' z i.2]
  have hk : (i.1 : ℝ) ≤ j := by exact_mod_cast hi.1
  constructor
  · have := hc.1; rw [abs_le] at him; linarith
  · have := hc.2; have := coverRad_le_half i.1; linarith

open Classical in
/-- The balls of levels `≤ j` whose `coverRad j`-thickening avoids `S`. -/
def removedIdx (j : ℕ) (S : Set ℂ) : Finset (ℕ × ℂ) :=
  (coverIdx j).filter fun i => Disjoint (thickening (coverRad j) (coverBall i)) S

lemma mem_removedIdx {j : ℕ} {S : Set ℂ} {i : ℕ × ℂ} :
    i ∈ removedIdx j S ↔ i ∈ coverIdx j ∧ Disjoint (thickening (coverRad j) (coverBall i)) S := by
  classical
  simp [removedIdx]

lemma removedIdx_subset (j : ℕ) (S : Set ℂ) : removedIdx j S ⊆ coverIdx j := fun _ hi =>
  (mem_removedIdx.1 hi).1

lemma removedIdx_mono {j j' : ℕ} (h : j ≤ j') (S : Set ℂ) : removedIdx j S ⊆ removedIdx j' S := by
  intro i hi
  rw [mem_removedIdx] at hi ⊢
  exact ⟨coverIdx_mono h hi.1, hi.2.mono_left (thickening_mono (coverRad_anti h) _)⟩

/-- The open set covered by the balls with indices in `T`. -/
def coverOpen (T : Finset (ℕ × ℂ)) : Set ℂ := ⋃ i ∈ T, coverBall i

lemma isOpen_coverOpen (T : Finset (ℕ × ℂ)) : IsOpen (coverOpen T) :=
  isOpen_biUnion fun _ _ => isOpen_ball

lemma coverOpen_mono {T T' : Finset (ℕ × ℂ)} (h : T ⊆ T') : coverOpen T ⊆ coverOpen T' :=
  biUnion_subset_biUnion_left (by exact_mod_cast h)

/-- The complement `W_j(S) = ℍ ∖ C_j(S)` of the cover of level `j` of `S`. -/
def coverCompl (j : ℕ) (S : Set ℂ) : Set ℂ := coverOpen (removedIdx j S)

lemma coverCompl_mono {j j' : ℕ} (h : j ≤ j') (S : Set ℂ) : coverCompl j S ⊆ coverCompl j' S :=
  coverOpen_mono (removedIdx_mono h S)

lemma coverBall_subset_thickening {r : ℝ} (hr : 0 < r) (i : ℕ × ℂ) :
    coverBall i ⊆ thickening r (coverBall i) := self_subset_thickening hr _

/-- Closed bounded sets of `ℍ`: the closure of `coverOpen T` for `T ⊆ coverIdx j`. -/
lemma closure_coverOpen_subset {j : ℕ} {T : Finset (ℕ × ℂ)} (hT : T ⊆ coverIdx j) :
    closure (coverOpen T) ⊆ H ∩ closedBall (0 : ℂ) ((j : ℝ) + 2) := by
  have hsub : coverOpen T ⊆ {z : ℂ | coverRad j ≤ z.im} ∩ closedBall (0 : ℂ) ((j : ℝ) + 2) := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
    have := mem_thickening_coverBall (hT hi) (coverBall_subset_thickening (coverRad_pos j) i hzi)
    have hle := coverRad_anti (mem_coverIdx.1 (hT hi)).1
    exact ⟨(lt_of_le_of_lt hle this.1).le, by rw [mem_closedBall, dist_zero_right]; exact this.2.le⟩
  refine (closure_minimal hsub ((isClosed_le continuous_const Complex.continuous_im).inter
    isClosed_closedBall)).trans fun z hz => ⟨?_, hz.2⟩
  exact lt_of_lt_of_le (coverRad_pos j) hz.1

lemma isCompact_closure_coverOpen {j : ℕ} {T : Finset (ℕ × ℂ)} (hT : T ⊆ coverIdx j) :
    IsCompact (closure (coverOpen T)) :=
  (isCompact_closedBall (0 : ℂ) _).of_isClosed_subset isClosed_closure
    ((closure_coverOpen_subset hT).trans inter_subset_right)

lemma coverOpen_subset_H {j : ℕ} {T : Finset (ℕ × ℂ)} (hT : T ⊆ coverIdx j) : coverOpen T ⊆ H :=
  subset_closure.trans ((closure_coverOpen_subset hT).trans inter_subset_left)

lemma coverCompl_subset_H (j : ℕ) (S : Set ℂ) : coverCompl j S ⊆ H :=
  coverOpen_subset_H (removedIdx_subset j S)

/-- Each point of `W_j(S)` has a `coverRad j`-ball avoiding `S`. -/
lemma disjoint_ball_of_mem_coverCompl {j : ℕ} {S : Set ℂ} {z : ℂ} (hz : z ∈ coverCompl j S) :
    Disjoint (ball z (coverRad j)) S := by
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
  refine (mem_removedIdx.1 hi).2.mono_left fun w hw => ?_
  exact mem_thickening_iff.2 ⟨z, hzi, mem_ball.1 hw⟩

lemma disjoint_coverCompl (j : ℕ) (S : Set ℂ) : Disjoint (coverCompl j S) S :=
  Set.disjoint_left.2 fun _ hz hzS =>
    Set.disjoint_left.1 (disjoint_ball_of_mem_coverCompl hz) (mem_ball_self (coverRad_pos j)) hzS

/-- Points of `ℍ` at positive distance from `S` are eventually in `W_j(S)`. -/
lemma exists_mem_coverCompl {S : Set ℂ} {z : ℂ} (hz : z ∈ H) {r : ℝ} (hr : 0 < r)
    (hzr : Disjoint (ball z r) S) : ∃ j, z ∈ coverCompl j S := by
  have hzim : 0 < z.im := hz
  obtain ⟨k, hk⟩ := exists_nat_gt (max (6 / z.im) (max (6 / r) ‖z‖))
  have hk1 : 6 / z.im < k := lt_of_le_of_lt (le_max_left _ _) hk
  have hk2 : 6 / r < k := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hk
  have hk3 : ‖z‖ < k := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hk
  have hρ : coverRad k * ((k : ℝ) + 2) = 1 := by unfold coverRad; field_simp
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk3
  have h3a : 3 * coverRad k ≤ z.im := by
    rw [div_lt_iff₀ hzim] at hk1; nlinarith [coverRad_pos k]
  have h3b : 3 * coverRad k < r := by
    rw [div_lt_iff₀ hr] at hk2; nlinarith [coverRad_pos k]
  have hzreg : z ∈ coverRegion k := ⟨h3a, by linarith⟩
  obtain ⟨c, hc, hzc⟩ := mem_iUnion₂.1 (coverRegion_subset k hzreg)
  refine ⟨k, mem_iUnion₂.2 ⟨(k, c), mem_removedIdx.2 ⟨mem_coverIdx.2 ⟨le_rfl, hc⟩, ?_⟩, hzc⟩⟩
  refine hzr.mono_left fun w hw => ?_
  have h1 : w ∈ ball c (coverRad k + coverRad k) := by
    have := thickening_ball (coverRad_pos k) (coverRad_pos k) c
    unfold coverBall at hw; rw [this] at hw; exact hw
  rw [mem_ball] at h1 hzc ⊢
  calc dist w z ≤ dist w c + dist z c := dist_triangle_right _ _ _
    _ < r := by linarith

/-- (Germ neighbourhoods inside the covers.) The germ neighbourhood of radius `coverRad j` of `S`
avoids `W_j(S)`. -/
lemma disjoint_germNbhd_coverCompl (j : ℕ) (S : Set ℂ) :
    Disjoint (germNbhd (coverRad j) S) (coverCompl j S) := by
  refine Set.disjoint_right.2 fun z hz hzg => ?_
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
  have hiI := (mem_removedIdx.1 hi).1
  obtain ⟨him, hnorm⟩ := mem_thickening_coverBall hiI
    (coverBall_subset_thickening (coverRad_pos j) i hzi)
  have hle := coverRad_anti (mem_coverIdx.1 hiI).1
  have hball := disjoint_ball_of_mem_coverCompl hz
  have hinv : 1 / coverRad j = (j : ℝ) + 2 := by unfold coverRad; field_simp
  rcases hzg.2 with h1 | h1
  · rw [thickening_union] at h1
    rcases h1 with h2 | h2
    · obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.1 h2
      exact Set.disjoint_left.1 hball (mem_ball.2 (by rw [dist_comm]; exact hzw)) hw.1
    · obtain ⟨w, hw, hzw⟩ := mem_thickening_iff.1 h2
      have : |z.im - w.im| ≤ dist z w := by
        rw [Complex.dist_eq]; exact Complex.abs_im_le_norm (z - w) |>.trans_eq' (by simp)
      have hw0 : w.im = 0 := hw
      rw [hw0, sub_zero, abs_le] at this
      linarith
  · have : 1 / coverRad j < ‖z‖ := h1
    rw [hinv] at this
    linarith

/-- (Covers inside germ neighbourhoods.) For `0 < δ ≤ 1` and `j ≥ ⌈6/δ⌉`, every point of `ℍ`
within `3δ/8` of a point outside `W_j(S)` lies in the germ neighbourhood of radius `δ` of `S`. -/
lemma mem_germNbhd_of_dist_lt {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {j : ℕ}
    (hj : ⌈6 / δ⌉₊ ≤ j) {S : Set ℂ} {z w : ℂ} (hz : z ∈ H) (hw : w ∉ coverCompl j S)
    (hzw : dist z w < 3 * (δ / 8)) : z ∈ germNbhd δ S := by
  have hzim : |z.im - w.im| ≤ dist z w := by
    rw [Complex.dist_eq]; exact Complex.abs_im_le_norm (z - w) |>.trans_eq' (by simp)
  have hzn : ‖w‖ ≤ ‖z‖ + dist z w := by
    rw [dist_eq_norm]; linarith [norm_sub_norm_le w z, norm_sub_rev z w]
  rw [abs_le] at hzim
  refine ⟨hz, ?_⟩
  by_cases h1 : w.im ≤ δ / 2
  · refine Or.inl ?_
    rw [thickening_union]
    refine Or.inr (mem_thickening_iff.2 ⟨(z.re : ℂ), ?_, ?_⟩)
    · show ((z.re : ℂ)).im = 0
      simp
    · rw [Complex.dist_eq]
      have : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hz]
      linarith
  push Not at h1
  by_cases h2 : 2 / δ < ‖w‖
  · refine Or.inr ?_
    show 1 / δ < ‖z‖
    have : 1 / δ + 3 * (δ / 8) ≤ 2 / δ := by
      rw [show 2 / δ = 1 / δ + 1 / δ by ring]
      have : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
      linarith
    linarith
  push Not at h2
  by_cases h3 : ∃ s ∈ S, dist w s < δ / 2
  · obtain ⟨s, hs, hws⟩ := h3
    have hsim : |w.im - s.im| ≤ dist w s := by
      rw [Complex.dist_eq]; exact Complex.abs_im_le_norm (w - s) |>.trans_eq' (by simp)
    rw [abs_le] at hsim
    refine Or.inl ?_
    rw [thickening_union]
    refine Or.inl (mem_thickening_iff.2 ⟨s, ⟨hs, ?_⟩, ?_⟩)
    · show 0 < s.im
      linarith
    · calc dist z s ≤ dist z w + dist w s := dist_triangle _ _ _
        _ < δ := by linarith
  · push Not at h3
    exfalso
    apply hw
    set k := ⌈6 / δ⌉₊
    have hk : 6 / δ ≤ k := Nat.le_ceil _
    have hkρ : coverRad k ≤ δ / 6 := by
      unfold coverRad
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_le_iff₀ hδ] at hk
      nlinarith
    have hwreg : w ∈ coverRegion k := by
      refine ⟨by linarith, ?_⟩
      have : 2 / δ ≤ 6 / δ := div_le_div_of_nonneg_right (by norm_num) hδ.le
      linarith
    obtain ⟨c, hc, hwc⟩ := mem_iUnion₂.1 (coverRegion_subset k hwreg)
    refine mem_iUnion₂.2 ⟨(k, c), mem_removedIdx.2 ⟨mem_coverIdx.2 ⟨hj, hc⟩, ?_⟩, hwc⟩
    refine Set.disjoint_left.2 fun v hv hvS => ?_
    have hjρ := coverRad_anti hj
    have h1v : v ∈ ball c (coverRad j + coverRad k) := by
      have := thickening_ball (coverRad_pos j) (coverRad_pos k) c
      unfold coverBall at hv; rw [this] at hv; exact hv
    rw [mem_ball] at h1v hwc
    have := h3 v hvS
    have : dist w v ≤ dist w c + dist v c := dist_triangle_right _ _ _
    linarith

/-- The pattern `removedIdx j S = T` is a hitting-measurable property of `S`. -/
lemma measurableSet_removedIdx_eq (j : ℕ) (T : Finset (ℕ × ℂ)) :
    MeasurableSet[hittingSigma] {S : Set ℂ | removedIdx j S = T} := by
  classical
  have hset : {S : Set ℂ | removedIdx j S = T} =
      {_S : Set ℂ | T ⊆ coverIdx j} ∩ ⋂ i ∈ coverIdx j,
        {S : Set ℂ | i ∈ T ↔ Disjoint (thickening (coverRad j) (coverBall i)) S} := by
    ext S
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro rfl
      exact ⟨removedIdx_subset j S, fun i hi => by rw [mem_removedIdx]; exact ⟨fun h => h.2,
        fun h => ⟨hi, h⟩⟩⟩
    · rintro ⟨hT, hi⟩
      ext i
      rw [mem_removedIdx]
      constructor
      · rintro ⟨hi1, hi2⟩; exact (hi i hi1).2 (by simpa [disjoint_comm] using hi2)
      · intro hiT; exact ⟨hT hiT, by simpa [disjoint_comm] using (hi i (hT hiT)).1 hiT⟩
  rw [hset]
  refine MeasurableSet.inter (MeasurableSet.const _) (Finset.measurableSet_biInter _ fun i hi => ?_)
  have hO : IsOpen (thickening (coverRad j) (coverBall i)) := isOpen_thickening
  have hOH : thickening (coverRad j) (coverBall i) ⊆ H := fun z hz =>
    lt_trans (coverRad_pos i.1) (mem_thickening_coverBall hi hz).1
  have hm : MeasurableSet[hittingSigma]
      {S : Set ℂ | Disjoint S (thickening (coverRad j) (coverBall i))} :=
    measurableSet_avoid hO hOH
  by_cases hiT : i ∈ T
  · have e : {S : Set ℂ | i ∈ T ↔ Disjoint (thickening (coverRad j) (coverBall i)) S} =
        {S : Set ℂ | Disjoint S (thickening (coverRad j) (coverBall i))} := by
      ext S; simp [hiT, disjoint_comm]
    rw [e]; exact hm
  · have e : {S : Set ℂ | i ∈ T ↔ Disjoint (thickening (coverRad j) (coverBall i)) S} =
        {S : Set ℂ | Disjoint S (thickening (coverRad j) (coverBall i))}ᶜ := by
      ext S; simp [hiT, disjoint_comm]
    rw [e]; exact hm.compl

/-- The union of the thickened balls with indices in `T`. -/
def coverThick (j : ℕ) (T : Finset (ℕ × ℂ)) : Set ℂ :=
  ⋃ i ∈ T, thickening (coverRad j) (coverBall i)

lemma isOpen_coverThick (j : ℕ) (T : Finset (ℕ × ℂ)) : IsOpen (coverThick j T) :=
  isOpen_biUnion fun _ _ => isOpen_thickening

lemma coverOpen_subset_coverThick (j : ℕ) (T : Finset (ℕ × ℂ)) :
    coverOpen T ⊆ coverThick j T :=
  biUnion_mono subset_rfl fun i _ => coverBall_subset_thickening (coverRad_pos j) i

lemma coverThick_subset_H {j : ℕ} {T : Finset (ℕ × ℂ)} (hT : T ⊆ coverIdx j) :
    coverThick j T ⊆ H := iUnion₂_subset fun i hi _ hz =>
  lt_trans (coverRad_pos i.1) (mem_thickening_coverBall (hT hi) hz).1

lemma disjoint_coverThick_removedIdx (j : ℕ) (S : Set ℂ) :
    Disjoint S (coverThick j (removedIdx j S)) := by
  refine Set.disjoint_right.2 fun z hz hzS => ?_
  obtain ⟨i, hi, hzi⟩ := mem_iUnion₂.1 hz
  exact Set.disjoint_left.1 (mem_removedIdx.1 hi).2 hzi hzS

/-- For a relatively closed `S ⊆ ℍ`, the complements `W_j(S)` exhaust `ℍ ∖ S`. -/
lemma iUnion_coverCompl {S : Set ℂ} (hSo : IsOpen (H \ S)) :
    ⋃ j, coverCompl j S = H \ S := by
  refine subset_antisymm (iUnion_subset fun j z hz =>
    ⟨coverCompl_subset_H j S hz, Set.disjoint_left.1 (disjoint_coverCompl j S) hz⟩) ?_
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hSo z hz
  have hr2 : Disjoint (ball z (min r (z.im))) S := by
    refine Set.disjoint_left.2 fun w hw hwS => ?_
    have hwr : w ∈ ball z r := ball_subset_ball (min_le_left _ _) hw
    exact (hball hwr).2 hwS
  obtain ⟨j, hj⟩ := exists_mem_coverCompl hz.1 (lt_min hr hz.1) hr2
  exact mem_iUnion.2 ⟨j, hj⟩

end LocalSets
end InteractingSLE

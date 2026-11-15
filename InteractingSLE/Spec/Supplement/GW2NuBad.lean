/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NuOrd
import InteractingSLE.Spec.Supplement.GW2SfPullback

/-!
# A bad point of the launch word maps to a bad point of the joint word

Packet PROVE-GW2-NOTHR (round 3, D35 (D-a)). SAFE's `GW2Sf.notMem_hitSet_of_boundary_chart` pulls the bad set
back through a real boundary chart `φ`. At the death the forward direction is needed: if `x` is a bad point of the
launch word `(b, J)` at angle `θ`, then `φ x` is a bad point of the chart word `(bR, JR)`. That holds when the chart
keeps the order of real points near `x` and matches the data (`bR (φ u) = b u + θ χ`). The cumulative weights are
`cumWeightRight`/`cumWeightLeft` of the data just right/left of the point. Labels are finite, so a point just beside
`φ x` with a real preimage just beside `x` carries the same weights (`Aux37Side.exists_ball_image`).

* **`sumR_le_of_boundary_chart`**, **`sumL_le_of_boundary_chart`**: the transfer (right, left).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Finset
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Nu

open GW2Rd

/-- A finite set of reals has a gap above any point. -/
theorem exists_gap_above (F : Finset ℝ) (x : ℝ) : ∃ δ > 0, ∀ z ∈ F, x < z → x + δ ≤ z := by
  classical
  by_cases hne : (F.filter (fun z => x < z)).Nonempty
  · obtain ⟨z₀, hz₀, hmin⟩ := (F.filter (fun z => x < z)).exists_min_image (fun z => z - x) hne
    refine ⟨z₀ - x, by linarith [(Finset.mem_filter.1 hz₀).2], fun z hz hxz => ?_⟩
    have := hmin z (Finset.mem_filter.2 ⟨hz, hxz⟩)
    linarith
  · refine ⟨1, one_pos, fun z hz hxz => absurd ⟨z, Finset.mem_filter.2 ⟨hz, hxz⟩⟩ hne⟩

/-- A finite set of reals has a gap below any point. -/
theorem exists_gap_below (F : Finset ℝ) (x : ℝ) : ∃ δ > 0, ∀ z ∈ F, z < x → z ≤ x - δ := by
  obtain ⟨δ, hδ, h⟩ := exists_gap_above (F.image Neg.neg) (-x)
  refine ⟨δ, hδ, fun z hz hzx => ?_⟩
  have := h (-z) (Finset.mem_image_of_mem _ hz) (by linarith)
  linarith

/-- A real boundary chart on a ball is one on every smaller ball. -/
theorem isRealBoundaryConformal_mono {φ : ℂ → ℂ} {x r r₁ : ℝ} (h : R16.IsRealBoundaryConformal φ x r)
    (hr : r₁ ≤ r) : R16.IsRealBoundaryConformal φ x r₁ := by
  have hb : ball (x : ℂ) r₁ ⊆ ball (x : ℂ) r := ball_subset_ball hr
  exact ⟨h.1.mono (inter_subset_inter_right _ hb), h.2.1.mono (inter_subset_inter_right _ hb),
    fun z hz => h.2.2.1 z (hb hz), h.2.2.2.1.mono_left (inter_subset_inter_right _ hb),
    h.2.2.2.2.mono (inter_subset_inter_right _ hb)⟩

/-- A nonempty open interval contains a point off any finite set. -/
theorem exists_mem_Ioo_notMem {a b : ℝ} (hab : a < b) {F : Set ℝ} (hF : F.Finite) : ∃ q ∈ Ioo a b, q ∉ F := by
  obtain ⟨q, hq⟩ := ((Set.Ioo_infinite hab).sdiff hF).nonempty
  exact ⟨q, hq.1, hq.2⟩

variable {κ θ : ℝ} {b bR : ℝ → ℝ} {J JR : Finset ℝ}

/-- **Right bad points move forward through a real boundary chart.** -/
theorem sumR_le_of_boundary_chart (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {φ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hφ : R16.IsRealBoundaryConformal φ x r) (hx : 0 < x) (hφx : 0 < (φ x).re)
    (hmono : ∀ u ∈ Ioo (x - r) (x + r), u ≤ x → (φ u).re ≤ (φ x).re)
    {E : Set ℝ} (hE : E.Finite) (hEJ : (J : Set ℝ) ⊆ E)
    (hheight : ∀ u ∈ Ioo (x - r) (x + r), u ∉ E → (φ u).re ∉ JR → bR (φ u).re = b u + θ * chiC κ)
    (hbad : ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ x), flowLineRhoR κ b J 0 θ i ≤ -2) :
    ∑ j ∈ univ.filter (fun j => flowLineXR bR JR 0 j ≤ (φ x).re), flowLineRhoR κ bR JR 0 0 j ≤ -2 := by
  classical
  set q := (φ x).re with hqdef
  obtain ⟨δ, hδ, hδJ⟩ := exists_gap_above J x
  obtain ⟨δR, hδR, hδRJ⟩ := exists_gap_above JR q
  set r₁ := min r δ with hr₁def
  have hr₁ : 0 < r₁ := lt_min hr hδ
  have hφ₁ := isRealBoundaryConformal_mono hφ (min_le_left r δ)
  obtain ⟨ε, hε, himg⟩ := Sec7.Aux37Side.exists_ball_image hφ₁ (y := x) (mem_ball_self hr₁)
  have hφxr : φ x = (q : ℂ) := Complex.ext (by simp [hqdef]) (by
    simpa using hφ.2.2.1 x (mem_ball_self hr) (by simp))
  set F : Set ℝ := (JR : Set ℝ) ∪ (fun e : ℝ => (φ (e : ℂ)).re) '' E with hFdef
  have hF : F.Finite := JR.finite_toSet.union (hE.image _)
  obtain ⟨q', hq', hq'F⟩ := exists_mem_Ioo_notMem (show q < q + min ε δR by
    have := lt_min hε hδR; linarith) hF
  obtain ⟨u, hub, -, hu, -, hu0⟩ := himg (q' : ℂ) (by
    rw [mem_ball, hφxr, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith [hq'.1])]
    linarith [hq'.2, min_le_left ε δR]) (by simp)
  have huim : u.im = 0 := hu0 (by simp)
  have hue : u = (u.re : ℂ) := Complex.ext rfl (by simpa using huim)
  have huI : u.re ∈ Ioo (x - r₁) (x + r₁) := Sec7.Aux37Side.ofReal_mem_ball_iff.1 (hue ▸ hub)
  have huI' : u.re ∈ Ioo (x - r) (x + r) :=
    ⟨by linarith [huI.1, min_le_left r δ], by linarith [huI.2, min_le_left r δ]⟩
  have hφu : (φ (u.re : ℂ)).re = q' := by rw [← hue, hu, Complex.ofReal_re]
  have huE : u.re ∉ E := fun h => hq'F (Or.inr ⟨u.re, h, hφu⟩)
  have hq'JR : q' ∉ JR := fun h => hq'F (Or.inl h)
  have hxu : x < u.re := by
    by_contra hle
    have := hmono u.re huI' (not_lt.1 hle)
    rw [hφu] at this
    linarith [hq'.1]
  have hupos : 0 < u.re := hx.trans hxu
  have huJ : u.re ∉ J := fun h => huE (hEJ h)
  -- the launch sum is constant on `[x, u]`
  have hL : ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ u.re), flowLineRhoR κ b J 0 θ i =
      ∑ i ∈ univ.filter (fun i => flowLineXR b J 0 i ≤ x), flowLineRhoR κ b J 0 θ i := by
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => h.trans hxu.le⟩) fun _ _ => rfl
    by_contra hgt
    rcases flowLineXR_eq_zero_or_mem b J i with h0 | hJ
    · rw [h0] at hgt; linarith
    · have := hδJ _ hJ (not_le.1 hgt)
      linarith [huI.2, min_le_right r δ]
  -- the chart sum is constant on `[q, q']`
  have hR : ∑ j ∈ univ.filter (fun j => flowLineXR bR JR 0 j ≤ q'), flowLineRhoR κ bR JR 0 0 j =
      ∑ j ∈ univ.filter (fun j => flowLineXR bR JR 0 j ≤ q), flowLineRhoR κ bR JR 0 0 j := by
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => ?_, fun h => h.trans hq'.1.le⟩)
      fun _ _ => rfl
    by_contra hgt
    rcases flowLineXR_eq_zero_or_mem bR JR j with h0 | hJ
    · rw [h0] at hgt; linarith
    · have := hδRJ _ hJ (not_le.1 hgt)
      linarith [hq'.2, min_le_right ε δR]
  have h1 := sum_filter_flowLineXR_le_theta (θ := θ) hκ hb hupos huJ
  have h2 := sum_filter_flowLineXR_le_theta (θ := 0) hκ hbR (hφx.trans hq'.1) hq'JR
  have hh := hheight u.re huI' huE (by rw [hφu]; exact hq'JR)
  rw [hφu] at hh
  rw [← hR, h2, zero_mul, add_zero, hh, ← h1, hL]
  exact hbad

/-- **Left bad points move forward through a real boundary chart** (mirror form). -/
theorem sumL_le_of_boundary_chart (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b J)
    (hbR : IsPiecewiseConstantBoundaryData bR JR) {φ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r)
    (hφ : R16.IsRealBoundaryConformal φ x r) (hx : x < 0) (hφx : (φ x).re < 0)
    (hmono : ∀ u ∈ Ioo (x - r) (x + r), x ≤ u → (φ x).re ≤ (φ u).re)
    {E : Set ℝ} (hE : E.Finite) (hEJ : (J : Set ℝ) ⊆ E)
    (hheight : ∀ u ∈ Ioo (x - r) (x + r), u ∉ E → (φ u).re ∉ JR → bR (φ u).re = b u + θ * chiC κ)
    (hbad : ∑ i ∈ univ.filter (fun i => x ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i ≤ -2) :
    ∑ j ∈ univ.filter (fun j => (φ x).re ≤ flowLineXL bR JR 0 j), flowLineRhoL κ bR JR 0 0 j ≤ -2 := by
  classical
  set q := (φ x).re with hqdef
  obtain ⟨δ, hδ, hδJ⟩ := exists_gap_below J x
  obtain ⟨δR, hδR, hδRJ⟩ := exists_gap_below JR q
  set r₁ := min r δ with hr₁def
  have hr₁ : 0 < r₁ := lt_min hr hδ
  have hφ₁ := isRealBoundaryConformal_mono hφ (min_le_left r δ)
  obtain ⟨ε, hε, himg⟩ := Sec7.Aux37Side.exists_ball_image hφ₁ (y := x) (mem_ball_self hr₁)
  have hφxr : φ x = (q : ℂ) := Complex.ext (by simp [hqdef]) (by
    simpa using hφ.2.2.1 x (mem_ball_self hr) (by simp))
  set F : Set ℝ := (JR : Set ℝ) ∪ (fun e : ℝ => (φ (e : ℂ)).re) '' E with hFdef
  have hF : F.Finite := JR.finite_toSet.union (hE.image _)
  obtain ⟨q', hq', hq'F⟩ := exists_mem_Ioo_notMem (show q - min ε δR < q by
    have := lt_min hε hδR; linarith) hF
  obtain ⟨u, hub, -, hu, -, hu0⟩ := himg (q' : ℂ) (by
    rw [mem_ball, hφxr, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith [hq'.2])]
    linarith [hq'.1, min_le_left ε δR]) (by simp)
  have huim : u.im = 0 := hu0 (by simp)
  have hue : u = (u.re : ℂ) := Complex.ext rfl (by simpa using huim)
  have huI : u.re ∈ Ioo (x - r₁) (x + r₁) := Sec7.Aux37Side.ofReal_mem_ball_iff.1 (hue ▸ hub)
  have huI' : u.re ∈ Ioo (x - r) (x + r) :=
    ⟨by linarith [huI.1, min_le_left r δ], by linarith [huI.2, min_le_left r δ]⟩
  have hφu : (φ (u.re : ℂ)).re = q' := by rw [← hue, hu, Complex.ofReal_re]
  have huE : u.re ∉ E := fun h => hq'F (Or.inr ⟨u.re, h, hφu⟩)
  have hq'JR : q' ∉ JR := fun h => hq'F (Or.inl h)
  have hux : u.re < x := by
    by_contra hle
    have := hmono u.re huI' (not_lt.1 hle)
    rw [hφu] at this
    linarith [hq'.2]
  have huneg : u.re < 0 := hux.trans hx
  have huJ : u.re ∉ J := fun h => huE (hEJ h)
  have hL : ∑ i ∈ univ.filter (fun i => u.re ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i =
      ∑ i ∈ univ.filter (fun i => x ≤ flowLineXL b J 0 i), flowLineRhoL κ b J 0 θ i := by
    refine Finset.sum_congr (Finset.filter_congr fun i _ => ⟨fun h => ?_, fun h => hux.le.trans h⟩) fun _ _ => rfl
    by_contra hlt
    rcases flowLineXL_eq_zero_or_mem b J i with h0 | hJ
    · rw [h0] at hlt; linarith
    · have := hδJ _ hJ (not_le.1 hlt)
      linarith [huI.1, min_le_right r δ]
  have hR : ∑ j ∈ univ.filter (fun j => q' ≤ flowLineXL bR JR 0 j), flowLineRhoL κ bR JR 0 0 j =
      ∑ j ∈ univ.filter (fun j => q ≤ flowLineXL bR JR 0 j), flowLineRhoL κ bR JR 0 0 j := by
    refine Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => ?_, fun h => hq'.2.le.trans h⟩)
      fun _ _ => rfl
    by_contra hlt
    rcases flowLineXL_eq_zero_or_mem bR JR j with h0 | hJ
    · rw [h0] at hlt; linarith
    · have := hδRJ _ hJ (not_le.1 hlt)
      linarith [hq'.1, min_le_right ε δR]
  have h1 := sum_filter_le_flowLineXL_theta (θ := θ) hκ hb huneg huJ
  have h2 := sum_filter_le_flowLineXL_theta (θ := 0) hκ hbR (hq'.2.trans hφx) hq'JR
  have hh := hheight u.re huI' huE (by rw [hφu]; exact hq'JR)
  rw [hφu] at hh
  rw [← hR, h2, zero_mul, add_zero, hh, ← h1, hL]
  exact hbad

end InteractingSLE.Theorem14.GW2Nu

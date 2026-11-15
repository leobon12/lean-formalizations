/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcTrace
import InteractingSLE.Spec.Sec7.R6FcCore
import InteractingSLE.Spec.Supplement.Q3KernelTip
import InteractingSLE.Foundations.Loewner.Reflect

/-!
# The landing of a seed coordinate is the extreme real point of the closed hull

Packet PROVE-R6-FACE3, item (F1) (landing identification). For a continuous Loewner trace `η` of a continuous driver
`W` (`W 0 = 0`) at a positive time `u` with `a_L < a_R` (the centred images of `0∓`, `WangWu.chartAL/chartAR`), let
`F̄_u = extendFrom ℍ (fwdMapInv W u)` be the boundary extension of the inverse map. Then:

* `landR_im_eq_zero`, `landR_mem_closure`: `b_R = F̄_u(a_R)` is real and lies on the closed hull;
* **`le_re_landR`**: every real point of the closed hull is `≤ b_R` (IVT on `F̄_u` along `[a_R, ∞)`, where it lands at
  alive real points and grows like the identity);
* **`exists_real_ge_of_mem_closure_fillH`** (the ray lemma): a real point of the closed filling of a compact set
  `Z ⊆ ℍ̄` is at most some real point of `Z` (a thin horizontal strip beyond the real footprint reaches `∞`);
* **`landR_spec`**: `b_R` is real and equals the largest real point of the trace `η([0, u])`;
* the mirror statements `landL_*` for `b_L = F̄_u(a_L)` (the smallest real point).

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Fd

open WangWu (chartAL chartAR)

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {u : ℝ}

/-! ### The extended inverse map -/

/-- The boundary extension of the inverse map stays within a bounded distance of the identity on `ℍ̄`. -/
theorem exists_norm_extendFrom_sub_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) :
    ∃ C : ℝ, ∀ z ∈ Hbar, ‖extendFrom H (fwdMapInv W u) z - z‖ ≤ C := by
  obtain ⟨C, hC⟩ := exists_norm_fwdMapInv_sub_le hW hW0 hu
  refine ⟨C, fun z hz => ?_⟩
  have hcl : z ∈ closure H := by rwa [QuantumZipper.CA.Car.closure_H_eq_Hbar]
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  have hlim := ((hη.hasBdryLimits hW hW0 hu).tendsto hz).sub
    ((continuous_id.tendsto z).mono_left nhdsWithin_le_nhds)
  exact le_of_tendsto (hlim.norm) (eventually_nhdsWithin_of_forall fun w hw => hC w hw)

/-- The extended inverse map is continuous along the real line. -/
theorem continuous_landing (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) :
    Continuous fun x : ℝ => extendFrom H (fwdMapInv W u) (x : ℂ) :=
  (hη.hasBdryLimits hW hW0 hu).continuousOn.comp_continuous Complex.continuous_ofReal
    fun x => R6Fc.real_mem_Hbar x

/-! ### The right landing -/

/-- **The right landing `F̄_u(a_R)` is real.** -/
theorem landR_im_eq_zero (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) :
    (extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).im = 0 := by
  have hc := Complex.continuous_im.comp (continuous_landing hη hW hW0 hu)
  have hcl : IsClosed {x : ℝ | (extendFrom H (fwdMapInv W u) (x : ℂ)).im = 0} := isClosed_eq hc continuous_const
  have hsub : Ioi (chartAR W u) ⊆ {x : ℝ | (extendFrom H (fwdMapInv W u) (x : ℂ)).im = 0} := fun x hx =>
    Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu
      (Supp8.RelTrans.extendFrom_notMem_closure_of_chartAR_lt hη hW hW0 hu hx)
  have hmem : chartAR W u ∈ closure (Ioi (chartAR W u)) := by rw [closure_Ioi]; exact Set.self_mem_Ici
  exact hcl.closure_subset_iff.2 hsub hmem

/-- **The right landing lies on the closed hull** (for `u > 0` and `a_L < a_R`). -/
theorem landR_mem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) :
    extendFrom H (fwdMapInv W u) (chartAR W u : ℂ) ∈ closure (fwdHull W u) :=
  Supp8.RelTrans.Icc_subset_hullImage hη hW hW0 hu hlt ⟨hlt.le, le_rfl⟩

/-- **Every real point of the closed hull is at most the right landing.** -/
theorem le_re_landR (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (fwdHull W u)) :
    x ≤ (extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).re := by
  by_contra hxb
  push Not at hxb
  set F : ℝ → ℂ := fun t => extendFrom H (fwdMapInv W u) (t : ℂ) with hF
  have hFc : Continuous F := continuous_landing hη hW hW0 hu.le
  obtain ⟨C, hC⟩ := exists_norm_extendFrom_sub_le hη hW hW0 hu.le
  set Y := max (chartAR W u) (x + C + 1) with hY
  have hgY : x < (F Y).re := by
    have h1 := hC (Y : ℂ) (R6Fc.real_mem_Hbar Y)
    have h2 : |(F Y).re - Y| ≤ C := by
      have := Complex.abs_re_le_norm (F Y - (Y : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      exact this.trans h1
    have h3 : x + C + 1 ≤ Y := le_max_right _ _
    linarith [(abs_le.1 h2).1]
  obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc (le_max_left (chartAR W u) (x + C + 1))
    (Complex.continuous_re.comp hFc).continuousOn ⟨hxb.le, hgY.le⟩
  have hya : chartAR W u < y := by
    rcases hy.1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hyx
      exact hxb.ne (hyx : (F (chartAR W u)).re = x)
  have hnot := Supp8.RelTrans.extendFrom_notMem_closure_of_chartAR_lt hη hW hW0 hu.le hya
  have him := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu.le hnot
  apply hnot
  have he : extendFrom H (fwdMapInv W u) (y : ℂ) = (x : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact hyx
    · simpa only [Complex.ofReal_im] using him
  rw [he]
  exact hx

/-! ### The left landing -/

/-- **The left landing `F̄_u(a_L)` is real.** -/
theorem landL_im_eq_zero (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 ≤ u) :
    (extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).im = 0 := by
  have hc := Complex.continuous_im.comp (continuous_landing hη hW hW0 hu)
  have hcl : IsClosed {x : ℝ | (extendFrom H (fwdMapInv W u) (x : ℂ)).im = 0} := isClosed_eq hc continuous_const
  have hsub : Iio (chartAL W u) ⊆ {x : ℝ | (extendFrom H (fwdMapInv W u) (x : ℂ)).im = 0} := fun x hx =>
    Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu
      (Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hu hx)
  have hmem : chartAL W u ∈ closure (Iio (chartAL W u)) := by rw [closure_Iio]; exact Set.self_mem_Iic
  exact hcl.closure_subset_iff.2 hsub hmem

/-- **The left landing lies on the closed hull.** -/
theorem landL_mem_closure (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) :
    extendFrom H (fwdMapInv W u) (chartAL W u : ℂ) ∈ closure (fwdHull W u) :=
  Supp8.RelTrans.Icc_subset_hullImage hη hW hW0 hu hlt ⟨le_rfl, hlt.le⟩

/-- **Every real point of the closed hull is at least the left landing.** -/
theorem re_landL_le (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    {x : ℝ} (hx : (x : ℂ) ∈ closure (fwdHull W u)) :
    (extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).re ≤ x := by
  by_contra hxb
  push Not at hxb
  set F : ℝ → ℂ := fun t => extendFrom H (fwdMapInv W u) (t : ℂ) with hF
  have hFc : Continuous F := continuous_landing hη hW hW0 hu.le
  obtain ⟨C, hC⟩ := exists_norm_extendFrom_sub_le hη hW hW0 hu.le
  set Y := min (chartAL W u) (x - C - 1) with hY
  have hgY : (F Y).re < x := by
    have h1 := hC (Y : ℂ) (R6Fc.real_mem_Hbar Y)
    have h2 : |(F Y).re - Y| ≤ C := by
      have := Complex.abs_re_le_norm (F Y - (Y : ℂ))
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      exact this.trans h1
    have h3 : Y ≤ x - C - 1 := min_le_right _ _
    linarith [(abs_le.1 h2).2]
  obtain ⟨y, hy, hyx⟩ := intermediate_value_Icc (min_le_left (chartAL W u) (x - C - 1))
    (Complex.continuous_re.comp hFc).continuousOn ⟨hgY.le, hxb.le⟩
  have hya : y < chartAL W u := by
    rcases hy.2.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [h] at hyx
      exact hxb.ne' (hyx : (F (chartAL W u)).re = x)
  have hnot := Supp8.RelTrans.extendFrom_notMem_closure_of_lt_chartAL hη hW hW0 hu.le hya
  have him := Supp8.BHMean.im_extendFrom_eq_zero_of_notMem_closure hη hW hW0 hu.le hnot
  apply hnot
  have he : extendFrom H (fwdMapInv W u) (y : ℂ) = (x : ℂ) := by
    apply Complex.ext
    · rw [Complex.ofReal_re]; exact hyx
    · simpa only [Complex.ofReal_im] using him
  rw [he]
  exact hx

/-! ### The ray lemma -/

/-- Below a real point beyond the real footprint of a compact set: some margin `c < x` bounds every real point. -/
theorem exists_lt_bound_real {Z : Set ℂ} (hZ : IsCompact Z) {x : ℝ} (h : ∀ z ∈ Z, z.im = 0 → z.re < x) :
    ∃ c < x, ∀ z ∈ Z, z.im = 0 → z.re < c := by
  have hZ0 : IsCompact (Z ∩ {z : ℂ | z.im = 0}) := hZ.inter_right (isClosed_eq Complex.continuous_im continuous_const)
  rcases (Z ∩ {z : ℂ | z.im = 0}).eq_empty_or_nonempty with he | hne
  · refine ⟨x - 1, by linarith, fun z hz hz0 => ?_⟩
    exact absurd (he ▸ (⟨hz, hz0⟩ : z ∈ Z ∩ {z : ℂ | z.im = 0})) (Set.notMem_empty z)
  · obtain ⟨m, hm, hmax⟩ := hZ0.exists_isMaxOn hne Complex.continuous_re.continuousOn
    have hmx := h m hm.1 hm.2
    refine ⟨(m.re + x) / 2, by linarith, fun z hz hz0 => ?_⟩
    have := hmax ⟨hz, hz0⟩
    simp only [mem_ofPred_eq] at this
    linarith

/-- **The ray lemma**: a real point of the closed filling of a compact subset `Z` of `ℍ̄` is at most some real point
of `Z`. (A thin horizontal strip to the right of the real footprint avoids `Z` and is unbounded, hence misses the
filling, `Sec6.subset_H_diff_fillH_of_isPreconnected`.) -/
theorem exists_real_ge_of_mem_closure_fillH {Z : Set ℂ} (hZ : IsCompact Z) (hZH : Z ⊆ Hbar) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (fillH Z)) : ∃ z ∈ Z, z.im = 0 ∧ x ≤ z.re := by
  by_contra hne
  push Not at hne
  obtain ⟨c, hcx, hc⟩ := exists_lt_bound_real hZ hne
  have hZ1 : IsCompact (Z ∩ {z : ℂ | c ≤ z.re}) :=
    hZ.inter_right (isClosed_le continuous_const Complex.continuous_re)
  have hpos : ∀ z ∈ Z ∩ {z : ℂ | c ≤ z.re}, 0 < z.im := fun z hz => by
    have h0 : 0 ≤ z.im := hZH hz.1
    rcases h0.lt_or_eq with h | h
    · exact h
    · exact absurd (hc z hz.1 h.symm) (not_lt.2 hz.2)
  obtain ⟨δ, hδ, hδZ⟩ : ∃ δ > 0, ∀ z ∈ Z ∩ {z : ℂ | c ≤ z.re}, δ ≤ z.im := by
    rcases (Z ∩ {z : ℂ | c ≤ z.re}).eq_empty_or_nonempty with he | hne1
    · exact ⟨1, one_pos, fun z hz => absurd (he ▸ hz) (Set.notMem_empty z)⟩
    · obtain ⟨m, hm, hmin⟩ := hZ1.exists_isMinOn hne1 Complex.continuous_im.continuousOn
      exact ⟨m.im, hpos m hm, fun z hz => hmin hz⟩
  set P : Set ℂ := {z : ℂ | c < z.re} ∩ {z : ℂ | 0 < z.im} ∩ {z : ℂ | z.im < δ} with hPdef
  have hPconv : Convex ℝ P :=
    ((convex_halfSpace_re_gt c).inter (convex_halfSpace_im_gt 0)).inter (convex_halfSpace_im_lt δ)
  have hPsub : P ⊆ H \ closure Z := fun z hz => by
    refine ⟨hz.1.2, ?_⟩
    rw [hZ.isClosed.closure_eq]
    intro hzZ
    have := hδZ z ⟨hzZ, (show c < z.re from hz.1.1).le⟩
    linarith [show z.im < δ from hz.2]
  have hPu : ¬ Bornology.IsBounded P := by
    intro hb
    obtain ⟨M, hM⟩ := hb.subset_closedBall 0
    have hmem : ((|c| + |M| + 1 : ℝ) : ℂ) + (δ / 2 : ℝ) * Complex.I ∈ P := by
      refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp only [mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero, Complex.add_im,
        Complex.mul_im, mul_one, zero_add]
      · linarith [le_abs_self c, abs_nonneg M]
      · linarith
      · linarith
    have h1 := hM hmem
    rw [mem_closedBall, dist_zero_right] at h1
    have h2 := Complex.abs_re_le_norm (((|c| + |M| + 1 : ℝ) : ℂ) + (δ / 2 : ℝ) * Complex.I)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero] at h2
    have h3 := le_abs_self (|c| + |M| + 1)
    linarith [le_abs_self M, abs_nonneg c]
  have hPf := Sec6.subset_H_diff_fillH_of_isPreconnected hZ.isBounded hPconv.isPreconnected hPsub hPu
  obtain ⟨w, hw, hwd⟩ := Metric.mem_closure_iff.1 hx (min (x - c) δ) (lt_min (by linarith) hδ)
  have hwH : w ∈ H := fillH_subset_H Z hw
  have hre : |w.re - x| < x - c := by
    have h1 := Complex.abs_re_le_norm (w - (x : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at h1
    rw [dist_comm, dist_eq_norm] at hwd
    exact h1.trans_lt (hwd.trans_le (min_le_left _ _))
  have him : w.im < δ := by
    have h1 := Complex.abs_im_le_norm (w - (x : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
    rw [dist_comm, dist_eq_norm] at hwd
    exact (le_abs_self _).trans_lt (h1.trans_lt (hwd.trans_le (min_le_right _ _)))
  have hwP : w ∈ P := ⟨⟨show c < w.re by linarith [(abs_lt.1 hre).1], hwH⟩, him⟩
  exact (hPf hwP).2 hw

/-- **The ray lemma, mirror**: a real point of the closed filling of a compact `Z ⊆ ℍ̄` is at least some real point
of `Z` (reflect `z ↦ −z̄`). -/
theorem exists_real_le_of_mem_closure_fillH {Z : Set ℂ} (hZ : IsCompact Z) (hZH : Z ⊆ Hbar) {x : ℝ}
    (hx : (x : ℂ) ∈ closure (fillH Z)) : ∃ z ∈ Z, z.im = 0 ∧ z.re ≤ x := by
  have hZ'c : IsCompact (LP.reflectC '' Z) := hZ.image LP.reflectHomeo.continuous
  have hZ'H : LP.reflectC '' Z ⊆ Hbar := by
    rintro _ ⟨z, hz, rfl⟩
    show 0 ≤ (LP.reflectC z).im
    rw [LP.im_reflectC]
    exact hZH hz
  have hx' : ((-x : ℝ) : ℂ) ∈ closure (fillH (LP.reflectC '' Z)) := by
    rw [LP.fillH_image_reflectC, LP.closure_image_reflectC]
    exact ⟨(x : ℂ), hx, LP.reflectC_ofReal x⟩
  obtain ⟨_, ⟨z, hz, rfl⟩, him, hle⟩ := exists_real_ge_of_mem_closure_fillH hZ'c hZ'H hx'
  refine ⟨z, hz, by rwa [LP.im_reflectC] at him, ?_⟩
  rw [LP.re_reflectC] at hle
  linarith

/-! ### The landings are the extreme real points of the trace -/

/-- The trace up to `u > 0` lies on the closed hull at `u`. -/
theorem trace_mem_closure_hull (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u) {t : ℝ}
    (ht : t ∈ Icc 0 u) : η t ∈ closure (fwdHull W u) := by
  rcases ht.1.lt_or_eq with ht0 | ht0
  · exact closure_mono (fwdHull_mono' ht.2) (Supp8.Q3Kernel.trace_mem_closure_fwdHull hη hW hW0 ht0)
  · rw [← ht0, hη.1]
    exact ConformalImageFull.zero_mem_closure_fwdHull hW hW0 hu

/-- The trace up to `u > 0` lies in `ℍ̄`. -/
theorem trace_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u) {t : ℝ}
    (ht : t ∈ Icc 0 u) : η t ∈ Hbar := by
  have h := trace_mem_closure_hull hη hW hW0 hu ht
  rw [← QuantumZipper.CA.Car.closure_H_eq_Hbar]
  exact closure_mono ((QuantumZipper.fwdHull_mono (W := W)).2 u) h

/-- The trace image on `[0, u]` is compact. -/
theorem isCompact_trace (hη : IsLoewnerTrace W η) {u : ℝ} : IsCompact (η '' Icc 0 u) :=
  isCompact_Icc.image_of_continuousOn (hη.2.1.mono Icc_subset_Ici_self)

/-- **(F1) The right landing `F̄_u(a_R)` is real and is the largest real point of the trace `η([0, u])`.** -/
theorem landR_spec (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) :
    extendFrom H (fwdMapInv W u) (chartAR W u : ℂ) = ((extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).re : ℂ) ∧
      (∃ t ∈ Icc 0 u, (η t).im = 0 ∧ (extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).re ≤ (η t).re) ∧
      ∀ t ∈ Icc 0 u, (η t).im = 0 → (η t).re ≤ (extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).re := by
  have hb : extendFrom H (fwdMapInv W u) (chartAR W u : ℂ) =
      ((extendFrom H (fwdMapInv W u) (chartAR W u : ℂ)).re : ℂ) :=
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact landR_im_eq_zero hη hW hW0 hu.le)
  refine ⟨hb, ?_, fun t ht ht0 => ?_⟩
  · have hm := landR_mem_closure hη hW hW0 hu hlt
    rw [hb, hη.2.2 u hu.le] at hm
    obtain ⟨_, ⟨t, ht, rfl⟩, him, hle⟩ := exists_real_ge_of_mem_closure_fillH (isCompact_trace hη)
      (by rintro _ ⟨t, ht, rfl⟩; exact trace_mem_Hbar hη hW hW0 hu ht) hm
    exact ⟨t, ht, him, hle⟩
  · have hm := trace_mem_closure_hull hη hW hW0 hu ht
    have he : η t = ((η t).re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact ht0)
    rw [he] at hm
    exact le_re_landR hη hW hW0 hu hm

/-- **(F1, mirror) The left landing `F̄_u(a_L)` is real and is the smallest real point of the trace.** -/
theorem landL_spec (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hu : 0 < u)
    (hlt : chartAL W u < chartAR W u) :
    extendFrom H (fwdMapInv W u) (chartAL W u : ℂ) = ((extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).re : ℂ) ∧
      (∃ t ∈ Icc 0 u, (η t).im = 0 ∧ (η t).re ≤ (extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).re) ∧
      ∀ t ∈ Icc 0 u, (η t).im = 0 → (extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).re ≤ (η t).re := by
  have hb : extendFrom H (fwdMapInv W u) (chartAL W u : ℂ) =
      ((extendFrom H (fwdMapInv W u) (chartAL W u : ℂ)).re : ℂ) :=
    Complex.ext rfl (by rw [Complex.ofReal_im]; exact landL_im_eq_zero hη hW hW0 hu.le)
  refine ⟨hb, ?_, fun t ht ht0 => ?_⟩
  · have hm := landL_mem_closure hη hW hW0 hu hlt
    rw [hb, hη.2.2 u hu.le] at hm
    obtain ⟨_, ⟨t, ht, rfl⟩, him, hle⟩ := exists_real_le_of_mem_closure_fillH (isCompact_trace hη)
      (by rintro _ ⟨t, ht, rfl⟩; exact trace_mem_Hbar hη hW hW0 hu ht) hm
    exact ⟨t, ht, him, hle⟩
  · have hm := trace_mem_closure_hull hη hW hW0 hu ht
    have he : η t = ((η t).re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact ht0)
    rw [he] at hm
    exact re_landL_le hη hW hW0 hu hm

end InteractingSLE.Sec7.R6Fd

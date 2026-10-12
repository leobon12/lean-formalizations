import LQGDimension.Existence.SeriesContinuityAux1
import LQGDimension.Existence.SeriesContinuityAux2

/-!
# Local uniform continuity of Gaussian series (`Blueprint.Existence.GaussianSeriesLocallyUnifCont`)

Let `ω` be an i.i.d. standard Gaussian sequence, `T₀ ⊆ ℝ × ℂ` countable and
`X_t(ω) = ∑ₖ v_t(k) ω_k` with finitely supported `v_t` such that
`‖v_s - v_t‖²_{ℓ²} ≤ L_m ‖s - t‖` on `T₀ ∩ box m`.  Then almost surely `X` is uniformly continuous
on every `T₀ ∩ box m`.

Proof (Lévy–Kolmogorov).  Fix `m`, put `Λ = max L_m 1`, `R = m + 1`, and use the coordinates
`coord (ε, z) = (ε, re z, im z) ∈ ℝ³` (sup norm), for which `‖coord s‖ ≤ R` on `box m`.  At level
`k`, with `h = R / 4^k`, group the points of `T₀ ∩ box m` by the level-`k` cell `c` of
`ChainBox.cell` (at most `64^{k+1}` cells): `grp c` consists of the points within `h` of some point
of cell `c`; it has `coord`-diameter `≤ 3h`, and any two points at distance `≤ h` lie in a common
group.  On each group, chaining plus concentration (`gaussSeq_osc_countable`) bounds the
probability that the oscillation around a base point exceeds `Mk + sk` by `2 e^{-7(k+1)}`.
A union bound gives `P(bad k) ≤ 2^{-k}` for the event
`bad k = {∃ s, t ∈ T₀ ∩ box m, ‖s - t‖ ≤ h, |X_s - X_t| > rk}` with `rk = 2 (Mk + sk) → 0`;
Borel–Cantelli concludes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped ENNReal

namespace LQGDimension

namespace SeriesCont

open Blueprint.Existence (box)

section Levels

variable (T₀ : Set (ℝ × ℂ)) (m : ℕ) (v : ℝ × ℂ → ℕ → ℝ)

/-- The level-`k` group of the cell `c`: points of `T₀ ∩ box m` within `hk R k` (in `coord`) of a
point of the cell. -/
def grp (R : ℝ) (k : ℕ) (c : Fin 3 → ℤ) : Set (ℝ × ℂ) :=
  {t | t ∈ T₀ ∩ box m ∧ ∃ q : Fin 3 → ℝ, ChainBox.cell R k q = c ∧ ‖coord t - q‖ ≤ hk R k}

open Classical in
/-- A base point of the group `grp c` (when it is nonempty). -/
def ctr (R : ℝ) (k : ℕ) (c : Fin 3 → ℤ) : ℝ × ℂ :=
  if h : (grp T₀ m R k c).Nonempty then h.some else 0

/-- The group `c` oscillates too much around its base point. -/
def badGrp (R Λ : ℝ) (k : ℕ) (c : Fin 3 → ℤ) : Set (ℕ → ℝ) :=
  {ω | ∃ t ∈ grp T₀ m R k c, Mk R Λ k + sk R Λ k ≤
    |(∑' j, v t j * ω j) - ∑' j, v (ctr T₀ m R k c) j * ω j|}

/-- The level-`k` bad event: two points at distance `≤ hk R k` with increment `> rk R Λ k`. -/
def bad (R Λ : ℝ) (k : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∃ s ∈ T₀ ∩ box m, ∃ t ∈ T₀ ∩ box m, ‖s - t‖ ≤ hk R k ∧
    rk R Λ k < |(∑' j, v s j * ω j) - ∑' j, v t j * ω j|}

variable {T₀ m}

theorem ctr_mem {R : ℝ} {k : ℕ} {c : Fin 3 → ℤ} (h : (grp T₀ m R k c).Nonempty) :
    ctr T₀ m R k c ∈ grp T₀ m R k c := by
  rw [ctr, dite_eq_left h]
  exact h.some_mem

theorem coord_sub_le_of_mem_grp {R : ℝ} (hR : 0 < R) {k : ℕ} {c : Fin 3 → ℤ} {s t : ℝ × ℂ}
    (hs : s ∈ grp T₀ m R k c) (ht : t ∈ grp T₀ m R k c) :
    ‖coord s - coord t‖ ≤ 3 * hk R k := by
  obtain ⟨-, q, hq, hsq⟩ := hs
  obtain ⟨-, q', hq', htq'⟩ := ht
  have hqq : ‖q - q'‖ < hk R k := ChainBox.norm_sub_lt_of_cell_eq hR k (hq.trans hq'.symm)
  have htq'' : ‖q' - coord t‖ ≤ hk R k := by rw [norm_sub_rev]; exact htq'
  calc ‖coord s - coord t‖ = ‖(coord s - q) + (q - q') + (q' - coord t)‖ := by
        congr 1; abel
    _ ≤ ‖coord s - q‖ + ‖q - q'‖ + ‖q' - coord t‖ := norm_add₃_le
    _ ≤ 3 * hk R k := by linarith

theorem measure_badGrp_le {R Λ : ℝ} (hR : 0 < R) (hΛ : 0 < Λ) (hT₀ : T₀.Countable)
    (hfin : ∀ t, ∃ N, ∀ j ≥ N, v t j = 0)
    (hv : ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' j, (v s j - v t j) ^ 2) ≤ Λ * ‖s - t‖)
    (k : ℕ) (c : Fin 3 → ℤ) :
    gaussSeq (badGrp T₀ m v R Λ k c) ≤ ENNReal.ofReal (2 * Real.exp (-7 * ((k : ℝ) + 1))) := by
  by_cases hne : (grp T₀ m R k c).Nonempty
  · have hvar : ∀ i ∈ grp T₀ m R k c, ∀ i' ∈ grp T₀ m R k c,
        (∑' j, (v i j - v i' j) ^ 2) ≤ √(2 * Λ) ^ 2 * ‖coord i - coord i'‖ := by
      intro i hi i' hi'
      rw [Real.sq_sqrt (by positivity)]
      calc (∑' j, (v i j - v i' j) ^ 2) ≤ Λ * ‖i - i'‖ := hv i hi.1.1 i' hi'.1.1 hi.1.2 hi'.1.2
        _ ≤ Λ * (2 * ‖coord i - coord i'‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le_two_mul_coord i i') hΛ.le
        _ = 2 * Λ * ‖coord i - coord i'‖ := by ring
    have h := gaussSeq_osc_countable (d := 3) v hfin (grp T₀ m R k c)
      (hT₀.mono fun t ht => ht.1.1) coord (L := √(2 * Λ)) (a := 3 * hk R k)
      (σ := σk R Λ k) (s := sk R Λ k) (Real.sqrt_nonneg _)
      (fun i hi i' hi' => coord_sub_le_of_mem_grp hR hi hi') hvar (σk_pos hR hΛ k)
      (sq_sqrt_two_mul_le hR hΛ k) (sk_nonneg R Λ k) (ctr_mem hne)
    rw [tail_exponent_eq hR hΛ k] at h
    exact h
  · have hempty : badGrp T₀ m v R Λ k c = ∅ := by
      ext ω
      refine iff_of_false ?_ (notMem_empty ω)
      rintro ⟨t, ht, -⟩
      exact hne ⟨t, ht⟩
    rw [hempty, measure_empty]
    exact zero_le

theorem bad_subset {R Λ : ℝ} (hR : 0 < R) (hRm : (m : ℝ) + 1 ≤ R) (k : ℕ) :
    bad T₀ m v R Λ k ⊆ ⋃ c ∈ ChainBox.box R k (0 : Fin 3 → ℝ), badGrp T₀ m v R Λ k c := by
  rintro ω ⟨s, hs, t, ht, hst, hlt⟩
  set c := ChainBox.cell R k (coord s) with hc
  have hcmem : c ∈ ChainBox.box R k (0 : Fin 3 → ℝ) :=
    ChainBox.cell_mem_box hR k
      (by rw [sub_zero]; exact (norm_coord_le_of_mem_box hs.2).trans hRm)
  have hsg : s ∈ grp T₀ m R k c :=
    ⟨hs, coord s, rfl, by rw [sub_self, norm_zero]; exact (hk_pos hR k).le⟩
  have htg : t ∈ grp T₀ m R k c :=
    ⟨ht, coord s, rfl, (norm_coord_sub_le t s).trans (by rw [norm_sub_rev]; exact hst)⟩
  rw [mem_iUnion₂]
  refine ⟨c, hcmem, ?_⟩
  set x := ∑' j, v s j * ω j with hx
  set y := ∑' j, v t j * ω j with hy
  set z := ∑' j, v (ctr T₀ m R k c) j * ω j with hz
  by_cases h1 : Mk R Λ k + sk R Λ k ≤ |x - z|
  · exact ⟨s, hsg, h1⟩
  by_cases h2 : Mk R Λ k + sk R Λ k ≤ |y - z|
  · exact ⟨t, htg, h2⟩
  exfalso
  push Not at h1 h2
  have h3 : |x - y| ≤ |x - z| + |y - z| := by
    have := abs_sub_le x z y
    rwa [abs_sub_comm z y] at this
  have hr : rk R Λ k = 2 * (Mk R Λ k + sk R Λ k) := rfl
  linarith

theorem measure_bad_le {R Λ : ℝ} (hR : 0 < R) (hRm : (m : ℝ) + 1 ≤ R) (hΛ : 0 < Λ)
    (hT₀ : T₀.Countable) (hfin : ∀ t, ∃ N, ∀ j ≥ N, v t j = 0)
    (hv : ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' j, (v s j - v t j) ^ 2) ≤ Λ * ‖s - t‖) (k : ℕ) :
    gaussSeq (bad T₀ m v R Λ k) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  calc gaussSeq (bad T₀ m v R Λ k)
      ≤ gaussSeq (⋃ c ∈ ChainBox.box R k (0 : Fin 3 → ℝ), badGrp T₀ m v R Λ k c) :=
        measure_mono (bad_subset v hR hRm k)
    _ ≤ ∑ c ∈ ChainBox.box R k (0 : Fin 3 → ℝ), gaussSeq (badGrp T₀ m v R Λ k c) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ c ∈ ChainBox.box R k (0 : Fin 3 → ℝ),
          ENNReal.ofReal (2 * Real.exp (-7 * ((k : ℝ) + 1))) :=
        Finset.sum_le_sum fun c _ => measure_badGrp_le v hR hΛ hT₀ hfin hv k c
    _ = ENNReal.ofReal (((ChainBox.box R k (0 : Fin 3 → ℝ)).card : ℝ) *
          (2 * Real.exp (-7 * ((k : ℝ) + 1)))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
        apply ENNReal.ofReal_le_ofReal
        calc (((ChainBox.box R k (0 : Fin 3 → ℝ)).card : ℕ) : ℝ) *
              (2 * Real.exp (-7 * ((k : ℝ) + 1)))
            ≤ ((4 : ℝ) ^ (k + 1)) ^ 3 * (2 * Real.exp (-7 * ((k : ℝ) + 1))) := by
              gcongr
              exact_mod_cast ChainBox.card_box_le R k (0 : Fin 3 → ℝ)
          _ ≤ (1 / 2) ^ k := level_count_bound k
    _ = (2⁻¹ : ℝ≥0∞) ^ k := by
        rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2), ENNReal.ofReal_ofNat]

theorem tsum_measure_bad_ne_top {R Λ : ℝ} (hR : 0 < R) (hRm : (m : ℝ) + 1 ≤ R) (hΛ : 0 < Λ)
    (hT₀ : T₀.Countable) (hfin : ∀ t, ∃ N, ∀ j ≥ N, v t j = 0)
    (hv : ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' j, (v s j - v t j) ^ 2) ≤ Λ * ‖s - t‖) :
    ∑' k, gaussSeq (bad T₀ m v R Λ k) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_
    (ENNReal.tsum_le_tsum fun k => measure_bad_le v hR hRm hΛ hT₀ hfin hv k)
  rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

end Levels

/-- **Almost sure uniform continuity on one box.** -/
theorem ae_uniformContinuousOn_box (T₀ : Set (ℝ × ℂ)) (hT₀ : T₀.Countable)
    (v : ℝ × ℂ → ℕ → ℝ) (hfin : ∀ t, ∃ N, ∀ j ≥ N, v t j = 0) (m : ℕ) (L : ℝ)
    (hL : ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' j, (v s j - v t j) ^ 2) ≤ L * ‖s - t‖) :
    ∀ᵐ ω ∂gaussSeq, UniformContinuousOn (fun t => ∑' j, v t j * ω j) (T₀ ∩ box m) := by
  set Λ := max L 1 with hΛdef
  have hΛ : 0 < Λ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hv : ∀ s ∈ T₀, ∀ t ∈ T₀, s ∈ box m → t ∈ box m →
      (∑' j, (v s j - v t j) ^ 2) ≤ Λ * ‖s - t‖ := fun s hs t ht hsm htm =>
    (hL s hs t ht hsm htm).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  set R : ℝ := (m : ℝ) + 1 with hRdef
  have hR : 0 < R := by positivity
  filter_upwards [ae_eventually_notMem (tsum_measure_bad_ne_top v hR le_rfl hΛ hT₀ hfin hv)]
    with ω hω
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  obtain ⟨k, hk1, hk2⟩ := (hω.and ((tendsto_rk R Λ).eventually (gt_mem_nhds hε))).exists
  refine ⟨hk R k, hk_pos hR k, fun x hx y hy hxy => ?_⟩
  rw [dist_eq_norm] at hxy
  rw [Real.dist_eq]
  by_contra hcon
  push Not at hcon
  exact hk1 ⟨x, hx, y, hy, hxy.le, lt_of_lt_of_le hk2 hcon⟩

end SeriesCont

/-- **`GaussianSeriesLocallyUnifCont`**: a Gaussian series over a countable set of (radius, centre)
pairs with Hölder-½ increments on every box is almost surely uniformly continuous on every box. -/
theorem gaussianSeriesLocallyUnifCont : Blueprint.Existence.GaussianSeriesLocallyUnifCont := by
  intro T₀ hT₀ v hfin hL
  rw [ae_all_iff]
  intro m
  obtain ⟨L, hLm⟩ := hL m
  exact SeriesCont.ae_uniformContinuousOn_box T₀ hT₀ v hfin m L hLm

end LQGDimension

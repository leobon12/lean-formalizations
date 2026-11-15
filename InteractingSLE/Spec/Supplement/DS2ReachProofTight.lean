/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.DS2ReachProofEvol

/-!
# DS2 in reach form, VI: tightness

Packet PROVE-T14-DS (proof of DS2, spec p. 553: "DS1 makes the first term small in probability uniformly over the
parameter family, and then `h` makes the second small. … The Brownian terms have their usual uniform modulus in
probability. The integrated equations therefore give joint tightness of the driver, every retained force coordinate
and the driving Brownian motion").

* `GoodPath.mem_modulusSet`: a good stopped path whose Brownian path has a modulus `ε_k` below `δ^B_k` and whose
  occupation integrals at the cutoffs `δ_k` are below `ε_k` lies in the Arzelà–Ascoli set with steps
  `min(δ^B_k/2, δ_k ε_k)` and moduli `(√κ + 3C₁) ε_k`;
* **`isTightMeasureSet_laws`**: the joint laws of the stopped state paths and the Brownian paths of a family of
  evolutions of DS1 words (uniform weight bound, `ε`, cross gap `a`, far gap `g`) are tight.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Finset ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp12

namespace DSReach

open DS2
open scoped PathMeas

/-- The modulus constants `C₁ = 2 + (n_L + n_R) R_w`. -/
def cOne (nL nR : ℕ) (Rw : ℝ) : ℝ := 2 + (nL + nR) * Rw

/-- The levels `ε_k = 1/(k+1)`. -/
def epsK (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

theorem epsK_pos (k : ℕ) : 0 < epsK k := by unfold epsK; positivity

theorem tendsto_epsK : Tendsto epsK atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

section Modulus

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε R g : ℝ} {T : ℝ≥0} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **A good path in the modulus set.** -/
theorem GoodPath.mem_modulusSet (h : GoodPath κ mL mR Rw ε R g xL xR ρL ρR w vL vR b ζ) (hε : 0 < ε)
    (hg : 0 < g) (hnL : 0 < nL) (hnR : 0 < nR) {δB δ : ℕ → ℝ} (hδB : ∀ k, 0 < δB k) (hδ : ∀ k, 0 < δ k)
    (hb : ∀ k, ∀ x y : Set.Icc (0 : ℝ≥0) T, dist x y < δB k → |b y - b x| < epsK k)
    (hiR : ∀ k, h.iR hnR T (δ k) ≤ epsK k) (hiL : ∀ k, h.iL hnL T (δ k) ≤ epsK k) :
    h.stopped T ∈ {f : C(Set.Icc (0 : ℝ≥0) T, SState nL nR) | (∀ x, f x ∈ cBuf mL mR R g) ∧
      ∀ k x y, dist x y ≤ min (δB k / 2) (δ k * epsK k) →
        dist (f x) (f y) ≤ (Real.sqrt κ + 3 * cOne nL nR Rw) * epsK k} := by
  refine ⟨h.stopped_mem_cBuf hε hg, fun k => ?_⟩
  -- it suffices to treat `x ≤ y`
  suffices H : ∀ x y : Set.Icc (0 : ℝ≥0) T, x ≤ y → dist x y ≤ min (δB k / 2) (δ k * epsK k) →
      dist (h.stopped T x) (h.stopped T y) ≤ (Real.sqrt κ + 3 * cOne nL nR Rw) * epsK k by
    intro x y hxy
    rcases le_total x y with hle | hle
    · exact H x y hle hxy
    · rw [dist_comm] at hxy ⊢
      exact H y x hle hxy
  intro x y hle hxy
  have hRw : 0 ≤ Rw := (abs_nonneg _).trans (h.word.2.2.1 ⟨0, hnR⟩)
  have hC : 0 ≤ cOne nL nR Rw := by unfold cOne; positivity
  have hdist : dist x y = (y : ℝ) - x := by
    rw [Subtype.dist_eq, NNReal.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hle))]
  rw [hdist] at hxy
  have hd := h.dist_stopped_le hε hg hnL hnR hle (hδ k)
  set τ := exitTime (cBuf mL mR R g) T (stOf w vL vR) ζ
  -- the Brownian term
  have hbB : |b (min (y : ℝ≥0) τ) - b (min (x : ℝ≥0) τ)| < epsK k := by
    have hx' : min (x : ℝ≥0) τ ≤ T := (min_le_left _ _).trans x.2.2
    have hy' : min (y : ℝ≥0) τ ≤ T := (min_le_left _ _).trans y.2.2
    refine hb k ⟨min (x : ℝ≥0) τ, zero_le, hx'⟩ ⟨min (y : ℝ≥0) τ, zero_le, hy'⟩ ?_
    have hmono : min (x : ℝ≥0) τ ≤ min (y : ℝ≥0) τ := min_le_min_right _ (Subtype.coe_le_coe.2 hle)
    rw [Subtype.dist_eq, NNReal.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast hmono))]
    have h1 := GoodPath.min_sub_min_le (τ := τ) (Subtype.coe_le_coe.2 hle)
    have h2 := (min_le_left _ _).trans' hxy
    have h3 := hδB k
    simp only at h1 h2 ⊢
    linarith
  -- the step term
  have hstep : ((y : ℝ) - x) / δ k ≤ epsK k := by
    rw [div_le_iff₀ (hδ k)]
    have := (min_le_right _ _).trans' hxy
    linarith
  have hsum : h.iR hnR T (δ k) + h.iL hnL T (δ k) + ((y : ℝ) - x) / δ k ≤ 3 * epsK k := by
    linarith [hiR k, hiL k]
  calc dist (h.stopped T x) (h.stopped T y)
      ≤ Real.sqrt κ * |b (min (y : ℝ≥0) τ) - b (min (x : ℝ≥0) τ)| +
          (2 + (nL + nR) * Rw) * (h.iR hnR T (δ k) + h.iL hnL T (δ k) + ((y : ℝ) - x) / δ k) := hd
    _ ≤ Real.sqrt κ * epsK k + cOne nL nR Rw * (3 * epsK k) := by
        have h0 : 0 ≤ h.iR hnR T (δ k) + h.iL hnL T (δ k) + ((y : ℝ) - x) / δ k := by
          have := h.iR_nonneg (T := T) hnR (δ k)
          have := h.iL_nonneg (T := T) hnL (δ k)
          have : 0 ≤ ((y : ℝ) - x) / δ k :=
            div_nonneg (sub_nonneg.2 (by exact_mod_cast hle)) (hδ k).le
          linarith
        have e1 := mul_le_mul_of_nonneg_left hbB.le (Real.sqrt_nonneg κ)
        have e2 := mul_le_mul_of_nonneg_left hsum hC
        unfold cOne at e2 ⊢
        linarith
    _ = (Real.sqrt κ + 3 * cOne nL nR Rw) * epsK k := by ring

end Modulus

/-! ### Choosing the cutoffs -/

/-- For `C`, `0 < q`, `0 < r` and `0 < c` there is `δ ∈ (0, r)` with `C δ^q ≤ c`. -/
theorem exists_cutoff {C q r c : ℝ} (hq : 0 < q) (hr : 0 < r) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ δ < r ∧ C * δ ^ q ≤ c := by
  have hcont : Tendsto (fun δ : ℝ => C * δ ^ q) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ ^ q) (𝓝 0) (𝓝 ((0 : ℝ) ^ q)) :=
      (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow hq.ne'] at h1
    have := (h1.const_mul C).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [mul_zero] at this
  have h0 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 r := Ioo_mem_nhdsGT hr
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo 0 r ∧ C * δ ^ q < c :=
    h0.and (hcont.eventually (gt_mem_nhds hc))
  obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := hev.exists
  exact ⟨δ, h1, h2, h3.le⟩

/-! ### Tightness -/

section Tight

variable {κ : ℝ} {nL nR : ℕ} {mL mR : ℕ} {Rw ε a R g : ℝ}

/-- **Joint tightness** (proof of DS2): the joint laws of the stopped state paths and the Brownian paths of
evolutions of DS1 words with a uniform weight bound `R_w`, inner bound `ε`, cross gap `a` and far gap `g` (stopped at
the outer closed buffer of radius `R + 1` and far gap `g/2`) form a tight family. -/
theorem isTightMeasureSet_laws (hκ : 0 < κ) (hnL : 0 < nL) (hnR : 0 < nR) (hε : 0 < ε) (ha : 0 < a)
    (hg : 0 < g) (hRw : 0 ≤ Rw) (T : ℝ≥0) {ι : Type*} {Ω : ι → Type u} [mΩ : ∀ m, MeasurableSpace (Ω m)]
    {P : ∀ m, Measure (Ω m)} [hP : ∀ m, IsProbabilityMeasure (P m)] {𝓕 : ∀ m, Filtration ℝ≥0 (mΩ m)}
    {xL : ι → Fin nL → ℝ} {xR : ι → Fin nR → ℝ} {ρL : ι → Fin nL → ℝ} {ρR : ι → Fin nR → ℝ}
    {W : ∀ m, ℝ≥0 → Ω m → ℝ} {VL : ∀ m, Fin nL → ℝ≥0 → Ω m → ℝ} {VR : ∀ m, Fin nR → ℝ≥0 → Ω m → ℝ}
    {B : ∀ m, ℝ≥0 → Ω m → ℝ} {ζ : ∀ m, Ω m → ℝ≥0∞}
    (hE : ∀ m, IsIntegratedSLEEvolution κ (xL m) (xR m) (ρL m) (ρR m) (P m) (𝓕 m) (W m) (VL m) (VR m) (B m)
      (ζ m))
    (hw : ∀ m, IsDS1Word mL mR Rw ε (xL m) (xR m) (ρL m) (ρR m))
    (hcr : ∀ m, a ≤ xR m ⟨0, hnR⟩ - xL m ⟨0, hnL⟩)
    (D : ∀ m, EvolData κ mL mR Rw ε R g (xL m) (xR m) (ρL m) (ρR m) (P m) (W m) (VL m) (VR m) (ζ m))
    (m₀ : ι) :
    IsTightMeasureSet (range fun m => (D m).law T) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro e he
  obtain ⟨e', he'0, he'pos, he'e⟩ := ENNReal.lt_iff_exists_real_btwn.1 he
  have he' : 0 < e' := ENNReal.ofReal_pos.1 he'pos
  -- the Brownian law and a compact set for it
  set ν := (P m₀).map ((D m₀).bP T) with hνdef
  have hν : ∀ m, (P m).map ((D m).bP T) = ν := fun m => (D m).map_bP_eq (D m₀) T
  have hνprob : IsProbabilityMeasure ν := by rw [hνdef]; infer_instance
  obtain ⟨Kβ, hKβc, hKβ⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.1
    (isTightMeasureSet_singleton (μ := ν)) (ENNReal.ofReal (e' / 2)) (by simpa using half_pos he')
  have hKβν : ν Kβᶜ ≤ ENNReal.ofReal (e' / 2) := hKβ ν rfl
  have hmodB : ∀ k, ∃ δ > 0, ∀ f ∈ Kβ, ∀ x y : Set.Icc (0 : ℝ≥0) T, dist x y < δ → dist (f x) (f y) < epsK k :=
    fun k => exists_modulus_of_isCompact hKβc (epsK_pos k)
  choose δB hδB0 hδB using hmodB
  -- the DS1 constants
  obtain ⟨r, hr, p, hp0, hp1, C, hds1⟩ := DS1.ds1.{u} κ hκ nL nR hnR T hRw hε ha (half_pos hg)
  obtain ⟨rL, hrL, pL, hpL0, hpL1, CL, hds1L⟩ := DS1.ds1_left.{u} κ hκ nL nR hnL T hRw hε ha (half_pos hg)
  set c : ℕ → ℝ := fun k => e' / 8 * (1 / 2) ^ k with hc
  have hcpos : ∀ k, 0 < c k := fun k => by simp only [hc]; positivity
  have hcut : ∀ k, ∃ δ : ℝ, 0 < δ ∧ δ < min r rL ∧ C * δ ^ (1 - p) ≤ epsK k * c k ∧
      CL * δ ^ (1 - pL) ≤ epsK k * c k := by
    intro k
    obtain ⟨δ₁, h1, h2, h3⟩ := exists_cutoff (C := C) (sub_pos.2 hp1) (lt_min hr hrL)
      (mul_pos (epsK_pos k) (hcpos k))
    obtain ⟨δ₂, h4, h5, h6⟩ := exists_cutoff (C := CL) (sub_pos.2 hpL1) (lt_min hr hrL)
      (mul_pos (epsK_pos k) (hcpos k))
    have hmono : ∀ {K q δ' : ℝ}, 0 < q → min δ₁ δ₂ ≤ δ' → K * δ' ^ q ≤ epsK k * c k →
        K * (min δ₁ δ₂) ^ q ≤ epsK k * c k := by
      intro K q δ' hq hle hK
      have hpos : 0 < epsK k * c k := mul_pos (epsK_pos k) (hcpos k)
      by_cases hK0 : 0 ≤ K
      · exact (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (lt_min h1 h4).le hle hq.le) hK0).trans hK
      · push Not at hK0
        have : K * (min δ₁ δ₂) ^ q ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hK0.le (Real.rpow_nonneg (lt_min h1 h4).le _)
        linarith
    refine ⟨min δ₁ δ₂, lt_min h1 h4, (min_le_left _ _).trans_lt h2, ?_, ?_⟩
    · exact hmono (sub_pos.2 hp1) (min_le_left _ _) h3
    · exact hmono (sub_pos.2 hpL1) (min_le_right _ _) h6
  choose δk hδk0 hδkr hδkC hδkCL using hcut
  set Kf : Set C(Set.Icc (0 : ℝ≥0) T, SState nL nR) := {f | (∀ x, f x ∈ cBuf mL mR R g) ∧
      ∀ k x y, dist x y ≤ min (δB k / 2) (δk k * epsK k) →
        dist (f x) (f y) ≤ (Real.sqrt κ + 3 * cOne nL nR Rw) * epsK k} with hKfdef
  have hKf : IsCompact Kf := isCompact_modulusSet (isCompact_cBuf mL mR R g)
    (fun k => lt_min (half_pos (hδB0 k)) (mul_pos (hδk0 k) (epsK_pos k)))
    (by simpa using tendsto_epsK.const_mul (Real.sqrt κ + 3 * cOne nL nR Rw))
  refine ⟨Kf ×ˢ Kβ, hKf.prod hKβc, ?_⟩
  rintro _ ⟨m, rfl⟩
  have hφm : ∀ δ, Measurable fun x => ENNReal.ofReal (invCut δ x) := fun δ =>
    ENNReal.measurable_ofReal.comp (measurable_invCut δ)
  set occR : ℕ → Ω m → ℝ≥0∞ := fun k => occ mL mR R g T (W m) (VL m) (VR m) (ζ m)
    (fun x => ENNReal.ofReal (invCut (δk k) x)) (EvolData.gpR hnR) with hoccR
  set occL : ℕ → Ω m → ℝ≥0∞ := fun k => occ mL mR R g T (W m) (VL m) (VR m) (ζ m)
    (fun x => ENNReal.ofReal (invCut (δk k) x)) (EvolData.gpL hnL) with hoccL
  -- the bad event
  have hsub : (fun ω => (fR mL mR R g T (W m) (VL m) (VR m) (ζ m) ω, (D m).bP T ω)) ⁻¹' (Kf ×ˢ Kβ)ᶜ ⊆
      (D m).Gᶜ ∪ ((D m).bP T ⁻¹' Kβᶜ ∪
        ⋃ k, ({ω | ENNReal.ofReal (epsK k) ≤ occR k ω} ∪ {ω | ENNReal.ofReal (epsK k) ≤ occL k ω})) := by
    intro ω hω
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq,
      not_or, not_not, not_exists, not_le] at hcon
    obtain ⟨hG, hβ, hocc⟩ := hcon
    apply hω
    refine ⟨?_, hβ⟩
    have hgood := (D m).good ω hG
    refine hgood.mem_modulusSet (T := T) hε hg hnL hnR hδB0 hδk0 (fun k x y hxy => ?_) (fun k => ?_)
      (fun k => ?_)
    · have := hδB k _ hβ x y hxy
      rw [Real.dist_eq, abs_sub_comm] at this
      exact this
    · have h1 := (D m).ofReal_iR_le_occ hε hg hnR T (δk k) hG
      exact ((ENNReal.ofReal_lt_ofReal_iff'.1 (h1.trans_lt (hocc k).1)).1).le
    · have h1 := (D m).ofReal_iL_le_occ hε hg hnL T (δk k) hG
      exact ((ENNReal.ofReal_lt_ofReal_iff'.1 (h1.trans_lt (hocc k).2)).1).le
  -- Markov's inequality for the occupation integrals
  have hxL0 : ∀ i : Fin nL, xL m i ≤ xL m ⟨0, hnL⟩ := fun i => (hw m).1.1 (Fin.le_def.2 (Nat.zero_le _))
  have hxR0 : ∀ j : Fin nR, xR m ⟨0, hnR⟩ ≤ xR m j := fun j => (hw m).1.2.2.1 (Fin.le_def.2 (Nat.zero_le _))
  have hds := hds1 mL mR (hE m) (hw m).2.1 (hw m).2.2.1 (hw m).2.2.2.2
    (fun i => by linarith [hcr m, hxL0 i])
  have hdsL := hds1L mL mR (hE m) (hw m).2.1 (hw m).2.2.1 (hw m).2.2.2.1
    (fun j => by linarith [hcr m, hxR0 j])
  have hεk : ∀ k, ENNReal.ofReal (epsK k) ≠ 0 := fun k => (ENNReal.ofReal_pos.2 (epsK_pos k)).ne'
  have hdiv : ∀ k, ENNReal.ofReal (epsK k * c k) / ENNReal.ofReal (epsK k) = ENNReal.ofReal (c k) := by
    intro k
    rw [ENNReal.ofReal_mul (epsK_pos k).le, mul_comm, mul_div_assoc,
      ENNReal.div_self (hεk k) ENNReal.ofReal_ne_top, mul_one]
  have hA : ∀ k, P m {ω | ENNReal.ofReal (epsK k) ≤ occR k ω} ≤ ENNReal.ofReal (c k) := by
    intro k
    refine (meas_ge_le_lintegral_div ((D m).aemeasurable_occ hε hg T (hφm (δk k)) (EvolData.continuous_gpR hnR))
      (hεk k) ENNReal.ofReal_ne_top).trans ?_
    rw [← hdiv k]
    refine ENNReal.div_le_div_right ?_ _
    refine (lintegral_mono_ae ?_).trans ((hds.1 (δk k) (hδk0 k) ((hδkr k).trans_le (min_le_left _ _))).trans
      (ENNReal.ofReal_le_ofReal (hδkC k)))
    filter_upwards [(D m).ae_mem_G] with ω hω
    exact (D m).occ_gpR_le hε hg hnR T _ hω
  have hB : ∀ k, P m {ω | ENNReal.ofReal (epsK k) ≤ occL k ω} ≤ ENNReal.ofReal (c k) := by
    intro k
    refine (meas_ge_le_lintegral_div ((D m).aemeasurable_occ hε hg T (hφm (δk k)) (EvolData.continuous_gpL hnL))
      (hεk k) ENNReal.ofReal_ne_top).trans ?_
    rw [← hdiv k]
    refine ENNReal.div_le_div_right ?_ _
    refine (lintegral_mono_ae ?_).trans ((hdsL.1 (δk k) (hδk0 k) ((hδkr k).trans_le (min_le_right _ _))).trans
      (ENNReal.ofReal_le_ofReal (hδkCL k)))
    filter_upwards [(D m).ae_mem_G] with ω hω
    exact (D m).occ_gpL_le hε hg hnL T _ hω
  -- the geometric sum
  have hsum : ∑' k, (ENNReal.ofReal (c k) + ENNReal.ofReal (c k)) = ENNReal.ofReal (e' / 2) := by
    have hcs : Summable c := (summable_geometric_two.mul_left (e' / 8))
    have htc : ∑' k, c k = e' / 4 := by
      simp only [hc]
      rw [tsum_mul_left, tsum_geometric_two]
      ring
    rw [ENNReal.tsum_add, ← ENNReal.ofReal_tsum_of_nonneg (fun k => (hcpos k).le) hcs, htc,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  have hU : P m (⋃ k, ({ω | ENNReal.ofReal (epsK k) ≤ occR k ω} ∪ {ω | ENNReal.ofReal (epsK k) ≤ occL k ω})) ≤
      ENNReal.ofReal (e' / 2) := by
    refine (measure_iUnion_le _).trans ?_
    rw [← hsum]
    exact ENNReal.tsum_le_tsum fun k => (measure_union_le _ _).trans (add_le_add (hA k) (hB k))
  have hβm : P m ((D m).bP T ⁻¹' Kβᶜ) ≤ ENNReal.ofReal (e' / 2) := by
    rw [← Measure.map_apply ((D m).measurable_bP T) hKβc.isClosed.measurableSet.compl, hν m]
    exact hKβν
  show (D m).law T (Kf ×ˢ Kβ)ᶜ ≤ e
  rw [EvolData.law, Measure.map_apply_of_aemeasurable ((D m).aemeasurable_pair hε hg T)
    (hKf.prod hKβc).isClosed.measurableSet.compl]
  calc P m _ ≤ P m ((D m).Gᶜ ∪ ((D m).bP T ⁻¹' Kβᶜ ∪
        ⋃ k, ({ω | ENNReal.ofReal (epsK k) ≤ occR k ω} ∪ {ω | ENNReal.ofReal (epsK k) ≤ occL k ω}))) :=
        measure_mono hsub
    _ ≤ P m (D m).Gᶜ + (P m ((D m).bP T ⁻¹' Kβᶜ) +
        P m (⋃ k, ({ω | ENNReal.ofReal (epsK k) ≤ occR k ω} ∪ {ω | ENNReal.ofReal (epsK k) ≤ occL k ω}))) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ 0 + (ENNReal.ofReal (e' / 2) + ENNReal.ofReal (e' / 2)) := by
        rw [(D m).null_G]
        exact add_le_add le_rfl (add_le_add hβm hU)
    _ = ENNReal.ofReal e' := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ e := he'e.le

end Tight

end DSReach

end Supp12

end InteractingSLE

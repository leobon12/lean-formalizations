/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactMartWord
import InteractingSLE.Spec.Sec7.Lemma71CMeas

/-!
# The image word of the contact step, part 4: the killed driver is an explicit limit, hence measurable

Packet PROVE-WW-B17, step B1 of PROVE-WW-B15's plan ("measurable image driver"). The killed glued driver `kW γ P` of a
killed arc (`ReverseContactMartWord`) is defined by choice (`chainDrv`). As for Lemma 7.1's mapped segments
(`Sec7.Lemma71C.segDrv`, PROVE-LEMMA71C), it is recovered before the terminal capacity by an explicit limit of
real parts of rational expressions in the mapping-out functions of the filled prefixes at capacity times, read at the
fixed points `i (N + 1)` (`Sec7.Lemma71C.tendsto_drvQuot`). Here the prefixes are taken along the killed capacity
inverse `kInv γ P` (inside `P`, so that times after the killing never enter):

* `kPre γ P r = γ([0, σ⁻¹(max r 0)])`, `kG`, `kQuot`;
* **`IsKilledArc.eventually_tendsto_kQuot`**: before the terminal capacity, for all large `N` the point `i (N + 1)` is
  outside every filled prefix up to `s`, and the quotients there tend to `kW γ P s`;
* **`measurable_indicator_kW`**: for a family of killed arcs, the killed driver at a fixed capacity time is measurable on
  an event below the terminal capacity as soon as the prefixes up to that capacity time are measurable for the dyadic
  hitting events there (PROVE-RESTART-CPL4's `measurable_indicator_mapOut`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open Sec7.Lemma71C Restart ImgWord

namespace ImgWord

/-- The prefix of a killed arc up to the capacity time `max r 0`. -/
def kPre (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) : Set ℂ := γ '' Icc 0 (kInv γ P (max r 0))

/-- The mapping-out function of the filled prefix at capacity time `r`. -/
def kG (γ : ℝ → ℂ) (P : Set ℝ) (r : ℝ) (z : ℂ) : ℂ := ConformalImage.mapOut (fillH (kPre γ P r)) z

/-- The left difference quotient of `kG` at capacity time `s`, read at `z`. -/
def kQuot (γ : ℝ → ℂ) (P : Set ℝ) (s : ℝ) (z : ℂ) (k : ℕ) : ℝ :=
  (kG γ P s z - 2 / (((k : ℂ) + 1) * (kG γ P s z - kG γ P (s - 1 / ((k : ℝ) + 1)) z))).re

end ImgWord

variable {γ : ℝ → ℂ} {P : Set ℝ}

theorem IsKilledArc.kInv_zero (hγ : IsKilledArc γ P) : kInv γ P 0 = 0 := by
  have := hγ.kInv_capClock hγ.zero_mem
  rwa [hγ.capClock_zero] at this

/-- **The filled prefixes are the hulls of a local driver** on the capacity range of a prefix in `P`. -/
theorem IsKilledArc.fillH_kPre_eq (hγ : IsKilledArc γ P) {S : ℝ} (hS : S ∈ P) {w : ℝ → ℝ}
    (hK : ∀ u ∈ Icc 0 S, fwdHull w (capClock γ u) = γ '' Ioc 0 u) {r : ℝ} (hr : r ≤ capClock γ S) :
    fillH (kPre γ P r) = fwdHull w (max r 0) := by
  set r' := max r 0 with hr'
  have hr'0 : 0 ≤ r' := le_max_right _ _
  have hr'S : r' ≤ capClock γ S := max_le hr (hγ.capClock_nonneg hS)
  have hlt : ((r'.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P :=
    lt_of_le_of_lt (WithTop.coe_le_coe.2 (Real.toNNReal_le_toNNReal hr'S)) (hγ.lt_kLife hS)
  have hle := hγ.kInv_le hS hlt (by rw [Real.coe_toNNReal _ hr'0]; exact hr'S)
  obtain ⟨hm, he⟩ := hγ.kInv_spec hlt
  rw [Real.coe_toNNReal _ hr'0] at hm he hle
  rw [kPre, hγ.fillH_eq hm, ← hK _ ⟨hγ.nonneg _ hm, hle⟩, he]

/-- **The quotients recover the killed driver**: before the terminal capacity, for all large `N` the test point
`i (N + 1)` is outside every filled prefix up to `s`, and the quotients at it tend to `kW γ P s`. -/
theorem IsKilledArc.eventually_tendsto_kQuot (hγ : IsKilledArc γ P) {s : ℝ≥0}
    (hs : (s : WithTop ℝ≥0) < kLife γ P) :
    ∀ᶠ N : ℕ in atTop, (∀ r ≤ (s : ℝ), zPt N ∉ fillH (kPre γ P r)) ∧
      Tendsto (fun k : ℕ => kQuot γ P s (zPt N) k) atTop (𝓝 (kW γ P s)) := by
  obtain ⟨S, hS, hsS⟩ := lt_kLife_iff.1 hs
  have hS0 : 0 < S := by
    refine lt_of_le_of_ne (hγ.nonneg S hS) fun h => ?_
    rw [← h, hγ.capClock_zero] at hsS
    exact absurd hsS (not_lt.2 s.coe_nonneg)
  obtain ⟨W, hW, hW0, hEq, hK⟩ := hγ.chainDrv_spec hS hS0
  have hkW : kW γ P s = W s := by rw [kW_of_lt hs]; exact hEq ⟨s.coe_nonneg, hsS.le⟩
  rw [hkW]
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hW (s : ℝ)).subset_ball 0
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge R
  filter_upwards [eventually_ge_atTop N₀] with N hN
  have hzK : ∀ r ≤ (s : ℝ), zPt N ∉ fwdHull W r := by
    intro r hr hmem
    have h1 := hR ((QuantumZipper.fwdHull_mono (W := W)).1 hr hmem)
    rw [Metric.mem_ball, dist_zero_right, norm_zPt] at h1
    have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hfill : ∀ r ≤ (s : ℝ), zPt N ∉ fillH (kPre γ P r) := by
    intro r hr
    rw [hγ.fillH_kPre_eq hS hK (hr.trans hsS.le)]
    exact hzK _ (max_le hr s.coe_nonneg)
  refine ⟨hfill, ?_⟩
  have hg : ∀ r ∈ Icc 0 (s : ℝ), kG γ P r (zPt N) = fwdMap W r (zPt N) + W r := fun r hr => by
    have hA := hγ.fillH_kPre_eq hS hK (hr.2.trans hsS.le)
    rw [max_eq_left hr.1] at hA
    simp only [kG, hA]
    exact IsMapOut.eqOn (isHPHull_fwdHull hW hr.1)
      (ConformalImage.isMapOut_mapOut (isHPHull_fwdHull hW hr.1)) (isMapOut_fwdMap hW hW0 hr.1)
      ⟨zPt_mem_H N, hzK r hr.2⟩
  rcases (s.coe_nonneg).lt_or_eq with hs0 | hs0
  · exact tendsto_drvQuot hW hs0 (zPt_mem_H N) (hzK s le_rfl) hg
  · have hne : zPt N ≠ ((W 0 : ℝ) : ℂ) := by
      intro h
      have h1 := congrArg Complex.im h
      rw [Complex.ofReal_im] at h1
      have h2 : (0 : ℝ) < (zPt N).im := zPt_mem_H N
      linarith
    have hq : ∀ k : ℕ, kQuot γ P s (zPt N) k = W s := by
      intro k
      have hk : (s : ℝ) - 1 / ((k : ℝ) + 1) ≤ 0 := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        rw [← hs0]; linarith
      have e1 : kG γ P ((s : ℝ) - 1 / ((k : ℝ) + 1)) (zPt N) = kG γ P s (zPt N) := by
        have h1 : max ((s : ℝ) - 1 / ((k : ℝ) + 1)) 0 = max (s : ℝ) 0 := by
          rw [max_eq_right hk, ← hs0, max_self]
        simp only [kG, kPre, h1]
      have e2 := hg s ⟨s.coe_nonneg, le_rfl⟩
      rw [← hs0, QuantumZipper.B5.fwdMap_zero_time W hne, sub_add_cancel] at e2
      rw [← hs0] at e1 ⊢
      simp only [kQuot, e1, sub_self, mul_zero, div_zero, sub_zero, e2, hW0]
      simp only [zPt, mul_re, I_re, add_re, natCast_re, one_re, zero_mul, I_im, add_im, natCast_im,
        one_im, add_zero, zero_sub, mul_zero, neg_zero]
    simp only [hq]
    exact tendsto_const_nhds

theorem kInv_mem (hγ : IsKilledArc γ P) (r : ℝ) : kInv γ P r ∈ P := by
  classical
  unfold kInv
  split_ifs with h
  · exact h.choose_spec.1
  · exact hγ.zero_mem

/-! ### Measurability at a fixed capacity time -/

section Fixed

variable {Ω : Type*} [MeasurableSpace Ω] {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ}

namespace ImgWord

open scoped Classical in
/-- The prefix at capacity time `max r 0` on `E`, and `∅` off `E`. -/
def kPreOn (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (E : Set Ω) (r : ℝ) (ω : Ω) : Set ℂ :=
  if ω ∈ E then kPre (γ ω) (P ω) r else ∅

end ImgWord

omit [MeasurableSpace Ω] in
theorem isCompact_kPreOn (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (E : Set Ω) (r : ℝ) (ω : Ω) :
    IsCompact (kPreOn γ P E r ω) := by
  classical
  unfold kPreOn
  split_ifs
  · exact isCompact_Icc.image_of_continuousOn ((hγ ω).cont.mono ((hγ ω).icc _ (kInv_mem (hγ ω) _)))
  · exact isCompact_empty

omit [MeasurableSpace Ω] in
theorem isPreconnected_kPreOn (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (E : Set Ω) (r : ℝ) (ω : Ω) :
    IsPreconnected (kPreOn γ P E r ω ∪ Restart.lowerHalf) := by
  classical
  unfold kPreOn
  split_ifs
  · refine (isPreconnected_Icc.image _ ((hγ ω).cont.mono ((hγ ω).icc _ (kInv_mem (hγ ω) _)))).union 0
      ⟨0, ⟨le_rfl, (hγ ω).nonneg _ (kInv_mem (hγ ω) _)⟩, (hγ ω).zero⟩ Restart.zero_mem_lowerHalf
      InteractingSLE.isPreconnected_lowerHalf
  · rw [empty_union]
    exact InteractingSLE.isPreconnected_lowerHalf

/-- **The killed driver at a fixed capacity time is measurable** on an event `E` below the terminal capacity, as soon
as the prefixes up to that capacity time are measurable for the dyadic hitting events on `E`. -/
theorem measurable_indicator_kW (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {s : ℝ≥0} {E : Set Ω}
    (hE : MeasurableSet E) (hEs : ∀ ω ∈ E, (s : WithTop ℝ≥0) < kLife (γ ω) (P ω))
    (hpre : ∀ r : ℝ, 0 ≤ r → r ≤ s → ∀ (n : ℕ) (k : ℤ × ℤ),
      MeasurableSet (E ∩ {ω | (dyadicSquare n k ∩ kPre (γ ω) (P ω) r).Nonempty})) :
    Measurable (E.indicator fun ω => kW (γ ω) (P ω) s) := by
  classical
  have hdy : ∀ r ≤ (s : ℝ), IsDyadicHitMeasurable (kPreOn γ P E r) := by
    intro r hr n k
    have heq : {ω | (dyadicSquare n k ∩ kPreOn γ P E r ω).Nonempty} =
        E ∩ {ω | (dyadicSquare n k ∩ kPre (γ ω) (P ω) (max r 0)).Nonempty} := by
      ext ω
      by_cases hω : ω ∈ E
      · simp only [kPreOn, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, true_and, kPre,
          max_eq_left (le_max_right r 0)]
      · simp [kPreOn, hω]
    rw [heq]
    exact hpre _ (le_max_right _ _) (max_le hr s.coe_nonneg) n k
  set G : ℝ → ℂ → Ω → ℂ := fun r z => {ω | z ∈ H \ fillH (kPreOn γ P E r ω)}.indicator
    fun ω => ConformalImage.mapOut (fillH (kPreOn γ P E r ω)) z with hGdef
  have hGm : ∀ r ≤ (s : ℝ), ∀ z, Measurable (G r z) := fun r hr z =>
    measurable_indicator_mapOut (hdy r hr) (isCompact_kPreOn hγ E r) (isPreconnected_kPreOn hγ E r) z
  set X : ℕ → ℕ → Ω → ℝ := fun N k ω => (G s (zPt N) ω - 2 / (((k : ℂ) + 1) *
    (G s (zPt N) ω - G ((s : ℝ) - 1 / ((k : ℝ) + 1)) (zPt N) ω))).re with hXdef
  have hXm : ∀ N k, Measurable (X N k) := by
    intro N k
    have h1 := hGm s le_rfl (zPt N)
    have h2 := hGm ((s : ℝ) - 1 / ((k : ℝ) + 1)) (by
      have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      linarith) (zPt N)
    exact Complex.measurable_re.comp (h1.sub (measurable_const.div (measurable_const.mul (h1.sub h2))))
  set Y : ℕ → Ω → ℝ := fun N ω => limUnder atTop fun k => X N k ω with hYdef
  have hYm : ∀ N, Measurable (Y N) := fun N =>
    (StronglyMeasurable.limUnder fun k => (hXm N k).stronglyMeasurable).measurable
  refine measurable_of_tendsto_metrizable (f := fun N => E.indicator (Y N)) (fun N => (hYm N).indicator hE) ?_
  rw [tendsto_pi_nhds]
  intro ω
  by_cases hω : ω ∈ E
  · simp only [indicator_of_mem hω]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(hγ ω).eventually_tendsto_kQuot (hEs ω hω)] with N hN
    obtain ⟨hout, hlim⟩ := hN
    have hXN : ∀ k, X N k ω = kQuot (γ ω) (P ω) s (zPt N) k := by
      intro k
      have hG : ∀ r ≤ (s : ℝ), G r (zPt N) ω = kG (γ ω) (P ω) r (zPt N) := by
        intro r hr
        have hmem : ω ∈ {ω | zPt N ∈ H \ fillH (kPreOn γ P E r ω)} := by
          refine ⟨zPt_mem_H N, ?_⟩
          simp only [kPreOn, hω, ↓reduceIte]
          exact hout r hr
        rw [hGdef]
        dsimp only
        rw [indicator_of_mem hmem]
        simp only [kPreOn, hω, ↓reduceIte, kG]
      have hk : (s : ℝ) - 1 / ((k : ℝ) + 1) ≤ s := by
        have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
        linarith
      simp only [hXdef, kQuot, hG s le_rfl, hG _ hk]
    have : Y N ω = kW (γ ω) (P ω) s := by
      simp only [hYdef, hXN]
      exact hlim.limUnder_eq
    exact this.symm
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

end Fixed

end InteractingSLE.WangWu

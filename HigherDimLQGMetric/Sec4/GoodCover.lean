import HigherDimLQGMetric.Sec4.Asymp
import HigherDimLQGMetric.Sec4.ChainDet
import HigherDimLQGMetric.Sharp.GridCount
import HigherDimLQGMetric.Sharp.GridNear

/-!
# Good scales at every grid point (packet L9b; MA6 P4 for [1] Lemma 4.4)

`l9b_goodCover`: with `C` the constant of Lemma 4.3 for the threshold `p` of the shell decoupling
(G3's `lemmaA1`, rate `A = (d+1)/c`, `θ = 19/20`), outside an event of probability `≤ θ` (for `ε` small,
uniformly in the subset `R ⊆ N^ε` with `|N^ε| ≤ 10|R|`), every point of the grid `εℤ^d ∩ B_{R₀}(0)` has a
radius `2^{-k}`, `k ∈ R`, at which `E^ε_{2^{-k}}(u; C)` occurs.

Proof (MA6 P4): the radii `2^{-(k_lo + i)}`, `i < m(ε)`, have ratio `1/2`; the events are `E` for indices in
`R` and the sure event otherwise, all `AEEventIn` the shell σ-algebras (`ref1_lemma43_aeEventIn`) and of
probability `≥ p` (`ref1_lemma43`); if all indices of `R` fail, fewer than `(19/20) m(ε)` succeed
(`l9b_card_lt`), which has probability `≤ e^{-A m(ε)} ≤ ε^{d+1}`; a union bound over the
`≤ (2R₀/ε + 5)^d` grid points gives `≤ (2R₀ + 5)^d ε`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- a finite set containing the grid `εℤ^d ∩ B_R(0)` -/
def l9bGrid (d : ℕ) (R ε : ℝ) : Finset (Rd d) := shellGridBox d (⌈R / ε⌉₊ + 1) ε

theorem card_l9bGrid_le {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ((l9bGrid d R ε).card : ℝ) ≤ ((2 * R + 5) / ε) ^ d := by
  have h1 := card_shellGridBox_le d (⌈R / ε⌉₊ + 1) ε
  have h2 : ((2 * (⌈R / ε⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ (2 * R + 5) / ε := by
    push_cast
    have hc : (⌈R / ε⌉₊ : ℝ) < R / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have h5 : 5 ≤ 5 / ε := by rw [le_div_iff₀ hε]; linarith
    calc 2 * ((⌈R / ε⌉₊ : ℝ) + 1) + 1 ≤ 2 * (R / ε + 2) + 1 := by linarith
      _ = 2 * R / ε + 5 := by ring
      _ ≤ 2 * R / ε + 5 / ε := by linarith
      _ = (2 * R + 5) / ε := by ring
  calc ((l9bGrid d R ε).card : ℝ) ≤ (((2 * (⌈R / ε⌉₊ + 1) + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast h1
    _ = ((2 * (⌈R / ε⌉₊ + 1) + 1 : ℕ) : ℝ) ^ d := by push_cast; ring
    _ ≤ ((2 * R + 5) / ε) ^ d := pow_le_pow_left₀ (by positivity) h2 d

theorem mem_l9bGrid {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) {u : Rd d} (hu : u ∈ gridPts ε)
    (huR : ‖u‖ < R) : u ∈ l9bGrid d R ε :=
  grid_ball_subset_shellGridBox hε hR ⟨hu, by rwa [mem_ball, dist_zero_right]⟩

/-- `e^{-A m} ≤ ε^{d+1}` when `A m ≥ (d+1) log ε⁻¹` -/
theorem l9b_exp_le_pow {ε A : ℝ} (hε : 0 < ε) {m : ℝ}
    (hm : ((d : ℝ) + 1) * Real.log ε⁻¹ ≤ A * m) : Real.exp (-A * m) ≤ ε ^ (d + 1) := by
  have h : Real.exp (-A * m) ≤ Real.exp (-(((d : ℝ) + 1) * Real.log ε⁻¹)) :=
    Real.exp_le_exp.2 (by linarith)
  refine h.trans_eq ?_
  rw [Real.log_inv, mul_neg, neg_neg, mul_comm, Real.exp_mul, Real.exp_log hε,
    ← Real.rpow_natCast]
  push_cast
  ring_nf

/-- **Good scales at every grid point** (MA6 P4 for [1] Lemma 4.4). -/
theorem l9b_goodCover (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R₀ : ℝ, 0 < R₀ → ∀ θ : ℝ≥0∞, 0 < θ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ R : Finset ℕ,
        R ⊆ nIdx ζ ε → (nIdx ζ ε).card ≤ 10 * R.card →
        P {ω | ∃ u ∈ l9bGrid d R₀ ε, ∀ k ∈ R, ¬ shellGood κ ξ D c ε C u (dyad k) (h ω)} ≤ θ := by
  have hd2 : 2 ≤ d := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set cc : ℝ := ζ / (4 * Real.log 2) with hcc
  have hcc0 : 0 < cc := by positivity
  set A : ℝ := ((d : ℝ) + 1) / cc with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨p, hp, Hs⟩ := lemmaA1 (by omega : 1 ≤ d) (1 / 4) 4 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) A (19 / 20) hA0 (by norm_num) (by norm_num)
  obtain ⟨C, hC1, ε₃, hε₃, H43⟩ := ref1_lemma43 hL6a hB2 hd hξ hsub hκ hD hp
  refine ⟨C, hC1, fun R₀ hR₀ θ hθ => ?_⟩
  -- the eventual conditions on `ε`
  have hsmallθ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal ((2 * R₀ + 5) ^ d * ε) < θ := by
    have ht : Tendsto (fun ε : ℝ => ENNReal.ofReal ((2 * R₀ + 5) ^ d * ε)) (𝓝[>] 0) (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      refine ENNReal.tendsto_ofReal ?_
      exact ((continuous_const.mul continuous_id).tendsto' (0 : ℝ) 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    exact ht.eventually (gt_mem_nhds hθ)
  have hev := (l9b_eventually_locHyp hd2 hκ).and ((l9b_eventually_locRad_small hζ0).and
    ((eventually_mCnt_ge hζ0).and (hsmallθ.and ((tendsto_log_inv_nhdsGT_zero.eventually
      (eventually_gt_atTop 0)).and (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))))))
  obtain ⟨ε₁, hε₁, Hev⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min ε₁ ε₃, lt_min hε₁ hε₃, ?_⟩
  intro Ω _ P _ h hh ε hε R hR hRcard
  obtain ⟨⟨hε0, hε1, hrad, -, hZ⟩, hloc, hm, hθε, hL0, hε01⟩ :=
    Hev ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hZ0 : locMass κ ε (locRad ε) ≠ 0 := by linarith
  set n := mCnt ζ ε with hn
  set k₀ := kLo ζ ε with hk₀
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hm
    exact_mod_cast this
  -- radii and events at one grid point
  let r : ℕ → ℝ := fun i => dyad (k₀ + i)
  have hr : ∀ i, 0 < r i := fun i => dyad_pos _
  have hrq : ∀ i, r (i + 1) ≤ 1 / 2 * r i := fun i => by
    simp only [r, ← add_assoc, dyad_succ]; ring_nf; exact le_rfl
  have hmemR : ∀ i, k₀ + i ∈ R → k₀ + i ∈ nIdx ζ ε := fun i hi => hR hi
  have hεr : ∀ i, k₀ + i ∈ R → ε < r i := by
    intro i hi
    have h1 := le_dyad_of_mem_nIdx hε0 hε1 hζ1 (hmemR i hi)
    have h2 : ε < ε ^ (1 - ζ / 2) := by
      have := l9b_eventually_mesh (ζ := ζ) hζ0 1
      rw [l9b_rpow_one_sub_half hε0]
      have hgt : 1 < ε ^ (-(ζ / 2)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 hε01.2
        (by linarith)
      nlinarith
    exact h2.trans_le h1
  have hloc' : ∀ i, k₀ + i ∈ R → 24 * locRad ε ≤ r i := fun i hi =>
    hloc.trans (le_dyad_of_mem_nIdx hε0 hε1 hζ1 (hmemR i hi))
  have hbad : ∀ u ∈ l9bGrid d R₀ ε,
      P {ω | ∀ k ∈ R, ¬ shellGood κ ξ D c ε C u (dyad k) (h ω)} ≤
        ENNReal.ofReal (Real.exp (-A * n)) := by
    intro u _
    classical
    let E : ℕ → Set Ω := fun i => if k₀ + i ∈ R then {ω | shellGood κ ξ D c ε C u (r i) (h ω)}
      else univ
    have hE : ∀ i, AEEventIn P (fieldSigma0 h (ann u (1 / 4 * r i) (4 * r i))) (E i) := by
      intro i
      by_cases hi : k₀ + i ∈ R
      · simp only [E, hi, ite_true]
        rw [show 1 / 4 * r i = r i / 4 by ring]
        exact ref1_lemma43_aeEventIn hd hκ hD hh hrad hZ0 (hloc' i hi) u (by linarith)
      · simp only [E, hi, ite_false]
        exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
    have hpE : ∀ i, ENNReal.ofReal p ≤ P (E i) := by
      intro i
      by_cases hi : k₀ + i ∈ R
      · simp only [E, hi, ite_true]
        exact H43 P h hh ε ⟨hε0, hε.2.trans_le (min_le_right _ _)⟩ (r i) (hεr i hi)
          (dyad_le_one _) u
      · simp only [E, hi, ite_false, measure_univ]
        exact ENNReal.ofReal_le_one.2 hp.le
    refine le_trans (measure_mono fun ω hω => ?_) (Hs P h hh.1 u r hr hrq E hE hpE n)
    show ((((Finset.range n).filter (fun i => ω ∈ E i)).card : ℕ) : ℝ) < 19 / 20 * (n : ℝ)
    refine l9b_card_lt (k₀ := k₀) (R := R) (by simpa [nIdx, hk₀, hn] using hR) (by
      rw [card_nIdx] at hRcard; exact hRcard) hn0 _ fun i hi => ?_
    obtain ⟨hin, hiE⟩ := Finset.mem_filter.1 hi
    refine ⟨Finset.mem_range.1 hin, fun hkR => ?_⟩
    have : ω ∈ {ω | shellGood κ ξ D c ε C u (r i) (h ω)} := by
      simpa only [E, hkR, ite_true] using hiE
    exact hω (k₀ + i) hkR this
  -- union bound
  calc P {ω | ∃ u ∈ l9bGrid d R₀ ε, ∀ k ∈ R, ¬ shellGood κ ξ D c ε C u (dyad k) (h ω)}
      = P (⋃ u ∈ l9bGrid d R₀ ε, {ω | ∀ k ∈ R, ¬ shellGood κ ξ D c ε C u (dyad k) (h ω)}) := by
        congr 1; ext ω; simp
    _ ≤ ∑ u ∈ l9bGrid d R₀ ε, P {ω | ∀ k ∈ R, ¬ shellGood κ ξ D c ε C u (dyad k) (h ω)} :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _u ∈ l9bGrid d R₀ ε, ENNReal.ofReal (Real.exp (-A * n)) := Finset.sum_le_sum hbad
    _ = ENNReal.ofReal ((l9bGrid d R₀ ε).card * Real.exp (-A * n)) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal ((2 * R₀ + 5) ^ d * ε) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hexp : Real.exp (-A * n) ≤ ε ^ (d + 1) := by
          refine l9b_exp_le_pow hε0 ?_
          have : A * cc = (d : ℝ) + 1 := by rw [hA]; field_simp
          calc ((d : ℝ) + 1) * Real.log ε⁻¹ = A * (cc * Real.log ε⁻¹) := by rw [← this]; ring
            _ ≤ A * n := by gcongr
        calc ((l9bGrid d R₀ ε).card : ℝ) * Real.exp (-A * n)
            ≤ ((2 * R₀ + 5) / ε) ^ d * ε ^ (d + 1) :=
              mul_le_mul (card_l9bGrid_le hR₀.le hε0 hε1) hexp (by positivity) (by positivity)
          _ = (2 * R₀ + 5) ^ d * ε := by
              rw [div_pow, pow_succ]; field_simp
    _ ≤ θ := hθε.le

end HigherDimLQGMetric

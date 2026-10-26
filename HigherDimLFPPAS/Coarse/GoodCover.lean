import HigherDimLFPPAS.Coarse.Lemma43
import HigherDimLQGMetric.Sec4.GoodCover

/-!
# Good scales at every grid point, with a polynomial rate (packet C27; MA3 P11 Step 2)

The event (4.11) of [3]'s proof of Lemma 4.4, for signed seeds and with an explicit polynomial failure bound: for
every `β > 0` there are `C ≥ 1` and `ε₀ > 0` (independent of the radius `R₀` of the grid) such that, uniformly in the
deterministic subset `R ⊆ N^ε` with `|N^ε| ≤ 10 |R|`, outside an event of outer probability `≤ (2R₀ + 5)^d ε^β`
every point of the grid `εℤ^d ∩ B_{R₀}(0)` (`l9bGrid`) has a radius `2^{-k}`, `k ∈ R`, at which `E^ε_{2^{-k}}(u; C)`
occurs (`c27_goodCover`).

The proof is the host's `HigherDimLQGMetric.l9b_goodCover` with three changes: Lemma 4.3′ (`c27_lemma43`, from (1.6))
in place of `ref1_lemma43`; the shell-decoupling rate `A = (d + β)/c` (`c = ζ/(4 log 2)`) in place of `(d+1)/c`, so
that `e^{-A m(ε)} ≤ ε^{d+β}` (`c27_exp_le_rpow`); and the failure bound is exported instead of `≤ θ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Coarse

open HigherDimLQGMetric HigherDimLFPPAS.Signed
open HigherDimLFPP (Rd e₁ lfppDistOn)

variable {d : ℕ}

/-- `e^{-A m} ≤ ε^{d+β}` when `A m ≥ (d+β) log ε⁻¹` -/
theorem c27_exp_le_rpow {ε A β m : ℝ} (hε : 0 < ε)
    (hm : ((d : ℝ) + β) * Real.log ε⁻¹ ≤ A * m) : Real.exp (-A * m) ≤ ε ^ ((d : ℝ) + β) := by
  have h : Real.exp (-A * m) ≤ Real.exp (-(((d : ℝ) + β) * Real.log ε⁻¹)) :=
    Real.exp_le_exp.2 (by linarith)
  refine h.trans_eq ?_
  rw [Real.rpow_def_of_pos hε, Real.log_inv]
  ring_nf

/-- `|grid| e^{-A m} ≤ (2R₀ + 5)^d ε^β` once `e^{-A m} ≤ ε^{d+β}` -/
theorem c27_card_mul_le {R₀ ε β x : ℝ} (hR₀ : 0 ≤ R₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hx0 : 0 ≤ x)
    (hx : x ≤ ε ^ ((d : ℝ) + β)) :
    ((l9bGrid d R₀ ε).card : ℝ) * x ≤ (2 * R₀ + 5) ^ d * ε ^ β := by
  have hsplit : ε ^ ((d : ℝ) + β) = ε ^ d * ε ^ β := by
    rw [Real.rpow_add hε, Real.rpow_natCast]
  calc ((l9bGrid d R₀ ε).card : ℝ) * x ≤ ((2 * R₀ + 5) / ε) ^ d * ε ^ ((d : ℝ) + β) :=
        mul_le_mul (card_l9bGrid_le hR₀ hε hε1) hx hx0 (by positivity)
    _ = (2 * R₀ + 5) ^ d * ε ^ β := by
        rw [hsplit, div_pow]
        field_simp

/-- **Good scales at every grid point, polynomial rate** (MA3 P11 Step 2; [3] (4.11)): for `β > 0` there are `C ≥ 1`
and `ε₀ > 0` such that for every `R₀ > 0`, every normalized LGF, `ε ∈ (0, ε₀)` and `R ⊆ N^ε` with `|N^ε| ≤ 10 |R|`,
the probability that some grid point of `εℤ^d ∩ B_{R₀}` has no good radius in `R` is `≤ (2R₀ + 5)^d ε^β`. -/
theorem c27_goodCover (hd : 3 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ R₀ : ℝ, 0 < R₀ →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistRd d), IsNormalizedLGF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ R : Finset ℕ,
        R ⊆ nIdx ζ ε → (nIdx ζ ε).card ≤ 10 * R.card →
        P {ω | ∃ u ∈ l9bGrid d R₀ ε, ∀ k ∈ R,
          ¬ shellGood κ ξ D (fun r => r ^ (ξ * Q)) ε C u (dyad k) (h ω)} ≤
          ENNReal.ofReal ((2 * R₀ + 5) ^ d * ε ^ β) := by
  have hd2 : 2 ≤ d := by omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set cc : ℝ := ζ / (4 * Real.log 2) with hcc
  have hcc0 : 0 < cc := by positivity
  set A : ℝ := ((d : ℝ) + β) / cc with hA
  have hA0 : 0 < A := by positivity
  obtain ⟨p, hp, Hs⟩ := lemmaA1 (by omega : 1 ≤ d) (1 / 4) 4 (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) A (19 / 20) hA0 (by norm_num) (by norm_num)
  obtain ⟨C, hC1, δ₀, hδ₀, ε₃, hε₃, H43⟩ := c27_lemma43 hd2 hD hκ hconv hp
  set c : ℝ → ℝ := fun r => r ^ (ξ * Q) with hcdef
  have hDw : IsWeakExpMetric d ξ D c := hD
  refine ⟨C, hC1, ?_⟩
  -- the eventual conditions on `ε`
  have hev := (l9b_eventually_locHyp_seed hd2 hκ).and ((l9b_eventually_locRad_small hζ0).and
    ((eventually_mCnt_ge hζ0).and ((c27_eventually_ratio_lt hζ0 hδ₀).and
      ((tendsto_log_inv_nhdsGT_zero.eventually (eventually_gt_atTop 0)).and
        (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))))))
  obtain ⟨ε₁, hε₁, Hev⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min ε₁ ε₃, lt_min hε₁ hε₃, fun R₀ hR₀ => ?_⟩
  intro Ω _ P _ h hh ε hε R hR hRcard
  obtain ⟨⟨hε0, hε1, hrad, -, hZ⟩, hloc, hm, hratio, hL0, hε01⟩ :=
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
  have hrlow : ∀ i, k₀ + i ∈ R → ε ^ (1 - ζ / 2) ≤ r i := fun i hi =>
    le_dyad_of_mem_nIdx hε0 hε1 hζ1 (hmemR i hi)
  have hεr : ∀ i, k₀ + i ∈ R → ε < r i := by
    intro i hi
    have h2 : ε < ε ^ (1 - ζ / 2) := by
      rw [l9b_rpow_one_sub_half hε0]
      have hgt : 1 < ε ^ (-(ζ / 2)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg hε0 hε01.2
        (by linarith)
      nlinarith
    exact h2.trans_le (hrlow i hi)
  have hloc' : ∀ i, k₀ + i ∈ R → 24 * locRad ε ≤ r i := fun i hi =>
    hloc.trans (hrlow i hi)
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
        exact ref1_lemma43_aeEventIn_seed hd hκ hDw hh hrad hZ0 (hloc' i hi) u (by linarith)
      · simp only [E, hi, ite_false]
        exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
    have hpE : ∀ i, ENNReal.ofReal p ≤ P (E i) := by
      intro i
      by_cases hi : k₀ + i ∈ R
      · simp only [E, hi, ite_true]
        exact H43 P h hh ε ⟨hε0, hε.2.trans_le (min_le_right _ _)⟩ (r i) (hεr i hi)
          (dyad_le_one _) (hratio _ (hrlow i hi)) u
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
    _ ≤ ENNReal.ofReal ((2 * R₀ + 5) ^ d * ε ^ β) := by
        refine ENNReal.ofReal_le_ofReal (c27_card_mul_le hR₀.le hε0 hε1 (Real.exp_pos _).le ?_)
        refine c27_exp_le_rpow hε0 ?_
        have : A * cc = (d : ℝ) + β := by rw [hA]; field_simp
        calc ((d : ℝ) + β) * Real.log ε⁻¹ = A * (cc * Real.log ε⁻¹) := by rw [← this]; ring
          _ ≤ A * n := by gcongr

end HigherDimLFPPAS.Coarse

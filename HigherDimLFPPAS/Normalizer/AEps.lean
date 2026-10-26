import HigherDimLFPPAS.Normalizer.Basic
import HigherDimLQGMetric.Frozen.TendstoInProbLU
import LQGMetric.Prob.Median

/-!
# `𝔞_ε` is the lower median of `D^ε_h(0, e₁)` under `P` (packet N1; MA1 Details A1)

The paper's normalizer (1.4), `𝔞_ε = inf {a > 0 : P[D^ε_h(0, e₁) ≤ a] ≥ 1/2}` for the given field `h` on
`(Ω, P)`, is the frozen `HigherDimLQGMetric.aEps κ ξ ε` (the lower median under the normalized law
`normLGFLaw d`), and it is positive. The only input on the seed is that the convolution field of the
normalized LGF at cutoff `ε` is a.s. continuous (hypothesis `hc`; for admissible seeds it is supplied in
`Normalizer/Seed.lean`). Main results:

* `n1_half_le_normLGFLaw_iff`, `n1_half_le_prob_iff`: `P[D^ε_h(0, e₁) ≤ x] ≥ 1/2 ↔ aEps κ ξ ε ≤ x`;
* `n1_aEps_pos_of_cont`: `0 < aEps κ ξ ε`;
* `n1_aEps_eq_sInf_prob`, `n1_aEps_eq_paperMedian_of_cont`: the two lower-median formulas;
* `n1_eventually_aEps_pos`: without any continuity input, Assumption 1.1 (v) alone forces
  `0 < aEps κ ξ ε` for all small `ε` (a nonpositive normalizer makes `𝔞_ε⁻¹ D^ε_h(0, e₁) ≤ 0` while
  `D_h(0, e₁) > 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Normalizer

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- The distribution function of `D^ε(0, e₁)` under `normLGFLaw d` reaches `1/2` exactly from
`aEps κ ξ ε` on (right continuity and the lower-quantile characterization). -/
theorem n1_half_le_normLGFLaw_iff {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z) (x : ℝ) :
    (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {g | lfppDist κ ξ ε g (0, e₁ d) ≤ x} ↔ aEps κ ξ ε ≤ x := by
  have : IsProbabilityMeasure (normLGFLaw d) := (normLGFLaw_spec_holds d hd).1
  have hX : AEMeasurable (fun g : DistRd d => lfppDist κ ξ ε g (0, e₁ d)) (normLGFLaw d) :=
    n1_aemeasurable_lfppDist ξ measurable_id hc (0, e₁ d)
  have haEps : aEps κ ξ ε =
      LQGMetric.lowerMedianLaw ((normLGFLaw d).map fun g => lfppDist κ ξ ε g (0, e₁ d)) :=
    LQGMetric.lowerMedian_eq_lowerMedianLaw hX
  have hmap : normLGFLaw d {g | lfppDist κ ξ ε g (0, e₁ d) ≤ x} =
      ((normLGFLaw d).map fun g => lfppDist κ ξ ε g (0, e₁ d)) (Iic x) :=
    (Measure.map_apply_of_aemeasurable hX measurableSet_Iic).symm
  rw [hmap, haEps]
  exact LQGMetric.le_measure_Iic_iff_lowerQuantile_le LQGMetric.inv_two_pos'
    LQGMetric.inv_two_lt_one'

/-- **The paper's distribution function.** For a normalized LGF `h` on `(Ω, P)`:
`P[D^ε_h(0, e₁) ≤ x] ≥ 1/2 ↔ aEps κ ξ ε ≤ x`. -/
theorem n1_half_le_prob_iff {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) (x : ℝ) :
    (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ x} ↔ aEps κ ξ ε ≤ x := by
  have hX : AEMeasurable (fun g : DistRd d => lfppDist κ ξ ε g (0, e₁ d)) (normLGFLaw d) :=
    n1_aemeasurable_lfppDist ξ measurable_id hc (0, e₁ d)
  have hA : NullMeasurableSet {g : DistRd d | lfppDist κ ξ ε g (0, e₁ d) ≤ x} (normLGFLaw d) :=
    hX.nullMeasurable measurableSet_Iic
  have hpre := n1_preimage_eq_normLGFLaw hd hh hA
  change (2 : ℝ≥0∞)⁻¹ ≤ P (h ⁻¹' {g | lfppDist κ ξ ε g (0, e₁ d) ≤ x}) ↔ _
  rw [hpre]
  exact n1_half_le_normLGFLaw_iff hd ξ hc x

/-- **Positivity of the normalizer**: the lower median of the a.s. positive variable `D^ε(0, e₁)` is
positive. -/
theorem n1_aEps_pos_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z) :
    0 < aEps κ ξ ε := by
  by_contra hneg
  push Not at hneg
  have hhalf : (2 : ℝ≥0∞)⁻¹ ≤ normLGFLaw d {g | lfppDist κ ξ ε g (0, e₁ d) ≤ aEps κ ξ ε} :=
    (n1_half_le_normLGFLaw_iff hd ξ hc (aEps κ ξ ε)).2 le_rfl
  have hne : (0 : Rd d) ≠ e₁ d := (HigherDimLFPP.e₁_ne_zero (by omega)).symm
  have hnull : normLGFLaw d {g | lfppDist κ ξ ε g (0, e₁ d) ≤ aEps κ ξ ε} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hc] with g hg
    have hpos := n1_lfppDist_pos (ξ := ξ) hg hne
    change ¬ lfppDist κ ξ ε g (0, e₁ d) ≤ aEps κ ξ ε
    exact not_le.2 (lt_of_le_of_lt hneg hpos)
  rw [hnull] at hhalf
  exact absurd hhalf (by simp)

/-- **`𝔞_ε` as a lower median under `P`** (index set `ℝ`): for a normalized LGF `h` on `(Ω, P)`,
`aEps κ ξ ε = inf {m : P[D^ε_h(0, e₁) ≤ m] ≥ 1/2}`. -/
theorem n1_aEps_eq_sInf_prob {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) :
    aEps κ ξ ε = sInf {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ m}} := by
  have hset : {m : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ m}} =
      Ici (aEps κ ξ ε) := by
    ext m
    exact n1_half_le_prob_iff hd ξ hc hh m
  rw [hset, csInf_Ici]

/-- **`𝔞_ε` as the paper's lower median (1.4)** (index set `(0, ∞)`): for a normalized LGF `h` on
`(Ω, P)`, `aEps κ ξ ε = inf {a > 0 : P[D^ε_h(0, e₁) ≤ a] ≥ 1/2}`. -/
theorem n1_aEps_eq_paperMedian_of_cont {d : ℕ} (hd : 2 ≤ d) {κ : Rd d → ℝ} (ξ : ℝ) {ε : ℝ}
    (hc : ∀ᵐ g ∂(normLGFLaw d), Continuous fun z => convMollify κ ε g z)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) :
    aEps κ ξ ε =
      sInf {a : ℝ | 0 < a ∧ (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ a}} := by
  have hpos := n1_aEps_pos_of_cont hd ξ hc
  have hset : {a : ℝ | 0 < a ∧ (2 : ℝ≥0∞)⁻¹ ≤ P {ω | lfppDist κ ξ ε (h ω) (0, e₁ d) ≤ a}} =
      Ici (aEps κ ξ ε) := by
    ext a
    rw [mem_ofPred_eq, n1_half_le_prob_iff hd ξ hc hh a, mem_Ici]
    exact ⟨fun ha => ha.2, fun ha => ⟨hpos.trans_le ha, ha⟩⟩
  rw [hset, csInf_Ici]

/-- A strictly positive random variable exceeds some deterministic `δ > 0` with positive outer
probability (countable subadditivity; no measurability needed). -/
theorem n1_exists_pos_prob_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : ∀ ω, 0 < X ω) : ∃ δ : ℝ, 0 < δ ∧ 0 < P {ω | δ ≤ X ω} := by
  by_contra hcon
  push Not at hcon
  have hzero : ∀ n : ℕ, P {ω | 1 / ((n : ℝ) + 1) ≤ X ω} = 0 := fun n =>
    le_antisymm (hcon _ (by positivity)) bot_le
  have hcover : (univ : Set Ω) ⊆ ⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) ≤ X ω} := by
    intro ω _
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hX ω)
    exact mem_iUnion.2 ⟨n, hn.le⟩
  have h1 : P univ ≤ 0 :=
    calc P univ ≤ P (⋃ n : ℕ, {ω | 1 / ((n : ℝ) + 1) ≤ X ω}) := measure_mono hcover
      _ ≤ ∑' n : ℕ, P {ω | 1 / ((n : ℝ) + 1) ≤ X ω} := measure_iUnion_le _
      _ = 0 := by simp only [hzero, tsum_zero]
  rw [measure_univ] at h1
  exact absurd h1 (by simp)

/-- **Eventual positivity of `𝔞_ε` from Assumption 1.1 (v)** (no input on the seed): if
`𝔞_ε⁻¹ D^ε_h → D_h` in probability, locally uniformly, then `0 < aEps κ ξ ε` for all small `ε > 0`. -/
theorem n1_eventually_aEps_pos {d : ℕ} (hd : 1 ≤ d) {κ : Rd d → ℝ} {ξ : ℝ}
    {D : DistRd d → ContMetric d} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hconv : TendstoInProbLU P (fun ε ω => (aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (𝓝[>] 0)
      (fun ω => (D (h ω)).1)) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < aEps κ ξ ε := by
  have hne : (0 : Rd d) ≠ e₁ d := (HigherDimLFPP.e₁_ne_zero (by omega)).symm
  obtain ⟨δ, hδ, hpos⟩ := n1_exists_pos_prob_le (P := P)
    (X := fun ω => (D (h ω)).1 (0, e₁ d)) fun ω => ContMetric.apply_pos _ hne
  have hmem : (0, e₁ d) ∈ closedBall (0 : Rd d) 1 ×ˢ closedBall (0 : Rd d) 1 := by
    refine ⟨mem_closedBall_self zero_le_one, ?_⟩
    rw [mem_closedBall, dist_zero_right, HigherDimLFPP.norm_e₁ (by omega)]
  have hlim := hconv 1 one_pos δ hδ
  have hev := (ENNReal.tendsto_nhds_zero.1 hlim) _ (ENNReal.half_pos hpos.ne')
  filter_upwards [hev] with ε hε
  by_contra hneg
  push Not at hneg
  -- with a nonpositive normalizer the event contains `{δ ≤ D_h(0, e₁)}`
  have hsub : {ω | δ ≤ (D (h ω)).1 (0, e₁ d)} ⊆ {ω | ENNReal.ofReal δ ≤
      ⨆ p ∈ closedBall (0 : Rd d) 1 ×ˢ closedBall (0 : Rd d) 1,
        edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p) ((D (h ω)).1 p)} := by
    intro ω hω
    change δ ≤ (D (h ω)).1 (0, e₁ d) at hω
    change ENNReal.ofReal δ ≤ _
    refine le_trans ?_ (le_biSup (fun p => edist (((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) p)
      ((D (h ω)).1 p)) hmem)
    have hN : ((aEps κ ξ ε)⁻¹ • lfppDist κ ξ ε (h ω)) (0, e₁ d) ≤ 0 := by
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 hneg)
        (HigherDimLFPP.lfppDistOn_nonneg _ _ _ _ _)
    rw [edist_dist, Real.dist_eq]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [abs_sub_comm]
    exact le_trans (by linarith) (le_abs_self _)
  have h1 := (measure_mono hsub).trans hε
  exact absurd (h1.trans_lt (ENNReal.half_lt_self hpos.ne' (measure_ne_top _ _))) (lt_irrefl _)

end HigherDimLFPPAS.Normalizer

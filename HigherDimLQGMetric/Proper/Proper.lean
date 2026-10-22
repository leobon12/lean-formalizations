import HigherDimLQGMetric.Proper.Confine
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# [S] Lemma 2.7: almost-sure properness and existence of geodesics

Choose distant sphere barriers with summable failure probabilities and apply Borel–Cantelli.
Every finite metric ball is then contained in a compact Euclidean ball.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- **[S] Lemma 2.7 (properness)** for the sharp weak class. -/
theorem lemma27_proper (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ProperSpace (D (h ω)).Space := by
  have hQ0 : 0 < Q := (Real.sqrt_nonneg _).trans_lt hQ
  let δ : ℕ → ℝ := fun k => ((1 : ℝ) / 2) ^ k
  have hδ : ∀ k, 0 < δ k := fun k => by dsimp [δ]; positivity
  have hchoice : ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ ∀ R : ℝ, 0 < R →
      P {ω | ¬ ∀ v : Rd d, ‖v‖ = t * R →
        ((k : ℝ) + 1) * sNorm ξ Q (h ω) R 0 < (D (h ω)).1 (0, v)} <
          ENNReal.ofReal (δ k) := by
    intro k
    obtain ⟨t, _, ht, hbound⟩ := proper_exists_high_sphere
      (show 2 ≤ d by omega) hξ hQ0 hD P h hh ((k : ℝ) + 1) (δ k) (hδ k) 0
    exact ⟨t, ht, hbound⟩
  let t : ℕ → ℝ := fun k => (hchoice k).choose
  let Bad : ℕ → Set Ω := fun k =>
    {ω | ¬ ∀ v : Rd d, ‖v‖ = t k →
      ((k : ℝ) + 1) * sNorm ξ Q (h ω) 1 0 < (D (h ω)).1 (0, v)}
  have hbad : ∀ k, P (Bad k) ≤ (1 / 2 : ℝ≥0∞) ^ k := by
    intro k
    have hbound := (hchoice k).choose_spec.2 1 one_pos
    have heq : P (Bad k) =
        P {ω | ¬ ∀ v : Rd d, ‖v‖ = t k * 1 →
          ((k : ℝ) + 1) * sNorm ξ Q (h ω) 1 0 < (D (h ω)).1 (0, v)} := by
      simp only [Bad, mul_one]
    rw [heq]
    have hreal : ENNReal.ofReal (δ k) = (1 / 2 : ℝ≥0∞) ^ k := by
      change ENNReal.ofReal (((1 : ℝ) / 2) ^ k) = (1 / 2 : ℝ≥0∞) ^ k
      rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (1 : ℝ) / 2)]
      congr 1
      norm_num [ENNReal.ofReal_div_of_pos]
    exact (hbound.le).trans_eq hreal
  have hsum : (∑' k, P (Bad k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbad)
    rw [ENNReal.tsum_geometric]
    norm_num
  have hae := ae_eventually_notMem hsum
  have hlen := hD.length P h hh.isLGFPlusCont
  filter_upwards [hae, hlen] with ω hω hL
  apply properSpace_of_sphere_growth (D (h ω)) hL
  intro M
  have hc : 0 < sNorm ξ Q (h ω) 1 0 := proper_sNorm_pos ξ Q (h ω) one_pos
  have hshift : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hdiverge : Tendsto (fun k : ℕ => ((k : ℝ) + 1) * sNorm ξ Q (h ω) 1 0)
      atTop atTop := Filter.Tendsto.atTop_mul_const hc hshift
  have hlarge : ∀ᶠ k : ℕ in atTop,
      M < ((k : ℝ) + 1) * sNorm ξ Q (h ω) 1 0 :=
    hdiverge.eventually_gt_atTop M
  obtain ⟨k, hkbad, hklarge⟩ := (hω.and hlarge).exists
  have htk : 0 < t k := (hchoice k).choose_spec.1
  refine ⟨t k, htk, fun v hv => ?_⟩
  have hgood : ((k : ℝ) + 1) * sNorm ξ Q (h ω) 1 0 <
      (D (h ω)).1 (0, v) := by
    have := hkbad
    simp only [Bad, Set.mem_ofPred_eq, not_not] at this
    exact this v hv
  exact hklarge.trans hgood

/-- A sharp weak metric is almost surely geodesic for every pair of points. -/
theorem lemma27_geodesic (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ)
    (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, ∀ x y : Rd d, ∃ (γ : ℝ → Rd d) (T : ℝ),
      γ 0 = x ∧ γ T = y ∧ IsGeodesicCurve ((D (h ω)).pt ∘ γ) 0 T := by
  filter_upwards [lemma27_proper hd hξ hQ hD P h hh,
    hD.length P h hh.isLGFPlusCont] with ω hproper hL x y
  obtain ⟨γ, hγ⟩ := @ContMetric.exists_geodesic d (D (h ω)) hL hproper x y
  exact ⟨γ, _, hγ.1, hγ.2.1, hγ.2.2.1⟩

end HigherDimLQGMetric

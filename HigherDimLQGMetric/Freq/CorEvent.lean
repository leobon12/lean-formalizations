import HigherDimLQGMetric.Freq.Package

/-! # Ratio events used to derive Corollary 5.5 from optimality -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric MeasureTheory
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Any violating pair in a fixed ball satisfies the normalized bounds for
some reciprocal integer threshold. -/
theorem s4c_ratio_pair_in_GEvent
    {ξ Q u R : ℝ} (hR : 0 < R) {A B : DistRd d → ContMetric d}
    {g : DistRd d} {x y : Rd d}
    (hx : x ∈ closedBall (0 : Rd d) (2 * R))
    (hy : y ∈ closedBall (0 : Rd d) (2 * R))
    (hxy : u * (A g).1 (x, y) < (B g).1 (x, y)) :
    ∃ m : ℕ, g ∈ GEvent A B ξ Q u (1 / (m + 1 : ℝ)) R := by
  have hne : x ≠ y := by
    intro he
    subst y
    simp [ContMetric.apply_self] at hxy
  have hdist : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hA : 0 < (A g).1 (x, y) := (A g).apply_pos hne
  have hs : 0 < sNorm ξ Q g R 0 := sNorm_pos ξ Q g hR 0
  let c : ℝ := min (‖x - y‖ / R)
    (min ((A g).1 (x, y) / sNorm ξ Q g R 0)
      (sNorm ξ Q g R 0 / (A g).1 (x, y)))
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hc
  let β : ℝ := 1 / (m + 1 : ℝ)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβdist : β * R ≤ ‖x - y‖ := by
    have hle : β < ‖x - y‖ / R := lt_of_lt_of_le hm (min_le_left _ _)
    exact (lt_div_iff₀ hR).mp hle |>.le
  have hβA : β * sNorm ξ Q g R 0 ≤ (A g).1 (x, y) := by
    have hle : β < (A g).1 (x, y) / sNorm ξ Q g R 0 :=
      lt_of_lt_of_le hm (le_trans (min_le_right _ _) (min_le_left _ _))
    exact (lt_div_iff₀ hs).mp hle |>.le
  have hAupper : (A g).1 (x, y) ≤ β⁻¹ * sNorm ξ Q g R 0 := by
    have hle : β < sNorm ξ Q g R 0 / (A g).1 (x, y) :=
      lt_of_lt_of_le hm (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmul : β * (A g).1 (x, y) < sNorm ξ Q g R 0 :=
      (lt_div_iff₀ hA).mp hle
    have hquot : (A g).1 (x, y) < sNorm ξ Q g R 0 / β := by
      apply (lt_div_iff₀ hβ).mpr
      nlinarith only [hmul]
    simpa [div_eq_mul_inv, mul_comm] using hquot.le
  exact ⟨m, x, hx, y, hy, hβdist, hβA, hAupper, hxy⟩

/-- Lowering the threshold preserves the ratio event. -/
theorem s4c_GEvent_mono_beta {ξ Q u R : ℝ} (hR : 0 < R)
    {A B : DistRd d → ContMetric d} {β β' : ℝ}
    (hβ : 0 < β) (hle : β ≤ β') :
    GEvent A B ξ Q u β' R ⊆ GEvent A B ξ Q u β R := by
  rintro g ⟨x, hx, y, hy, hdist, hAlo, hAhi, hratio⟩
  have hs : 0 ≤ sNorm ξ Q g R 0 := (sNorm_pos ξ Q g hR 0).le
  refine ⟨x, hx, y, hy, ?_, ?_, ?_, hratio⟩
  · exact (mul_le_mul_of_nonneg_right hle hR.le).trans hdist
  · exact (mul_le_mul_of_nonneg_right hle hs).trans hAlo
  · exact hAhi.trans (mul_le_mul_of_nonneg_right
      (inv_anti₀ hβ hle) hs)

/-- A positive event at a fixed radius contains a normalized ratio event
whose beta is also a lower bound on its probability. -/
theorem s4c_GEvent_probability_beta
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) {ξ Q u R β' : ℝ} (hR : 0 < R)
    (hβ' : 0 < β') {A B : DistRd d → ContMetric d}
    (hpos : 0 < P (h ⁻¹' GEvent A B ξ Q u β' R)) :
    ∃ β : ℝ, 0 < β ∧
      ENNReal.ofReal β ≤ P (h ⁻¹' GEvent A B ξ Q u β R) := by
  let M := P (h ⁻¹' GEvent A B ξ Q u β' R)
  have hMtop : M ≠ ⊤ := ne_top_of_le_ne_top
    (by simp : P Set.univ ≠ ⊤) (measure_mono (Set.subset_univ _))
  have hMreal : 0 < M.toReal := ENNReal.toReal_pos hpos.ne' hMtop
  let β := min β' (M.toReal / 2)
  have hβ : 0 < β := lt_min hβ' (by positivity)
  have hβ'le : β ≤ β' := min_le_left _ _
  have hβM : ENNReal.ofReal β ≤ M := by
    apply (ENNReal.ofReal_le_iff_le_toReal hMtop).mpr
    exact (min_le_right _ _).trans (by linarith only [hMreal])
  refine ⟨β, hβ, hβM.trans ?_⟩
  exact measure_mono (Set.preimage_mono (s4c_GEvent_mono_beta hR hβ hβ'le))

/-- A positive ratio violation at any two points belongs to some ratio
event with integer radius and reciprocal integer beta. -/
theorem s4c_ratio_violation_cover
    {ξ Q u : ℝ} {A B : DistRd d → ContMetric d} {g : DistRd d}
    {x y : Rd d}
    (hxy : u * (A g).1 (x, y) < (B g).1 (x, y)) :
    ∃ n m : ℕ, g ∈ GEvent A B ξ Q u (1 / (m + 1 : ℝ)) (n + 1 : ℝ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ ‖y‖)
  have hR : 0 < (n + 1 : ℝ) := by positivity
  have hx : x ∈ closedBall (0 : Rd d) (2 * (n + 1 : ℝ)) := by
    rw [mem_closedBall, dist_zero_right]
    have hxn : ‖x‖ < (n : ℝ) := (le_max_left _ _).trans_lt (by exact_mod_cast hn)
    linarith
  have hy : y ∈ closedBall (0 : Rd d) (2 * (n + 1 : ℝ)) := by
    rw [mem_closedBall, dist_zero_right]
    have hyn : ‖y‖ < (n : ℝ) := (le_max_right _ _).trans_lt (by exact_mod_cast hn)
    linarith
  obtain ⟨m, hm⟩ := s4c_ratio_pair_in_GEvent hR hx hy hxy
  exact ⟨n, m, hm⟩

/-- Failure of an almost-sure upper ratio yields a positive normalized
ratio event at a deterministic radius. -/
theorem s4c_optimal_G_positive
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) {ξ Q u : ℝ} {A B : DistRd d → ContMetric d}
    (hopt : ¬ ∀ᵐ ω ∂P, ∀ x y : Rd d,
      (B (h ω)).1 (x, y) ≤ u * (A (h ω)).1 (x, y)) :
    ∃ n m : ℕ,
      0 < P (h ⁻¹' GEvent A B ξ Q u (1 / (m + 1 : ℝ)) (n + 1 : ℝ)) := by
  let W : Set Ω := {ω | ∃ x y : Rd d,
    u * (A (h ω)).1 (x, y) < (B (h ω)).1 (x, y)}
  have hW : 0 < P W := by
    apply pos_iff_ne_zero.mpr
    intro hz
    apply hopt
    change {ω | ∀ x y : Rd d,
      (B (h ω)).1 (x, y) ≤ u * (A (h ω)).1 (x, y)} ∈ ae P
    rw [mem_ae_iff]
    simpa only [Set.compl_ofPred, not_forall, not_le, W] using hz
  have hcover : W ⊆ ⋃ n : ℕ, ⋃ m : ℕ,
      h ⁻¹' GEvent A B ξ Q u (1 / (m + 1 : ℝ)) (n + 1 : ℝ) := by
    intro ω hω
    obtain ⟨x, y, hxy⟩ := hω
    obtain ⟨n, m, hm⟩ := s4c_ratio_violation_cover hxy
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨m, hm⟩⟩
  have hbig : P (⋃ n : ℕ, ⋃ m : ℕ,
      h ⁻¹' GEvent A B ξ Q u (1 / (m + 1 : ℝ)) (n + 1 : ℝ)) ≠ 0 :=
    (lt_of_lt_of_le hW (measure_mono hcover)).ne'
  obtain ⟨n, hn⟩ := exists_measure_pos_of_not_measure_iUnion_null hbig
  obtain ⟨m, hm⟩ := exists_measure_pos_of_not_measure_iUnion_null hn.ne'
  exact ⟨n, m, hm⟩

/-- A positive ratio event at radius `R₀` gives a positive ratio event at
each larger radius, with a possibly smaller beta. -/
theorem s4c_GEvent_positive_larger
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) {ξ Q u β₀ R₀ R₁ : ℝ}
    {A B : DistRd d → ContMetric d} (hR₀ : 0 < R₀)
    (hR : R₀ ≤ R₁)
    (hpos : 0 < P (h ⁻¹' GEvent A B ξ Q u β₀ R₀)) :
    ∃ m : ℕ, 0 < P (h ⁻¹' GEvent A B ξ Q u (1 / (m + 1 : ℝ)) R₁) := by
  have hR₁ : 0 < R₁ := hR₀.trans_le hR
  have hcover : h ⁻¹' GEvent A B ξ Q u β₀ R₀ ⊆
      ⋃ m : ℕ, h ⁻¹' GEvent A B ξ Q u (1 / (m + 1 : ℝ)) R₁ := by
    intro ω hω
    obtain ⟨x, hx, y, hy, _, _, _, hxy⟩ := hω
    have hx' : x ∈ closedBall (0 : Rd d) (2 * R₁) :=
      closedBall_subset_closedBall (by linarith only [hR]) hx
    have hy' : y ∈ closedBall (0 : Rd d) (2 * R₁) :=
      closedBall_subset_closedBall (by linarith only [hR]) hy
    obtain ⟨m, hm⟩ := s4c_ratio_pair_in_GEvent hR₁ hx' hy' hxy
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  have hbig : P (⋃ m : ℕ,
      h ⁻¹' GEvent A B ξ Q u (1 / (m + 1 : ℝ)) R₁) ≠ 0 :=
    (lt_of_lt_of_le hpos (measure_mono hcover)).ne'
  exact exists_measure_pos_of_not_measure_iUnion_null hbig

end HigherDimLQGMetric

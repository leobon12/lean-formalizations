import HigherDimLQGMetric.DGZ.Interfaces
import HigherDimLQGMetric.DGZ.AcrossAroundTools
import HigherDimLQGMetric.DGZ.FunctionalsMeas
import HigherDimLFPP.Exist.Quantile
import HigherDimLFPP.Exist.Scaling
import HigherDimLFPP.Field.Symmetry
import HigherDimLFPP.Field.BandFacts
import HigherDimLFPP.Field.SupBounds

/-!
# Basic facts for the real-scale DGZ adapter

The whole-space median is positive for a continuous band version.  A rescaled
real band splits pointwise into a dyadic band and a continuous upper band.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : WN d → Ω → ℝ} {κ : Rd d → ℝ}

/-- Every real cutoff in `(0,1]` lies in a unique dyadic scale interval.  The ratio `s` is
allowed to equal `1`; this is the empty-upper-band case. -/
theorem adapter_exists_dyadic_scale {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N : ℕ, ∃ s : ℝ, (1 / 2 : ℝ) < s ∧ s ≤ 1 ∧
      ε = ((2 : ℝ)⁻¹ ^ N) * s := by
  obtain ⟨N, hlow, hupp⟩ := exists_nat_pow_near_of_lt_one hε hε1
    (by norm_num : (0 : ℝ) < (1 / 2)) (by norm_num : (1 / 2 : ℝ) < 1)
  let a : ℝ := (2 : ℝ)⁻¹ ^ N
  have ha : 0 < a := by dsimp [a]; positivity
  have heq : (1 / 2 : ℝ) ^ N = a := by simp [a]
  rw [heq] at hupp
  have hlow' : a / 2 < ε := by
    rw [pow_succ, heq] at hlow
    norm_num at hlow
    nlinarith
  refine ⟨N, ε / a, ?_, ?_, ?_⟩
  · exact (lt_div_iff₀ ha).2 (by linarith)
  · exact (div_le_iff₀ ha).2 (by simpa only [one_mul] using hupp)
  · exact (mul_div_cancel₀ ε ha.ne').symm

/-- A cutoff below `2^{-N₀}` has dyadic index at least `N₀`. -/
theorem adapter_index_ge_of_eps_lt {ε s : ℝ} {N N₀ : ℕ}
    (hs : 1 / 2 < s) (hεeq : ε = ((2 : ℝ)⁻¹ ^ N) * s)
    (hε : ε < ((2 : ℝ)⁻¹ ^ N₀)) : N₀ ≤ N := by
  by_contra hN
  have hNN : N + 1 ≤ N₀ := by omega
  have hpow : ((2 : ℝ)⁻¹ ^ N₀) ≤ (2 : ℝ)⁻¹ ^ (N + 1) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2⁻¹ : ℝ) ≤ 1) hNN
  have hstrict : ((2 : ℝ)⁻¹ ^ (N + 1)) < ε := by
    rw [hεeq, pow_succ]
    have ha : 0 < (2 : ℝ)⁻¹ ^ N := by positivity
    nlinarith
  linarith

/-- A box has a fixed-width open box neighbourhood, as required by `HolderTightShape`. -/
theorem adapter_closure_obox_subset {c : Rd d} {R S : ℝ} (hRS : R < S) :
    closure (HigherDimLFPP.DGZ.obox c R) ⊆ HigherDimLFPP.DGZ.obox c S := by
  exact (closure_minimal (HigherDimLFPP.DGZ.obox_subset_cbox c R)
    (HigherDimLFPP.DGZ.isClosed_cbox c R)).trans (cbox_subset_obox hRS)

/-- Euclidean closed balls fit in `ℓ^∞` boxes with any larger radius. -/
theorem adapter_closedBall_subset_obox {c : Rd d} {R S : ℝ} (hRS : R < S) :
    Metric.closedBall c R ⊆ HigherDimLFPP.DGZ.obox c S := by
  intro z hz i
  have hnorm : ‖z - c‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  exact (HigherDimLFPP.DGZ.abs_apply_le_norm (z - c) i).trans_lt (hnorm.trans_lt hRS)

/-- The lower median of a whole-space LFPP distance is positive. -/
theorem aHat_pos (hd : 0 < d) (hW : IsWhiteNoise P W)
    {ε : ℝ} {G : ℝ → Rd d → Ω → ℝ} (hG : IsBandVersion P W κ ε 1 (G ε)) (ξ : ℝ) :
    0 < aHat P G ξ ε := by
  have hP := hW.isProbabilityMeasure
  have hm : Measurable (fun ω => lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d)) :=
    measurable_lfppMetric hG.continuous hG.measurable ξ 0 (e₁ d)
  have hpos : ∀ ω, 0 < lfppMetric ξ (fun z => G ε z ω) 0 (e₁ d) := by
    intro ω
    exact lfppMetric_pos (hG.continuous ω) (e₁_ne_zero hd).symm
  exact HigherDimLFPP.Conc.lowerQuantile_map_pos hm.aemeasurable
    (ae_of_all _ hpos) (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)

/-- Subtracting a lower band from a version with the same lower cutoff gives a version of the
remaining upper band. The equality of fields is pointwise, by the definition of the difference. -/
theorem adapter_sub_band (hW : IsWhiteNoise P W) (hκ : IsLFPPKernel κ)
    {a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (h1b : 1 ≤ b)
    {X Y : Rd d → Ω → ℝ} (hX : IsBandVersion P W κ a b X)
    (hY : IsBandVersion P W κ a 1 Y) :
    IsBandVersion P W κ 1 b (fun z ω => X z ω - Y z ω) where
  continuous ω := (hX.continuous ω).sub (hY.continuous ω)
  measurable z := (hX.measurable z).sub (hY.measurable z)
  ae_eq z := by
    filter_upwards [hX.ae_eq z, hY.ae_eq z,
      hW.bandVec_add_ae hκ ha ha1 h1b z] with ω hXω hYω hadd
    rw [hXω, hYω, hadd]
    ring

/-- A real cutoff, after rescaling by `s`, is a dyadic cutoff plus a unit-scale band.
The equality in the conclusion holds at every point and every sample. -/
theorem adapter_realScale_coupling (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise P W)
    {G : ℝ → Rd d → Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hG : IsBandVersion P W κ ε 1 (G ε)) (N : ℕ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hεeq : ε = ((2 : ℝ)⁻¹ ^ N) * s) :
    ∃ H : ℕ → Rd d → Ω → ℝ,
      IsDyadicRealization κ P
        (fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hs f)) H ∧
      ∃ B : Rd d → Ω → ℝ,
        IsBandVersion P
          (fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hs f))
          κ 1 (1 / s) B ∧
        ∀ z ω, G ε (s • z) ω = H N z ω + B z ω := by
  let W' : WN d → Ω → ℝ :=
    fun f => W (simL2 (LinearIsometryEquiv.refl ℝ (Rd d)) 0 hs f)
  have hW' : IsWhiteNoise P W' := hW.comp_simL2 _ 0 hs
  obtain ⟨H, hH⟩ := exists_isDyadicRealization hκ hW'
  have hscale : IsBandVersion P W' κ ((2 : ℝ)⁻¹ ^ N) (1 / s)
      (fun z ω => G ε (s • z) ω) := by
    have h := hG.comp_smul hκ hs hε
    refine h.congr_band ?_ ?_
    · rw [hεeq]
      exact mul_div_cancel_right₀ _ hs.ne'
    · ring
  let B : Rd d → Ω → ℝ := fun z ω => G ε (s • z) ω - H N z ω
  have hB : IsBandVersion P W' κ 1 (1 / s) B :=
    adapter_sub_band hW' hκ (by positivity)
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2⁻¹ : ℝ) ≤ 1))
      (by exact (one_le_div hs).2 hs1) hscale (hH.band N)
  refine ⟨H, hH, B, hB, ?_⟩
  intro z ω
  simp only [B]
  ring

/-- A bounded-ratio upper band has a uniformly tight supremum on each fixed box.  This also
includes `b = 1`, when the band is empty. -/
theorem adapter_exists_upperBand_sup_bound (hd : 0 < d) (hκ : IsLFPPKernel κ)
    {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 < θ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ},
        IsWhiteNoise P W → ∀ {b : ℝ}, 1 ≤ b → b ≤ 2 →
        ∀ {B : Rd d → Ω → ℝ}, IsBandVersion P W κ 1 b B →
          P {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) R, L < |B z ω|} ≤
            ENNReal.ofReal θ := by
  have hdz : NeZero d := ⟨hd.ne'⟩
  obtain ⟨L₀, hL₀, htail⟩ := @HigherDimLFPP.exists_bandSup_bounds d hdz κ hκ
  let V : ℝ := Real.log 2
  have hV : 0 < V := Real.log_pos one_lt_two
  let M : ℝ := HigherDimLFPP.SupB.supMean d L₀ V (d * Real.log (2 * R + 1))
  let u : ℝ := 2 * Real.sqrt (V / θ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hu2 : u ^ 2 = 4 * (V / θ) := by
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have htailθ : 2 * Real.exp (-u ^ 2 / (2 * V)) ≤ θ := by
    have hx : 0 < u ^ 2 / (2 * V) := by rw [hu2]; positivity
    have he : Real.exp (-(u ^ 2 / (2 * V))) ≤ 1 / (u ^ 2 / (2 * V)) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le hx (by linarith [Real.add_one_le_exp (u ^ 2 / (2 * V))])
    calc
      2 * Real.exp (-u ^ 2 / (2 * V)) ≤ 2 * (1 / (u ^ 2 / (2 * V))) := by
        simpa only [neg_div] using mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 2)
      _ = θ := by rw [hu2]; field_simp; ring
  refine ⟨max 0 (M + u), le_max_left _ _, ?_⟩
  intro Ω _ P W hW b hb1 hb2 B hB
  have hbV : Real.log (b / 1) ≤ V := by
    simpa only [div_one, V] using Real.log_le_log (by linarith) hb2
  have h := (htail hW one_pos hb1 hB hV hbV 0 hR).2.2.2 hu
  have hsub : {ω | ∃ z ∈ HigherDimLFPP.DGZ.cbox (0 : Rd d) R,
      max 0 (M + u) < |B z ω|} ⊆
      {ω | ∃ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) R,
        HigherDimLFPP.SupB.supMean d L₀ V (d * Real.log (2 * R / 1 + 1)) + u < |B z ω|} := by
    rintro ω ⟨z, hz, hzB⟩
    exact ⟨z, hz, lt_of_le_of_lt (by simpa only [M, div_one] using le_max_right 0 (M + u)) hzB⟩
  exact (measure_mono hsub).trans (h.trans (ENNReal.ofReal_le_ofReal htailθ))

/-- The median is below a threshold whose lower tail has probability at least one half. -/
theorem adapter_lowerMedian_le_of_half_le {X : Ω → ℝ} (hX : AEMeasurable X P) [IsProbabilityMeasure P]
    {t : ℝ} (ht : (2⁻¹ : ℝ≥0∞) ≤ P {ω | X ω ≤ t}) :
    LQGMetric.lowerQuantile (P.map X) 2⁻¹ ≤ t := by
  apply (LQGMetric.le_measure_Iic_iff_lowerQuantile_le
    (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).1
  rwa [Measure.map_apply_of_aemeasurable hX measurableSet_Iic]

/-- The median is above a threshold whose lower tail has probability below one half. -/
theorem adapter_lt_lowerMedian_of_measure_lt {X : Ω → ℝ} (hX : AEMeasurable X P)
    [IsProbabilityMeasure P] {t : ℝ} (ht : P {ω | X ω ≤ t} < (2⁻¹ : ℝ≥0∞)) :
    t < LQGMetric.lowerQuantile (P.map X) 2⁻¹ := by
  by_contra hnot
  have hle : LQGMetric.lowerQuantile (P.map X) 2⁻¹ ≤ t := le_of_not_gt hnot
  have h := (LQGMetric.le_measure_Iic_iff_lowerQuantile_le
    (μ := P.map X) (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)).2 hle
  rw [Measure.map_apply_of_aemeasurable hX measurableSet_Iic] at h
  exact (not_le_of_gt ht) h

/-- A complementary event of outer probability at most one quarter leaves at least half the
probability on the original event. No measurability of the event is required. -/
theorem adapter_half_le_measure_of_compl_le [IsProbabilityMeasure P] {A : Set Ω}
    (hA : P Aᶜ ≤ (4⁻¹ : ℝ≥0∞)) : (2⁻¹ : ℝ≥0∞) ≤ P A := by
  have hA' : P Aᶜ ≤ (2⁻¹ : ℝ≥0∞) :=
    hA.trans (by norm_num : (4⁻¹ : ℝ≥0∞) ≤ 2⁻¹)
  have hcover : (1 : ℝ≥0∞) ≤ P A + P Aᶜ := by
    rw [← measure_univ (μ := P)]
    exact (measure_mono (by simp : (Set.univ : Set Ω) ⊆ A ∪ Aᶜ)).trans
      (measure_union_le A Aᶜ)
  have hsum : (1 : ℝ≥0∞) ≤ P A + 2⁻¹ := hcover.trans (add_le_add le_rfl hA')
  have hdiff : (1 : ℝ≥0∞) - 2⁻¹ ≤ P A := (tsub_le_iff_right).2 hsum
  simpa only [ENNReal.one_sub_inv_two] using hdiff

end HigherDimLQGMetric.DGZ

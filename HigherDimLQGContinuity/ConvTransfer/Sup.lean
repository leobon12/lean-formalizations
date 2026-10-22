import HigherDimLQGContinuity.ConvTransfer.Tail
import HigherDimLFPP.Field.SupBounds

/-!
# Gaussian supremum estimate for the infrared correction

The finite-family argument specializes the existing Gaussian grid theorem to a
white-noise process whose variance grows logarithmically with the observation
radius and whose increments are Lipschitz at unit scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Real
open scoped RealInnerProductSpace

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd WN)

/-- Finite-family expected maximum of a Gaussian field with prescribed point
variance and unit-scale quadratic increment bound. -/
theorem convEnv_integral_iSup_finset_le {d : ℕ} [NeZero d]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} (hW : HigherDimLFPP.IsWhiteNoise P W)
    (u : Rd d → WN d) (I : Rd d → Ω → ℝ)
    (hI : ∀ z, I z =ᵐ[P] W (u z))
    {L V R : ℝ} (hL : 0 < L) (hV : 0 < V)
    (hvar : ∀ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) R, ‖u z‖ ^ 2 ≤ V)
    (hinc : ∀ z w : Rd d, ‖u z - u w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2)
    (hR : 0 ≤ R) {s : ℝ} (hs : s * s = 1)
    (F : Finset (Rd d))
    (hF : ∀ z ∈ F, z ∈ HigherDimLFPP.Osc.box (0 : Rd d) R)
    (hGF : HigherDimLFPP.Osc.grid (0 : Rd d) R 1 ⊆ F) :
    ∫ ω, (⨆ z : F, s * I z ω) ∂P ≤
      HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R + 1)) := by
  classical
  let k : Rd d → WN d := u
  have hval : ∫ ω, (⨆ z : F, s * I z ω) ∂P =
      LQGDimension.gaussianExpectedMax F (fun z w => ⟪k z, k w⟫) 0 := by
    have h := hW.integral_iSup_eq_gaussianExpectedMax F (fun z => s • k z) 0
    have hae : ∀ᵐ ω ∂P, ∀ z : F, s * I z ω = W (s • k z) ω + (0 : Rd d → ℝ) z := by
      refine ae_all_iff.2 fun z => ?_
      filter_upwards [hW.smul_ae s (k z), hI z] with ω h1 h2
      rw [h1, h2, Pi.zero_apply, add_zero]
    have hC : (fun z w : Rd d => ⟪s • k z, s • k w⟫) =
        fun z w => ⟪k z, k w⟫ := by
      funext z w
      rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, hs, one_mul]
    rw [hC] at h
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    simp only [hω]
  obtain ⟨v, hv, hEq⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F
    (fun z w => ⟪k z, k w⟫) (LQGDimension.posSemidef_gramOn F k)
  rw [hval, hEq]
  let G := HigherDimLFPP.Osc.grid (0 : Rd d) R 1
  have hG : G.Nonempty := Finset.card_pos.1
    (HigherDimLFPP.Osc.one_le_card_grid (0 : Rd d) R 1)
  have hgr : ∀ z ∈ F, HigherDimLFPP.Osc.gridOf 0 R 1 z ∈ G ∧
      ‖z - HigherDimLFPP.Osc.gridOf 0 R 1 z‖ ≤ √(d : ℝ) * 1 :=
    fun z hz => ⟨HigherDimLFPP.Osc.gridOf_mem_grid 0 one_pos (hF z hz),
      HigherDimLFPP.Osc.norm_sub_gridOf_le 0 one_pos (hF z hz)⟩
  have hv' : ∀ g ∈ G, ‖v g‖ ^ 2 ≤ V := by
    intro g hg
    rw [← real_inner_self_eq_norm_sq, hv g (hGF hg) g (hGF hg),
      real_inner_self_eq_norm_sq]
    exact hvar g (hF g (hGF hg))
  have hinc' : ∀ z ∈ F, ∀ w ∈ F,
      ‖v z - v w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / 1 ^ 2 := by
    intro z hz w hw
    have e : ‖v z - v w‖ ^ 2 = ‖k z - k w‖ ^ 2 := by
      rw [norm_sub_sq_real, norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (k z),
        ← real_inner_self_eq_norm_sq (k w), hv z hz z hz, hv z hz w hw, hv w hw w hw]
    simpa only [one_pow, div_one, k] using e.le.trans (hinc z w)
  have hlogN : Real.log G.card ≤ d * Real.log (2 * R + 1) := by
    simpa only [div_one] using HigherDimLFPP.SupB.log_card_grid_le
      (0 : Rd d) hR one_pos
  have hlog0 : 0 ≤ Real.log G.card := Real.log_nonneg
    (by exact_mod_cast hG.card_pos)
  let ℓ : ℝ := d * Real.log (2 * R + 1)
  set lam : ℝ := √(1 + ℓ) with hlam
  have hℓ0 : 0 ≤ ℓ := by
    dsimp [ℓ]
    exact mul_nonneg (Nat.cast_nonneg d) (Real.log_nonneg (by linarith))
  have hlam0 : 0 < lam := Real.sqrt_pos.2 (by linarith)
  have hlam2 : lam ^ 2 = 1 + ℓ := Real.sq_sqrt (by linarith)
  have hN : Real.log G.card ≤ lam ^ 2 := by rw [hlam2]; dsimp [ℓ]; linarith
  set c₁ : ℝ := V / 2 with hc₁
  set c₂ : ℝ := π ^ 2 * (√(d : ℝ) ^ 2 * L) / 8 with hc₂
  have hc₁0 : 0 < c₁ := by positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  have hc₂0 : 0 < c₂ := by positivity
  have hmain := HigherDimLFPP.SupB.vecExpectedMax_le_grid hGF hG
    (HigherDimLFPP.Osc.gridOf 0 R 1) one_pos (Real.sqrt_nonneg _)
    hL.le hgr v hv' hinc'
    (l₁ := lam / √c₁) (l₂ := lam / √c₂) (by positivity) (by positivity)
  have h1 := HigherDimLFPP.SupB.softmax_opt hc₁0 hlam0 hN
  have h2 := HigherDimLFPP.SupB.softmax_opt hc₂0 hlam0 hN
  refine hmain.trans ?_
  unfold HigherDimLFPP.SupB.supMean
  rw [← hlam, ← hc₁, ← hc₂]
  linarith

/-- Borell's tail bound with a variance bound only on the observation box. -/
theorem convEnv_vecSup_tail {d : ℕ} [NeZero d] {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {W : WN d → Ω → ℝ}
    (hW : HigherDimLFPP.IsWhiteNoise P W) (v : Rd d → WN d)
    {L V : ℝ} (hL : 0 < L) (hV : 0 < V)
    (hvL : ∀ z w, ‖v z - v w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2)
    {X : Rd d → Ω → ℝ} (hXc : ∀ ω, Continuous fun z => X z ω)
    (hX : ∀ z, X z =ᵐ[P] W (v z))
    {R : ℝ} (hR : 0 ≤ R)
    (hvV : ∀ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) R, ‖v z‖ ^ 2 ≤ V)
    {u : ℝ} (hu : 0 ≤ u) :
    Integrable (fun ω => ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) R, |X z ω|) P ∧
    P {ω | HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R + 1)) + u ≤
        ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) R, |X z ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) := by
  classical
  have := hW.isProbabilityMeasure
  let B : Set (Rd d) := HigherDimLFPP.Osc.box 0 R
  have : CompactSpace B := isCompact_iff_compactSpace.1
    (HigherDimLFPP.Osc.isCompact_box 0 R)
  have hzero : (0 : Rd d) ∈ B := fun i => by simpa only [sub_self, abs_zero] using hR
  have : Nonempty B := ⟨⟨0, hzero⟩⟩
  let M := HigherDimLFPP.SupB.supMean d L V (d * Real.log (2 * R + 1))
  have hXi : ∀ z, Integrable (X z) P := fun z => by
    have hm : MemLp (X z) 2 P :=
      (hW.memLp (v z) 2 ENNReal.ofNat_ne_top).ae_eq (hX z).symm
    exact hm.integrable one_le_two
  have hfin : ∀ s : ℝ, s * s = 1 → ∀ (n : ℕ) (t : Fin (n + 1) → B),
      ∫ ω, (⨆ i, s * X (t i) ω) ∂P ≤ M := by
    intro s hs n t
    let F : Finset (Rd d) := (Finset.univ.image fun i => (t i : Rd d)) ∪
      HigherDimLFPP.Osc.grid 0 R 1
    have hFB : ∀ z ∈ F, z ∈ B := by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
        exact (t i).2
      · exact HigherDimLFPP.Osc.grid_subset_box 0 hR one_pos hz
    have hGF : HigherDimLFPP.Osc.grid 0 R 1 ⊆ F := Finset.subset_union_right
    have : Nonempty F := ⟨⟨t 0, Finset.mem_union_left _
      (Finset.mem_image_of_mem _ (Finset.mem_univ 0))⟩⟩
    have hint1 : Integrable (fun ω => ⨆ i, s * X (t i) ω) P :=
      HigherDimLFPP.SupB.integrable_iSup_of_finite fun i => (hXi _).const_mul s
    have hint2 : Integrable (fun ω => ⨆ z : F, s * X z ω) P :=
      HigherDimLFPP.SupB.integrable_iSup_of_finite fun z => (hXi _).const_mul s
    have hpt : ∀ ω, (⨆ i, s * X (t i) ω) ≤ ⨆ z : F, s * X z ω := fun ω =>
      ciSup_le fun i => le_ciSup (f := fun z : F => s * X z ω) (Finite.bddAbove_range _)
        ⟨t i, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩
    exact (integral_mono hint1 hint2 hpt).trans
      (convEnv_integral_iSup_finset_le hW v X hX hL hV hvV hvL hR hs F hFB hGF)
  let Y : B → Ω → ℝ := fun z ω => X z ω
  have hYg : IsGaussianProcess Y P :=
    ((hW.isGaussianProcess_comp v).congr fun z => (hX z).symm).comp_right Subtype.val
  have hY0 : ∀ z, ∫ ω, Y z ω ∂P = 0 := fun z => by
    rw [integral_congr_ae (hX z)]
    exact hW.integral_eq_zero _
  have hYc : ∀ ω, Continuous fun z => Y z ω := fun ω =>
    (hXc ω).comp continuous_subtype_val
  obtain ⟨hint, hMle⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hYg hYc
    (C := M) fun n t => by simpa only [one_mul] using hfin 1 (one_mul 1) n t
  obtain ⟨hint', hMle'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous
    (LQGMetric.SupTail.isGaussianProcess_neg hYg) (fun ω => (hYc ω).neg) (C := M)
    fun n t => by simpa only [neg_one_mul] using hfin (-1) (by norm_num) n t
  have habs : (fun ω => ⨆ z : B, |X z ω|) =
      fun ω => max (⨆ z : B, X z ω) (⨆ z : B, -X z ω) :=
    funext fun ω => HigherDimLFPP.SupB.iSup_abs_eq_max (f := fun z : B => X z ω) (hYc ω)
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact hint.sup hint'
  have hvar : ∀ z : B, Var[Y z; P] ≤ √V ^ 2 := fun z => by
    rw [Real.sq_sqrt hV.le, show Y z = X z from rfl,
      ((hW.hasLaw_single (v z)).congr (hX z)).variance_eq,
      variance_id_gaussianReal, Real.coe_toNNReal _ (sq_nonneg _)]
    exact hvV z z.2
  have htail := LQGMetric.SupTail.tail_iSup_abs_le hYg hY0 hYc hint hint'
    hMle hMle' hvar hu
  rw [Real.sq_sqrt hV.le] at htail
  calc P {ω | M + u ≤ ⨆ z : B, |X z ω|}
      = ENNReal.ofReal (P.real {ω | M + u ≤ ⨆ z : B, |X z ω|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-u ^ 2 / (2 * V))) :=
      ENNReal.ofReal_le_ofReal htail

/-- Gaussian tail for the centered infrared correction on a box. -/
theorem convEnv_infrared_box_tail {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) :
    ∃ L C : ℝ, 0 < L ∧ 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WN d → Ω → ℝ}, HigherDimLFPP.IsWhiteNoise P W →
      ∀ {I : Rd d → Ω → ℝ}, (∀ ω, Continuous fun x => I x ω) →
        (∀ x, I x =ᵐ[P] W (HigherDimLFPP.bandVecM κ (Ioi 1)
          (Measure.dirac x) (HigherDimLQGMetric.unitSphereProb d))) →
      ∀ {R : ℝ}, 1 ≤ R →
      Integrable (fun ω => ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) R, |I z ω|) P ∧
      ∀ {u : ℝ}, 0 ≤ u →
      P {ω | HigherDimLFPP.SupB.supMean d L (C * (1 + Real.log (√(d : ℝ) * R)))
        (d * Real.log (2 * R + 1)) + u ≤
          ⨆ z : HigherDimLFPP.Osc.box (0 : Rd d) R, |I z ω|} ≤
      ENNReal.ofReal (2 * Real.exp
        (-u ^ 2 / (2 * (C * (1 + Real.log (√(d : ℝ) * R)))))) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨L, hLp, hinc⟩ := convEnv_infrared_incr_le hd hκ
  obtain ⟨C₀, hC₀, hvar⟩ := convEnv_infrared_var_le_log hd hκ
  let C : ℝ := max 1 C₀
  have hCp : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨L, C, hLp, hCp, ?_⟩
  intro Ω _ P W hW I hIc hIeq R hR
  have hR0 : 0 ≤ R := by linarith
  let ρ : ℝ := √(d : ℝ) * R
  have hdge : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hroot : 1 ≤ √(d : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hdge
  have hρ : 1 ≤ ρ := by
    dsimp [ρ]
    nlinarith
  have hV : 0 < C * (1 + Real.log ρ) := by
    have hlog : 0 ≤ Real.log ρ := Real.log_nonneg hρ
    positivity
  have hloc : ∀ z ∈ HigherDimLFPP.Osc.box (0 : Rd d) R,
      ‖HigherDimLFPP.bandVecM κ (Ioi 1) (Measure.dirac z)
        (HigherDimLQGMetric.unitSphereProb d)‖ ^ 2 ≤
          C * (1 + Real.log ρ) := by
    intro z hz
    have hz' : z ∈ Metric.closedBall (0 : Rd d) ρ := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa only [sub_zero, ρ] using
        (HigherDimLFPP.Osc.norm_sub_le_of_mem_box hR0 hz)
    exact (hvar hρ z hz').trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith [Real.log_nonneg hρ]))
  have hmain (u : ℝ) (hu : 0 ≤ u) := convEnv_vecSup_tail hW
    (fun x => HigherDimLFPP.bandVecM κ (Ioi 1) (Measure.dirac x)
      (HigherDimLQGMetric.unitSphereProb d)) hLp hV hinc hIc hIeq hR0 hloc hu
  refine ⟨(hmain 0 le_rfl).1, ?_⟩
  intro u hu
  simpa only [ρ] using (hmain u hu).2

end HigherDimLQGContinuity

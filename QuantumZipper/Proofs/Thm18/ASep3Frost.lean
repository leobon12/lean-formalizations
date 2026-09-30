import QuantumZipper.Proofs.Thm18.ASep3Traj
import QuantumZipper.Proofs.Thm18.ASep3Dil
import QuantumZipper.Proofs.Zipper.UnifUC1Push
import QuantumZipper.Proofs.Zipper.UnifUCIdDet
import QuantumZipper.Proofs.Thm18.RTBeurMass

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP3 (step 3): Frostman and support bounds for the A-sep family at small radii

`frostman_muA0_small`: on a box of good parameters (`hgood0`, `hlow` as in `genFam_muA0`), there
is `ρ₀ > 0` such that for all `ρ ∈ [0, ρ₀]` the X-measure
`muA0 p ρ = (bindFc ν_p ρ).map f_τ⁻¹`, `ν_p = fc(d, r).map (w ↦ f_τ(a w))`, is `1/3`-Frostman and
supported in a fixed ball, uniformly in the box. These are the hypotheses of `genFam_dil`
(ASep3Dil.lean) for the small-radius part of the family.

Proof: `ν_p` is `1`-Frostman (`isFrostman_alphaA`), hence `1/3`-Frostman; `bindFc` keeps a
`1/3`-Frostman bound (`RegCont.isFrostman_bindFc`); `bindFc ν_p ρ` is carried by points of `ℍ`
within `2ρ ≤ (m/2) e^{-8T/m²}` of the good image points `f_τ(a w)`, where `f_τ⁻¹` is co-Lipschitz
(`norm_sub_le_fwdMapInv_sub`, ASep3Traj.lean), so the pushforward is Frostman
(`isFrostman_map_of_coLip`) and bounded (`norm_fwdMapInv_sub_le`). Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace ASep

open RegCont

/-- `1`-Frostman probability measures are `1/3`-Frostman. -/
theorem isFrostman_third_of_one {ν : Measure ℂ} [IsProbabilityMeasure ν] {C : ℝ}
    (hF : TwoPoint.IsFrostman ν 1 C) : TwoPoint.IsFrostman ν (1 / 3) (max C 1) := by
  intro w s hs
  have hle1 : (ν (closedBall w s)).toReal ≤ 1 := by
    have := prob_le_one (μ := ν) (s := closedBall w s)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
  rcases le_or_gt s 1 with h1 | h1
  · have hs3 : s ≤ s ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow_of_exponent_ge hs h1 (show (1 / 3 : ℝ) ≤ 1 by norm_num)
      simpa using this
    calc (ν (closedBall w s)).toReal ≤ C * s ^ (1 : ℝ) := hF w s hs
      _ ≤ max C 1 * s ^ (1 / 3 : ℝ) := by
          rw [Real.rpow_one]
          exact mul_le_mul (le_max_left _ _) hs3 hs.le (le_trans zero_le_one (le_max_right _ _))
  · have : 1 ≤ s ^ (1 / 3 : ℝ) := Real.one_le_rpow h1.le (by norm_num)
    calc (ν (closedBall w s)).toReal ≤ 1 := hle1
      _ ≤ max C 1 * s ^ (1 / 3 : ℝ) := by
          nlinarith [le_max_right C 1]

/-- **Frostman and support bounds for the A-sep family at small radii.** -/
theorem frostman_muA0_small {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    {r a₀ a₁ T m : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖) :
    ∃ ρ₀ C B : ℝ, 0 < ρ₀ ∧ 0 ≤ C ∧ 0 ≤ B ∧ ∀ p : Fin 2 → ℝ, p 0 ∈ Icc (0 : ℝ) T →
      p 1 ∈ Icc a₀ a₁ → ∀ ρ ∈ Icc (0 : ℝ) ρ₀,
        TwoPoint.IsFrostman (muA0 W d r p ρ) (1 / 3) C ∧ ∀ᵐ z ∂muA0 W d r p ρ, ‖z‖ ≤ B := by
  set ε : ℝ := m / 2 * Real.exp (-(8 * T / m ^ 2)) with hεdef
  have hε : 0 < ε := by positivity
  set CF : ℝ := 6 / r * (2 * (Real.exp (8 * T / m ^ 2) / a₀)) ^ (1 : ℝ) +
    (2 / (m / 2 * Real.exp (-(8 * T / m ^ 2)))) ^ (1 : ℝ) with hCFdef
  set L : ℝ := Real.exp (2 * T / (m / 4) ^ 2) with hLdef
  have hL : 0 < L := Real.exp_pos _
  set C3 : ℝ := 24 * max CF 1 with hC3def
  have hC3 : 0 ≤ C3 := by positivity
  refine ⟨ε / 4, C3 * (2 * L) ^ (1 / 3 : ℝ) + (2 / 1) ^ (1 / 3 : ℝ),
    |a₁| * (‖d‖ + r) + Real.exp (8 * T / m ^ 2) * ε, by positivity, by positivity,
    by positivity, fun p hp0 hp1 ρ hρ => ?_⟩
  have hT : 0 ≤ T := hp0.1.trans hp0.2
  have ha : 0 < p 1 := ha₀.trans_le hp1.1
  have hgm := measurable_gA hW hW0 hm hgood0 hlow hp0 hp1
  have hνeq : (foldedCircle d r).map (fun w => fwdMap W (p 0) ((p 1 : ℂ) * w)) =
      (foldedCircle d r).map (gA W d r (p 0) (p 1)) :=
    Measure.map_congr (by
      filter_upwards [ae_mem_foldSph d hr.le] with w hw
      exact (gA_of_mem hw).symm)
  set ν := (foldedCircle d r).map (gA W d r (p 0) (p 1)) with hνdef
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hgm.aemeasurable).2 inferInstance
  have hν1 : TwoPoint.IsFrostman ν 1 CF := fun w s hs =>
    isFrostman_alphaA hW hW0 hr ha₀ hm hgood0 hlow hp0 hp1 w s hs
  have hσF : TwoPoint.IsFrostman (bindFc ν ρ) (1 / 3) C3 :=
    isFrostman_bindFc (isFrostman_third_of_one hν1) hρ.1
  have : IsProbabilityMeasure (bindFc ν ρ) :=
    ⟨by rw [CircleFubini.bind_circle_univ, measure_univ]⟩
  have hgood_w : ∀ᵐ w ∂foldedCircle d r, w ∈ foldSph d r ∧ w ∈ H :=
    (ae_mem_foldSph d hr.le).and (TwoPoint.foldedCircle_ae_mem_H d hr)
  have hgH : ∀ w, w ∈ foldSph d r → w ∈ H →
      gA W d r (p 0) (p 1) w = fwdMap W (p 0) ((p 1 : ℂ) * w) ∧
        (p 1 : ℂ) * w ∈ scaledSph d r a₀ a₁ ∧ 0 < ((p 1 : ℂ) * w).im ∧
        0 < (fwdMap W (p 0) ((p 1 : ℂ) * w)).im := fun w hw hwH => by
    have hc := mul_mem_compl_fwdHull hW ha₀ hm hgood0 hlow hp0 hp1 hw hwH
    exact ⟨gA_of_mem hw, mem_scaledSph hp1 hw, hc.1,
      FwdHolo.mapsTo_fwdMap hW hp0.1 hc⟩
  -- the carrying set
  set Z : Set ℂ := fwdMap W (p 0) '' {z | z ∈ scaledSph d r a₀ a₁ ∧ 0 < z.im} with hZ
  have hA : ∀ᵐ x ∂bindFc ν ρ, x ∈ cthickening ρ Z := by
    have hS : MeasurableSet {x : ℂ | x ∉ cthickening ρ Z} :=
      isClosed_cthickening.measurableSet.compl
    rw [ae_iff]
    show (ν.bind fun y => foldedCircle y ρ) {x : ℂ | x ∉ cthickening ρ Z} = 0
    have hmk : Measurable fun y : ℂ => foldedCircle y ρ {x : ℂ | x ∉ cthickening ρ Z} :=
      (Measure.measurable_coe hS).comp (CircleFubini.measurable_foldedCircle' ρ)
    rw [CircleFubini.bind_circle_apply ν hS, hνdef, lintegral_map hmk hgm]
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hgood_w] with w hw
    obtain ⟨e1, e2, e3, e4⟩ := hgH w hw.1 hw.2
    show foldedCircle (gA W d r (p 0) (p 1) w) ρ {x : ℂ | x ∉ cthickening ρ Z} = 0
    rw [e1]
    refine ae_iff.1 ?_
    filter_upwards [FrostmanReg.foldedCircle_ae_near_frostman
      (c := fwdMap W (p 0) ((p 1 : ℂ) * w)) (z := fwdMap W (p 0) ((p 1 : ℂ) * w))
      (show (0 : ℝ) ≤ (fwdMap W (p 0) ((p 1 : ℂ) * w)).im from e4.le) hρ.1] with v hv
    refine mem_cthickening_of_dist_le v _ ρ Z ⟨_, ⟨e2, e3⟩, rfl⟩ ?_
    rw [dist_eq_norm]; simpa using hv.2
  have hH : ∀ᵐ x ∂bindFc ν ρ, x ∈ H := by
    rcases hρ.1.eq_or_lt with h0 | hpos
    · subst h0
      have hνH : ∀ᵐ z ∂ν, z ∈ H :=
        (ae_map_iff hgm.aemeasurable isOpen_H.measurableSet).2 (by
          filter_upwards [hgood_w] with w hw
          obtain ⟨e1, -, -, e4⟩ := hgH w hw.1 hw.2
          show 0 < (gA W d r (p 0) (p 1) w).im
          rw [e1]; exact e4)
      rw [RegUnif.bindFc_zero_of_ae_H hνH]
      exact hνH
    · exact RegUnif.bindFc_ae_mem_H ν hpos
  set E : Set ℂ := {ζ | 0 < ζ.im ∧ ∃ z₀, (z₀ ∈ scaledSph d r a₀ a₁ ∧ 0 < z₀.im) ∧
    ‖ζ - fwdMap W (p 0) z₀‖ ≤ ε} with hEdef
  have hE : ∀ᵐ x ∂bindFc ν ρ, x ∈ E := by
    filter_upwards [hA, hH] with x hxA hxH
    refine ⟨hxH, ?_⟩
    have h1 : infEDist x Z < ENNReal.ofReal ε := by
      refine lt_of_le_of_lt (mem_cthickening_iff.1 hxA) ?_
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith [hρ.2])
    obtain ⟨_, ⟨z₀, hz₀, rfl⟩, hlt⟩ := infEDist_lt_iff.1 h1
    refine ⟨z₀, hz₀, ?_⟩
    rw [← dist_eq_norm]
    exact (edist_lt_ofReal.1 hlt).le
  have hsolZ : ∀ z₀ ∈ scaledSph d r a₀ a₁, ∃ u, IsForwardSol W z₀ T u := by
    rintro _ ⟨q, hq, rfl⟩; exact hgood0 q.1 hq.1 q.2 hq.2
  have hnormZ : ∀ z₀ ∈ scaledSph d r a₀ a₁, ‖z₀‖ ≤ |a₁| * (‖d‖ + r) := by
    rintro _ ⟨q, hq, rfl⟩
    have hq0 : 0 < q.1 := ha₀.trans_le hq.1.1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le]
    exact mul_le_mul (hq.1.2.trans (le_abs_self _)) (norm_le_of_mem_foldSph hq.2)
      (norm_nonneg _) (abs_nonneg _)
  have hgmeas : Measurable (fwdMapInv W (p 0)) := RTBeur.measurable_fwdMapInv_rt hW hW0 hp0.1
  refine ⟨?_, ?_⟩
  · have hco : ∀ x ∈ E, ∀ y ∈ E, ‖fwdMapInv W (p 0) x - fwdMapInv W (p 0) y‖ ≤ 1 →
        ‖x - y‖ ≤ L * ‖fwdMapInv W (p 0) x - fwdMapInv W (p 0) y‖ := by
      rintro x ⟨hxH, z₀, hz₀, hxz⟩ y ⟨hyH, z₀', hz₀', hyz⟩ -
      have h := norm_sub_le_fwdMapInv_sub hW hW0 hm hp0 (hsolZ z₀ hz₀.1) (hlow z₀ hz₀.1)
        (hsolZ z₀' hz₀'.1) (hlow z₀' hz₀'.1) hxH hyH hxz hyz
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      rw [hLdef]
      exact Real.exp_le_exp.2 (by gcongr; exact hp0.2)
    have hF := isFrostman_map_of_coLip hgmeas hE hL one_pos (by norm_num : (0 : ℝ) < 1 / 3)
      hC3 (fun w s hs => hσF w s hs) hco
    unfold muA0
    rw [hνeq]
    exact fun w s hs => hF w s hs
  · unfold muA0
    rw [hνeq]
    refine (ae_map_iff hgmeas.aemeasurable
      (measurableSet_le measurable_norm measurable_const)).2 ?_
    filter_upwards [hE] with x hx
    obtain ⟨hxH, z₀, hz₀, hxz⟩ := hx
    have h := norm_fwdMapInv_sub_le hW hW0 hT hm hz₀.2 (hsolZ z₀ hz₀.1) (hlow z₀ hz₀.1) hp0
      hxH hxz
    have h2 := norm_le_norm_add_norm_sub' (fwdMapInv W (p 0) x) z₀
    have h3 := hnormZ z₀ hz₀.1
    have h4 : Real.exp (8 * T / m ^ 2) * ‖x - fwdMap W (p 0) z₀‖ ≤
        Real.exp (8 * T / m ^ 2) * ε :=
      mul_le_mul_of_nonneg_left hxz (Real.exp_pos _).le
    linarith

end ASep
end QuantumZipper

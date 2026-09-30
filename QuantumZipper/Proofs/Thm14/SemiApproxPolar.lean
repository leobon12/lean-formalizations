import QuantumZipper.Proofs.Thm14.SemiApproxDens
import QuantumZipper.Proofs.Thm12.CharFun
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# SEMI-APPROX, part 2: the polar representation of `ψ_j dz` and of the semicircle

With `m = Leb|(-1,1) ⊗ Leb|(0,π)` (`saM`) and `Γ_e(t,θ) = c + (s + e t) e^{iθ}` (`saGam`):

* `tdens_saPsi`: `ψ_j dz = (m.withDensity W_j).map Γ_{ε_j}`, `W_j(t,θ) = a(t) φ_j(sin θ)/Z_j`;
* `fc_eq_saM`: `fc(c,s) = (m.withDensity W_∞).map Γ_0`, `W_∞(t,θ) = a(t)/π`;
* `integral_saPsi`: `∫ ψ_j = 1`;
* `saW_le`, `saW_tendsto`: the weights are uniformly bounded and converge to `W_∞` on the box.

Own elementary proof: translation, polar coordinates (`Complex.lintegral_comp_polarCoord_symm`),
the substitution `r = s + ε_j t` (`lintegral_image_eq_lintegral_abs_deriv_mul`), Tonelli, and
the semicircle formula `foldedCircle_real_eq`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology Real NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

open CharFun

/-- The parameter measure `Leb|(-1,1) ⊗ Leb|(0,π)`. -/
def saM : Measure (ℝ × ℝ) := (volume.restrict (Ioo (-1 : ℝ) 1)).prod (volume.restrict (Ioo 0 π))

instance : IsFiniteMeasure saM := by unfold saM; infer_instance

/-- The parametrization `Γ_e(t,θ) = c + (s + e t) e^{iθ}`. -/
def saGam (c s e : ℝ) (p : ℝ × ℝ) : ℂ := circleMap (c : ℂ) (s + e * p.1) p.2

/-- The weights `W_j`. -/
def saW (j : ℕ) (p : ℝ × ℝ) : ℝ≥0 := Real.toNNReal (saA p.1 * saAng j p.2 / saZ j)

/-- The limit weight `W_∞`. -/
def saWinf (p : ℝ × ℝ) : ℝ≥0 := Real.toNNReal (saA p.1 / π)

theorem continuous_circleMap_prod (c : ℂ) :
    Continuous fun p : ℝ × ℝ => circleMap c p.1 p.2 :=
  continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const)))

theorem continuous_saGam (c s e : ℝ) : Continuous (saGam c s e) :=
  (continuous_circleMap_prod (c : ℂ)).comp
    ((continuous_const.add (continuous_const.mul continuous_fst)).prodMk continuous_snd)

theorem measurable_saW (j : ℕ) : Measurable (saW j) :=
  measurable_real_toNNReal.comp (((saA_continuous.comp continuous_fst).mul
    ((saAng_continuous j).comp continuous_snd)).div_const _).measurable

theorem measurable_saWinf : Measurable saWinf :=
  measurable_real_toNNReal.comp ((saA_continuous.comp continuous_fst).div_const _).measurable

theorem lintegral_saA : ∫⁻ t in Ioo (-1 : ℝ) 1, ENNReal.ofReal (saA t) = 1 := by
  rw [setLIntegral_eq_of_support_subset, ← ofReal_integral_eq_lintegral_ofReal
    (show Integrable saA volume from saBump.integrable_normed (μ := volume)) (ae_of_all _ saA_nonneg), saA_integral, ENNReal.ofReal_one]
  intro t ht
  by_contra h
  refine ht ?_
  show ENNReal.ofReal (saA t) = 0
  rw [ENNReal.ofReal_eq_zero.2 (le_of_eq (saA_eq_zero ?_))]
  simp only [mem_Ioo, not_and_or, not_lt] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

/-- **Polar representation of `ψ_j dz`** (lintegral form). -/
theorem lintegral_saPsi (c s : ℝ) (hs : 0 < s) (j : ℕ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ z, ENNReal.ofReal (saPsi c s j z) * g z =
      ∫⁻ p, (saW j p : ℝ≥0∞) * g (saGam c s (saEps s j) p) ∂saM := by
  set ε := saEps s j with hεdef
  have hε : 0 < ε := saEps_pos hs j
  have hεs : ε ≤ s / 4 := saEps_le hs j
  have hZ := (saZ_pos j).ne'
  set Hf : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (saA ((p.1 - s) / ε) / ε * saAng j p.2 / saZ j) *
    g (circleMap (c : ℂ) p.1 p.2) with hHf
  have hHm : Measurable Hf := by
    refine (ENNReal.measurable_ofReal.comp ?_).mul (hg.comp (continuous_circleMap_prod _).measurable)
    exact ((((saA_continuous.comp ((continuous_fst.sub continuous_const).div_const _)).div_const
      _).mul ((saAng_continuous j).comp continuous_snd)).div_const _).measurable
  -- translation and polar coordinates
  rw [← lintegral_add_left_eq_self _ (c : ℂ),
    ← Complex.lintegral_comp_polarCoord_symm (fun z => ENNReal.ofReal (saPsi c s j (↑c + z)) *
      g (↑c + z))]
  have hT : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  have hTm : MeasurableSet (polarCoord.target) := by
    rw [hT]; exact measurableSet_Ioi.prod measurableSet_Ioo
  have e1 : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
      (ENNReal.ofReal (saPsi c s j (↑c + Complex.polarCoord.symm p)) *
        g (↑c + Complex.polarCoord.symm p)) = ∫⁻ p in polarCoord.target, Hf p := by
    refine setLIntegral_congr_fun hTm fun p hp => ?_
    rw [hT] at hp
    have hr : 0 < p.1 := hp.1
    have hcm : (c : ℂ) + Complex.polarCoord.symm p = circleMap (c : ℂ) p.1 p.2 := by
      rw [Complex.polarCoord_symm_apply, circleMap, Complex.exp_mul_I, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin]
    have hn : ‖(c : ℂ) + Complex.polarCoord.symm p - c‖ = p.1 := by
      rw [add_sub_cancel_left, Complex.norm_polarCoord_symm, abs_of_pos hr]
    have him : ((c : ℂ) + Complex.polarCoord.symm p - c).im = p.1 * Real.sin p.2 := by
      rw [add_sub_cancel_left, Complex.polarCoord_symm_apply]
      simp [Complex.sin_ofReal_re, Complex.cos_ofReal_re]
    simp only [hHf, smul_eq_mul, ← mul_assoc]
    rw [← ENNReal.ofReal_mul hr.le, hcm.symm]
    congr 2
    unfold saPsi saAng
    rw [hn, him, ← hεdef]
    field_simp
  rw [e1]
  -- restrict to the box `(s-ε, s+ε) × (0, π)`
  have hU : MeasurableSet (Ioo (s - ε) (s + ε) ×ˢ Ioo 0 π) := measurableSet_Ioo.prod measurableSet_Ioo
  have e2 : ∫⁻ p in polarCoord.target, Hf p =
      ∫⁻ p in Ioo (s - ε) (s + ε) ×ˢ Ioo 0 π, Hf p := by
    rw [hT, ← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo),
      ← lintegral_indicator hU]
    congr 1
    funext p
    by_cases hp : p ∈ Ioo (s - ε) (s + ε) ×ˢ Ioo 0 π
    · have hp' : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π :=
        ⟨show 0 < p.1 by linarith [hp.1.1], by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩
      rw [indicator_of_mem hp, indicator_of_mem hp']
    · rw [indicator_of_notMem hp]
      by_cases hp' : p ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π
      · rw [indicator_of_mem hp']
        simp only [hHf]
        by_cases h1 : p.1 ∈ Ioo (s - ε) (s + ε)
        · have h2 : p.2 ≤ 0 := by
            by_contra h2
            exact hp ⟨h1, lt_of_not_ge h2, hp'.2.2⟩
          rw [saAng_eq_zero j (Real.sin_nonpos_of_nonpos_of_neg_pi_le h2 hp'.2.1.le)]
          simp
        · rw [saA_eq_zero]
          · simp
          rw [abs_div, abs_of_pos hε, le_div_iff₀ hε, one_mul]
          simp only [mem_Ioo, not_and_or, not_lt] at h1
          rcases h1 with h | h
          · rw [abs_of_nonpos (by linarith)]; linarith
          · rw [abs_of_nonneg (by linarith)]; linarith
      · rw [indicator_of_notMem hp']
  rw [e2, Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hHm.aemeasurable]
  -- substitution `r = s + ε t`
  have himg : (fun t : ℝ => s + ε * t) '' Ioo (-1) 1 = Ioo (s - ε) (s + ε) := by
    ext r
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    · intro hr
      have : ε * ((r - s) / ε) = r - s := by field_simp
      refine ⟨(r - s) / ε, ⟨?_, ?_⟩, by simp only; linarith⟩
      · rw [lt_div_iff₀ hε]; linarith [hr.1]
      · rw [div_lt_iff₀ hε]; linarith [hr.2]
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo
    (f := fun t => s + ε * t) (f' := fun _ => ε) (fun t _ => ((hasDerivAt_id' t).const_mul ε).const_add s
      |>.hasDerivWithinAt |>.congr_deriv (by simp))
    (fun x _ y _ hxy => by simpa [hε.ne'] using hxy)]
  unfold saM
  rw [lintegral_prod _ (show Measurable fun p => (saW j p : ℝ≥0∞) * g (saGam c s ε p) from
    ((measurable_saW j).coe_nnreal_ennreal).mul
    (hg.comp (continuous_saGam c s ε).measurable)).aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun θ => ?_
  simp only [hHf, saW, saGam, ← mul_assoc]
  rw [abs_of_pos hε, ← ENNReal.ofReal_mul hε.le]
  congr 2
  have : (s + ε * t - s) / ε = t := by field_simp; ring
  rw [this]
  field_simp

/-- **Polar representation of `ψ_j dz`.** -/
theorem tdens_saPsi (c s : ℝ) (hs : 0 < s) (j : ℕ) :
    tdens (saPsi c s j) =
      (saM.withDensity fun p => (saW j p : ℝ≥0∞)).map (saGam c s (saEps s j)) := by
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  unfold CharFun.tdens
  rw [lintegral_map hg (continuous_saGam _ _ _).measurable,
    lintegral_withDensity_eq_lintegral_mul _ (show Measurable fun z =>
      ENNReal.ofReal (saPsi c s j z) from ENNReal.measurable_ofReal.comp
      (saPsi_contDiff c s hs j).continuous.measurable) hg,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_saW j).coe_nnreal_ennreal
      (show Measurable fun p => g (saGam c s (saEps s j) p) from
        hg.comp (continuous_saGam _ _ _).measurable)]
  exact lintegral_saPsi c s hs j g hg

/-- **The semicircle in the parameter space.** -/
theorem fc_eq_saM (c : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    foldedCircle (c : ℂ) s =
      (saM.withDensity fun p => (saWinf p : ℝ≥0∞)).map (saGam c s 0) := by
  rw [foldedCircle_real_eq c hs]
  refine Measure.ext_of_lintegral _ fun g hg => ?_
  have hcm : Measurable (circleMap (c : ℂ) s) := (continuous_circleMap _ _).measurable
  rw [lintegral_smul_measure, lintegral_map hg hcm, lintegral_map hg (continuous_saGam _ _ _).measurable,
    lintegral_withDensity_eq_lintegral_mul _ measurable_saWinf.coe_nnreal_ennreal
      (show Measurable fun p => g (saGam c s 0 p) from
        hg.comp (continuous_saGam _ _ _).measurable)]
  have e : ∀ p : ℝ × ℝ, ((fun p => (saWinf p : ℝ≥0∞)) * fun p => g (saGam c s 0 p)) p =
      ENNReal.ofReal (saA p.1) * ENNReal.ofReal π⁻¹ * g (circleMap (c : ℂ) s p.2) := fun p => by
    simp only [Pi.mul_apply, saWinf, saGam, zero_mul, add_zero]
    rw [← ENNReal.ofReal_mul (saA_nonneg _), div_eq_mul_inv]
    rfl
  simp_rw [e]
  unfold saM
  rw [lintegral_prod_mul (show Measurable fun t => ENNReal.ofReal (saA t) * ENNReal.ofReal π⁻¹
    from (ENNReal.measurable_ofReal.comp saA_continuous.measurable).mul_const _).aemeasurable
    (show Measurable fun θ => g (circleMap (c : ℂ) s θ) from hg.comp hcm).aemeasurable,
    lintegral_mul_const _ (show Measurable fun t => ENNReal.ofReal (saA t) from
      ENNReal.measurable_ofReal.comp saA_continuous.measurable), lintegral_saA, one_mul,
    ENNReal.ofReal_inv_of_pos Real.pi_pos, smul_eq_mul]

/-- **Mass one.** -/
theorem integral_saPsi (c s : ℝ) (hs : 0 < s) (j : ℕ) : ∫ z, saPsi c s j z = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (saPsi_nonneg c s hs j))
    (saPsi_contDiff c s hs j).continuous.aestronglyMeasurable]
  have h := lintegral_saPsi c s hs j (fun _ => 1) measurable_const
  simp only [mul_one] at h
  rw [h]
  have e : ∀ p : ℝ × ℝ, (saW j p : ℝ≥0∞) =
      ENNReal.ofReal (saA p.1) * ENNReal.ofReal (saAng j p.2 / saZ j) := fun p => by
    rw [← ENNReal.ofReal_mul (saA_nonneg _), ← mul_div_assoc]; rfl
  simp_rw [e]
  unfold saM
  rw [lintegral_prod_mul (show Measurable fun t => ENNReal.ofReal (saA t) from
    ENNReal.measurable_ofReal.comp saA_continuous.measurable).aemeasurable
    (show Measurable fun θ => ENNReal.ofReal (saAng j θ / saZ j) from
      ENNReal.measurable_ofReal.comp ((saAng_continuous j).div_const _).measurable).aemeasurable,
    lintegral_saA, one_mul, ← ofReal_integral_eq_lintegral_ofReal
      ((saAng_integrableOn j).div_const _)
      (ae_of_all _ fun θ => div_nonneg (saAng_nonneg j θ) (saZ_pos j).le),
    integral_div, ← saZ, div_self (saZ_pos j).ne', ENNReal.toReal_ofReal zero_le_one]

theorem saW_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ j p, (saW j p : ℝ) ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_saA_le
  have hZ0 := saZ_pos 0
  refine ⟨M / saZ 0, by positivity, fun j p => ?_⟩
  rw [saW, Real.coe_toNNReal']
  refine max_le ?_ (by positivity)
  have hZ := saZ_pos j
  calc saA p.1 * saAng j p.2 / saZ j ≤ M * 1 / saZ j :=
        div_le_div_of_nonneg_right (mul_le_mul (hM _) (saAng_le_one j _) (saAng_nonneg j _) hM0)
          hZ.le
    _ ≤ M / saZ 0 := by
        rw [mul_one]; exact div_le_div_of_nonneg_left hM0 hZ0 (saZ_mono (Nat.zero_le j))

theorem saWinf_le : ∃ M : ℝ, 0 ≤ M ∧ ∀ p, (saWinf p : ℝ) ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_saA_le
  refine ⟨M / π, by positivity, fun p => ?_⟩
  rw [saWinf, Real.coe_toNNReal']
  exact max_le (div_le_div_of_nonneg_right (hM _) Real.pi_pos.le) (by positivity)

theorem saW_tendsto {p : ℝ × ℝ} (hp : p.2 ∈ Ioo 0 π) :
    Tendsto (fun j => saW j p) atTop (𝓝 (saWinf p)) := by
  refine (continuous_real_toNNReal.tendsto _).comp ?_
  have h1 : Tendsto (fun j => saAng j p.2) atTop (𝓝 1) :=
    tendsto_const_nhds.congr' ((saAng_eventually_one
      (Real.sin_pos_of_pos_of_lt_pi hp.1 hp.2)).mono fun j h => h.symm)
  have := (tendsto_const_nhds (x := saA p.1)).mul h1 |>.div saZ_tendsto Real.pi_ne_zero
  rw [mul_one] at this
  exact this

end Thm14WDG
end QuantumZipper

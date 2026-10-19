import HigherDimLFPP.Lower.Lemma53Expand

/-!
# Lemma 5.3: the expansion terms as white-noise pairings (source §5.2, Steps 2 and 4)

Packet P-L3, target T3 (audit HA4, "Details for later use" D4 (K2), (K5), D6 Steps 2 and 4;
finding HA4-4).  Fix a white noise `W` and evaluate P-L2a's construction on the band values
`Y_ω(t) = W(k_t)(ω)` (P-L2a's `integral_gLawD_eq_whiteNoise` identifies every finite-model
expectation with such a white-noise expectation).

* `integral_exp_W`, `integral_expRem_W`: one-point Gaussian moments
  `E e^{c W(f)} = e^{c²‖f‖²/2}` and `E R(c W(f)) = e^{c²‖f‖²/2} - 1` (no supremum over a box is
  needed, HA4-4).
* `LParams.integral_remW_one`: `E ∫ R(ζH) dν_{j,μ} = q^{-ζ²/2} - 1` (every root-band value has
  variance `log(ρ/ρq) = log(1/q)`).
* `LParams.replM h j = h ν_{j,μ}` (an atomic measure) and `LParams.ae_linW_eq`:
  `⟨H, h ν_{j,μ}⟩ = W(bandVecM κ (ρq, ρ) (h ν_{j,μ}) 0)` a.s.; `replM_le`, `replM_real_univ_le`:
  `h ν_{j,μ} ≤ ν_{j,μ}` with mass `≤ 1` for `0 ≤ h ≤ 1` (the prefix measures of (K5)).
* Integrability of all terms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

variable {d : ℕ} {κ : Rd d → ℝ} {Ω : Type*} [MeasurableSpace Ω] {Pr : Measure Ω}
  {W : WN d → Ω → ℝ}

/-! ## One-point Gaussian moments -/

theorem integrable_exp_W (hW : IsWhiteNoise Pr W) (f : WN d) (c : ℝ) :
    Integrable (fun ω => Real.exp (c * W f ω)) Pr :=
  GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal (hW.hasLaw_single f) c

/-- `E e^{c W(f)} = e^{c² ‖f‖² / 2}`. -/
theorem integral_exp_W (hW : IsWhiteNoise Pr W) (f : WN d) (c : ℝ) :
    ∫ ω, Real.exp (c * W f ω) ∂Pr = Real.exp (c ^ 2 * ‖f‖ ^ 2 / 2) := by
  have h := mgf_gaussianReal (hW.hasLaw_single f) c
  unfold mgf at h
  rw [h, Real.coe_toNNReal _ (sq_nonneg _)]
  ring_nf

theorem integrable_expRem_W (hW : IsWhiteNoise Pr W) (f : WN d) (c : ℝ) :
    Integrable (fun ω => expRem (c * W f ω)) Pr := by
  have := hW.isProbabilityMeasure
  unfold expRem
  exact ((integrable_exp_W hW f c).sub' (integrable_const 1)).sub'
    ((integrable_W hW f).const_mul c)

/-- `E R(c W(f)) = e^{c² ‖f‖² / 2} - 1`, `R(t) = eᵗ - 1 - t`. -/
theorem integral_expRem_W (hW : IsWhiteNoise Pr W) (f : WN d) (c : ℝ) :
    ∫ ω, expRem (c * W f ω) ∂Pr = Real.exp (c ^ 2 * ‖f‖ ^ 2 / 2) - 1 := by
  have := hW.isProbabilityMeasure
  unfold expRem
  rw [integral_sub ((integrable_exp_W hW f c).sub' (integrable_const 1))
      ((integrable_W hW f).const_mul c),
    integral_sub (integrable_exp_W hW f c) (integrable_const 1), integral_const_mul,
    hW.integral_eq_zero, integral_exp_W hW f c]
  simp

/-! ## The construction on white-noise band values -/

namespace LParams

variable (P : LParams d) (Sμ : Finset (Rd d)) (w : Rd d → ℝ)

theorem measurable_wnField (hW : IsWhiteNoise Pr W) :
    Measurable fun ω => fun s : TriD d => W (triVec κ s) ω :=
  Measurable.of_eval fun _ => hW.measurable _

omit [MeasurableSpace Ω] in
theorem rv_wnField (ω : Ω) (j : Fin (P.J + 1)) (i : ℕ) (z : Rd d) :
    P.rv (fun t => W (triVec κ t) ω) j i z =
      W (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z)) ω := rfl

theorem integrable_linW (hW : IsWhiteNoise Pr W) (h : Rd d → ℝ) (j : Fin (P.J + 1)) :
    Integrable (fun ω => P.linW Sμ w h j (fun t => W (triVec κ t) ω)) Pr := by
  unfold linW
  refine (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun z _ => ?_).const_mul _
  exact (integrable_W hW (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z))).const_mul _

theorem integrable_remW (hW : IsWhiteNoise Pr W) (h : Rd d → ℝ) (j : Fin (P.J + 1)) :
    Integrable (fun ω => P.remW Sμ w h j (fun t => W (triVec κ t) ω)) Pr := by
  unfold remW
  refine (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun z _ => ?_).const_mul _
  exact (integrable_expRem_W hW (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z)) P.ζ).const_mul _

/-- **The Taylor remainder** (HA4 D6 Step 2, finding HA4-4): `E ∫ R(ζH) dν_{j,μ} = q^{-ζ²/2} - 1`
in the form `e^{ζ² log(1/q)/2} - 1`. -/
theorem integral_remW_one (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise Pr W) {Sμ : Finset (Rd d)}
    {w : Rd d → ℝ} (hμ : IsFinProb Sμ w) (hK : 0 < P.K) (hρ : 0 < P.ρ) (hq0 : 0 < P.q)
    (hq1 : P.q ≤ 1) (j : Fin (P.J + 1)) :
    ∫ ω, P.remW Sμ w (fun _ => 1) j (fun t => W (triVec κ t) ω) ∂Pr =
      Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1 := by
  have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
  have hρq : 0 < P.ρ * P.q := mul_pos hρ hq0
  have hnorm : ∀ p : Rd d, ‖bandVec κ (P.ρ * P.q) P.ρ p‖ ^ 2 = Real.log (1 / P.q) := by
    intro p
    rw [norm_bandVec_sq hκ hρq (mul_le_of_le_one_right hρ.le hq1)]
    congr 1
    field_simp
  unfold remW
  simp only [rv_wnField, mul_one]
  rw [integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun z _ =>
    (integrable_expRem_W hW _ P.ζ).const_mul _]
  have e : ∀ i ∈ Finset.range P.K, ∫ ω, ∑ z ∈ Sμ,
      w z * expRem (P.ζ * W (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z)) ω) ∂Pr =
      ∑ z ∈ Sμ, w z * (Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1) := by
    intro i _
    rw [integral_finsetSum _ fun z _ => (integrable_expRem_W hW _ P.ζ).const_mul _]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [integral_const_mul, integral_expRem_W hW, hnorm]
  rw [Finset.sum_congr rfl e, Finset.sum_congr rfl fun i _ =>
    (Finset.sum_mul Sμ w (Real.exp (P.ζ ^ 2 * Real.log (1 / P.q) / 2) - 1)).symm, hμ.2, one_mul,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- `h ν_{j,μ} = K⁻¹ Σ_{i,z} w z h(T_i^j z) δ_{T_i^j z}`. -/
def replM (h : Rd d → ℝ) (j : Fin (P.J + 1)) : Measure (Rd d) :=
  atomM (Finset.range P.K ×ˢ Sμ) (fun x => 1 / (P.K : ℝ) * (w x.2 * h ((P.T j x.1).app x.2)))
    (fun x => (P.T j x.1).app x.2)

instance isFiniteMeasure_replM (h : Rd d → ℝ) (j : Fin (P.J + 1)) :
    IsFiniteMeasure (P.replM Sμ w h j) := by
  unfold replM
  infer_instance

/-- **The pairing `⟨H, h ν_{j,μ}⟩` is a white-noise pairing** (a.s.). -/
theorem ae_linW_eq (hκ : IsLFPPKernel κ) (hW : IsWhiteNoise Pr W) (hρq : 0 < P.ρ * P.q)
    {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ Sμ, 0 ≤ w z) {h : Rd d → ℝ}
    (hh : ∀ p, 0 ≤ h p) (j : Fin (P.J + 1)) :
    ∀ᵐ ω ∂Pr, P.linW Sμ w h j (fun t => W (triVec κ t) ω) =
      W (bandVecM κ (Ioo (P.ρ * P.q) P.ρ) (P.replM Sμ w h j) 0) ω := by
  have hK : (0 : ℝ) ≤ 1 / (P.K : ℝ) := by positivity
  have e := ae_W_atomM (P := Pr) hκ hW (b := P.ρ) hρq (Finset.range P.K ×ˢ Sμ)
    (c := fun x => 1 / (P.K : ℝ) * (w x.2 * h ((P.T j x.1).app x.2)))
    (fun x hx => mul_nonneg hK (mul_nonneg (hw x.2 (Finset.mem_product.1 hx).2) (hh _)))
    (fun x => (P.T j x.1).app x.2)
  filter_upwards [e] with ω hω
  rw [replM, hω, Finset.sum_product]
  unfold linW
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [rv_wnField]
  ring

theorem replM_le {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hw : ∀ z ∈ Sμ, 0 ≤ w z)
    {h : Rd d → ℝ} (hh1 : ∀ p, h p ≤ 1) (j : Fin (P.J + 1)) :
    P.replM Sμ w h j ≤ P.replM Sμ w (fun _ => 1) j := by
  refine Measure.le_iff.2 fun s _ => ?_
  unfold replM
  rw [atomM_apply, atomM_apply]
  refine Finset.sum_le_sum fun x hx => mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hwx := hw x.2 (Finset.mem_product.1 hx).2
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hh1 _) hwx) (by positivity)

theorem replM_real_univ_le {Sμ : Finset (Rd d)} {w : Rd d → ℝ} (hμ : IsFinProb Sμ w)
    (hK : 0 < P.K) {h : Rd d → ℝ} (hh : ∀ p, 0 ≤ h p) (hh1 : ∀ p, h p ≤ 1)
    (j : Fin (P.J + 1)) : (P.replM Sμ w h j).real univ ≤ 1 := by
  have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
  have hc : ∀ x ∈ Finset.range P.K ×ˢ Sμ,
      0 ≤ 1 / (P.K : ℝ) * (w x.2 * h ((P.T j x.1).app x.2)) := fun x hx =>
    mul_nonneg (by positivity) (mul_nonneg (hμ.1 x.2 (Finset.mem_product.1 hx).2) (hh _))
  unfold replM
  rw [atomM_real_univ _ hc, Finset.sum_product]
  calc ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ, 1 / (P.K : ℝ) * (w z * h ((P.T j i).app z))
      ≤ ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ, 1 / (P.K : ℝ) * w z := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun z hz => ?_
        exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (hμ.1 z hz) (hh1 _))
          (by positivity)
    _ = 1 := by
        rw [Finset.sum_congr rfl fun i _ => (Finset.mul_sum Sμ w (1 / (P.K : ℝ))).symm, hμ.2,
          mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- `1 · ν_{j,μ}` is the replaced measure `ν_{j,μ}` of P-L1/`coupledWithin_repl_polyM`. -/
theorem replM_one (j : Fin (P.J + 1)) :
    P.replM Sμ w (fun _ => 1) j = atomM (Finset.range P.K ×ˢ Sμ)
      (fun x => 1 / (P.K : ℝ) * w x.2) (fun x => (edgeSim P.q (P.v j) x.1).app x.2) := by
  unfold replM
  exact atomM_congr _ (fun x _ => by rw [mul_one]) fun x _ => rfl

theorem isProbabilityMeasure_replM_one {Sμ : Finset (Rd d)} {w : Rd d → ℝ}
    (hμ : IsFinProb Sμ w) (hK : 0 < P.K) (j : Fin (P.J + 1)) :
    IsProbabilityMeasure (P.replM Sμ w (fun _ => 1) j) := by
  have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
  unfold replM
  refine isProbabilityMeasure_atomM _ (fun x hx => mul_nonneg (by positivity)
    (by rw [mul_one]; exact hμ.1 x.2 (Finset.mem_product.1 hx).2)) ?_ _
  rw [Finset.sum_product]
  simp only [mul_one]
  rw [Finset.sum_congr rfl fun i _ => (Finset.mul_sum Sμ w (1 / (P.K : ℝ))).symm, hμ.2,
    mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-! ## Integrability of the terms at the selected index -/

variable {P}

theorem measurable_sel_wn (hP : P.Good) (hW : IsWhiteNoise Pr W) :
    Measurable fun ω => P.sel (fun t => W (triVec κ t) ω) :=
  hP.measurable_sel.comp (LParams.measurable_wnField (κ := κ) hW)

/-- A bounded function of the selected index is integrable. -/
theorem integrable_of_sel (hP : P.Good) (hW : IsWhiteNoise Pr W) (g : Fin (P.J + 1) → ℝ) :
    Integrable (fun ω => g (P.sel (fun t => W (triVec κ t) ω))) Pr := by
  have := hW.isProbabilityMeasure
  refine Integrable.mono' (integrable_const (∑ j, |g j|)) ?_ (Filter.Eventually.of_forall
    fun ω => ?_)
  · exact ((measurable_of_countable g).comp (measurable_sel_wn hP hW)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun j => |g j|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ _)

/-- `∫ h e^{ζH} dν_{I,μ}` is integrable on the white-noise space. -/
theorem integrable_tiltH (hP : P.Good) (hW : IsWhiteNoise Pr W) {Sμ : Finset (Rd d)}
    {w : Rd d → ℝ} (hw : ∀ z ∈ Sμ, 0 ≤ w z) {h : Rd d → ℝ} (hh : ∀ p, 0 ≤ h p)
    (hh1 : ∀ p, h p ≤ 1) :
    Integrable (fun ω => P.tiltH Sμ w h (fun t => W (triVec κ t) ω)) Pr := by
  have hK : (0 : ℝ) ≤ 1 / (P.K : ℝ) := by positivity
  set G : Ω → ℝ := fun ω => (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K, ∑ z ∈ Sμ,
    w z * ∑ j, Real.exp (P.ζ * W (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z)) ω) with hG
  have hGi : Integrable G Pr :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun z _ =>
      (integrable_finsetSum _ fun j _ => integrable_exp_W hW _ _).const_mul _).const_mul _
  refine Integrable.mono' hGi ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · have hm := hP.measurable_of_sel (Φ := fun j Y => (1 / (P.K : ℝ)) * ∑ i ∈ Finset.range P.K,
      ∑ z ∈ Sμ, w z * h ((P.T j i).app z) * Real.exp (P.ζ * P.rv Y j i z)) fun j =>
        measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
          fun z _ => measurable_const.mul (measurable_exp_eval _ _))
    exact (hm.comp (LParams.measurable_wnField (κ := κ) hW)).aestronglyMeasurable
  · have h0 : 0 ≤ P.tiltH Sμ w h (fun t => W (triVec κ t) ω) := by
      unfold tiltH
      exact mul_nonneg hK (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun z hz =>
        mul_nonneg (mul_nonneg (hw z hz) (hh _)) (Real.exp_pos _).le)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    unfold tiltH
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum
      fun z hz => ?_) hK
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hw z hz)
    calc h ((P.T (P.sel (fun t => W (triVec κ t) ω)) i).app z) *
          Real.exp (P.ζ * P.rv (fun t => W (triVec κ t) ω) (P.sel fun t => W (triVec κ t) ω) i z)
        ≤ 1 * Real.exp (P.ζ * P.rv (fun t => W (triVec κ t) ω)
            (P.sel fun t => W (triVec κ t) ω) i z) :=
          mul_le_mul_of_nonneg_right (hh1 _) (Real.exp_pos _).le
      _ ≤ ∑ j, Real.exp (P.ζ * W (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z)) ω) := by
          rw [one_mul]
          exact Finset.single_le_sum (f := fun j => Real.exp (P.ζ *
            W (bandVec κ (P.ρ * P.q) P.ρ ((P.T j i).app z)) ω)) (fun j _ => (Real.exp_pos _).le)
            (Finset.mem_univ _)

end LParams

end HigherDimLFPP.Lower

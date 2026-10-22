import HigherDimLQGMetric.Sphere.Potential

/-!
# The unit-sphere log potential and the variances of sphere-average differences

Packet F3 (Phase A, block A1), target 3. MA0 Details (a) D-F3 (`Var(h_r(z) − h_R(0)) =
log(R/r) + O(1)` uniformly over `z ∈ B_{LR}(0)`, `r ≤ R`; the unit-sphere log potential is bounded
and continuous on compacts); blueprint Lemma `lem:potential` (a)–(c) and Lemma `r1:lem:var` (a)
(the explicit form with `log⁺(|w|/ρ)`, erratum of BW2).

`sphPot d = F₁ = logPotM σ` (`σ = unitSphereProb d`), `sphEnergy d = c_d = ∫ F₁ dσ`. For `d ≥ 2`:

* `continuous_sphPot`, `sphPot_le` (`F₁ ≤ 2^d`), `neg_log_le_sphPot` (`F₁(x) ≥ -log(|x| + 1)`),
  `abs_sphPot_le` (`|F₁(x)| ≤ 2^d + log(|x| + 1)`): bounded and continuous on compacts;
* scaling (`logPotM_sphMeas`): `F_{R,w}(x) = log(1/R) + F₁((x - w)/R)` for the potential of
  `σ_{R,w}`;
* mutual energies (`logEnergy_sphMeas`):
  `I(σ_{r,z}, σ_{R,w}) = log(1/R) + ∫ F₁((z + r u - w)/R) dσ(u)`, in particular
  `I(σ_{r,z}, σ_{r,z}) = log(1/r) + c_d`;
* the exact variance (`IsWholeSpaceLGF.variance_sphereAvg_sub_eq`), for all `r, R > 0`:
  `Var(h_r(z) - h_R(w)) = log(R/r) + 2 c_d - 2 ∫ F₁((z + r u - w)/R) dσ(u)`;
* D-F3 (`exists_abs_variance_sphereAvg_sub_sub_log_le`): for `L ≥ 0` there is `K_L` with
  `|Var(h_r(z) - h_R(w)) - log(R/r)| ≤ K_L` whenever `0 < r ≤ R`, `|z - w| ≤ L R`;
* blueprint `r1:lem:var` (a) (`exists_variance_sphereAvg_sub_le`): there is `K_d` with
  `Var(h_r(z) - h_ρ(w)) ≤ log(ρ/r) + 2 log⁺(|z - w|/ρ) + K_d` for `r ≤ ρ` and
  `≤ log(r/ρ) + 2 log⁺(|z - w|/r) + K_d` for `ρ ≤ r`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- `F₁`: the logarithmic potential of the uniform measure on the unit sphere. -/
abbrev sphPot (d : ℕ) : Rd d → ℝ := logPotM (unitSphereProb d)

/-- `c_d = ∫ F₁ dσ = I(σ, σ)`. -/
def sphEnergy (d : ℕ) : ℝ := ∫ u, sphPot d u ∂(unitSphereProb d)

theorem unitSphereProb_smallBall (hd : 2 ≤ d) :
    ∀ z : Rd d, ∀ s > 0, (unitSphereProb d).real (closedBall z s) ≤ 2 ^ d * s :=
  fun z _ hs => unitSphereProb_closedBall_le_mul hd z hs

theorem ae_unitSphereProb_norm_le (d : ℕ) : ∀ᵐ y ∂(unitSphereProb d), ‖y‖ ≤ 1 := by
  filter_upwards [ae_unitSphereProb_norm_eq_one d] with y hy
  exact hy.le

theorem integrable_log_norm_sub_unitSphereProb (hd : 2 ≤ d) (x : Rd d) :
    Integrable (fun y => Real.log ‖x - y‖) (unitSphereProb d) :=
  integrable_log_norm_sub_left (by positivity) (unitSphereProb_smallBall hd)
    (ae_unitSphereProb_norm_le d) x

/-- **`F₁` is continuous** (`d ≥ 2`). -/
theorem continuous_sphPot (hd : 2 ≤ d) : Continuous (sphPot d) :=
  continuous_logPotM (by positivity) (unitSphereProb_smallBall hd) (ae_unitSphereProb_norm_le d)

theorem sphPot_le (hd : 2 ≤ d) (x : Rd d) : sphPot d x ≤ 2 ^ d :=
  logPotM_le (by positivity) (unitSphereProb_smallBall hd) (ae_unitSphereProb_norm_le d) x

theorem neg_log_le_sphPot (hd : 2 ≤ d) (x : Rd d) : -Real.log (‖x‖ + 1) ≤ sphPot d x := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have h := neg_mul_le_logPotM (by positivity) (unitSphereProb_smallBall hd)
    (ae_unitSphereProb_norm_le d) x
  rw [probReal_univ, one_mul, max_eq_right (Real.log_nonneg (by linarith [norm_nonneg x]))] at h
  exact h

/-- **`F₁` is bounded on compacts**: `|F₁(x)| ≤ 2^d + log(|x| + 1)`. -/
theorem abs_sphPot_le (hd : 2 ≤ d) (x : Rd d) : |sphPot d x| ≤ 2 ^ d + Real.log (‖x‖ + 1) := by
  have h1 := sphPot_le hd x
  have h2 := neg_log_le_sphPot hd x
  have h3 : 0 ≤ Real.log (‖x‖ + 1) := Real.log_nonneg (by linarith [norm_nonneg x])
  have h4 : (0 : ℝ) ≤ 2 ^ d := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- `∫ log|x - R v|⁻¹ dσ(v) = log(1/R) + F₁(x/R)` (`R > 0`). -/
theorem integral_neg_log_norm_sub_smul (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) (x : Rd d) :
    ∫ v, -Real.log ‖x - R • v‖ ∂(unitSphereProb d) = -Real.log R + sphPot d (R⁻¹ • x) := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hpt : ∀ᵐ v ∂(unitSphereProb d), -Real.log ‖x - R • v‖ =
      -Real.log R + -Real.log ‖R⁻¹ • x - v‖ := by
    filter_upwards [ae_ne_of_smallBall (unitSphereProb_smallBall hd) (R⁻¹ • x)] with v hv
    have hne : ‖R⁻¹ • x - v‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hv))
    have e : x - R • v = R • (R⁻¹ • x - v) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hR, Real.log_mul hR.ne' hne]
    ring
  have hi : Integrable (fun v => -Real.log ‖R⁻¹ • x - v‖) (unitSphereProb d) :=
    (integrable_log_norm_sub_unitSphereProb hd _).neg
  rw [integral_congr_ae hpt, integral_add (integrable_const _) hi, integral_const, probReal_univ,
    one_smul]
  rfl

/-- **Scaling of sphere potentials**: `F_{R,w}(x) = log(1/R) + F₁((x - w)/R)`. -/
theorem logPotM_sphMeas (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) (w x : Rd d) :
    logPotM (sphMeas R w) x = -Real.log R + sphPot d (R⁻¹ • (x - w)) := by
  have hm : Measurable fun y : Rd d => -Real.log ‖x - y‖ :=
    (measurable_const.sub measurable_id).norm.log.neg
  rw [logPotM, sphMeas, integral_map (by fun_prop) hm.aestronglyMeasurable]
  rw [← integral_neg_log_norm_sub_smul hd hR (x - w)]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [sub_add_eq_sub_sub]

/-- The sphere potentials are continuous. -/
theorem continuous_logPotM_sphMeas (hd : 2 ≤ d) {R : ℝ} (hR : 0 < R) (w : Rd d) :
    Continuous (logPotM (sphMeas R w)) := by
  have e : logPotM (sphMeas R w) = fun x => -Real.log R + sphPot d (R⁻¹ • (x - w)) :=
    funext fun x => logPotM_sphMeas hd hR w x
  rw [e]
  exact continuous_const.add ((continuous_sphPot hd).comp (by fun_prop))

theorem integrable_logEnergy_sphMeas (hd : 2 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (z w : Rd d) :
    Integrable (fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖)
      ((sphMeas r z).prod (sphMeas R w)) := by
  have hP := logPairable_sphLaw hd hr hR hr hR z w z w 0 0 0 0
  have := hP.integrable_prod (HigherDimLFPP.FieldAux.le_add_four₁ _ _ _ _)
    (HigherDimLFPP.FieldAux.le_add_four₂ _ _ _ _)
  rw [sphLaw_zero, sphLaw_zero] at this
  exact this.neg

/-- **Mutual energies of sphere measures**:
`I(σ_{r,z}, σ_{R,w}) = log(1/R) + ∫ F₁((z + r u - w)/R) dσ(u)`. -/
theorem logEnergy_sphMeas (hd : 2 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z w : Rd d) :
    logEnergy (sphMeas r z) (sphMeas R w) =
      -Real.log R + ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d) := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hg₁ : Measurable fun u : Rd d => z + r • u := by fun_prop
  have hg₂ : Measurable fun v : Rd d => w + R • v := by fun_prop
  have hint := integrable_logEnergy_sphMeas hd hr hR z w
  have hmap : (sphMeas r z).prod (sphMeas R w) =
      ((unitSphereProb d).prod (unitSphereProb d)).map
        (Prod.map (fun u : Rd d => z + r • u) fun v : Rd d => w + R • v) :=
    Measure.map_prod_map _ _ hg₁ hg₂
  have hFm : Measurable fun p : Rd d × Rd d => -Real.log ‖p.1 - p.2‖ :=
    (measurable_fst.sub measurable_snd).norm.log.neg
  rw [hmap] at hint
  have hint' := (integrable_map_measure hFm.aestronglyMeasurable
    (hg₁.prodMap hg₂).aemeasurable).1 hint
  have hint'' : Integrable (fun q : Rd d × Rd d => -Real.log ‖(z + r • q.1) - (w + R • q.2)‖)
      ((unitSphereProb d).prod (unitSphereProb d)) := hint'
  unfold logEnergy
  rw [hmap, integral_map (hg₁.prodMap hg₂).aemeasurable hFm.aestronglyMeasurable]
  simp only [Prod.map_fst, Prod.map_snd]
  rw [integral_prod _ hint'']
  have hin : ∀ u : Rd d, ∫ v, -Real.log ‖(z + r • (u, v).1) - (w + R • (u, v).2)‖
        ∂(unitSphereProb d) = -Real.log R + sphPot d (R⁻¹ • (z + r • u - w)) := by
    intro u
    rw [← integral_neg_log_norm_sub_smul hd hR (z + r • u - w)]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    simp only
    rw [sub_add_eq_sub_sub]
  simp_rw [hin]
  have hc : Continuous fun u : Rd d => sphPot d (R⁻¹ • (z + r • u - w)) :=
    (continuous_sphPot hd).comp (by fun_prop)
  rw [integral_add (integrable_const _) (integrable_unitSphereProb_of_continuous hc),
    integral_const, probReal_univ, one_smul]

/-- `I(σ_{r,z}, σ_{r,z}) = log(1/r) + c_d`. -/
theorem logEnergy_sphMeas_self (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    logEnergy (sphMeas r z) (sphMeas r z) = -Real.log r + sphEnergy d := by
  rw [logEnergy_sphMeas hd hr hr z z, sphEnergy]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- `logCov(σ_{r,z}, σ_{R,w}, σ_{r,z}, σ_{R,w}) = log(R/r) + 2 c_d - 2 ∫ F₁((z + r u - w)/R) dσ`. -/
theorem logCov_sphMeas_self (hd : 2 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z w : Rd d) :
    HigherDimLFPP.logCov (sphMeas r z) (sphMeas R w) (sphMeas r z) (sphMeas R w) =
      Real.log (R / r) + 2 * sphEnergy d -
        2 * ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d) := by
  have := isProbabilityMeasure_sphMeas (show 1 ≤ d by omega) r z
  have := isProbabilityMeasure_sphMeas (show 1 ≤ d by omega) R w
  rw [logCov_eq_logEnergy, logEnergy_comm (sphMeas R w) (sphMeas r z),
    logEnergy_sphMeas_self hd hr z, logEnergy_sphMeas_self hd hR w,
    logEnergy_sphMeas hd hr hR z w, Real.log_div hR.ne' hr.ne']
  ring

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- **Exact variance of a sphere-average difference** (`d ≥ 2`, all `r, R > 0`):
`Var(h_r(z) - h_R(w)) = log(R/r) + 2 c_d - 2 ∫ F₁((z + r u - w)/R) dσ(u)`. -/
theorem IsWholeSpaceLGF.variance_sphereAvg_sub_eq (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z w : Rd d) :
    Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) R w; P] =
      Real.log (R / r) + 2 * sphEnergy d -
        2 * ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d) := by
  rw [hh.variance_sphereAvg_sub hd hr hR z w, logCov_sphMeas_self hd hr hR z w]

theorem abs_integral_sphPot_le (hd : 2 ≤ d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z w : Rd d)
    {L : ℝ} (hrR : r ≤ R) (hzw : ‖z - w‖ ≤ L * R) :
    |∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d)| ≤
      2 ^ d + Real.log (L + 2) := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  have hL : 0 ≤ L := by
    have := norm_nonneg (z - w)
    by_contra hneg
    push Not at hneg
    nlinarith
  have hb : ∀ᵐ u ∂(unitSphereProb d), ‖sphPot d (R⁻¹ • (z + r • u - w))‖ ≤
      2 ^ d + Real.log (L + 2) := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    rw [Real.norm_eq_abs]
    refine (abs_sphPot_le hd _).trans (add_le_add le_rfl (Real.log_le_log (by positivity) ?_))
    have hn : ‖R⁻¹ • (z + r • u - w)‖ ≤ L + 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
      have e : z + r • u - w = (z - w) + r • u := by abel
      rw [e]
      calc R⁻¹ * ‖(z - w) + r • u‖ ≤ R⁻¹ * (‖z - w‖ + ‖r • u‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.2 hR.le)
        _ = R⁻¹ * ‖z - w‖ + r / R := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]; field_simp
        _ ≤ L + 1 := by
            have h1 : R⁻¹ * ‖z - w‖ ≤ L := by
              rw [inv_mul_le_iff₀ hR]; linarith
            have h2 : r / R ≤ 1 := (div_le_one hR).2 hrR
            linarith
    linarith
  calc |∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d)|
      = ‖∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d)‖ := (Real.norm_eq_abs _).symm
    _ ≤ 2 ^ d + Real.log (L + 2) := by
        have := norm_integral_le_of_norm_le_const (μ := unitSphereProb d) hb
        rwa [probReal_univ, mul_one] at this

/-- **D-F3**: `Var(h_r(z) - h_R(w)) = log(R/r) + O(1)` uniformly over `0 < r ≤ R`,
`|z - w| ≤ L R` (`d ≥ 2`, every LGF). -/
theorem exists_abs_variance_sphereAvg_sub_sub_log_le (hd : 2 ≤ d) (L : ℝ) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r R : ℝ}, 0 < r → r ≤ R → ∀ z w : Rd d, ‖z - w‖ ≤ L * R →
        |Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) R w; P] - Real.log (R / r)| ≤ K := by
  refine ⟨2 * |sphEnergy d| + 2 * (2 ^ d + Real.log (L + 2)),
    fun {Ω} _ {P} {h} hh {r R} hr hrR z w hzw => ?_⟩
  have hR : 0 < R := hr.trans_le hrR
  rw [hh.variance_sphereAvg_sub_eq hd hr hR z w]
  have hJ := abs_integral_sphPot_le hd hr hR z w hrR hzw
  have : Real.log (R / r) + 2 * sphEnergy d -
      2 * ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d) - Real.log (R / r) =
      2 * sphEnergy d - 2 * ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d) := by ring
  rw [this]
  calc |2 * sphEnergy d - 2 * ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d)|
      ≤ |2 * sphEnergy d| + |2 * ∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d)| :=
        abs_sub _ _
    _ = 2 * |sphEnergy d| +
          2 * |∫ u, sphPot d (R⁻¹ • (z + r • u - w)) ∂(unitSphereProb d)| := by
        rw [abs_mul, abs_mul, abs_two]
    _ ≤ 2 * |sphEnergy d| + 2 * (2 ^ d + Real.log (L + 2)) := by linarith

theorem log_add_two_le (a : ℝ) (ha : 0 ≤ a) :
    Real.log (a + 2) ≤ max 0 (Real.log a) + Real.log 3 := by
  rcases le_total a 1 with h | h
  · have : Real.log (a + 2) ≤ Real.log 3 := Real.log_le_log (by linarith) (by linarith)
    linarith [le_max_left 0 (Real.log a)]
  · have ha0 : 0 < a := by linarith
    have : Real.log (a + 2) ≤ Real.log (3 * a) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) ha0.ne'] at this
    linarith [le_max_right 0 (Real.log a)]

/-- The upper half of the exact formula: `Var(h_r(z) - h_R(w)) ≤ log(R/r) + 2 c_d +
2 log(|z - w|/R + r/R + 1)`. -/
theorem IsWholeSpaceLGF.variance_sphereAvg_sub_le_log (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (z w : Rd d) :
    Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) R w; P] ≤
      Real.log (R / r) + 2 * sphEnergy d + 2 * Real.log (‖z - w‖ / R + r / R + 1) := by
  have := isProbabilityMeasure_unitSphereProb (show 1 ≤ d by omega)
  rw [hh.variance_sphereAvg_sub_eq hd hr hR z w]
  have hlow : ∀ᵐ u ∂(unitSphereProb d), -Real.log (‖z - w‖ / R + r / R + 1) ≤
      sphPot d (R⁻¹ • (z + r • u - w)) := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    refine le_trans ?_ (neg_log_le_sphPot hd _)
    rw [neg_le_neg_iff]
    refine Real.log_le_log (by positivity) ?_
    have hn : ‖R⁻¹ • (z + r • u - w)‖ ≤ ‖z - w‖ / R + r / R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
      have e : z + r • u - w = (z - w) + r • u := by abel
      rw [e]
      calc R⁻¹ * ‖(z - w) + r • u‖ ≤ R⁻¹ * (‖z - w‖ + ‖r • u‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (inv_nonneg.2 hR.le)
        _ = ‖z - w‖ / R + r / R := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu]; field_simp
    linarith
  have hc : Continuous fun u : Rd d => sphPot d (R⁻¹ • (z + r • u - w)) :=
    (continuous_sphPot hd).comp (by fun_prop)
  have hint := integral_mono_ae (integrable_const _)
    (integrable_unitSphereProb_of_continuous hc) hlow
  rw [integral_const, probReal_univ, one_smul] at hint
  linarith

/-- **Blueprint `r1:lem:var` (a)** (explicit uniform form, `d ≥ 2`): there is `K_d` such that for
every LGF, `Var(h_r(z) - h_ρ(w)) ≤ log(ρ/r) + 2 log⁺(|z - w|/ρ) + K_d` for `0 < r ≤ ρ`, and
`≤ log(r/ρ) + 2 log⁺(|z - w|/r) + K_d` for `0 < ρ ≤ r`. -/
theorem exists_variance_sphereAvg_sub_le (hd : 2 ≤ d) :
    ∃ K : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d},
      IsWholeSpaceLGF h P → ∀ {r ρ : ℝ}, 0 < r → 0 < ρ → ∀ z w : Rd d,
        (r ≤ ρ → Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] ≤
          Real.log (ρ / r) + 2 * max 0 (Real.log (‖z - w‖ / ρ)) + K) ∧
        (ρ ≤ r → Var[fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w; P] ≤
          Real.log (r / ρ) + 2 * max 0 (Real.log (‖z - w‖ / r)) + K) := by
  refine ⟨2 * sphEnergy d + 2 * Real.log 3, fun {Ω} _ {P} {h} hh {r ρ} hr hρ z w => ⟨?_, ?_⟩⟩
  · intro hrρ
    have h1 := hh.variance_sphereAvg_sub_le_log hd hr hρ z w
    have h2 : Real.log (‖z - w‖ / ρ + r / ρ + 1) ≤ Real.log (‖z - w‖ / ρ + 2) :=
      Real.log_le_log (by positivity) (by linarith [(div_le_one hρ).2 hrρ])
    have h3 := log_add_two_le (‖z - w‖ / ρ) (by positivity)
    linarith
  · intro hρr
    have e : (fun ω => sphereAvg (h ω) r z - sphereAvg (h ω) ρ w) =
        -fun ω => sphereAvg (h ω) ρ w - sphereAvg (h ω) r z := by
      funext ω; simp only [Pi.neg_apply, neg_sub]
    rw [e, variance_neg]
    have h1 := hh.variance_sphereAvg_sub_le_log hd hρ hr w z
    rw [norm_sub_rev] at h1
    have h2 : Real.log (‖z - w‖ / r + ρ / r + 1) ≤ Real.log (‖z - w‖ / r + 2) :=
      Real.log_le_log (by positivity) (by linarith [(div_le_one hr).2 hρr])
    have h3 := log_add_two_le (‖z - w‖ / r) (by positivity)
    linarith

end HigherDimLQGMetric

import QuantumZipper.Proofs.LQG.AreaP3bLaw
import QuantumZipper.Proofs.LQG.TwoRadiusTilt

/-!
# M4-P3(b), area version, part 3: moments of the rescaled inner masses

For the inner field `Y = innerS X z δ D R` and `W_k = FinArea.massFunC γ S δ k Y`
(`S` with `‖w − z‖ + 2^{-k} < δ` and `Im w ≥ d` on `S`):

* `lintegral_massFunC_inner_le`: `E W_k ≤ e^{γ²K/2} |S|`, `K = 2 log R − log D − log(2d)`;
* `integral_abs_massFunC_step_le`: the two-radius lemma for the inner field,
  `E|W_k − W_{k+1}| ≤ (√(4π c₁ |S|) δ + 2 c₂ |S|) e^{−β' L}`, `L = ½ log(δ/2^{-k})`,
  `β' = min(e₁°, (2−γ)²/4) > 0` (the scale enters only through `δ/2^{-k}`).

Same structure as `FracMom.integral_abs_innerMass_step_le` (boundary case).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId TwoRadiusC FinArea

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- Standing geometric hypotheses at level `k`. -/
structure Setup (z : ℂ) (δ D R d : ℝ) (S : Set ℂ) (k : ℕ) : Prop where
  hδD : δ ≤ D
  hDz : D ≤ z.im
  hDR : ‖z‖ + D ≤ R
  hD1 : D ≤ 1
  hR1 : 1 ≤ R
  hd : 0 < d
  hd1 : 2 * d ≤ 1
  hSd : ∀ w ∈ S, d ≤ w.im
  hSk : ∀ w ∈ S, ‖w - z‖ + radius k < δ

theorem Setup.succ {z : ℂ} {δ D R d : ℝ} {S : Set ℂ} {k : ℕ} (h : Setup z δ D R d S k) :
    Setup z δ D R d S (k + 1) :=
  { h with
    hSk := fun w hw =>
      (calc ‖w - z‖ + radius (k + 1) = ‖w - z‖ + radius k / 2 := by
              rw [AreaExist.aradius_succ]
        _ ≤ ‖w - z‖ + radius k := by linarith [radius_pos k]
        _ < δ := h.hSk w hw : ‖w - z‖ + radius (k + 1) < δ) }

theorem Setup.hδ {z : ℂ} {δ D R d : ℝ} {S : Set ℂ} {k : ℕ} (h : Setup z δ D R d S k)
    (hne : S.Nonempty) : 0 < δ := by
  obtain ⟨w, hw⟩ := hne
  linarith [norm_nonneg (w - z), h.hSk w hw, radius_pos k]

theorem Setup.K_nonneg {z : ℂ} {δ D R d : ℝ} {S : Set ℂ} {k : ℕ} (h : Setup z δ D R d S k)
    (hD : 0 < D) : 0 ≤ 2 * log R - log D - log (2 * d) := by
  have := log_nonneg h.hR1
  have := log_nonpos hD.le h.hD1
  have := log_nonpos (by linarith [h.hd]) h.hd1
  linarith

theorem trlHypC_of_setup [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {z : ℂ}
    {δ D R d : ℝ} {S : Set ℂ} {k : ℕ} (h : Setup z δ D R d S k) :
    TRLHypC P S (2 * radius k) (2 * log R - log D - log (2 * d)) (log 2)
      (fun _ => 1 / 2 * log (δ / radius k)) (vI z δ D R k) (fun _ => (log 2).toNNReal)
      (iU X z δ D R k) (iΔ X z δ D R k) :=
  trlHypC_inner hX (P := P) h.hδD h.hDz h.hDR h.hD1 h.hR1 h.hd h.hd1 h.hSd h.hSk

/-- One-point first moment of the rescaled inner density. -/
theorem integral_wDensC_inner_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {z : ℂ} {δ D R d : ℝ} {S : Set ℂ} {k : ℕ} (h : Setup z δ D R d S k) {w : ℂ}
    (hw : w ∈ S) :
    Integrable (fun ω => wDensC γ δ k (innerS X z δ D R ω) w) P ∧
      ∫ ω, wDensC γ δ k (innerS X z δ D R ω) w ∂P ≤
        exp (γ ^ 2 / 2 * (2 * log R - log D - log (2 * d))) := by
  have hδ : 0 < δ := h.hδ ⟨w, hw⟩
  have hr := radius_pos k
  have hT := trlHypC_of_setup hX (P := P) h
  have hL := hT.lawU w hw
  have hi : Integrable (fun ω => exp (0 + γ * iU X z δ D R k w ω)) P :=
    hL.integrable_fun_comp (TwoRadius.integrable_exp_mul_add_gaussianReal _ γ 0)
  simp only [zero_add] at hi
  refine ⟨hi.const_mul _, ?_⟩
  have h2 := TwoRadius.integral_exp_mul_add_gaussianReal (vI z δ D R k w) γ 0
  simp only [zero_add] at h2
  have h3 : ∫ ω, exp (γ * iU X z δ D R k w ω) ∂P = exp (vI z δ D R k w * γ ^ 2 / 2) := by
    rw [← h2]; exact hL.integral_comp (f := fun x => exp (γ * x)) (by fun_prop)
  simp only [wDensC]
  rw [integral_const_mul]
  change (radius k / δ) ^ (γ ^ 2 / 2) * ∫ ω, exp (γ * iU X z δ D R k w ω) ∂P ≤ _
  rw [h3, rpow_def_of_pos (div_pos hr hδ), ← exp_add]
  apply exp_le_exp.2
  have hv := hT.varU w hw
  have hL0 : 0 ≤ log (δ / radius k) :=
    log_nonneg (by rw [le_div_iff₀ hr]; linarith [norm_nonneg (w - z), h.hSk w hw])
  rw [log_div hr.ne' hδ.ne']
  rw [log_div hδ.ne' hr.ne'] at hv hL0
  have hg : 0 ≤ γ ^ 2 / 2 := by positivity
  nlinarith

/-- `E W_k(S) ≤ e^{γ²K/2} |S|`. -/
theorem lintegral_massFunC_inner_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {z : ℂ} {δ D R d : ℝ} {S : Set ℂ} (hS : MeasurableSet S) {k : ℕ}
    (h : Setup z δ D R d S k) :
    ∫⁻ ω, massFunC γ S δ k (innerS X z δ D R ω) ∂P ≤
      ENNReal.ofReal (exp (γ ^ 2 / 2 * (2 * log R - log D - log (2 * d)))) * volume S := by
  have hU : Measurable (fun q : Ω × ℂ => avgReg (innerS X z δ D R q.1) k q.2) :=
    (measurable_avgReg k).comp (((measurable_innerS hX z δ D R).comp measurable_fst).prodMk
      measurable_snd)
  have hmeas : Measurable (fun q : Ω × ℂ =>
      ENNReal.ofReal (wDensC γ δ k (innerS X z δ D R q.1) q.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul (hU.const_mul _).exp)
  simp only [massFunC]
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  calc ∫⁻ w in S, ∫⁻ ω, ENNReal.ofReal (wDensC γ δ k (innerS X z δ D R ω) w) ∂P
      ≤ ∫⁻ w in S, ENNReal.ofReal (exp (γ ^ 2 / 2 * (2 * log R - log D - log (2 * d)))) :=
        setLIntegral_mono measurable_const fun w hw => by
          obtain ⟨hi, hle⟩ := integral_wDensC_inner_le hX (P := P) γ h hw
          rw [← ofReal_integral_eq_lintegral_ofReal hi
            (ae_of_all _ fun ω => wDensC_nonneg γ (h.hδ ⟨w, hw⟩) k _ w)]
          exact ENNReal.ofReal_le_ofReal hle
    _ = _ := setLIntegral_const _ _

theorem measurable_massFunC_inner (hX : IsFreeGFFModConstH X P) (γ : ℝ) (S : Set ℂ) (z : ℂ)
    (δ D R : ℝ) (k : ℕ) : Measurable (fun ω => massFunC γ S δ k (innerS X z δ D R ω)) :=
  (measurable_massFunC γ S δ k).comp (measurable_innerS hX z δ D R)

theorem ae_massFunC_inner_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) {z : ℂ} {δ D R d : ℝ} {S : Set ℂ} (hS : MeasurableSet S) (hSf : volume S < ∞)
    {k : ℕ} (h : Setup z δ D R d S k) :
    ∀ᵐ ω ∂P, massFunC γ S δ k (innerS X z δ D R ω) < ⊤ :=
  ae_lt_top (measurable_massFunC_inner hX γ S z δ D R k)
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne)
      (lintegral_massFunC_inner_le hX γ hS h))

theorem integrable_massFunC_inner_toReal [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (γ : ℝ) {z : ℂ} {δ D R d : ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) {k : ℕ} (h : Setup z δ D R d S k) :
    Integrable (fun ω => (massFunC γ S δ k (innerS X z δ D R ω)).toReal) P :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_massFunC_inner hX γ S z δ D R k).aemeasurable
    (ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSf.ne)
      (lintegral_massFunC_inner_le hX γ hS h))

set_option maxHeartbeats 400000 in
/-- For a sample with finite mass, `W_k` is the Bochner integral of the density. -/
theorem integrableOn_wDensC_of_lt_top (γ : ℝ) {δ : ℝ} (hδ : 0 < δ) (k : ℕ) {S : Set ℂ}
    {x : FieldSample} (hx : massFunC γ S δ k x < ⊤) :
    IntegrableOn (fun w => wDensC γ δ k x w) S ∧
      ∫ w in S, wDensC γ δ k x w = (massFunC γ S δ k x).toReal := by
  have hnn : 0 ≤ᵐ[volume.restrict S] fun w => wDensC γ δ k x w :=
    ae_of_all _ fun w => wDensC_nonneg γ hδ k x w
  have hm : Measurable (fun w : ℂ => wDensC γ δ k x w) :=
    measurable_const.mul (((RegClosure.measurable_avgReg_slice x k).const_mul γ).exp)
  have hfi : HasFiniteIntegral (fun w : ℂ => wDensC γ δ k x w) (volume.restrict S) :=
    (hasFiniteIntegral_iff_ofReal hnn).2 (by simpa only [massFunC] using hx)
  refine ⟨⟨hm.aestronglyMeasurable, hfi⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  rfl

/-- The TRL density of the inner field is the difference of consecutive rescaled densities. -/
theorem dC_inner_eq (γ : ℝ) {z : ℂ} {δ D R : ℝ} (hδ : 0 < δ) (k : ℕ) (t : ℂ) (ω : Ω) :
    dC (2 * γ) (fun _ => (1 : ℝ)) (fun _ => 1 / 2 * log (δ / radius k))
        (fun _ => (log 2).toNNReal) (iU X z δ D R k) (iΔ X z δ D R k) t ω =
      wDensC γ δ k (innerS X z δ D R ω) t - wDensC γ δ (k + 1) (innerS X z δ D R ω) t := by
  have hr := radius_pos k
  have hlog2 : (0 : ℝ) ≤ log 2 := log_nonneg one_le_two
  simp only [dC, TwoRadius.tiltY, iΔ, iU, one_mul, wDensC]
  rw [Real.coe_toNNReal _ hlog2]
  set A := avgReg (innerS X z δ D R ω) k t
  set B := avgReg (innerS X z δ D R ω) (k + 1) t
  have e1 : (radius k / δ) ^ (γ ^ 2 / 2) * exp (γ * A) =
      exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (δ / radius k)) + 2 * γ / 2 * A) := by
    rw [rpow_def_of_pos (div_pos hr hδ), ← exp_add, log_div hr.ne' hδ.ne',
      log_div hδ.ne' hr.ne']
    congr 1; ring
  have e2 : (radius (k + 1) / δ) ^ (γ ^ 2 / 2) * exp (γ * B) =
      exp (-((2 * γ) ^ 2 / 4) * (1 / 2 * log (δ / radius k)) + 2 * γ / 2 * A) *
        exp (-((2 * γ) ^ 2 / 8 * log 2) + 2 * γ / 2 * (B - A)) := by
    rw [AreaExist.aradius_succ, rpow_def_of_pos (div_pos (div_pos hr two_pos) hδ), ← exp_add,
      ← exp_add, log_div (div_pos hr two_pos).ne' hδ.ne', log_div hr.ne' two_ne_zero,
      log_div hδ.ne' hr.ne']
    congr 1; ring
  rw [e1, e2]
  ring

/-! ### The two-radius step bound for the inner masses -/

/-- **Planar two-radius bound for the rescaled inner mass** (`f ≡ 1`, `M = 1`): the right side of
`TwoRadiusC.trlC_bound_area` with `δ = 2·2^{-k}`, `K = 2 log R − log D − log (2d)`, `W = log 2` and
`Lc = ½ log (δ/2^{-k})`, applied to `trlHypC_inner`. `dC_inner_eq` identifies `∫_S dC` with
`W_k − W_{k+1}` on the a.e. set where both masses are finite
(`ae_massFunC_inner_lt_top`, `integrableOn_wDensC_of_lt_top`). -/
theorem integral_abs_massFunC_step_le [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {z : ℂ} {δ D R d : ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) {k : ℕ} (h : Setup z δ D R d S k)
    (hδ : 0 < δ) :
    ∫ ω, |(massFunC γ S δ k (innerS X z δ D R ω)).toReal -
        (massFunC γ S δ (k + 1) (innerS X z δ D R ω)).toReal| ∂P
      ≤ √(((1 + exp ((2 * γ) ^ 2 / 4 * log 2)) *
            (exp ((2 * γ - max 0 ((3 * γ - 2) / 2)) ^ 2 *
                (2 * log R - log D - log (2 * d)) / 2) *
            exp ((2 * γ ^ 2 - (max 0 ((3 * γ - 2) / 2)) ^ 2) *
              (1 / 2 * log (δ / radius k))))) *
            (π * (2 * radius k) ^ 2 * volume.real S))
        + 2 * (exp ((2 * γ / 2 + (2 - γ) / 2) ^ 2 *
              (2 * log R - log D - log (2 * d)) / 2) *
            exp (-((2 - γ) ^ 2 / 4) * (1 / 2 * log (δ / radius k)))) * volume.real S := by
  have hr := radius_pos k
  have hb := trlC_bound_area (P := P) hγ hγ2 (δ := 2 * radius k) (M := 1)
    (Lc := 1 / 2 * log (δ / radius k)) (f := fun _ => (1 : ℝ)) (by positivity) hS hSf
    measurable_const (fun _ => by simp) (trlHypC_of_setup hX (P := P) h)
  have hEq : ∫ ω, |(massFunC γ S δ k (innerS X z δ D R ω)).toReal -
        (massFunC γ S δ (k + 1) (innerS X z δ D R ω)).toReal| ∂P =
      ∫ ω, |∫ t in S, dC (2 * γ) (fun _ => (1 : ℝ)) (fun _ => 1 / 2 * log (δ / radius k))
        (fun _ => (log 2).toNNReal) (iU X z δ D R k) (iΔ X z δ D R k) t ω| ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [ae_massFunC_inner_lt_top hX γ hS hSf h,
      ae_massFunC_inner_lt_top hX γ hS hSf h.succ] with ω h1 h2
    have h1' := integrableOn_wDensC_of_lt_top γ hδ k h1
    have h2' := integrableOn_wDensC_of_lt_top γ hδ (k + 1) h2
    have hkey : (massFunC γ S δ k (innerS X z δ D R ω)).toReal -
        (massFunC γ S δ (k + 1) (innerS X z δ D R ω)).toReal =
        ∫ t in S, dC (2 * γ) (fun _ => (1 : ℝ)) (fun _ => 1 / 2 * log (δ / radius k))
          (fun _ => (log 2).toNNReal) (iU X z δ D R k) (iΔ X z δ D R k) t ω := by
      rw [← h1'.2, ← h2'.2, ← integral_sub h1'.1 h2'.1]
      exact setIntegral_congr_fun hS fun t _ => (dC_inner_eq γ hδ k t ω).symm
    exact congrArg abs hkey
  refine hEq.trans_le ?_
  refine hb.trans ?_
  simp only [one_pow, one_mul]
  exact le_rfl

end AreaP3b
end QuantumZipper

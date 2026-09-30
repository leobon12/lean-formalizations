import QuantumZipper.Proofs.Thm18.RT5FarCore
import QuantumZipper.Proofs.Thm18.R18T6Curve
import QuantumZipper.Proofs.Thm18.R18RTMaskAsm
import QuantumZipper.Proofs.RS.TipA

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT5 FarPull, driver facts

The zipped driver `V` of `zipWeldUp` along `(T, W')` at a configuration with driver `D`:
`V s = W'(T − max s 0) − W' T` for `s ≤ T` and `D(s − T) − W' T` for `s > T` (the formula of
`zipWeldUp`). When its canonical rescaling agrees with a good driver `W` on `[0,∞)` (T7b), `V` is
the Brownian rescaling of `W` (so it has radial limits everywhere), its reversal on `[0,T]` is
`W'`, and its shift by `T` is `D`. Loewner concatenation (Rohde–Schramm, *Basic properties of
SLE*, proof of Thm 6.1, p. 23; `RS.fwdMapInv_add_shift`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- The zipped (not yet rescaled) driver of `zipWeldUp γ T W'` at a configuration with driver
`D`. -/
def rt5V (T : ℝ) (W' D : ℝ → ℝ) : ℝ → ℝ :=
  fun s => if s ≤ T then W' (T - max s 0) - W' T else D (s - T) - W' T

theorem rt5V_zipWeldUp (γ T : ℝ) (W' : ℝ → ℝ) (c : FieldSample × (ℝ → ℝ)) :
    (zipWeldUp γ T W' c).2 = rt5V T W' c.2 := rfl

section
variable {T : ℝ} {W' D W : ℝ → ℝ} {a : ℝ}

/-- `V` is the rescaled `W`, extended by `0` to negative times. -/
theorem rt5V_eq_scale (hT : 0 ≤ T) (hW0 : W 0 = 0) (ha : 0 < a)
    (hV : ∀ u : ℝ, 0 ≤ u → rt5V T W' D (a ^ 2 * max u 0) / a = W u) (r : ℝ) :
    rt5V T W' D r = (fun r => W (a⁻¹ ^ 2 * r) / a⁻¹) (max r 0) := by
  have ha0 : a ≠ 0 := ha.ne'
  rcases le_or_gt 0 r with hr | hr
  · have h := hV (a⁻¹ ^ 2 * r) (by positivity)
    have e : a ^ 2 * max (a⁻¹ ^ 2 * r) 0 = r := by
      rw [max_eq_left (by positivity)]; field_simp
    rw [e] at h
    simp only [max_eq_left hr, ← h]
    field_simp
  · have hrT : r ≤ T := by linarith
    simp only [rt5V, if_pos hrT, max_eq_right hr.le, sub_zero, sub_self, mul_zero, hW0,
      zero_div]

theorem continuous_rt5V (hT : 0 ≤ T) (hWc : Continuous W) (hW0 : W 0 = 0) (ha : 0 < a)
    (hV : ∀ u : ℝ, 0 ≤ u → rt5V T W' D (a ^ 2 * max u 0) / a = W u) :
    Continuous (rt5V T W' D) := by
  have e : rt5V T W' D = fun r => W (a⁻¹ ^ 2 * max r 0) / a⁻¹ :=
    funext fun r => rt5V_eq_scale hT hW0 ha hV r
  rw [e]; fun_prop

theorem rt5V_zero (hT : 0 ≤ T) : rt5V T W' D 0 = 0 := by
  simp [rt5V, hT]

/-- The reversal of `V` on `[0,T]` is `W'`. -/
theorem rt5V_rev (hW'0 : W' 0 = 0) (hT : 0 ≤ T) :
    EqOn (fun r => rt5V T W' D (T - r) - rt5V T W' D T) W' (Icc 0 T) := by
  intro r hr
  have h1 : T - r ≤ T := by linarith [hr.1]
  simp only [rt5V, if_pos h1, if_pos le_rfl, max_eq_left (sub_nonneg.2 hr.2), max_eq_left hT,
    sub_self, hW'0]
  ring_nf

/-- The shift of `V` by `T` is `D` on `[0,∞)`. -/
theorem rt5V_shift (hW'0 : W' 0 = 0) (hT : 0 ≤ T) (hD0 : D 0 = 0) :
    EqOn (RS.shiftDrive (rt5V T W' D) T) D (Ici 0) := by
  intro r hr
  simp only [RS.shiftDrive]
  rcases (show (0 : ℝ) ≤ r from hr).lt_or_eq with hr | rfl
  · have h1 : ¬ T + r ≤ T := by linarith
    simp only [rt5V, if_neg h1, if_pos le_rfl, max_eq_left hT, sub_self, hW'0,
      show T + r - T = r by ring]
    ring
  · simp [hD0]

/-- `f̂_T` of `V` is the reverse map of `W'`. -/
theorem fwdMapInv_rt5V_eq (hVc : Continuous (rt5V T W' D)) (hT : 0 ≤ T) (hW'0 : W' 0 = 0)
    {w : ℂ} (hw : w ∈ H) : fwdMapInv (rt5V T W' D) T w = revMap W' T w := by
  rw [UnzipInvariance.fwdMapInv_eq_revMap_timeRev _ hVc (rt5V_zero hT) hT hw]
  exact ReverseFlow.revMap_congr_drive w (rt5V_rev hW'0 hT)

/-- Radial limits of `V` (from those of `W`). -/
theorem tendsto_fwdMapInv_rt5V (hT : 0 ≤ T) (hW : RS.RadialGood W) (ha : 0 < a)
    (hV : ∀ u : ℝ, 0 ≤ u → rt5V T W' D (a ^ 2 * max u 0) / a = W u) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun y : ℝ => fwdMapInv (rt5V T W' D) t (y * Complex.I)) (𝓝[>] 0)
        (𝓝 (trace W (a⁻¹ ^ 2 * t) / ((a⁻¹ : ℝ) : ℂ))) ∧
      trace (rt5V T W' D) t = trace W (a⁻¹ ^ 2 * t) / ((a⁻¹ : ℝ) : ℂ) := by
  have hWc := hW.1
  have hW0 := hW.2.1
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  have hVc := continuous_rt5V hT hWc hW0 ha hV
  have hsc := RS.trace_scale hWc hW0 hai ht (hW.tendsto (by positivity))
  have hSc : Continuous fun r => W (a⁻¹ ^ 2 * r) / a⁻¹ := by fun_prop
  have hEq : EqOn (rt5V T W' D) (fun r => W (a⁻¹ ^ 2 * r) / a⁻¹) (Ici 0) := fun r hr => by
    rw [rt5V_eq_scale hT hW0 ha hV r, max_eq_left (show (0 : ℝ) ≤ r from hr)]
  have hT' : Tendsto (fun y : ℝ => fwdMapInv (rt5V T W' D) t (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace W (a⁻¹ ^ 2 * t) / ((a⁻¹ : ℝ) : ℂ))) := by
    refine hsc.1.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    exact (RS.fwdMapInv_congr_Ici hVc (rt5V_zero hT) hSc (by simp [hW0]) hEq ht
      (RS.mul_I_mem_H hy)).symm
  exact ⟨hT', hT'.limUnder_eq⟩

/-- Radial limits of the unzipped driver `D = outDrv W s b`. -/
theorem tendsto_fwdMapInv_outDrv (hW : RS.RadialGood W) (hinj : InjOn (trace W) (Ici 0))
    (hH : ∀ t > (0 : ℝ), trace W t ∈ H) {s b : ℝ} (hs : 0 ≤ s)
    (hhull : fwdHull W s = trace W '' Ioc 0 s) (hb : 0 < b) {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun y : ℝ => fwdMapInv (outDrv W s b) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (trace (outDrv W s b) u)) := by
  have hWc := hW.1
  set V := RS.shiftDrive W s with hVdef
  have hVc : Continuous V := RS.continuous_shiftDrive hWc s
  have hV0 : V 0 = 0 := RS.shiftDrive_zero W s
  have hDc : Continuous (outDrv W s b) := by unfold outDrv; fun_prop
  have hD0 : outDrv W s b 0 = 0 := by simp [outDrv]
  have hSc : Continuous fun r => V (b ^ 2 * r) / b := by fun_prop
  have hEq : EqOn (outDrv W s b) (fun r => V (b ^ 2 * r) / b) (Ici 0) := fun r hr => by
    have hr0 : (0 : ℝ) ≤ r := hr
    simp only [outDrv, hVdef, RS.shiftDrive, max_eq_left hr0,
      max_eq_left (mul_nonneg (sq_nonneg b) hr0)]
  have hlim := tendsto_fwdMapInv_shift hW hinj hH hhull hs (mul_nonneg (sq_nonneg b) hu)
  have hsc := RS.trace_scale hVc hV0 hb hu hlim
  have hT' : Tendsto (fun y : ℝ => fwdMapInv (outDrv W s b) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 ((if b ^ 2 * u = 0 then 0 else fwdMap W s (trace W (s + b ^ 2 * u))) / b)) := by
    refine hsc.1.congr' (eventually_mem_nhdsWithin.mono fun y hy => ?_)
    exact (RS.fwdMapInv_congr_Ici hDc hD0 hSc (by simp [hV0]) hEq hu (RS.mul_I_mem_H hy)).symm
  have e := hT'.limUnder_eq
  unfold trace
  rw [e]
  exact hT'

end

end R18
end QuantumZipper

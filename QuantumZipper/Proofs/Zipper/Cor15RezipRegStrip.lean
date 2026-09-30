import QuantumZipper.Proofs.GFF.CoordRegEnergyBasic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Corollary 1.5, input R: strip bounds from polynomial strip masses

Task COR15-R. The general RC3 theorem (`CoordReg.ae_evalReg_coordChange_revMap_gen`) asks for
the log-weighted boundary-layer bound `CoordReg.StripBound ν c γ`:
`∫_{Im z ≤ s} (1 + |log Im z|) dν ≤ c s^γ` for `0 < s ≤ 1`. `stripBound_of_pow` derives it from
a polynomial bound on the strip masses, `ν{Im < s} ≤ A s^a` (all `s > 0`), with `γ = a/2`, by
the layer-cake formula for `max(log(s / Im z), 0)` (as in
`CoordRegComp.stripBound_foldedCircle`). For the pushed measures `ν = σ.map f` of (R) the strip
masses are bounded by `Cor15Group.map_revMapInv_im_le` (`Cor15RezipRegDist.lean`).
**Own elementary argument** (cost rule of `AGENT_GUIDE.md`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Real Topology

namespace QuantumZipper
namespace Cor15Group

open CoordReg

/-- Layer-cake bound: `∫ max(log(s / |Im|), 0) dν ≤ A s^a / a`. -/
theorem lintegral_logRatio_le_of_pow {ν : Measure ℂ} (hνH : ∀ᵐ z ∂ν, z ∈ H) {A a s : ℝ}
    (hA : 0 ≤ A) (ha : 0 < a) (hs : 0 < s)
    (h : ∀ τ : ℝ, 0 < τ → ν {z | z.im < τ} ≤ ENNReal.ofReal (A * τ ^ a)) :
    ∫⁻ u, ENNReal.ofReal (max (Real.log (s / |u.im|)) 0) ∂ν ≤
      ENNReal.ofReal (A * s ^ a / a) := by
  set g : ℂ → ℝ := fun u => max (Real.log (s / |u.im|)) 0 with hg
  have hmeas : Measurable g :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hnn : 0 ≤ᵐ[ν] g := ae_of_all _ fun x => (le_max_right _ _ : (0 : ℝ) ≤ g x)
  rw [lintegral_eq_lintegral_meas_lt _ hnn hmeas.aemeasurable]
  have hC : Integrable (fun t : ℝ => A * s ^ a * Real.exp (-a * t))
      (volume.restrict (Ioi 0)) :=
    (exp_neg_integrableOn_Ioi 0 ha).const_mul _
  have hval : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (A * s ^ a * Real.exp (-a * t)) =
      ENNReal.ofReal (A * s ^ a / a) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hC (ae_of_all _ fun t => by positivity),
      integral_const_mul, integral_exp_mul_Ioi (by linarith) 0,
      show (-a) * 0 = 0 by ring, Real.exp_zero]
    congr 1
    field_simp
  rw [← hval]
  refine setLIntegral_mono (ENNReal.measurable_ofReal.comp (measurable_const.mul
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)))) fun t (ht : 0 < t) => ?_
  have hsub : {x : ℂ | t < g x} ≤ᵐ[ν] {x | x.im < s * Real.exp (-t)} := by
    filter_upwards [hνH] with x hxH hx
    have hx0 : 0 < x.im := hxH
    change t < max (Real.log (s / |x.im|)) 0 at hx
    show x.im < s * Real.exp (-t)
    rcases lt_max_iff.1 hx with hx | hx
    · rw [abs_of_pos hx0] at hx
      have h1 := (Real.lt_log_iff_exp_lt (div_pos hs hx0)).1 hx
      rw [lt_div_iff₀ hx0] at h1
      rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos t)]
      linarith [mul_comm x.im (Real.exp t)]
    · linarith
  refine (measure_mono_ae hsub).trans ((h _ (by positivity)).trans (le_of_eq ?_))
  congr 1
  rw [Real.mul_rpow hs.le (Real.exp_pos _).le, ← Real.exp_mul]
  ring_nf

/-- **Strip bound from polynomial strip masses** (own elementary argument). -/
theorem stripBound_of_pow {ν : Measure ℂ} [IsFiniteMeasure ν] (hνH : ∀ᵐ z ∂ν, z ∈ H)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (h : ∀ τ : ℝ, 0 < τ → ν {z | z.im < τ} ≤ ENNReal.ofReal (A * τ ^ a)) :
    StripBound ν (A * (2 ^ a * (1 + 2 / a) + 1 / a)) (a / 2) := by
  intro s hs hs1
  set S : Set ℂ := {x : ℂ | x.im < 2 * s} with hSdef
  set gf : ℂ → ℝ := fun u => max (Real.log (s / |u.im|)) 0 with hgf
  have hgm : Measurable gf :=
    (Real.measurable_log.comp (measurable_const.div
      (continuous_abs.measurable.comp Complex.measurable_im))).max measurable_const
  have hg0 : ∀ u, 0 ≤ gf u := fun u => le_max_right _ _
  have hgl := lintegral_logRatio_le_of_pow hνH hA ha hs h
  have hgi : Integrable gf ν :=
    ⟨hgm.aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hg0)]
      exact lt_of_le_of_lt hgl ENNReal.ofReal_lt_top⟩
  have hgI : ∫ u, gf u ∂ν ≤ A * s ^ a / a := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hg0) hgm.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hgl
  have hSm : MeasurableSet S := measurableSet_lt Complex.measurable_im measurable_const
  have hSν : ν.real S ≤ A * (2 * s) ^ a := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) (h _ (by linarith))
  set L := 1 + |Real.log s| with hL
  have hL0 : 0 ≤ L := by positivity
  have hpt : ∀ᵐ u ∂ν, {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) u ≤
      S.indicator (fun _ => L) u + gf u := by
    filter_upwards [hνH] with u hu
    have hu0 : 0 < u.im := hu
    by_cases hh : u.im ≤ s
    · have hS' : u ∈ S := by show u.im < 2 * s; linarith
      rw [indicator_of_mem (show u ∈ {z : ℂ | z.im ≤ s} from hh), indicator_of_mem hS']
      have e1 : Real.log (s / |u.im|) = Real.log s - Real.log u.im := by
        rw [abs_of_pos hu0, Real.log_div hs.ne' hu0.ne']
      have e2 : |Real.log u.im| = -Real.log u.im :=
        abs_of_nonpos (Real.log_nonpos hu0.le (hh.trans hs1))
      have e3 : |Real.log s| = -Real.log s := abs_of_nonpos (Real.log_nonpos hs.le hs1)
      have e4 : Real.log (s / |u.im|) ≤ gf u := le_max_left _ _
      rw [hL]
      linarith
    · rw [indicator_of_notMem (show u ∉ {z : ℂ | z.im ≤ s} from hh)]
      exact add_nonneg (indicator_nonneg (fun _ _ => hL0) _) (hg0 u)
  have hle : ∫ u, {z : ℂ | z.im ≤ s}.indicator (fun z => 1 + |Real.log z.im|) u ∂ν ≤
      ∫ u, (S.indicator (fun _ => L) u + gf u) ∂ν := integral_mono_of_nonneg
    (ae_of_all _ fun u => indicator_nonneg (fun z _ => by positivity) u)
    ((((integrable_const L).indicator hSm).add hgi :
      Integrable (fun u => S.indicator (fun _ => L) u + gf u) ν)) hpt
  rw [integral_add ((integrable_const L).indicator hSm) hgi, integral_indicator_const L hSm,
    smul_eq_mul] at hle
  refine hle.trans ?_
  -- numerics: `s^a (1 + |log s|) ≤ s^{a/2} (1 + 2/a)` and `s^a ≤ s^{a/2}`
  set q := s ^ (a / 2) with hq
  have hq0 : 0 ≤ q := Real.rpow_nonneg hs.le _
  have hq1 : q ≤ 1 := Real.rpow_le_one hs.le hs1 (by positivity)
  have hsa : s ^ a = q * q := by
    rw [hq, ← Real.rpow_add hs]; congr 1; ring
  have hlog : |Real.log s| * q ≤ 2 / a := by
    have := Real.abs_log_mul_self_rpow_lt s (a / 2) hs hs1 (by positivity)
    rw [abs_mul, abs_of_nonneg hq0, one_div_div] at this
    exact this.le
  have h2s : (2 * s) ^ a = 2 ^ a * (q * q) := by
    rw [Real.mul_rpow (by norm_num) hs.le, hsa]
  have h2a : 0 ≤ (2 : ℝ) ^ a := by positivity
  have hLq : q * L ≤ 1 + 2 / a := by
    rw [hL, mul_add, mul_one]
    nlinarith [mul_comm q |Real.log s|]
  have hqq : q * q ≤ q := by nlinarith
  calc ν.real S * L + ∫ u, gf u ∂ν ≤ A * (2 * s) ^ a * L + A * s ^ a / a :=
        add_le_add (mul_le_mul_of_nonneg_right hSν hL0) hgI
    _ = A * 2 ^ a * q * (q * L) + A * (q * q) / a := by rw [h2s, hsa]; ring
    _ ≤ A * 2 ^ a * q * (1 + 2 / a) + A * q / a := by
        gcongr
    _ = A * (2 ^ a * (1 + 2 / a) + 1 / a) * s ^ (a / 2) := by rw [← hq]; ring

/-- **Negative moments of `Im` from polynomial strip masses** (own elementary argument):
if `ν{Im < τ} ≤ A τ^a` and `0 < b < a`, then `∫ (Im z)^{-b} dν < ∞`. -/
theorem lintegral_im_rpow_neg_ne_top {ν : Measure ℂ} [IsFiniteMeasure ν] (hνH : ∀ᵐ z ∂ν, z ∈ H)
    {A a b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) (hab : b < a)
    (h : ∀ τ : ℝ, 0 < τ → ν {z | z.im < τ} ≤ ENNReal.ofReal (A * τ ^ a)) :
    ∫⁻ z, ENNReal.ofReal (z.im ^ (-b)) ∂ν ≠ ⊤ := by
  set f : ℂ → ℝ := fun z => z.im ^ (-b) with hf
  have hfm : Measurable f := Complex.measurable_im.pow_const _
  have hnn : 0 ≤ᵐ[ν] f := by
    filter_upwards [hνH] with z hz
    exact Real.rpow_nonneg (le_of_lt hz) _
  rw [lintegral_eq_lintegral_meas_lt _ hnn hfm.aemeasurable,
    ← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine ne_top_of_le_ne_top ?_ (lintegral_union_le _ _ _)
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · refine ne_top_of_le_ne_top ?_
      (setLIntegral_mono measurable_const fun t _ => measure_mono (subset_univ _))
    rw [setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  · have hab' : -(a / b) < -1 := by
      have := (one_lt_div hb).2 hab
      linarith
    have hint : IntegrableOn (fun t : ℝ => A * t ^ (-(a / b))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt hab' one_pos).const_mul A
    refine ne_top_of_le_ne_top hint.lintegral_lt_top.ne
      (setLIntegral_mono ((measurable_id.pow_const _).const_mul A).ennreal_ofReal
        fun t (ht : 1 < t) => ?_)
    have ht0 : 0 < t := by linarith
    have hsub : {z : ℂ | t < f z} ≤ᵐ[ν] {z | z.im < t ^ (-(1 / b))} := by
      filter_upwards [hνH] with z hz hzt
      have hz0 : 0 < z.im := hz
      change t < z.im ^ (-b) at hzt
      show z.im < t ^ (-(1 / b))
      by_contra hcon
      push Not at hcon
      have h1 : z.im ^ (-b) ≤ (t ^ (-(1 / b))) ^ (-b) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos ht0 _) hcon (by linarith)
      rw [← Real.rpow_mul ht0.le, show -(1 / b) * -b = 1 by field_simp, Real.rpow_one] at h1
      linarith
    refine (measure_mono_ae hsub).trans ((h _ (Real.rpow_pos_of_pos ht0 _)).trans
      (le_of_eq ?_))
    rw [← Real.rpow_mul ht0.le]
    congr 2
    field_simp

end Cor15Group
end QuantumZipper

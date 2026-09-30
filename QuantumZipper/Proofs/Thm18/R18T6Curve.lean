import QuantumZipper.Proofs.Thm18.R18T6Down
import QuantumZipper.Proofs.Thm18.R18AreaNullScale
import QuantumZipper.Proofs.RS.TraceShift
import QuantumZipper.Proofs.RS.TipCore
import QuantumZipper.Proofs.RS.GenerationBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18 T6 (R18-AREAREAD), part 3: the unzipped curve carries no transported area

After unzipping `η` up to capacity time `T`, the remaining curve is `f_T(η[T,∞))` (Rohde–Schramm,
*Basic properties of SLE*, the trace identity `γ̂_s(t) = g_s ∘ g_{s+t}⁻¹`, proof of Thm 6.1 p. 23;
here `RS.fwdMapInv_shift_eq`), rescaled by `1/a`. Hence its preimage under `z ↦ f_T(z)/a` in
`ℍ ∖ K_T` lies in `η`, and the transported area of the unzipped curve is at most the area of `η`,
which is `0` (Sheffield p. 48, T1). Deterministic, for a driver whose trace exists at all times
(`RS.RadialGood`), is simple, stays in `ℍ` at positive times, and whose hulls are the trace
images. Own elementary argument (continuity of `f̂_T` on `ℍ`).
-/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

variable {W : ℝ → ℝ} {T a : ℝ}

/-- The trace at a point of `[0,∞)` lies on the curve. -/
theorem trace_mem_curveOf (hc : ContinuousOn (trace W) (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    trace W t ∈ curveOf W := by
  have hs : range (fun q : ℚ≥0 => (1 : ℝ) * (q : ℝ)) ⊆ Ici 0 := by
    rintro _ ⟨q, rfl⟩
    simp only [mem_Ici, one_mul]
    exact q.cast_nonneg
  have h := closure_image_eq_of_dense hc hs (Ici_subset_closure_range_mul one_pos)
  have e : trace W '' range (fun q : ℚ≥0 => (1 : ℝ) * (q : ℝ)) =
      range fun q : ℚ≥0 => trace W (q : ℝ) := by
    rw [← range_comp]; simp [Function.comp_def]
  rw [e] at h
  unfold curveOf
  rw [h]
  exact subset_closure ⟨t, ht, rfl⟩

/-- Later points of a simple trace lie outside the earlier hull. -/
theorem trace_mem_compl_hull (hinj : InjOn (trace W) (Ici 0)) (hH : ∀ t > (0 : ℝ), trace W t ∈ H)
    (hhull : fwdHull W T = trace W '' Ioc 0 T) (hT : 0 ≤ T) {u : ℝ} (hu : 0 < u) :
    trace W (T + u) ∈ H \ fwdHull W T := by
  refine ⟨hH _ (by linarith), fun hK => ?_⟩
  rw [hhull] at hK
  obtain ⟨s, hs, hse⟩ := hK
  have := hinj (show (0 : ℝ) ≤ s from hs.1.le) (show (0 : ℝ) ≤ T + u by linarith) hse
  linarith [hs.2]

/-- The radial limits of the shifted driver `V = W(T+·) − W(T)`. -/
theorem tendsto_fwdMapInv_shift (hW : RS.RadialGood W) (hinj : InjOn (trace W) (Ici 0))
    (hH : ∀ t > (0 : ℝ), trace W t ∈ H) (hhull : fwdHull W T = trace W '' Ioc 0 T) (hT : 0 ≤ T)
    {u : ℝ} (hu : 0 ≤ u) :
    Tendsto (fun y : ℝ => fwdMapInv (RS.shiftDrive W T) u (y * Complex.I)) (𝓝[>] 0)
      (𝓝 (if u = 0 then 0 else fwdMap W T (trace W (T + u)))) := by
  have hWc := hW.1
  have hW0 := hW.2.1
  have heq : (fun y : ℝ => fwdMapInv (RS.shiftDrive W T) u (y * Complex.I)) =ᶠ[𝓝[>] 0]
      fun y : ℝ => fwdMap W T (fwdMapInv W (T + u) (y * Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact RS.fwdMapInv_shift_eq hWc hW0 hT hu (RS.mul_I_mem_H hy)
  refine Tendsto.congr' heq.symm ?_
  rcases hu.lt_or_eq with hu | rfl
  · rw [if_neg hu.ne']
    have hp := trace_mem_compl_hull hinj hH hhull hT hu
    have hca : ContinuousAt (fwdMap W T) (trace W (T + u)) :=
      (E6.continuousOn_fwdMap_compl hWc hT).continuousAt
        ((FwdHolo.isOpen_compl_fwdHull hWc hT).mem_nhds hp)
    exact hca.tendsto.comp (hW.tendsto (by linarith))
  · rw [if_pos rfl, add_zero]
    have heq2 : (fun y : ℝ => fwdMap W T (fwdMapInv W T (y * Complex.I))) =ᶠ[𝓝[>] 0]
        fun y : ℝ => (y : ℂ) * Complex.I := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact RS.fwdMap_fwdMapInv hWc hW0 hT (RS.mul_I_mem_H hy)
    refine Tendsto.congr' heq2.symm ?_
    have : Tendsto (fun y : ℝ => (y : ℂ) * Complex.I) (𝓝 0) (𝓝 ((0 : ℝ) * Complex.I)) :=
      ((Complex.continuous_ofReal.mul continuous_const).tendsto 0)
    simpa using this.mono_left nhdsWithin_le_nhds

/-- **The unzipped curve pulls back into `η`**: a point `z ∈ ℍ ∖ K_T` with `f_T(z)/a` on the
curve of the unzipped, rescaled driver lies on `η`. -/
theorem mem_curveOf_of_unzip (hW : RS.RadialGood W) (hinj : InjOn (trace W) (Ici 0))
    (hH : ∀ t > (0 : ℝ), trace W t ∈ H) (hhull : fwdHull W T = trace W '' Ioc 0 T) (hT : 0 ≤ T)
    (ha : 0 < a) {z : ℂ} (hz : z ∈ H \ fwdHull W T)
    (hmem : ((a : ℂ))⁻¹ * fwdMap W T z ∈
      curveOf fun s => (W (T + max (a ^ 2 * max s 0) 0) - W T) / a) :
    z ∈ curveOf W := by
  have hWc := hW.1
  have hW0 := hW.2.1
  set V := RS.shiftDrive W T with hVdef
  have hVc : Continuous V := RS.continuous_shiftDrive hWc T
  have hV0 : V 0 = 0 := RS.shiftDrive_zero W T
  set W' : ℝ → ℝ := fun s => (W (T + max (a ^ 2 * max s 0) 0) - W T) / a with hW'def
  set R : Set ℂ := (fun u : ℝ => fwdMap W T (trace W (T + u)) / a) '' Ioi 0 with hRdef
  -- the trace of `W'` at rational times
  have htr : ∀ q : ℚ≥0, trace W' (q : ℝ) = 0 ∨ trace W' (q : ℝ) ∈ R := by
    intro q
    have hq : (0 : ℝ) ≤ q := q.cast_nonneg
    have hW'c : Continuous W' := by rw [hW'def]; fun_prop
    have hW''c : Continuous fun r => V (a ^ 2 * r) / a := by fun_prop
    have hcg : trace W' q = trace (fun r => V (a ^ 2 * r) / a) q := by
      refine RS.trace_congr_drive hW'c (by simp [hW'def]) hW''c (by simp [hV0]) hq
        fun r hr => ?_
      have hr0 : 0 ≤ r := hr.1
      simp only [hW'def, hVdef, RS.shiftDrive, max_eq_left hr0,
        max_eq_left (mul_nonneg (sq_nonneg a) hr0)]
    have hlim := tendsto_fwdMapInv_shift hW hinj hH hhull hT
      (mul_nonneg (sq_nonneg a) hq)
    have hsc := RS.trace_scale hVc hV0 ha hq hlim
    have hval : trace W' q =
        (if a ^ 2 * (q : ℝ) = 0 then 0 else fwdMap W T (trace W (T + a ^ 2 * q))) / a := by
      rw [hcg]
      exact hsc.1.limUnder_eq
    by_cases h0 : a ^ 2 * (q : ℝ) = 0
    · left; rw [hval, if_pos h0, zero_div]
    · right
      rw [hval, if_neg h0]
      exact ⟨a ^ 2 * q, lt_of_le_of_ne (mul_nonneg (sq_nonneg a) hq) (Ne.symm h0), rfl⟩
  have hsub : range (fun q : ℚ≥0 => trace W' (q : ℝ)) ⊆ {0} ∪ R := by
    rintro _ ⟨q, rfl⟩
    rcases htr q with h | h
    · exact Or.inl h
    · exact Or.inr h
  set p : ℂ := ((a : ℂ))⁻¹ * fwdMap W T z with hpdef
  have hfz : fwdMap W T z ∈ H := FwdHolo.mapsTo_fwdMap hWc hT hz
  have hmulH : ∀ w ∈ H, ((a : ℂ))⁻¹ * w ∈ H := fun w hw => by
    show 0 < (((a : ℂ))⁻¹ * w).im
    rw [← Complex.ofReal_inv, Complex.im_ofReal_mul]
    exact mul_pos (inv_pos.2 ha) hw
  have hpH : p ∈ H := hmulH _ hfz
  have hpR : p ∈ closure R := by
    have h1 : p ∈ closure ({0} ∪ R) := closure_mono hsub hmem
    rw [closure_union, closure_singleton] at h1
    rcases h1 with h | h
    · exfalso
      have : (0 : ℝ) < p.im := hpH
      rw [mem_singleton_iff.1 h] at this
      simp at this
    · exact h
  have hRH : R ⊆ H := by
    rintro _ ⟨u, hu, rfl⟩
    show fwdMap W T (trace W (T + u)) / (a : ℂ) ∈ H
    rw [div_eq_inv_mul]
    exact hmulH _ (FwdHolo.mapsTo_fwdMap hWc hT (trace_mem_compl_hull hinj hH hhull hT hu))
  set g : ℂ → ℂ := fun w => fwdMapInv W T ((a : ℂ) * w) with hgdef
  have hmulH' : ∀ w ∈ H, (a : ℂ) * w ∈ H := fun w hw => by
    show 0 < ((a : ℂ) * w).im
    rw [Complex.im_ofReal_mul]
    exact mul_pos ha hw
  have hg : ContinuousOn g H :=
    (E6.continuousOn_fwdMapInv_H hWc hW0 hT).comp (continuous_const.mul continuous_id).continuousOn
      fun w hw => hmulH' w hw
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha.ne'
  have hgR : g '' R ⊆ curveOf W := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    have hp := trace_mem_compl_hull hinj hH hhull hT hu
    simp only [hgdef]
    rw [mul_div_cancel₀ _ hac, RS.fwdMapInv_fwdMap hWc hW0 hT hp]
    have hu' : 0 < u := hu
    exact trace_mem_curveOf hW.2.2.2.1 (by linarith)
  have hgp : g p ∈ closure (g '' R) := ((hg p hpH).mono hRH).mem_closure_image hpR
  have hgpz : g p = z := by
    simp only [hgdef, hpdef]
    rw [← mul_assoc, mul_inv_cancel₀ hac, one_mul, RS.fwdMapInv_fwdMap hWc hW0 hT hz]
  rw [← hgpz]
  exact closure_minimal hgR isClosed_closure hgp

/-- **The curve of `Z^LEN_{−ℓ} c` carries no carried area**, when `η` carries none (T1) and the
driver of `c` has a simple trace in `ℍ` whose hulls are the trace images. -/
theorem zipLenDownA_curve_null {γ ℓ : ℝ} {c : AreaConfig} (hW : RS.RadialGood c.drv)
    (hinj : InjOn (trace c.drv) (Ici 0)) (hH : ∀ t > (0 : ℝ), trace c.drv t ∈ H)
    (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull c.drv t = trace c.drv '' Ioc 0 t)
    (hnull : c.area (curveOf c.drv) = 0)
    (ha : 0 < areaScale (zipCapDownA γ (downTime γ ℓ c) c).area) :
    (zipLenDownA γ ℓ c).area (curveOf (zipLenDownA γ ℓ c).drv) = 0 := by
  set T := downTime γ ℓ c with hTdef
  have hT : 0 ≤ T := lenTimeOpen_nonneg _ _ _
  set a := areaScale (zipCapDownA γ T c).area with hadef
  have hWc := hW.1
  have hCm : MeasurableSet (curveOf (zipLenDownA γ ℓ c).drv) := isClosed_closure.measurableSet
  have hmm : Measurable fun z : ℂ => ((a : ℂ))⁻¹ * z := measurable_const.mul measurable_id
  set S := (fun z : ℂ => ((a : ℂ))⁻¹ * z) ⁻¹' curveOf (zipLenDownA γ ℓ c).drv with hSdef
  have hSm : MeasurableSet S := hmm hCm
  rw [zipLenDownA_area, ← hTdef, ← hadef, Measure.map_apply hmm hCm, ← hSdef,
    zipCapDownA_area_eq_areaTransport]
  unfold E6.areaTransport
  rw [Measure.map_apply_of_aemeasurable (E6.aemeasurable_fwdMap_restrict hWc hT _) hSm,
    Measure.restrict_apply' (E6.measurableSet_compl_fwdHull hWc hT)]
  refine measure_mono_null (fun z hz => ?_) hnull
  exact mem_curveOf_of_unzip hW hinj hH (hhull T hT) hT ha hz.2 hz.1

end R18
end QuantumZipper

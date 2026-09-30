import QuantumZipper.Proofs.Zipper.B5ZeroMinus
import QuantumZipper.Proofs.Zipper.E1CoordChange2

/-!
# B5-V endpoints (1): the flow property of the real reverse flow

Task B5V-FIX (`handoff/B5.md`, R1 (d)). For a driver `V` and a time `t ≥ 0`, let
`V' r = V (t + r) − V t` (`r ≥ 0`). The real reverse flow of `V` on `[0, t + r]` is the flow of
`V` on `[0,t]` followed by the flow of `V'` on `[0,r]`:

* `isRealRevSol_shift`, `isRealRevSol_concat`: restriction-and-shift and concatenation of real
  solutions;
* `realHitTime_eq_add`: `τ^V_x = t + τ^{V'}_{F x}` for `x` alive at time `t`, `F = realRevMap V t`;
* `realRevMap_zeroMinus_add`: `F (0₋^V(t + r)) = 0₋^{V'}(r)` for `0 < r < s`, `t + s = T`,
  when both reverse hulls (`V` at `T`, `V'` at `s`) are simple arcs;
* **`realRevMap_endpoints`**: with `a = 0₋^V(T)`, `c = 0₋^V(t)`: `a < c`, `F` strictly increasing on
  `(a,c)`, `F → 0₋^{V'}(s)` at `a⁺` and `F → 0` at `c⁻`.

For `V = vrev W T`, `V' = vrev W s` (`vrev_shift`). Own elementary proof (flow property of an ODE;
Lawler, *Conformally invariant processes in the plane*, §4.1, uses it without proof).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace B5

open RealLine

variable {V V' : ℝ → ℝ} {t : ℝ}

theorem continuousOn_two_div_of_isRealRevSol {x T : ℝ} {u : ℝ → ℝ} (hu : IsRealRevSol V x T u) :
    ContinuousOn (fun y => 2 / u y) (Icc 0 T) :=
  continuousOn_const.div hu.1 fun y hy => (hu.2 y hy).1

theorem intervalIntegrable_two_div {T : ℝ} {u : ℝ → ℝ}
    (hc : ContinuousOn (fun y => 2 / u y) (Icc 0 T)) {a b : ℝ} (ha : a ∈ Icc 0 T)
    (hb : b ∈ Icc 0 T) : IntervalIntegrable (fun y => 2 / u y) volume a b :=
  (hc.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

/-- **Restriction and shift.** -/
theorem isRealRevSol_shift (ht : 0 ≤ t) (hV' : ∀ r, 0 ≤ r → V' r = V (t + r) - V t)
    {x r : ℝ} {u : ℝ → ℝ} (hr : 0 ≤ r) (hu : IsRealRevSol V x (t + r) u) :
    IsRealRevSol V' (u t) r (fun q => u (t + q)) := by
  have hc := continuousOn_two_div_of_isRealRevSol hu
  have hmaps : MapsTo (fun q => t + q) (Icc 0 r) (Icc 0 (t + r)) := fun q hq =>
    ⟨by linarith [hq.1], by linarith [hq.2]⟩
  refine ⟨hu.1.comp (continuous_const.add continuous_id).continuousOn hmaps, fun q hq => ?_⟩
  refine ⟨(hu.2 _ (hmaps hq)).1, ?_⟩
  have htI : t ∈ Icc 0 (t + r) := ⟨ht, by linarith⟩
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_two_div hc ⟨le_rfl, by linarith⟩ htI)
    (intervalIntegrable_two_div hc htI (hmaps hq))
  have hshift : ∫ y in (0 : ℝ)..q, 2 / u (t + y) = ∫ y in t..t + q, 2 / u y := by
    rw [intervalIntegral.integral_comp_add_left (fun y => 2 / u y) t, add_zero]
  have e1 := (hu.2 _ (hmaps hq)).2
  have e2 := (hu.2 t htI).2
  rw [hV' q hq.1, hshift]
  simp only at e1 ⊢
  linarith

/-- **Concatenation.** -/
theorem isRealRevSol_concat (ht : 0 ≤ t) (hV' : ∀ r, 0 ≤ r → V' r = V (t + r) - V t)
    {x r : ℝ} {u v : ℝ → ℝ} (hr : 0 ≤ r) (hu : IsRealRevSol V x t u)
    (hv : IsRealRevSol V' (u t) r v) :
    IsRealRevSol V x (t + r) (fun q => if q ≤ t then u q else v (q - t)) := by
  set w : ℝ → ℝ := fun q => if q ≤ t then u q else v (q - t) with hw
  have hv0 : v 0 = u t := by
    rw [isRealRevSol_zero hv hr, hV' 0 le_rfl, add_zero, sub_self, sub_zero]
  have hwL : ∀ q ≤ t, w q = u q := fun q hq => if_pos hq
  have hwR : ∀ q, t ≤ q → w q = v (q - t) := by
    intro q hq
    rcases eq_or_lt_of_le hq with h | h
    · rw [← h, hwL t le_rfl, sub_self, hv0]
    · exact if_neg (not_le.2 h)
  have hmapsR : ∀ q ∈ Icc t (t + r), q - t ∈ Icc 0 r := fun q hq =>
    ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have hwne : ∀ q ∈ Icc 0 (t + r), w q ≠ 0 := by
    intro q hq
    rcases le_total q t with h | h
    · rw [hwL q h]; exact (hu.2 q ⟨hq.1, h⟩).1
    · rw [hwR q h]; exact (hv.2 _ (hmapsR q ⟨h, hq.2⟩)).1
  have hcL : ContinuousOn w (Icc 0 t) := hu.1.congr fun q hq => hwL q hq.2
  have hcR : ContinuousOn w (Icc t (t + r)) :=
    (hv.1.comp (continuous_sub_right t).continuousOn fun q hq => hmapsR q hq).congr
      fun q hq => hwR q hq.1
  have hIcc : Icc 0 (t + r) = Icc 0 t ∪ Icc t (t + r) :=
    (Icc_union_Icc_eq_Icc ht (by linarith)).symm
  have hcw : ContinuousOn w (Icc 0 (t + r)) := by
    rw [hIcc]; exact hcL.union_of_isClosed hcR isClosed_Icc isClosed_Icc
  have hc : ContinuousOn (fun y => 2 / w y) (Icc 0 (t + r)) :=
    continuousOn_const.div hcw hwne
  refine ⟨hcw, fun q hq => ⟨hwne q hq, ?_⟩⟩
  rcases le_total q t with h | h
  · have hI : ∫ y in (0 : ℝ)..q, 2 / w y = ∫ y in (0 : ℝ)..q, 2 / u y :=
      intervalIntegral.integral_congr fun y hy => by
        rw [uIcc_of_le hq.1] at hy
        simp only [hwL y (hy.2.trans h)]
    rw [hI, hwL q h]
    exact (hu.2 q ⟨hq.1, h⟩).2
  · have htI : t ∈ Icc 0 (t + r) := ⟨ht, by linarith⟩
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_two_div hc ⟨le_rfl, by linarith⟩ htI)
      (intervalIntegrable_two_div hc htI hq)
    have hI1 : ∫ y in (0 : ℝ)..t, 2 / w y = ∫ y in (0 : ℝ)..t, 2 / u y :=
      intervalIntegral.integral_congr fun y hy => by
        rw [uIcc_of_le ht] at hy
        simp only [hwL y hy.2]
    have hI2 : ∫ y in t..q, 2 / w y = ∫ y in (0 : ℝ)..q - t, 2 / v y := by
      rw [intervalIntegral.integral_congr (g := fun y => 2 / v (y - t)) fun y hy => by
        rw [uIcc_of_le h] at hy
        simp only [hwR y hy.1]]
      rw [intervalIntegral.integral_comp_sub_right (fun y => 2 / v y) t, sub_self]
    have e1 := (hv.2 _ (hmapsR q ⟨h, hq.2⟩)).2
    have e2 := (hu.2 t ⟨ht, le_rfl⟩).2
    have e3 := hV' (q - t) (by linarith)
    rw [add_sub_cancel] at e3
    rw [hwR q h, ← hsplit, hI1, hI2]
    linarith

/-- **Flow property of the hitting time.** -/
theorem realHitTime_eq_add (hV : Continuous V) (ht : 0 ≤ t)
    (hV' : ∀ r, 0 ≤ r → V' r = V (t + r) - V t) {x : ℝ} {u : ℝ → ℝ}
    (hu : IsRealRevSol V x t u) :
    realHitTime V x = ENNReal.ofReal t + realHitTime V' (realRevMap V t x) := by
  rw [realRevMap_eq hV hu ht le_rfl]
  apply le_antisymm
  · refine iSup_le fun T => iSup_le fun hT => iSup_le fun ⟨w, hw⟩ => ?_
    rcases le_total T t with h | h
    · exact (ENNReal.ofReal_le_ofReal h).trans le_self_add
    · have hwt : w t = u t :=
        isRealRevSol_unique hV ht (isRealRevSol_restrict hw h) hu ⟨ht, le_rfl⟩
      have hw' : IsRealRevSol V x (t + (T - t)) w := by rwa [add_sub_cancel]
      have hs := isRealRevSol_shift ht hV' (sub_nonneg.2 h) hw'
      rw [hwt] at hs
      calc ENNReal.ofReal T = ENNReal.ofReal t + ENNReal.ofReal (T - t) := by
            rw [← ENNReal.ofReal_add ht (sub_nonneg.2 h), add_sub_cancel]
        _ ≤ _ := by gcongr; exact RealLine.ofReal_le_realHitTime (sub_nonneg.2 h) hs
  · have htx : ENNReal.ofReal t ≤ realHitTime V x := RealLine.ofReal_le_realHitTime ht hu
    have hle : realHitTime V' (u t) ≤ realHitTime V x - ENNReal.ofReal t := by
      refine iSup_le fun r => iSup_le fun hr => iSup_le fun ⟨v, hv⟩ => ?_
      refine ENNReal.le_sub_of_add_le_left ENNReal.ofReal_ne_top ?_
      rw [← ENNReal.ofReal_add ht hr]
      exact RealLine.ofReal_le_realHitTime (by linarith) (isRealRevSol_concat ht hV' hr hu hv)
    calc ENNReal.ofReal t + realHitTime V' (u t)
        ≤ ENNReal.ofReal t + (realHitTime V x - ENNReal.ofReal t) := by gcongr
      _ = realHitTime V x := add_tsub_cancel_of_le htx

section Endpoints

variable {T s : ℝ} (hV : Continuous V) (hV0 : V 0 = 0) (hT : 0 < T)
  (hK : IsSimpleCurveHull (revHull V T)) (hV'c : Continuous V') (hV'0 : V' 0 = 0) (hs : 0 < s)
  (hK' : IsSimpleCurveHull (revHull V' s)) (ht : 0 ≤ t) (hts : t + s = T)
  (hV' : ∀ r, 0 ≤ r → V' r = V (t + r) - V t)
include hV hV0 hT hK hV'c hV'0 hs hK' ht hts hV'

omit hV'c hV'0 hK' hV' in
/-- The hitting time of a point of `(0₋(T), 0₋(t))` lies in `(t, T)`. -/
theorem hitTime_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (zeroMinus V T) (zeroMinus V t)) :
    ∃ τ, t < τ ∧ τ < T ∧ realHitTime V x = ENNReal.ofReal τ ∧ zeroMinus V τ = x := by
  have hanti := strictAntiOn_zeroMinus hV hV0 hT hK
  have htI : t ∈ Icc 0 T := ⟨ht, by linarith⟩
  have hc0 : zeroMinus V t ≤ 0 := by
    rw [← zeroMinus_zero_time hV hV0]
    exact hanti.antitoneOn ⟨le_rfl, hT.le⟩ htI ht
  obtain ⟨he, hτ, hz⟩ := hitTime_spec hV hV0 hT hK ⟨hx.1, (hx.2.trans_le hc0).le⟩
  refine ⟨_, ?_, ?_, he, hz⟩
  · by_contra h
    push Not at h
    have := hanti.antitoneOn hτ htI h
    rw [hz] at this
    exact absurd hx.2 (not_lt.2 this)
  · refine lt_of_le_of_ne hτ.2 fun h => ?_
    rw [h] at hz
    exact absurd hx.1 (by rw [hz]; exact lt_irrefl _)

/-- **Key identity:** `F (0₋^V(t + r)) = 0₋^{V'}(r)` for `0 < r < s`. -/
theorem realRevMap_zeroMinus_add {r : ℝ} (hr : r ∈ Ioo 0 s) :
    realRevMap V t (zeroMinus V (t + r)) = zeroMinus V' r := by
  have hanti := strictAntiOn_zeroMinus hV hV0 hT hK
  set x := zeroMinus V (t + r) with hxdef
  have hx : x ∈ Ioo (zeroMinus V T) (zeroMinus V t) :=
    ⟨hanti ⟨by linarith [hr.1], by linarith [hr.2]⟩ ⟨hT.le, le_rfl⟩ (by linarith [hr.2]),
      hanti ⟨ht, by linarith⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩ (by linarith [hr.1])⟩
  obtain ⟨τ, htτ, hτT, he, hz⟩ := hitTime_of_mem_Ioo hV hV0 hT hK hs ht hts hx
  have hτ : τ = t + r := hanti.injOn ⟨by linarith, hτT.le⟩
    ⟨by linarith [hr.1], by linarith [hr.2]⟩ hz
  have hlive : E1.IsLive V t x := by
    show ENNReal.ofReal t < realHitTime V x
    rw [he]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htτ
  obtain ⟨u, hu⟩ := exists_isRealRevSol_of_lt_realHitTime hlive
  have hadd := realHitTime_eq_add hV ht hV' hu
  rw [he, hτ, ENNReal.ofReal_add ht hr.1.le] at hadd
  have hτ' : realHitTime V' (realRevMap V t x) = ENNReal.ofReal r :=
    ((ENNReal.add_right_inj ENNReal.ofReal_ne_top).1 hadd).symm
  have hxneg : x < 0 := hx.2.trans_le (by
    rw [← zeroMinus_zero_time hV hV0]
    exact hanti.antitoneOn ⟨le_rfl, hT.le⟩ ⟨ht, by linarith⟩ ht)
  have hF0 : realRevMap V t x < 0 := E1.realRevMap_neg hV hV0 ht hxneg hlive
  have hlt : zeroMinus V' s < realRevMap V t x :=
    (realHitTime_lt_iff hV'c hV'0 hs hK' hF0.le).1
      (by rw [hτ']; exact (ENNReal.ofReal_lt_ofReal_iff hs).2 hr.2)
  obtain ⟨-, -, hz'⟩ := hitTime_spec hV'c hV'0 hs hK' ⟨hlt, hF0.le⟩
  rw [hτ', ENNReal.toReal_ofReal hr.1.le] at hz'
  exact hz'.symm

/-- Every point of `(0₋(T), 0₋(t))` is `0₋^V(t + r)` for some `r ∈ (0,s)`, and
`F x = 0₋^{V'}(r)`. -/
theorem exists_eq_zeroMinus_add {x : ℝ} (hx : x ∈ Ioo (zeroMinus V T) (zeroMinus V t)) :
    ∃ r ∈ Ioo 0 s, x = zeroMinus V (t + r) ∧ realRevMap V t x = zeroMinus V' r := by
  obtain ⟨τ, htτ, hτT, -, hz⟩ := hitTime_of_mem_Ioo hV hV0 hT hK hs ht hts hx
  have hr : τ - t ∈ Ioo 0 s := ⟨by linarith, by linarith⟩
  have hx' : x = zeroMinus V (t + (τ - t)) := by rw [add_sub_cancel, hz]
  refine ⟨τ - t, hr, hx', ?_⟩
  rw [hx']
  exact realRevMap_zeroMinus_add hV hV0 hT hK hV'c hV'0 hs hK' ht hts hV' hr

/-- **The endpoints of the unzipped segment (deterministic).** With `a = 0₋^V(T)`,
`c = 0₋^V(t)`, `F = realRevMap V t`: `a < c`, `F` is strictly increasing on `(a,c)`, and
`F → 0₋^{V'}(s)` at `a⁺`, `F → 0` at `c⁻`. -/
theorem realRevMap_endpoints :
    zeroMinus V T < zeroMinus V t ∧
      StrictMonoOn (realRevMap V t) (Ioo (zeroMinus V T) (zeroMinus V t)) ∧
      Tendsto (realRevMap V t) (𝓝[>] (zeroMinus V T)) (𝓝 (zeroMinus V' s)) ∧
      Tendsto (realRevMap V t) (𝓝[<] (zeroMinus V t)) (𝓝 0) := by
  have hanti := strictAntiOn_zeroMinus hV hV0 hT hK
  have hanti' := strictAntiOn_zeroMinus hV'c hV'0 hs hK'
  have hac : zeroMinus V T < zeroMinus V t :=
    hanti ⟨ht, by linarith⟩ ⟨hT.le, le_rfl⟩ (by linarith)
  have hmem : ∀ r ∈ Ioo 0 s, zeroMinus V (t + r) ∈ Ioo (zeroMinus V T) (zeroMinus V t) :=
    fun r hr => ⟨hanti ⟨by linarith [hr.1], by linarith [hr.2]⟩ ⟨hT.le, le_rfl⟩ (by linarith [hr.2]),
      hanti ⟨ht, by linarith⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩ (by linarith [hr.1])⟩
  have hbd : ∀ x ∈ Ioo (zeroMinus V T) (zeroMinus V t),
      zeroMinus V' s < realRevMap V t x ∧ realRevMap V t x < 0 := by
    intro x hx
    obtain ⟨r, hr, -, hF⟩ := exists_eq_zeroMinus_add hV hV0 hT hK hV'c hV'0 hs hK' ht hts hV' hx
    rw [hF]
    refine ⟨hanti' ⟨hr.1.le, hr.2.le⟩ ⟨hs.le, le_rfl⟩ hr.2, ?_⟩
    rw [← zeroMinus_zero_time hV'c hV'0]
    exact hanti' ⟨le_rfl, hs.le⟩ ⟨hr.1.le, hr.2.le⟩ hr.1
  have hmono : StrictMonoOn (realRevMap V t) (Ioo (zeroMinus V T) (zeroMinus V t)) := by
    refine (strictMonoOn_realRevMap hV ht).mono fun x hx => ?_
    obtain ⟨τ, htτ, -, he, -⟩ := hitTime_of_mem_Ioo hV hV0 hT hK hs ht hts hx
    exact exists_isRealRevSol_of_lt_realHitTime (by
      rw [he]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 htτ)
  have hcont := continuousOn_zeroMinus_Icc hV'c hV'0 hs hK'
  refine ⟨hac, hmono, ?_, ?_⟩
  · refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
    · filter_upwards [Ioo_mem_nhdsGT hac] with x hx using hl.trans (hbd x hx).1
    · have h1 : Tendsto (zeroMinus V') (𝓝[<] s) (𝓝 (zeroMinus V' s)) :=
        (hcont s ⟨hs.le, le_rfl⟩).tendsto.mono_left (nhdsWithin_le_of_mem
          (mem_of_superset (Ioo_mem_nhdsLT hs) Ioo_subset_Icc_self))
      obtain ⟨r, hru, hr⟩ := ((h1.eventually (gt_mem_nhds hu)).and (Ioo_mem_nhdsLT hs)).exists
      have hx0 := hmem r hr
      filter_upwards [Ioo_mem_nhdsGT hx0.1] with x hx
      have := hmono ⟨hx.1, hx.2.trans hx0.2⟩ hx0 hx.2
      rw [realRevMap_zeroMinus_add hV hV0 hT hK hV'c hV'0 hs hK' ht hts hV' hr] at this
      exact this.trans hru
  · refine tendsto_order.2 ⟨fun l hl => ?_, fun u hu => ?_⟩
    · have h1 : Tendsto (zeroMinus V') (𝓝[>] 0) (𝓝 (zeroMinus V' 0)) :=
        (hcont 0 ⟨le_rfl, hs.le⟩).tendsto.mono_left (nhdsWithin_le_of_mem
          (mem_of_superset (Ioo_mem_nhdsGT hs) Ioo_subset_Icc_self))
      rw [zeroMinus_zero_time hV'c hV'0] at h1
      obtain ⟨r, hrl, hr⟩ := ((h1.eventually (lt_mem_nhds hl)).and (Ioo_mem_nhdsGT hs)).exists
      have hx0 := hmem r hr
      filter_upwards [Ioo_mem_nhdsLT hx0.2] with x hx
      have := hmono hx0 ⟨hx0.1.trans hx.1, hx.2⟩ hx.1
      rw [realRevMap_zeroMinus_add hV hV0 hT hK hV'c hV'0 hs hK' ht hts hV' hr] at this
      exact hrl.trans this
    · filter_upwards [Ioo_mem_nhdsLT hac] with x hx using (hbd x hx).2.trans hu

end Endpoints

end B5
end QuantumZipper

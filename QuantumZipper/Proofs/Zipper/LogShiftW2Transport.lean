import QuantumZipper.LQG.Measures
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-W2 (1): transport to capacity time from the *new-piece* sub-arc lengths

Task LSL-W2. Variant of `LogShiftWTransport.lean` adapted to what the field cocycle gives
directly: at a stage `T`, the boundary position `a r` of the curve point of capacity time
`r ∈ [u, T]` (continuous, strictly increasing, `a T = 0`), and the `Γ⁰` boundary measure of the
*new* piece `[a r, 0]` (the image of the left side of `η[r, T]`) is `μ(r, T]`. With `μ` without
atoms on `(u, T]`, `ν_Γ` restricted to `[a u, 0]` is the image of `μ` restricted to `(u, T]`
(`lsw2_map_left`; mirror `lsw2_map_right`). If moreover `ν_Z = ρ · ν_Γ` off the two tips
`{a 0, b 0}` and `ρ (a r) = w r`, then `ν_Z [a u, 0] = ∫_{(u,T]} w dμ` (`lsw2_stage`).

Also: a measure whose cumulative `μ(u, r]` is continuous in `r` has no atoms on `(u, ∞)`
(`lsw2_atom_zero`). Own elementary bookkeeping (Sheffield arXiv:1012.4797 §1.4, §5.4 pp. 71–72
for the meaning).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace QuantumZipper
namespace F1

/-- Clamp to `[u, T]`. -/
def lswClamp (u T r : ℝ) : ℝ := max u (min r T)

theorem lswClamp_of_mem {u T r : ℝ} (h : r ∈ Ioc u T) : lswClamp u T r = r := by
  unfold lswClamp
  rw [min_eq_left h.2, max_eq_right h.1.le]

theorem lswClamp_mem {u T : ℝ} (huT : u ≤ T) (r : ℝ) : lswClamp u T r ∈ Icc u T :=
  ⟨le_max_left _ _, max_le huT (min_le_right _ _)⟩

theorem continuous_comp_lswClamp {u T : ℝ} (huT : u ≤ T) {a : ℝ → ℝ}
    (ha : ContinuousOn a (Icc u T)) : Continuous (fun r => a (lswClamp u T r)) :=
  ha.comp_continuous (continuous_const.max (continuous_id.min continuous_const))
    (lswClamp_mem huT)

/-- **No atoms from a continuous cumulative.** -/
theorem lsw2_atom_zero {μ : Measure ℝ} {u : ℝ} {F : ℝ → ℝ≥0∞}
    (hF : ∀ r, u ≤ r → μ (Ioc u r) = F r) (hfin : ∀ r, u ≤ r → F r ≠ ⊤)
    (hc : ContinuousOn (fun r => (F r).toReal) (Ici u)) {r : ℝ} (hr : u < r) : μ {r} = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_) (by simp)
  rw [zero_add]
  have hcr := (hc r (mem_Ici.2 hr.le)).tendsto
  have hev : ∀ᶠ q in 𝓝[Ici u] r, |(F q).toReal - (F r).toReal| < δ := by
    have := Metric.tendsto_nhds.1 hcr δ (by exact_mod_cast hδ)
    filter_upwards [this] with q hq
    simpa [Real.dist_eq] using hq
  have hmem : Ioo u r ∈ 𝓝[<] r := Ioo_mem_nhdsLT hr
  have hle : 𝓝[<] r ≤ 𝓝[Ici u] r :=
    nhdsWithin_le_of_mem (mem_of_superset hmem fun q hq => mem_Ici.2 hq.1.le)
  have hev' : ∀ᶠ q in 𝓝[<] r, |(F q).toReal - (F r).toReal| < δ := hle hev
  obtain ⟨q, hq, hqr⟩ := (hev'.and hmem).exists
  have hsplit : F r = F q + μ (Ioc q r) := by
    rw [← hF r hr.le, ← hF q hqr.1.le, ← measure_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc, Ioc_union_Ioc_eq_Ioc hqr.1.le hqr.2.le]
  have hfq := hfin q hqr.1.le
  have hfr := hfin r hr.le
  have hIfin : μ (Ioc q r) ≠ ⊤ := by
    intro h
    rw [h, add_top] at hsplit
    exact hfr hsplit
  have hreal : (μ (Ioc q r)).toReal = (F r).toReal - (F q).toReal := by
    rw [hsplit, ENNReal.toReal_add hfq hIfin]
    ring
  calc μ {r} ≤ μ (Ioc q r) := measure_mono (singleton_subset_iff.2 ⟨hqr.2, le_rfl⟩)
    _ = ENNReal.ofReal (μ (Ioc q r)).toReal := (ENNReal.ofReal_toReal hIfin).symm
    _ ≤ ENNReal.ofReal δ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hreal]
        have := abs_lt.1 hq
        linarith [this.1]
    _ = δ := ENNReal.ofReal_coe_nnreal

/-- **Left side: image measure.** -/
theorem lsw2_map_left {νΓ μ : Measure ℝ} {u T : ℝ} (huT : u ≤ T) {a : ℝ → ℝ}
    (hac : ContinuousOn a (Icc u T)) (ham : StrictMonoOn a (Icc u T)) (haT : a T = 0)
    (hL : ∀ r ∈ Icc u T, νΓ (Icc (a r) 0) = μ (Ioc r T))
    (hat : ∀ r ∈ Ioc u T, μ {r} = 0) (hfin : μ (Ioc u T) ≠ ⊤) :
    (μ.restrict (Ioc u T)).map (fun r => a (lswClamp u T r)) = νΓ.restrict (Icc (a u) 0) := by
  have hg := (continuous_comp_lswClamp huT hac).measurable
  have : IsFiniteMeasure ((μ.restrict (Ioc u T)).map (fun r => a (lswClamp u T r))) := by
    have : IsFiniteMeasure (μ.restrict (Ioc u T)) := isFiniteMeasure_restrict.2 hfin
    infer_instance
  have hmemI : ∀ q ∈ Ioc u T, q ∈ Icc u T := fun q hq => ⟨hq.1.le, hq.2⟩
  have huI : u ∈ Icc u T := ⟨le_rfl, huT⟩
  have hTI : T ∈ Icc u T := ⟨huT, le_rfl⟩
  refine Measure.ext_of_Ici _ _ fun y => ?_
  rw [Measure.map_apply hg measurableSet_Ici, Measure.restrict_apply (hg measurableSet_Ici),
    Measure.restrict_apply measurableSet_Ici]
  have hpre : ∀ S : Set ℝ, (fun r => a (lswClamp u T r)) ⁻¹' S ∩ Ioc u T =
      {q | a q ∈ S} ∩ Ioc u T := by
    intro S
    ext q
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [lswClamp_of_mem h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [lswClamp_of_mem h2]
      exact ⟨h1, h2⟩
  rw [hpre]
  rcases le_or_gt y (a u) with hy | hy
  · have e1 : {q | a q ∈ Ici y} ∩ Ioc u T = Ioc u T := inter_eq_right.2 fun q hq =>
      le_trans hy (ham.monotoneOn huI (hmemI q hq) hq.1.le)
    have e2 : Ici y ∩ Icc (a u) 0 = Icc (a u) 0 := inter_eq_right.2 fun q hq => le_trans hy hq.1
    rw [e1, e2, hL u huI]
  rcases lt_or_ge 0 y with hy0 | hy0
  · have e1 : {q | a q ∈ Ici y} ∩ Ioc u T = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ici, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      have := ham.monotoneOn (hmemI q h2) hTI h2.2
      rw [haT] at this
      linarith
    have e2 : Ici y ∩ Icc (a u) 0 = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_Ici, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro h1 _
      linarith
    rw [e1, e2, measure_empty, measure_empty]
  obtain ⟨r, hr, hry⟩ : ∃ r ∈ Icc u T, a r = y := by
    have h := intermediate_value_Icc huT hac
    rw [haT] at h
    exact h ⟨hy.le, hy0⟩
  have hru : u < r := by
    rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h] at hry
      linarith
    · exact h
  have e1 : {q | a q ∈ Ici y} ∩ Ioc u T = Icc r T := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ici, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [← hry, ham.le_iff_le hr ⟨h2.le, h3⟩] at h1
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨?_, lt_of_lt_of_le hru h1, h3⟩
      rw [← hry, ham.le_iff_le hr ⟨(hru.trans_le h1).le, h3⟩]
      exact h1
  have e2 : Ici y ∩ Icc (a u) 0 = Icc y 0 := by
    ext q
    simp only [mem_inter_iff, mem_Ici, mem_Icc]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨h1, by linarith, h3⟩
  rw [e1, e2, ← hry, hL r hr, ← Icc_sdiff_left, measure_sdiff_null (hat r ⟨hru, hr.2⟩)]

/-- **Right side: image measure.** -/
theorem lsw2_map_right {νΓ μ : Measure ℝ} {u T : ℝ} (huT : u ≤ T) {b : ℝ → ℝ}
    (hbc : ContinuousOn b (Icc u T)) (hbm : StrictAntiOn b (Icc u T)) (hbT : b T = 0)
    (hL : ∀ r ∈ Icc u T, νΓ (Icc 0 (b r)) = μ (Ioc r T))
    (hat : ∀ r ∈ Ioc u T, μ {r} = 0) (hfin : μ (Ioc u T) ≠ ⊤) :
    (μ.restrict (Ioc u T)).map (fun r => b (lswClamp u T r)) = νΓ.restrict (Icc 0 (b u)) := by
  have hg := (continuous_comp_lswClamp huT hbc).measurable
  have : IsFiniteMeasure ((μ.restrict (Ioc u T)).map (fun r => b (lswClamp u T r))) := by
    have : IsFiniteMeasure (μ.restrict (Ioc u T)) := isFiniteMeasure_restrict.2 hfin
    infer_instance
  have hmemI : ∀ q ∈ Ioc u T, q ∈ Icc u T := fun q hq => ⟨hq.1.le, hq.2⟩
  have huI : u ∈ Icc u T := ⟨le_rfl, huT⟩
  have hTI : T ∈ Icc u T := ⟨huT, le_rfl⟩
  refine Measure.ext_of_Iic _ _ fun y => ?_
  rw [Measure.map_apply hg measurableSet_Iic, Measure.restrict_apply (hg measurableSet_Iic),
    Measure.restrict_apply measurableSet_Iic]
  have hpre : ∀ S : Set ℝ, (fun r => b (lswClamp u T r)) ⁻¹' S ∩ Ioc u T =
      {q | b q ∈ S} ∩ Ioc u T := by
    intro S
    ext q
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [lswClamp_of_mem h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [lswClamp_of_mem h2]
      exact ⟨h1, h2⟩
  rw [hpre]
  rcases le_or_gt (b u) y with hy | hy
  · have e1 : {q | b q ∈ Iic y} ∩ Ioc u T = Ioc u T := inter_eq_right.2 fun q hq =>
      le_trans (hbm.antitoneOn huI (hmemI q hq) hq.1.le) hy
    have e2 : Iic y ∩ Icc 0 (b u) = Icc 0 (b u) := inter_eq_right.2 fun q hq => le_trans hq.2 hy
    rw [e1, e2, hL u huI]
  rcases lt_or_ge y 0 with hy0 | hy0
  · have e1 : {q | b q ∈ Iic y} ∩ Ioc u T = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Iic, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      have := hbm.antitoneOn (hmemI q h2) hTI h2.2
      rw [hbT] at this
      linarith
    have e2 : Iic y ∩ Icc 0 (b u) = ∅ := by
      ext q
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false, not_and]
      intro h1 h2 _
      linarith
    rw [e1, e2, measure_empty, measure_empty]
  obtain ⟨r, hr, hry⟩ : ∃ r ∈ Icc u T, b r = y := by
    have h := intermediate_value_Icc' huT hbc
    rw [hbT] at h
    exact h ⟨hy0, hy.le⟩
  have hru : u < r := by
    rcases eq_or_lt_of_le hr.1 with h | h
    · rw [← h] at hry
      linarith
    · exact h
  have e1 : {q | b q ∈ Iic y} ∩ Ioc u T = Icc r T := by
    ext q
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Iic, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      rw [← hry, hbm.le_iff_ge ⟨h2.le, h3⟩ hr] at h1
      exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨?_, lt_of_lt_of_le hru h1, h3⟩
      rw [← hry, hbm.le_iff_ge ⟨(hru.trans_le h1).le, h3⟩ hr]
      exact h1
  have e2 : Iic y ∩ Icc 0 (b u) = Icc 0 y := by
    ext q
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1, h2, by linarith⟩
  rw [e1, e2, ← hry, hL r hr, ← Icc_sdiff_left, measure_sdiff_null (hat r ⟨hru, hr.2⟩)]

/-- **One stage, both sides**: the `Z` lengths of the new pieces from the global density off the
tips. -/
theorem lsw2_stage {νΓ νZ μm μp : Measure ℝ} {u T : ℝ} (hu : 0 ≤ u) (huT : u ≤ T)
    {a b : ℝ → ℝ} (hac : ContinuousOn a (Icc 0 T)) (hbc : ContinuousOn b (Icc 0 T))
    (ham : StrictMonoOn a (Icc 0 T)) (hbm : StrictAntiOn b (Icc 0 T)) (haT : a T = 0)
    (hbT : b T = 0)
    (hLm : ∀ r ∈ Icc u T, νΓ (Icc (a r) 0) = μm (Ioc r T))
    (hLp : ∀ r ∈ Icc u T, νΓ (Icc 0 (b r)) = μp (Ioc r T))
    (hatm : ∀ r ∈ Ioc u T, μm {r} = 0) (hatp : ∀ r ∈ Ioc u T, μp {r} = 0)
    (hfinm : μm (Ioc u T) ≠ ⊤) (hfinp : μp (Ioc u T) ≠ ⊤)
    {ρ w : ℝ → ℝ≥0∞} (hρ : Measurable ρ) (hρa : ∀ r ∈ Ioc u T, ρ (a r) = w r)
    (hρb : ∀ r ∈ Ioc u T, ρ (b r) = w r)
    (hZ : νZ = (νΓ.restrict ({a 0, b 0} : Set ℝ)ᶜ).withDensity ρ) :
    (νZ (Icc (a u) 0), νZ (Icc 0 (b u))) =
      (∫⁻ r in Ioc u T, w r ∂μm, ∫⁻ r in Ioc u T, w r ∂μp) := by
  have hsub : Icc u T ⊆ Icc 0 T := fun q hq => ⟨hu.trans hq.1, hq.2⟩
  have h0I : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hu.trans huT⟩
  have hTI : T ∈ Icc 0 T := ⟨hu.trans huT, le_rfl⟩
  have hmS : MeasurableSet (({a 0, b 0} : Set ℝ)ᶜ) :=
    ((measurableSet_singleton _).insert _).compl
  -- off the tips on `(u, T]`
  have hoff : ∀ q ∈ Ioc u T, a q ∈ ({a 0, b 0} : Set ℝ)ᶜ ∧ b q ∈ ({a 0, b 0} : Set ℝ)ᶜ := by
    intro q hq
    have hq0 : (0 : ℝ) < q := lt_of_le_of_lt hu hq.1
    have hqI : q ∈ Icc 0 T := ⟨hq0.le, hq.2⟩
    have ha0 : a 0 < a q := ham h0I hqI hq0
    have hb0 : b q < b 0 := hbm h0I hqI hq0
    have haq : a q ≤ 0 := by have := ham.monotoneOn hqI hTI hq.2; rwa [haT] at this
    have hbq : 0 ≤ b q := by have := hbm.antitoneOn hqI hTI hq.2; rwa [hbT] at this
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases h with h | h
      · exact (ne_of_gt ha0) h
      · rw [mem_singleton_iff] at h
        linarith
    · rcases h with h | h
      · linarith
      · rw [mem_singleton_iff] at h
        exact (ne_of_lt hb0) h
  have key : ∀ (c : ℝ → ℝ) (I : Set ℝ) (μ : Measure ℝ), MeasurableSet I →
      Continuous (fun r => c (lswClamp u T r)) →
      (μ.restrict (Ioc u T)).map (fun r => c (lswClamp u T r)) = νΓ.restrict I →
      (∀ q ∈ Ioc u T, c q ∈ ({a 0, b 0} : Set ℝ)ᶜ) → (∀ q ∈ Ioc u T, ρ (c q) = w q) →
      νZ I = ∫⁻ r in Ioc u T, w r ∂μ := by
    intro c I μ hI hc hmap hcoff hcw
    rw [hZ, withDensity_apply _ hI, Measure.restrict_restrict hI, inter_comm,
      ← Measure.restrict_restrict hmS, ← hmap, setLIntegral_map hmS hρ hc.measurable,
      Measure.restrict_restrict (hc.measurable hmS)]
    have e : (fun r => c (lswClamp u T r)) ⁻¹' ({a 0, b 0} : Set ℝ)ᶜ ∩ Ioc u T = Ioc u T :=
      inter_eq_right.2 fun q hq => by
        show c (lswClamp u T q) ∈ ({a 0, b 0} : Set ℝ)ᶜ
        rw [lswClamp_of_mem hq]
        exact hcoff q hq
    rw [e]
    refine setLIntegral_congr_fun measurableSet_Ioc fun q hq => ?_
    show ρ (c (lswClamp u T q)) = w q
    rw [lswClamp_of_mem hq, hcw q hq]
  refine Prod.ext ?_ ?_
  · exact key a _ μm measurableSet_Icc (continuous_comp_lswClamp huT (hac.mono hsub))
      (lsw2_map_left huT (hac.mono hsub) (ham.mono hsub) haT hLm hatm hfinm)
      (fun q hq => (hoff q hq).1) hρa
  · exact key b _ μp measurableSet_Icc (continuous_comp_lswClamp huT (hbc.mono hsub))
      (lsw2_map_right huT (hbc.mono hsub) (hbm.mono hsub) hbT hLp hatp hfinp)
      (fun q hq => (hoff q hq).2) hρb

end F1
end QuantumZipper

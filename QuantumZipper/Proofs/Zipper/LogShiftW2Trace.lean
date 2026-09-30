import QuantumZipper.Proofs.Zipper.LogShiftW2Pos
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.Thm12.Semigroup
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Zipper.WedgeTipXReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LSL-W2 (4): boundary correspondence `E_T(a_T(r)) = E_T(b_T(r)) = η(r)`

Task LSL-W2. Proves `LswPosTraceStmt`, hence `LswPosStmt` (`lswPosStmt_of_trace`).

* `trace_eq_extInv`: `η(r) = E_r(0)` once `E_r = F2.extInv W r` is continuous on `ℍ̄`
  (`η(r) = lim_{y↓0} f_r⁻¹(iy)`).
* `extInv_lswPos_fst`: with `V = vrev W T`, `t₀ = T − r`, on `ℍ` the Loewner semigroup
  (`Semigroup.revMap_split`, `B2.fwdMapInv_eq_revMap_vrev`) gives
  `E_T = E_r ∘ revMap V t₀`; the Carathéodory extension `F₀` of `revMap V t₀`
  (`CaraR.revMapCaratheodory`) is continuous on `ℍ̄` with `F₀(0₋^V(t₀)) = 0`, and
  `a_T(r) = 0₋^V(t₀)` (`lswPos_fst_eq_zeroMinus`); letting `z → a_T(r)` inside `ℍ`,
  `E_T(a_T(r)) = E_r(0) = η(r)`.
* `extInv_neg_real`: reflection `E^{−W}_T(−x) = −conj(E^W_T(x))` (`F1.fwdMapInv_reflect` plus
  continuity), which transfers the left identity for `−W` to the right position
  `b_T(r) = −a^{−W}_T(r)` (`lswPos_neg`).

Sources: Lawler, *Conformally invariant processes in the plane* (2005), §4.1 (semigroup of the
Loewner maps, boundary behaviour for simple curves); Pommerenke, *Boundary Behaviour of Conformal
Maps* (1992), Thm 2.6 (via `CaraR.revMapCaratheodory`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology ComplexConjugate
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

theorem lsw2_ofReal_mem_Hbar (x : ℝ) : ((x : ℝ) : ℂ) ∈ Hbar :=
  show (0 : ℝ) ≤ ((x : ℝ) : ℂ).im by simp

theorem lsw2_H_sub_Hbar : H ⊆ Hbar := fun z (hz : 0 < z.im) => (le_of_lt hz : 0 ≤ z.im)

theorem lsw2_neBot (x : ℝ) : (𝓝[H] ((x : ℝ) : ℂ)).NeBot := by
  have hmem : ((x : ℝ) : ℂ) ∈ closure H := by
    rw [CA.Car.closure_H_eq_Hbar]
    exact lsw2_ofReal_mem_Hbar x
  exact mem_closure_iff_nhdsWithin_neBot.1 hmem

/-- `η(r) = E_r(0)`. -/
theorem trace_eq_extInv {W : ℝ → ℝ} {r : ℝ} (hGC : ContinuousOn (F2.extInv W r) Hbar) :
    trace W r = F2.extInv W r 0 := by
  unfold trace
  refine Tendsto.limUnder_eq ?_
  have hc : Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ)) (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y (hy : 0 < y) => ?_⟩
    · have : Continuous (fun y : ℝ => ((y : ℂ) * Complex.I)) := by fun_prop
      have h := this.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul] at h
      exact h.mono_left nhdsWithin_le_nhds
    · show (0 : ℝ) ≤ ((y : ℂ) * Complex.I).im
      simp [hy.le]
  have h := ((hGC 0 (lsw2_ofReal_mem_Hbar 0)).tendsto).comp hc
  refine h.congr' (eventually_nhdsWithin_of_forall fun y (hy : 0 < y) => ?_)
  show F2.extInv W r ((y : ℂ) * Complex.I) = fwdMapInv W r ((y : ℂ) * Complex.I)
  simp [F2.extInv, hy]

/-- **Left position: `E_T(a_T(r)) = E_r(0)`** (deterministic). -/
theorem extInv_lswPos_fst {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hneg : ∀ v ≤ 0, W v = 0)
    (hK : ∀ s : ℝ, 0 < s → IsSimpleCurveHull (revHull (B2.vrev W s) s))
    (halive : ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol W (x : ℂ) T v)
    (hGC : ∀ t : ℝ, 0 ≤ t → ContinuousOn (F2.extInv W t) Hbar) {T r : ℝ} (hr : r ∈ Ioc 0 T) :
    F2.extInv W T ((lswPos W T r).1 : ℂ) = F2.extInv W r 0 := by
  have hT : 0 < T := lt_of_lt_of_le hr.1 hr.2
  set V := B2.vrev W T with hVdef
  have hVc : Continuous V := B2.continuous_vrev hW T
  have hV0 : V 0 = 0 := B2.vrev_zero hT.le
  have ha := lswPos_fst_eq_zeroMinus hW hW0 hneg hK halive hT ⟨hr.1.le, hr.2⟩
  rcases eq_or_lt_of_le hr.2 with hrT | hrT
  · rw [ha, hrT, sub_self, B5.zeroMinus_zero_time hVc hV0]
    simp
  set t₀ := T - r with ht₀def
  have ht₀ : 0 < t₀ := sub_pos.2 hrT
  obtain ⟨F₀, hF₀⟩ := CaraR.revMapCaratheodory V hVc hV0 t₀ ht₀
    (B5.isSimpleCurveHull_of_le hVc hV0 hT (hK T hT) ht₀ (by rw [ht₀def]; linarith [hr.1]))
  set a := zeroMinus V t₀ with hadef
  rw [ha]
  -- `E_T = E_r ∘ F₀` on `ℍ`
  have hsplit : ∀ z ∈ H, F2.extInv W T z = F2.extInv W r (F₀ z) := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hw : revMap V t₀ z ∈ H := Semigroup.mem_H_revMap hVc ht₀.le hz
    have hw' : 0 < (revMap V t₀ z).im := hw
    have h2 : ∀ q ∈ Icc (0 : ℝ) r, V (t₀ + q) - V t₀ = B2.vrev W r q := by
      intro q hq
      have m1 : t₀ + q ∈ Icc (0 : ℝ) T := ⟨by linarith [hq.1], by rw [ht₀def]; linarith [hq.2]⟩
      have m2 : t₀ ∈ Icc (0 : ℝ) T := ⟨ht₀.le, by rw [ht₀def]; linarith [hr.1]⟩
      rw [hVdef, B2.vrev_of_mem m1, B2.vrev_of_mem m2, B2.vrev_of_mem hq,
        show T - (t₀ + q) = r - q by rw [ht₀def]; ring, show T - t₀ = r by rw [ht₀def]; ring]
      ring
    have hsp := Semigroup.revMap_split (W2 := B2.vrev W r) hVc ht₀.le (fun _ _ => rfl) h2
      ⟨hr.1.le, le_rfl⟩ hz
    rw [show t₀ + r = T by rw [ht₀def]; ring] at hsp
    rw [WedgeUnzip.extInv_eq_fwdMapInv hz', B2.fwdMapInv_eq_revMap_vrev hW hW0 hT.le hz, hsp,
      ← B2.fwdMapInv_eq_revMap_vrev hW hW0 hr.1.le hw, ← WedgeUnzip.extInv_eq_fwdMapInv hw',
      (hF₀.1 hz).symm]
  have hne := lsw2_neBot a
  have h1 : Tendsto (F2.extInv W T) (𝓝[H] (a : ℂ)) (𝓝 (F2.extInv W T a)) :=
    ((hGC T hT.le) _ (lsw2_ofReal_mem_Hbar a)).tendsto.mono_left
      (nhdsWithin_mono _ lsw2_H_sub_Hbar)
  have hF0a : F₀ (a : ℂ) = 0 := hF₀.2.2.2.1
  have hF : Tendsto F₀ (𝓝[H] (a : ℂ)) (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · have := ((hF₀.2.1 _ (lsw2_ofReal_mem_Hbar a)).tendsto.mono_left
        (nhdsWithin_mono _ lsw2_H_sub_Hbar))
      rwa [hF0a] at this
    · rw [hF₀.1 hz]
      exact lsw2_H_sub_Hbar (Semigroup.mem_H_revMap hVc ht₀.le hz)
  have h2 : Tendsto (fun z => F2.extInv W r (F₀ z)) (𝓝[H] (a : ℂ)) (𝓝 (F2.extInv W r 0)) :=
    ((hGC r hr.1.le) 0 (by simpa using lsw2_ofReal_mem_Hbar 0)).tendsto.comp hF
  exact tendsto_nhds_unique (h1.congr' (eventually_nhdsWithin_of_forall hsplit)) h2

/-- **Reflection of the boundary extension at real points.** -/
theorem extInv_neg_real {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hGC : ContinuousOn (F2.extInv W T) Hbar) (hGC' : ContinuousOn (F2.extInv (-W) T) Hbar)
    (x : ℝ) : F2.extInv (-W) T ((-x : ℝ) : ℂ) = -conj (F2.extInv W T (x : ℂ)) := by
  have hne := lsw2_neBot x
  have hid : ∀ z ∈ H, F2.extInv (-W) T (-conj z) = -conj (F2.extInv W T z) := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hz'' : 0 < (-conj z).im := by simpa using hz'
    rw [WedgeUnzip.extInv_eq_fwdMapInv hz'', WedgeUnzip.extInv_eq_fwdMapInv hz',
      fwdMapInv_reflect W hW hT]
  have hr : Tendsto (fun z : ℂ => -conj z) (𝓝[H] (x : ℂ)) (𝓝[Hbar] ((-x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · have hc : Continuous (fun z : ℂ => -conj z) := by fun_prop
      have := hc.tendsto (x : ℂ)
      simp only [Complex.conj_ofReal] at this
      push_cast
      exact this.mono_left nhdsWithin_le_nhds
    · have hz' : 0 < z.im := hz
      show (0 : ℝ) ≤ (-conj z).im
      simp [hz'.le]
  have h1 := ((hGC' _ (lsw2_ofReal_mem_Hbar (-x))).tendsto).comp hr
  have h2 : Tendsto (fun z => -conj (F2.extInv W T z)) (𝓝[H] (x : ℂ))
      (𝓝 (-conj (F2.extInv W T x))) := by
    have hc : Continuous (fun z : ℂ => -conj z) := by fun_prop
    exact (hc.tendsto _).comp (((hGC _ (lsw2_ofReal_mem_Hbar x)).tendsto).mono_left
      (nhdsWithin_mono _ lsw2_H_sub_Hbar))
  exact tendsto_nhds_unique (h1.congr' (eventually_nhdsWithin_of_forall hid)) h2

/-- The a.s. hypotheses used above, for an SLE driver. -/
theorem ae_lsw2_driver_facts {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, Continuous (drive κ B ω) ∧ drive κ B ω 0 = 0 ∧ (∀ v ≤ 0, drive κ B ω v = 0) ∧
      (∀ s : ℝ, 0 < s → IsSimpleCurveHull (revHull (B2.vrev (drive κ B ω) s) s)) ∧
      (∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (drive κ B ω) (x : ℂ) T v) ∧
      (∀ t : ℝ, 0 ≤ t → ContinuousOn (F2.extInv (drive κ B ω) t) Hbar) := by
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le P
    B hB, RS.ae_real_alive hB hκ hκ4.le, hB.cont, hB.eval_zero_ae_eq_zero,
    WedgeUnzip.globalCaraStmt_holds κ hκ hκ4 P B hB] with ω hK hal hc h0 hGC
  refine ⟨?_, by simp [drive, h0], fun v hv => by simp [drive, Real.toNNReal_of_nonpos hv, h0],
    hK, hal, hGC⟩
  unfold drive
  exact continuous_const.mul (hc.comp continuous_real_toNNReal)

/-- **`LswPosTraceStmt` holds.** -/
theorem lswPosTraceStmt_holds : LswPosTraceStmt := by
  intro κ hκ hκ4 Ω _ P _ B hB
  have hB' : IsBrownianReal (RegUnif.negB B) P := hB.neg
  filter_upwards [ae_lsw2_driver_facts hκ hκ4 hB, ae_lsw2_driver_facts hκ hκ4 hB']
    with ω ⟨hW, hW0, hneg, hK, hal, hGC⟩ ⟨hW', hW0', hneg', hK', hal', hGC'⟩ T hT r hr
  rw [RegUnif.drive_negB] at hW' hW0' hneg' hK' hal' hGC'
  have hr' : r ∈ Icc 0 T := ⟨hr.1.le, hr.2⟩
  rw [trace_eq_extInv (hGC r hr.1.le)]
  refine ⟨extInv_lswPos_fst hW hW0 hneg hK hal hGC hr, ?_⟩
  -- right side by reflection
  have hb : (lswPos (drive κ B ω) T r).2 = -(lswPos (-drive κ B ω) T r).1 := by
    rw [lswPos_neg hW hr.2]
    simp
  have hleft := extInv_lswPos_fst hW' hW0' hneg' hK' hal' hGC' hr
  have href1 := extInv_neg_real hW' hT (hGC' T hT) (by simpa using hGC T hT)
    (lswPos (-drive κ B ω) T r).1
  have href2 := extInv_neg_real hW hr.1.le (hGC r hr.1.le) (hGC' r hr.1.le) 0
  rw [neg_neg] at href1
  rw [hb, href1, hleft]
  simp only [neg_zero, Complex.ofReal_zero] at href2
  rw [href2]
  simp

end F1
end QuantumZipper

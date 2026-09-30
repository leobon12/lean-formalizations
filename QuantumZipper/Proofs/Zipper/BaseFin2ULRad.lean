import QuantumZipper.Proofs.Zipper.BaseFin2UL
import QuantumZipper.Proofs.Zipper.LocHitScaleRead
import QuantumZipper.Proofs.ItoLite.Oscillation
import QuantumZipper.Proofs.Zipper.B5VSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-UL-R: exponential moments of `|O^±_1|` (`BaseULRadStmt`)

Proves `BaseFin2.baseULRadStmt_holds : BaseULRadStmt`.

* `|O^±_1| ≤ 3M + 3` when `|W| ≤ M` on `[0,1]` (`E6.abs_sideImages_le`, the Loewner real-flow
  estimate of `B5.sideSmallStmt`), with `M = √κ · osc_{[0,1]} B`.
* The Brownian oscillation has the Gaussian tail `P(osc > a) ≤ 2 e^{−a²/2}`
  (`BMOsc.bmOsc_tail`, reflection principle / Doob), hence the explicit exponential moment
  `ul_expMom_of_tail` (own elementary layer-cake bookkeeping), uniform in the probability space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

theorem ul_tail_term (l : ℝ) (m : ℕ) :
    ENNReal.ofReal (Real.exp (l * ((m : ℝ) + 2))) *
        ENNReal.ofReal (2 * Real.exp (-(((m : ℝ) + 1) ^ 2) / 2)) ≤
      ENNReal.ofReal (2 * Real.exp ((l + 1) ^ 2 / 2 + l)) *
        ENNReal.ofReal (Real.exp (-1)) ^ m := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Real.exp_nat_mul]
  have h : Real.exp (l * ((m : ℝ) + 2)) * (2 * Real.exp (-(((m : ℝ) + 1) ^ 2) / 2)) =
      2 * Real.exp (l * ((m : ℝ) + 2) + -(((m : ℝ) + 1) ^ 2) / 2) := by
    rw [Real.exp_add]; ring
  have h' : 2 * Real.exp ((l + 1) ^ 2 / 2 + l) * Real.exp ((m : ℝ) * -1) =
      2 * Real.exp ((l + 1) ^ 2 / 2 + l + (m : ℝ) * -1) := by
    rw [mul_assoc, ← Real.exp_add]
  rw [h, h']
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.2 (by nlinarith [sq_nonneg ((m : ℝ) + 1 - (l + 1))])) (by norm_num)

/-- **Exponential moment from a Gaussian tail** (own elementary bookkeeping). -/
theorem ul_expMom_of_tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {O : Ω → ℝ} (hOm : Measurable O)
    (htail : ∀ a : ℝ, 0 < a → P {ω | a < O ω} ≤ ENNReal.ofReal (2 * Real.exp (-(a ^ 2) / 2)))
    {l : ℝ} (hl : 0 ≤ l) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (l * O ω)) ∂P ≤
      ENNReal.ofReal (Real.exp l) + ENNReal.ofReal (2 * Real.exp ((l + 1) ^ 2 / 2 + l)) *
        ∑' m : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ m := by
  let f : ℕ → Ω → ℝ≥0∞ := fun m => {ω | ((m : ℝ) + 1) < O ω}.indicator
    (fun _ => ENNReal.ofReal (Real.exp (l * ((m : ℝ) + 2))))
  have hSm : ∀ m : ℕ, MeasurableSet {ω | ((m : ℝ) + 1) < O ω} := fun m =>
    measurableSet_lt measurable_const hOm
  have hpt : ∀ ω, ENNReal.ofReal (Real.exp (l * O ω)) ≤
      ENNReal.ofReal (Real.exp l) + ∑' m, f m ω := by
    intro ω
    rcases le_or_gt (O ω) 1 with h1 | h1
    · refine le_trans ?_ le_self_add
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by nlinarith))
    · refine le_trans ?_ le_add_self
      have hc2 : 2 ≤ ⌈O ω⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast h1)
      obtain ⟨m, hm⟩ : ∃ m : ℕ, m + 2 = ⌈O ω⌉₊ := ⟨⌈O ω⌉₊ - 2, by omega⟩
      have hmR : ((m : ℝ) + 2) = ⌈O ω⌉₊ := by exact_mod_cast hm
      have hle : O ω ≤ (m : ℝ) + 2 := hmR ▸ Nat.le_ceil _
      have hlt : (m : ℝ) + 1 < O ω := by
        have := Nat.ceil_lt_add_one (show 0 ≤ O ω by linarith)
        linarith
      refine le_trans ?_ (ENNReal.le_tsum m)
      simp only [f, indicator_of_mem (show ω ∈ {ω | ((m : ℝ) + 1) < O ω} from hlt)]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle hl))
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (l * O ω)) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (Real.exp l) + ∑' m, f m ω ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp l) + ∑' m, ∫⁻ ω, f m ω ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_tsum fun m =>
          (measurable_const.indicator (hSm m)).aemeasurable]
    _ ≤ ENNReal.ofReal (Real.exp l) + ∑' m : ℕ, ENNReal.ofReal (2 * Real.exp ((l + 1) ^ 2 / 2 + l)) *
          ENNReal.ofReal (Real.exp (-1)) ^ m := by
        gcongr with m
        simp only [f]
        rw [lintegral_indicator_const (hSm m)]
        refine le_trans ?_ (ul_tail_term l m)
        gcongr
        exact htail _ (by positivity)
    _ = _ := by rw [ENNReal.tsum_mul_left]

/-- **`BaseULRadStmt` holds.** -/
theorem baseULRadStmt_holds : BaseULRadStmt := by
  intro κ hκ hκ4 s hs
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = 3 * s * Real.sqrt κ := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  refine ⟨ENNReal.ofReal (Real.exp (3 * s)) * (ENNReal.ofReal (Real.exp l) +
      ENNReal.ofReal (2 * Real.exp ((l + 1) ^ 2 / 2 + l)) *
        ∑' m : ℕ, ENNReal.ofReal (Real.exp (-1)) ^ m), ?_, ?_⟩
  · refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ul_geom_ne_top⟩)
  intro Ω _ P _ B hB
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hpre : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hOm : Measurable (bmOsc B' 0 1) := measurable_bmOsc hB'm hB'c 0 1
  have hMm : Measurable fun ω =>
      ENNReal.ofReal (Real.exp (3 * s)) * ENNReal.ofReal (Real.exp (l * bmOsc B' 0 1 ω)) :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (hOm.const_mul l))).const_mul _
  have hBn : IsBrownianReal (RegUnif.negB B) P := hB.neg
  refine ⟨_, hMm.aemeasurable, ?_, ?_⟩
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    refine ul_expMom_of_tail hOm (fun a ha => ?_) hl0
    have := BMOsc.bmOsc_tail hpre hB'm hB'c 0 1 one_pos ha
    simpa using this
  · filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero, F1.ae_lsw2_driver_facts hκ hκ4 hB,
      F1.ae_lsw2_driver_facts hκ hκ4 hBn] with ω heq h0 hD hD'
    obtain ⟨hW, hW0, hneg, hK, hal, _⟩ := hD
    obtain ⟨_, _, _, hK', hal', _⟩ := hD'
    rw [RegUnif.drive_negB] at hK' hal'
    set O := bmOsc B' 0 1 ω with hO
    have hbdd : BddAbove (range fun x : Icc (0 : ℝ≥0) (0 + 1) => |B' x ω - B' 0 ω|) := by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := 0 + 1)).image
        (f := fun r => |B' r ω - B' 0 ω|) (by have := hB'c ω; fun_prop) |>.bddAbove
      exact ⟨C, by rintro _ ⟨x, rfl⟩; exact hC ⟨x, x.2, rfl⟩⟩
    have hM : ∀ r ∈ Icc (0 : ℝ) 1, |drive κ B ω r| ≤ Real.sqrt κ * O := by
      intro r hr
      have hmem : r.toNNReal ∈ Icc (0 : ℝ≥0) (0 + 1) :=
        ⟨r.toNNReal.2, by rw [zero_add]; exact Real.toNNReal_le_one.2 hr.2⟩
      have h1 : |B' r.toNNReal ω - B' 0 ω| ≤ O := by
        rw [hO, bmOsc_eq_iSup_subtype (hB'c ω)]
        exact le_ciSup hbdd ⟨r.toNNReal, hmem⟩
      have hB0 : B' 0 ω = 0 := by rw [heq 0]; exact h0
      rw [hB0, sub_zero] at h1
      have e : drive κ B ω r = Real.sqrt κ * B' r.toNNReal ω := by
        simp only [drive, heq]
      rw [e, abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ)]
      exact mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg κ)
    obtain ⟨hs1, hs2⟩ := E6.abs_sideImages_le hW hW0 one_pos hM
      (fun x hx => hal x hx 1 zero_le_one)
    rw [Real.sqrt_one, mul_one] at hs1 hs2
    have e1 : (sideImages (drive κ B ω) 1).1 = zeroMinus (B2.Vr κ 1 B ω) 1 :=
      B5.sideImages_fst_eq_zeroMinus_vrev hW hW0 one_pos (hK 1 one_pos)
        (fun x hx => hal x hx 1 zero_le_one)
    have e2 : (sideImages (drive κ B ω) 1).2 = zeroPlus (B2.Vr κ 1 B ω) 1 := by
      have := Thm18Asm.G4Core.lswPos_snd_eq_zeroPlus hW hW0 hneg hK' hal' one_pos
        ⟨le_rfl, zero_le_one⟩
      rw [F1.lswPos_zero_drive h0 1, sub_zero] at this
      exact this
    rw [e1] at hs1
    rw [e2] at hs2
    have hR : ulRad κ B ω ≤ 3 * (Real.sqrt κ * O) + 3 := max_le hs1 hs2
    have hexp : Real.exp (s * ulRad κ B ω) ≤ Real.exp (3 * s) * Real.exp (l * O) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      rw [hl]
      nlinarith
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hexp

end BaseFin2
end QuantumZipper

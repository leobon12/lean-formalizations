import QuantumZipper.Proofs.LQG.InfiniteMass
import QuantumZipper.Statements.Thm14

/-!
# WELD-READ, deterministic part: `R_h` at rationals from real-centred semicircle values

Task WELD-READ (`Thm14WDG.WeldRPairingReadable`). The welding map
`weldR γ x s = inf {r ≥ 0 : ν[s,0] ≤ ν[0,r]}` (`ν = qBoundaryMeasure γ x`) is read off
measurably from the values of `x` at the real-centred folded circles
`foldedCircle (m / 2^n) (2^{-k})`, and it does not see an additive constant:

* `wRm_eq_wRq`: for **any** measure `ν`, the infimum over reals equals an infimum over
  rationals (the set is upward closed), written in `ℝ≥0∞` so that it is measurable.
* `mIcc_eq`: `ν(Icc a b) = ⨅ₙ Psi γ (Ioo (a - 1/(n+1)) (b + 1/(n+1)))` whenever `bdryApprox γ y`
  has a vague limit `ν` (`InfMass.Psi_eq` + continuity from above).
* `weldReadF`: the resulting measurable functional; `weldReadF_eq`: it equals the welding map of
  the vague limit.
* `wRm_smul`: the welding map is unchanged by `ν ↦ c ν` (`0 < c < ∞`), the paper's remark that
  `R_h` does not see the additive constant of `h` (Sheffield, arXiv:1012.4797, p. 15).
* `recR`: a measurable reconstruction of a field sample from values at the real-centred folded
  circles, and `weldReadF_recR`: if these values are those of `g` shifted by a constant `c`, then
  `weldReadF` of the reconstruction is `weldR γ g`.

Own elementary bookkeeping (no published source needed).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm14WDG

/-! ## The welding map of a measure -/

/-- The welding map of a measure `ν` on `ℝ`: `weldR γ x = wRm (qBoundaryMeasure γ x)`. -/
def wRm (ν : Measure ℝ) (s : ℝ) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ ν (Icc s 0) ≤ ν (Icc 0 r)}

theorem weldR_eq_wRm (γ : ℝ) (x : FieldSample) (s : ℝ) :
    weldR γ x s = wRm (qBoundaryMeasure γ x) s := rfl

/-- The welding map does not see a positive finite multiple of the measure. -/
theorem wRm_smul {ν : Measure ℝ} {c : ℝ≥0∞} (h0 : c ≠ 0) (ht : c ≠ ∞) (s : ℝ) :
    wRm (c • ν) s = wRm ν s := by
  unfold wRm
  congr 1
  ext r
  simp only [mem_setOf_eq, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.mul_le_mul_iff_right h0 ht]

/-- The rational form of the welding infimum. -/
def wRq (A : ℝ≥0∞) (B : ℚ → ℝ≥0∞) : ℝ :=
  (⨅ r : ℚ, if 0 ≤ (r : ℝ) ∧ A ≤ B r then ENNReal.ofReal r else ∞).toReal

/-- The welding infimum over reals is the (measurable) infimum over rationals, for any measure. -/
theorem wRm_eq_wRq (ν : Measure ℝ) (s : ℝ) :
    wRm ν s = wRq (ν (Icc s 0)) (fun r => ν (Icc 0 r)) := by
  set S := {r : ℝ | 0 ≤ r ∧ ν (Icc s 0) ≤ ν (Icc 0 r)} with hS
  have hup : ∀ r ∈ S, ∀ r', r ≤ r' → 0 ≤ r' ∧ ν (Icc s 0) ≤ ν (Icc 0 r') :=
    fun r hr r' hrr' => ⟨hr.1.trans hrr', hr.2.trans (measure_mono (Icc_subset_Icc_right hrr'))⟩
  unfold wRm wRq
  rw [← hS]
  rcases S.eq_empty_or_nonempty with he | hne
  · rw [he, Real.sInf_empty]
    have : (⨅ r : ℚ, if 0 ≤ (r : ℝ) ∧ ν (Icc s 0) ≤ ν (Icc 0 r) then ENNReal.ofReal r
        else ∞) = ∞ := by
      refine iInf_eq_top.2 fun r => ?_
      rw [if_neg]
      intro h
      have hr : (r : ℝ) ∈ S := h
      rw [he] at hr
      exact hr
    rw [this, ENNReal.toReal_top]
  · have hbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
    have hR0 : 0 ≤ sInf S := le_csInf hne fun r hr => hr.1
    have key : (⨅ r : ℚ, if 0 ≤ (r : ℝ) ∧ ν (Icc s 0) ≤ ν (Icc 0 r) then ENNReal.ofReal r
        else ∞) = ENNReal.ofReal (sInf S) := by
      refine le_antisymm ?_ (le_iInf fun r => ?_)
      · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
        obtain ⟨a, haS, ha⟩ := Real.lt_sInf_add_pos hne (show (0 : ℝ) < ε by exact_mod_cast hε)
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ha
        have hqS := hup a haS q hq1.le
        refine (iInf_le _ q).trans ?_
        rw [if_pos hqS]
        calc ENNReal.ofReal q ≤ ENNReal.ofReal (sInf S + ε) := ENNReal.ofReal_le_ofReal hq2.le
          _ = ENNReal.ofReal (sInf S) + ε := by
            rw [← ENNReal.ofReal_coe_nnreal]; exact ENNReal.ofReal_add hR0 ε.2
      · split_ifs with h
        · exact ENNReal.ofReal_le_ofReal (csInf_le hbdd h)
        · exact le_top
    rw [key, ENNReal.toReal_ofReal hR0]

/-! ## Measurable access to `ν(Icc a b)` -/

/-- `ν(Icc a b)` computed from the measurable open-set functional `InfMass.Psi`. -/
def mIcc (γ a b : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  ⨅ n : ℕ, InfMass.Psi γ (Ioo (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1))) y

theorem measurable_mIcc (γ a b : ℝ) : Measurable (mIcc γ a b) :=
  Measurable.iInf fun _ => InfMass.measurable_Psi γ _

theorem iInter_Ioo_eq_Icc (a b : ℝ) :
    (⋂ n : ℕ, Ioo (a - 1 / ((n : ℝ) + 1)) (b + 1 / ((n : ℝ) + 1))) = Icc a b := by
  ext t
  simp only [mem_iInter, mem_Ioo, mem_Icc]
  constructor
  · intro h
    constructor
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [(h n).1]
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [(h n).2]
  · rintro ⟨h1, h2⟩ n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := Nat.one_div_pos_of_nat
    constructor <;> linarith

theorem mIcc_eq {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (a b : ℝ) : mIcc γ a b y = ν (Icc a b) := by
  have := hν.1
  unfold mIcc
  simp_rw [InfMass.Psi_eq isOpen_Ioo hν]
  rw [← iInter_Ioo_eq_Icc]
  refine (Antitone.measure_iInter (fun n m hnm => ?_)
    (fun n => measurableSet_Ioo.nullMeasurableSet) ⟨0, measure_Ioo_lt_top.ne⟩).symm
  have : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := Nat.one_div_le_one_div hnm
  exact Ioo_subset_Ioo (by linarith) (by linarith)

/-! ## The measurable reading functional -/

/-- The measurable functional reading the welding map at `q` off a field sample. -/
def weldReadF (γ : ℝ) (q : ℚ) (y : FieldSample) : ℝ :=
  wRq (mIcc γ q 0 y) (fun r => mIcc γ 0 r y)

theorem measurable_weldReadF (γ : ℝ) (q : ℚ) : Measurable (weldReadF γ q) := by
  unfold weldReadF wRq
  refine ENNReal.measurable_toReal.comp (Measurable.iInf fun r => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (MeasurableSet.const (0 ≤ (r : ℝ))).inter
    (measurableSet_le (measurable_mIcc _ _ _) (measurable_mIcc _ _ _))

theorem weldReadF_eq {γ : ℝ} {y : FieldSample} {ν : Measure ℝ}
    (hν : IsVagueLimitR (bdryApprox γ y) ν) (q : ℚ) : weldReadF γ q y = wRm ν q := by
  unfold weldReadF
  rw [wRm_eq_wRq]
  simp only [mIcc_eq hν]

/-! ## Real-centred folded circles and the reconstruction -/

/-- The real-centred dyadic folded circle with index `i = (m, n, k)`:
`foldedCircle (m / 2^n) (2^{-k})`. -/
def fcR (i : ℤ × ℕ × ℕ) : Measure ℂ :=
  foldedCircle ((((i.1 : ℝ) / (2 : ℝ) ^ i.2.1 : ℝ)) : ℂ) (radius i.2.2)

instance (i : ℤ × ℕ × ℕ) : IsProbabilityMeasure (fcR i) := by
  unfold fcR; infer_instance

theorem dyadicRoundC_ofReal (n : ℕ) (t : ℝ) :
    dyadicRoundC n (t : ℂ) = ((dyadicRound n t : ℝ) : ℂ) := by
  apply Complex.ext
  · simp only [dyadicRoundC, Complex.ofReal_re]
  · show dyadicRound n ((t : ℂ).im) = ((dyadicRound n t : ℝ) : ℂ).im
    rw [Complex.ofReal_im, Complex.ofReal_im]
    simp [dyadicRound]

/-- `bdryApprox` only reads the values at the real-centred dyadic folded circles. -/
theorem bdryApprox_congr_fcR {x x' : FieldSample} (h : ∀ i, x (fcR i) = x' (fcR i)) (γ : ℝ) :
    bdryApprox γ x = bdryApprox γ x' := by
  funext k
  have ha : ∀ t : ℝ, avgReg x k (t : ℂ) = avgReg x' k (t : ℂ) := by
    intro t
    unfold avgReg
    congr 1
    funext n
    rw [dyadicRoundC_ofReal]
    exact h (⌊(2 : ℝ) ^ n * t⌋, n, k)
  unfold bdryApprox
  simp only [ha]

open Classical in
/-- Measurable reconstruction of a field sample from values at the real-centred folded circles
(junk `0` elsewhere). -/
def recR (v : ℤ × ℕ × ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, fcR i = μ then v h.choose else 0

theorem measurable_recR : Measurable recR := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold recR
  by_cases h : ∃ i, fcR i = μ
  · simp only [h, ↓reduceDIte]; exact measurable_pi_apply _
  · simp only [h, ↓reduceDIte]; exact measurable_const

theorem recR_fcR {v : ℤ × ℕ × ℕ → ℝ} {g : FieldSample} {c : ℝ}
    (hv : ∀ i, v i = g (fcR i) + c) (i : ℤ × ℕ × ℕ) : recR v (fcR i) = addConst g c (fcR i) := by
  classical
  have h : ∃ j, fcR j = fcR i := ⟨i, rfl⟩
  simp only [recR, h, ↓reduceDIte, hv, addConst, measure_univ, ENNReal.toReal_one, mul_one]
  rw [h.choose_spec]

/-- **Reading `R` off shifted real-centred values.** If `v` lists the values of `g` at the
real-centred dyadic folded circles shifted by a constant `c`, the raw circle averages of `g`
converge on `Hbar`, and `bdryApprox γ g` has a vague limit, then `weldReadF γ q (recR v)` is
`weldR γ g q`. -/
theorem weldReadF_recR {γ : ℝ} {v : ℤ × ℕ × ℕ → ℝ} {g : FieldSample} {c : ℝ}
    (hv : ∀ i, v i = g (fcR i) + c) (hg : LocalRule.RawConverges g Hbar)
    {ν : Measure ℝ} (hν : IsVagueLimitR (bdryApprox γ g) ν) (q : ℚ) :
    weldReadF γ q (recR v) = weldR γ g q := by
  have hb : bdryApprox γ (recR v) = fun k =>
      ENNReal.ofReal (Real.exp (γ * c / 2)) • bdryApprox γ g k := by
    rw [bdryApprox_congr_fcR (recR_fcR hv) γ]
    exact funext (LocalRule.bdryApprox_addConst hg γ c)
  have hν' : IsVagueLimitR (bdryApprox γ (recR v)) (ENNReal.ofReal (Real.exp (γ * c / 2)) • ν) := by
    rw [hb]; exact BdryVague.IsVagueLimitR.const_smul hν ENNReal.ofReal_ne_top
  rw [weldReadF_eq hν', wRm_smul (LocalRule.ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top,
    weldR_eq_wRm, qBoundaryMeasure_eq hν]

end Thm14WDG
end QuantumZipper

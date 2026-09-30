import QuantumZipper.Proofs.RS.Simple
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.TraceRadial
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.Thm11.NonSwallowing
import QuantumZipper.Proofs.Thm18.G1PkgPath
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DRVGOOD: a Borel set of good driver paths

Goodness of a chordal driver (Rohde–Schramm radial Hölder bound `RS.RadialGood`, simple trace in
`ℍ`, hull = trace) is not obviously a measurable property of the driver path. For the law
transfer of Sheffield arXiv:1012.4797, Theorem 1.8 (3) (p. 26: the zipped / unzipped curve is
again an SLE curve, since its driver has the law of `√κ B`), we use a countable certificate
`Good W`:

* `CondH`: a Cauchy form of the radial Hölder bound at rational times and heights;
* `CondV`: the hulls `K_n` are Lebesgue-null;
* `CondI`, `CondP`: quantitative injectivity and `ℍ`-valuedness of the trace at rational times
  (the trace at rational times is the limit `trS` along `y = 1/(n+1)`).

On the path space `ℝ≥0 → ℝ` (product σ-algebra) the set of paths whose regularized driver `pW`
satisfies `Good` is measurable (`measurableSet_goodSet`): Loewner maps at fixed times are
measurable in the driver (`RS.measurable_fwdMapInv_drive`), the hull is jointly measurable
(`NonSwallow.measurableSet_fwdHull_prod`), and limits of measurable sequences are measurable
(mathlib `StronglyMeasurable.limUnder`). Own elementary bookkeeping (the paper leaves the
measurability implicit).
-/

noncomputable section

open MeasureTheory Filter Set Topology Complex
open scoped NNReal ENNReal

namespace QuantumZipper
namespace DrvGood

/-! ## The certificate -/

/-- The approximants `f̂_t(i/(n+1))`. -/
def aprx (W : ℝ → ℝ) (t : ℝ) (n : ℕ) : ℂ :=
  fwdMapInv W t (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I)

/-- The trace along the sequence `y = 1/(n+1)`. -/
def trS (W : ℝ → ℝ) (t : ℝ) : ℂ := limUnder atTop (aprx W t)

/-- Cauchy form of the radial Hölder bound at rational times and heights. -/
def CondH (W : ℝ → ℝ) : Prop :=
  ∃ δ : ℚ, 0 < δ ∧ ∀ N : ℕ, ∃ C : ℕ, ∀ t y y' : ℚ, 0 ≤ t → t ≤ (N : ℚ) → 0 < y → y ≤ 1 →
    0 < y' → y' ≤ 1 →
      ‖fwdMapInv W (t : ℝ) (((y : ℝ) : ℂ) * I) - fwdMapInv W (t : ℝ) (((y' : ℝ) : ℂ) * I)‖ ≤
        (C : ℝ) * ((y : ℝ) ^ (δ : ℝ) + (y' : ℝ) ^ (δ : ℝ))

/-- Null hulls. -/
def CondV (W : ℝ → ℝ) : Prop := ∀ n : ℕ, volume (fwdHull W n) = 0

/-- Quantitative injectivity of the trace at rational times. -/
def CondI (W : ℝ → ℝ) : Prop :=
  ∀ p q r s : ℚ, 0 ≤ p → p < q → q < r → r < s → ∃ m : ℕ, ∀ u v : ℚ, p ≤ u → u ≤ q → r ≤ v →
    v ≤ s → 1 / ((m : ℝ) + 1) ≤ ‖trS W u - trS W v‖

/-- Quantitative `ℍ`-valuedness of the trace at rational times. -/
def CondP (W : ℝ → ℝ) : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → ∃ m : ℕ, ∀ u : ℚ, a ≤ u → u ≤ b → 1 / ((m : ℝ) + 1) ≤ (trS W u).im

/-- The countable goodness certificate. -/
def Good (W : ℝ → ℝ) : Prop := CondH W ∧ CondV W ∧ CondI W ∧ CondP W

/-! ## The path space -/

/-- The regularized path process on the path space (continuous, started at `0`). -/
def pB (t : ℝ≥0) (x : ℝ≥0 → ℝ) : ℝ :=
  Thm18Asm.G1Pkg.pathReg x t - Thm18Asm.G1Pkg.pathReg x 0

/-- The driver of a path. -/
def pW (x : ℝ≥0 → ℝ) : ℝ → ℝ := drive 1 pB x

/-- The good paths. -/
def goodSet : Set (ℝ≥0 → ℝ) := {x | Good (pW x)}

theorem measurable_pB (t : ℝ≥0) : Measurable (pB t) := by
  have hm := Thm18Asm.G1Pkg.pathReg_spec.1
  exact (measurable_pi_iff.1 hm t).sub (measurable_pi_iff.1 hm 0)

theorem continuous_pB (x : ℝ≥0 → ℝ) : Continuous fun t => pB t x :=
  (Thm18Asm.G1Pkg.pathReg_spec.2.1 x).sub continuous_const

theorem pB_zero (x : ℝ≥0 → ℝ) : pB 0 x = 0 := sub_self _

/-- The driver of the path of a continuous driver `W` with `W 0 = 0`, constant on `(-∞,0]`. -/
theorem pW_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (hmax : ∀ r, W r = W (max r 0)) :
    pW (fun t : ℝ≥0 => W t) = W := by
  have hc : Continuous fun t : ℝ≥0 => W t := hW.comp continuous_subtype_val
  have hr := Thm18Asm.G1Pkg.pathReg_spec.2.2 _ hc
  funext r
  simp only [pW, drive, pB, hr, Real.sqrt_one, one_mul, NNReal.coe_zero, hW0, sub_zero,
    Real.coe_toNNReal']
  exact (hmax r).symm

theorem im_ofReal_mul_I (y : ℝ) : (((y : ℝ) : ℂ) * I).im = y := by simp

theorem measurable_fwdMapInv_pW {t : ℝ} (ht : 0 ≤ t) {w : ℂ} (hw : 0 < w.im) :
    Measurable fun x => fwdMapInv (pW x) t w :=
  RS.measurable_fwdMapInv_drive measurable_pB continuous_pB pB_zero 1 ht hw

theorem measurable_trS {t : ℝ} (ht : 0 ≤ t) : Measurable fun x => trS (pW x) t := by
  have h : ∀ n : ℕ, Measurable fun x => aprx (pW x) t n := fun n =>
    measurable_fwdMapInv_pW ht (by rw [im_ofReal_mul_I]; positivity)
  exact (StronglyMeasurable.limUnder (l := atTop) (f := fun n x => aprx (pW x) t n)
    fun n => (h n).stronglyMeasurable).measurable

theorem measurable_imp_const {α : Type*} [MeasurableSpace α] {P : Prop} {q : α → Prop}
    (h : P → Measurable q) : Measurable fun a => P → q a := by
  by_cases hP : P
  · simpa [hP] using h hP
  · simp [hP]

theorem measurable_le_prop {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    (c : ℝ) : Measurable fun a => c ≤ f a :=
  measurableSet_setOfPred.1 (measurableSet_le measurable_const hf)

theorem measurable_le_prop' {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    (c : ℝ) : Measurable fun a => f a ≤ c :=
  measurableSet_setOfPred.1 (measurableSet_le hf measurable_const)

theorem measurable_condH : Measurable fun x => CondH (pW x) := by
  refine Measurable.exists fun δ => measurable_const.and (Measurable.forall fun N =>
    Measurable.exists fun C => Measurable.forall fun t => Measurable.forall fun y =>
      Measurable.forall fun y' => ?_)
  refine measurable_imp_const fun ht => measurable_imp_const fun _ => measurable_imp_const
    fun hy => measurable_imp_const fun _ => measurable_imp_const fun hy' =>
      measurable_imp_const fun _ => ?_
  have ht' : (0 : ℝ) ≤ t := by exact_mod_cast ht
  have hy1 : 0 < ((((y : ℝ)) : ℂ) * I).im := by rw [im_ofReal_mul_I]; exact_mod_cast hy
  have hy2 : 0 < ((((y' : ℝ)) : ℂ) * I).im := by rw [im_ofReal_mul_I]; exact_mod_cast hy'
  exact measurable_le_prop'
    ((measurable_fwdMapInv_pW ht' hy1).sub (measurable_fwdMapInv_pW ht' hy2)).norm _

theorem measurable_condV : Measurable fun x => CondV (pW x) := by
  refine Measurable.forall fun n => ?_
  have hS := NonSwallow.measurableSet_fwdHull_prod measurable_pB continuous_pB 1
    (T := (n : ℝ)) (Nat.cast_nonneg n)
  exact (measurable_measure_prodMk_right (μ := (volume : Measure ℂ)) hS).eq_const 0

theorem measurable_condI : Measurable fun x => CondI (pW x) := by
  refine Measurable.forall fun p => Measurable.forall fun q => Measurable.forall fun r =>
    Measurable.forall fun s => measurable_imp_const fun hp => measurable_imp_const fun _ =>
      measurable_imp_const fun _ => measurable_imp_const fun _ => Measurable.exists fun m =>
        Measurable.forall fun u => Measurable.forall fun v => ?_
  refine measurable_imp_const fun hu => measurable_imp_const fun _ => measurable_imp_const
    fun hv => measurable_imp_const fun _ => ?_
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast hp.trans hu
  have hv' : (0 : ℝ) ≤ v := by
    have : (0 : ℚ) ≤ v := by linarith
    exact_mod_cast this
  exact measurable_le_prop ((measurable_trS hu').sub (measurable_trS hv')).norm _

theorem measurable_condP : Measurable fun x => CondP (pW x) := by
  refine Measurable.forall fun a => Measurable.forall fun b => measurable_imp_const fun ha =>
    measurable_imp_const fun _ => Measurable.exists fun m => Measurable.forall fun u => ?_
  refine measurable_imp_const fun hu => measurable_imp_const fun _ => ?_
  have hu' : (0 : ℝ) ≤ u := by
    have : (0 : ℚ) ≤ u := by linarith
    exact_mod_cast this
  exact measurable_le_prop (Complex.measurable_im.comp (measurable_trS hu')) _

/-- **The good paths form a measurable set.** -/
theorem measurableSet_goodSet : MeasurableSet goodSet :=
  measurableSet_setOfPred.2
    (measurable_condH.and (measurable_condV.and (measurable_condI.and measurable_condP)))

end DrvGood
end QuantumZipper

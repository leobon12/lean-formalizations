import QuantumZipper.Proofs.Thm18.G4ZipUp2Basic
import QuantumZipper.Proofs.Thm18.G4Read2Bdry
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: a measurable continuous path on `[0,1]` read from a driver

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4-ZIPUP2.

From a measurably read pair `(T, W') = F d` we build a path `drvPath F d ∈ C([0,1], ℝ)` which is

* a measurable function of `d` (`measurable_drvPath`) and continuous **for every** `d` (it is an
  element of `C([0,1], ℝ)` by construction), with `drvPath F d 0 = 0`;
* the Brownian rescaling `s ↦ W'(T s)/√T` of the driver whenever `T > 0`, `W'` is continuous and
  `W' 0 = 0` (`drvPath_apply`), so that `sclDrv (drvPath F d, T) = W'` on `[0,T]`
  (`sclDrv_drvPath_eqOn`).

Construction: the piecewise-linear dyadic surrogates `surScaled n n T W'` (`G4ZipUp2Basic.lean`)
are measurable `C([0,1], ℝ)`-valued functions of `d`; `drvPath` is their limit
(`limUnder` in the Polish space `C([0,1], ℝ)`, measurable by
`MeasureTheory.StronglyMeasurable.limUnder`), recentred at `0`. For a continuous driver the
surrogates converge uniformly (`tendsto_surDrv_uniform`), so the limit is the rescaled driver;
otherwise `limUnder` returns *some* continuous path, which is harmless.

**Own elementary argument** (measurable continuous modification; no published source needed:
dyadic interpolation, Heine–Cantor, completeness of `C([0,1], ℝ)`).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- The `n`-th surrogate path on `[0,1]`: `s ↦ surScaled n n T W' s`. -/
def surPath (n : ℕ) (T : ℝ) (W' : ℝ → ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun s => surScaled n n T W' s.1, (continuous_surScaled n n T W').comp continuous_subtype_val⟩

theorem measurable_surPath_comp {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) (n : ℕ) :
    Measurable fun d => surPath n (F d).1 (F d).2 :=
  ContinuousMap.measurable_iff_eval.2 fun s => measurable_surScaled hF1 hF2 n n s.1

/-- The limit of the surrogate paths (junk, but still a continuous path, if there is no limit). -/
def limPath (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : C(Icc (0 : ℝ) 1, ℝ) :=
  limUnder atTop fun n => surPath n (F d).1 (F d).2

/-- The path read from the driver, recentred so that it vanishes at `0`. -/
def drvPath (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) : C(Icc (0 : ℝ) 1, ℝ) :=
  limPath F d - ContinuousMap.const _ (limPath F d ⟨0, left_mem_Icc.2 zero_le_one⟩)

theorem drvPath_zero (F : E6.FullData → ℝ × (ℝ → ℝ)) (d : E6.FullData) :
    drvPath F d ⟨0, left_mem_Icc.2 zero_le_one⟩ = 0 := by
  simp [drvPath]

theorem measurable_limPath {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) :
    Measurable (limPath F) :=
  (StronglyMeasurable.limUnder fun n =>
    (measurable_surPath_comp hF1 hF2 n).stronglyMeasurable).measurable

theorem measurable_drvPath {F : E6.FullData → ℝ × (ℝ → ℝ)}
    (hF1 : Measurable fun d => (F d).1)
    (hF2 : Measurable fun q : E6.FullData × ℝ => (F q.1).2 q.2) :
    Measurable (drvPath F) := by
  have hL := measurable_limPath hF1 hF2
  refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
  have h1 : Measurable fun d => limPath F d s := (continuous_eval_const s).measurable.comp hL
  have h0 : Measurable fun d => limPath F d ⟨0, left_mem_Icc.2 zero_le_one⟩ :=
    (continuous_eval_const _).measurable.comp hL
  exact h1.sub h0

/-- The rescaled driver `s ↦ (W'(T s) − W' 0)/√T` as a path on `[0,1]`. -/
def resPath0 (T : ℝ) (W' : ℝ → ℝ) (hW : Continuous W') : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun s => (W' (T * s.1) - W' 0) / Real.sqrt T,
    ((hW.comp (continuous_const.mul continuous_subtype_val)).sub continuous_const).div_const _⟩

/-- For a continuous driver the surrogate paths converge uniformly to the rescaled driver. -/
theorem tendsto_surPath {T : ℝ} (hT : 0 < T) {W' : ℝ → ℝ} (hW : Continuous W') :
    Tendsto (fun n => surPath n T W') atTop (𝓝 (resPath0 T W' hW)) := by
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have hε' : 0 < ε / 2 * Real.sqrt T := by positivity
  filter_upwards [tendsto_surDrv_uniform hW ⌈T⌉₊ _ hε', eventually_ge_atTop ⌈T⌉₊] with n hn hnN
  refine lt_of_le_of_lt ((ContinuousMap.dist_le (by positivity)).2 fun s => ?_)
    (half_lt_self hε)
  have hs := s.2
  have hTs : T * s.1 ∈ Icc (0 : ℝ) ⌈T⌉₊ :=
    ⟨mul_nonneg hT.le hs.1, (mul_le_of_le_one_right hT.le hs.2).trans (Nat.le_ceil T)⟩
  have h := hn n hnN _ hTs
  show dist ((surDrv n n W' (T * s.1) - WedgeLaw.extP W' 0) / Real.sqrt T)
    ((W' (T * s.1) - W' 0) / Real.sqrt T) ≤ ε / 2
  rw [WedgeLaw.extP_of_continuous hW, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hsT,
    div_le_iff₀ hsT]
  have : surDrv n n W' (T * s.1) - W' 0 - (W' (T * s.1) - W' 0) =
      surDrv n n W' (T * s.1) - W' (T * s.1) := by ring
  rw [this]
  exact h

/-- **Identification.** For a continuous driver with `W' 0 = 0` at a time `T > 0`, the read path
is the Brownian rescaling of the driver. -/
theorem drvPath_eq {F : E6.FullData → ℝ × (ℝ → ℝ)} {d : E6.FullData} (hT : 0 < (F d).1)
    (hW : Continuous (F d).2) (hW0 : (F d).2 0 = 0) :
    drvPath F d = resPath0 (F d).1 (F d).2 hW := by
  have hL : limPath F d = resPath0 (F d).1 (F d).2 hW := (tendsto_surPath hT hW).limUnder_eq
  ext s
  simp only [drvPath, hL, ContinuousMap.sub_apply, ContinuousMap.const_apply]
  simp [resPath0, hW0]

/-- The Brownian-scaled driver of the read path agrees with the driver on `[0,T]`. -/
theorem sclDrv_drvPath_eqOn {F : E6.FullData → ℝ × (ℝ → ℝ)} {d : E6.FullData}
    (hT : 0 < (F d).1) (hW : Continuous (F d).2) (hW0 : (F d).2 0 = 0) :
    EqOn (sclDrv (drvPath F d, (F d).1)) (F d).2 (Icc 0 (F d).1) := by
  intro r hr
  have hsT : 0 < Real.sqrt (F d).1 := Real.sqrt_pos.2 hT
  have hmem : r / (F d).1 ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hr.1 hT.le, (div_le_one hT).2 hr.2⟩
  show Real.sqrt (F d).1 * extIccPath zero_le_one (drvPath F d) (r / (F d).1) = (F d).2 r
  rw [extIccPath_of_mem zero_le_one _ hmem, drvPath_eq hT hW hW0]
  show Real.sqrt (F d).1 * (((F d).2 ((F d).1 * (r / (F d).1)) - (F d).2 0) /
    Real.sqrt (F d).1) = (F d).2 r
  rw [mul_div_cancel₀ _ hT.ne', hW0, sub_zero, mul_div_cancel₀ _ hsT.ne']

end Thm18Asm
end QuantumZipper

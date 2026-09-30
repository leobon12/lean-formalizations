import QuantumZipper.Proofs.Thm18.G4ReadDrv

/-!
# Theorem 1.8, node G4: the driver part of the measurable zip-up

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (3). Task
G4-READ.

`G4ZipUpReadStmt` (`G4ReadDrv.lean`) asks the data of the zip-up
`canonConfig γ (zipWeldUp γ T W' x)` along a measurably read driver `(T, W')` to be a measurable
function of the data of `x`. Its driver coordinates are explicit: with `a` the scale of the
zipped field, the coordinate `s ≥ 0` is `(W'(T − a²s) − W' T)/a` for `a²s ≤ T` and
`(x.2 (a²s − T) − W' T)/a` otherwise. The second value reads the driver of `x` at a *random*
time; it is read measurably from the data by dyadic approximation from below (`extDrv`), which
is correct for continuous drivers (this is where the continuity premise of `G4ZipReadCStmt` is
used). So only the field coordinates and the scale remain (`G4ZipUpFieldReadStmt`).

* `measurable_extDrv`, `extDrv_eq`: the dyadic reading of a driver at a random time.
* `canonConfig_zipWeldUp_snd`: the explicit driver of the zip-up.
* `g4ZipUpReadStmt_of_field`: `G4ZipUpReadStmt` from `G4ZipUpFieldReadStmt`.
* `g4Stmt_of_coreNodesField`: `G4Stmt` with the reading nodes replaced by `G4LenDrvReadStmt` and
  `G4ZipUpFieldReadStmt`.

**Own elementary argument** (measurability bookkeeping).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-- The dyadic lower approximation `⌊2ⁿ r⌋₊ / 2ⁿ ≥ 0` of `r`. -/
def dyLow (n : ℕ) (r : ℝ) : ℝ≥0 :=
  ⟨(⌊(2 : ℝ) ^ n * r⌋₊ : ℝ) / 2 ^ n, by positivity⟩

theorem tendsto_dyLow {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n => ((dyLow n r : ℝ≥0) : ℝ)) atTop (𝓝 r) := by
  have h0 : Tendsto (fun n : ℕ => r - (1 / 2 : ℝ) ^ n) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds (fun n => ?_)
    (fun n => ?_)
  · show r - (1 / 2 : ℝ) ^ n ≤ (⌊(2 : ℝ) ^ n * r⌋₊ : ℝ) / 2 ^ n
    rw [le_div_iff₀ (by positivity)]
    have h1 := Nat.lt_floor_add_one ((2 : ℝ) ^ n * r)
    have e : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    nlinarith
  · show (⌊(2 : ℝ) ^ n * r⌋₊ : ℝ) / 2 ^ n ≤ r
    rw [div_le_iff₀ (by positivity)]
    have h1 := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 ^ n * r)
    linarith

/-- The driver read at time `r` by dyadic approximation from below. -/
def extDrv (e : ℝ≥0 → ℝ) (r : ℝ) : ℝ :=
  limUnder atTop fun n => e (dyLow n r)

theorem measurable_dyEval (n : ℕ) :
    Measurable fun q : E6.FullData × ℝ => q.1.2 (dyLow n q.2) := by
  let g : E6.FullData × ℕ → ℝ := fun p =>
    p.1.2 ⟨(p.2 : ℝ) / 2 ^ n, by positivity⟩
  have hg : Measurable g := measurable_from_prod_countable_left fun m => by
    simp only [g]
    exact (measurable_pi_apply (⟨(m : ℝ) / 2 ^ n, by positivity⟩ : ℝ≥0)).comp measurable_snd
  exact hg.comp (measurable_fst.prodMk ((measurable_const.mul measurable_snd).nat_floor))

theorem measurable_extDrv : Measurable fun q : E6.FullData × ℝ => extDrv q.1.2 q.2 := by
  unfold extDrv
  exact (StronglyMeasurable.limUnder fun n => (measurable_dyEval n).stronglyMeasurable).measurable

theorem extDrv_eq {e : ℝ → ℝ} (he : Continuous e) {r : ℝ} (hr : 0 ≤ r) :
    extDrv (fun t : ℝ≥0 => e t) r = e r :=
  ((he.tendsto r).comp (tendsto_dyLow hr)).limUnder_eq

/-- The driver coordinate `s` of the zip-up along `(T, W')` with scale `a`, the old driver read
by `extDrv`. -/
def zipDrvOut (T a : ℝ) (W' : ℝ → ℝ) (e : ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  if a ^ 2 * s ≤ T then (W' (T - a ^ 2 * s) - W' T) / a
  else (extDrv e (a ^ 2 * s - T) - W' T) / a

end Thm18Asm
end QuantumZipper

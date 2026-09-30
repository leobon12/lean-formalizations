import QuantumZipper.Proofs.Zipper.F1ReadMeasPath
import QuantumZipper.Proofs.RS.RealAlive
import QuantumZipper.Proofs.Probability.BrownianPathMeas

/-!
# READLEN, path part (2): the dyadic read-off of `√κ B` is a.s. good (canonical space)

Theorem 1.3, node F1d input (d) (`F1.ReadLenAEMeasStmt`). **`readPathGoodStmt_holds`**: for
`0 < κ ≤ 4` and a Brownian motion `B`, for the law `ν` of `√κ B` on `ℝ≥0 → ℝ` (product
σ-algebra), `ν`-a.s. the read-off `readDrv p` carries the continuity certificate `DyUC`, starts at `0` and keeps every real
`x ≠ 0` alive up to time `1` (`PathGood`).

The difficulty is that "every real point is alive" is not known to be an event of the product
σ-algebra, so the a.s. statement for `B` (`RS.ae_real_alive`) cannot simply be pushed forward.
Instead we run `RS.ae_real_alive` **on the canonical space** `(ℝ≥0 → ℝ, ν)` itself, for the
canonical process `canB κ t p = readDrv p t / √κ` (on the measurable certificate `DyUC`,
`0` elsewhere): it is a Brownian motion under `ν` (its finite-dimensional laws are those of
`B`, since `canB κ t = p t / √κ` `ν`-a.s., and its paths are continuous on `DyUC`, which has full
`ν`-measure by `dyUC_of_continuous`), and its driver `√κ · canB κ` is `readDrv p` on `[0,∞)`.
Then `∀ᵐ p ∂ν` is exactly the required statement, with no measurability of the alive event.

Sources: Rohde–Schramm, *Basic properties of SLE*, Lemma 6.2 / Theorem 6.1 (`RS.ae_real_alive`,
real points are never swallowed for `κ ≤ 4`); the canonical-space transfer is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace F1

theorem measurable_readDrv_eval (u : ℝ) : Measurable fun p : ℝ≥0 → ℝ => readDrv p u := by
  have h1 : Measurable fun p : ℝ≥0 → ℝ => ((fun r : ℝ => p r.toNNReal), u) :=
    (measurable_pi_iff.2 fun r => measurable_pi_apply _).prodMk measurable_const
  exact B4d.measurable_pathExt.comp h1

open Classical in
/-- The canonical process on path space: the dyadic read-off scaled by `1/√κ`, on the
certificate `DyUC`. -/
def canB (κ : ℝ) (t : ℝ≥0) (p : ℝ≥0 → ℝ) : ℝ := if DyUC p then readDrv p t / Real.sqrt κ else 0

theorem measurable_canB (κ : ℝ) (t : ℝ≥0) : Measurable (canB κ t) := by
  classical
  exact Measurable.ite measurableSet_dyUC ((measurable_readDrv_eval t).div_const _)
    measurable_const

/-- **The path part of READLEN** (proved below, `readPathGoodStmt_holds`). For `0 < κ ≤ 4` and
a Brownian motion `B`, the dyadic read-off of the driver `√κ B` is a.s. (law of `√κ B` on
`ℝ≥0 → ℝ`) good: it carries the continuity certificate `DyUC`, starts at `0`, and keeps every
real `x ≠ 0` alive up to time `1`. -/
def ReadPathGoodStmt (κ : ℝ) : Prop :=
  0 < κ → κ ≤ 4 → ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure P → IsBrownianReal B P →
    ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), PathGood p

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

omit [MeasurableSpace Ω] in
theorem readDrv_drivePath (κ : ℝ) {ω : Ω} (hc : Continuous fun t => B t ω) :
    readDrv (drivePath κ (pathOf B ω)) = drive κ B ω := by
  rw [← drive_nnreal]
  exact readDrv_eq (continuous_drive_of κ hc) (drive_toNNReal κ B ω)

omit [MeasurableSpace Ω] in
theorem canB_drivePath {κ : ℝ} (hκ : 0 < κ) {ω : Ω} (hc : Continuous fun t => B t ω)
    (t : ℝ≥0) : canB κ t (drivePath κ (pathOf B ω)) = B t ω := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hp : Continuous (drivePath κ (pathOf B ω)) := by
    rw [← drive_nnreal]; exact (continuous_drive_of κ hc).comp NNReal.continuous_coe
  classical
  simp only [canB, dyUC_of_continuous hp, ↓reduceIte, readDrv_drivePath κ hc, drive,
    Real.toNNReal_coe]
  field_simp

/-- **The canonical process is a Brownian motion under the law of `√κ B`.** -/
theorem isBrownianReal_canB {κ : ℝ} (hκ : 0 < κ) (hB : IsBrownianReal B P) :
    IsBrownianReal (canB κ) (P.map fun ω => drivePath κ (pathOf B ω)) := by
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hφ : AEMeasurable (fun ω => drivePath κ (pathOf B ω)) P :=
    (measurable_drivePath κ).comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)
  set E : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun t p => p t / Real.sqrt κ with hEdef
  have hpre : IsPreBrownianReal E (P.map fun ω => drivePath κ (pathOf B ω)) := by
    refine ⟨fun I => ⟨?_, ?_⟩⟩
    · exact (measurable_pi_iff.2 fun i => (measurable_pi_apply _).div_const _).aemeasurable
    · have hg : Measurable fun p : ℝ≥0 → ℝ => I.restrict fun t => E t p :=
        measurable_pi_iff.2 fun i => (measurable_pi_apply _).div_const _
      rw [AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hφ]
      have e : ((fun p : ℝ≥0 → ℝ => I.restrict fun t => E t p) ∘
          fun ω => drivePath κ (pathOf B ω)) = fun ω => I.restrict fun t => B t ω := by
        funext ω i
        simp only [Function.comp_apply, Finset.restrict, hEdef, drivePath, pathOf]
        field_simp
      rw [e]
      exact (hB.toIsPreBrownianReal.hasLaw I).map_eq
  have hcongr : ∀ t, E t =ᵐ[P.map fun ω => drivePath κ (pathOf B ω)] canB κ t := by
    intro t
    have hm : MeasurableSet {p : ℝ≥0 → ℝ | E t p = canB κ t p} :=
      measurableSet_eq_fun ((measurable_pi_apply _).div_const _) (measurable_canB κ t)
    refine (ae_map_iff hφ hm).2 ?_
    filter_upwards [hB.cont] with ω hc
    show drivePath κ (pathOf B ω) t / Real.sqrt κ = _
    rw [canB_drivePath hκ hc]
    simp only [drivePath, pathOf]
    field_simp
  refine ⟨hpre.congr hcongr, ?_⟩
  have hUC : ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), DyUC p := by
    refine (ae_map_iff hφ measurableSet_dyUC).2 ?_
    filter_upwards [hB.cont] with ω hc
    refine dyUC_of_continuous ?_
    rw [← drive_nnreal]; exact (continuous_drive_of κ hc).comp NNReal.continuous_coe
  filter_upwards [hUC] with p hp
  classical
  have e : (fun t => canB κ t p) = fun t : ℝ≥0 => readDrv p t / Real.sqrt κ := by
    funext t; simp only [canB, hp, ↓reduceIte]
  rw [e]
  exact ((continuous_readDrv_of_dyUC hp).comp NNReal.continuous_coe).div_const _

/-- **The path part holds**: `ReadPathGoodStmt κ` for every `κ`. -/
theorem readPathGoodStmt_holds (κ : ℝ) : ReadPathGoodStmt κ := by
  intro hκ hκ4 Ω _ P B hPr hB
  have hs : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  have hφ : AEMeasurable (fun ω => drivePath κ (pathOf B ω)) P :=
    (measurable_drivePath κ).comp_aemeasurable (IsBrownianReal.aemeasurable_pathOf hB)
  have hB' := isBrownianReal_canB hκ hB
  have hUC : ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), DyUC p := by
    refine (ae_map_iff hφ measurableSet_dyUC).2 ?_
    filter_upwards [hB.cont] with ω hc
    refine dyUC_of_continuous ?_
    rw [← drive_nnreal]; exact (continuous_drive_of κ hc).comp NNReal.continuous_coe
  have h0 : ∀ᵐ p ∂(P.map fun ω => drivePath κ (pathOf B ω)), p 0 = 0 := by
    refine (ae_map_iff hφ (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const)).2 ?_
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω h
    simp only [drivePath, pathOf, h, mul_zero]
  filter_upwards [hUC, h0, RS.ae_real_alive hB' hκ hκ4] with p hp hp0 halive
  refine ⟨hp, by rw [readDrv_zero, hp0], fun x hx => ?_⟩
  obtain ⟨v, hv⟩ := halive x hx 1 zero_le_one
  refine ⟨v, isForwardSol_congr_drive (fun r hr => ?_) hv⟩
  classical
  simp only [drive, canB, hp, ↓reduceIte, Real.coe_toNNReal _ hr.1]
  field_simp

end F1
end QuantumZipper

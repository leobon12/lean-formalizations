/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuReach
import InteractingSLE.Spec.Supplement.GW2BfJ32Near
import InteractingSLE.Spec.Supplement.GW2RvSlow

/-!
# Reach from a target visit at a root `x`

Packet PROVE-GW2-BUF (round 18; clause (iii) of `VNearImgOn` at a root `x`). J32's sample of a candidate reads its
start plus the dilated, oriented increment of J32's reader (`GW2Bf.j32Sample_snd`). The start is the history start
(`GW2Bf.ae_j32Start_eq_histStart`), and the increment is the stage driver of the corrected root-`x` instance
(`GW2Rv.ae_j32DriverId_schedInstSX`) below the gain and below the version's cap. A visit of the dilated stage driver
above `2 + 1/8` before such a stop therefore puts the sample in the reach set (`mem_reachSet_of_scaled_target_before`).

* **`ae_reach_of_visit_instX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- `q < 4^k τ` gives `q / 4^k < τ`. -/
theorem div_four_pow_lt' {q : ℝ≥0} (k : ℕ) {τ : ℝ≥0∞} (h : ((q : ℝ≥0) : ℝ≥0∞) < (4 : ℝ≥0∞) ^ k * τ) :
    ((q / (4 : ℝ≥0) ^ k : ℝ≥0) : ℝ≥0∞) < τ := by
  have h4 : ((4 : ℝ≥0) ^ k : ℝ≥0) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h4' : ((((4 : ℝ≥0) ^ k : ℝ≥0)) : ℝ≥0∞) = (4 : ℝ≥0∞) ^ k := by push_cast; rfl
  rw [ENNReal.coe_div h4, ENNReal.div_lt_iff (Or.inl (by rw [h4']; exact pow_ne_zero _ (by norm_num)))
    (Or.inl (by rw [h4']; exact ENNReal.pow_ne_top (by norm_num))), h4', mul_comm]
  exact h

/-- **Reach from a dilated target visit of the root-`x` stage driver** before a stop below the gain and the cap. -/
theorem ae_reach_of_visit_instX (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hord : GW2Sdx.HistOrdered c r l)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hA : IsRelVersionXA (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V)
    (ch : GW2Sdh.SchedChoice Ω) :
    ∀ᵐ ξ ∂c.P, ∀ (lam : ℝ) (τ : ℝ≥0∞) (t : ℝ≥0), 0 < lam →
      GW2Bf.histStart c r l ξ < 2 + 1 / 8 → lam * (2 + 1 / 8 - GW2Bf.histStart c r l ξ) ≤ 2 + 1 / 8 →
      τ ≤ (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) → τ ≤ V ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) →
      (t : ℝ≥0∞) < (4 : ℝ≥0∞) ^ r.2 * τ →
      2 + 1 / 8 < lam * ((-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
        (schedInstSX c r l a (schedGTX h13 c r l a) hA ch).drvX c (rootPt r.1) (t / (4 : ℝ≥0) ^ r.2) ξ)) →
      RootJ32.sourceSample c r l a ξ ∈ RootD25.reachSet := by
  filter_upwards [GW2Bf.ae_j32Start_eq_histStart h13 c r l (GW2Bf.v0_le_historyTime c r l hord),
    ae_j32DriverId_schedInstSX h13 c r l a hx hA ch] with ξ hst hd lam τ t hlam hS hscale hτg hτV ht hvis
  have hW : Continuous fun t : ℝ≥0 => (-1 : ℝ) ^ l.length * ((2 : ℝ) ^ r.2 *
      (schedInstSX c r l a (schedGTX h13 c r l a) hA ch).drvX c (rootPt r.1) (t / (4 : ℝ≥0) ^ r.2) ξ) :=
    continuous_const.mul (continuous_const.mul
      ((GW2Rd.continuous_stgDrv (hA.1.1.2.1 ξ) _).comp (continuous_id.div_const _)))
  have hz1 : (RootJ32.sourceSample c r l a ξ).1 = (4 : ℝ≥0∞) ^ r.2 * (GW2Sdg.rootGain c r l a ξ : ℝ≥0∞) :=
    GW2Bf.j32Sample_fst c r l a ξ
  have hτz : (4 : ℝ≥0∞) ^ r.2 * τ ≤ (RootJ32.sourceSample c r l a ξ).1 := by
    rw [hz1]
    exact mul_le_mul_right hτg _
  refine mem_reachSet_of_scaled_target_before hW hτz (fun q hq => ?_) hlam hS hscale ht hvis
  have hqz : ((q : ℝ≥0) : ℝ≥0∞) < (RootJ32.sourceSample c r l a ξ).1 := hq.trans_le hτz
  have hlive : 0 < (RootJ31.sourceSample c r l a ξ).1 :=
    lt_of_le_of_lt zero_le (hqz.trans_eq (RootJ32.sourceSample_fst c r l a ξ))
  have hu : (q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 < GW2Sdg.rootGain c r l a ξ :=
    GW2Sdg.div_four_pow_lt r.2 (by rw [← hz1]; exact hqz)
  have huV : (((q : ℝ≥0) / (4 : ℝ≥0) ^ r.2 : ℝ≥0) : ℝ≥0∞) < V ξ - (GW2Sdg.rootHistCap c r l a ξ : ℝ≥0∞) :=
    (div_four_pow_lt' r.2 hq).trans_le hτV
  rw [GW2Bf.j32Sample_snd c r l a ξ hqz, hst a hlive, hd _ hu huV]

end InteractingSLE.Theorem14.GW2Bh

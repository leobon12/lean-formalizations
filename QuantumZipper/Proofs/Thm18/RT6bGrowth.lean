import QuantumZipper.Proofs.Thm18.RT6bUnz
import QuantumZipper.Proofs.Thm18.RTHmpMain
import QuantumZipper.Proofs.Thm18.R18ZipFacDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT6b: log growth of the circle averages of the unzipped field (`UnzGrowthStmt`)

The log growth of the raw folded-circle averages (Hu–Miller–Peres, Ann. Probab. 38 (2010),
Prop. 2.1; `circAvgLogGrowthStmt_holds` at the wedge) is a Borel event of the circle coordinates
(`growthSet`: dyadic circles are coordinates, `CoordsFull.fullIndex_surj`). The unzipped
configuration `Z^A_{−b} c₀` has the full-data law of `c₀` (E6, `map_cfgData_zipLenDownA`), so the
event transfers. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm CoordsFull

/-- The Borel set of coordinate vectors with log growth at dyadic radii on bounded sets. -/
def growthSet : Set (ℕ → ℝ) :=
  ⋂ R : ℕ, ⋃ C : ℕ, ⋂ i : ℕ, ⋂ k : ℕ,
    {c | (fullIndex i).2 = radius k → ‖(fullIndex i).1‖ ≤ R → |c i| ≤ C * (k + 1)}

theorem measurableSet_growthSet : MeasurableSet growthSet := by
  refine MeasurableSet.iInter fun R => MeasurableSet.iUnion fun C =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  by_cases h : (fullIndex i).2 = radius k ∧ ‖(fullIndex i).1‖ ≤ R
  · have e : {c : ℕ → ℝ | (fullIndex i).2 = radius k → ‖(fullIndex i).1‖ ≤ R →
        |c i| ≤ C * (k + 1)} = {c : ℕ → ℝ | |c i| ≤ (C : ℝ) * ((k : ℝ) + 1)} := by
      ext c; simp [h.1, h.2]
    rw [e]
    exact measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply i))
      measurable_const
  · have e : {c : ℕ → ℝ | (fullIndex i).2 = radius k → ‖(fullIndex i).1‖ ≤ R →
        |c i| ≤ C * (k + 1)} = univ := by
      ext c; simp only [mem_setOf_eq, mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e]; exact MeasurableSet.univ

theorem coordsFull_mem_growthSet {x : FieldSample}
    (h : ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
      |x (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1)) :
    coordsFull x ∈ growthSet := by
  simp only [growthSet, mem_iInter, mem_iUnion, mem_setOf_eq]
  intro R
  obtain ⟨C, hC, hb⟩ := h R
  refine ⟨⌈C⌉₊, fun i k hr hn => ?_⟩
  have hfix : dyadicRoundC (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) i).2.2.1 (fullIndex i).1 =
      (fullIndex i).1 :=
    RTHmp.dyadicRoundC_fixed le_rfl (a := (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) i).1)
      (b := (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) i).2.1) (by simp only [fullIndex])
      (by simp only [fullIndex])
  have e : coordsFull x i = x (foldedCircle (dyadicRoundC
      (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) i).2.2.1 (fullIndex i).1) (radius k)) := by
    unfold coordsFull
    rw [hfix, hr]
  rw [e]
  refine (hb k _ _ hn).trans ?_
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil C) (by positivity)

theorem growth_of_mem_growthSet {x : FieldSample} (h : coordsFull x ∈ growthSet) :
    ∀ Rr : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k n : ℕ) (w : ℂ), ‖w‖ ≤ Rr →
      |x (foldedCircle (dyadicRoundC n w) (radius k))| ≤ C * (k + 1) := by
  simp only [growthSet, mem_iInter, mem_iUnion, mem_setOf_eq] at h
  intro Rr
  obtain ⟨C, hC⟩ := h (⌈Rr⌉₊ + 2)
  refine ⟨C, by positivity, fun k n w hw => ?_⟩
  obtain ⟨i, hi⟩ := fullIndex_surj n w 1 one_pos k
  rw [← radius_eq_div] at hi
  have hn : ‖(fullIndex i).1‖ ≤ ((⌈Rr⌉₊ + 2 : ℕ) : ℝ) := by
    rw [hi]
    have h1 := CircleCont.norm_dyadicRoundC_sub_le n w
    have h2 : (1 : ℝ) / 2 ^ n ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have h3 := norm_le_insert' (dyadicRoundC n w) w
    have h4 := Nat.le_ceil Rr
    push_cast
    nlinarith [norm_sub_rev (dyadicRoundC n w) w, norm_nonneg w]
  have := hC i k (by rw [hi]) hn
  have e : coordsFull x i = x (foldedCircle (dyadicRoundC n w) (radius k)) := by
    show x (foldedCircle (fullIndex i).1 (fullIndex i).2) = _
    rw [hi]
  rw [← e]; exact this

/-- **Log growth of the unzipped field**, from X1 (E6 on the full data) and the log growth at the
wedge. -/
theorem unzGrowthStmt_holds (hX1 : BaseFin.BaseFiniteStmt) : UnzGrowthStmt := by
  intro γ Ω _ P _ B Y hS hIn b hb
  have hE : MeasurableSet {d : E6.FullData | d.1.1 ∈ growthSet} :=
    measurableSet_growthSet.preimage (measurable_fst.comp measurable_fst)
  have hX0 : AEMeasurable (fun ω => cfgData (wedgeAConfig γ B Y ω).toPair) P :=
    aemeasurable_cfgData_wedgeConfig hS hIn
  have hX1' := aemeasurable_cfgData_zipLenDownA hX1 hS hb (B := B) (Y := Y)
  have h0 : ∀ᵐ ω ∂P, cfgData (wedgeAConfig γ B Y ω).toPair ∈
      {d : E6.FullData | d.1.1 ∈ growthSet} := by
    filter_upwards [circAvgLogGrowthStmt_holds γ P B Y hS hIn] with ω h
    exact coordsFull_mem_growthSet h
  have h' := (ae_map_iff hX0 hE).2 h0
  rw [← map_cfgData_zipLenDownA hX1 hS hb] at h'
  filter_upwards [(ae_map_iff hX1' hE).1 h'] with ω h
  exact growth_of_mem_growthSet h

end R18
end QuantumZipper

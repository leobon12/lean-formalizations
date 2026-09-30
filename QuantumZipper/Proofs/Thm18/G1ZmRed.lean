import QuantumZipper.Proofs.Thm18.G3Z2b2Inn
import QuantumZipper.Proofs.Thm18.G3ZcFormat

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-ZOOM (1): the wedge Palm-window limit from its fixed-path form

`G1WedgePalmLimStmt` (G3ZcFormat) is reduced to the same limit **for one deterministic good
path** `a` (`G1ZmPathStmt`: the path is fixed, only the independent `(γ − 2/γ)`-wedge is
random), given the a.s. regularity of the window points (`G1ZmFacRegStmt`, the premise of the
curve Fubini `g1zWedgePalmInt_fubini`; supplied by Z-REG).

Proof: curve Fubini (`g1zWedgePalmInt_fubini`, Sheffield arXiv:1012.4797 p. 70: the curve is
independent of the wedge), then dominated convergence over the path (`lintegral_map'` back to
`Ω`, bound `1`: the Palm window carries boundary mass at most `U`,
`measure_g1Win_le`). Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Zm

open G3Z2b2 D3Plus

/-- Continuity from below along a monotone family indexed by an order-connected parameter set. -/
theorem measure_le_of_monotone_cover (μ : Measure ℝ) {I T : Set ℝ} {K : ℝ → Set ℝ} {V : ℝ≥0∞}
    (hI : I.OrdConnected) (hK : Monotone K) (hT : ∀ t ∈ T, ∃ x ∈ I, t ∈ K x)
    (hle : ∀ x ∈ I, μ (K x) ≤ V) : μ T ≤ V := by
  by_cases hmax : ∃ m ∈ I, ∀ y ∈ I, y ≤ m
  · obtain ⟨m, hm, hmm⟩ := hmax
    calc μ T ≤ μ (K m) := measure_mono fun t ht => by
            obtain ⟨x, hx, htx⟩ := hT t ht
            exact hK (hmm x hx) htx
      _ ≤ V := hle m hm
  · push_neg at hmax
    have hsub : T ⊆ ⋃ q : {q : ℚ // (q : ℝ) ∈ I}, K (q : ℝ) := by
      intro t ht
      obtain ⟨x, hx, htx⟩ := hT t ht
      obtain ⟨y, hy, hxy⟩ := hmax x hx
      obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn hxy
      have hq : (q : ℝ) ∈ I := hI.out hx hy ⟨hxq.le, hqy.le⟩
      exact mem_iUnion.2 ⟨⟨q, hq⟩, hK hxq.le htx⟩
    have hdir : Directed (· ⊆ ·) fun q : {q : ℚ // (q : ℝ) ∈ I} => K (q : ℝ) := by
      intro q₁ q₂
      rcases le_total ((q₁ : ℚ) : ℝ) ((q₂ : ℚ) : ℝ) with h | h
      · exact ⟨q₂, hK h, le_rfl⟩
      · exact ⟨q₁, le_rfl, hK h⟩
    calc μ T ≤ μ (⋃ q : {q : ℚ // (q : ℝ) ∈ I}, K (q : ℝ)) := measure_mono hsub
      _ = ⨆ q : {q : ℚ // (q : ℝ) ∈ I}, μ (K (q : ℝ)) := hdir.measure_iUnion
      _ ≤ V := iSup_le fun q => hle _ q.2

/-- **The Palm window carries boundary mass at most `U`** (any measure on `ℝ`). -/
theorem measure_g1Win_le (μ : Measure ℝ) (left : Bool) (V : ℝ≥0∞) :
    μ {x | x ∈ g1SideHalf left ∧ μ (g1SideSeg left x) ≤ V} ≤ V := by
  cases left
  · refine measure_le_of_monotone_cover μ (I := {x | 0 < x ∧ μ (Icc 0 x) ≤ V})
      (K := fun x => Icc 0 x) ?_ (fun x y h => Icc_subset_Icc_right h) ?_ ?_
    · refine ⟨fun x hx y hy z hz => ⟨lt_of_lt_of_le hx.1 hz.1, ?_⟩⟩
      exact (measure_mono (Icc_subset_Icc_right hz.2)).trans hy.2
    · intro t ht
      simp only [g1SideHalf, g1SideSeg, mem_setOf_eq, Bool.false_eq_true, if_false,
        mem_Ioi] at ht
      exact ⟨t, ht, ⟨ht.1.le, le_rfl⟩⟩
    · exact fun x hx => hx.2
  · refine measure_le_of_monotone_cover μ (I := {y | 0 < y ∧ μ (Icc (-y) 0) ≤ V})
      (K := fun y => Icc (-y) 0) ?_ (fun x y h => Icc_subset_Icc_left (neg_le_neg h)) ?_ ?_
    · refine ⟨fun x hx y hy z hz => ⟨lt_of_lt_of_le hx.1 hz.1, ?_⟩⟩
      exact (measure_mono (Icc_subset_Icc_left (neg_le_neg hz.2))).trans hy.2
    · intro t ht
      simp only [g1SideHalf, g1SideSeg, mem_setOf_eq, if_true, mem_Iio] at ht
      refine ⟨-t, ⟨by linarith [ht.1], by simpa using ht.2⟩, ?_⟩
      simp only [neg_neg]
      exact ⟨le_rfl, ht.1.le⟩
    · exact fun x hx => hx.2

variable {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}

/-- The measurable Palm-window functional is at most `U`. -/
theorem g1PhiM_le {γ L : ℝ} {R : ℕ} {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞}
    (hΓ1 : ∀ y, Γ y ≤ 1) (left : Bool) (U : ℝ) (p : FieldSample × (ℝ≥0 → ℝ)) :
    g1PhiM γ L R Γ Ψ left U p ≤ ENNReal.ofReal U := by
  classical
  set μ := bdryM γ p.1
  set T := {x | x ∈ g1SideHalf left ∧ μ (g1SideSeg left x) ≤ ENNReal.ofReal U}
  calc g1PhiM γ L R Γ Ψ left U p ≤ ∫⁻ x, T.indicator 1 x ∂μ := by
        unfold g1PhiM
        refine lintegral_mono fun x => ?_
        unfold g1IntM
        split_ifs with h
        · rw [indicator_of_mem (show x ∈ T from h)]
          exact hΓ1 _
        · exact bot_le
    _ ≤ μ T := by
        refine (lintegral_indicator_le _ _).trans ?_
        simp
    _ ≤ ENNReal.ofReal U := measure_g1Win_le μ left _

end G1Zm
end Thm18Asm
end QuantumZipper

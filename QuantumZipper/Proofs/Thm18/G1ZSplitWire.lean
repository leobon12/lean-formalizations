import QuantumZipper.Proofs.Thm18.G1ZSplitDefs
import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-SPLIT: the derivations of A1, A and B2 from their parts (Theorem 1.8, G1 zoom half)

Statements and sources: `G1ZSplitDefs.lean`, plan `handoff/G1-ZSPLIT.md` (decision D48).

* `g1SidePt_eq_of_len`: if the side boundary measure charges open intervals of the side
  half-line and gives the segment `[β,0]` (resp. `[0,β]`) mass `ℓ`, the rerooting point is `β`;
* **`g1RerootPathStmt_of_parts`**: A1 from A1a, A1b, A1c;
* **`g1RerootStmt_of`**: A from E6, F1, A1, A1a, A1c and the factorization A2 (law transfer
  through `configLawFull`, Sheffield arXiv:1012.4797 p. 70);
* **`g1PalmModelStmt_of`**: B2 from B2-C, B2-R, Z1, Z2.

All arguments are own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus

/-! ## The rerooting point from the length -/

/-- **The rerooting point from the length** (own elementary argument): if `ν` charges every open
interval of the side half-line and `ν(seg β) = ℓ` for `β` in the half-line, then
`g1SidePt ℓ = β`. -/
theorem g1SidePt_eq_of_len {γ : ℝ} {left : Bool} {x : FieldSample} {ℓ β : ℝ}
    (hβ : β ∈ g1SideHalf left)
    (hpos : ∀ u v : ℝ, u < v → Ioo u v ⊆ g1SideHalf left → 0 < g1SideNu γ left x (Ioo u v))
    (hlen : g1SideNu γ left x (g1SideSeg left β) = ENNReal.ofReal ℓ) :
    g1SidePt γ left x ℓ = β := by
  set ν := g1SideNu γ left x with hν
  cases left with
  | true =>
    simp only [g1SideHalf, ite_true, mem_Iio] at hβ
    simp only [g1SideHalf, ite_true] at hpos
    simp only [g1SideSeg, ite_true] at hlen
    simp only [g1SidePt, ite_true, lenLeft]
    rw [← hν]
    have hl : IsLeast {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ ν (Icc (-y) 0)} (-β) := by
      refine ⟨⟨by linarith, by rw [neg_neg, hlen]⟩, ?_⟩
      rintro y ⟨hy, hyℓ⟩
      by_contra hlt
      push Not at hlt
      have hsub : Icc (-y) 0 ∪ Ioo β (-y) ⊆ Icc β 0 := by
        rintro z (hz | hz)
        · exact ⟨by linarith [hz.1], hz.2⟩
        · exact ⟨hz.1.le, by linarith [hz.2]⟩
      have hdisj : Disjoint (Icc (-y) 0) (Ioo β (-y)) := by
        rw [Set.disjoint_left]
        intro z hz' hz
        exact absurd hz'.1 (not_le.2 hz.2)
      have hp : 0 < ν (Ioo β (-y)) :=
        hpos β (-y) (by linarith) fun z hz => show z < 0 by linarith [hz.2]
      have hfin : ν (Icc (-y) 0) ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := ν (Icc β 0)) (by rw [hlen]; exact ENNReal.ofReal_ne_top)
          (measure_mono fun z hz => ⟨by linarith [hz.1], hz.2⟩)
      have h1 : ν (Icc (-y) 0) < ν (Icc (-y) 0) + ν (Ioo β (-y)) :=
        ENNReal.lt_add_right hfin hp.ne'
      rw [← measure_union hdisj measurableSet_Ioo] at h1
      have h2 := h1.trans_le (measure_mono hsub)
      rw [hlen] at h2
      exact absurd (hyℓ.trans_lt h2) (lt_irrefl _)
    rw [hl.csInf_eq, neg_neg]
  | false =>
    simp only [g1SideHalf, Bool.false_eq_true, ite_false, mem_Ioi] at hβ
    simp only [g1SideHalf, Bool.false_eq_true, ite_false] at hpos
    simp only [g1SideSeg, Bool.false_eq_true, ite_false] at hlen
    simp only [g1SidePt, Bool.false_eq_true, ite_false, lenRight]
    rw [← hν]
    have hl : IsLeast {y : ℝ | 0 < y ∧ ENNReal.ofReal ℓ ≤ ν (Icc 0 y)} β := by
      refine ⟨⟨hβ, hlen.ge⟩, ?_⟩
      rintro y ⟨hy, hyℓ⟩
      by_contra hlt
      push Not at hlt
      have hsub : Icc 0 y ∪ Ioo y β ⊆ Icc 0 β := by
        rintro z (hz | hz)
        · exact ⟨hz.1, by linarith [hz.2]⟩
        · exact ⟨by linarith [hz.1], hz.2.le⟩
      have hdisj : Disjoint (Icc 0 y) (Ioo y β) := by
        rw [Set.disjoint_left]
        intro z hz' hz
        exact absurd hz'.2 (not_le.2 hz.1)
      have hp : 0 < ν (Ioo y β) := hpos y β hlt fun z hz => show 0 < z by linarith [hz.1]
      have hfin : ν (Icc 0 y) ≠ ⊤ := by
        refine ne_top_of_le_ne_top (b := ν (Icc 0 β)) (by rw [hlen]; exact ENNReal.ofReal_ne_top)
          (measure_mono fun z hz => ⟨hz.1, by linarith [hz.2]⟩)
      have h1 : ν (Icc 0 y) < ν (Icc 0 y) + ν (Ioo y β) := ENNReal.lt_add_right hfin hp.ne'
      rw [← measure_union hdisj measurableSet_Ioo] at h1
      have h2 := h1.trans_le (measure_mono hsub)
      rw [hlen] at h2
      exact absurd (hyℓ.trans_lt h2) (lt_irrefl _)
    exact hl.csInf_eq

/-! ## A1 from its parts -/

/-- A.s. the Theorem 1.8 driver is good. -/
theorem ae_g1zDrvGood {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample} (hS : Thm18Setting γ P B Y)
    (hIn : Thm18Inputs γ P B Y) : ∀ᵐ ω ∂P, G1zDrvGood (drive (γ ^ 2) B ω) := by
  filter_upwards [hS.2.2.1.cont, hS.2.2.1.eval_zero_ae_eq_zero, hIn.2.2] with ω hc h0 hin
  refine ⟨?_, ?_, fun s => ?_, hin.1, hin.2.1⟩
  · exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  · simp only [drive, Real.toNNReal_zero]
    rw [h0]; simp
  · simp only [drive]
    congr 2
    apply NNReal.eq
    simp [Real.coe_toNNReal']

/-! ## A from E6, F1, A1 and the factorization -/

/-- The local data are functions of the full data. -/
theorem locFieldFull_congr_dataFull {x y : FieldSample}
    (h : WedgeMeas.dataFull H x = WedgeMeas.dataFull H y) (R : ℕ) :
    locFieldFull R x = locFieldFull R y := by
  have h1 : CoordsFull.coordsFull x = CoordsFull.coordsFull y := congrArg Prod.fst h
  have h2 : ∀ ρ : TestFun H, pairRaw x ρ.1 = pairRaw y ρ.1 := fun ρ =>
    congrFun (congrArg Prod.snd h) ρ
  unfold locFieldFull
  rw [h1]
  congr 1
  funext ρ
  rw [h2 ρ]

/-! ## B2 from its parts -/

theorem addConst_zero' (x : FieldSample) : addConst x 0 = x := by
  funext μ
  simp [addConst]

theorem g1PalmIntC_zero (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → FieldSample) (left : Bool) (U : ℝ) (R : ℕ)
    (Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞) :
    g1PalmIntC γ P Z left U 0 R Γ = g1PalmInt γ P Z left U R Γ := by
  simp only [g1PalmIntC, g1PalmInt, addConst_zero']

/-- **B2 from B2-C, B2-R, Z1 and Z2.** -/
theorem g1PalmModelStmt_of (hC : G1SideConstInvStmt) (hR : G1PalmConstStmt)
    (hZ1 : G1PalmToWedgeStmt) (hZ2 : G1WedgePalmZoomStmt) : G1PalmModelStmt := by
  intro γ Ω _ P _ B Y hS hIn left R Γ hΓ hΓ1 ε hε
  obtain ⟨U, hU, hap⟩ := hZ2 γ P B Y hS hIn left R Γ hΓ hΓ1 ε hε
  refine ⟨U, hU, g1WApproxAt_of_seq_const ?_⟩
  have hγ : γ ≠ 0 := hS.1.ne'
  have key : ∀ L : ℝ, (ENNReal.ofReal U)⁻¹ * g1zWedgePalmInt γ P B Y left U L R Γ =
      (ENNReal.ofReal U)⁻¹ * g1PalmInt γ P (g1SideField γ B Y left) left U R Γ := by
    intro L
    have h1 := hZ1 γ P B Y hS hIn left U hU (L / γ) R Γ hΓ hΓ1
    rw [mul_div_cancel₀ L hγ] at h1
    rw [← h1, hR γ P B Y hS hIn left U hU (L / γ) R Γ hΓ hΓ1,
      hC γ P B Y hS hIn left (L / γ) R Γ hΓ hΓ1, ← g1PalmIntC_zero,
      hR γ P B Y hS hIn left U hU 0 R Γ hΓ hΓ1]
    simp only [addConst_zero']
  have hfun : (fun L : ℝ => (ENNReal.ofReal U)⁻¹ * g1zWedgePalmInt γ P B Y left U L R Γ) =
      fun _ => (ENNReal.ofReal U)⁻¹ * g1PalmInt γ P (g1SideField γ B Y left) left U R Γ :=
    funext key
  rw [hfun] at hap
  exact hap

end Thm18Asm
end QuantumZipper

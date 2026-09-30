import QuantumZipper.Proofs.Thm18.G4Rezip2Base
import QuantumZipper.Proofs.Thm14.WeldingData

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: the unzipped welding identity from equal side lengths

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (the quantum
lengths of the two sides of every initial segment of `η` agree). This file reduces the unscaled
welding node `G4UnzipWeldHomStmt` (`G4Rezip2Hom.lean`) to two statements about the unzipped
field `x_τ` at the unzipping time `τ = τ_ℓ` (`V = vrev W τ`, whose reverse flow re-zips
`η[τ − r, τ]` in time `r`, and sends `[0₋(V,r), 0]` and `[0, 0₊(V,r)]` onto its two sides):

* `G4UnzipSideLenStmt`: `ν_{x_τ}[0₋(V,r), 0] = ν_{x_τ}[0, 0₊(V,r)]` for all `r ∈ (0,τ]`, the
  equality of the quantum lengths of the two sides of `η[τ − r, τ]` (Theorem 1.8, in the
  coordinates of `x_τ`; it follows from `LenEqStmt` at times `τ − r`, `τ` and the length
  cocycle on both sides, blueprint B5);
* `G4UnzipBdryPosRightStmt`: `ν_{x_τ}` charges every nonempty open interval of `[0,∞)` (the
  right counterpart of `UnzipBdryPosStmt`; `[0,O⁺_τ]` is the right side of `η[0,τ]`, and
  `(O⁺_τ,∞)` the image of `ν_Y` on `(0,∞)`).

The Loewner input is the arc structure of the reverse flow (project L-wc/L-0m,
`WeldingConsistency.exists_zeroMinus_eq`, `weldingHom_eq_of_le`, citing Lawler, *Conformally
Invariant Processes in the Plane*, §4.1) and the Carathéodory extension
(`CaraR.revMapCaratheodory`, Pommerenke, *Boundary Behaviour of Conformal Maps*, Thm 2.1), which
gives `weldingHom V r (0₋(V,r)) = 0₊(V,r)`. **Own elementary argument** (bookkeeping).
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. Deterministic lemmas -/

/-- `weldingHom W T 0 = 0`. -/
theorem weldingHom_zero_self (W : ℝ → ℝ) (T : ℝ) : weldingHom W T 0 = 0 :=
  IsLeast.csInf_eq ⟨⟨le_rfl, rfl⟩, fun _ hy => hy.1⟩

/-- `R_x(0) = 0`. -/
theorem weldHomR_zero_self (γ : ℝ) (x : FieldSample) : weldHomR γ x 0 = 0 :=
  IsLeast.csInf_eq ⟨⟨le_rfl, le_rfl⟩, fun _ hy => hy.1⟩

/-- **`R_x(s) = z` at an exact length match**: if `ν[s,0] = ν[0,z]` and `ν` charges every
`(v,z)`, `0 ≤ v < z`, then `weldHomR γ x s = z`. -/
theorem weldHomR_eq_of_exact {γ : ℝ} {x : FieldSample} {s z : ℝ} (hz : 0 ≤ z)
    (hex : qBoundaryMeasure γ x (Icc s 0) = qBoundaryMeasure γ x (Icc 0 z))
    (hpos : ∀ v : ℝ, 0 ≤ v → v < z → 0 < qBoundaryMeasure γ x (Ioo v z)) :
    weldHomR γ x s = z := by
  refine IsLeast.csInf_eq ⟨⟨hz, hex.le⟩, ?_⟩
  rintro r ⟨hr0, hr⟩
  by_contra hlt
  push Not at hlt
  have hdisj : Disjoint (Icc 0 r) (Ioo r z) :=
    Set.disjoint_left.2 fun u hu hu' => (lt_irrefl u) (hu.2.trans_lt hu'.1)
  have hsub : Icc 0 r ∪ Ioo r z ⊆ Icc 0 z := by
    rintro u (hu | hu)
    · exact ⟨hu.1, hu.2.trans hlt.le⟩
    · exact ⟨hr0.trans hu.1.le, hu.2.le⟩
  have h1 := measure_mono (μ := qBoundaryMeasure γ x) hsub
  rw [measure_union hdisj measurableSet_Ioo, ← hex] at h1
  have hfin : qBoundaryMeasure γ x (Icc 0 r) ≠ ⊤ := (qBoundaryMeasure_Icc_lt_top _ _ _ _).ne
  have h3 : qBoundaryMeasure γ x (Icc 0 r) <
      qBoundaryMeasure γ x (Icc 0 r) + qBoundaryMeasure γ x (Ioo r z) :=
    ENNReal.lt_add_right hfin (hpos r hr0 hlt).ne'
  exact absurd (h3.trans_le (h1.trans hr)) (lt_irrefl _)

/-- **Deterministic reduction**: the welding homeomorphism of a driver `V` with simple hull at
time `τ` is `R_x` on `[0₋(V,τ), 0]` as soon as the two sides of each sub-arc have equal
`ν_x`-length and `ν_x` charges the open intervals of `[0,∞)`. -/
theorem weldingHom_eq_weldHomR_of {γ : ℝ} {V : ℝ → ℝ} (hVc : Continuous V) (hV0 : V 0 = 0)
    {τ : ℝ} (hτ : 0 < τ) (hK : IsSimpleCurveHull (revHull V τ)) {x : FieldSample}
    (hL : ∀ r ∈ Ioc (0 : ℝ) τ, qBoundaryMeasure γ x (Icc (zeroMinus V r) 0) =
      qBoundaryMeasure γ x (Icc 0 (zeroPlus V r)))
    (hP : ∀ v w : ℝ, 0 ≤ v → v < w → 0 < qBoundaryMeasure γ x (Ioo v w)) :
    ∀ u ∈ Icc (zeroMinus V τ) 0, weldingHom V τ u = weldHomR γ x u := by
  intro u hu
  rcases eq_or_lt_of_le hu.2 with h0 | hu0
  · rw [h0, weldingHom_zero_self, weldHomR_zero_self]
  obtain ⟨r, hr, hzr⟩ := WeldingConsistency.exists_zeroMinus_eq CaraR.revMapCaratheodory
    CoreArc.loewnerSubhullsOfArc hVc hV0 hτ hK hu.1 hu0
  have hKr : IsSimpleCurveHull (revHull V r) :=
    WeldingConsistency.isSimpleCurveHull_revHull_of_le CoreArc.loewnerSubhullsOfArc hVc hV0 hτ hK
      hr.1 hr.2
  obtain ⟨Fr, hFr⟩ := CaraR.revMapCaratheodory V hVc hV0 r hr.1 hKr
  rw [WeldingConsistency.weldingHom_eq_of_le CaraR.revMapCaratheodory
    CoreArc.loewnerSubhullsOfArc hVc hV0 hτ hK hr.1 hr.2 ⟨hzr.le, hu0.le⟩, ← hzr,
    hFr.2.2.2.2.1]
  exact (weldHomR_eq_of_exact (Real.sInf_nonneg fun _ hy => hy.1.le) (hL r hr)
    fun v hv hvz => hP v _ hv hvz).symm

/-! ## 2. The a.s. nodes and the reduction -/

end Thm18Asm
end QuantumZipper

import QuantumZipper.Proofs.Zipper.BaseFin2Unit
import QuantumZipper.Proofs.Zipper.TipXE0Hcap
import QuantumZipper.Proofs.RS.TransienceCanon
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# X1-SLE: the base-return tail `SLEBaseTailStmt` from the Field–Lawler escape estimate

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*,
Electron. J. Probab. 20 (2015), no. 10, 1–14 (arXiv:1407.3314, `literature/1407.3314.pdf`),
**Theorem 1.1** (p. 3; proved as Proposition 3.4, p. 8): for `0 < κ ≤ 4` there is `c < ∞` such
that for chordal `SLE_κ` in `ℍ` from `0` to `∞`, `T = inf{t : |γ(t)| = 1}` and `r > 0`,
`P{γ[T, ∞) ∩ C_r ≠ ∅ | γ_T} ≤ c e^{−r(4a−1)}`, `a = 2/κ`, `C_r = {|z| = e^{−r}}`.

`FieldLawlerReturnStmt` is its unconditional form after Brownian scaling by `R`
(`4a − 1 = 8/κ − 1`, `ε = R e^{−r}`): the probability that the trace, after having reached
`|·| ≥ R`, comes back into `B(0, ε)` is at most `c (ε/R)^{8/κ−1}` (for `ε < R` the event is
contained in `{γ[T_R, ∞) ∩ C_ε ≠ ∅}` by continuity; for `ε ≥ R` the bound is `≥ 1` once
`c ≥ 1`). This is exactly the "return to the root" estimate that Lawler 2005 Prop. 6.12 (p. 128),
Rohde–Schramm Thm 7.1 and Kemppainen Prop. 5.5 give only qualitatively.

**Proved here:** `sleBaseTail_of_fieldLawler : FieldLawlerReturnStmt → SLEBaseTailStmt`.
The curve leaves `B̄(0, 1/5)` before time `1/32` (half-plane capacity,
`TipXE.two_mul_le_sq_of_fwdHull_subset`, `(1/5)² < 2 · 1/32`), so a visit of `B(0, ε)` during
`[1/16, 4]` is a return after reaching `|·| ≥ 1/5`. Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace BaseFin2

open WedgeUnzip

/-- **(Literature node) Field–Lawler, EJP 20 (2015), Theorem 1.1, unconditional scaled form.**
After reaching `|·| ≥ R`, the chordal `SLE_κ` trace (`κ < 4`) returns into `B(0, ε)` with
probability at most `c (ε/R)^{8/κ − 1}`. -/
def FieldLawlerReturnStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∃ c : ℝ, 0 ≤ c ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P → ∀ R ε : ℝ, 0 < R → 0 < ε →
      P {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ R ≤ ‖sleTrace κ B ω s‖ ∧ ‖sleTrace κ B ω t‖ < ε} ≤
        ENNReal.ofReal (c * (ε / R) ^ (8 / κ - 1))

/-- Pathwise step: for a continuous driver with `W 0 = 0` whose hulls are the trace images,
a visit of `B(0, ε)` during `[1/16, 4]` is a return after reaching `|·| ≥ 1/5`. -/
theorem bf2sle_return_of_baseDist {W : ℝ → ℝ} (hWc : Continuous W) (hW0 : W 0 = 0)
    (hhull : ∀ t : ℝ, 0 ≤ t → fwdHull W t = trace W '' Ioc 0 t) {r ε : ℝ}
    (hr : r ∈ Icc (1 / 16 : ℝ) 4) (hε : ‖trace W r‖ < ε) :
    ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ (1 / 5 : ℝ) ≤ ‖trace W s‖ ∧ ‖trace W t‖ < ε := by
  by_contra hcon
  have hK : fwdHull W (1 / 32) ⊆ closedBall (0 : ℂ) (1 / 5) := by
    rw [hhull _ (by norm_num)]
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    by_contra hgt
    push Not at hgt
    exact hcon ⟨s, r, hs.1.le, by linarith [hs.2, hr.1], hgt.le, hε⟩
  have := TipXE.two_mul_le_sq_of_fwdHull_subset hWc hW0 (by norm_num) (by norm_num) hK
  norm_num at this

/-- **`SLEBaseTailStmt` from the Field–Lawler escape estimate.** -/
theorem sleBaseTail_of_fieldLawler (hFL : FieldLawlerReturnStmt) : SLEBaseTailStmt := by
  intro κ hκ hκ4
  obtain ⟨c, hc, hFLκ⟩ := hFL κ hκ hκ4
  set α : ℝ := 8 / κ - 1 with hα
  have hα0 : 0 < α := by
    rw [hα, sub_pos, lt_div_iff₀ hκ]; linarith
  refine ⟨c * 5 ^ α, α, by positivity, hα0, ?_⟩
  intro Ω _ P _ B hB ε hε
  obtain ⟨B'', -, hB''c, hB''0, hB'', hBeq⟩ := RS.exists_good_version0 hB
  have hsub : {ω | baseDist κ B ω < ENNReal.ofReal ε} ≤ᵐ[P]
      {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ (1 / 5 : ℝ) ≤ ‖sleTrace κ B ω s‖ ∧
        ‖sleTrace κ B ω t‖ < ε} := by
    filter_upwards [hBeq, RS.rohdeSchrammSimple κ hκ hκ4.le P B'' hB''] with ω hω hrs
    intro hlt
    have hdr : drive κ B'' ω = drive κ B ω := by
      funext t; simp only [drive, hω]
    have htr : sleTrace κ B ω = trace (drive κ B'' ω) := by
      rw [hdr]; rfl
    simp only [baseDist] at hlt
    obtain ⟨r, hr⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hrI, hr'⟩ := iInf_lt_iff.1 hr
    have hnr : ‖sleTrace κ B ω r‖ < ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).1 hr'
    have hWc : Continuous (drive κ B'' ω) :=
      continuous_const.mul ((hB''c ω).comp continuous_real_toNNReal)
    have hW0 : drive κ B'' ω 0 = 0 := by simp [drive, hB''0 ω]
    have hhull : ∀ t : ℝ, 0 ≤ t → fwdHull (drive κ B'' ω) t =
        trace (drive κ B'' ω) '' Ioc 0 t := fun t ht => hrs.2 t ht
    rw [htr] at hnr ⊢
    exact bf2sle_return_of_baseDist hWc hW0 hhull hrI hnr
  refine (measure_mono_ae hsub).trans ((hFLκ P B hB (1 / 5) ε (by norm_num) hε).trans ?_)
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  have h5 : ε / (1 / 5 : ℝ) = 5 * ε := by field_simp
  rw [h5, Real.mul_rpow (by norm_num) hε.le]
  ring

end BaseFin2
end QuantumZipper

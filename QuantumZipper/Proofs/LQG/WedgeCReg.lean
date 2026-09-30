import QuantumZipper.Proofs.Zipper.F1B4dPath

/-!
# WEDGE-CREG (2): the lateral part commutes with the reflection after regularization

`F1.WedgeLatReflRegStmt γ α` (open input (i) of B4(d), `F1B4dPath`): for a free field `X` and an
independent `α`-wedge radial process `A`, almost surely

  `avgReg (wedgeField (lateralPart (reflectH X)) A Q) = avgReg (reflectH (wedgeField (lateralPart X) A Q))`.

Route (own elementary argument; the mathematical content is Sheffield, arXiv:1012.4797, §1.6:
the radial part `h_{|·|}(0)` of the free field is reflection invariant and the radial profile
`Q(−log|z|) + A_{−log|z|}` is a function of `|z|`).

* `avgReg` only reads raw values at dyadic lattice circles `fc(d, 2^{-k})`, so it suffices to
  compare raw values there (`raw_wedge_reflect`);
* the right side is `evalReg W (fc(−d̄, 2^{-k}))` (`fc_map_negConj`), which equals the raw value
  `W (fc(−d̄, 2^{-k}))` because `W` is regular and `−d̄` is again a lattice point
  (`F1.raw_fc_lpt_eq_evalReg`); regularity of `W` comes from `LogSingGood.wedgeRefGoodAS_holds`;
* for a sample that is `GoodRad` (regular, with raw dyadic semicircle values about `0` given by
  the witness; a.s. true for the free field by `WedgeTK.exists_isRegVersion`), the semicircle
  averages about `0` of `reflectH x` and `x` agree (`radAvgReg_reflectH`), and radial integrands
  are invariant under `u ↦ −ū`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace WedgeCReg

variable {x : FieldSample} {F : ℂ × ℝ → ℝ}

/-- The semicircle averages about `0` of `reflectH x` and of `x` agree, for a `GoodRad` sample. -/
theorem radAvgReg_reflectH (hx : WedgeTK.GoodRad x F) {r : ℝ} (hr : 0 ≤ r) :
    radAvgReg (RegClosure.reflectH x) r = radAvgReg x r := by
  have hs : ∀ n : ℕ, dyadicRound n r + radius n = WedgeTK.dyRad n (⌊(2 : ℝ) ^ n * r⌋.toNat) := by
    intro n
    rw [CoordsFull.radAvg_radius_eq_div, WedgeTK.dyRad]
    have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
    have : ((⌊(2 : ℝ) ^ n * r⌋.toNat : ℕ) : ℝ) = (⌊(2 : ℝ) ^ n * r⌋ : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg h0
    rw [this]; push_cast; ring
  unfold radAvgReg
  congr 1
  funext n
  show evalReg x ((foldedCircle 0 _).map fun z => -conj z) = _
  rw [F1.fc_map_negConj, hs n]
  simp only [map_zero, neg_zero]
  rw [hx.1.evalReg_fc_of_mem GaussTK.zero_mem_Hbar (WedgeTK.dyRad_pos _ _), hx.2]

theorem norm_neg_conj (u : ℂ) : ‖-conj u‖ = ‖u‖ := by rw [norm_neg, Complex.norm_conj]

/-- Raw values of the two wedge fields at a folded circle, for a `GoodRad` sample `x`. -/
theorem raw_wedge_reflect (hx : WedgeTK.GoodRad x F) (a : ℝ → ℝ) (Q : ℝ) (d : ℂ) {s : ℝ}
    (hs : 0 < s) :
    wedgeField (lateralPart (RegClosure.reflectH x)) a Q (foldedCircle d s) =
      wedgeField (lateralPart x) a Q (foldedCircle (-conj d) s) := by
  unfold wedgeField lateralPart
  rw [hx.1.reflectH'.evalReg_fc d hs, hx.1.evalReg_fc _ hs, F1.B4d.foldH_neg_conj]
  simp only [neg_neg, Complex.conj_conj]
  rw [← F1.integral_fc_negConj (fun v => radAvgReg x ‖v‖),
    ← F1.integral_fc_negConj (fun v => Q * -Real.log ‖v‖ + a (-Real.log ‖v‖))]
  simp only [norm_neg_conj]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  exact radAvgReg_reflectH hx (norm_nonneg u)

/-- **Deterministic core.** For a `GoodRad` sample `x` whose wedge field is regular, the wedge
field of the reflection has the regularized circle averages of the reflected wedge field. -/
theorem regEq_wedge_reflect (hx : WedgeTK.GoodRad x F) (a : ℝ → ℝ) (Q : ℝ) {FW : ℂ × ℝ → ℝ}
    (hW : IsRegularWith (wedgeField (lateralPart x) a Q) FW) :
    RegEq (wedgeField (lateralPart (RegClosure.reflectH x)) a Q)
      (RegClosure.reflectH (wedgeField (lateralPart x) a Q)) := by
  intro k z
  unfold avgReg
  congr 1
  funext n
  rw [CircleCont.dyadicRoundC_eq_lpt]
  show _ = evalReg _ ((foldedCircle _ _).map fun z => -conj z)
  rw [F1.fc_map_negConj, raw_wedge_reflect hx a Q _ (radius_pos k)]
  have e : -conj (CircleCont.lpt n ⌊(2 : ℝ) ^ n * z.re⌋ ⌊(2 : ℝ) ^ n * z.im⌋) =
      CircleCont.lpt n (-⌊(2 : ℝ) ^ n * z.re⌋) ⌊(2 : ℝ) ^ n * z.im⌋ := by
    apply Complex.ext <;> simp [CircleCont.lpt, neg_div]
  rw [e]
  exact F1.raw_fc_lpt_eq_evalReg hW n _ _ k

/-- **WEDGE-CREG (2): `F1.WedgeLatReflRegStmt` holds** for `γ ∈ (0,2)` and `α < Q`. -/
theorem wedgeLatReflRegStmt_holds {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    F1.WedgeLatReflRegStmt γ α := by
  intro Ω' _ P' X A hP hX hA hI
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hG.ae_good, LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP hX hA hI]
    with ω h1 h2
  obtain ⟨FW, hFW⟩ := h2.1
  funext k z
  exact regEq_wedge_reflect h1 _ _ hFW k z

end WedgeCReg
end QuantumZipper

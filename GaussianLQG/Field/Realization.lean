import GaussianLQG.Field.Realization.Pairing

/-!
# The coordinate realization of the normalized whole-plane GFF (blueprint Proposition 1.9)

Given a Hilbert basis `b` of the white-noise space `L²(ℝ × ℂ)` made of nice vectors, the GFF
frame `e_j = frameFunN (b j)` (blueprint Appendix B) is realized on the coordinate space
`(ℝ^ℕ, stdP)`:

* `h₀ = Realization.field0 b`: the coordinate series `∑_k ω_k F_k` of the antiderivative field
  (`F_k(x) = ⟪rectL2 x, b_k⟫`) converges locally uniformly along a subsequence, almost surely
  (`Realization/Uniform.lean`); its mixed derivative `∂_re ∂_im` is a whole-plane GFF, and
  subtracting the circle average `h̃_1(0)` normalizes it (`Realization/Field.lean`);
* `ΩW = Realization.goodW b`: the convergence set intersected with the existence set of
  `h̃_1(0)`, which is measurable, of full measure and invariant under finitely supported shifts;
  on it, coordinate shifts are Cameron–Martin shifts by `f_v = ∑_j v_j e_j`
  (`Realization.field0_shift`);
* pairing compatibility with every regular measure (`Realization/Pairing.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace GaussianLQG

/-- **Coordinate realization of the normalized whole-plane GFF** (blueprint
Proposition `prop:realization`, with the frame of Appendix B). -/
theorem exists_realization (b : HilbertBasis ℕ ℝ WNSpace) (hb : ∀ j, IsNiceWN (b j))
    (hcont : ∀ j, Continuous (frameFunN (b j))) (hframe : IsGFFFrame (fun j => frameFunN (b j))) :
    ∃ (h₀ : Coord → LQGMetric.DistC) (ΩW : Set Coord),
      Measurable h₀ ∧ LQGMetric.IsNormalizedWPGFF h₀ stdP ∧ MeasurableSet ΩW ∧ stdP ΩWᶜ = 0 ∧
      (∀ ω ∈ ΩW, ∀ v, shiftBy ω v ∈ ΩW) ∧
      (∀ ω ∈ ΩW, ∀ v, h₀ (shiftBy ω v) =
        LQGMetric.addFun (h₀ ω) (frameFunC (fun j => frameFunN (b j)) hcont v)) ∧
      ∀ μ, IsRegular μ → ∀ᵐ ω ∂stdP,
        Filter.Tendsto (fun n => ∑ j ∈ Finset.range n, ω j * ∫ z, frameFunN (b j) z ∂μ)
          Filter.atTop (nhds (measPairing (h₀ ω) μ)) :=
  ⟨Realization.field0 b, Realization.goodW b, Realization.measurable_field0 b,
    Realization.isNormalizedWPGFF_field0 b, Realization.measurableSet_goodW b,
    ae_iff.mp (Realization.ae_mem_goodW b),
    fun _ hω v => Realization.shiftBy_mem_goodW b hb hω v,
    fun _ hω v => Realization.field0_shift b hb hcont hω v,
    fun _ hμ => Realization.ae_tendsto_measPairing b hb hframe hμ⟩

end GaussianLQG

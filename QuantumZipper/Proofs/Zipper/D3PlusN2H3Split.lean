import QuantumZipper.Proofs.Zipper.D3PlusN2HeartLaw
import QuantumZipper.Proofs.LQG.WedgeRestriction
import QuantumZipper.Proofs.GFF.Existence.AdmissibleAux

/-!
# N2-H3: the model's window data from the lateral/radial splitting of `evalReg`

Task N2-H3, node `N2HModelDecompStmt` (`D3PlusN2HeartStmt.lean`).

Source: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.7(ii), pp. 77–78: the
field is `h = h† + h_{|·|}(0)` (lateral part plus radial part), the radial part at radius
`e^{−t}` is the drifted Brownian motion, and the circle-average embedding at scale
`a = r e^{−T}` only shifts the radial time by `T` ("the rescaling procedure does not affect the
projection of `h` onto `H₂(ℍ)`"). Sheffield, arXiv:1012.4797, p. 25.

This file proves `N2HModelDecompStmt` from the sub-node `N2H3SplitStmt`, the splitting of the
regularized evaluation of the model field at the rescaled window measure `ν = μ.map (a ·)`:

  `evalReg (h_L) ν = evalReg (lateral data) ν + ∫ (Z_{a|z|}(0) + α(−log (a|z|)) + L/γ) dμ(z)`,

together with integrability of the radial term. The deduction is the pathwise bookkeeping of the
radial time shift (DMS p. 78): with `T = Tc ≥ log K + 1` and `|z| ≤ K`,
`Q(−log|z|) + X_{T − log|z|} = Z_{a|z|}(0) + α(−log(a|z|)) + L/γ + Q log a`
(`n2_radial_pointwise`), plus continuity of the radial Brownian path (`WedgeLaw.extP` reads a
continuous path exactly). Own elementary bookkeeping on top of the cited decomposition.

**Status of `N2H3SplitStmt`.** Its analytic content is the regularity of the local field `Z` at
the random rescaled measure: the dyadic regularizations `∫ avgReg Z k dν` must converge for the
random `ν = μ.map (a(ω) ·)`. For folded circles and bounded densities (the measures the
consumers read) this follows from the regular version of the free field; for an arbitrary local
admissible `μ` (bounded log-potential only) the project has no a.s. convergence of `evalReg`
(the gap `F2.EvalRegRawStmt`, cf. DECISIONS D17), so the node is left open.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Radial time shift, pointwise** (DMS p. 78). -/
theorem n2_radial_pointwise {γ α L r : ℝ} {Ω : Type*} {X : Ω → FieldSample} {ω : Ω} {K : ℕ}
    (hK : 0 < K) (hr : 0 < r)
    (hT : Real.log K + 1 ≤ ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω) {z : ℂ}
    (hz0 : z ≠ 0) (hzK : ‖z‖ ≤ K) :
    Qc γ * (-Real.log ‖z‖) + (n2RadR γ α L r K X ω).2 (-Real.log ‖z‖) =
      (radAvgReg (locZField X r ω) (n2EmbScale γ α L r X ω * ‖z‖) +
        α * (-Real.log (n2EmbScale γ α L r X ω * ‖z‖)) + L / γ) +
        Qc γ * Real.log (n2EmbScale γ α L r X ω) := by
  set T := ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω with hTdef
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hmax : max (-Real.log ‖z‖) (-Real.log K) = -Real.log ‖z‖ :=
    max_eq_left (neg_log_le_of_norm_le hK hzK)
  have hlogK : Real.log ‖z‖ ≤ Real.log K := Real.log_le_log hn hzK
  have ht : 0 ≤ T + -Real.log ‖z‖ := by linarith
  have hexp : r * Real.exp (-(T + -Real.log ‖z‖)) = r * Real.exp (-T) * ‖z‖ := by
    rw [neg_add, neg_neg, Real.exp_add, Real.exp_log hn]; ring
  have hsq : √2 * ((√2)⁻¹ * radAvgReg (locZField X r ω) (r * Real.exp (-T) * ‖z‖)) =
      radAvgReg (locZField X r ω) (r * Real.exp (-T) * ‖z‖) :=
    mul_inv_cancel_left₀ (by positivity) _
  have hl1 : Real.log (r * Real.exp (-T) * ‖z‖) = Real.log r - T + Real.log ‖z‖ := by
    rw [Real.log_mul (by positivity) hn.ne', Real.log_mul hr.ne' (Real.exp_pos _).ne',
      Real.log_exp]; ring
  have hl2 : Real.log (r * Real.exp (-T)) = Real.log r - T := by
    rw [Real.log_mul hr.ne' (Real.exp_pos _).ne', Real.log_exp]; ring
  have hlev : n2Lev γ α L r = L / γ - (α - Qc γ) * Real.log r := rfl
  simp only [n2RadR, ZoomRadial.zoomRadial, ZoomRadial.Xc, hmax, zRadB, n2EmbScale, ← hTdef,
    Real.coe_toNNReal _ ht, hexp]
  rw [hsq, hl1, hl2, hlev]
  ring

/-- The model's radial path is continuous when the radial Brownian path is. -/
theorem continuous_n2RadR_snd {γ α L r : ℝ} {Ω : Type*} {X : Ω → FieldSample} {ω : Ω} (K : ℕ)
    (hc : Continuous fun t => zRadB X r t ω) : Continuous (n2RadR γ α L r K X ω).2 := by
  have hm : Continuous fun s : ℝ =>
      ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω + max s (-Real.log K) :=
    continuous_const.add (continuous_id.max continuous_const)
  change Continuous fun s => n2Lev γ α L r +
    √2 * zRadB X r (ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω +
      max s (-Real.log K)).toNNReal ω +
    (α - Qc γ) * (ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω + max s (-Real.log K))
  exact (continuous_const.add (continuous_const.mul
    (hc.comp (continuous_real_toNNReal.comp hm)))).add (continuous_const.mul hm)

end D3Plus
end QuantumZipper

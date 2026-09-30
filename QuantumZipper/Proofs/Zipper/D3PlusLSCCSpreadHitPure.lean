import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpreadMeas
import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpread

/-!
# D3⁺(ii) spread, part 3: the hitting-time input in pure Brownian-motion form

Task LSCC-SPREAD. `LSCCSpreadHitStmt` (`D3PlusLSCCSpread.lean`) depends on the free field `X` only
through the statement that the radial process `zRadB X r` is a standard Brownian motion. This file
records that dependence exactly: the input `HitLevSpreadStmt` is the same total-variation
statement for an *arbitrary* Brownian motion `b` and an arbitrary level `λ`, with no reference to
the Gaussian free field,

* `HitLevSpreadStmt`: for a Brownian motion `b` and `α < Q`, the law of the first hitting time
  `Tc α Q λ b` of `0` by `Xc α Q λ b` (`ZoomRadial.Tc`) is insensitive to a bounded shift of the
  level: `d_TV (law (Tc α Q λ b), law (Tc α Q (λ + c) b)) → 0` as `λ → ∞`;

and `lsccSpreadHit_of_pure : HitLevSpreadStmt → LSCCSpreadHitStmt` is proved here: instantiate
with `b = zRadB X r` (`isBrownianReal_zRadB`) and reparametrise the level by
`λ = n2Lev γ α L r = L/γ − (α − Q) log r`, which tends to `∞` (`tendsto_n2Lev`) and shifts by
`c / γ` (`n2Lev_shift`).

`lscConstGen_locFieldFull_of_pure` is the capstone: the constant part of rich D3⁺(ii) follows from
asymptotic independence, this pure hitting-time spread input, the pair-form independence of the
hitting time and the remainder, the stationarity of the remainder, and D3⁺(i)'s model node.

**The hitting-time spread `HitLevSpreadStmt` for drifted Brownian motion is not proved** in this
repository: its standard proof uses the explicit inverse Gaussian density of the hitting time
(equivalently the joint law of a Brownian motion and its running maximum, via the reflection
principle), and mathlib at this pin has no hitting-time law for Brownian motion (only
`Probability/BrownianMotion/Basic.lean` and `GaussianProjectiveFamily.lean`). It is recorded here
as an exact input, following Duplantier–Miller–Sheffield arXiv:1409.7055, Prop. 4.7 (p. 78) and
Sheffield arXiv:1012.4797, proof of Prop. 1.6 (p. 25).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **The hitting-time spread of a drifted Brownian motion** (pure form, no Gaussian free
field): a bounded shift of a large level changes the law of the hitting time by `o(1)` in total
variation. -/
def HitLevSpreadStmt : Prop :=
  ∀ (α Q : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (b : ℝ≥0 → Ω → ℝ), IsBrownianReal b P → α < Q → ∀ c : ℝ,
    Tendsto (fun L => TV.tvDist
      (P.map fun ω => ZoomRadial.Tc α Q L b ω)
      (P.map fun ω => ZoomRadial.Tc α Q (L + c) b ω)) atTop (𝓝 0)

/-- **The model form of the hitting-time spread follows from the pure form**: `zRadB X r` is a
Brownian motion and the embedding level `n2Lev γ α L r` is an increasing reparametrisation that
shifts by `c / γ`. -/
theorem lsccSpreadHit_of_pure (h : HitLevSpreadStmt) : LSCCSpreadHitStmt := by
  intro γ α r Ω _ P _ X c hγ hγ2 hα hr hX
  have h1 := (h α (Qc γ) P (zRadB X r) (isBrownianReal_zRadB hX hr) hα (c / γ)).comp
    (tendsto_n2Lev hγ α r)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h1
    (fun _ => bot_le) fun L => ?_
  refine le_of_eq ?_
  rw [n2Lev_shift γ α r L c]
  simp only [Function.comp_apply]

end D3Plus
end QuantumZipper

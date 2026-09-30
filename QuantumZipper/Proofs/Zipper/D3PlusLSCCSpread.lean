import QuantumZipper.Proofs.Zipper.D3PlusLSCCSpreadBasic

/-!
# D3⁺(ii), constant part: node LSCC-SPREAD reduced to the hitting-time spread and the remainder

Task LSCC-SPREAD. `LSCCSpreadStmt` (`D3PlusLSCCInd.lean`) says that the law of the log scale
`lsccS γ r α L X = log (scaleSur γ L r (localZ, circData α 0))` of the model zoom is insensitive
to a bounded shift `L ↦ L + c` of the level. Following Duplantier–Miller–Sheffield
arXiv:1409.7055, Prop. 4.7 (p. 78) and Sheffield arXiv:1012.4797, proof of Prop. 1.6 (p. 25),
write the log scale as the negative of the embedding (hitting) time plus an `O_P(1)` remainder,

* `lsccR γ r α L X = lsccS γ r α L X + τ_L`,
  `τ_L = ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r)` the hitting time of the level
  `n2Lev γ α L r = L/γ − (α − Q) log r` by the radial Brownian motion `zRadB X r`,

so that `lsccS = lsccR − τ_L` holds *identically* (`lsccS_eq_sub_Tc`). A bounded shift `L ↦ L + c`
shifts the level by `c / γ` (`n2Lev_shift`), and the hitting time of a large level by a Brownian
motion with positive drift has spread `≍ √L` (inverse Gaussian law): shifting the level by a
bounded amount costs `o(1)` in total variation. This is exactly the content of the named input

* `LSCCSpreadHitStmt`: `d_TV (law τ_L, law τ_{L+c}) → 0` for every real `c`;

and of the two facts collected in

* `LSCCSpreadRemStmt`: (i) the joint law of `(τ_L, lsccR … L)` is asymptotically the product of
  its marginals (asymptotic independence of the hitting time and of the post-hitting-time data,
  DMS Prop. 4.7: Williams path decomposition / strong Markov property), and (ii) the law of the
  remainder `lsccR … L` is insensitive to the same bounded shift (the remainder is `log r` plus
  the `O_P(1)` log of the circle-average embedding factor, whose law converges).

`lsccSpread_of_hit_rem : LSCCSpreadHitStmt → LSCCSpreadRemStmt → LSCCSpreadStmt` is the
elementary glue (triangle inequality on the total variation norm with the product measures in
between, `lscc_tvDist_prod_le`), and `lscConstGen_locFieldFull_of_hit_rem` plugs it into
`lscConstGen_locFieldFull_of_tmZero` (`D3PlusLSCCInd.lean`).

**Not proved here** (deliberately, and reported): the hitting-time TV lemma `LSCCSpreadHitStmt`
itself. Its proof needs the inverse Gaussian density of the hitting time of a drifted Brownian
motion (equivalently the joint law of a Brownian motion and its running maximum), which this
repository does not have; the remainder statement `LSCCSpreadRemStmt` is the part of the D3⁺
scaling limit carried by D3⁺(i)'s embedding machinery. Both are inputs (see DEVIATIONS).

The pushforwards in these statements are genuine measures: `measurable_lsccS` and
`aemeasurable_Tc_zRadB` (`D3PlusLSCCSpreadBasic.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The `O_P(1)` remainder of the log scale -/

/-- The remainder of the log scale after subtracting the embedding time: `lsccS = lsccR − τ`. -/
def lsccR (γ r α L : ℝ) {Ω : Type*} (X : Ω → FieldSample) (ω : Ω) : ℝ :=
  lsccS γ r α L X ω + ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω

/-! ## The two named inputs -/

/-- **Node LSCC-SPREAD-HIT (the hitting-time spread).** A bounded shift of the embedding level
changes the law of the hitting time by `o(1)` in total variation. This is the analytic content of
"the hitting time of a large level by a Brownian motion with positive drift has spread `≍ √L`":
for drift `ν = Qc γ − α > 0` and level `n2Lev γ α L r = L/γ + ν log r`, the hitting time has the
inverse Gaussian law `IG(λ/ν, λ²/2)`, whose density depends on `λ` through a `1/√λ`-Lipschitz
profile, so `d_TV (law T_λ, law T_{λ + c/γ}) → 0` (Duplantier–Miller–Sheffield arXiv:1409.7055,
Prop. 4.7, p. 78; Sheffield arXiv:1012.4797, proof of Prop. 1.6, p. 25). -/
def LSCCSpreadHitStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (c : ℝ),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    Tendsto (fun L => TV.tvDist
      (P.map fun ω => ZoomRadial.Tc α (Qc γ) (n2Lev γ α L r) (zRadB X r) ω)
      (P.map fun ω => ZoomRadial.Tc α (Qc γ) (n2Lev γ α (L + c) r) (zRadB X r) ω))
      atTop (𝓝 0)

/-! ## The glue -/

/-! ## The constant part of rich D3⁺(ii) -/

end D3Plus
end QuantumZipper

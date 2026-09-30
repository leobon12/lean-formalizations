import QuantumZipper.Proofs.Probability.Girsanov.Generator
import QuantumZipper.Proofs.ItoLite.OptionalStopping
import QuantumZipper.Proofs.Probability.Girsanov.DynkinStop

/-!
# GIR-4: the h-transform (`Q`-Dynkin formula)

Blueprint `blueprint/GIRSANOV_BLUEPRINT.md`, §2, node GIR-4.

Context of `FrozenMart.martingale_localDynkin_stopped`: `U` solves `U_t = u + ∫₀ᵗ b(U) + B_t e`
(`b` bounded Lipschitz), `F` is `C³` on the open set `O`, `dynkinGen b e F = 0` on `K \ Cl`
(`K ⊆ O` closed, `Cl` closed), `c ≤ F ≤ M` on `K` with `0 < c`, and `U` stays in `K` up to its
hitting time `τ = hittingBtwn U Cl 0 T` of `Cl` (capped at `T`).

Write `J x = DF(x)e / F(x)` for the logarithmic derivative of `F` along the noise and
`Q := (F(U_τ)/F(u)) · P` for the h-transform of `P` by `F`. Then a function `G` with
`L G + J · DG(e) = 0` on `K \ Cl` makes `G(U_{·∧τ})` a `Q`-martingale, and if
`L G + J · DG(e) ≤ 0` (and `G ≥ 0`) then `E^Q[G(U_σ)] ≤ E^Q[G(U_ρ)]` for stopping times
`ρ ≤ σ ≤ τ`.

* `Girsanov.martingale_hTransform`: the martingale (h-transform) version.
* `Girsanov.integral_hTransform_le`: the supermartingale version between two stopping times.

Proof. GIR-0's `Girsanov.dynkinGen_hTransform` gives, on `K \ Cl`,
`L(F·G) = F·(LG + J·DG(e)) + G·LF`, so `F·G` has vanishing (`≤ 0`) generator whenever `F` and
`G` do; and `F·G` is `C³` on `O` and bounded on `K`. The local Dynkin formula for `F·G`
(`FrozenMart.martingale_localDynkin_stopped` in the martingale case, GIR-D
`Girsanov.integral_mul_localDynkin_stopped_le` in the supermartingale case) then gives the
`P`-statements for `F·G`. The density `D_t = F(U_{t∧τ})/F(u)` is a bounded nonnegative
`P`-martingale with `E[D_0] = 1` (here `u ∈ K` and `F u > 0` follow from `U_0 = u` and `hUK`),
so `Q = D_T·P` is a probability measure and Bayes' rule (GIR-1,
`Girsanov.martingale_withDensity_of_mul` and `Girsanov.integral_withDensity_stoppedValue`)
converts the `P`-statements for `F·G` into the `Q`-statements for `G`.

Sources: Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, GTM 274, Springer
2016: the claim "`XD` a `P`-martingale implies `X` a `Q`-martingale" in the proof of Theorem
5.22 (pp. 134–135, PDF pp. 146–147) and §5.6 (pp. 138–139); Lawler, *Conformally Invariant
Processes in the Plane*, §1.9, Example 1.19 (p. 15) and the proof of Lemma 1.30 (p. 23) for the
h-transform generator and its use; Lawler–Zhou, *SLE curves and natural parametrization*,
arXiv:1006.4936, §2.1 (p. 12). The generator identity is GIR-0 (`dynkinGen_hTransform`).

Deviation from Le Gall (recorded in `DEVIATIONS.md`): instead of Itô's formula for `M̃ D` and
the bracket `⟨M, L⟩` (Le Gall, Thm 5.10, p. 113) we check the hypothesis of the h-transform
through the Dynkin formula for the product `F·G` (GIR-0) and Bayes' rule (GIR-1/GIR-D); this is
the same argument with a different tool, as in Revuz–Yor, Ch. VIII, p. 330.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Girsanov

open FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Elementary helpers -/

omit mΩ [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A function that is continuous on a set containing the range of `f` is measurable after
composition with `f`. -/
theorem measurable_comp_of_continuousOn {K O : Set E} {G : E → ℝ} (hKO : K ⊆ O)
    (hG : ContinuousOn G O) {m : MeasurableSpace Ω} {f : Ω → E} (hf : Measurable[m] f)
    (hfK : ∀ ω, f ω ∈ K) : Measurable[m] fun ω => G (f ω) :=
  (hG.mono hKO).domRestrict.measurable.comp (hf.subtype_mk (h := hfK))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- `untopA` of a minimum of two coerced `ℝ≥0`. -/
theorem untopA_min_coe_nnreal (a b : ℝ≥0) :
    (min (a : WithTop ℝ≥0) (b : WithTop ℝ≥0)).untopA = min a b := by
  rw [← WithTop.coe_min, ItoLite.untopA_coe_nnreal]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem untopA_min_coe (a : ℝ≥0) {b : WithTop ℝ≥0} (hb : b ≠ ⊤) :
    (min (a : WithTop ℝ≥0) b).untopA = min a b.untopA := by
  cases b with
  | top => exact absurd rfl hb
  | coe b => rw [untopA_min_coe_nnreal, ItoLite.untopA_coe_nnreal]

/-! ### GIR-4(a): the h-transform martingale -/

/-! ### GIR-4(b): the `Q`-Dynkin inequality between two stopping times -/

end Girsanov
end QuantumZipper

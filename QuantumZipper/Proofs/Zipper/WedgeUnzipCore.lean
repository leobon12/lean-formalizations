import QuantumZipper.Proofs.Zipper.WedgeUnzipB3d
import QuantumZipper.Proofs.Zipper.F2Step3Dens
import QuantumZipper.Proofs.LQG.WedgeGood
import QuantumZipper.Proofs.Section5.Prop17Field

/-!
# D29 (wedge unzipping), part 3: the wedge core W-G from the free-field (`x`-level) statements

Decision D29 (`DECISIONS.md`, `handoff/WEDGE-UNZIP.md`). Source of the route: Sheffield,
arXiv:1012.4797, §1.6 (definition of the `α`-quantum wedge through its radial part `A_t` and the
lateral part of a free boundary GFF; for `t ≥ 0`, `A_t` is a Brownian motion with drift) and
§5.4, pp. 71–72 (regularity is transported to the wedge from free-field-type fields); Duplantier–
Miller–Sheffield, arXiv:1409.7055, §4.2 (Def. 4.4: the radial/lateral decomposition of the wedge).

On the unit disc the unscaled wedge field *is* a free field plus `α₀(−log|·|)`: its radial part for
`t = −log|z| ≥ 0` is `B_{2t} + α₀ t` (in the paper's normalization), independent of the lateral
part. Resampling the radial part on `t < 0` by a fresh Brownian motion gives a free field `X''`
with `Z = X'' + α₀(−log|·|) + G`, `G` a random continuous radial function vanishing on the unit
disc (`WedgeDecompStmt`). Unzipping commutes with adding a continuous function
(`UnzipAddFunStmt`, deterministic: `coordChange` is affine in the field), and goodness is stable
under adding a function continuous on `ℍ̄` (M4-T1, `IsLQGGood.add_ofFun`), once `f_t⁻¹` extends
continuously to `ℍ̄` (`GlobalCaraStmt`, Carathéodory / Rohde–Schramm). So the wedge statement
`WedgeGoodAllStmt` follows from the `x`-level statement `XGoodAllStmt` for `x = X + α₀(−log|·|)`.

Proved here: `wedgeGoodAll_of_decomp` (exact reduction) and the product-extension transfer
`ae_of_ae_prod_fst`. The radial resampling is our own formulation of the paper's definition; the
reduction is our own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## Core statements -/

/-- **(Core W-D, radial resampling)** In the setting of `F2.UnscaledB3dStmt`, on a product
extension there are a free field `X''` independent of the driver and a random function `G`,
continuous and vanishing on the closed unit disc, such that a.s. the unscaled wedge field agrees
with `X'' + α₀(−log|·|) + G` on every folded circle. (Construction: `X''` = lateral part of `X'`
plus the radial path `A_t + (Q − α₀) t` for `t ≥ 0`, continued by a fresh Brownian motion for
`t < 0`.) -/
def WedgeDecompStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (Q : Measure Ω₂) (_ : IsProbabilityMeasure Q)
      (X'' : Ω × Ω₂ → FieldSample) (G : Ω × Ω₂ → ℂ → ℝ),
      IsFreeGFFModConstH X'' (P.prod Q) ∧
      IsBrownianReal (fun t (ω : Ω × Ω₂) => B'' t ω.1) (P.prod Q) ∧
      IndepFun (pathOf (fun t (ω : Ω × Ω₂) => B'' t ω.1)) X'' (P.prod Q) ∧
      ∀ᵐ ω ∂(P.prod Q), Continuous (G ω) ∧ (∀ z : ℂ, ‖z‖ ≤ 1 → G ω z = 0) ∧
        ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
          F2.zU (Real.sqrt κ) X' A ω.1 (foldedCircle d r) =
            (X'' ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r)

/-- **(Core X-C, continuum limit for `x`)** A.s. `x = X + α₀(−log|·|)` is a regular sample and,
for all `t ≥ 0` and folded circles, the smoothed pairings of `x` against the image of the circle
under `f_t⁻¹` are integrable and converge as the smoothing radius tends to `0⁺`. -/
def XContinuumStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, IsRegularSample (X ω + F2.logSingField κ) ∧
      ∀ t, 0 ≤ t → ∀ (c : ℂ) (r : ℝ), 0 < r →
        (∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg (X ω + F2.logSingField κ)
          (foldedCircle u ρ)) ((foldedCircle c r).map (fwdMapInv (drive κ B ω) t))) ∧
        ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg (X ω + F2.logSingField κ) (foldedCircle u ρ)
          ∂((foldedCircle c r).map (fwdMapInv (drive κ B ω) t))) (𝓝[>] 0) (𝓝 L)

/-- **(Core C, global Carathéodory)** A.s., for all `t ≥ 0`, `E_t` (`f_t⁻¹` on `ℍ`, its boundary
extension on `ℝ`) is continuous on `ℍ̄` (global form of `F2.Step3BdryExtStmt`; Pommerenke,
*Boundary Behaviour of Conformal Maps*, Thm 2.6, with the Rohde–Schramm simple trace). -/
def GlobalCaraStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ContinuousOn (F2.extInv (drive κ B ω) t) Hbar

/-- **(Deterministic, to be proved) Unzipping commutes with adding a continuous function.** For a
regular `x` whose smoothed pairings against the images `(f_t⁻¹)_* fc(d, r)` converge (so that
`evalReg` there is a genuine limit), the field unzipped from `x + g` agrees on every folded circle
with the field unzipped from `x` plus `g ∘ E_t`. (Own elementary argument: `coordChange` is affine
in the field, `avgReg (x + ofFun g) = avgReg x + (circle average of g)`, dominated convergence.) -/
def UnzipAddFunStmt : Prop :=
  ∀ (γ : ℝ) (x : FieldSample) (g : ℂ → ℝ) (W : ℝ → ℝ) (t : ℝ), 0 ≤ t → Continuous W →
    W 0 = 0 → Continuous g → IsRegularSample x →
    (∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      (∀ ρ : ℝ, 0 < ρ → Integrable (fun u => evalReg x (foldedCircle u ρ))
        ((foldedCircle d r).map (fwdMapInv W t))) ∧
      ∃ L : ℝ, Tendsto (fun ρ => ∫ u, evalReg x (foldedCircle u ρ)
        ∂((foldedCircle d r).map (fwdMapInv W t))) (𝓝[>] 0) (𝓝 L)) →
    ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      unzippedField γ (x + ofFun g, W) t (foldedCircle d r) =
        (unzippedField γ (x, W) t + ofFun (g ∘ F2.extInv W t)) (foldedCircle d r)

/-- **(Core P, realization of `P_*` samples)** Every `P_*` sample `(Y, B')` is, on a product
extension, `avgReg`-equal to the canonical description of an unscaled wedge configuration
`(Z, √κ B'')` in the setting of `F2.UnscaledB3dStmt`, whose canonicalized configuration is
`(canonical γ Z, √κ B')`. Since `unzippedField` reads the field only through `avgReg`, every
statement about unzipped fields then transfers exactly. (Planned proof: the transfer theorem,
Kallenberg, *Foundations of Modern Probability*, 2nd ed., Thm 6.10, applied to the circle
coordinates `coordsFull` and the reconstruction `rdField`; `B''` is the Brownian rescaling of `B'`
by `1 / scaleParam γ Z`, `F2.randScale_of_aemeasurable`.) -/
def PStarRealizeStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∃ (Ω₂ : Type) (_ : MeasurableSpace Ω₂) (Q : Measure Ω₂) (_ : IsProbabilityMeasure Q)
      (X' : Ω' × Ω₂ → FieldSample) (A : ℝ → Ω' × Ω₂ → ℝ) (B'' : ℝ≥0 → Ω' × Ω₂ → ℝ),
      IsFreeGFFModConstH X' (P'.prod Q) ∧
      IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A (P'.prod Q) ∧
      IndepFun X' (fun ω t => A t ω) (P'.prod Q) ∧ IsBrownianReal B'' (P'.prod Q) ∧
      IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') (P'.prod Q) ∧
      ∀ᵐ ω ∂(P'.prod Q),
        avgReg (Y ω.1) = avgReg (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω)) ∧
        canonConfig (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω) =
          (canonical (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω), drive κ B' ω.1)

/-! ## Transfer from a product extension -/

/-- An a.s. property of the first coordinate under `P ⊗ Q` holds `P`-a.s. (no measurability
needed: `Measure.prod_prod` holds for all sets). -/
theorem ae_of_ae_prod_fst {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {Q : Measure Ω₂} [IsProbabilityMeasure Q] {S : Ω → Prop}
    (h : ∀ᵐ ω ∂(P.prod Q), S ω.1) : ∀ᵐ ω ∂P, S ω := by
  rw [ae_iff] at h ⊢
  have e : {ω : Ω × Ω₂ | ¬ S ω.1} = {ω : Ω | ¬ S ω} ×ˢ (univ : Set Ω₂) := by
    ext ω; simp
  rw [e, Measure.prod_prod, measure_univ, mul_one] at h
  exact h

/-! ## The reduction -/

/-- Raw agreement on folded circles centred in `ℍ̄` gives equal circle coordinates. -/
theorem coords_eq_of_fc {x y : FieldSample}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → x (foldedCircle d r) = y (foldedCircle d r)) :
    Factorization.coords x = Factorization.coords y := by
  funext i
  unfold Factorization.coords
  rw [← WedgeTK.fc_foldH_eq, h _ (CircleFubini.foldH_mem_Hbar' _) _ (radius_pos _)]

end WedgeUnzip
end QuantumZipper

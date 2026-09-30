import QuantumZipper.Proofs.Zipper.UnifRC3UC

/-!
# UNIF-RC3 (decision D33): the exact statements that remain for `UnifUCStmt`

`UnifRC3UC.unifRC3Stmt_of_uc` reduces `RegUnif.UnifRC3Stmt` (hence `B3d.CapCocycleRegStmt`) to
`UnifUCStmt`. This file fixes the objects and the statements of the planned proof of
`UnifUCStmt` (a three-parameter Kolmogorov–Čentsov step for a fixed driver, then the transfer
to the Brownian driver, as in JOINTMOD). Nothing here is assumed anywhere; the statements are
the task boundaries (see `handoff/REG-UNIF.md`, section UNIF-RC3 / D33).

For a driver `W`, `p = (u, s) ∈ tri T`, a dyadic folded circle `fc(d, 2^{-k})`:

* `alphaUS W d k p = (R_{u,s})_* fc(d, 2^{-k})`, `R_{u,s} = revMap (vrev W (u + s)) s`
  (the pushed circle, in the coordinates of the field unzipped by `u`);
* `muUS W d k p ρ = (ψ_u)_* (alphaUS ⋆ fc(·, ρ))`, `ψ_u = fwdMapInv W u` (the circle-smoothed
  pushed circle, in the coordinates of the free field); `ρ = 0` gives `(ψ_{u+s})_* fc(d, 2^{-k})`;
* `detJ κ W d k p j`: the deterministic part of the regularized values at scale `2^{-j}`;
* `PhiW κ W d k j x p = ∫ avgReg y_u j dα_{u,s}` for the field `y_u` unzipped by `u` from
  `h⁰ + x` along the fixed driver `W`.

Statements (all for `T > 0`):

1. `EnergyRadStmt T` (radius modulus, uniform in `p`): the Neumann energy of
   `muUS p ρ − muUS p ρ'` is `≤ C |ρ − ρ'|^a` on `tri T × [0,1]²`.
2. `EnergyParStmt T` (time modulus, uniform in `ρ`): for Hölder drivers, the energy of
   `muUS p ρ − muUS p' ρ` is `≤ C ‖p − p'‖^b` on `tri T² × [0,1]`.
3. `IdentStmt κ T` (stochastic Fubini at fixed parameters): a.s.
   `PhiW j p = X(muUS p 2^{-j}) + detJ p j`.
4. `DetUnifStmt κ T`: `detJ · j → ∫ Ψ_u dα_{u,s}` uniformly on `tri T`.
5. `FixedUCStmt κ T P X`: for every Hölder driver, a.s. `PhiW` is uniformly Cauchy on
   `triQ T` (from 1–4 by `KolmG.exists_continuous_modification_G` with `d = 3`).
6. Transfer: `(∀ Hölder W, FixedUCStmt) ⇒ UnifUCStmt` (measurable event in (path, field),
   `CharFun.ae_indep`, as `RegCont.ae_continuousOn_unzippedField` / `JointModRandom`).

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 (p. 18); Revuz–Yor, 3rd ed.,
Ch. I, Thm (2.1); Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1 (energy of differences of
circle-average measures). The uniformity in the time parameters is an own argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace QuantumZipper
namespace RegUnif

open RegCont B2

/-- The pushed dyadic circle `α_{u,s} = (R_{u,s})_* fc(d, 2^{-k})`. -/
def alphaUS (W : ℝ → ℝ) (d : ℂ) (k : ℕ) (p : ℝ × ℝ) : Measure ℂ :=
  (foldedCircle d (radius k)).map (revMap (vrev W (p.1 + p.2)) p.2)

/-- The circle-smoothed pushed circle in free-field coordinates,
`μ_{u,s,ρ} = (ψ_u)_* (α_{u,s} ⋆ fc(·, ρ))`. -/
def muUS (W : ℝ → ℝ) (d : ℂ) (k : ℕ) (p : ℝ × ℝ) (ρ : ℝ) : Measure ℂ :=
  (bindFc (alphaUS W d k p) ρ).map (fwdMapInv W p.1)

/-- The deterministic density of the field unzipped by `u`: `Ψ_u = h⁰ ∘ ψ_u + Q log |ψ_u'|`. -/
def PsiU (κ : ℝ) (W : ℝ → ℝ) (u : ℝ) (v : ℂ) : ℝ :=
  h0rev κ (fwdMapInv W u v) + Qc (Real.sqrt κ) * Real.log ‖deriv (fwdMapInv W u) v‖

/-- The deterministic part of the regularized values at scale `2^{-j}`. -/
def detJ (κ : ℝ) (W : ℝ → ℝ) (d : ℂ) (k : ℕ) (p : ℝ × ℝ) (j : ℕ) : ℝ :=
  ∫ z, (∫ v, PsiU κ W p.1 v ∂foldedCircle z (radius j)) ∂alphaUS W d k p

/-- The regularized values `∫ avgReg y_u j dα_{u,s}` for a fixed driver `W` and field `x`. -/
def PhiW (κ : ℝ) (W : ℝ → ℝ) (d : ℂ) (k j : ℕ) (x : FieldSample) (p : ℝ × ℝ) : ℝ :=
  ∫ z, avgReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) p.1) j z ∂alphaUS W d k p

/-- `W` is `a`-Hölder with constant `CH` on `[0, T]` (at scales `≤ 1/2`), `W 0 = 0`. -/
def HolderDrv (W : ℝ → ℝ) (T a CH : ℝ) : Prop :=
  Continuous W ∧ W 0 = 0 ∧ 0 < a ∧ a ≤ 1 ∧ 0 ≤ CH ∧
    ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ 1 / 2 → |W t - W t'| ≤ CH * |t - t'| ^ a

/-- **Open (task UNIF-RC3-E1): radius modulus, uniform in the time parameters.** -/
def EnergyRadStmt (T : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ (d : ℂ) (k : ℕ), ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧
    ∀ p ∈ tri T, ∀ ρ ∈ Icc (0 : ℝ) 1, ∀ ρ' ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p ρ') (muUS W d k p ρ, muUS W d k p ρ')| ≤
        C * |ρ - ρ'| ^ a

/-- **Open (task UNIF-RC3-E2): time modulus, uniform in the radius.** -/
def EnergyParStmt (T : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, ∀ a CH : ℝ, HolderDrv W T a CH → ∀ (d : ℂ) (k : ℕ), ∃ C b : ℝ, 0 ≤ C ∧ 0 < b ∧
    ∀ p ∈ tri T, ∀ p' ∈ tri T, ∀ ρ ∈ Icc (0 : ℝ) 1,
      |kernelCov2 neumannH (muUS W d k p ρ, muUS W d k p' ρ) (muUS W d k p ρ, muUS W d k p' ρ)| ≤
        C * dist p p' ^ b

/-- **Open (task UNIF-RC3-ID): stochastic Fubini at fixed parameters** (the steps `hfub`, `hae`,
`hk` inside `CoordReg.ae_regShift_coordChange_revMap_gen`, for the measure `α_{u,s}`). -/
def IdentStmt (κ T : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → FieldSample),
    IsFreeGFFModConstH X P → ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ (d : ℂ) (k : ℕ),
      ∀ p ∈ tri T, ∀ j : ℕ, ∀ᵐ ω ∂P,
        PhiW κ W d k j (X ω) p = X ω (muUS W d k p (radius j)) + detJ κ W d k p j

/-- **Open (task UNIF-RC3-DET): uniform convergence of the deterministic part.** -/
def DetUnifStmt (κ T : ℝ) : Prop :=
  ∀ W : ℝ → ℝ, Continuous W → W 0 = 0 → ∀ (d : ℂ) (k : ℕ),
    TendstoUniformlyOn (fun j p => detJ κ W d k p j)
      (fun p => ∫ v, PsiU κ W p.1 v ∂alphaUS W d k p) atTop (tri T)

/-- **Open (task UNIF-RC3-FIX): uniform Cauchy for a fixed Hölder driver** (from
`EnergyRadStmt`, `EnergyParStmt`, `IdentStmt`, `DetUnifStmt` by the three-parameter
Kolmogorov–Čentsov step `KolmG.exists_continuous_modification_G (d := 3)`, as
`JointModFixed.exists_contMod_ν4`). -/
def FixedUCStmt (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → FieldSample) :
    Prop :=
  ∀ W : ℝ → ℝ, ∀ a CH : ℝ, HolderDrv W T a CH → ∀ (d : ℂ) (k : ℕ), ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ N : ℕ,
    ∀ j, N ≤ j → ∀ j', N ≤ j' → ∀ p ∈ triQ T,
      |PhiW κ W d k j (X ω) p - PhiW κ W d k j' (X ω) p| ≤ 1 / ((n : ℝ) + 1)

/-- `PhiJ` is `PhiW` along the Brownian driver (pathwise identification used by the transfer
step). -/
theorem PhiJ_eq_PhiW {Ω : Type} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (κ : ℝ) (d : ℂ)
    (k j : ℕ) (ω : Ω) (p : ℝ × ℝ) :
    PhiJ κ B X d k j ω p = PhiW κ (drive κ B ω) d k j (X ω) p := by
  unfold PhiJ PhiW alphaUS
  rw [B2.Yf_eq_unzippedField, add_sub_cancel_right]
  rfl

end RegUnif
end QuantumZipper

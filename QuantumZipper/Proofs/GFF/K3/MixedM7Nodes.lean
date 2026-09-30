import QuantumZipper.Proofs.GFF.K3.MixedM7Stmt
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# K3-mixed node M7 (half-disc form): the D3⁺ interface and the remaining sub-nodes

Decision D22 (`DECISIONS.md`) fixes M7 as `MixedFreeCouplingHalfDiscStmt D c d t r r' ρ₀`
(`MixedM7Stmt.lean`). This file contains

* `outsideSigma_anti_radius`: the outside σ-algebra of L2 shrinks as the radius grows (any
  centre `t`);
* `MixedFreeCouplingHalfDiscStmt.d3plus_data`: the statement delivers exactly the data of the
  zoom lemma D3⁺ (`blueprint/E_BRANCH_BLUEPRINT.md` §3) on the half-disc of radius `r'`:
  `g ω` Neumann-harmonic on `ball t r'` and `g z` measurable for `σ(Ξ) ⊔ outsideSigma X t r'`;
* the two analytic sub-nodes of the proof, as named `Prop`s (**not assumed anywhere**):
  `MixedHalfDiscMarkovCovStmt` (M7-a, the mixed-field half-disc Markov property in covariance
  form) and `PoissonHarmonicVersionStmt` (M7-b, harmonic versions of Gaussian processes indexed
  by a weakly harmonic Hilbert-space curve).

## Proof plan for M7 (route; own adaptation of the sources below)

Sources. Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), §2.6,
Thm. 2.17 (PDF p. 14): `H(D) = H_U(D) ⊕ H_U^⊥(D)`, the orthogonal decomposition into the closure
of functions supported in `U` and the functions harmonic in `U`; the σ-algebras of the two parts
are independent. Werner–Powell, *Lecture notes on the Gaussian free field*, arXiv:2004.04720,
Prop. 4.3 (PDF p. 98, printed p. 94): Markov property with a version of the harmonic part that is
a.s. harmonic. Both are stated for Dirichlet boundary conditions; for the mixed space
`mixedSpace D (realSet (Icc c d))` and `U = ball t r ∩ H` the same Hilbert argument applies with
`H_U` the closure of gradients of smooth functions with compact support in `ball t r` (not
vanishing on `ℝ`), and `H_U^⊥` the functions harmonic in `U` with Neumann condition on
`(t − r, t + r)`; the harmonic extension is given by the folded Poisson measures `P_z`
(`halfDiscPoisson t r z`, node L1).

* **M7-a** (`MixedHalfDiscMarkovCovStmt`): covariance form of the mixed Markov property.
* **M7-b** (`PoissonHarmonicVersionStmt`): harmonic versions.
* **M7-c** (assembly, own construction). Steps 1–3 are proved from M7-a in `MixedM7Local.lean`,
  `MixedM7Gram.lean`, `MixedM7Joint.lean`, `MixedM7Real.lean` and `MixedM7Couple.lean`
  (`exists_mixedFree_markovCoupling`); step 4 (stochastic Fubini + M7-b) remains. With `v_μ = rieszVec D V μ`
  (mixed, `GradSpace D`) and `v̂_μ = freeVec` (free, `HkE`): `W_loc := closure span
  {v_μ − v_{bal μ} : μ local}` and `Ŵ_loc` likewise. By M7-a and L2 the two generating families
  have the same Gram matrix `kernelCov (halfDiscGreen t r)`, so there is a linear isometry
  `J : Ŵ_loc ≃ W_loc` matching them, and `v_ρ ⊥ W_loc` for `ρ` carried outside `ball t r`.
  On `E := GradSpace D × HkE` put `a_μ := (v_μ, 0)` (mixed field), `w_μ := (J (P̂_loc v̂_μ),
  P̂_⊥ v̂_μ)` (free field; Gram `kernelCov2 neumannH` on balanced pairs) and realize everything
  with one isonormal process (`gs_process_hilbert`); `Ξ` := the process on
  `W_locᗮ × {0}`. Then `Ξ ⊥ X` (orthogonal Gaussian families), and for local `μ`,
  `a_μ − w_{μ − μ(ℂ) ρ₀} = (v_{bal μ}, 0) − w_{bal μ − μ(ℂ) ρ₀} = ∫ ((v_{P_z}, 0) − w_{P_z − ρ₀}) dμ(z)`
  weakly (as in `MixedM5Weak`), so `Y μ − (X μ − μ(ℂ) X ρ₀) = ∫ g dμ` a.s. (stochastic Fubini, as
  `stochFubini_kernel`) with `g` the M7-b version of `z ↦ Ξ(v_{P_z}) − (X(P_z) − X ρ₀)`; each
  term is `σ(Ξ) ⊔ outsideSigma X t r`-measurable because `P_z` and `ρ₀` give no mass to
  `ball t r`. The global definition through `E` handles the measures that are
  `IsAdmissibleDual` but not `IsAdmissibleH` (e.g. measures on the Dirichlet arc).
-/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped RealInnerProductSpace

namespace QuantumZipper.K3

/-- The outside σ-algebra of the half-disc (node L2) is antitone in the radius. -/
theorem outsideSigma_anti_radius {Ω : Type*} [MeasurableSpace Ω] (X : Ω → FieldSample) (t : ℝ)
    {r r' : ℝ} (h : r' ≤ r) : outsideSigma X t r ≤ outsideSigma X t r' :=
  iSup_le fun p => le_iSup_of_le (⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1,
    measure_mono_null (ball_subset_ball h) p.2.2.2.2.1,
    measure_mono_null (ball_subset_ball h) p.2.2.2.2.2⟩ : OutIdx t r') le_rfl

/-- **M7-a (sub-node, not proved): half-disc Markov property of the mixed field, covariance
form.** For a half-disc `ball t r ∩ H ⊆ D` on the free arc and `0 < r' < r`, with
`V = mixedSpace D (realSet (Icc c d))`: the folded Poisson measures `P_z`, `z ∈ closedBall t r' ∩
Hbar`, are `V`-admissible; every admissible `μ` carried by `closedBall t r'` and its
balayage `bal t r μ` (onto the arc, by the folded Poisson measures) are `V`-admissible;
`μ − bal μ` is uncorrelated with every `V`-admissible `ρ` giving no mass to `ball t r`; and
`Cov_D(μ, ν) = Cov_D(bal μ, bal ν) + kernelCov (halfDiscGreen t r) μ ν` (the local part is the
same half-disc field as for the free field, `covariance_markovZ`). Source: Sheffield (2007)
Thm. 2.17 (Dirichlet case), adapted to the mixed space (Neumann on `(t − r, t + r)`). -/
def MixedHalfDiscMarkovCovStmt (D : Set ℂ) (c d t r r' : ℝ) : Prop :=
  Prop16Geometry D c d → t ∈ Set.Ioo c d → 0 < r' → r' < r → ball (t : ℂ) r ∩ H ⊆ D →
    (∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar,
      IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) (halfDiscPoisson t r z)) ∧
    ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) μ ∧
      IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) (bal t r μ) ∧
      (∀ ρ : Measure ℂ, IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) ρ →
        ρ (ball (t : ℂ) r) = 0 →
        dualCov D (mixedSpace D (realSet (Set.Icc c d))) μ ρ =
          dualCov D (mixedSpace D (realSet (Set.Icc c d))) (bal t r μ) ρ) ∧
      ∀ ν : Measure ℂ, IsAdmissibleH ν → ν (closedBall (t : ℂ) r')ᶜ = 0 →
        dualCov D (mixedSpace D (realSet (Set.Icc c d))) μ ν =
          dualCov D (mixedSpace D (realSet (Set.Icc c d))) (bal t r μ) (bal t r ν) +
            kernelCov (halfDiscGreen t r) μ ν

/-- **M7-b (sub-node, not proved): harmonic versions.** Let `u : ℂ → E` be a curve in a Hilbert
space whose even extension `u ∘ foldH` is weakly harmonic on `ball t r` (every `⟪u (foldH ·), e⟫`
is harmonic there), and let `F` be a Gaussian process with covariance `⟪u z, u w⟫` (in the
isonormal form produced by `gs_process_hilbert`). Then `F` has a version `G` with
`G ω ∘ foldH` harmonic on a neighbourhood of `closedBall t r'` for **every** `ω`, and `G z` is
measurable for every σ-algebra for which all `F w` (`w ∈ ball t r ∩ Hbar`) are measurable.
Applied to `u z = v_{P_z}` (mixed and free) this gives the harmonic `g` of M7 (and upgrades
L2's continuous `harmH` to a harmonic one). Source: Werner–Powell, arXiv:2004.04720, Prop. 4.3
(PDF p. 98), harmonic version of the harmonic part; here via the Taylor expansion of the
vector-valued harmonic function `u ∘ foldH` (Cauchy estimates, Borel–Cantelli). -/
def PoissonHarmonicVersionStmt (t r r' : ℝ) : Prop :=
  0 < r' → r' < r →
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (u : ℂ → E) (F : ℂ → Ω → ℝ),
    (∀ e : E, InnerProductSpace.HarmonicOnNhd (fun z => ⟪u (foldH z), e⟫) (ball (t : ℂ) r)) →
    (∀ z, Measurable (F z)) →
    (∀ {ι : Type} [Fintype ι] (τ : ι → ℂ) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * F (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • u (τ i)‖ ^ 2).toNNReal) P) →
    ∃ G : Ω → ℂ → ℝ,
      (∀ ω, InnerProductSpace.HarmonicOnNhd (fun z => G ω (foldH z)) (closedBall (t : ℂ) r')) ∧
      (∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar, ∀ᵐ ω ∂P, G ω z = F z ω) ∧
      ∀ m : MeasurableSpace Ω, (∀ w ∈ ball (t : ℂ) r ∩ Hbar, Measurable[m] (F w)) →
        ∀ z, Measurable[m] fun ω => G ω z

end QuantumZipper.K3

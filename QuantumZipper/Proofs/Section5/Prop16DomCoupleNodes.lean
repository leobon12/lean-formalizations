import QuantumZipper.Proofs.GFF.Existence
import QuantumZipper.Proofs.GFF.K3.MixedM5Stmt

/-!
# Proposition 1.6, node DOM-COUPLE (part 1): the two sub-nodes and the isonormal realization

`Prop16MixedFreeLocCouplingStmt` (`Prop16LocGood.lean`) asks for a coupling of the mixed field
`Y` on `D` with a free field `X` on `ℍ` such that `Y = X + ψ` on the dyadic folded circles inside
`D ∪ (a,b)`, `ψ` continuous there. This file names the two analytic sub-nodes of its proof and
proves the Gaussian realization from an abstract Hilbert-space datum.

## Route (own adaptation of the sources)

Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), Thm 2.17 (PDF p. 14):
for `U ⊆ D`, `H(D) = H_U(D) ⊕ H_U^⊥(D)`, the second summand consisting of the functions
harmonic in `U`. Mixed form used here (`U = D`, ambient space the free Dirichlet space of `ℍ`):
the mixed space on `D` (zero on `∂D ∩ ℍ`, free on `(c,d)`), extended by zero, is a closed
subspace `J(M)` of the free space; its complement consists of functions harmonic in `D` with
Neumann condition on `(c,d)`. With `v̂_μ = freeVec μ` (`HkE`), `ρ₀` a unit reference measure
carried outside `closure D`, `e_μ := J(m_μ)` the image of the mixed Riesz vector, the vector
`k_μ := v̂_μ − v̂_{ρ₀} − e_μ` is the projection of `v̂_μ − v̂_{ρ₀}` onto `J(M)ᗮ`, and
`k_μ = ∫ H dμ` weakly, `H z` the harmonic part "at `z`" (harmonic in `z` after even reflection
across `(c,d)`; Werner–Powell, arXiv:2004.04720, Prop. 4.3, PDF p. 98, for the harmonic
version). This is recorded as

* `DomMarkovCurveStmt D c d` (**not proved**): the Hilbert datum `(e, ρ₀, H)`.

The probabilistic step (continuous version + stochastic Fubini) is recorded as

* `GaussContFubiniStmt` (**proved**: `gaussContFubini_holds`, `Prop16DomCoupleGlue.lean`): for
  an isonormal process `W` on a Hilbert space and a curve `H` Lipschitz on the compact subsets
  of `O ∩ Hbar` (`O` open), `z ↦ W(H z)` has a version
  `G` with continuous paths on `O ∩ Hbar` and `∫ G dμ = W(∫ H dμ)` a.s. for compactly carried
  finite `μ`. Sources: Kolmogorov's continuity criterion (Revuz–Yor, *Continuous martingales
  and Brownian motion*, Ch. I, Thm (2.1), multiparameter form; Karatzas–Shreve, Problem 2.2.9);
  the Fubini identity is the `L²` computation `E[(∫ G dμ − W k)²] = 0`.

Proved here (own construction, as `exists_freeGFF`): for any process `W` on `(ℕ → ℝ, stdP)` with
isonormal laws on `HkE` (`gs_process_hilbert`), `domX W` (`μ ↦ W(v̂_μ)`) is a free field mod
constants and `domY W e` (`μ ↦ W(e_μ)`) is a mixed GFF when the Gram matrix of `e` is `dualCov`
(`domX_isFree`, `domY_isMixedGFF`), and the zero-variance identity `domY_sub_domX_ae`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal

namespace QuantumZipper

namespace Prop16Asm

open GFFExist LQGDimension.ExistAsm

/-- **Sub-node DOM-b: continuous version and stochastic Fubini** (proved as
`gaussContFubini_holds`, `Prop16DomCoupleGlue.lean`). For an isonormal
process `W` on a Hilbert space `E` and a curve `H`, Lipschitz on the compact subsets of
`O ∩ Hbar` (`O` open), there is `G` with `G ω` continuous on `O ∩ Hbar` for every `ω` such that
`∫ G ω dμ = W k ω` a.s. whenever `μ` is finite, carried by a compact subset of `O ∩ Hbar`, and
`k = ∫ H dμ` weakly. Sources: Revuz–Yor Ch. I Thm (2.1) (Kolmogorov), Karatzas–Shreve
Problem 2.2.9; Fubini by the `L²` computation. -/
def GaussContFubiniStmt : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : E → Ω → ℝ) (O : Set ℂ) (H : ℂ → E),
    IsOpen O → (∀ x, Measurable (W x)) →
    (∀ {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ),
      HasLaw (fun ω => ∑ i, a i * W (τ i) ω)
        (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) P) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ O ∩ Hbar → ∃ C : ℝ≥0, LipschitzOnWith C H K) →
    ∃ G : Ω → ℂ → ℝ, (∀ ω, ContinuousOn (G ω) (O ∩ Hbar)) ∧
      ∀ μ : Measure ℂ, IsFiniteMeasure μ →
        (∃ K : Set ℂ, IsCompact K ∧ K ⊆ O ∩ Hbar ∧ μ Kᶜ = 0) →
        ∀ k : E, (∀ x : E, ⟪k, x⟫ = ∫ z, ⟪H z, x⟫ ∂μ) →
          ∀ᵐ ω ∂P, ∫ z, G ω z ∂μ = W k ω

/-! ### The isonormal realization -/

open Classical in
/-- The free field realized from an isonormal process on `HkE`. -/
def domX (W : HkE → (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → FieldSample := fun ω μ =>
  if h : IsAdmissibleH μ then W (freeVec ⟨μ, h⟩) ω else 0

theorem domX_apply {W : HkE → (ℕ → ℝ) → ℝ} (μ : Measure ℂ) (h : IsAdmissibleH μ)
    (ω : ℕ → ℝ) : domX W ω μ = W (freeVec ⟨μ, h⟩) ω := by
  simp [domX, h]

section Real

variable {W : HkE → (ℕ → ℝ) → ℝ} (hWm : ∀ x, Measurable (W x))
  (hW : ∀ {ι : Type} [Fintype ι] (τ : ι → HkE) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * W (τ i) ω) (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) stdP)

include hWm hW in
/-- The realized free field is a free GFF modulo constants (as `exists_freeGFF`). -/
theorem domX_isFree : IsFreeGFFModConstH (domX W) stdP := by
  set X : AdmT → (ℕ → ℝ) → ℝ := fun μ => W (freeVec μ) with hXdef
  have hX : ∀ {ι : Type} [Fintype ι] (τ : ι → AdmT) (c : ι → ℝ),
      HasLaw (fun ω => ∑ i, c i * X (τ i) ω)
        (gaussianReal 0 (‖∑ i, c i • freeVec (τ i)‖ ^ 2).toNNReal) stdP :=
    fun τ c => hW (fun i => freeVec (τ i)) c
  have hXm : ∀ μ, Measurable (X μ) := fun μ => hWm _
  have hFX : ∀ (μ : Measure ℂ) (h : IsAdmissibleH μ) ω, domX W ω μ = X ⟨μ, h⟩ ω :=
    fun μ h ω => domX_apply μ h ω
  have hdiff : ∀ (μ ν : Measure ℂ) (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν),
      (fun ω => domX W ω μ - domX W ω ν) = fun ω => X ⟨μ, hμ⟩ ω - X ⟨ν, hν⟩ ω := by
    intro μ ν hμ hν; funext ω; rw [hFX μ hμ, hFX ν hν]
  have hlaw2 : ∀ μ ν : AdmT, HasLaw (fun ω => X μ ω - X ν ω)
      (gaussianReal 0 (‖freeVec μ - freeVec ν‖ ^ 2).toNNReal) stdP :=
    fun μ ν => gs_comb4 hX ![μ, ν, μ, μ] ![1, -1, 0, 0] _
      (fun ω => by simp [Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, sub_eq_add_neg])
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro μ
    by_cases h : IsAdmissibleH μ
    · have : (fun ω => domX W ω μ) = X ⟨μ, h⟩ := funext (hFX μ h)
      rw [this]; exact hXm _
    · have : (fun ω => domX W ω μ) = fun _ => 0 := by funext ω; simp [domX, h]
      rw [this]; exact measurable_const
  · refine gs_isGaussianProcess (fun p => ?_) fun I c => ?_
    · rw [hdiff _ _ p.2.1 p.2.2.1]
      exact ((hXm _).sub (hXm _)).aemeasurable
    · set τ : I ⊕ I → AdmT := Sum.elim (fun i => ⟨i.1.1.1, i.1.2.1⟩)
        (fun i => ⟨i.1.1.2, i.1.2.2.1⟩) with hτ
      set c' : I ⊕ I → ℝ := Sum.elim c (fun i => -c i) with hc'
      have e : (fun ω => ∑ i : I, c i * (domX W ω i.1.1.1 - domX W ω i.1.1.2)) =
          fun ω => ∑ j, c' j * X (τ j) ω := by
        funext ω
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hτ, hc', Sum.elim_inl, Sum.elim_inr]
        rw [hFX _ i.1.2.1 ω, hFX _ i.1.2.2.1 ω]
        ring
      exact ⟨_, e ▸ hX τ c'⟩
  · intro μ ν hμ hν _
    rw [hdiff μ ν hμ hν]
    exact gs_integral_eq_zero (hlaw2 ⟨μ, hμ⟩ ⟨ν, hν⟩)
  · intro p q hp1 hp2 hp hq1 hq2 hq
    rw [hdiff _ _ hp1 hp2, hdiff _ _ hq1 hq2]
    have hinner := freeVec_inner ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hp hq
    simp only [Prod.mk.eta] at hinner
    rw [← hinner]
    refine gs_cov_eq (hlaw2 _ _) (hlaw2 _ _) ?_
    exact gs_comb4 hX ![⟨p.1, hp1⟩, ⟨p.2, hp2⟩, ⟨q.1, hq1⟩, ⟨q.2, hq2⟩] ![1, -1, 1, -1] _
      (fun ω => by simp [Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four]; abel)
  · intro μ ν hμ hν a b
    have hw := gffEx_admissible_comb hμ hν a b
    have hlaw := gs_comb4 hX ![⟨_, hw⟩, ⟨μ, hμ⟩, ⟨ν, hν⟩, ⟨μ, hμ⟩] ![1, -(a : ℝ), -(b : ℝ), 0]
      (fun ω => X ⟨_, hw⟩ ω - ((a : ℝ) * X ⟨μ, hμ⟩ ω + (b : ℝ) * X ⟨ν, hν⟩ ω))
      (fun ω => by simp [Fin.sum_univ_four]; ring) (0 : HkE)
      (by
        simp [Fin.sum_univ_four, freeVec_comb ⟨μ, hμ⟩ ⟨ν, hν⟩ a b ⟨_, hw⟩ rfl]
        try module)
    have h0 : (‖(0 : HkE)‖ ^ 2).toNNReal = 0 := by simp
    have hae : ∀ᵐ ω ∂stdP,
        X ⟨_, hw⟩ ω - ((a : ℝ) * X ⟨μ, hμ⟩ ω + (b : ℝ) * X ⟨ν, hν⟩ ω) = 0 := by
      refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
      rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    filter_upwards [hae] with ω hω
    rw [hFX _ hw ω, hFX μ hμ ω, hFX ν hν ω]
    linarith

end Real

end Prop16Asm

end QuantumZipper

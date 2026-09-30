import QuantumZipper.Proofs.Zipper.FieldLawlerCoverDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-IMAGESUM: splitting `FieldLawler.FLImageCrosscutSumStmt` into its three separate inputs

Task FL-IMAGESUM (helper of FL-THM, D75).

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015)
no. 10, arXiv:1407.3314 (`literature/1407.3314.pdf`), proof of **Prop. 3.4** (p. 9), using
**Lemma 3.3** (p. 8, proved in §4, Prop. 4.1 and Cor. 4.2, pp. 10–11), **(2.1)** and **(2.4)**
(pp. 6), and the first inequality `ℰ_ℍ(η, γ̃) ≥ ℰ_ℍ(η, ℝ₋)` of the proof of **Prop. 3.1** (p. 7);
conformal invariance of excursion measure: Lawler, *Conformally invariant processes in the plane*,
Prop. 5.8 (cited by FL p. 5).

`FLImageCrosscutSumStmt` asks for three different things at once, which FL obtain from three
different sources; they are separated here, and `flImageCrosscutSum_of_parts` (proved) recombines
them.

1. `FLImageTopStmt` — **topology** (FL p. 9, first display: `D ∩ C_r = ⋃ⱼ ηⱼ`, crosscuts of
   `D`). The components `ηⱼ` of `H_t ∩ {|z| = ε}` map under `Z_t` to pairwise disjoint crosscuts
   `Z_t ηⱼ` of `ℍ` lying in `Z_t(H_t ∩ {|z| = ε})`, each with both real endpoints on one side of
   `0` (the tip `Z_t⁻¹(0+)` is at distance `R > ε`), and every point of `Z_t(H_t ∩ B(0, ε))` lies
   under one of them.
2. `FLHullHarmExistsStmt` — **existence of harmonic measure** of a crosscut in the unbounded
   component of `ℍ \ η` (Perron's method; Garnett–Marshall, *Harmonic Measure*, Ch. III and its
   notes, PDF p. 91; the boundary is regular since `arcH η` is a continuum and the rest lies in
   `ℝ`). The repository has this only for `bddPart` (`lwHarm_exists_crosscut`).
3. `FLImageSumBoundStmt` — **the analytic estimate** of FL p. 9: for ANY family of pairwise
   disjoint image crosscuts contained in `Z_t(H_t ∩ {|z| = ε})` (such a crosscut is automatically
   the image of a whole component, since its ends leave every compact subset of `ℍ`),
   `Σⱼ ℰ_ℍ(Z_t ηⱼ, opposite half-line) ≤ C ε/R` for `ε ≤ δ₀ R`. FL's chain, transported to
   `H_t` by conformal invariance:
   `ℰ_ℍ(Z_t ηⱼ, ℝ∓) ≤ ℰ_ℍ(Z_t ηⱼ, Z_t γ̃) = ℰ_{H_t}(ηⱼ, γ̃) ≤ ℰ_{H_t}(ηⱼ, C_R)` (FL p. 7 and
   (2.1): `γ̃` a curve from the tip to `∞` outside `B(0, R)`), then
   `Σⱼ ℰ_{H_t}(ηⱼ, C_R) ≤ 2 ℰ_{H_t}(C_ε, C_R)` (Lemma 3.3), `≤ 2 ℰ_ℍ(C_ε, C_R) ≤ c ε/R` ((2.4)).

**Obstacle to proving 3 here.** The repository has excursion measure only in the half-plane with
one real boundary set (`excR h J = ∫_J ∂_y h`); FL's chain needs `ℰ_D(V, W)` between two
non-real boundary arcs of a general domain (`H_t`, `ℍ \ B̄(0, ε)`), its conformal invariance,
the strong-Markov decomposition behind (2.1), and the Brownian reflection argument of Prop. 4.1.
In pointwise harmonic-function form (the form closest to the repository's `IsHarmMeas`),
Cor. 4.2 reads `Σ_{j ∈ S'} hⱼ ≤ 2 ω` on `⋂_{j ∈ S'} hullComp (Z_t ηⱼ)`, `ω` the harmonic measure
of `⋃_{j ∈ S'} Z_t ηⱼ` there, for the sub-family `S'` on one side of `0`; the remaining step is
`∫_{ℝ∓} ∂_y ω ≤ c ε/R` (FL (2.1) with the separating curve `Z_t(C_R)`, and (2.4)).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **Topological part (FL p. 9, first display of the proof of Prop. 3.4).** At the first time
`t` the simple trace reaches `{|z| = R}` and for `0 < ε < R`, the images `Z_t ηⱼ` of the
components `ηⱼ` of `H_t ∩ {|z| = ε}` are pairwise disjoint crosscuts of `ℍ` inside
`Z_t(H_t ∩ {|z| = ε})`, with both real endpoints on one side of `0`, and every point of
`Z_t(H_t ∩ B(0, ε))` lies under one of them. -/
def FLImageTopStmt : Prop :=
  ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
    ∀ t R ε : ℝ, 0 ≤ t → 0 < R → 0 < ε → ε < R →
    trace W 0 = 0 → ContinuousOn (trace W) (Icc 0 t) → InjOn (trace W) (Icc 0 t) →
    (∀ s ∈ Ioc 0 t, trace W s ∈ H) →
    fwdHull W t = trace W '' Ioc 0 t →
    (∀ s ∈ Ico 0 t, ‖trace W s‖ < R) → ‖trace W t‖ = R →
    Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W t)) →
    ∃ (S : Set ℕ) (η : ℕ → ℝ → ℂ) (a b : ℕ → ℝ),
      (∀ j ∈ S, IsCrosscutH (η j) ∧ Tendsto (η j) (𝓝[>] 0) (𝓝 (a j : ℂ)) ∧
        Tendsto (η j) (𝓝[<] 1) (𝓝 (b j : ℂ)) ∧ 0 < a j * b j ∧
        arcH (η j) ⊆ {p | ‖fwdMapInv W t p‖ = ε}) ∧
      S.PairwiseDisjoint (fun j => arcH (η j)) ∧
      ∀ p ∈ H, ‖fwdMapInv W t p‖ < ε → ∃ j ∈ S, p ∉ hullComp (η j)

/-- **Existence of harmonic measure** of a crosscut `η` of `ℍ` in the unbounded component of
`ℍ \ η` (Perron's method, Garnett–Marshall, *Harmonic Measure*, Ch. III, PDF p. 91). -/
def FLHullHarmExistsStmt : Prop :=
  ∀ η : ℝ → ℂ, IsCrosscutH η → ∃ h : ℂ → ℝ, IsHarmMeas (hullComp η) (arcH η) h

/-- **Analytic part (FL p. 9: Lemma 3.3, (2.1), (2.4), and p. 7).** For every family of pairwise
disjoint crosscuts of `ℍ` contained in `Z_t(H_t ∩ {|z| = ε})` with both endpoints on one side of
`0`, and their harmonic measures in the unbounded components, the excursion measures to the
opposite half-line sum to at most `C ε/R` when `ε ≤ δ₀ R`. -/
def FLImageSumBoundStmt : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
    ∀ t R ε : ℝ, 0 ≤ t → 0 < R → 0 < ε → ε ≤ δ₀ * R →
    trace W 0 = 0 → ContinuousOn (trace W) (Icc 0 t) → InjOn (trace W) (Icc 0 t) →
    (∀ s ∈ Ioc 0 t, trace W s ∈ H) →
    fwdHull W t = trace W '' Ioc 0 t →
    (∀ s ∈ Ico 0 t, ‖trace W s‖ < R) → ‖trace W t‖ = R →
    Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W t)) →
    ∀ (S : Set ℕ) (η : ℕ → ℝ → ℂ) (a b : ℕ → ℝ) (h : ℕ → ℂ → ℝ),
      (∀ j ∈ S, IsCrosscutH (η j) ∧ Tendsto (η j) (𝓝[>] 0) (𝓝 (a j : ℂ)) ∧
        Tendsto (η j) (𝓝[<] 1) (𝓝 (b j : ℂ)) ∧ 0 < a j * b j ∧
        arcH (η j) ⊆ {p | ‖fwdMapInv W t p‖ = ε} ∧
        IsHarmMeas (hullComp (η j)) (arcH (η j)) (h j)) →
      S.PairwiseDisjoint (fun j => arcH (η j)) →
      ∑' j, S.indicator (fun j => excR (h j) {x : ℝ | x * a j ≤ 0}) j ≤
        ENNReal.ofReal (C * (ε / R))

/-- **Reduction.** The three parts give `FLImageCrosscutSumStmt`. -/
theorem flImageCrosscutSum_of_parts (hT : FLImageTopStmt) (hE : FLHullHarmExistsStmt)
    (hB : FLImageSumBoundStmt) : FLImageCrosscutSumStmt := by
  obtain ⟨C, δ₀, hC, hδ₀, hB⟩ := hB
  refine ⟨C, min δ₀ (1 / 2), hC, lt_min hδ₀ (by norm_num), ?_⟩
  intro W hW hW0 t R ε ht hR hε hεR h0 hcont hinj hH hhull hlt heq htip
  have hεδ : ε ≤ δ₀ * R :=
    hεR.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hR.le)
  have hεR' : ε < R := by
    have := hεR.trans (mul_le_mul_of_nonneg_right (min_le_right δ₀ (1 / 2 : ℝ)) hR.le)
    linarith
  obtain ⟨S, η, a, b, hS, hdisj, hcov⟩ :=
    hT W hW hW0 t R ε ht hR hε hεR' h0 hcont hinj hH hhull hlt heq htip
  have hex : ∀ j, ∃ g : ℂ → ℝ, j ∈ S → IsHarmMeas (hullComp (η j)) (arcH (η j)) g := by
    intro j
    by_cases hj : j ∈ S
    · obtain ⟨g, hg⟩ := hE (η j) (hS j hj).1
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h' => absurd h' hj⟩
  choose h hh using hex
  refine ⟨S, η, a, b, h, fun j hj => ⟨(hS j hj).1, (hS j hj).2.1, (hS j hj).2.2.1,
    (hS j hj).2.2.2.1, hh j hj⟩, ?_, hcov⟩
  exact hB W hW hW0 t R ε ht hR hε hεδ h0 hcont hinj hH hhull hlt heq htip S η a b h
    (fun j hj => ⟨(hS j hj).1, (hS j hj).2.1, (hS j hj).2.2.1, (hS j hj).2.2.2.1,
      (hS j hj).2.2.2.2, hh j hj⟩) hdisj

end FieldLawler
end QuantumZipper

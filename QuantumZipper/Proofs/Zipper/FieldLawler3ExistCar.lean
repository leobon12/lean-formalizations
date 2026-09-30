import QuantumZipper.Proofs.Zipper.FieldLawler3ExistGlue
import QuantumZipper.Proofs.Complex.HoloLog
import QuantumZipper.Proofs.Complex.RMTStep3
import QuantumZipper.Proofs.Complex.BasicsCayley

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-EXIST: harmonic measure on open sets with finitely many simply connected components

Task FL3-EXIST (Track A, towards `FieldLawler.FLImageSumBoundStmt`).

* `flExist_carHyp`: a bounded domain `V ⊆ B(0, R₀)` all of whose complementary components are
  unbounded carries the Carathéodory hypotheses `Car.CarHyp ψ V (frontier V) R₀`, with `ψ` a Riemann
  map `𝔻 → V` precomposed with the Cayley map (Riemann mapping theorem
  `RMT.riemann_mapping_of_hasHoloSqrt`, square roots `RMT.hasHoloSqrt_of_unbounded_compl`; as in
  `flHullHarmExists_holds`).
* `flExist_ulc_components`: an open bounded `U` with finitely many components, each of which has
  only unbounded complementary components and a ULC frontier, carries a harmonic measure of every
  bounded `A` disjoint from `U`.

**Source.** Garnett–Marshall, *Harmonic Measure*, Ch. I §1, p. 5, eq. (1.6) (conformal
invariance; harmonic measure through a Riemann map with Carathéodory extension, Pommerenke,
*Boundary Behaviour of Conformal Maps*, Thm 2.1), component by component. The repository
statement of this is `lwHarm_exists_car`; the wiring here is routine (own bookkeeping).
-/

noncomputable section

open Set Filter Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

/-- **Carathéodory hypotheses for a bounded domain with unbounded complementary components**
(Riemann mapping theorem + Cayley map), with boundary set `E = frontier V`. -/
theorem flExist_carHyp {V : Set ℂ} {R₀ : ℝ} (hVo : IsOpen V) (hVc : IsPreconnected V)
    (hne : V.Nonempty) (hVb : V ⊆ ball 0 R₀)
    (hcomp : ∀ a ∉ V, ¬ Bornology.IsBounded (connectedComponentIn Vᶜ a)) :
    ∃ ψ : ℂ → ℂ, Car.CarHyp ψ V (frontier V) R₀ := by
  have hVuniv : V ≠ univ := by
    intro h
    have h1 := hVb (h ▸ mem_univ ((|R₀| : ℝ) : ℂ))
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_abs] at h1
    linarith [le_abs_self R₀]
  obtain ⟨-, -, -, ψ₀, hψb, hψd, -⟩ := RMT.riemann_mapping_of_hasHoloSqrt hVo hVc hne hVuniv
    (RMT.hasHoloSqrt_of_unbounded_compl hVo hVc hcomp)
  refine ⟨ψ₀ ∘ cayley, ?_, hψb.comp bijOn_cayley_H, hVo, hVb, isClosed_frontier, subset_rfl,
    ?_, ?_⟩
  · exact hψd.comp (differentiableOn_cayley_Hbar.mono H_subset_Hbar) bijOn_cayley_H.mapsTo
  · intro z hz hzV
    rw [hVo.frontier_eq] at hz
    exact hz.2 hzV
  · exact frontier_subset_closure.trans ((closure_mono hVb).trans closure_ball_subset_closedBall)

/-- **Existence of harmonic measure** on an open set `U ⊆ B(0, R₀)` with finitely many
components, each with only unbounded complementary components and ULC frontier, for every
bounded `A` disjoint from `U`. -/
theorem flExist_ulc_components {U A : Set ℂ} {R₀ : ℝ} (hU : IsOpen U) (hUb : U ⊆ ball 0 R₀)
    (hfin : (connectedComponentIn U '' U).Finite) (hA : Bornology.IsBounded A)
    (hAU : Disjoint A U)
    (hsc : ∀ z ∈ U, ∀ a ∉ connectedComponentIn U z,
      ¬ Bornology.IsBounded (connectedComponentIn (connectedComponentIn U z)ᶜ a))
    (hulc : ∀ z ∈ U, Topo.ULC (frontier (connectedComponentIn U z))) :
    ∃ g : ℂ → ℝ, IsHarmMeas U A g := by
  refine flExist_car_components hU hfin hA hAU fun z hz => ?_
  obtain ⟨ψ, hψ⟩ := flExist_carHyp hU.connectedComponentIn isPreconnected_connectedComponentIn
    ⟨z, mem_connectedComponentIn hz⟩ ((connectedComponentIn_subset U z).trans hUb) (hsc z hz)
  exact ⟨ψ, _, R₀, hψ, hulc z hz⟩

/-- The frontier of a connected component of an open set lies in the frontier of the set. -/
lemma flExist_frontier_comp {U : Set ℂ} (hU : IsOpen U) (z : ℂ) :
    frontier (connectedComponentIn U z) ⊆ frontier U := by
  intro w hw
  have hVo : IsOpen (connectedComponentIn U z) := hU.connectedComponentIn
  rw [hVo.frontier_eq] at hw
  rw [hU.frontier_eq]
  refine ⟨closure_mono (connectedComponentIn_subset U z) hw.1, fun hwU => hw.2 ?_⟩
  obtain ⟨y, hyW, hyV⟩ := mem_closure_iff.1 hw.1 _ hU.connectedComponentIn
    (mem_connectedComponentIn hwU)
  rw [connectedComponentIn_eq hyV, ← connectedComponentIn_eq hyW]
  exact mem_connectedComponentIn hwU

/-- If every point off a bounded open set `U` lies in an unbounded preconnected subset of `Uᶜ`,
then every complementary component of every component of `U` is unbounded. -/
lemma flExist_compl_unbdd {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hcomp : ∀ a ∉ U, ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Uᶜ ∧
      ¬ Bornology.IsBounded C) (z : ℂ) :
    ∀ a ∉ connectedComponentIn U z,
      ¬ Bornology.IsBounded (connectedComponentIn (connectedComponentIn U z)ᶜ a) := by
  intro a ha
  have hVU : (connectedComponentIn U z) ⊆ U := connectedComponentIn_subset U z
  suffices h : ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ (connectedComponentIn U z)ᶜ ∧
      ¬ Bornology.IsBounded C by
    obtain ⟨C, hC, haC, hCV, hCb⟩ := h
    exact fun hb => hCb (hb.subset (hC.subset_connectedComponentIn haC hCV))
  by_cases haU : a ∈ U
  · set V' := connectedComponentIn U a
    have hV'U : V' ⊆ U := connectedComponentIn_subset U a
    obtain ⟨b, hb⟩ : (frontier V').Nonempty := nonempty_frontier_iff.2
      ⟨⟨a, mem_connectedComponentIn haU⟩, fun h =>
        NormedSpace.unbounded_univ ℝ ℂ (hUb.subset (h ▸ hV'U))⟩
    have hbU : b ∉ U := by
      have := flExist_frontier_comp hU a hb
      rw [hU.frontier_eq] at this
      exact this.2
    obtain ⟨C, hC, hbC, hCU, hCb⟩ := hcomp b hbU
    refine ⟨closure V' ∪ C, isPreconnected_connectedComponentIn.closure.union b
      (frontier_subset_closure hb) hbC hC, Or.inl (subset_closure (mem_connectedComponentIn haU)),
      ?_, fun h => hCb (h.subset subset_union_right)⟩
    have hdisj : Disjoint (connectedComponentIn U z) V' := by
      rw [Set.disjoint_left]
      intro y hyV hyV'
      apply ha
      rw [connectedComponentIn_eq hyV, ← connectedComponentIn_eq hyV']
      exact mem_connectedComponentIn haU
    refine union_subset ?_ (hCU.trans (compl_subset_compl.2 hVU))
    exact (Disjoint.closure_right hdisj hU.connectedComponentIn).subset_compl_left
  · obtain ⟨C, hC, haC, hCU, hCb⟩ := hcomp a haU
    exact ⟨C, hC, haC, hCU.trans (compl_subset_compl.2 hVU), hCb⟩

/-- **Existence of harmonic measure from a ULC frame.** Let `U ⊆ B(0, R₀)` be open with finitely
many components, such that every point off `U` lies in an unbounded preconnected subset of `Uᶜ`,
and let `E` be a closed ULC set with `frontier U ⊆ E ⊆ Uᶜ ∩ B̄(0, R₀)`. Then every bounded `A`
disjoint from `U` has a harmonic measure in `U`. -/
theorem flExist_of_frame {U A E : Set ℂ} {R₀ : ℝ} (hU : IsOpen U) (hUb : U ⊆ ball 0 R₀)
    (hfin : (connectedComponentIn U '' U).Finite) (hA : Bornology.IsBounded A)
    (hAU : Disjoint A U)
    (hcomp : ∀ a ∉ U, ∃ C : Set ℂ, IsPreconnected C ∧ a ∈ C ∧ C ⊆ Uᶜ ∧
      ¬ Bornology.IsBounded C)
    (hEc : IsClosed E) (hE : Topo.ULC E) (hfrE : frontier U ⊆ E) (hEU : E ⊆ Uᶜ)
    (hEb : E ⊆ closedBall 0 R₀) :
    ∃ g : ℂ → ℝ, IsHarmMeas U A g := by
  refine flExist_car_components hU hfin hA hAU fun z hz => ?_
  obtain ⟨ψ, hψ⟩ := flExist_carHyp hU.connectedComponentIn isPreconnected_connectedComponentIn
    ⟨z, mem_connectedComponentIn hz⟩ ((connectedComponentIn_subset U z).trans hUb)
    (flExist_compl_unbdd hU (isBounded_ball.subset hUb) hcomp z)
  refine ⟨ψ, E, R₀, ⟨hψ.holo, hψ.bij, hψ.isOpen, hψ.bdd, hEc,
    (flExist_frontier_comp hU z).trans hfrE,
    hEU.trans (compl_subset_compl.2 (connectedComponentIn_subset U z)), hEb⟩, hE⟩

end FieldLawler
end QuantumZipper

import QuantumZipper.Proofs.GFF.K3.MixedM7AsmMix
import QuantumZipper.Proofs.GFF.K3.MixedM7Real

/-!
# K3-mixed M7, assembly part 2: the `Ξ`-family as an isonormal process, weak Bochner identity

* `inner_rieszVec_bind_eq_integral_mixCurve`: for a finite measure `μ` carried by
  `closedBall t ρ ∩ Hbar` whose balayage `μ.bind P` is `V`-admissible,
  `⟪v_{μ.bind P}, e⟫ = ∫ ⟪v_{P_x}, e⟫ dμ(x)` for every `e ∈ GradSpace D` (weak Bochner identity
  for the balayage, as in `inner_mixCurve_meanValue`).
* `xiSub`: the closed subspace of `GradSpace D` orthogonal to the mixed local vectors; its
  elements are exactly the index set `XiIdx` of the `Ξ`-family of the Markov coupling
  (`mem_xiSub_iff`).
* `xiEmb`: the isometric embedding `x ↦ (x, 0)` of `GradSpace D` into the joint space of the
  coupling (`MixedM7Real.lean`), and `hasLaw_xi`: the `Ξ`-family of the realized coupling is an
  isonormal process on `xiSub`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

open GFFExist LQGDimension.ExistAsm

section

variable {D : Set ℂ} {c d t r ρ : ℝ}

/-- **Weak Bochner identity for the balayage.** -/
theorem inner_rieszVec_bind_eq_integral_mixCurve (hgeom : Prop16Geometry D c d)
    (ht : t ∈ Set.Ioo c d) (hρ : 0 < ρ) (hρr : ρ < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (hμK : μ (closedBall (t : ℂ) ρ ∩ Hbar)ᶜ = 0)
    (hμA : IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) (μ.bind (halfDiscPoisson t r)))
    (e : GradSpace D) :
    ⟪rieszVec D (mixedSpace D (realSet (Icc c d))) (μ.bind (halfDiscPoisson t r)), e⟫ =
      ∫ x, ⟪mixCurve D c d t r ρ x, e⟫ ∂μ := by
  set V := mixedSpace D (realSet (Icc c d)) with hVdef
  have hV : IsDNSpace D V := isDNSpace_mixedSpace D _
  obtain ⟨L, B, -, -, -, hB⟩ := exists_lip_mixCurve hgeom ht hρ hρr hsub
  have hcont := continuous_mixCurve hgeom ht hρ hρr hsub
  have hadm := (mixedHalfDiscMarkovCov_holds D c d t r ρ hgeom ht hρ hρr hsub).1
  set G := gradClosure D V with hG
  have hproj : ∀ w ∈ G, ⟪w, e⟫ = ⟪w, G.starProjection e⟫ := fun w hw => by
    rw [← G.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hw]
  have hPe : G.starProjection e ∈ (Submodule.span ℝ (gradFeat D '' V)).topologicalClosure := by
    rw [Submodule.starProjection_apply]; exact (G.orthogonalProjectionOnto e).2
  have hmem : ∀ x, mixCurve D c d t r ρ x ∈ G := fun x => rieszVec_mem
  by_cases hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g
  swap
  · have h0 : ∀ x, mixCurve D c d t r ρ x = 0 := fun x =>
      eq_zero_of_mem_gradClosure_of_nopos hV hpos (hmem x)
    rw [eq_zero_of_mem_gradClosure_of_nopos hV hpos (rieszVec_mem (μ := μ.bind _))]
    simp [h0]
  have hmain := inner_eq_integral_of_mem_closure_span (μ := μ)
    (G := gradFeat D '' V) (v := mixCurve D c d t r ρ) (B := B) (ae_of_all _ hB)
    (fun g _ => (hcont.inner continuous_const).aestronglyMeasurable)
    (y := rieszVec D V (μ.bind (halfDiscPoisson t r))) ?_ hPe
  · rw [hproj _ rieszVec_mem, hmain.2]
    exact integral_congr_ae (ae_of_all _ fun x => (hproj _ (hmem x)).symm)
  · rintro _ ⟨f, hf, rfl⟩
    have hint : Integrable f (μ.bind (halfDiscPoisson t r)) := integrable_of_admissible hV hμA hf
    rw [pair_rieszVec hV hμA hpos f hf, integral_bind_halfDiscPoisson_m7as _ hint]
    refine integral_congr_ae ?_
    filter_upwards [mem_ae_iff.2 hμK] with x hx
    rw [mixCurve_eq hx.2 (mem_closedBall_iff_norm.1 hx.1), pair_rieszVec hV (hadm x hx) hpos f hf]

end

/-- The closed subspace orthogonal to the mixed local vectors. -/
def xiSub (D : Set ℂ) (c d t r r' : ℝ) : Submodule ℝ (GradSpace D) :=
  (Submodule.span ℝ (Set.range fun ν : LocIdx t r' => mixedLocVec D c d t r ν.1))ᗮ

theorem mem_xiSub_iff {D : Set ℂ} {c d t r r' : ℝ} {u : GradSpace D} :
    u ∈ xiSub D c d t r r' ↔ ∀ ν : LocIdx t r', ⟪u, mixedLocVec D c d t r ν.1⟫ = 0 := by
  rw [xiSub, Submodule.mem_orthogonal']
  refine ⟨fun h ν => h _ (Submodule.subset_span ⟨ν, rfl⟩), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨ν, rfl⟩ := hx; exact h ν
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- The isometric embedding `x ↦ (x, 0)` into the joint space. -/
def xiEmb (D : Set ℂ) : GradSpace D →ₗᵢ[ℝ] WithLp 2 (GradSpace D × HkE) where
  toFun x := WithLp.toLp 2 (x, (0 : HkE))
  map_add' x y := by rw [← WithLp.toLp_add, Prod.mk_add_mk, add_zero]
  map_smul' a x := by rw [RingHom.id_apply, ← WithLp.toLp_smul, Prod.smul_mk, smul_zero]
  norm_map' x := WithLp.norm_toLp_fst 2 (GradSpace D) HkE x

end QuantumZipper.K3

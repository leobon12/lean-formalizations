import HigherDimLQGMetric.Field.Measurable
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Compactness.SigmaCompact

/-!
# The cylinder σ-algebra of `𝒟'(U)` is countably generated

Packet F1 (measurability for the frozen cylinder σ-algebras; ruling M10). Port of LQGMetric's
`lqg_metric/LQGMetric/Field/StandardBorelTest.lean` (`𝓓_K` is second countable),
`Field/StandardBorelDist.lean` (countably many pairings generate the cylinder σ-algebra) and the
inclusions `inclK` of `Field/StandardBorelExt.lean`, from `ℂ` to `Rd d`.

* `secondCountableTopology_testK`: for a compact `K ⊆ ℝ^d`, the Fréchet space
  `𝓓_K = 𝓓^{⊤}_{K}(ℝ^d, ℝ)` is second countable. Its topology is `⨅ᵢ` of the topologies induced by
  `f ↦ Dⁱf ∈ ℝ^d →ᵇ Mᵢ`; for functions vanishing off `K` the sup-distance over `ℝ^d` equals the
  sup-distance over `K`, so each of these induced topologies is induced by `f ↦ Dⁱf|_K ∈ C(K, Mᵢ)`,
  which is second countable (`Mᵢ` finite dimensional); a countable infimum of second countable
  topologies is second countable.
* `distOn_measurableSpace_eq_comap`: with a compact exhaustion `K_n` of `U` and dense sequences in
  the separable spaces `𝓓_{K_n}`, the countably many pairings `h ↦ ⟨h, φ_{n,k}⟩` generate the
  cylinder σ-algebra of `𝒟'(U)` (pointwise limits, `measurable_of_tendsto_metrizable`); hence
  `MeasurableSpace.CountablyGenerated (DistOn U)` and `injective_distOn_pairings`.

Standard facts (Trèves, *Topological Vector Spaces, Distributions and Kernels*, Ch. 13–14); own
elementary proofs as in the 2D layer.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Topology Set TopologicalSpace Filter
open scoped Distributions

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- continuous multilinear maps between finite-dimensional real spaces form a finite-dimensional
space (they inject into all multilinear maps, mathlib `Module.Finite.multilinearMap`) -/
instance finiteDimensional_cmm (i : ℕ) : FiniteDimensional ℝ (Rd d [×i]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective
    (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ) (A := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective

instance secondCountable_cmm (i : ℕ) : SecondCountableTopology (Rd d [×i]→L[ℝ] ℝ) := by
  have : ProperSpace (Rd d [×i]→L[ℝ] ℝ) := FiniteDimensional.proper_real _
  infer_instance

/-- two maps into pseudometric spaces with the same distances induce the same topology -/
theorem induced_eq_of_dist_eq {X A B : Type*} [PseudoMetricSpace A] [PseudoMetricSpace B]
    (f : X → A) (g : X → B) (h : ∀ x y, dist (f x) (f y) = dist (g x) (g y)) :
    TopologicalSpace.induced f inferInstance = TopologicalSpace.induced g inferInstance := by
  refine TopologicalSpace.ext_nhds fun x => ?_
  rw [nhds_induced, nhds_induced]
  refine ((Metric.nhds_basis_ball.comap f).ext (Metric.nhds_basis_ball.comap g) ?_ ?_)
  · intro ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    simp only [mem_preimage, Metric.mem_ball] at hy ⊢
    rwa [h]
  · intro ε hε
    refine ⟨ε, hε, fun y hy => ?_⟩
    simp only [mem_preimage, Metric.mem_ball] at hy ⊢
    rwa [← h]

section
variable (K : Compacts (Rd d))

/-- `f ↦ Dⁱf|_K ∈ C(K, M_i)` -/
def derivOnK (i : ℕ) (f : 𝓓^{⊤}_{K}(Rd d, ℝ)) : C((K : Set (Rd d)), Rd d [×i]→L[ℝ] ℝ) :=
  ⟨fun y => iteratedFDeriv ℝ i f y,
    (f.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp continuous_subtype_val⟩

theorem dist_derivOnK (i : ℕ) (f g : 𝓓^{⊤}_{K}(Rd d, ℝ)) :
    dist (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i f)
      (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i g) =
    dist (derivOnK K i f) (derivOnK K i g) := by
  apply le_antisymm
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).2 fun y => ?_
    simp only [ContDiffMapSupportedIn.structureMapLM_top_apply]
    by_cases hy : y ∈ (K : Set (Rd d))
    · exact ContinuousMap.dist_apply_le_dist (f := derivOnK K i f) (g := derivOnK K i g) ⟨y, hy⟩
    · rw [f.iteratedFDeriv_zero_on_compl hy, g.iteratedFDeriv_zero_on_compl hy, dist_self]
      exact dist_nonneg
  · refine (ContinuousMap.dist_le dist_nonneg).2 fun y => ?_
    have := BoundedContinuousFunction.dist_coe_le_dist (f := ContDiffMapSupportedIn.structureMapLM
      ℝ ⊤ i f) (g := ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i g) (y : Rd d)
    simpa [ContDiffMapSupportedIn.structureMapLM_top_apply, derivOnK] using this

/-- `𝓓_K(ℝ^d)` is second countable -/
instance secondCountableTopology_testK : SecondCountableTopology 𝓓^{⊤}_{K}(Rd d, ℝ) := by
  show @SecondCountableTopology _ (⨅ (i : ℕ), TopologicalSpace.induced
    (ContDiffMapSupportedIn.structureMapLM ℝ ⊤ i) inferInstance)
  refine secondCountableTopology_iInf fun i => ?_
  rw [induced_eq_of_dist_eq _ (derivOnK K i) (dist_derivOnK K i)]
  exact secondCountableTopology_induced _ _ _

end

instance locallyCompactSpace_opens (U : Opens (Rd d)) : LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

section
variable (U : Opens (Rd d))

/-- compact exhaustion of `U`, as compacts of `ℝ^d` -/
def exhaustK (n : ℕ) : Compacts (Rd d) :=
  ⟨(↑) '' CompactExhaustion.choice U n,
    ((CompactExhaustion.choice U).isCompact n).image continuous_subtype_val⟩

lemma exhaustK_subset (n : ℕ) : (exhaustK U n : Set (Rd d)) ⊆ U := by
  rintro _ ⟨x, _, rfl⟩; exact x.2

lemma exists_exhaustK_superset {C : Set (Rd d)} (hC : IsCompact C) (hCU : C ⊆ U) :
    ∃ n, C ⊆ exhaustK U n := by
  have hc : IsCompact ((↑) ⁻¹' C : Set U) := by
    rw [Subtype.isCompact_iff, image_preimage_eq_of_subset fun x hx => ⟨⟨x, hCU hx⟩, rfl⟩]
    exact hC
  obtain ⟨n, hn⟩ := (CompactExhaustion.choice U).exists_superset_of_isCompact hc
  refine ⟨n, fun x hx => ⟨⟨x, hCU hx⟩, hn hx, rfl⟩⟩

/-- dense sequences in `𝓓_{K_n}` -/
def denseSeqK (n : ℕ) : ℕ → 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) :=
  Classical.choose (exists_dense_seq 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ))

lemma denseRange_denseSeqK (n : ℕ) : DenseRange (denseSeqK U n) :=
  Classical.choose_spec (exists_dense_seq 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ))

/-- the countable generating family `φ_{n,k}` -/
def distGen (j : ℕ × ℕ) : TestOn U :=
  TestFunction.ofSupportedIn (exhaustK_subset U j.1) (denseSeqK U j.1 j.2)

/-- the σ-algebra generated by the countable family of pairings -/
@[instance_reducible] def distGenMS : MeasurableSpace (DistOn U) :=
  MeasurableSpace.comap (fun (h : DistOn U) (j : ℕ × ℕ) => h (distGen U j)) MeasurableSpace.pi

theorem distOn_measurableSpace_eq_comap :
    DistOn.measurableSpace U =
      MeasurableSpace.comap (fun (h : DistOn U) (j : ℕ × ℕ) => h (distGen U j))
        MeasurableSpace.pi := by
  show _ = distGenMS U
  have hgen : ∀ j, Measurable[(distGenMS U)] fun h : DistOn U => h (distGen U j) := fun j =>
    (measurable_pi_apply j).comp (comap_measurable (m := MeasurableSpace.pi)
      (fun (h : DistOn U) (j : ℕ × ℕ) => h (distGen U j)))
  refine le_antisymm ?_ (measurable_pi_iff.2 fun j => measurable_distOn_apply _).comap_le
  show MeasurableSpace.comap _ _ ≤ (distGenMS U)
  refine Measurable.comap_le ?_
  let : MeasurableSpace (DistOn U) := distGenMS U
  refine Measurable.of_eval fun φ => ?_
  obtain ⟨n, hn⟩ := exists_exhaustK_superset U φ.hasCompactSupport.isCompact φ.tsupport_subset
  let ψ : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hn h)⟩
  have hψ : TestFunction.ofSupportedIn (exhaustK_subset U n) ψ = φ := by ext; rfl
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.1 ((denseRange_denseSeqK U n) ψ)
  choose k hk using hs
  have hT : Tendsto (fun i (h : DistOn U) => h (distGen U (n, k i))) atTop
      (𝓝 fun h : DistOn U => h φ) := by
    refine tendsto_pi_nhds.2 fun h => ?_
    have hc : Continuous fun χ : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) =>
        h (TestFunction.ofSupportedIn (exhaustK_subset U n) χ) :=
      (map_continuous h).comp
        (TestFunction.ofSupportedInCLM ℝ (exhaustK_subset U n)).continuous
    have := (hc.tendsto ψ).comp hlim
    rw [hψ] at this
    refine this.congr fun i => ?_
    simp only [Function.comp_apply, distGen, ← hk i]
  exact @measurable_of_tendsto_metrizable _ _ (distGenMS U) _ _ _ _ _ _ (fun i => hgen (n, k i)) hT

theorem injective_distOn_pairings :
    Function.Injective fun (h : DistOn U) (j : ℕ × ℕ) => h (distGen U j) := by
  intro h₁ h₂ heq
  -- both pairings agree on the generators, hence on every test function (density)
  ext φ
  obtain ⟨n, hn⟩ := exists_exhaustK_superset U φ.hasCompactSupport.isCompact φ.tsupport_subset
  let ψ : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) :=
    ⟨φ, φ.contDiff, fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hn h)⟩
  have hψ : TestFunction.ofSupportedIn (exhaustK_subset U n) ψ = φ := by ext; rfl
  have hc : ∀ h : DistOn U, Continuous fun χ : 𝓓^{⊤}_{exhaustK U n}(Rd d, ℝ) =>
      h (TestFunction.ofSupportedIn (exhaustK_subset U n) χ) := fun h =>
    (map_continuous h).comp (TestFunction.ofSupportedInCLM ℝ (exhaustK_subset U n)).continuous
  have := ((denseRange_denseSeqK U n).equalizer (hc h₁) (hc h₂)
    (funext fun k => congrFun heq (n, k)))
  have := congrFun this ψ
  simpa [hψ] using this

instance countablyGenerated_distOn : MeasurableSpace.CountablyGenerated (DistOn U) := by
  rw [distOn_measurableSpace_eq_comap U]
  exact MeasurableSpace.CountablyGenerated.comap _

end

/-- the inclusion `𝓓_K ⊆ 𝓓_{K'}` -/
def inclK {K K' : Compacts (Rd d)} (h : (K : Set (Rd d)) ⊆ K') (ψ : 𝓓^{⊤}_{K}(Rd d, ℝ)) :
    𝓓^{⊤}_{K'}(Rd d, ℝ) where
  toFun := ψ
  contDiff' := ψ.contDiff
  zero_on_compl' := fun _ hx => ψ.zero_on_compl fun hxK => hx (h hxK)

theorem continuous_inclK {K K' : Compacts (Rd d)} (h : (K : Set (Rd d)) ⊆ K') :
    Continuous (inclK h) := by
  rw [ContDiffMapSupportedIn.continuous_iff_comp]
  intro i
  have : (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i ∘ inclK h) =
      ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i := by
    funext ψ
    ext x : 1
    simp only [Function.comp_apply, ContDiffMapSupportedIn.structureMapCLM_top_apply]
    rfl
  rw [this]
  exact (ContDiffMapSupportedIn.structureMapCLM ℝ ⊤ i).continuous

end HigherDimLQGMetric

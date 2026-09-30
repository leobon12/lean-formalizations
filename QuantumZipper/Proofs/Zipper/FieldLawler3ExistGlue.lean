import QuantumZipper.Proofs.Thm18.LWHarmCar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-EXIST: harmonic measure of a finite disjoint union of open sets (gluing)

Task FL3-EXIST (Track A, towards `FieldLawler.FLImageSumBoundStmt`). `fl3_lemma33` takes the
harmonic measures `IsHarmMeas (D \ arcs) arcs h` as inputs; the Loewner domains `D \ arcs` are
not connected, so the Carathéodory existence theorem `lwHarm_exists_car` (one conformal
parametrisation `ψ : ℍ → D`) does not apply to them directly. Here:

* `flExist_glue`: harmonic measures `IsHarmMeas (V i) A (h i)` on finitely many pairwise disjoint
  open sets glue to one on `⋃ i, V i` (the clauses of `IsHarmMeas` are local, and the frontier of
  each `V i` lies in the frontier of the union, so the boundary conditions transfer).
* `flExist_components`: the same for an open set with finitely many connected components.
* `flExist_const_one`: on a bounded open `V` whose frontier lies in `closure A`, `h ≡ 1` is a
  harmonic measure of `A` (the case excluded by the side condition of `lwHarm_exists_car`).
* `flExist_car_components`: existence on an open set with finitely many components, each
  of which carries a Carathéodory parametrisation `Car.CarHyp` with ULC boundary set.

**Source.** For each piece this is the Dirichlet characterization of harmonic measure
(Garnett–Marshall, *Harmonic Measure*, Ch. III, PDF p. 91); the gluing over components is the
standard remark that the Dirichlet problem on an open set is solved component by component.
Own elementary argument (bookkeeping of the filter clauses, under 150 lines).
-/

noncomputable section

open Set Filter Metric Complex Function
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar
open QuantumZipper.CA

section Glue

variable {ι : Type*} {V : ι → Set ℂ}

/-- The frontier of one of pairwise disjoint open sets lies in the frontier of their union. -/
lemma flExist_frontier_sub (hVo : ∀ i, IsOpen (V i)) (hdisj : Pairwise (Disjoint on V)) (i : ι) :
    frontier (V i) ⊆ frontier (⋃ j, V j) := by
  intro z hz
  rw [(hVo i).frontier_eq] at hz
  rw [(isOpen_iUnion hVo).frontier_eq]
  refine ⟨closure_mono (subset_iUnion V i) hz.1, fun hzU => ?_⟩
  obtain ⟨j, hj⟩ := mem_iUnion.1 hzU
  by_cases hij : j = i
  · subst hij; exact hz.2 hj
  · exact (Disjoint.closure_right ((hdisj hij)) (hVo j)).ne_of_mem hj hz.1 rfl

/-- The glued function: `h i` on `V i`, `0` off the union. -/
def flExistGlue (V : ι → Set ℂ) (h : ι → ℂ → ℝ) (z : ℂ) : ℝ :=
  open Classical in
  if hz : ∃ i, z ∈ V i then h hz.choose z else 0

lemma flExistGlue_eq (hdisj : Pairwise (Disjoint on V)) (h : ι → ℂ → ℝ) {i : ι} {z : ℂ}
    (hz : z ∈ V i) : flExistGlue V h z = h i z := by
  have hex : ∃ j, z ∈ V j := ⟨i, hz⟩
  rw [flExistGlue, dif_pos hex]
  by_cases hij : hex.choose = i
  · rw [hij]
  · exact absurd (hdisj hij) (not_disjoint_iff.2 ⟨z, hex.choose_spec, hz⟩)

lemma flExistGlue_tendsto [Finite ι] (hdisj : Pairwise (Disjoint on V)) (h : ι → ℂ → ℝ)
    {l : Filter ℂ} {c : ℝ} (hl : ∀ i, Tendsto (h i) (l ⊓ 𝓟 (V i)) (𝓝 c)) :
    Tendsto (flExistGlue V h) (l ⊓ 𝓟 (⋃ i, V i)) (𝓝 c) := by
  intro s hs
  have hi : ∀ i, {z | z ∈ V i → h i z ∈ s} ∈ l := fun i => mem_inf_principal.1 (hl i hs)
  rw [mem_map, mem_inf_principal]
  refine mem_of_superset (iInter_mem.2 hi) fun z hz hzU => ?_
  obtain ⟨i, hzi⟩ := mem_iUnion.1 hzU
  show flExistGlue V h z ∈ s
  rw [flExistGlue_eq hdisj h hzi]
  exact mem_iInter.1 hz i hzi

/-- **Gluing.** Harmonic measures of `A` on finitely many pairwise disjoint open sets glue to a
harmonic measure of `A` on their union. -/
theorem flExist_glue [Finite ι] (hVo : ∀ i, IsOpen (V i)) (hdisj : Pairwise (Disjoint on V))
    {A : Set ℂ} {h : ι → ℂ → ℝ} (hh : ∀ i, IsHarmMeas (V i) A (h i)) :
    IsHarmMeas (⋃ i, V i) A (flExistGlue V h) := by
  have hfr := flExist_frontier_sub hVo hdisj
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
    have heq : flExistGlue V h =ᶠ[𝓝 z] h i :=
      Filter.mem_of_superset ((hVo i).mem_nhds hzi) fun w hw => flExistGlue_eq hdisj h hw
    exact (InnerProductSpace.harmonicAt_congr_nhds heq).2 ((hh i).harm z hzi)
  · intro z hz
    obtain ⟨i, hzi⟩ := mem_iUnion.1 hz
    rw [flExistGlue_eq hdisj h hzi]
    exact (hh i).mem01 z hzi
  · intro x₀ hA hcl
    refine flExistGlue_tendsto hdisj h fun i => (hh i).one x₀ hA fun hmem => hcl ?_
    exact closure_mono (sdiff_subset_sdiff_left (hfr i)) hmem
  · intro x₀ hx₀ hcl
    refine flExistGlue_tendsto hdisj h fun i => ?_
    by_cases hfi : x₀ ∈ frontier (V i)
    · exact (hh i).zero x₀ hfi hcl
    · have hnot : x₀ ∉ closure (V i) := by
        intro hc
        refine hfi ⟨hc, ?_⟩
        rw [(hVo i).interior_eq]
        intro hv
        rw [(isOpen_iUnion hVo).frontier_eq] at hx₀
        exact hx₀.2 (mem_iUnion.2 ⟨i, hv⟩)
      have hbot : 𝓝 x₀ ⊓ 𝓟 (V i) = ⊥ := by
        rw [← nhdsWithin, ← not_neBot, ← mem_closure_iff_nhdsWithin_neBot]
        exact hnot
      show Tendsto (h i) (𝓝 x₀ ⊓ 𝓟 (V i)) _
      rw [hbot]
      exact tendsto_bot
  · intro hAb
    exact flExistGlue_tendsto hdisj h fun i => (hh i).infty hAb

end Glue

/-- **Gluing over components.** If an open set `U ⊆ ℂ` has finitely many connected components
and each carries a harmonic measure of `A`, then `U` does. -/
theorem flExist_components {U A : Set ℂ} (hU : IsOpen U)
    (hfin : (connectedComponentIn U '' U).Finite)
    (hc : ∀ z ∈ U, ∃ h : ℂ → ℝ, IsHarmMeas (connectedComponentIn U z) A h) :
    ∃ g : ℂ → ℝ, IsHarmMeas U A g := by
  set S := connectedComponentIn U '' U with hS
  have : Finite S := hfin.to_subtype
  have hmem : ∀ V : S, ∃ z ∈ U, connectedComponentIn U z = (V : Set ℂ) := fun V => V.2
  choose z hzU hzV using hmem
  have hVo : ∀ V : S, IsOpen (V : Set ℂ) := fun V => by
    rw [← hzV V]; exact hU.connectedComponentIn
  have hdisj : Pairwise (Disjoint on fun V : S => (V : Set ℂ)) := by
    intro V W hVW
    show Disjoint (V : Set ℂ) (W : Set ℂ)
    rw [← hzV V, ← hzV W]
    rw [Set.disjoint_left]
    intro y hyV hyW
    apply hVW
    apply Subtype.ext
    rw [← hzV V, ← hzV W, connectedComponentIn_eq hyV, connectedComponentIn_eq hyW]
  have hUeq : (⋃ V : S, (V : Set ℂ)) = U := by
    apply Subset.antisymm
    · refine iUnion_subset fun V => ?_
      rw [← hzV V]; exact connectedComponentIn_subset U _
    · intro y hy
      exact mem_iUnion.2 ⟨⟨_, y, hy, rfl⟩, mem_connectedComponentIn hy⟩
  have hh : ∀ V : S, ∃ h : ℂ → ℝ, IsHarmMeas (V : Set ℂ) A h := fun V => by
    rw [← hzV V]; exact hc _ (hzU V)
  choose h hh using hh
  exact ⟨_, hUeq ▸ flExist_glue hVo hdisj hh⟩

/-- On a bounded open set whose frontier lies in `closure A`, the constant `1` is a harmonic
measure of `A`. -/
lemma flExist_const_one {V A : Set ℂ} (hVb : Bornology.IsBounded V)
    (hfr : frontier V ⊆ closure A) : IsHarmMeas V A (fun _ => 1) := by
  refine ⟨fun z _ => InnerProductSpace.harmonicAt_const _, fun _ _ => ⟨zero_le_one, le_rfl⟩,
    fun _ _ _ => tendsto_const_nhds, fun x₀ hx hA => absurd (hfr hx) hA, fun _ => ?_⟩
  have hbot : Bornology.cobounded ℂ ⊓ 𝓟 V = ⊥ := by
    rw [inf_principal_eq_bot]
    exact Bornology.isBounded_def.1 hVb
  rw [hbot]
  exact tendsto_bot

/-- **Existence on Carathéodory components.** Let `U` be open with finitely many components,
`A` bounded and disjoint from `U`, and let every component carry a Carathéodory parametrisation
`ψ : ℍ → V` with ULC boundary set (`Car.CarHyp`). Then `U` carries a harmonic measure of `A`. -/
theorem flExist_car_components {U A : Set ℂ} (hU : IsOpen U)
    (hfin : (connectedComponentIn U '' U).Finite) (hA : Bornology.IsBounded A)
    (hAU : Disjoint A U)
    (hcar : ∀ z ∈ U, ∃ (ψ : ℂ → ℂ) (E : Set ℂ) (R₀ : ℝ),
      Car.CarHyp ψ (connectedComponentIn U z) E R₀ ∧ Topo.ULC E) :
    ∃ g : ℂ → ℝ, IsHarmMeas U A g := by
  refine flExist_components hU hfin fun z hz => ?_
  obtain ⟨ψ, E, R₀, hC, hE⟩ := hcar z hz
  have hAV : Disjoint A (connectedComponentIn U z) :=
    hAU.mono_right (connectedComponentIn_subset U z)
  by_cases hq : ∃ q ∈ frontier (connectedComponentIn U z), q ∉ closure A
  · exact lwHarm_exists_car hC hE hA hAV hq
  · push Not at hq
    exact ⟨_, flExist_const_one ((Metric.isBounded_ball).subset hC.bdd) hq⟩

end FieldLawler
end QuantumZipper

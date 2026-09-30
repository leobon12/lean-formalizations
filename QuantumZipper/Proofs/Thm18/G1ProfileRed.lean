import QuantumZipper.Proofs.Thm18.G1RCProfile
import QuantumZipper.Proofs.Thm18.G1PkgPath
import QuantumZipper.Proofs.Probability.BrownianPathMeas
import QuantumZipper.Proofs.RS.RohdeSchrammSimple

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PROFILE: from the path law back to deterministic chords

`G1RC.G1ProfileStmt` is stated `∀ᵐ a ∂(P.map (pathOf B))` over the path space `ℝ≥0 → ℝ` with the
product σ-algebra, and the only access to `Ψ left a` is `G1PsiSel`'s clause for *continuous* paths
with a *simple-chord* trace. Continuity is not a measurable property of paths (in fact
`∀ᵐ a ∂(P.map (pathOf B)), Continuous a` is false: `G1PathNoGo.lean`), so the a.e. statement
cannot be obtained by conditioning on continuity directly.

This file removes that obstruction for every predicate that depends on the path only through
the selected maps `Ψ left a`:

* `exists_countable_dep_of_measurable`: a measurable `f : (ι → ℝ) × Z → β` (β second countable
  and T1) depends on only countably many coordinates of its first argument
  (the countable-coordinates property of product σ-algebras; own elementary proof: the sets
  determined by countably many coordinates form a σ-algebra containing the generators).
* `ae_map_pathOf_of_chord`: given `G1RegPathChordStmt` (the trace of the continuous
  regularization `G1Pkg.pathReg a` is a simple chord for `P.map (pathOf B)`-a.e. path), every
  property of `(Ψ true a, Ψ false a)` that holds for all continuous simple-chord paths holds
  `P.map (pathOf B)`-a.e. Proof (own): `Ψ` only reads the path on a countable set `S`; a.e. path
  agrees with its regularization on `S` (Brownian paths are a.s. continuous and `pathReg` is the
  identity on continuous paths), so `Ψ left a = Ψ left (pathReg a)` with `pathReg a` continuous.
* `g1RegPathChordStmt : G1RegPathChordStmt` (proved): the regularized coordinate process
  `t, a ↦ pathReg a t` is a Brownian motion under `P.map (pathOf B)` (`isBrownianReal_regCoord`),
  so Rohde–Schramm (Ann. of Math. 161 (2005), Theorems 4.7 and 6.1; `RS.rohdeSchrammSimple`)
  applies on the path space itself.
* `g1ProfileStmt_of_det' : G1ProfileDetStmt → G1ProfileStmt`, where `G1ProfileDetStmt` is the
  same analytic statement for every continuous path whose trace is a simple chord
  (deterministic in the path, no a.e. over paths).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

/-! ## Countably many coordinates -/

/-- The σ-algebra of subsets of `(ι → ℝ) × Z` determined by countably many coordinates of the
first factor (and arbitrary dependence on the second). -/
@[instance_reducible]
def cdSpace (ι Z : Type*) : MeasurableSpace ((ι → ℝ) × Z) where
  MeasurableSet' A := ∃ S : Set ι, S.Countable ∧ ∀ p q : (ι → ℝ) × Z, p.2 = q.2 →
    (∀ i ∈ S, p.1 i = q.1 i) → (p ∈ A ↔ q ∈ A)
  measurableSet_empty := ⟨∅, Set.countable_empty, fun _ _ _ _ => by simp⟩
  measurableSet_compl := by
    rintro A ⟨S, hS, hdet⟩
    exact ⟨S, hS, fun p q h2 h1 => by rw [mem_compl_iff, mem_compl_iff, hdet p q h2 h1]⟩
  measurableSet_iUnion := by
    intro f hf
    choose S hS hdet using hf
    refine ⟨⋃ n, S n, Set.countable_iUnion hS, fun p q h2 h1 => ?_⟩
    simp only [mem_iUnion]
    exact exists_congr fun n => hdet n p q h2 fun i hi => h1 i (mem_iUnion.2 ⟨n, hi⟩)

theorem prod_le_cdSpace (ι Z : Type*) [MeasurableSpace Z] :
    (inferInstance : MeasurableSpace ((ι → ℝ) × Z)) ≤ cdSpace ι Z := by
  refine sup_le ?_ ?_
  · rw [MeasurableSpace.comap_le_iff_le_map]
    change (⨆ i, (inferInstance : MeasurableSpace ℝ).comap (fun b : ι → ℝ => b i)) ≤ _
    refine iSup_le fun i => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro s _
    exact ⟨{i}, Set.countable_singleton i, fun p q _ h1 => by
      show p.1 i ∈ s ↔ q.1 i ∈ s
      rw [h1 i rfl]⟩
  · rw [MeasurableSpace.comap_le_iff_le_map]
    intro s _
    exact ⟨∅, Set.countable_empty, fun p q h2 _ => by
      show p.2 ∈ s ↔ q.2 ∈ s
      rw [h2]⟩

/-- **Countable dependence.** A measurable map on `(ι → ℝ) × Z` (product σ-algebra) with values
in a second-countable T1 space depends on only countably many coordinates of the first factor.
Own elementary proof. -/
theorem exists_countable_dep_of_measurable {ι Z β : Type*} [MeasurableSpace Z]
    [TopologicalSpace β] [SecondCountableTopology β] [T1Space β] [MeasurableSpace β]
    [OpensMeasurableSpace β] {f : (ι → ℝ) × Z → β} (hf : Measurable f) :
    ∃ S : Set ι, S.Countable ∧
      ∀ a a' : ι → ℝ, (∀ i ∈ S, a i = a' i) → ∀ z, f (a, z) = f (a', z) := by
  obtain ⟨b, hbc, -, hb⟩ := TopologicalSpace.exists_countable_basis β
  have hmem : ∀ U : b, MeasurableSet[cdSpace ι Z] (f ⁻¹' (U : Set β)) := fun U =>
    prod_le_cdSpace ι Z _ (hf (hb.isOpen U.2).measurableSet)
  choose S hS hdet using hmem
  have : Countable b := hbc.to_subtype
  refine ⟨⋃ U, S U, Set.countable_iUnion hS, fun a a' haa z => ?_⟩
  by_contra hne
  obtain ⟨U, hUb, hxU, hUs⟩ := hb.exists_subset_of_mem_open (Set.mem_compl_singleton_iff.2 hne)
    isOpen_compl_singleton
  have h := hdet ⟨U, hUb⟩ (a, z) (a', z) rfl fun i hi => haa i (mem_iUnion.2 ⟨⟨U, hUb⟩, hi⟩)
  exact hUs (h.1 hxU) rfl

/-! ## Transfer from continuous simple chords to the path law -/

/-- **Regularized Rohde–Schramm on the path space.** For `0 < γ < 2` and a Brownian motion `B`,
the SLE_{γ²} trace driven by the continuous regularization `G1Pkg.pathReg a` of the path is a
simple chord for `P.map (pathOf B)`-a.e. path `a`. (Path-space form of Rohde–Schramm,
Theorems 4.7 and 6.1; the `Ω`-side statement is `RS.rohdeSchrammSimple`.) -/
def G1RegPathChordStmt : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ a ∂(P.map (pathOf B)), IsSimpleChord (pathTrace (γ ^ 2) (G1Pkg.pathReg a))

/-- **Transfer.** Any property of the pair of selected maps `(Ψ true a, Ψ false a)` that holds for
every continuous path with a simple-chord trace holds for `P.map (pathOf B)`-a.e. path. -/
theorem ae_map_pathOf_of_chord (hRS : G1RegPathChordStmt) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ}
    (hΨ : G1PsiSel γ Ψ) (Q : (Bool → ℂ → ℂ) → Prop)
    (hQ : ∀ a : ℝ≥0 → ℝ, Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) →
      Q fun left => Ψ left a) :
    ∀ᵐ a ∂(P.map (pathOf B)), Q fun left => Ψ left a := by
  obtain ⟨S₁, hS₁, hd₁⟩ := exists_countable_dep_of_measurable (hΨ.1 true)
  obtain ⟨S₀, hS₀, hd₀⟩ := exists_countable_dep_of_measurable (hΨ.1 false)
  have hmS : MeasurableSet {a : ℝ≥0 → ℝ | ∀ t ∈ S₁ ∪ S₀, a t = G1Pkg.pathReg a t} := by
    have : {a : ℝ≥0 → ℝ | ∀ t ∈ S₁ ∪ S₀, a t = G1Pkg.pathReg a t} =
        ⋂ t ∈ S₁ ∪ S₀, {a : ℝ≥0 → ℝ | a t = G1Pkg.pathReg a t} := by
      ext a; simp [mem_iInter]
    rw [this]
    exact MeasurableSet.biInter (hS₁.union hS₀) fun t _ => measurableSet_eq_fun
      (measurable_pi_apply t) ((measurable_pi_apply t).comp G1Pkg.pathReg_spec.1)
  have hreg : ∀ᵐ a ∂(P.map (pathOf B)), ∀ t ∈ S₁ ∪ S₀, a t = G1Pkg.pathReg a t := by
    refine (ae_map_iff (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB) hmS).2 ?_
    filter_upwards [hB.cont] with ω hω t _
    have hc : Continuous (pathOf B ω) := hω
    rw [G1Pkg.pathReg_spec.2.2 _ hc]
  filter_upwards [hRS γ hγ hγ2 P B hB, hreg] with a ha hra
  have heq : (fun left => Ψ left a) = fun left => Ψ left (G1Pkg.pathReg a) := by
    funext left z
    cases left
    · exact hd₀ a _ (fun t ht => hra t (Or.inr ht)) z
    · exact hd₁ a _ (fun t ht => hra t (Or.inl ht)) z
  rw [heq]
  exact hQ _ (G1Pkg.pathReg_spec.2.1 a) ha

/-! ## The deterministic form of the profile input -/

/-- The conclusion of `G1ProfileStmt` for one map `ψ` (the pushed circles are `ψ_* fc(d, r)`). -/
def ProfileConcl (γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    (X : Ω' → FieldSample) (A : ℝ → Ω' → ℝ) (ψ : ℂ → ℂ) : Prop :=
  ∀ G : Ω' → ℂ × ℝ → ℝ, IsRegVersion X P' G →
    ∀ᵐ ω' ∂P',
      (∀ d ∈ Hbar, ∀ r : ℝ, 0 < r → ProfileGood (X ω') (G ω') (fun t => A t ω') (Qc γ)
        (scaleParam γ (wedge0 γ X A ω')) ((foldedCircle d r).map ψ)) ∧
      ContinuousOn (dPart γ X A ψ ω') (Hbar ×ˢ Ioi 0) ∧
      ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
        ∫ u, dPart γ X A ψ ω' (u, ρ) ∂foldedCircle w r =
          ∫ v, dPart γ X A ψ ω' (v, r) ∂foldedCircle w ρ

/-- **Profile input, deterministic in the path**: `G1ProfileStmt`'s conclusion for every continuous
path whose SLE_{γ²} trace is a simple chord (so that `Ψ left a` is the inverse of a normalized
uniformizer of the side component, `G1PsiSel`). -/
def G1ProfileDetStmt : Prop :=
  G1RepSetting fun γ _ _ _ _ _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ a : ℝ≥0 → ℝ, Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) → ∀ left : Bool,
      ProfileConcl γ P' X A (Ψ left a)

/-- **`G1ProfileStmt` from the deterministic form and regularized Rohde–Schramm.** -/
theorem g1ProfileStmt_of_det (hRS : G1RegPathChordStmt) (hD : G1ProfileDetStmt) :
    G1ProfileStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  have := ae_map_pathOf_of_chord hRS hγ hγ2 hB hΨ
    (fun ψs => ∀ left, ProfileConcl γ P' X A (ψs left))
    (fun a hc hs left => hD γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ a hc hs left)
  filter_upwards [this] with a ha left G hG
  exact ha left G hG

/-- The regularized coordinate process on the path space: `t, a ↦ pathReg a t`. -/
def regCoord (t : ℝ≥0) (a : ℝ≥0 → ℝ) : ℝ := G1Pkg.pathReg a t

/-- **The regularized coordinate process is a Brownian motion under the path law.** Its paths are
continuous for every input (`G1Pkg.pathReg_spec`), and its finite-dimensional laws under
`P.map (pathOf B)` are those of `B`, because `pathReg` is the identity on the (a.s. continuous)
Brownian paths. Own bookkeeping. -/
theorem isBrownianReal_regCoord {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianReal regCoord (P.map (pathOf B)) where
  hasLaw I := by
    have hIm : Measurable fun p : ℝ≥0 → ℝ => (I.restrict p : I → ℝ) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply (i : ℝ≥0)
    have hf : Measurable fun a : ℝ≥0 → ℝ => I.restrict (regCoord · a) :=
      hIm.comp G1Pkg.pathReg_spec.1
    have hmB := QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB
    refine ⟨hf.aemeasurable, ?_⟩
    rw [AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hmB]
    rw [← (hB.hasLaw I).map_eq]
    refine Measure.map_congr ?_
    filter_upwards [hB.cont] with ω hω
    have hc : Continuous (pathOf B ω) := hω
    show I.restrict (G1Pkg.pathReg (pathOf B ω)) = I.restrict (B · ω)
    rw [G1Pkg.pathReg_spec.2.2 _ hc]
    rfl
  cont := ae_of_all _ fun a => G1Pkg.pathReg_spec.2.1 a

/-- **`G1RegPathChordStmt` holds**: Rohde–Schramm (`RS.rohdeSchrammSimple`) applied on the path
space to the regularized coordinate process. -/
theorem g1RegPathChordStmt : G1RegPathChordStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB
  have : IsProbabilityMeasure (P.map (pathOf B)) :=
    (Measure.isProbabilityMeasure_map_iff (QuantumZipper.IsBrownianReal.aemeasurable_pathOf hB)).2 inferInstance
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  filter_upwards [RS.rohdeSchrammSimple (γ ^ 2) (by positivity) hκ4 (P.map (pathOf B)) regCoord
    (isBrownianReal_regCoord hB)] with a ha
  exact ha.1

/-- **`G1ProfileStmt` from its deterministic form alone.** -/
theorem g1ProfileStmt_of_det' (hD : G1ProfileDetStmt) : G1ProfileStmt :=
  g1ProfileStmt_of_det g1RegPathChordStmt hD

end G1RC
end Thm18Asm
end QuantumZipper

import InteractingSLE.GFF.LocalSets.AvoidIndep
import InteractingSLE.GFF.LocalSets.GermCutoff
import InteractingSLE.GFF.LocalSets.BallCovers

/-!
# The conditional law of the field given a finitely-valued cover (Lemma 3.6, (i) ⇒ (iii))

Specification §3.2, proof of Lemma 3.6, p. 52–53: "We will now show that `Â_δ` satisfies (iii)
… That `Â_δ` satisfies (iii) thus follows from Proposition 3.1", and the "finite conditioning
argument" with all finer covers recorded. Let `A` satisfy (i) for a zero-boundary GFF `h` on `ℍ`.
For the cover of level `j` (`BallCovers`), on the atom `{W_j(A) = W_T}` the field is
`h = G_T h + Q_T h` (Proposition 3.1 on `W_T`), and `Q_j h := Q_{T(A)} h` (`coverProj`). With
`𝒢_j = σ(A) ∨ σ(Q_k h : k ≥ j)` (`coverSigma`, decreasing in `j`):

`E[1_G e^{i h(φ)}] = E[1_G e^{i (Q_j h)(φ)} e^{−σ²_{W_j(A)}(φ)/2}]`, `E[1_G h(φ)] = E[1_G (Q_j h)(φ)]`
for every `G ∈ 𝒢_j` (`setIntegral_coverSigma`).

Proof: on the atom `T`, every event of `𝒢_j` coincides up to a null set with an event of
`𝒦_T = σ(Q_T h) ∨ avoidSigma A W_T` (`coverSigma_le_atomTrace`: `σ(A)` by the trace lemma; `Q_k h`,
`k ≥ j`, through the nesting lemma since `W_T ⊆ W_{T'}` there), and `G_T h` is independent of
`𝒦_T` (`indep_markov_avoidSigma`, which is where (i) is used). The source's increasing martingale
over finer covers is not needed: the trace lemma records all of `σ(A)` at once.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

/-- The open set `W_T ∩ ℍ` of a finite family of balls, as an element of `Opens ℂ`. -/
def markovOpen (T : Finset (ℕ × ℂ)) : Opens ℂ :=
  ⟨coverOpen T ∩ H, (isOpen_coverOpen T).inter isOpen_H⟩

lemma markovOpen_subset_H (T : Finset (ℕ × ℂ)) : (markovOpen T : Set ℂ) ⊆ H := inter_subset_right

lemma coe_markovOpen {j : ℕ} {T : Finset (ℕ × ℂ)} (hT : T ⊆ coverIdx j) :
    (markovOpen T : Set ℂ) = coverOpen T :=
  inter_eq_left.2 (coverOpen_subset_H hT)

lemma markovOpen_mono {T T' : Finset (ℕ × ℂ)} (h : T ⊆ T') : markovOpen T ≤ markovOpen T' :=
  inter_subset_inter_left _ (coverOpen_mono h)

/-- A Borel version of the projection onto `H(W_T)` (Proposition 3.1). -/
def coverMarkov (T : Finset (ℕ × ℂ)) : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens :=
  (exists_markovMap.{u} (markovOpen T) (markovOpen_subset_H T)).choose

lemma measurable_coverMarkov (T : Finset (ℕ × ℂ)) : Measurable (coverMarkov.{u} T) :=
  (exists_markovMap.{u} (markovOpen T) (markovOpen_subset_H T)).choose_spec.1

lemma isMarkovDecomposition_coverMarkov {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (T : Finset (ℕ × ℂ)) :
    GFF.IsMarkovDecomposition (markovOpen T) upperHalfPlaneOpens h
      (fun ω => coverMarkov.{u} T (h ω)) P :=
  (exists_markovMap.{u} (markovOpen T) (markovOpen_subset_H T)).choose_spec.2 hh

section Defs

variable {Ω : Type u}

/-- The atom `{C_j(A) = ℍ ∖ W_T}` of the cover of level `j`. -/
def coverAtom (j : ℕ) (A : Ω → Set ℂ) (T : Finset (ℕ × ℂ)) : Set Ω :=
  {ω | removedIdx j (A ω) = T}

/-- The projection `Q_j h` of `h` onto `H^⊥(W_j(A))`, the cover of level `j` of `A`. -/
def coverProj (j : ℕ) (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (ω : Ω) :
    DistOn upperHalfPlaneOpens :=
  markovCompl (coverMarkov.{u} (removedIdx j (A ω))) (h ω)

/-- `𝒢_j = ℳ ∨ σ(Q_k h : k ≥ j)` for a σ-algebra `ℳ` of set information (`ℳ = σ(A)` for
Lemma 3.6, `ℳ = σ(A₁, A₂)` for the marked union of Proposition 3.7), a decreasing family. -/
@[instance_reducible]
def coverSigmaM (ℳ : MeasurableSpace Ω) (j : ℕ) (A : Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) : MeasurableSpace Ω :=
  ℳ ⊔ ⨆ (k : ℕ) (_ : j ≤ k), MeasurableSpace.comap (coverProj k A h) inferInstance

/-- `𝒢_j = σ(A) ∨ σ(Q_k h : k ≥ j)`. -/
@[instance_reducible]
def coverSigma (j : ℕ) (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace Ω :=
  coverSigmaM (MeasurableSpace.comap A hittingSigma) j A h

lemma coverSigmaM_anti (ℳ : MeasurableSpace Ω) (A : Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) : Antitone fun j => coverSigmaM ℳ j A h := fun j _ hjj' =>
  sup_le_sup le_rfl (iSup₂_le fun k hk => le_iSup₂_of_le (f := fun (k : ℕ) (_ : j ≤ k) =>
    MeasurableSpace.comap (coverProj k A h) inferInstance) k (hjj'.trans hk) le_rfl)

lemma coverSigma_anti (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    Antitone fun j => coverSigma j A h := coverSigmaM_anti _ A h

lemma mem_coverAtom_powerset {j : ℕ} {A : Ω → Set ℂ} (ω : Ω) :
    removedIdx j (A ω) ∈ (coverIdx j).powerset :=
  Finset.mem_powerset.2 (removedIdx_subset j (A ω))

lemma coverAtom_subset_avoid (j : ℕ) (A : Ω → Set ℂ) (T : Finset (ℕ × ℂ)) :
    coverAtom j A T ⊆ {ω | Disjoint (A ω) (coverThick j T)} := by
  intro ω hω
  rw [coverAtom, mem_ofPred_eq] at hω
  rw [mem_ofPred_eq, ← hω]
  exact disjoint_coverThick_removedIdx j (A ω)

end Defs

section Meas

variable {Ω : Type u} {ℳ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

lemma measurableSet_coverAtom {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A) (j : ℕ)
    (T : Finset (ℕ × ℂ)) : MeasurableSet (coverAtom j A T) :=
  hA (measurableSet_removedIdx_eq j T)

/-- A function given on each atom of the cover of level `j` by a measurable function is
measurable. -/
lemma measurable_of_coverAtom {β : Type*} [MeasurableSpace β] {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (j : ℕ) {F : Finset (ℕ × ℂ) → Ω → β}
    (hF : ∀ T, Measurable (F T)) : Measurable fun ω => F (removedIdx j (A ω)) ω := by
  intro B hB
  have e : (fun ω => F (removedIdx j (A ω)) ω) ⁻¹' B =
      ⋃ T ∈ (coverIdx j).powerset, coverAtom j A T ∩ F T ⁻¹' B := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, coverAtom, mem_ofPred_eq, exists_prop]
    exact ⟨fun h => ⟨_, mem_coverAtom_powerset ω, rfl, h⟩, fun ⟨T, _, hT, h⟩ => hT ▸ h⟩
  rw [e]
  exact Finset.measurableSet_biUnion _ fun T _ =>
    (measurableSet_coverAtom hA j T).inter (hF T hB)

lemma measurable_coverProj {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (j : ℕ) :
    Measurable (coverProj j A h) :=
  measurable_of_coverAtom hA j fun T => (measurable_markovCompl (measurable_coverMarkov.{u} T)).comp hh

lemma coverSigmaM_le (hℳ : ℳ ≤ mΩ) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (j : ℕ) : coverSigmaM ℳ j A h ≤ mΩ :=
  sup_le hℳ (iSup₂_le fun k _ => (measurable_coverProj hA hh k).comap_le)

lemma coverSigma_le {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (j : ℕ) :
    coverSigma j A h ≤ mΩ :=
  coverSigmaM_le hA.comap_le hA hh j

end Meas

section Struct

variable {Ω : Type u} {ℳ : MeasurableSpace Ω} {𝒮 : Set ℂ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- `𝒦_T = σ(Q_T h) ∨ 𝒮 W_T` for a family `𝒮` of avoidance σ-algebras (`𝒮 = avoidSigma A`
for Lemma 3.6): the σ-algebra independent of the projection onto `H(W_T)`. -/
@[instance_reducible]
def atomSigmaM (𝒮 : Set ℂ → MeasurableSpace Ω) (h : Ω → DistOn upperHalfPlaneOpens)
    (T : Finset (ℕ × ℂ)) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => markovCompl (coverMarkov.{u} T) (h ω)) inferInstance ⊔
    𝒮 (markovOpen T)

/-- `𝒦_T = σ(Q_T h) ∨ avoidSigma A W_T` (`indep_markov_avoidSigma`). -/
@[instance_reducible]
def atomSigma (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (T : Finset (ℕ × ℂ)) :
    MeasurableSpace Ω :=
  atomSigmaM (avoidSigma A) h T

omit mΩ in
lemma coverAtom_eq_empty {j : ℕ} {A : Ω → Set ℂ} {T : Finset (ℕ × ℂ)} (hT : ¬ T ⊆ coverIdx j) :
    coverAtom j A T = ∅ := by
  ext ω
  simp only [coverAtom, mem_ofPred_eq, mem_empty_iff_false, iff_false]
  rintro rfl
  exact hT (removedIdx_subset j _)

omit mΩ in
/-- Each event of `σ(A)` is, on an atom of the cover of level `j`, an event of
`avoidSigma A W_T`. -/
lemma measurableSet_avoidSigma_coverAtom {A : Ω → Set ℂ} (j : ℕ) (T : Finset (ℕ × ℂ))
    {B : Set (Set ℂ)} (hB : MeasurableSet[hittingSigma] B) :
    MeasurableSet[avoidSigma A (markovOpen T)] (A ⁻¹' B ∩ coverAtom j A T) := by
  by_cases hT : T ⊆ coverIdx j
  · have e : A ⁻¹' B ∩ coverAtom j A T =
        A ⁻¹' (B ∩ {S | removedIdx j S = T}) ∩ {ω | Disjoint (A ω) (coverThick j T)} := by
      ext ω
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, coverAtom_subset_avoid j A T h2⟩
      · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h1, h2⟩
    rw [e]
    refine measurableSet_avoidSigma_inter (isOpen_coverThick j T) ?_ (coverThick_subset_H hT)
      (hB.inter (measurableSet_removedIdx_eq j T))
    exact inter_subset_left.trans (coverOpen_subset_coverThick j T)
  · rw [coverAtom_eq_empty hT, inter_empty]; exact @MeasurableSet.empty _ (avoidSigma A (markovOpen T))

/-- The σ-algebra of the sets that coincide on the atom `{C_j(A) = ℍ ∖ W_T}`, up to a null set,
with a set of `𝒦_T`. -/
@[instance_reducible]
def atomTraceM (𝒮 : Set ℂ → MeasurableSpace Ω) (j : ℕ) (A : Ω → Set ℂ)
    (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω) (T : Finset (ℕ × ℂ))
    (hatom : MeasurableSet[𝒮 (markovOpen T)] (coverAtom j A T)) : MeasurableSpace Ω where
  MeasurableSet' G := ∃ G', MeasurableSet[atomSigmaM 𝒮 h T] G' ∧ G ∩ coverAtom j A T =ᵐ[P] G'
  measurableSet_empty := ⟨∅, @MeasurableSet.empty _ (atomSigmaM 𝒮 h T), by simp⟩
  measurableSet_compl G := by
    rintro ⟨G', hG', he⟩
    refine ⟨coverAtom j A T \ G', ?_, ?_⟩
    · exact (le_sup_right (a := MeasurableSpace.comap
        (fun ω => markovCompl (coverMarkov.{u} T) (h ω)) inferInstance) _ hatom).diff hG'
    · have : Gᶜ ∩ coverAtom j A T = coverAtom j A T \ (G ∩ coverAtom j A T) := by
        ext ω; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
      rw [this]
      exact EventuallyEqSet.rfl.diff he
  measurableSet_iUnion f hf := by
    choose G' hG' he using hf
    refine ⟨⋃ i, G' i, MeasurableSet.iUnion hG', ?_⟩
    rw [iUnion_inter]
    exact EventuallyEqSet.countable_iUnion he

/-- **Marking data** for the cover argument: a σ-algebra `ℳ ⊇ σ(A)` of set information and
avoidance σ-algebras `𝒮 W` such that, on each atom of each cover, every event of `ℳ` is an event
of `𝒮 W_T`, and the projection onto `H(W_T)` is independent of `σ(Q_T h) ∨ 𝒮 W_T`. -/
structure IsCoverMarking (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) (P : Measure Ω)
    (ℳ : MeasurableSpace Ω) (𝒮 : Set ℂ → MeasurableSpace Ω) : Prop where
  le : ℳ ≤ mΩ
  le_avoid : ∀ W, 𝒮 W ≤ mΩ
  comap_le : MeasurableSpace.comap A hittingSigma ≤ ℳ
  trace : ∀ (j : ℕ) (T : Finset (ℕ × ℂ)) (B : Set Ω), MeasurableSet[ℳ] B →
    MeasurableSet[𝒮 (markovOpen T)] (B ∩ coverAtom j A T)
  indep : ∀ T : Finset (ℕ × ℂ), Indep
    (MeasurableSpace.comap (fun ω => coverMarkov.{u} T (h ω)) inferInstance) (atomSigmaM 𝒮 h T) P

omit [IsProbabilityMeasure P] in
lemma IsCoverMarking.measurableSet_coverAtom {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hmk : IsCoverMarking A h P ℳ 𝒮)
    (j : ℕ) (T : Finset (ℕ × ℂ)) : MeasurableSet[𝒮 (markovOpen T)] (coverAtom j A T) := by
  have := hmk.trace j T _ (hmk.comap_le _ ⟨_, measurableSet_removedIdx_eq j T, rfl⟩)
  rwa [show A ⁻¹' {S | removedIdx j S = T} = coverAtom j A T from rfl, inter_self] at this

/-- **Every event of `𝒢_j` is, on each atom of the cover of level `j`, an event of `𝒦_T`** (up to
a null set): `ℳ` by the trace property, and `Q_k h` (`k ≥ j`) because on the atom `W_T ⊆ W_{T'}`
and `Q_{T'} h` is a function of `Q_T h` (nesting). -/
theorem coverSigmaM_le_atomTraceM {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) (hmk : IsCoverMarking A h P ℳ 𝒮) (j : ℕ)
    (T : Finset (ℕ × ℂ)) :
    coverSigmaM ℳ j A h ≤ atomTraceM 𝒮 j A h P T (hmk.measurableSet_coverAtom j T) := by
  have hhm := hh.measurable
  refine sup_le ?_ (iSup₂_le fun k hk => ?_)
  · intro B hB
    exact ⟨B ∩ coverAtom j A T, le_sup_right (a := MeasurableSpace.comap
      (fun ω => markovCompl (coverMarkov.{u} T) (h ω)) inferInstance) _
      (hmk.trace j T B hB), EventuallyEqSet.rfl⟩
  · rintro _ ⟨B, hB, rfl⟩
    have hnest : ∀ T' : Finset (ℕ × ℂ), T ⊆ T' → ∃ Ψ : DistOn upperHalfPlaneOpens →
        DistOn upperHalfPlaneOpens, Measurable Ψ ∧
        (fun ω => markovCompl (coverMarkov.{u} T') (h ω)) =ᵐ[P]
          fun ω => Ψ (markovCompl (coverMarkov.{u} T) (h ω)) := fun T' hTT' =>
      exists_measurable_markovCompl_comp (markovOpen_mono hTT') (markovOpen_subset_H T') hhm
        (isMarkovDecomposition_coverMarkov hh T) (isMarkovDecomposition_coverMarkov hh T')
    classical
    let G' : Finset (ℕ × ℂ) → Set Ω := fun T' =>
      if hT : T ⊆ T' then
        (coverAtom k A T' ∩ coverAtom j A T) ∩
          (fun ω => (hnest T' hT).choose (markovCompl (coverMarkov.{u} T) (h ω))) ⁻¹' B
      else ∅
    have hG'm : ∀ T', MeasurableSet[atomSigmaM 𝒮 h T] (G' T') := by
      intro T'
      by_cases hT : T ⊆ T'
      · simp only [G', hT, ↓reduceDIte]
        refine MeasurableSet.inter (le_sup_right (a := MeasurableSpace.comap
          (fun ω => markovCompl (coverMarkov.{u} T) (h ω)) inferInstance) _
          (hmk.trace j T _ (hmk.comap_le _ ⟨_, measurableSet_removedIdx_eq k T', rfl⟩))) ?_
        exact le_sup_left (b := 𝒮 (markovOpen T)) _
          ⟨_, (hnest T' hT).choose_spec.1 hB, rfl⟩
      · simp only [G', hT, ↓reduceDIte]; exact @MeasurableSet.empty _ (atomSigmaM 𝒮 h T)
    have hG'e : ∀ T', (coverAtom k A T' ∩ coverAtom j A T ∩
        (fun ω => markovCompl (coverMarkov.{u} T') (h ω)) ⁻¹' B) =ᵐ[P] G' T' := by
      intro T'
      by_cases hT : T ⊆ T'
      · simp only [G', hT, ↓reduceDIte]
        filter_upwards [(hnest T' hT).choose_spec.2] with ω hω
        simp only [coverAtom, mem_inter_iff, mem_preimage, mem_ofPred_eq, hω]
      · simp only [G', hT, ↓reduceDIte]
        refine EventuallyEqSet.of_eq (Set.eq_empty_of_forall_notMem fun ω hω => hT ?_)
        obtain ⟨⟨h1, h2⟩, -⟩ := hω
        simp only [coverAtom, mem_ofPred_eq] at h1 h2
        rw [← h1, ← h2]; exact removedIdx_mono hk (A ω)
    refine ⟨⋃ T' ∈ (coverIdx k).powerset, G' T',
      Finset.measurableSet_biUnion _ fun T' _ => hG'm T', ?_⟩
    have e : coverProj k A h ⁻¹' B ∩ coverAtom j A T = ⋃ T' ∈ (coverIdx k).powerset,
        coverAtom k A T' ∩ coverAtom j A T ∩
          (fun ω => markovCompl (coverMarkov.{u} T') (h ω)) ⁻¹' B := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_iUnion, coverAtom, mem_ofPred_eq, exists_prop,
        coverProj]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨_, mem_coverAtom_powerset (A := A) ω, ⟨rfl, h2⟩, h1⟩
      · rintro ⟨T', -, ⟨rfl, h2⟩, h1⟩; exact ⟨h1, h2⟩
    rw [e]
    exact EventuallyEqSet.countable_bUnion (Finset.countable_toSet _) fun T' _ => hG'e T'

end Struct

section Law

variable {Ω : Type u} {𝒦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- Factorization of a set integral under independence. -/
theorem setIntegral_exp_mul_of_indep (h𝒦 : 𝒦 ≤ mΩ)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hind : Indep (MeasurableSpace.comap X inferInstance) 𝒦 P) {G' : Set Ω}
    (hG' : MeasurableSet[𝒦] G') {Y : Ω → ℂ} (hY : StronglyMeasurable[𝒦] Y) {C : ℝ}
    (hYb : ∀ ω, ‖Y ω‖ ≤ C) (φ : TestOn upperHalfPlaneOpens) :
    ∫ ω in G', Complex.exp (Complex.I * (X ω φ : ℂ)) * Y ω ∂P =
      (∫ ω, Complex.exp (Complex.I * (X ω φ : ℂ)) ∂P) * ∫ ω in G', Y ω ∂P := by
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * (X ω φ : ℂ))
  have hFm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] F :=
    (@GFF.measurable_exp_I_mul Ω (MeasurableSpace.comap X inferInstance) _
      ((measurable_distOn_apply φ).comp (comap_measurable X))).stronglyMeasurable
  have hFi : Integrable F P := GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hX)
  set W : Ω → ℂ := G'.indicator Y
  have hW : StronglyMeasurable[𝒦] W := hY.indicator hG'
  have hWb : ∀ ω, ‖W ω‖ ≤ max C 0 := fun ω => by
    by_cases hω : ω ∈ G'
    · simp only [W, indicator_of_mem hω]; exact (hYb ω).trans (le_max_left _ _)
    · simp only [W, indicator_of_notMem hω, norm_zero]; exact le_max_right _ _
  have hpull := integral_mul_condExp_of_bdd (P := P) h𝒦 hW hWb hFi
  have hc := condExp_indep_eq (μ := P) hX.comap_le h𝒦 hFm hind
  have e1 : ∫ ω in G', F ω * Y ω ∂P = ∫ ω, W ω * F ω ∂P := by
    rw [← integral_indicator (h𝒦 _ hG')]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    by_cases hω : ω ∈ G' <;> simp [W, hω, mul_comm]
  rw [e1, hpull]
  have e2 : ∫ ω, W ω * (P[F|𝒦]) ω ∂P = ∫ ω, W ω * (∫ ω, F ω ∂P) ∂P :=
    integral_congr_ae (hc.mono fun ω hω => by simp only [hω])
  rw [e2, integral_mul_const, ← integral_indicator (h𝒦 _ hG'), mul_comm]

/-- The real counterpart: a centred `σ(X)`-measurable variable integrates to `0` on each event
of a σ-algebra independent of `X`. -/
theorem setIntegral_eq_zero_of_indep (h𝒦 : 𝒦 ≤ mΩ)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hind : Indep (MeasurableSpace.comap X inferInstance) 𝒦 P) {G' : Set Ω}
    (hG' : MeasurableSet[𝒦] G') (φ : TestOn upperHalfPlaneOpens)
    (hi : Integrable (fun ω => X ω φ) P) (h0 : ∫ ω, X ω φ ∂P = 0) :
    ∫ ω in G', X ω φ ∂P = 0 := by
  have hFm : StronglyMeasurable[MeasurableSpace.comap X inferInstance] fun ω => X ω φ :=
    ((measurable_distOn_apply φ).comp (comap_measurable X)).stronglyMeasurable
  have hc := condExp_indep_eq (μ := P) hX.comap_le h𝒦 hFm hind
  rw [← setIntegral_condExp h𝒦 hi hG', setIntegral_congr_ae (h𝒦 _ hG')
    (hc.mono fun ω hω _ => hω)]
  simp [h0]

end Law

section Law2

variable {Ω : Type u} {ℳ : MeasurableSpace Ω} {𝒮 : Set ℂ → MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens}

omit mΩ in
lemma coverProj_of_mem_coverAtom {j : ℕ} {T : Finset (ℕ × ℂ)} {ω : Ω}
    (hω : ω ∈ coverAtom j A T) :
    coverProj j A h ω = markovCompl (coverMarkov.{u} T) (h ω) := by
  simp only [coverAtom, mem_ofPred_eq] at hω
  simp only [coverProj, hω]

omit mΩ in
lemma coverCompl_of_mem_coverAtom {j : ℕ} {T : Finset (ℕ × ℂ)} {ω : Ω}
    (hω : ω ∈ coverAtom j A T) : coverCompl j (A ω) = (markovOpen T : Set ℂ) := by
  simp only [coverAtom, mem_ofPred_eq] at hω
  rw [coverCompl, hω, coe_markovOpen (hω ▸ removedIdx_subset j (A ω))]

lemma measurable_markovCompl_coverMarkov (hhm : Measurable h) (T : Finset (ℕ × ℂ)) :
    Measurable fun ω => markovCompl (coverMarkov.{u} T) (h ω) :=
  (measurable_markovCompl (measurable_coverMarkov.{u} T)).comp hhm

lemma atomSigmaM_le {𝒮 : Set ℂ → MeasurableSpace Ω} (h𝒮 : ∀ W, 𝒮 W ≤ mΩ) (hhm : Measurable h)
    (T : Finset (ℕ × ℂ)) : atomSigmaM 𝒮 h T ≤ mΩ :=
  sup_le (measurable_markovCompl_coverMarkov hhm T).comap_le (h𝒮 _)

/-- Lemma 3.6 (i) gives the marking data with `ℳ = σ(A)` and `𝒮 = avoidSigma A`. -/
theorem isCoverMarking_avoid (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P) :
    IsCoverMarking A h P (MeasurableSpace.comap A hittingSigma) (avoidSigma A) where
  le := hA.comap_le
  le_avoid := avoidSigma_le hA
  comap_le := le_rfl
  trace := by
    rintro j T _ ⟨B, hB, rfl⟩
    exact measurableSet_avoidSigma_coverAtom j T hB
  indep T := indep_markov_avoidSigma hh hA hloc (measurable_coverMarkov.{u} T)
    (isMarkovDecomposition_coverMarkov hh T)

/-- **The conditional law on one atom.** -/
theorem setIntegral_coverAtomM
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮) (j : ℕ)
    (T : Finset (ℕ × ℂ)) {G : Set Ω} (hG : MeasurableSet[coverSigmaM ℳ j A h] G)
    (φ : TestOn upperHalfPlaneOpens) :
    (∫ ω in G ∩ coverAtom j A T, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P =
      ∫ ω in G ∩ coverAtom j A T, Complex.exp (Complex.I * (coverProj j A h ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl j (A ω)) φ φ) : ℝ) : ℂ) ∂P) ∧
    ∫ ω in G ∩ coverAtom j A T, h ω φ ∂P = ∫ ω in G ∩ coverAtom j A T, coverProj j A h ω φ ∂P := by
  have hhm := hh.measurable
  obtain ⟨G', hG'm, hG'e⟩ := coverSigmaM_le_atomTraceM hh hmk j T G hG
  have hd := isMarkovDecomposition_coverMarkov hh T
  have hind := hmk.indep T
  have hle := atomSigmaM_le hmk.le_avoid hhm T
  have hXm : Measurable fun ω => coverMarkov.{u} T (h ω) := (measurable_coverMarkov T).comp hhm
  have hQm : Measurable[atomSigmaM 𝒮 h T] fun ω => markovCompl (coverMarkov.{u} T) (h ω) :=
    (comap_measurable _).mono le_sup_left le_rfl
  have hsplit : ∀ ω, h ω φ = coverMarkov.{u} T (h ω) φ + markovCompl (coverMarkov.{u} T) (h ω) φ :=
    fun ω => by simp [markovCompl]
  have hGs : MeasurableSet (G ∩ coverAtom j A T) :=
    (coverSigmaM_le hmk.le hA hhm j _ hG).inter (measurableSet_coverAtom hA j T)
  have hcv : zeroGFFTestCov (markovOpen T) φ φ = ‖covVec (markovOpen T) φ‖ ^ 2 := by
    rw [zeroGFFTestCov_eq_inner_covVec (markovOpen T).isOpen (markovOpen_subset_H T),
      real_inner_self_eq_norm_sq]
  have hc : ∫ ω, Complex.exp (Complex.I * (coverMarkov.{u} T (h ω) φ : ℂ)) ∂P =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (markovOpen T) φ φ) : ℝ) : ℂ) := by
    rw [integral_exp_markov (markovOpen_subset_H T) hd φ, hcv]
  have hQs : StronglyMeasurable[atomSigmaM 𝒮 h T] fun ω =>
      Complex.exp (Complex.I * (markovCompl (coverMarkov.{u} T) (h ω) φ : ℂ)) :=
    (@GFF.measurable_exp_I_mul Ω (atomSigmaM 𝒮 h T) _
      ((measurable_distOn_apply φ).comp hQm)).stronglyMeasurable
  have key := setIntegral_exp_mul_of_indep hle hXm hind hG'm hQs (C := 1)
    (fun ω => (Complex.norm_exp_I_mul_ofReal _).le) φ
  beta_reduce at key
  constructor
  · have hL : ∫ ω in G ∩ coverAtom j A T, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P =
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (markovOpen T) φ φ) : ℝ) : ℂ) *
          ∫ ω in G', Complex.exp (Complex.I * (markovCompl (coverMarkov.{u} T) (h ω) φ : ℂ)) ∂P := by
      rw [setIntegral_congr_set hG'e, ← hc, ← key]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hsplit ω, Complex.ofReal_add, mul_add, Complex.exp_add]
    have hR : ∫ ω in G ∩ coverAtom j A T, Complex.exp (Complex.I * (coverProj j A h ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl j (A ω)) φ φ) : ℝ) : ℂ) ∂P =
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (markovOpen T) φ φ) : ℝ) : ℂ) *
          ∫ ω in G', Complex.exp (Complex.I * (markovCompl (coverMarkov.{u} T) (h ω) φ : ℂ)) ∂P := by
      rw [setIntegral_congr_fun hGs (g := fun ω => Complex.exp (Complex.I *
        (markovCompl (coverMarkov.{u} T) (h ω) φ : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (markovOpen T) φ φ) : ℝ) : ℂ)) fun ω hω => by
          simp only [coverProj_of_mem_coverAtom hω.2, coverCompl_of_mem_coverAtom hω.2],
        integral_mul_const, setIntegral_congr_set hG'e, mul_comm]
    rw [hL, hR]
  · have hXi : Integrable (fun ω => coverMarkov.{u} T (h ω) φ) P :=
      (hd.isZBGFFExtOn.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
    have hQi : Integrable (fun ω => markovCompl (coverMarkov.{u} T) (h ω) φ) P :=
      ((hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two).sub hXi
    have hL : ∫ ω in G ∩ coverAtom j A T, h ω φ ∂P =
        ∫ ω in G', markovCompl (coverMarkov.{u} T) (h ω) φ ∂P := by
      rw [setIntegral_congr_set hG'e]
      have : ∫ ω in G', h ω φ ∂P = ∫ ω in G', coverMarkov.{u} T (h ω) φ ∂P +
          ∫ ω in G', markovCompl (coverMarkov.{u} T) (h ω) φ ∂P := by
        rw [← integral_add hXi.integrableOn hQi.integrableOn]
        exact integral_congr_ae (Eventually.of_forall hsplit)
      rw [this, setIntegral_eq_zero_of_indep hle hXm hind hG'm φ hXi (hd.isZBGFFExtOn.centered φ),
        zero_add]
    have hR : ∫ ω in G ∩ coverAtom j A T, coverProj j A h ω φ ∂P =
        ∫ ω in G', markovCompl (coverMarkov.{u} T) (h ω) φ ∂P := by
      rw [setIntegral_congr_fun hGs (g := fun ω => markovCompl (coverMarkov.{u} T) (h ω) φ)
        fun ω hω => by simp only [coverProj_of_mem_coverAtom hω.2], setIntegral_congr_set hG'e]
    rw [hL, hR]

omit mΩ in
lemma eq_biUnion_coverAtom (j : ℕ) (G : Set Ω) :
    G = ⋃ T ∈ (coverIdx j).powerset, G ∩ coverAtom j A T := by
  ext ω
  simp only [mem_iUnion, mem_inter_iff, exists_prop, coverAtom, mem_ofPred_eq]
  exact ⟨fun h => ⟨_, mem_coverAtom_powerset (A := A) ω, h, rfl⟩, fun ⟨_, _, h, _⟩ => h⟩

omit mΩ in
lemma pairwise_disjoint_coverAtom (j : ℕ) (G : Set Ω) :
    Set.Pairwise (↑(coverIdx j).powerset) (Function.onFun Disjoint fun T => G ∩ coverAtom j A T) := by
  intro T _ T' _ hTT'
  refine Set.disjoint_left.2 fun ω h1 h2 => hTT' ?_
  simp only [coverAtom, mem_inter_iff, mem_ofPred_eq] at h1 h2
  rw [← h1.2, ← h2.2]

lemma measurable_coverVar (hA : Measurable[mΩ, hittingSigma] A) (j : ℕ)
    (φ : TestOn upperHalfPlaneOpens) :
    Measurable fun ω => zeroGFFTestCov (coverCompl j (A ω)) φ φ :=
  measurable_of_coverAtom (F := fun T _ => zeroGFFTestCov (coverOpen T) φ φ) hA j
    fun _ => measurable_const

/-- **Conditional law given `𝒢_j`** (the cover of level `j` of `A`): for every event `G` of
`𝒢_j`, `E[1_G e^{i h(φ)}] = E[1_G e^{i (Q_j h)(φ)} e^{−σ²_{W_j(A)}(φ)/2}]` and
`E[1_G h(φ)] = E[1_G (Q_j h)(φ)]`. -/
theorem setIntegral_coverSigmaM
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hmk : IsCoverMarking A h P ℳ 𝒮) (j : ℕ)
    {G : Set Ω} (hG : MeasurableSet[coverSigmaM ℳ j A h] G) (φ : TestOn upperHalfPlaneOpens) :
    (∫ ω in G, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P =
      ∫ ω in G, Complex.exp (Complex.I * (coverProj j A h ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl j (A ω)) φ φ) : ℝ) : ℂ) ∂P) ∧
    ∫ ω in G, h ω φ ∂P = ∫ ω in G, coverProj j A h ω φ ∂P := by
  have hhm := hh.measurable
  have hms : ∀ T ∈ (coverIdx j).powerset, MeasurableSet (G ∩ coverAtom j A T) := fun T _ =>
    (coverSigmaM_le hmk.le hA hhm j _ hG).inter (measurableSet_coverAtom hA j T)
  have hPm : Measurable fun ω => coverProj j A h ω φ :=
    (measurable_distOn_apply φ).comp (measurable_coverProj hA hhm j)
  have hb1 : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hhm)
  have hb2 : Integrable (fun ω => Complex.exp (Complex.I * (coverProj j A h ω φ : ℂ)) *
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl j (A ω)) φ φ) : ℝ) : ℂ)) P := by
    refine (GFF.integrable_exp_I_mul hPm).mul_bdd ?_ (c := 1) (Eventually.of_forall fun ω => ?_)
    · exact (Complex.measurable_ofReal.comp
        (Real.measurable_exp.comp (measurable_const.mul (measurable_coverVar hA j φ)))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := zeroGFFTestCov_self_nonneg (V := coverCompl j (A ω)) (isOpen_coverOpen _)
        (coverCompl_subset_H j (A ω)) φ
      linarith
  have hhi : Integrable (fun ω => h ω φ) P :=
    (hh.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  have hPi : ∀ T, IntegrableOn (fun ω => coverProj j A h ω φ) (coverAtom j A T) P := by
    intro T
    have hXi : Integrable (fun ω => coverMarkov.{u} T (h ω) φ) P :=
      ((isMarkovDecomposition_coverMarkov hh T).isZBGFFExtOn.gaussian.hasGaussianLaw_eval
        φ).memLp_two.integrable one_le_two
    refine (hhi.sub hXi).integrableOn.congr_fun (fun ω hω => ?_) (measurableSet_coverAtom hA j T)
    simp only [coverProj_of_mem_coverAtom hω, markovCompl, sub_apply, Pi.sub_apply]
  constructor
  · conv_lhs => rw [eq_biUnion_coverAtom (A := A) j G]
    conv_rhs => rw [eq_biUnion_coverAtom (A := A) j G]
    rw [integral_biUnion_finset _ hms (pairwise_disjoint_coverAtom j G) fun _ _ => hb1.integrableOn,
      integral_biUnion_finset _ hms (pairwise_disjoint_coverAtom j G) fun _ _ => hb2.integrableOn]
    exact Finset.sum_congr rfl fun T _ => (setIntegral_coverAtomM hh hA hmk j T hG φ).1
  · conv_lhs => rw [eq_biUnion_coverAtom (A := A) j G]
    conv_rhs => rw [eq_biUnion_coverAtom (A := A) j G]
    rw [integral_biUnion_finset _ hms (pairwise_disjoint_coverAtom j G) fun _ _ => hhi.integrableOn,
      integral_biUnion_finset _ hms (pairwise_disjoint_coverAtom j G) fun T _ =>
        (hPi T).mono_set inter_subset_right]
    exact Finset.sum_congr rfl fun T _ => (setIntegral_coverAtomM hh hA hmk j T hG φ).2

/-- `setIntegral_coverSigmaM` for `ℳ = σ(A)`, from Lemma 3.6 (i). -/
theorem setIntegral_coverSigma (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P)
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsAvoidanceLocal A h P) (j : ℕ)
    {G : Set Ω} (hG : MeasurableSet[coverSigma j A h] G) (φ : TestOn upperHalfPlaneOpens) :
    (∫ ω in G, Complex.exp (Complex.I * (h ω φ : ℂ)) ∂P =
      ∫ ω in G, Complex.exp (Complex.I * (coverProj j A h ω φ : ℂ)) *
        ((Real.exp (-(1 / 2) * zeroGFFTestCov (coverCompl j (A ω)) φ φ) : ℝ) : ℂ) ∂P) ∧
    ∫ ω in G, h ω φ ∂P = ∫ ω in G, coverProj j A h ω φ ∂P :=
  setIntegral_coverSigmaM hh hA (isCoverMarking_avoid hh hA hloc) j hG φ

end Law2

end LocalSets
end InteractingSLE

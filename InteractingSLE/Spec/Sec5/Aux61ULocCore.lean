/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketStopWallsFinStop
import InteractingSLE.WangWu.ReverseContactMartFilt2Markov

/-!
# The union of a retained hull with a flow hull at a stop of the initially enlarged filtration

Packet PROVE-AUX61-UNIONLOC, item (P1) of `planning/handoffs/PROVE-AUX61-CHARTLOC.md`. Astra's follow-up 4, §1.1
(`source/external/AstraIG1/ig1_followup4_audited.txt` L84–L104, ruling R71): "take the counterflow record censored on
`{K ∩ U = ∅}` and a forward own-time record censored on its corresponding hull-avoidance event. Their kernels depend
only on `h − P_U h`, by Aux. 18. Use the original coupling in which the two explorations are conditionally independent
given the full field […]; their censored kernels therefore multiply. […] no determination of the counterflow is
assumed. At deterministic forward grid times this proves marked locality for the pair. An enlarged stopping decision is
measurable from the retained pair at each grid time."

The abstract statement proved here. On a probability space with a field `h`:

* a **retained set** `A₂` (the counterflow hull `K_s`) with marks `ℋ₂`, history-marked local, read from a σ-algebra
  `𝒜₂`;
* a monotone **hull process** `K_t` (the flow hull) adapted to a right-continuous filtration `𝓕` inside a σ-algebra
  `𝒜₁`, history-marked local at every bounded `𝓕`-stopping time `τ` with the marks `𝓕_τ` (what the frozen optional hull
  coupling gives through the capacity coding theorem, `WholeField.isHistoryAvoidanceLocal_hull`);
* `𝒜₁` and `𝒜₂` conditionally independent given the field (the glue);
* a **stop** `T` of the initially enlarged filtration `ℋ₂ ∨ 𝓕_t`, with marks `ℳ`, in the Galmarino form
  `IsEnlargedStop`: for every bounded `𝓕`-stopping time `σ` and mark `M`, `{T ≤ σ} ∩ M ∈ ℋ₂ ∨ 𝓕_σ`.

Then the union `ℍ ∩ (A₂ ∪ K_T)` (on `{T < ∞}`; `ℍ` elsewhere) satisfies the history-marked avoidance criterion for
`ℳ` (**`isHistoryAvoidanceLocal_unionAt`**). The stop may depend on BOTH records; neither curve is assumed to be
determined by the field.

Proof: the union at deterministic times and at the `𝓕`-hitting times of `U` is marked local for the joint marks by
the conditional-independence union lemma (`WangWu.isHistoryAvoidanceLocal_union`, Proposition 3.7 with retained
histories); the stop is then handled by `PocketStopWalls.isHistoryAvoidanceLocal_walls_hull` with empty walls and the
union process `A₂ ∪ K_t` as the hull: `{K_T ∩ U = ∅}` splits at the capped hitting time `σ` of `U` into
`⋃_{r ∈ ℚ} {K_r ∩ U = ∅} ∩ {T < r}` and `{K_σ ∩ U = ∅} ∩ {T = σ}`, so no inner open-set exhaustion (no Gaussian tail
identity) is needed. The hitting time of the union process is `0` where `A₂` meets `U`, the `𝓕`-hitting time of `K`
elsewhere.

R48 / R77: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement`, any `*_of_param`, or
Astra's post-contact kernel.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61ULoc

open QuantumZipper (H)
open LQGMetric (DistOn CondIndepEv)
open LocalSets WholeField Sec7.PocketStopWalls Sec7.PocketStopWallsFin

/-! ### The enlarged stop -/

section Stop

variable {X : Type*}

/-- **A stop of the initially enlarged filtration `ℋ ∨ 𝓕_t`, in Galmarino form**: for every bounded stopping time `σ`
of `𝓕` and every mark `M ∈ ℳ`, the event `{T ≤ σ} ∩ M` is in `ℋ ∨ 𝓕_σ`. -/
def IsEnlargedStop (ℳ ℋ : MeasurableSpace X) {mX : MeasurableSpace X} (𝓕 : Filtration ℝ≥0 mX) (T : X → ℝ≥0∞) :
    Prop :=
  ∀ (σ : X → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun x => ((σ x : ℝ≥0) : WithTop ℝ≥0)) (M : Set X), MeasurableSet[ℳ] M →
    MeasurableSet[ℋ ⊔ hσ.measurableSpace] ({x | T x ≤ (σ x : ℝ≥0∞)} ∩ M)

/-- The enlarged stop is `PocketStopWallsFin.IsMarkedStop` with the identity as information (σ-algebra `ℋ`). -/
theorem IsEnlargedStop.isMarkedStop {ℳ ℋ : MeasurableSpace X} {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX}
    {T : X → ℝ≥0∞} (hT : IsEnlargedStop ℳ ℋ 𝓕 T) : @IsMarkedStop X X ℋ ℳ mX 𝓕 id T := by
  intro σ hσ M hM
  rw [MeasurableSpace.comap_id]
  exact hT σ hσ M hM

/-- **`{T < r} ∩ M ∈ ℋ ∨ 𝓕_r`.** -/
theorem IsEnlargedStop.measurableSet_lt_inter {ℳ ℋ : MeasurableSpace X} {mX : MeasurableSpace X}
    {𝓕 : Filtration ℝ≥0 mX} {T : X → ℝ≥0∞} (hT : IsEnlargedStop ℳ ℋ 𝓕 T) {M : Set X} (hM : MeasurableSet[ℳ] M)
    (r : ℝ≥0) : MeasurableSet[ℋ ⊔ 𝓕 r] ({x | T x < r} ∩ M) := by
  have h := @measurableSet_lt_inter_of_isMarkedStop X X ℋ ℳ mX 𝓕 id T hT.isMarkedStop M hM r
  rwa [MeasurableSpace.comap_id] at h

/-- **`{T = σ} ∩ {T < N} ∩ M ∈ ℋ ∨ 𝓕_σ`** for every bounded stopping time `σ`. -/
theorem IsEnlargedStop.measurableSet_eq_inter {ℳ ℋ : MeasurableSpace X} {mX : MeasurableSpace X}
    {𝓕 : Filtration ℝ≥0 mX} {T : X → ℝ≥0∞} (hT : IsEnlargedStop ℳ ℋ 𝓕 T) (σ : X → ℝ≥0)
    (hσ : IsStoppingTime 𝓕 fun x => ((σ x : ℝ≥0) : WithTop ℝ≥0)) (N : ℕ) {M : Set X} (hM : MeasurableSet[ℳ] M) :
    MeasurableSet[ℋ ⊔ hσ.measurableSpace] ({x | T x = (σ x : ℝ≥0∞)} ∩ ({x | T x < N} ∩ M)) := by
  have h := @measurableSet_eq_inter_of_isMarkedStop X X ℋ ℳ mX 𝓕 id T hT.isMarkedStop σ hσ N M hM
  rwa [MeasurableSpace.comap_id] at h

/-- **The enlarged stop pulled back along `π : X → Ω`**: `𝓕` is a filtration on `Ω` (the flow's own space), the stop
`T` and the marks live on `X` (the glued space), and for every bounded `𝓕`-stopping time `σ` and mark `M`, the event
`{T ≤ σ ∘ π} ∩ M` is in `ℋ ∨ π⁻¹ 𝓕_σ`. -/
def IsEnlargedStopComap (ℳ ℋ : MeasurableSpace X) {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ)
    (π : X → Ω) (T : X → ℝ≥0∞) : Prop :=
  ∀ (σ : Ω → ℝ≥0) (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) (M : Set X), MeasurableSet[ℳ] M →
    MeasurableSet[ℋ ⊔ hσ.measurableSpace.comap π] ({x | T x ≤ (σ (π x) : ℝ≥0∞)} ∩ M)

/-- **Traces of a join with a σ-algebra** (`PocketStopWalls.measurableSet_inter_of_sup` with the identity as
information). -/
theorem measurableSet_inter_of_sup' {ℋ 𝒮 𝒜 : MeasurableSpace X} {D : Set X} (hD : MeasurableSet[𝒮] D)
    (hH : ∀ B, MeasurableSet[ℋ] B → MeasurableSet[𝒮] (D ∩ B))
    (hA : ∀ F, MeasurableSet[𝒜] F → MeasurableSet[𝒮] (D ∩ F)) {Q : Set X} (hQ : MeasurableSet[ℋ ⊔ 𝒜] Q) :
    MeasurableSet[𝒮] (D ∩ Q) := by
  refine @measurableSet_inter_of_sup X X ℋ 𝒮 𝒜 D hD id hH hA Q ?_
  rwa [MeasurableSpace.comap_id]

section Comap

variable {ℳ ℋ : MeasurableSpace X} {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {π : X → Ω}
  {T : X → ℝ≥0∞}

/-- At a constant time: `{T ≤ c} ∩ M ∈ ℋ ∨ π⁻¹ 𝓕_c`. -/
theorem IsEnlargedStopComap.measurableSet_le_inter (hT : IsEnlargedStopComap ℳ ℋ 𝓕 π T) (c : ℝ≥0) {M : Set X}
    (hM : MeasurableSet[ℳ] M) : MeasurableSet[ℋ ⊔ (𝓕 c).comap π] ({x | T x ≤ (c : ℝ≥0∞)} ∩ M) := by
  have h := hT (fun _ => c) (isStoppingTime_const 𝓕 c) M hM
  rwa [IsStoppingTime.measurableSpace_const] at h

/-- **`{T < r} ∩ M ∈ ℋ ∨ π⁻¹ 𝓕_r`.** -/
theorem IsEnlargedStopComap.measurableSet_lt_inter (hT : IsEnlargedStopComap ℳ ℋ 𝓕 π T) {M : Set X}
    (hM : MeasurableSet[ℳ] M) (r : ℝ≥0) : MeasurableSet[ℋ ⊔ (𝓕 r).comap π] ({x | T x < r} ∩ M) := by
  have e : {x | T x < r} ∩ M = ⋃ q : ℚ, ⋃ (_ : ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) < r),
      ({x | T x ≤ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)} ∩ M) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hlt, hM⟩
      obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
      exact ⟨q, h2, h1.le, hM⟩
    · rintro ⟨q, hq, h1, hM⟩
      exact ⟨h1.trans_lt hq, hM⟩
  rw [e]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => ?_
  have hle : Real.toNNReal q ≤ r := by exact_mod_cast hq.le
  exact (sup_le_sup_left (MeasurableSpace.comap_mono (𝓕.mono hle)) _) _ (hT.measurableSet_le_inter _ hM)

/-- **`{T = σ ∘ π} ∩ {T < N} ∩ M ∈ ℋ ∨ π⁻¹ 𝓕_σ`** for every bounded stopping time `σ`. -/
theorem IsEnlargedStopComap.measurableSet_eq_inter (hT : IsEnlargedStopComap ℳ ℋ 𝓕 π T) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕 fun ω => ((σ ω : ℝ≥0) : WithTop ℝ≥0)) (N : ℕ) {M : Set X} (hM : MeasurableSet[ℳ] M) :
    MeasurableSet[ℋ ⊔ hσ.measurableSpace.comap π]
      ({x | T x = (σ (π x) : ℝ≥0∞)} ∩ ({x | T x < N} ∩ M)) := by
  set 𝒮 : MeasurableSpace X := ℋ ⊔ hσ.measurableSpace.comap π with h𝒮
  have hpre : ∀ S, MeasurableSet[hσ.measurableSpace] S → MeasurableSet[𝒮] (π ⁻¹' S) := fun S hS =>
    (le_sup_right : hσ.measurableSpace.comap π ≤ 𝒮) _ ⟨S, hS, rfl⟩
  have hN : MeasurableSet[𝒮] {x | σ (π x) < (N : ℝ≥0)} := by
    have h := hσ.measurableSet_lt' (N : ℝ≥0)
    simp only [WithTop.coe_lt_coe] at h
    exact hpre _ h
  have hlt : MeasurableSet[𝒮] {x | T x < (σ (π x) : ℝ≥0∞)} := by
    have e : {x | T x < (σ (π x) : ℝ≥0∞)} = ⋃ q : ℚ,
        ({x | Real.toNNReal q < σ (π x)} ∩ {x | T x ≤ ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞)}) := by
      ext x
      simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
      constructor
      · intro h
        obtain ⟨q, -, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h
        exact ⟨q, by exact_mod_cast h2, h1.le⟩
      · rintro ⟨q, h1, h2⟩
        exact h2.trans_lt (by exact_mod_cast h1)
    rw [e]
    refine MeasurableSet.iUnion fun q => ?_
    set c : ℝ≥0 := Real.toNNReal q with hc
    have hD0 : MeasurableSet[hσ.measurableSpace] {ω | c < σ ω} := by
      have h := hσ.measurableSet_gt' c
      simpa only [WithTop.coe_lt_coe] using h
    have hD : MeasurableSet[𝒮] {x | c < σ (π x)} := hpre _ hD0
    refine measurableSet_inter_of_sup' (𝒜 := (𝓕 c).comap π) hD
      (fun B hB => hD.inter ((le_sup_left : ℋ ≤ 𝒮) _ hB)) (fun F hF => ?_) ?_
    · obtain ⟨F₀, hF₀, rfl⟩ := hF
      have hc' := isStoppingTime_const 𝓕 c
      have hF₀' : MeasurableSet[hc'.measurableSpace] F₀ := by rwa [IsStoppingTime.measurableSpace_const]
      have h1 : MeasurableSet[hσ.measurableSpace]
          (F₀ ∩ {ω | (c : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)}) :=
        IsStoppingTime.measurableSpace_mono (hc'.min hσ) hσ (fun ω => min_le_right _ _) _
          (IsStoppingTime.measurableSet_inter_le hc' hσ F₀ hF₀')
      have e' : {x | c < σ (π x)} ∩ π ⁻¹' F₀ =
          π ⁻¹' ((F₀ ∩ {ω | (c : WithTop ℝ≥0) ≤ ((σ ω : ℝ≥0) : WithTop ℝ≥0)}) ∩ {ω | c < σ ω}) := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage, WithTop.coe_le_coe]
        exact ⟨fun h => ⟨⟨h.2, h.1.le⟩, h.1⟩, fun h => ⟨h.2, h.1.1⟩⟩
      rw [e']
      exact hpre _ (h1.inter hD0)
    · have h := hT.measurableSet_le_inter c (@MeasurableSet.univ _ ℳ)
      rwa [inter_univ] at h
  have hA : MeasurableSet[𝒮] ({x | T x ≤ (σ (π x) : ℝ≥0∞)} ∩ M) := hT σ hσ M hM
  have e : {x | T x = (σ (π x) : ℝ≥0∞)} ∩ ({x | T x < N} ∩ M) =
      ({x | T x ≤ (σ (π x) : ℝ≥0∞)} ∩ M) ∩ ({x | σ (π x) < (N : ℝ≥0)} ∩ {x | T x < (σ (π x) : ℝ≥0∞)}ᶜ) := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_compl_iff, not_lt]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1.le, h3⟩, ?_, h1.ge⟩
      have : (σ (π x) : ℝ≥0∞) < ((N : ℝ≥0) : ℝ≥0∞) := by rw [← h1, ENNReal.coe_natCast]; exact h2
      exact_mod_cast this
    · rintro ⟨⟨h1, h3⟩, h2, h4⟩
      have heq : T x = (σ (π x) : ℝ≥0∞) := le_antisymm h1 h4
      refine ⟨heq, ?_, h3⟩
      rw [heq, ← ENNReal.coe_natCast]
      exact_mod_cast h2
  rw [e]
  exact hA.inter (hN.inter hlt.compl)

end Comap

end Stop

/-! ### Two measurability facts -/

section Meas

variable {X : Type*}

/-- A random set whose avoidance events of the open subsets of `ℍ` are in `𝒜` is `𝒜`-hitting-measurable. -/
theorem measurable_hitting_of_avoid {𝒜 : MeasurableSpace X} {A : X → Set ℂ}
    (hA : ∀ U : Set ℂ, IsOpen U → U ⊆ H → MeasurableSet[𝒜] {x | Disjoint (A x) U}) :
    Measurable[𝒜, hittingSigma] A := by
  refine @measurable_generateFrom _ _ 𝒜 _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have e : A ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} = {x | Disjoint (A x) U}ᶜ := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, Set.not_disjoint_iff_nonempty_inter]
  rw [e]
  exact (hA U hU hUH).compl

/-- The stopped σ-algebra of a stopping time lies in every σ-algebra containing the filtration. -/
theorem measurableSpace_le_of_forall_le {mX : MeasurableSpace X} {𝓕 : Filtration ℝ≥0 mX}
    {𝒜 : MeasurableSpace X} (h𝒜 : ∀ t, 𝓕 t ≤ 𝒜) {τ : X → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) :
    hτ.measurableSpace ≤ 𝒜 :=
  fun _ hF => (iSup_le h𝒜) _ ((hτ.measurableSet _).1 hF).1

end Meas

/-! ### The union at the stop -/

section Union

variable {X : Type*}

/-- **The retained set with the hull at the stop**: `ℍ ∩ (A₂ ∪ K_T)` where `T < ∞`, and `ℍ` elsewhere. -/
def unionAt (A₂ : X → Set ℂ) (K : ℝ≥0 → X → Set ℂ) (T : X → ℝ≥0∞) (x : X) : Set ℂ :=
  if T x < ⊤ then H ∩ (A₂ x ∪ K (T x).toNNReal x) else H

theorem unionAt_eq_wallsHullAt (A₂ : X → Set ℂ) (K : ℝ≥0 → X → Set ℂ) (T : X → ℝ≥0∞) :
    unionAt A₂ K T = wallsHullAt (fun _ => ∅) (fun r x => A₂ x ∪ K r x) T := by
  funext x
  simp only [unionAt, wallsHullAt, empty_union]

/-- **The union of the retained set and the hull at a deterministic time or a stopping time is history-marked local
for the joint marks** (`WangWu.isHistoryAvoidanceLocal_union` for an `𝒜₁`-measurable hull read at `τ`). -/
theorem isHistoryAvoidanceLocal_union_at {𝒜₁ 𝒜₂ ℋ₁ ℋ₂ : MeasurableSpace X} [mX : MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {h : X → DistOn upperHalfPlaneOpens}
    (h𝒜₁ : 𝒜₁ ≤ mX) (h𝒜₂ : 𝒜₂ ≤ mX) (hℋ₁ : ℋ₁ ≤ 𝒜₁) (hℋ₂ : ℋ₂ ≤ 𝒜₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance) 𝒜₁ 𝒜₂ μ)
    {A₁ A₂ : X → Set ℂ} (hA₁ : Measurable[ℋ₁, hittingSigma] A₁) (hA₂ : Measurable[ℋ₂, hittingSigma] A₂)
    (hloc₁ : IsHistoryAvoidanceLocal ℋ₁ A₁ h μ) (hloc₂ : IsHistoryAvoidanceLocal ℋ₂ A₂ h μ) :
    IsHistoryAvoidanceLocal (ℋ₂ ⊔ ℋ₁) (fun x => A₂ x ∪ A₁ x) h μ := by
  have hu := WangWu.isHistoryAvoidanceLocal_union h𝒜₁ h𝒜₂ hℋ₁ hℋ₂ (hA₁.mono hℋ₁ le_rfl)
    (hA₂.mono hℋ₂ le_rfl) hci hloc₁ hloc₂
  rw [sup_comm]
  simpa only [union_comm] using hu

/-- **The hull process of a pulled-back space is history-marked local at the pulled-back stopping times**: if `K` is
history-marked local on `(Ω, P)` at the stopping time `τ` with the marks `𝓕_τ`, and `μ.map π = P`, then `K_τ ∘ π` is
history-marked local on `(X, μ)` for the field `h₀ ∘ π` with the marks `π⁻¹ 𝓕_τ`
(`WangWu.isHistoryAvoidanceLocal_of_map_eq`). -/
theorem isHistoryAvoidanceLocal_comap_stop {Ω : Type*} {𝔐 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [mX : MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀) {π : X → Ω} (hπ : Measurable π)
    (hμπ : μ.map π = P) (h𝔐 : 𝔐 ≤ mΩ) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsHistoryAvoidanceLocal 𝔐 A h₀ P) :
    IsHistoryAvoidanceLocal (𝔐.comap π) (fun x => A (π x)) (fun x => h₀ (π x)) μ := by
  have hlaw : μ.map (fun x => (h₀ (π x), π x)) = P.map (fun ω => (h₀ ω, id ω)) := by
    rw [show (fun x => (h₀ (π x), π x)) = (fun ω => (h₀ ω, id ω)) ∘ π from rfl,
      ← Measure.map_map (hh₀.prodMk measurable_id) hπ, hμπ]
  refine WangWu.isHistoryAvoidanceLocal_of_map_eq (𝔐 := 𝔐) hh₀ measurable_id (hh₀.comp hπ) hπ hlaw hA h𝔐 ?_
  rw [MeasurableSpace.comap_id]
  exact hloc

/-- **The union law at an enlarged stop, flow side on a factor `π : X → Ω`** (the glued space `X = Ω × Hist` with
`π = Prod.fst`). As `isHistoryAvoidanceLocal_unionAt`, with the hull process `K`, its right-continuous filtration `𝓕`
and its marked locality at bounded stopping times on the flow's own probability space `(Ω, P)` (field `h₀`), the
glued measure projecting to `P`, the field on `X` read through `π`, `π⁻¹ 𝓕_t ≤ 𝒜₁` conditionally independent of `𝒜₂`
given the field, and the stop given in pulled-back Galmarino form (`IsEnlargedStopComap`). -/
theorem isHistoryAvoidanceLocal_unionAt_comap {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝒜₁ 𝒜₂ ℋ₂ ℳ : MeasurableSpace X} [mX : MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : Measurable h₀) {π : X → Ω}
    (hπ : Measurable π) (hμπ : μ.map π = P) (h𝒜₁ : 𝒜₁ ≤ mX) (h𝒜₂ : 𝒜₂ ≤ mX) (hℋ₂ : ℋ₂ ≤ 𝒜₂)
    (hci : CondIndepEv (MeasurableSpace.comap (fun x => h₀ (π x)) inferInstance) 𝒜₁ 𝒜₂ μ)
    {A₂ : X → Set ℂ} (hA₂ : Measurable[ℋ₂, hittingSigma] A₂)
    (hloc₂ : IsHistoryAvoidanceLocal ℋ₂ A₂ (fun x => h₀ (π x)) μ)
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsRightContinuous] (h𝓕 : ∀ t, (𝓕 t).comap π ≤ 𝒜₁)
    {K : ℝ≥0 → Ω → Set ℂ} (hKmono : ∀ ω, Monotone fun t => K t ω)
    (hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) U})
    (hKst : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {ω | Disjoint (K ((τ ω).untopD 0) ω) U})
    (hloc : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      IsHistoryAvoidanceLocal hτ.measurableSpace (fun ω => K ((τ ω).untopD 0) ω) h₀ P)
    {T : X → ℝ≥0∞} (hT : IsEnlargedStopComap ℳ ℋ₂ 𝓕 π T)
    (hS0 : ∀ M, MeasurableSet[ℳ] M → MeasurableSet[ℋ₂ ⊔ ⨆ r, (𝓕 r).comap π] M) :
    IsHistoryAvoidanceLocal ℳ (unionAt A₂ (fun r x => K r (π x)) T) (fun x => h₀ (π x)) μ := by
  set h : X → DistOn upperHalfPlaneOpens := fun x => h₀ (π x) with hdef
  have hh : Measurable h := hh₀.comp hπ
  have hℋ₂X : ℋ₂ ≤ mX := hℋ₂.trans h𝒜₂
  have hπle : ∀ 𝔐 : MeasurableSpace Ω, 𝔐 ≤ mΩ → 𝔐.comap π ≤ mX := fun 𝔐 h𝔐 =>
    (MeasurableSpace.comap_mono h𝔐).trans hπ.comap_le
  -- the pulled-back hull at a finite stopping time, with the retained set
  have hKτ : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      IsHistoryAvoidanceLocal (ℋ₂ ⊔ hτ.measurableSpace.comap π)
        (fun x => A₂ x ∪ K ((τ (π x)).untopD 0) (π x)) h μ := by
    intro τ hτ hfin
    have hτΩ : hτ.measurableSpace ≤ ⨆ t, 𝓕 t := fun _ hF => ((hτ.measurableSet _).1 hF).1
    have hτ𝒜 : hτ.measurableSpace.comap π ≤ 𝒜₁ := by
      refine (MeasurableSpace.comap_mono hτΩ).trans ?_
      rw [MeasurableSpace.comap_iSup]
      exact iSup_le h𝓕
    have hAm : Measurable[hτ.measurableSpace, hittingSigma] fun ω => K ((τ ω).untopD 0) ω :=
      measurable_hitting_of_avoid fun U hU hUH => hKst τ hτ hfin U hU hUH
    have hAm' : Measurable[hτ.measurableSpace.comap π, hittingSigma]
        fun x => K ((τ (π x)).untopD 0) (π x) :=
      hAm.comp (comap_measurable π)
    have hloc₁ := isHistoryAvoidanceLocal_comap_stop hh₀ hπ hμπ hτ.measurableSpace_le
      (hAm.mono hτ.measurableSpace_le le_rfl) (hloc τ hτ hfin)
    exact isHistoryAvoidanceLocal_union_at h𝒜₁ h𝒜₂ hτ𝒜 hℋ₂ hci hAm' hA₂ hloc₁ hloc₂
  have hcomp : ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ ω, τ ω ≠ ⊤) →
      ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G → GFF.IsMarkovDecomposition U upperHalfPlaneOpens h (fun x => G (h x)) μ →
      ∀ F, MeasurableSet[ℋ₂ ⊔ hτ.measurableSpace.comap π] F →
        IsCompEvent (MeasurableSpace.comap h inferInstance) μ (fun x => markovCompl G (h x))
          ({x | Disjoint (A₂ x ∪ K ((τ (π x)).untopD 0) (π x)) U} ∩ F) := by
    intro τ hτ hfin U G hUH hG hMD F hF
    obtain ⟨g, hg, hge⟩ := hKτ τ hτ hfin U G hUH hG hMD F hF
    have hav := measurableSet_avoid U.isOpen hUH
    have hm : MeasurableSet {x | Disjoint (A₂ x ∪ K ((τ (π x)).untopD 0) (π x)) (U : Set ℂ)} := by
      have e : {x | Disjoint (A₂ x ∪ K ((τ (π x)).untopD 0) (π x)) (U : Set ℂ)} =
          {x | Disjoint (A₂ x) (U : Set ℂ)} ∩ π ⁻¹' {ω | Disjoint (K ((τ ω).untopD 0) ω) (U : Set ℂ)} := by
        ext x
        simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, disjoint_union_left]
      rw [e]
      exact (hℋ₂X _ (hA₂ hav)).inter (hπ (hτ.measurableSpace_le _ (hKst τ hτ hfin U U.isOpen hUH)))
    exact ⟨hm.inter ((sup_le hℋ₂X (hπle _ hτ.measurableSpace_le)) _ hF), g, hg, hge⟩
  rw [unionAt_eq_wallsHullAt]
  refine isHistoryAvoidanceLocal_walls_hull (𝒳 := Unit) (X := fun _ => ())
    (ℱ := fun r => ℋ₂ ⊔ (𝓕 r).comap π) hh measurable_const measurable_const ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the empty walls are determined local
    intro U G hUH hG hMD B hB
    by_cases hB0 : () ∈ B
    · refine ⟨univ, MeasurableSet.univ, Eq.eventuallyEq ?_⟩
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, empty_disjoint, true_and, mem_preimage, hB0, mem_univ]
    · refine ⟨∅, MeasurableSet.empty, Eq.eventuallyEq ?_⟩
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, empty_disjoint, true_and, mem_preimage, hB0,
        mem_empty_iff_false]
  · intro x a b hab
    exact union_subset_union_right _ (hKmono (π x) hab)
  · intro a b hab
    exact sup_le_sup_left (MeasurableSpace.comap_mono (𝓕.mono hab)) _
  · -- deterministic times
    intro U G hUH hG hMD r F hF
    have hτ := isStoppingTime_const 𝓕 r
    have h1 := hcomp (fun _ => (r : WithTop ℝ≥0)) hτ (fun _ => WithTop.coe_ne_top) U G hUH hG hMD F
      (by rw [IsStoppingTime.measurableSpace_const]; exact hF)
    simpa only [WithTop.untopD_coe] using h1
  · -- the capped hitting times of the union process
    intro U G hUH hG hMD
    have hKad' : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | Disjoint (K t ω) (U : Set ℂ)} :=
      fun t => hKad t U U.isOpen hUH
    have hD : MeasurableSet[ℋ₂] {x | Disjoint (A₂ x) (U : Set ℂ)} := hA₂ (measurableSet_avoid U.isOpen hUH)
    have hτN : ∀ N : ℕ, IsStoppingTime 𝓕 fun ω => ((hitCap K U (N : ℝ≥0) ω : ℝ≥0) : WithTop ℝ≥0) :=
      fun N => isStoppingTime_hitCap hKmono hKad'
    classical
    refine ⟨fun N x => if Disjoint (A₂ x) (U : Set ℂ) then hitCap K U (N : ℝ≥0) (π x) else 0,
      fun N => ℋ₂ ⊔ (hτN N).measurableSpace.comap π, fun N => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · intro x
      show (if Disjoint (A₂ x) (U : Set ℂ) then hitCap K U (N : ℝ≥0) (π x) else 0) ≤ (N : ℝ≥0)
      split_ifs
      · exact hitCap_le (π x)
      · exact zero_le
    · intro x t ht
      by_cases hx : Disjoint (A₂ x) (U : Set ℂ)
      · simp only [hx, ↓reduceIte] at ht
        exact disjoint_union_left.2 ⟨hx, disjoint_of_lt_hitCap ht⟩
      · simp only [hx, ↓reduceIte] at ht
        exact absurd ht (not_lt.2 zero_le)
    · intro x t ht htN
      by_cases hx : Disjoint (A₂ x) (U : Set ℂ)
      · simp only [hx, ↓reduceIte] at ht
        exact fun hd => not_disjoint_of_hitCap_lt hKmono ht htN (disjoint_union_left.1 hd).2
      · exact fun hd => hx (disjoint_union_left.1 hd).1
    · intro F hF
      have h1 := hcomp _ (hτN N) (fun _ => WithTop.coe_ne_top) U G hUH hG hMD F hF
      simp only [WithTop.untopD_coe] at h1
      have e : {x | Disjoint (A₂ x ∪ K (if Disjoint (A₂ x) (U : Set ℂ) then hitCap K U (N : ℝ≥0) (π x) else 0)
          (π x)) (U : Set ℂ)} ∩ F =
          {x | Disjoint (A₂ x ∪ K (hitCap K U (N : ℝ≥0) (π x)) (π x)) (U : Set ℂ)} ∩ F := by
        ext x
        simp only [mem_inter_iff, mem_ofPred_eq, disjoint_union_left]
        by_cases hx : Disjoint (A₂ x) (U : Set ℂ)
        · simp only [hx, ↓reduceIte, true_and]
        · simp only [hx, false_and]
      rw [e]
      exact h1
    · intro M hM
      have h0 := isStoppingTime_const 𝓕 (0 : ℝ≥0)
      have hle0 : h0.measurableSpace.comap π ≤ (hτN N).measurableSpace.comap π :=
        MeasurableSpace.comap_mono
          (IsStoppingTime.measurableSpace_mono h0 (hτN N) fun ω => WithTop.coe_le_coe.2 zero_le)
      have hA := hT.measurableSet_eq_inter (fun ω => hitCap K U (N : ℝ≥0) ω) (hτN N) N hM
      have hB := hT.measurableSet_eq_inter (fun _ => (0 : ℝ≥0)) h0 N hM
      have hB' : MeasurableSet[ℋ₂ ⊔ (hτN N).measurableSpace.comap π]
          ({x | T x = ((0 : ℝ≥0) : ℝ≥0∞)} ∩ ({x | T x < N} ∩ M)) := sup_le_sup_left hle0 _ _ hB
      have e : {x | T x = ((if Disjoint (A₂ x) (U : Set ℂ) then hitCap K U (N : ℝ≥0) (π x) else 0 : ℝ≥0) :
          ℝ≥0∞)} ∩ ({x | T x < N} ∩ M) =
          ({x | Disjoint (A₂ x) (U : Set ℂ)} ∩
              ({x | T x = (hitCap K U (N : ℝ≥0) (π x) : ℝ≥0∞)} ∩ ({x | T x < N} ∩ M))) ∪
            ({x | Disjoint (A₂ x) (U : Set ℂ)}ᶜ ∩
              ({x | T x = ((0 : ℝ≥0) : ℝ≥0∞)} ∩ ({x | T x < N} ∩ M))) := by
        ext x
        by_cases hx : Disjoint (A₂ x) (U : Set ℂ)
        · simp only [hx, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, mem_union, mem_compl_iff, true_and,
            not_true_eq_false, false_and, or_false]
        · simp only [hx, ↓reduceIte, mem_inter_iff, mem_ofPred_eq, mem_union, mem_compl_iff, false_and,
            not_false_eq_true, true_and, false_or]
      rw [e]
      refine le_sup_right (a := MeasurableSpace.comap (fun _ : X => ()) inferInstance) _ ?_
      exact (le_sup_left (a := ℋ₂) _ hD |>.inter hA).union ((le_sup_left (a := ℋ₂) _ hD).compl.inter hB')
  · intro M hM r
    exact le_sup_right (a := MeasurableSpace.comap (fun _ : X => ()) inferInstance) _
      (hT.measurableSet_lt_inter hM r)
  · intro M hM
    refine le_sup_right (a := MeasurableSpace.comap (fun _ : X => ()) inferInstance) _ ?_
    have hle : ℋ₂ ⊔ ⨆ r, (𝓕 r).comap π ≤ ⨆ r, ℋ₂ ⊔ (𝓕 r).comap π := sup_le
      (le_sup_left.trans (le_iSup (fun r => ℋ₂ ⊔ (𝓕 r).comap π) 0))
      (iSup_le fun r => le_sup_right.trans (le_iSup (fun r => ℋ₂ ⊔ (𝓕 r).comap π) r))
    exact hle _ (hS0 M hM)

/-- **The union of a retained set with a hull process at a stop of the initially enlarged filtration is
history-marked local** (Astra follow-up 4 §1.1, L84–L104; Proposition 3.7 with retained histories at an enlarged stop).
Hypotheses:
* the retained set `A₂` is `ℋ₂`-hitting-measurable and history-marked local for its marks `ℋ₂ ≤ 𝒜₂`;
* the monotone hull process `K` is adapted to the right-continuous filtration `𝓕 ≤ 𝒜₁` (`hKad`), its avoidance events
  at bounded stopping times are `𝓕_τ`-measurable (`hKst`), and it is history-marked local at every bounded stopping
  time with the marks `𝓕_τ` (`hloc`);
* `𝒜₁` and `𝒜₂` are conditionally independent given the field (`hci`);
* `T` is a stop of the enlarged filtration `ℋ₂ ∨ 𝓕_t` with marks `ℳ` (`hT`), and the marks are events of
  `ℋ₂ ∨ 𝓕_∞` (`hS0`).
Then `unionAt A₂ K T` satisfies the history-marked avoidance criterion for `ℳ`. -/
theorem isHistoryAvoidanceLocal_unionAt {𝒜₁ 𝒜₂ ℋ₂ ℳ : MeasurableSpace X} [mX : MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {h : X → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (h𝒜₁ : 𝒜₁ ≤ mX) (h𝒜₂ : 𝒜₂ ≤ mX) (hℋ₂ : ℋ₂ ≤ 𝒜₂)
    (hci : CondIndepEv (MeasurableSpace.comap h inferInstance) 𝒜₁ 𝒜₂ μ)
    {A₂ : X → Set ℂ} (hA₂ : Measurable[ℋ₂, hittingSigma] A₂) (hloc₂ : IsHistoryAvoidanceLocal ℋ₂ A₂ h μ)
    {𝓕 : Filtration ℝ≥0 mX} [𝓕.IsRightContinuous] (h𝓕 : ∀ t, 𝓕 t ≤ 𝒜₁)
    {K : ℝ≥0 → X → Set ℂ} (hKmono : ∀ x, Monotone fun t => K t x)
    (hKad : ∀ (t : ℝ≥0) (U : Set ℂ), IsOpen U → U ⊆ H → MeasurableSet[𝓕 t] {x | Disjoint (K t x) U})
    (hKst : ∀ (τ : X → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ x, τ x ≠ ⊤) → ∀ U : Set ℂ, IsOpen U →
      U ⊆ H → MeasurableSet[hτ.measurableSpace] {x | Disjoint (K ((τ x).untopD 0) x) U})
    (hloc : ∀ (τ : X → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓕 τ), (∀ x, τ x ≠ ⊤) →
      IsHistoryAvoidanceLocal hτ.measurableSpace (fun x => K ((τ x).untopD 0) x) h μ)
    {T : X → ℝ≥0∞} (hT : IsEnlargedStop ℳ ℋ₂ 𝓕 T)
    (hS0 : ∀ M, MeasurableSet[ℳ] M → MeasurableSet[ℋ₂ ⊔ ⨆ r, 𝓕 r] M) :
    IsHistoryAvoidanceLocal ℳ (unionAt A₂ K T) h μ := by
  have hT' : IsEnlargedStopComap ℳ ℋ₂ 𝓕 id T := by
    intro σ hσ M hM
    rw [MeasurableSpace.comap_id]
    exact hT σ hσ M hM
  exact isHistoryAvoidanceLocal_unionAt_comap (P := μ) hh measurable_id Measure.map_id h𝒜₁ h𝒜₂ hℋ₂ hci hA₂
    hloc₂ (fun t => by rw [MeasurableSpace.comap_id]; exact h𝓕 t) hKmono hKad hKst hloc hT'
    (fun M hM => by
      have e : (⨆ r, (𝓕 r).comap id) = ⨆ r, 𝓕 r := iSup_congr fun r => MeasurableSpace.comap_id
      rw [e]
      exact hS0 M hM)

end Union

end InteractingSLE.Sec5.Aux61ULoc

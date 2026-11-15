/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RS133Prob
import InteractingSLE.Spec.Sec7.Aux119Bdry

/-!
# Aux. lemma 119: the nested comparisons of the complete wall union with the walls' stopped prefixes

Packet PROVE-STRIPSYS25. Specification §7.4, the proof of Aux. lemma 119 (`source/spec/p385-432.md` L50, p. 387):

> Now retain the complete marked incoming union `A`. On every compact selected open side, nested local-set boundary
> comparison makes the mean `h_A` agree at the boundary with its single-path own mean. The collar is free of all other
> portions, by the two-arc geometry, compactness, and injectivity. Choose the own times from a countable rational family
> before selecting a suitable one on a realization. This gives all the boundary identities simultaneously on one event
> of probability one.

The complete marked incoming union of two walls `γ`, `ρ` is `wallUnion γ ρ = (γ ∪ ρ) ∩ ℍ`. For walls with Lemma 6.2's
inputs (continuous, from `0`, measurable at fixed times, determined by the field, history-sensitively local, in the
closed half-plane) that are transient, `wallUnion` is a field-determined local set (`isLocalSet_wallUnion`, Lemma 6.2
for two complete curves), and so is every stopped prefix `γ([0, q]) ∩ ℍ` (`RS133.isLocalSet_range_and_aeDetermined`).
Proposition 3.8 for the two field-determined local sets (`SideHeightBox.ae_tendsto_sub_of_locals`) then compares their
means at every prefix point `γ(s)`, `s < q`, off the other wall: near such a point the union is the prefix
(`exists_ball_inter_subset_prefix`, compactness and injectivity).

## Main results

* `exists_ball_inter_subset_prefix` (deterministic): near `γ(s)`, `s < q`, off `ρ`, the union is the prefix;
* `isLocalSet_wallUnion`: Lemma 6.2 for the complete union;
* **`ae_tendsto_sub_prefix`**: the nested comparison at one own time;
* **`ae_tendsto_sub_prefix_rat`**: at all rational own times on one probability-one event;
* `tendsto_sub_changePocket_left`, `tendsto_sub_changePocket_right`: the restriction to the change pocket's approach.

Conditional helpers; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology Bornology Function
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Aux119Nested

open QuantumZipper (H)
open LocalSets

/-! ### Geometry: near a prefix point off the other wall, the union is the prefix -/

section Geometry

/-- A continuous transient path has a closed range. -/
theorem isClosed_range_of_tendsto {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (htr : Tendsto γ atTop (cobounded ℂ)) :
    IsClosed (range γ) := by
  have h := Sec6.isClosed_image_le_of_tendsto_cobounded hγ htr ⊤
  have e : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ⊤} = univ := eq_univ_of_forall fun t => show (t : ℝ≥0∞) ≤ ⊤ from le_top
  rwa [e, image_univ] at h

/-- A continuous transient path has a closed image on every terminal interval `[q, ∞)`. -/
theorem isClosed_image_Ici {γ : ℝ≥0 → ℂ} (hγ : Continuous γ) (htr : Tendsto γ atTop (cobounded ℂ)) (q : ℝ≥0) :
    IsClosed (γ '' Ici q) := by
  have hc : Continuous fun t : ℝ≥0 => γ (q + t) := hγ.comp (continuous_const.add continuous_id)
  have ht : Tendsto (fun t : ℝ≥0 => γ (q + t)) atTop (cobounded ℂ) :=
    htr.comp (tendsto_atTop_mono (fun t => (le_add_self : t ≤ q + t)) tendsto_id)
  have e : γ '' Ici q = range fun t : ℝ≥0 => γ (q + t) := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t - q, show γ (q + (t - q)) = γ t by rw [add_tsub_cancel_of_le (mem_Ici.1 ht)]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨q + t, mem_Ici.2 le_self_add, rfl⟩
  rw [e]
  exact isClosed_range_of_tendsto hc ht

/-- **Near a prefix point off the other wall, the union is the prefix** ("The collar is free of all other portions,
by the two-arc geometry, compactness, and injectivity"): for an injective continuous transient path `γ`, a continuous
transient path `ρ`, `s < q` and `γ(s) ∉ ρ`, some ball about `γ(s)` meets `(γ ∪ ρ) ∩ ℍ` only in `γ([0, q]) ∩ ℍ`. -/
theorem exists_ball_inter_subset_prefix {γ ρ : ℝ≥0 → ℂ} (hγ : Continuous γ) (hγtr : Tendsto γ atTop (cobounded ℂ))
    (hγi : Injective γ) (hρ : Continuous ρ) (hρtr : Tendsto ρ atTop (cobounded ℂ)) {s q : ℝ≥0} (hsq : s < q)
    (hsρ : γ s ∉ range ρ) : ∃ r > 0, (range γ ∪ range ρ) ∩ H ∩ ball (γ s) r ⊆ γ '' Icc 0 q ∩ H := by
  have hK : IsClosed (γ '' Ici q ∪ range ρ) := (isClosed_image_Ici hγ hγtr q).union (isClosed_range_of_tendsto hρ hρtr)
  have hp : γ s ∉ γ '' Ici q ∪ range ρ := by
    rintro (⟨t, ht, he⟩ | h)
    · exact absurd (hγi he) (ne_of_gt (lt_of_lt_of_le hsq (mem_Ici.1 ht)))
    · exact hsρ h
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hK.isOpen_compl (γ s) hp
  refine ⟨r, hr, ?_⟩
  rintro z ⟨⟨hzγρ, hzH⟩, hzb⟩
  have hzK : z ∉ γ '' Ici q ∪ range ρ := hball hzb
  rcases hzγρ with ⟨t, rfl⟩ | hzρ
  · refine ⟨⟨t, ⟨zero_le, ?_⟩, rfl⟩, hzH⟩
    by_contra hlt
    exact hzK (Or.inl ⟨t, le_of_lt (not_le.1 hlt), rfl⟩)
  · exact absurd (Or.inr hzρ) hzK

end Geometry

/-! ### The complete wall union as a local set -/

section Union

variable {Ω : Type*}

/-- **The complete marked incoming union** of two walls: `(γ ∪ ρ) ∩ ℍ`. -/
def wallUnion (γ ρ : Ω → ℝ≥0 → ℂ) (ω : Ω) : Set ℂ := (range (γ ω) ∪ range (ρ ω)) ∩ H

theorem wallUnion_comm (γ ρ : Ω → ℝ≥0 → ℂ) : wallUnion γ ρ = wallUnion ρ γ :=
  funext fun ω => by rw [wallUnion, wallUnion, union_comm]

theorem H_diff_wallUnion (γ ρ : Ω → ℝ≥0 → ℂ) (ω : Ω) : H \ wallUnion γ ρ ω = H \ (range (γ ω) ∪ range (ρ ω)) := by
  ext z
  simp only [wallUnion, Set.mem_sdiff, mem_inter_iff, not_and]
  exact ⟨fun ⟨hz, h⟩ => ⟨hz, fun h' => h h' hz⟩, fun ⟨hz, h⟩ => ⟨hz, fun h' _ => h h'⟩⟩

/-- The union is the explored set of the two complete curves. -/
theorem wallUnion_eq_explored (γ ρ : Ω → ℝ≥0 → ℂ) :
    wallUnion γ ρ = Sec6.explored ![γ, ρ] (fun _ _ => ⊤) := by
  funext ω
  ext z
  simp only [wallUnion, Sec6.explored, mem_inter_iff, mem_union, mem_iUnion, mem_image, mem_range, le_top,
    ofPred_true, mem_univ, true_and, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → DistOn upperHalfPlaneOpens}

/-- **Lemma 6.2 for the complete union**: for two transient walls with Lemma 6.2's inputs, the complete union is a
local set, measurable for the hitting σ-algebra and almost surely determined by the field. -/
theorem isLocalSet_wallUnion (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {γ ρ : Ω → ℝ≥0 → ℂ}
    (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (X ω))
    (hγloc : Sec6.IsEntranceHistoryLocal γ X P)
    (hρc : ∀ ω, Continuous (ρ ω)) (hρ0 : ∀ ω, ρ ω 0 = 0) (hρm : ∀ t, Measurable fun ω => ρ ω t)
    (hρdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ρ ω t) =ᵐ[P] fun ω => f (X ω))
    (hρloc : Sec6.IsEntranceHistoryLocal ρ X P)
    (htr : ∀ᵐ ω ∂P, Tendsto (γ ω) atTop (cobounded ℂ) ∧ Tendsto (ρ ω) atTop (cobounded ℂ)) :
    Measurable[mΩ, hittingSigma] (wallUnion γ ρ) ∧ IsLocalSet (wallUnion γ ρ) X P ∧
      MeasurableSpace.comap (wallUnion γ ρ) hittingSigma ≤ aeSigma (MeasurableSpace.comap X inferInstance) P := by
  set η : Fin 2 → Ω → ℝ≥0 → ℂ := ![γ, ρ] with hη
  have hc : ∀ i ω, Continuous (η i ω) := fun i ω => by
    fin_cases i
    · exact hγc ω
    · exact hρc ω
  have h0 : ∀ i ω, η i ω 0 = (fun _ => (0 : ℂ)) i := fun i ω => by
    fin_cases i
    · exact hγ0 ω
    · exact hρ0 ω
  have hm : ∀ i t, Measurable fun ω => η i ω t := fun i t => by
    fin_cases i
    · exact hγm t
    · exact hρm t
  have hdet : ∀ i (t : ℝ≥0), ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => η i ω t) =ᵐ[P] fun ω => f (X ω) := fun i t => by
    fin_cases i
    · exact hγdet t
    · exact hρdet t
  have hloc : ∀ i, Sec6.IsEntranceHistoryLocal (η i) X P := fun i => by
    fin_cases i
    · exact hγloc
    · exact hρloc
  have hcl : ∀ᵐ ω ∂P, IsOpen (H \ Sec6.explored η (fun _ _ => (⊤ : ℝ≥0∞)) ω) := by
    filter_upwards [htr] with ω hω
    refine Sec6.isOpen_H_diff_explored (fun i => hc i ω) fun i => ?_
    fin_cases i
    · exact hω.1
    · exact hω.2
  have h := WangWu.isLocalSet_explored_and_aeDetermined (P := P) (η := η) (x := fun _ => (0 : ℂ))
    (τ := fun _ _ => (⊤ : ℝ≥0∞)) (S := fun _ _ _ => (⊤ : ℝ≥0∞)) hX hc h0 hm hdet hloc
    (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ => measurable_const) hcl
  rw [← wallUnion_eq_explored] at h
  refine ⟨?_, h.1, fun s hs => h.2 s hs⟩
  rw [wallUnion_eq_explored]
  exact Sec6.measurable_explored hc hm fun _ => measurable_const

omit [IsProbabilityMeasure P] in
/-- Every component of `(γ ∪ ρ) ∩ ℍ ∪ {Im ≤ 0}` is unbounded (the hypothesis of Proposition 3.8). -/
theorem ae_not_isBounded_lowerUnion_wallUnion {γ ρ : Ω → ℝ≥0 → ℂ} (hγc : ∀ ω, Continuous (γ ω))
    (hγ0 : ∀ ω, γ ω 0 = 0) (hγim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (γ ω t).im) (hρc : ∀ ω, Continuous (ρ ω))
    (hρ0 : ∀ ω, ρ ω 0 = 0) (hρim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (ρ ω t).im) :
    ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (wallUnion γ ρ ω),
      ¬ IsBounded (connectedComponentIn (lowerUnion (wallUnion γ ρ ω)) z) := by
  filter_upwards [hγim, hρim] with ω hγω hρω
  have h := Sec6.not_isBounded_lowerUnion_explored (η := ![γ, ρ]) (τ := fun _ _ => (⊤ : ℝ≥0∞)) (ω := ω)
    (fun i => by fin_cases i; exacts [hγc ω, hρc ω])
    (fun i => by fin_cases i <;> simp [hγ0, hρ0])
    (fun i t => by fin_cases i; exacts [hγω t, hρω t])
  rwa [← wallUnion_eq_explored] at h

end Union

/-! ### The nested comparison -/

section Nested

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : Ω → DistOn upperHalfPlaneOpens}

/-- **The nested comparison at one own time** (Proposition 3.8 for the complete union and a stopped prefix): almost
surely, for all harmonic representatives `v` of the union mean and `v_q` of the prefix mean, at every prefix point
`γ(s)`, `s < q`, in `ℍ` and off the other wall (`γ` injective), `v − v_q → 0` along `ℍ ∖ (γ ∪ ρ)`. -/
theorem ae_tendsto_sub_prefix (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {γ ρ : Ω → ℝ≥0 → ℂ}
    (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (X ω))
    (hγloc : Sec6.IsEntranceHistoryLocal γ X P) (hγim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (γ ω t).im)
    (hρc : ∀ ω, Continuous (ρ ω)) (hρ0 : ∀ ω, ρ ω 0 = 0) (hρm : ∀ t, Measurable fun ω => ρ ω t)
    (hρdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ρ ω t) =ᵐ[P] fun ω => f (X ω))
    (hρloc : Sec6.IsEntranceHistoryLocal ρ X P) (hρim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (ρ ω t).im)
    (htr : ∀ᵐ ω ∂P, Tendsto (γ ω) atTop (cobounded ℂ) ∧ Tendsto (ρ ω) atTop (cobounded ℂ))
    {gU : Ω → DistOn upperHalfPlaneOpens} (hgU : IsLocalSetMean (wallUnion γ ρ) X P gU) (q : ℝ≥0)
    {gq : Ω → DistOn upperHalfPlaneOpens} (hgq : IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) X P gq) :
    ∀ᵐ ω ∂P, ∀ v vq : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion γ ρ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion γ ρ ω → gU ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vq (H \ (γ ω '' Icc 0 q ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 q ∩ H) → gq ω φ = ∫ z, vq z * φ z) →
      Injective (γ ω) → ∀ s : ℝ≥0, s < q → γ ω s ∈ H → γ ω s ∉ range (ρ ω) →
        Tendsto (fun z => v z - vq z) (𝓝[H \ wallUnion γ ρ ω] (γ ω s)) (𝓝 0) := by
  obtain ⟨hUm, hUloc, hUdet⟩ := isLocalSet_wallUnion hX hγc hγ0 hγm hγdet hγloc hρc hρ0 hρm hρdet hρloc htr
  obtain ⟨hBloc, hBdet⟩ := RS133.isLocalSet_range_and_aeDetermined hX hγc hγ0 hγm hγdet hγloc q
  have h := SideHeightBox.ae_tendsto_sub_of_locals hX hUm (StripMark.measurable_range hγc hγm q) hUloc hBloc hUdet
    hBdet (ae_not_isBounded_lowerUnion_wallUnion hγc hγ0 hγim hρc hρ0 hρim)
    (RS133.ae_not_isBounded_lowerUnion_range hγc hγ0 hγim q) hgU hgq
  filter_upwards [h, htr] with ω hω hωtr v vq hv hgv hvq hgvq hinj s hsq hsH hsρ
  have hBU : γ ω '' Icc 0 q ∩ H ⊆ wallUnion γ ρ ω := fun z ⟨⟨t, _, ht⟩, hzH⟩ => ⟨Or.inl ⟨t, ht⟩, hzH⟩
  have hpU : γ ω s ∈ wallUnion γ ρ ω := ⟨Or.inl ⟨s, rfl⟩, hsH⟩
  have hpB : γ ω s ∈ γ ω '' Icc 0 q ∩ H := ⟨⟨s, ⟨zero_le, hsq.le⟩, rfl⟩, hsH⟩
  obtain ⟨r, hr, hball⟩ := exists_ball_inter_subset_prefix (hγc ω) hωtr.1 hinj (hρc ω) hωtr.2 hsq hsρ
  have key := hω v vq hv hgv hvq hgvq (γ ω s) (Or.inl hpU) (Or.inl hpB)
    ⟨1, one_pos, fun z hz => hBU hz.1⟩ ⟨r, hr, hball⟩
  rwa [union_eq_left.2 hBU] at key

/-- **The nested comparisons at all rational own times, on one probability-one event** ("Choose the own times from a
countable rational family before selecting a suitable one on a realization. This gives all the boundary identities
simultaneously on one event of probability one"). -/
theorem ae_tendsto_sub_prefix_rat (hX : IsZeroBoundaryGFF upperHalfPlaneOpens X P) {γ ρ : Ω → ℝ≥0 → ℂ}
    (hγc : ∀ ω, Continuous (γ ω)) (hγ0 : ∀ ω, γ ω 0 = 0) (hγm : ∀ t, Measurable fun ω => γ ω t)
    (hγdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => γ ω t) =ᵐ[P] fun ω => f (X ω))
    (hγloc : Sec6.IsEntranceHistoryLocal γ X P) (hγim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (γ ω t).im)
    (hρc : ∀ ω, Continuous (ρ ω)) (hρ0 : ∀ ω, ρ ω 0 = 0) (hρm : ∀ t, Measurable fun ω => ρ ω t)
    (hρdet : ∀ t : ℝ≥0, ∃ f : DistOn upperHalfPlaneOpens → ℂ, Measurable f ∧
      (fun ω => ρ ω t) =ᵐ[P] fun ω => f (X ω))
    (hρloc : Sec6.IsEntranceHistoryLocal ρ X P) (hρim : ∀ᵐ ω ∂P, ∀ t, 0 ≤ (ρ ω t).im)
    (htr : ∀ᵐ ω ∂P, Tendsto (γ ω) atTop (cobounded ℂ) ∧ Tendsto (ρ ω) atTop (cobounded ℂ))
    {gU : Ω → DistOn upperHalfPlaneOpens} (hgU : IsLocalSetMean (wallUnion γ ρ) X P gU)
    {gq : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    (hgq : ∀ q : ℝ≥0, IsLocalSetMean (fun ω => γ ω '' Icc 0 q ∩ H) X P (gq q)) :
    ∀ᵐ ω ∂P, ∀ q : ℚ≥0, ∀ v vq : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ wallUnion γ ρ ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ wallUnion γ ρ ω → gU ω φ = ∫ z, v z * φ z) →
      InnerProductSpace.HarmonicOnNhd vq (H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H)) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (γ ω '' Icc 0 (q : ℝ≥0) ∩ H) →
        gq q ω φ = ∫ z, vq z * φ z) →
      Injective (γ ω) → ∀ s : ℝ≥0, s < q → γ ω s ∈ H → γ ω s ∉ range (ρ ω) →
        Tendsto (fun z => v z - vq z) (𝓝[H \ wallUnion γ ρ ω] (γ ω s)) (𝓝 0) :=
  ae_all_iff.2 fun q => ae_tendsto_sub_prefix hX hγc hγ0 hγm hγdet hγloc hγim hρc hρ0 hρm hρdet hρloc hρim htr
    hgU (q : ℝ≥0) (hgq q)

end Nested

/-! ### Restriction to the change pocket -/

section Pocket

open PocketCoord

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

/-- The change pocket lies off the complete union of its walls. -/
theorem changePocket_subset_H_diff (h : IsChangeConfigInc R L r) :
    changePocket R L r ⊆ H \ (range L ∪ range R) := fun z hz => by
  obtain ⟨hzH, hz⟩ := h.changePocket_subset hz
  exact ⟨hzH, fun hm => hz (hm.elim Or.inr Or.inl)⟩

/-- **The nested comparison along the change pocket's approach to a left-wall point.** -/
theorem tendsto_sub_changePocket_left (h : IsChangeConfigInc R L r) {v w : ℂ → ℝ} {p : ℂ}
    (hcmp : Tendsto (fun z => v z - w z) (𝓝[H \ (range L ∪ range R)] p) (𝓝 0)) :
    Tendsto (fun z => v z - w z) (𝓝[changePocket R L r] p) (𝓝 0) :=
  hcmp.mono_left (nhdsWithin_mono _ (changePocket_subset_H_diff h))

/-- **The nested comparison along the change pocket's approach to a right-wall point.** -/
theorem tendsto_sub_changePocket_right (h : IsChangeConfigInc R L r) {v w : ℂ → ℝ} {p : ℂ}
    (hcmp : Tendsto (fun z => v z - w z) (𝓝[H \ (range R ∪ range L)] p) (𝓝 0)) :
    Tendsto (fun z => v z - w z) (𝓝[changePocket R L r] p) (𝓝 0) := by
  rw [union_comm] at hcmp
  exact tendsto_sub_changePocket_left h hcmp

end Pocket

end InteractingSLE.Sec7.Aux119Nested

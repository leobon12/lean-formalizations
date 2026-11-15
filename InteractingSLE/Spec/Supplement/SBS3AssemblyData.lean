/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3AdvanceMain
import InteractingSLE.Spec.Supplement.SBS3AssemblyWord
import InteractingSLE.Spec.Sec7.ReverseArcLift

/-!
# S3: protected word, marked means, and both canonical phases

The data below keep the distributional representatives and the transition-hull
gaps explicit. The two zero phases are consequences of Aux. 57; they are not
fields of the data. Constructing these data from the retained histories is a
separate mathematical obligation, as is identifying the word's schedule label.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open InteractingSLE.Restart

namespace InteractingSLE.Theorem14.SB.S3

/-- Harmonic representatives of two single means and their differences from
one common union mean. The zero boundary limits refer to that same union. -/
structure MarkedUnionMeans (A₁ A₂ O : Set ℂ) (p : ℂ) (v₁ v₂ : ℂ → ℝ) : Prop where
  open_domain : IsOpen O
  domain_old : O ⊆ H \ A₁
  domain_second : O ⊆ H \ A₂
  representatives : ∃ (G G₁ G₂ : DistOn upperHalfPlaneOpens) (ua ub : ℂ → ℝ),
    InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁) ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ →
      G₁ φ = ∫ z, v₁ z * φ z) ∧
    InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂) ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ →
      G₂ φ = ∫ z, v₂ z * φ z) ∧
    InnerProductSpace.HarmonicOnNhd ua O ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      G φ - G₁ φ = ∫ z, ua z * φ z) ∧
    InnerProductSpace.HarmonicOnNhd ub O ∧
    (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      G φ - G₂ φ = ∫ z, ub z * φ z) ∧
    Tendsto ua (𝓝[O] p) (𝓝 0) ∧ Tendsto ub (𝓝[O] p) (𝓝 0)

/-- Compare the two representatives on any chosen protected approach. -/
theorem MarkedUnionMeans.tendsto_sub {A₁ A₂ O : Set ℂ} {p : ℂ} {v₁ v₂ : ℂ → ℝ}
    (h : MarkedUnionMeans A₁ A₂ O p v₁ v₂) {F : Filter ℂ} (hF : F ≤ 𝓝[O] p) :
    Tendsto (fun z => v₁ z - v₂ z) F (𝓝 0) := by
  obtain ⟨G, G₁, G₂, ua, ub, hv₁, hr₁, hv₂, hr₂, hua, hra, hub, hrb, ha, hb⟩ :=
    h.representatives
  exact (Sec7.tendsto_sub_of_union_means h.open_domain h.domain_old h.domain_second
    hv₁ hr₁ hv₂ hr₂ hua hra hub hrb ha hb).mono_left hF

/-- The geometric hypotheses for comparing two canonical derivative logs
through the same joint hull. In particular, the second path has its own
transition gap and its own mapping-out limit; the old gap does not imply it. -/
structure JointPhaseGaps (A₁ A₂ B : Set ℂ) (F : Filter ℂ) (L₁ L₂ : ℂ → ℂ) : Prop where
  hull_old : IsHPHull A₁
  hull_second : IsHPHull A₂
  hull_joint : IsHPHull B
  old_subset : A₁ ⊆ B
  second_subset : A₂ ⊆ B
  in_domain : F ≤ 𝓟 (H \ B)
  charts : ∃ (g₁ g₂ gB LB : ℂ → ℂ) (x₁ x₂ r₁ r₂ : ℝ),
    IsMapOut A₁ g₁ ∧ IsMapOut A₂ g₂ ∧ IsMapOut B gB ∧
    IsCanonicalDerivLog A₁ g₁ L₁ ∧ IsCanonicalDerivLog A₂ g₂ L₂ ∧
    IsCanonicalDerivLog B gB LB ∧ 0 < r₁ ∧ 0 < r₂ ∧
    Disjoint (ball (x₁ : ℂ) r₁) (g₁ '' (B \ A₁)) ∧
    Disjoint (ball (x₂ : ℂ) r₂) (g₂ '' (B \ A₂)) ∧
    Tendsto g₁ F (𝓝[H] (x₁ : ℂ)) ∧ Tendsto g₂ F (𝓝[H] (x₂ : ℂ))

/-- Both exact zero transitions give equality of inherited phases on the
selected filter, even when the physical contact has several prime ends. -/
theorem JointPhaseGaps.tendsto_sub {A₁ A₂ B : Set ℂ} {F : Filter ℂ}
    {L₁ L₂ : ℂ → ℂ} (h : JointPhaseGaps A₁ A₂ B F L₁ L₂) :
    Tendsto (fun z => (L₁ z).im - (L₂ z).im) F (𝓝 0) := by
  obtain ⟨g₁, g₂, gB, LB, x₁, x₂, r₁, r₂, hg₁, hg₂, hgB,
    hL₁, hL₂, hLB, hr₁, hr₂, hd₁, hd₂, hq₁, hq₂⟩ := h.charts
  have h₁ := Sec7.ReverseArc.tendsto_im_sub_of_le h.hull_old h.hull_joint
    h.old_subset hg₁ hgB hL₁ hLB h.in_domain hr₁ hd₁ hq₁
  have h₂ := Sec7.ReverseArc.tendsto_im_sub_of_le h.hull_second h.hull_joint
    h.second_subset hg₂ hgB hL₂ hLB h.in_domain hr₂ hd₂ hq₂
  have hdiff := h₂.sub h₁
  simp only [sub_self] at hdiff
  exact hdiff.congr fun z => by ring

/-- A protected comparison at a compact physical common arc. The word and
its unmarked coordinate are retained explicitly. The label is deliberately
absent: constancy of a finite word does not establish its schedule genealogy.
The means here are distributional comparison data; this structure alone does
not assert that they are the local-set means of a particular random field. -/
structure ProtectedWordComparison (κ target : ℝ) (A : Set ℂ) (β : ℝ≥0 → ℂ)
    (a b : ℝ≥0) where
  point : ℂ
  approach : Filter ℂ
  point_mem : point ∈ β '' Ioo a b
  nontrivial : approach.NeBot
  joint_domain : approach ≤ 𝓝[H \ fillH (A ∪ β '' Icc 0 b)] point
  word : BoundaryWord
  coordinate : ℝ
  old_mean : ℂ → ℝ
  second_mean : ℂ → ℝ
  background : ℂ → ℝ
  old_log : ℂ → ℂ
  second_log : ℂ → ℂ
  comparison_domain : Set ℂ
  approach_domain : approach ≤ 𝓝[comparison_domain] point
  means : MarkedUnionMeans (fillH A) (fillH (β '' Icc 0 b)) comparison_domain
    point old_mean second_mean
  phases : JointPhaseGaps (fillH A) (fillH (β '' Icc 0 b))
    (fillH (A ∪ β '' Icc 0 b)) approach old_log second_log
  old_readout : IsChartWordMean κ word coordinate approach old_mean background old_log
  second_readout : ∃ (word₂ : BoundaryWord) (x₂ : ℝ),
    IsChartWordMean κ word₂ x₂ approach second_mean background second_log ∧ word₂.fn x₂ = target

/-- The old side limit is derived from its canonical word readout. -/
theorem ProtectedWordComparison.old_side {κ target : ℝ} {A : Set ℂ}
    {β : ℝ≥0 → ℂ} {a b : ℝ≥0} (d : ProtectedWordComparison κ target A β a b) :
    Tendsto (fun z => d.old_mean z + d.background z + chiC κ * (d.old_log z).im)
      d.approach (𝓝 (d.word.fn d.coordinate)) :=
  d.old_readout.tendsto

/-- The second side limit is derived from its unmarked word readout and
the specified exposed-side label. -/
theorem ProtectedWordComparison.second_side {κ target : ℝ} {A : Set ℂ}
    {β : ℝ≥0 → ℂ} {a b : ℝ≥0} (d : ProtectedWordComparison κ target A β a b) :
    Tendsto (fun z => d.second_mean z + d.background z + chiC κ * (d.second_log z).im)
      d.approach (𝓝 target) := by
  obtain ⟨word₂, x₂, hread, hvalue⟩ := d.second_readout
  have h := hread.tendsto
  rw [hvalue] at h
  exact h

/-- The marked union comparison and the two gap-derived phases identify the
actual word value with the exposed second-side value. -/
theorem ProtectedWordComparison.word_value_eq {κ target : ℝ} {A : Set ℂ}
    {β : ℝ≥0 → ℂ} {a b : ℝ≥0} (d : ProtectedWordComparison κ target A β a b) :
    d.word.fn d.coordinate = target := by
  let _ : d.approach.NeBot := d.nontrivial
  exact Sec7.eq_of_side_limits (d.means.tendsto_sub d.approach_domain)
    d.phases.tendsto_sub d.old_side d.second_side

/-- Assemble the earlier rational S3 interface from explicit word, marked
mean and geometric phase data, once the canonical label has been supplied. -/
theorem ProtectedWordComparison.hasJointSideComparison {κ ϑ : ℝ} {l : List (ℝ × ℝ≥0)}
    {A : Set ℂ} {β : ℝ≥0 → ℂ} {a b : ℝ≥0}
    (d : ProtectedWordComparison κ (-sleLambda κ - ϑ * chiC κ) A β a b)
    (hlabel : Lh.SideH κ l (d.word.fn d.coordinate)) :
    HasJointSideComparison κ ϑ l A β a b := by
  exact ⟨d.point, d.approach, d.old_mean, d.second_mean, d.background,
    (fun z => (d.old_log z).im), (fun z => (d.second_log z).im),
    d.word.fn d.coordinate, d.point_mem, d.nontrivial, d.joint_domain, hlabel,
    d.means.tendsto_sub d.approach_domain, d.phases.tendsto_sub, d.old_side, d.second_side⟩

end InteractingSLE.Theorem14.SB.S3

import SupercriticalLQGUniqueness.B2.PfeAxioms.LocalObservableLocalizedLimit

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

def countableLocalizedObservable
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (V : ℕ → Set ℂ) (x y : ℂ)
    (hx : ∀ n, x ∈ V n) (hy : ∀ n, y ∈ V n) :
    DistC → ℝ≥0∞ :=
  fun g => ⨅ n : ℕ, lowerLocalizedNeighborhoodObservable ξ
    ε (fun k => m (ε k)) (V := V n) ⟨x, hx n⟩ ⟨y, hy n⟩ g

theorem measurable_countableLocalizedObservable
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (V : ℕ → Set ℂ) (x y : ℂ)
    (hx : ∀ n, x ∈ V n) (hy : ∀ n, y ∈ V n)
    (hopen : ∀ n, IsOpen (V n))
    (hbounded : ∀ n, Bornology.IsBounded (V n)) :
    Measurable (countableLocalizedObservable ξ m ε V x y hx hy) := by
  unfold countableLocalizedObservable
  apply Measurable.iInf
  intro n
  exact measurable_lowerLocalizedNeighborhoodObservable ξ
    ε (fun k => m (ε k)) (hopen n) (hbounded n)
    ⟨x, hx n⟩ ⟨y, hy n⟩

 

theorem joint_law_internal_countableLocalized_of_smallAnnulusCosts
    (hStrong : Inputs.DG20LimitStrongSB)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    {U : Set ℂ} (H : CompactExhaustion U) (x y : U)
    (W V : ℕ → Set ℂ)
    (hgeo : ∀ n,
      IsOpen (W n) ∧ IsCompact (closure (W n)) ∧
      closure (W n) ⊆ U ∧
      (H n).image Subtype.val ⊆ W n ∧
      (x : ℂ) ∈ W n ∧ (y : ℂ) ∈ W n ∧
      IsOpen (V n) ∧ IsCompact (closure (V n)) ∧
      closure (V n) ⊆ U ∧ closure (W n) ⊆ V n ∧
      IsCompact (frontier (V n)) ∧
      (frontier (V n)).Nonempty ∧
      Disjoint (closure (W n)) (frontier (V n)))
    (hsmall : ∀ᵐ ω ∂P, ∀ n,
      PfeWeyl.SmallAnnulusCosts
        (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
          (m (ε k)) (X (ε k) ω))
        (D (h ω)) (closure (W n)) (V n)) :
    ∃ (F : DistC → ℝ≥0∞), Measurable F ∧
      P.map (fun ω => (h ω, (D (h ω)).internal U (x, y))) =
        P.map (fun ω => (h ω, F (h ω))) := by
  have hxV : ∀ n, (x : ℂ) ∈ V n := fun n =>
    (hgeo n).2.2.2.2.2.2.2.2.2.1
      (subset_closure (hgeo n).2.2.2.2.1)
  have hyV : ∀ n, (y : ℂ) ∈ V n := fun n =>
    (hgeo n).2.2.2.2.2.2.2.2.2.1
      (subset_closure (hgeo n).2.2.2.2.2.1)
  let F := countableLocalizedObservable ξ m ε V x y hxV hyV
  refine ⟨F, ?_, ?_⟩
  · exact measurable_countableLocalizedObservable ξ m ε V x y hxV hyV
      (fun n => (hgeo n).2.2.2.2.2.2.1)
      (fun n => (hgeo n).2.2.2.2.2.2.2.1.isBounded.subset subset_closure)
  · apply Measure.map_congr
    filter_upwards [ae_internal_eq_countable_localized_observable_of_smallAnnulusCosts
      hStrong ξ Q hQ m hm ε hε D hD P h hh X hX H x y W V hgeo hsmall]
      with ω hω
    exact congrArg (fun d : ℝ≥0∞ => (h ω, d)) hω

 

theorem comap_countableLocalizedObservable_le_fieldSigma
    {Ω : Type} [MeasurableSpace Ω]
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (V : ℕ → Set ℂ) (x y : ℂ)
    (hx : ∀ n, x ∈ V n) (hy : ∀ n, y ∈ V n)
    (hopen : ∀ n, IsOpen (V n))
    (hbounded : ∀ n, Bornology.IsBounded (V n))
    (hcompact : ∀ n, IsCompact (closure (V n)))
    (O : TopologicalSpace.Opens ℂ)
    (hVO : ∀ n, closure (V n) ⊆ O)
    (Y : Ω → DistC) :
    MeasurableSpace.comap
      (fun ω => countableLocalizedObservable ξ m ε V x y hx hy (Y ω))
      inferInstance ≤ LQGMetric.Blueprint.fieldSigma Y O := by
  let mΩ := LQGMetric.Blueprint.fieldSigma Y O
  have hcomponent (n : ℕ) :
      Measurable[mΩ]
        (fun ω => lowerLocalizedNeighborhoodObservable ξ
          ε (fun k => m (ε k))
          (⟨x, hx n⟩ : V n) ⟨y, hy n⟩ (Y ω)) := by
    apply (comap_measurable _).mono
    · exact comap_lowerLocalizedNeighborhoodObservable_le_fieldSigma_of_compact
        ξ ε (fun k => m (ε k)) hε (hopen n) (hbounded n)
        (hcompact n) O (hVO n) ⟨x, hx n⟩ ⟨y, hy n⟩ Y
    · exact le_rfl
  have hF : Measurable[mΩ]
      (fun ω => countableLocalizedObservable ξ m ε V x y hx hy (Y ω)) := by
    change Measurable[mΩ]
      (fun ω => ⨅ n, lowerLocalizedNeighborhoodObservable ξ
        ε (fun k => m (ε k))
        (⟨x, hx n⟩ : V n) ⟨y, hy n⟩ (Y ω))
    exact Measurable.iInf hcomponent
  exact hF.comap_le

end SupercriticalLQGUniqueness.B2.PfeAxioms

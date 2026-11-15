/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB3ProofTop
import InteractingSLE.Spec.Supplement.SB3ProofMeas
import InteractingSLE.Spec.Supplement.GW1PieceSimpleProof

/-!
# Physical switch certificates and measurable conditional-law transfer

The source compares available upper prefixes with every finite lower prefix under
the retained conditional law (SB4, pp. 634–635). The deterministic final certificate
is the landed SB3 topology theorem; it does not require a maximal upper lifetime.
Rational evaluations of continuous physical pieces make the avoidance event
null-measurable, so conditional conclusions can be lifted without the R51 defect.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB

/-- A physical set is read through a relative upper path which has the S1
comparison with every finite prefix of a proper relative lower walk. The final
implication is the geometric side correspondence of the physical chart. -/
def HasSewnSideCertificate (A S : Set ℂ) : Prop :=
  ∃ (γ η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (u : ℝ) (g : ℂ → ℂ),
    Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ u ≤ 0 ∧ η 0 = u ∧
    ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ} ∧
    (∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
      IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) η a) ∧
    A ⊆ g '' (η '' {t | (t : ℝ≥0∞) ≤ ζ}) ∧
    ∀ z ∈ η '' {t | (t : ℝ≥0∞) ≤ ζ}, g z ∈ S → z ∈ rightSideOf (range γ)

/-- The SB3 crossing certificate handles a stopped new piece, including its
available endpoint; no extension to a maximal flow line is needed here. -/
theorem HasSewnSideCertificate.avoids {A S : Set ℂ}
    (h : HasSewnSideCertificate A S) : A ∩ S = ∅ := by
  obtain ⟨γ, η, ζ, u, g, hγ, hγ0, hu, hη0, hη, hS1, hA, hside⟩ := h
  have hav := sb3TopologyStatement γ η ζ u hγ hγ0 hu hη0 hη hS1
  refine eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨w, hw, hwz⟩ := hA hz.1
  have hbad := hside w hw (hwz.symm ▸ hz.2)
  exact (eq_empty_iff_forall_notMem.1 hav) w ⟨hw, hbad⟩

/-- A finite regular simple piece has a continuous parametrization on all of
`ℝ≥0`, obtained by freezing its available parametrization at its endpoint. -/
theorem _root_.InteractingSLE.Theorem14.GW1Z.IsSimplePiece.exists_continuous_param {c : Chart} {W : ℝ≥0 → ℝ}
    {T : ℝ≥0∞} {A : Set ℂ} (h : GW1Z.IsSimplePiece c W T A) (hT : T ≠ ⊤) :
    ∃ f : ℝ≥0 → ℂ, Continuous f ∧
      range f = c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) T).toNNReal) T := by
  obtain ⟨g, hgc, _, hgr, _, _, _⟩ := h.exists_param
  have hmem : ∀ t : ℝ≥0, ((min t T.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ T := fun t => by
    exact (ENNReal.coe_le_coe.2 (min_le_right t T.toNNReal)).trans
      (le_of_eq (ENNReal.coe_toNNReal hT))
  refine ⟨fun t => g (min t T.toNNReal),
    hgc.comp_continuous (continuous_id.min continuous_const) hmem, ?_⟩
  rw [← hgr]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨min t T.toNNReal, hmem t, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : t ≤ T.toNNReal := by
      have he : (t : ℝ≥0∞) ≤ (T.toNNReal : ℝ≥0∞) := by
        rw [ENNReal.coe_toNNReal hT]
        exact ht
      exact ENNReal.coe_le_coe.1 he
    exact ⟨t, congrArg g (min_eq_left ht')⟩

/-- For a continuous frozen piece, avoiding an open side is a countable condition. -/
theorem range_avoids_open_iff_rat {a : ℝ≥0 → ℂ} {S : Set ℂ}
    (ha : Continuous a) (hS : IsOpen S) :
    range a ∩ S = ∅ ↔ ∀ q : ℚ, a (q : ℝ).toNNReal ∉ S := by
  constructor
  · intro h q hq
    exact (eq_empty_iff_forall_notMem.1 h) _ ⟨mem_range_self _, hq⟩
  · intro h
    have hall : ∀ t : ℝ, a t.toNNReal ∉ S :=
      isClosed_property Rat.denseRange_cast
        (hS.isClosed_compl.preimage (ha.comp continuous_real_toNNReal)) h
    refine eq_empty_of_forall_notMem ?_
    rintro z ⟨⟨t, rfl⟩, ht⟩
    have hnot : a t ∉ S := by
      simpa only [Real.toNNReal_coe] using hall (t : ℝ)
    exact hnot ht

/-- Rational point/side incidence makes the frozen-piece avoidance event measurable. -/
theorem measurableSet_rat_avoidance {Ω : Type*} [MeasurableSpace Ω]
    {a : Ω → ℝ≥0 → ℂ} {S : Ω → Set ℂ}
    (hm : ∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) :
    MeasurableSet {ω | ∀ q : ℚ, a ω (q : ℝ).toNNReal ∉ S ω} := by
  rw [ofPred_forall]
  exact MeasurableSet.iInter fun q => (hm q).compl

/-- Almost-sure continuous parametrizations suffice: the actual set need not have
been regularized at every sample. The launch event is retained explicitly. -/
theorem nullMeasurableSet_piece_avoidance {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : Set Ω} (hF : NullMeasurableSet F P)
    {A S : Ω → Set ℂ} {a : Ω → ℝ≥0 → ℂ}
    (hm : ∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω})
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) :
    NullMeasurableSet {ω | ω ∈ F → A ω ∩ S ω = ∅} P := by
  have hB : NullMeasurableSet {ω | ω ∈ F → ∀ q : ℚ, a ω (q : ℝ).toNNReal ∉ S ω} P := by
    have he : {ω | ω ∈ F → ∀ q : ℚ, a ω (q : ℝ).toNNReal ∉ S ω} =
        Fᶜ ∪ {ω | ∀ q : ℚ, a ω (q : ℝ).toNNReal ∉ S ω} := by
      ext ω
      exact imp_iff_not_or
    rw [he]
    exact hF.compl.union (measurableSet_rat_avoidance hm).nullMeasurableSet
  refine hB.congr ?_
  filter_upwards [hreg] with ω hω
  apply propext
  constructor
  · intro h hωF
    obtain ⟨hc, ho, he⟩ := hω hωF
    rw [he]
    exact (range_avoids_open_iff_rat hc ho).2 (h hωF)
  · intro h hωF
    obtain ⟨hc, ho, he⟩ := hω hωF
    exact (range_avoids_open_iff_rat hc ho).1 (he ▸ h hωF)

/-- Conditional S1 comparisons and physical side transport lift to the ambient
piece once its rational incidence events and continuous parametrization are known. -/
theorem ae_piece_avoids_of_kernel_certificate {Ω : Type*} {𝒢 : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ) {F : Set Ω} (hF : NullMeasurableSet F P)
    {A S : Ω → Set ℂ} {a : Ω → ℝ≥0 → ℂ}
    (hm : ∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω})
    (hreg : ∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω))
    (hcert : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀),
      ω ∈ F → HasSewnSideCertificate (A ω) (S ω)) :
    ∀ᵐ ω ∂P, ω ∈ F → A ω ∩ S ω = ∅ := by
  apply ae_of_ae_condExpKernel_of_nullMeasurableSet h𝒢
    (nullMeasurableSet_piece_avoidance hF hm hreg)
  filter_upwards [hcert] with ω₀ hω₀
  exact hω₀.mono fun ω hω hωF => (hω hωF).avoids

end InteractingSLE.Theorem14.SB

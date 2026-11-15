/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS5Proof

/-!
# The upper-half-plane form of the side comparison in Lemma S5

The first relative prefix in the source (supplement p. 583) has a proper
completion. We retain its resulting half-plane condition in the intermediate
side statement, and derive the source-facing `S5Statement` from this corrected
intermediate statement.

Old-range preservation away from the terminal junction and transport of real
boundary points are proved. The junction germ and interior conformal transport
remain the explicit inputs `S5JunctionGermStatement` and
`S5InteriorTransportStatement`; the final assembly theorem is conditional on them.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H)
open InteractingSLE.Supp9B

namespace InteractingSLE.Theorem14.SB

/-- S5's physical side comparison with the relative first prefix restricted to
the closed upper half-plane, as supplied by its proper completion. -/
def S5SideUpperStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β β' : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsProperCompletion β a₂ β' →
    p '' Icc 0 1 ⊆ closedRightSide β' →
    ∀ (c : Chart) (g : ℂ → ℂ), IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c →
      ContinuousOn g {z | 0 ≤ z.im} → EqOn g c.2.1 H →
      (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) →
    ∀ (tL a₁ : ℝ≥0) (aR bt : ℝ≥0 → ℂ), tL ≤ a₂ → β tL = realMin (p '' Icc 0 1) →
      IsProperCurve bt → bt 0 = 0 → (∀ s ≤ a₂ - tL, g (bt s) = β (tL + s)) →
      (∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) →
      (∀ s ∈ Icc 0 a₁, 0 ≤ (aR s).im) → aR '' Icc 0 a₁ ⊆ closedRightSide bt →
      p '' Icc 0 1 ∪ g '' (aR '' Icc 0 a₁) ⊆ closedRightSide (gluedCurve β' g bt tL)

/-- The half-plane condition of the corrected helper follows from the proper
completion already required by `S5Statement`. -/
theorem s5Statement_of_sideUpper (hS : S5SideUpperStatement) : S5Statement := by
  intro p β a₂ hp hp0 hpH hβ0 hS1 c g hc hgc hgi hgf
    tL a₁ aR bR w htL hβtL hbR0 hbR hw haR0 hord
  have haRH : ∀ s ∈ Icc 0 a₁, 0 ≤ (aR s).im := by
    obtain ⟨alpha, _, hat, _, _⟩ := hord
    intro s hs
    rw [← hat.2.2.2.2 s hs.2]
    exact hat.2.2.1 s
  obtain ⟨β', hβ', hA⟩ := hS1
  obtain ⟨bt, hbt, hbt0, hreal, _, haR⟩ := exists_leftShift_of_ordered hbR0 hw haR0 hord
  have hbtP : IsProperCurve bt := isProperCurve_of_isProperCompletion hbt
  have hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s) := fun s hs => by
    rw [hbt.2.2.2.2 s hs]
    exact hbR s hs
  exact ⟨gluedCurve β' g bt tL,
    isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi htL hβtL hbtP hbtβ hreal,
    hS p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi hgf
      tL a₁ aR bt htL hβtL hbtP hbt0 hbtβ hreal haRH haR⟩

/-- Closed right sides are complements of the open left sides. -/
theorem s5_closedRightSide_eq_compl {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ)
    (h0 : (γ 0).im = 0) : closedRightSide γ = (leftSide γ)ᶜ := by
  ext z
  constructor
  · rintro (hz | hz) hleft
    · exact Set.disjoint_left.1 (disjoint_leftSide_rightSide hγ h0) hleft hz
    · exact connectedComponentIn_subset _ _ hleft hz
  · intro hz
    by_cases hseed : z ∈ seedRayClosure γ
    · exact Or.inr hseed
    · have hs : z ∈ leftSide γ ∪ rightSide γ :=
        (compl_seedRayClosure_eq hγ h0) ▸ hseed
      exact Or.inl (hs.resolve_left hz)

theorem s5_isClosed_closedRightSide {γ : ℝ≥0 → ℂ} (hγ : IsProperCurve γ)
    (h0 : (γ 0).im = 0) : IsClosed (closedRightSide γ) := by
  rw [s5_closedRightSide_eq_compl hγ h0]
  exact (isOpen_leftSide' hγ).isClosed_compl

/-- Transport on the open half-plane and the relative curve suffices on the
entire closed half-plane. Real points off the curve are approached vertically
within its open right side; real curve points use the curve correspondence. -/
theorem s5_image_right_upper_of_interior {bt Γ : ℝ≥0 → ℂ} {g : ℂ → ℂ}
    (hbt : IsProperCurve bt) (hbt0 : bt 0 = 0) (hΓ : IsProperCurve Γ)
    (hΓ0 : Γ 0 = 0) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hcurve : ∀ t, g (bt t) ∈ closedRightSide Γ)
    (hinterior : ∀ w ∈ rightSide bt ∩ H, g w ∈ closedRightSide Γ) :
    g '' (closedRightSide bt ∩ {w | 0 ≤ w.im}) ⊆ closedRightSide Γ := by
  rintro _ ⟨w, ⟨hwR, hwH⟩, rfl⟩
  rcases hwR with hwR | hwcurve
  · rcases (show 0 ≤ w.im from hwH).lt_or_eq with hpos | hzero
    · exact hinterior w ⟨hwR, hpos⟩
    · have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hw] at hwR ⊢
      have hevent : ∀ᶠ y : ℝ in 𝓝[>] 0,
          (w.re : ℂ) + (y : ℂ) * I ∈ rightSide bt :=
        ((tendsto_vertical_nhdsWithin_H w.re).mono_right nhdsWithin_le_nhds).eventually
          ((isOpen_rightSide' hbt).mem_nhds hwR)
      refine (s5_isClosed_closedRightSide hΓ (by rw [hΓ0]; rfl)).mem_of_tendsto
        (tendsto_g_vertical hgc w.re) ?_
      filter_upwards [hevent, self_mem_nhdsWithin] with y hyR hy
      exact hinterior _ ⟨hyR, by simpa [QuantumZipper.H] using hy⟩
  · rcases hwcurve with ⟨t, rfl⟩ | ⟨hre, him⟩
    · exact hcurve t
    · have hw : w = bt 0 := by
        apply Complex.ext hre
        rw [hbt0] at him ⊢
        exact le_antisymm him hwH
      rw [hw]
      exact hcurve 0

/-- Side preservation away from the terminal junction follows from the existing
local side principle. A relative neighborhood at the junction suffices for a
connected old range, even when that range returns to the junction many times. -/
theorem s5_oldRange_of_junction_germ {A : Set ℂ} {γ₁ γ₂ : ℝ≥0 → ℂ} {a : ℝ≥0}
    (hAc : IsPreconnected A) (hA0 : (0 : ℂ) ∈ A) (hAH : ∀ z ∈ A, 0 ≤ z.im)
    (h₁ : IsProperCurve γ₁) (h₂ : IsProperCurve γ₂) (h₁0 : γ₁ 0 = 0)
    (hagree : ∀ t ≤ a, γ₂ t = γ₁ t) (hA : A ⊆ closedRightSide γ₁)
    (havoid : ∀ t, a < t → γ₂ t ∉ A)
    (hjunction : γ₂ a ∈ A →
      ∀ᶠ z in 𝓝 (γ₂ a), z ∈ A → z ∈ closedRightSide γ₂) :
    A ⊆ closedRightSide γ₂ := by
  have h₂0 : γ₂ 0 = 0 := (hagree 0 zero_le).trans h₁0
  have him₁ : (γ₁ 0).im = 0 := by rw [h₁0]; rfl
  have him₂ : (γ₂ 0).im = 0 := by rw [h₂0]; rfl
  have hlocal : ∀ z ∈ A, z ∈ closedRightSide γ₂ →
      ∀ᶠ w in 𝓝 z, w ∈ A → w ∈ closedRightSide γ₂ := by
    intro z hz hzR
    rcases hzR with hzR | hzS
    · filter_upwards [(isOpen_rightSide' h₂).mem_nhds hzR] with w hw _
      exact Or.inl hw
    · obtain ⟨s, hs⟩ : ∃ s, γ₂ s = z := by
        rcases hzS with h | ⟨hre, him⟩
        · exact h
        · refine ⟨0, ?_⟩
          apply Complex.ext hre.symm
          rw [h₂0] at him ⊢
          exact (le_antisymm him (hAH z hz)).symm
      by_cases hsa : s < a
      · have hevent := eventually_mem_leftSide_of_eqOn h₂ h₁ him₂
          (fun t ht => (hagree t ht).symm) hsa
        rw [hs] at hevent
        filter_upwards [hevent] with w hw hwA
        rw [s5_closedRightSide_eq_compl h₂ him₂]
        intro hwL
        have hwR := hA hwA
        rw [s5_closedRightSide_eq_compl h₁ him₁] at hwR
        exact hwR (hw hwL)
      · have hsa' : s = a := le_antisymm
          (le_of_not_gt fun hgt => havoid s hgt (hs ▸ hz)) (not_lt.1 hsa)
        have hza : γ₂ a = z := hsa' ▸ hs
        rw [← hza]
        exact hjunction (hza ▸ hz)
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.1 hAc
  let E : Set A := Subtype.val ⁻¹' closedRightSide γ₂
  have hEc : IsClosed E := (s5_isClosed_closedRightSide h₂ him₂).preimage continuous_subtype_val
  have hEo : IsOpen E := isOpen_iff_mem_nhds.2 fun z hz => by
    have hlim := continuous_subtype_val.continuousAt.tendsto.eventually (hlocal z z.2 hz)
    filter_upwards [hlim] with w hw
    exact hw w.2
  have hE0 : (⟨0, hA0⟩ : A) ∈ E := Or.inr (Or.inl ⟨0, h₂0⟩)
  have hEall : (univ : Set A) ⊆ E :=
    isPreconnected_univ.subset_isClopen ⟨hEc, hEo⟩ ⟨⟨0, hA0⟩, mem_univ _, hE0⟩
  intro z hz
  exact hEall (mem_univ (⟨z, hz⟩ : A))

section Gluing

variable {p : ℝ → ℂ} {β β' : ℝ≥0 → ℂ} {a₂ tL : ℝ≥0}
  {c : Chart} {g : ℂ → ℂ} {bt : ℝ≥0 → ℂ}

/-- Every new tail point misses the old range, including original real points. -/
theorem s5_gluedCurve_avoids_oldRange (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hβ' : ∀ t ≤ a₂, β' t = β t)
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (htL : tL ≤ a₂)
    (hbt : IsProperCurve bt) (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0)
    {s : ℝ≥0} (hs : a₂ < s) : gluedCurve β' g bt tL s ∉ p '' Icc 0 1 := by
  intro hz
  rcases gluedCurve_mem_of_lt hp hp0 hβ' hc hgc hgi htL hbt hbtβ hreal hs with
    hD | ⟨x, hx, he⟩
  · exact hD.2 ⟨hD.1, Or.inl (subset_closure hz)⟩
  · have hxmin := (realBase_facts hp hp0).2.2.1 x (he ▸ hz)
    exact (not_le.2 hx) hxmin.1

/-- The old range remains on the right provided its points near the terminal
junction remain on the right. No condition is needed at a junction outside it. -/
theorem s5_oldRange_subset_of_junction (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hβ' : IsProperCompletion β a₂ β') (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0)
    (hjunction : β a₂ ∈ p '' Icc 0 1 →
      ∀ᶠ z in 𝓝 (β a₂), z ∈ p '' Icc 0 1 → z ∈ closedRightSide (gluedCurve β' g bt tL)) :
    p '' Icc 0 1 ⊆ closedRightSide (gluedCurve β' g bt tL) := by
  have hΓ := isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbtβ hreal
  apply s5_oldRange_of_junction_germ (isPreconnected_Icc.image p hp)
    (show (0 : ℂ) ∈ p '' Icc 0 1 from ⟨0, left_mem_Icc.2 zero_le_one, hp0⟩)
    (by rintro z ⟨s, hs, rfl⟩; exact hpH s hs)
    (isProperCurve_of_isProperCompletion hβ') (isProperCurve_of_isProperCompletion hΓ)
    ((hβ'.2.2.2.2 0 zero_le).trans hβ0)
    (fun t ht => (hΓ.2.2.2.2 t ht).trans (hβ'.2.2.2.2 t ht).symm) hA
    (fun s hs => s5_gluedCurve_avoids_oldRange hp hp0 hβ'.2.2.2.2 hc hgc hgi htL hbt hbtβ hreal hs)
  rw [hΓ.2.2.2.2 a₂ le_rfl]
  exact hjunction

/-- The nonjunction case of old-range preservation is unconditional. -/
theorem s5_oldRange_subset_of_junction_notMem (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hβ0 : β 0 = 0)
    (hβ' : IsProperCompletion β a₂ β') (hA : p '' Icc 0 1 ⊆ closedRightSide β')
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (htL : tL ≤ a₂) (hβtL : β tL = realMin (p '' Icc 0 1)) (hbt : IsProperCurve bt)
    (hbtβ : ∀ s ≤ a₂ - tL, g (bt s) = β (tL + s))
    (hreal : ∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0)
    (hnot : β a₂ ∉ p '' Icc 0 1) :
    p '' Icc 0 1 ⊆ closedRightSide (gluedCurve β' g bt tL) :=
  s5_oldRange_subset_of_junction hp hp0 hpH hβ0 hβ' hA hc hgc hgi htL hβtL hbt hbtβ hreal
    (fun h => (hnot h).elim)

end Gluing

/-! ## The two remaining topological inputs

These propositions are explicit remaining inputs, not proved results. The first
is the boundary-contact step in the collar/winding argument on p. 583. The second
is the interior conformal orientation step. The theorems below discharge every
other part of the corrected side comparison from precisely these inputs.
-/

/-- Remaining junction input: points of the old range sufficiently near a
terminal old-range contact lie on the right of the new completion. -/
def S5JunctionGermStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β β' : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsProperCompletion β a₂ β' →
    p '' Icc 0 1 ⊆ closedRightSide β' →
    ∀ (c : Chart) (g : ℂ → ℂ), IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c →
      ContinuousOn g {z | 0 ≤ z.im} → EqOn g c.2.1 H →
      (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) →
    ∀ (tL : ℝ≥0) (bt : ℝ≥0 → ℂ), tL ≤ a₂ → β tL = realMin (p '' Icc 0 1) →
      IsProperCurve bt → bt 0 = 0 → (∀ s ≤ a₂ - tL, g (bt s) = β (tL + s)) →
      (∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) →
      β a₂ ∈ p '' Icc 0 1 →
      ∀ᶠ z in 𝓝 (β a₂), z ∈ p '' Icc 0 1 → z ∈ closedRightSide (gluedCurve β' g bt tL)

/-- Remaining interior input: after the old range is known to be on the right,
the inverse chart takes interior relative right-side points to the physical
closed right side. No assertion about arbitrary lower-half-plane points occurs. -/
def S5InteriorTransportStatement : Prop :=
  ∀ (p : ℝ → ℂ) (β β' : ℝ≥0 → ℂ) (a₂ : ℝ≥0), ContinuousOn p (Icc 0 1) → p 0 = 0 →
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) → β 0 = 0 → IsProperCompletion β a₂ β' →
    p '' Icc 0 1 ⊆ closedRightSide β' →
    ∀ (c : Chart) (g : ℂ → ℂ), IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c →
      ContinuousOn g {z | 0 ≤ z.im} → EqOn g c.2.1 H →
      (∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) →
    ∀ (tL : ℝ≥0) (bt : ℝ≥0 → ℂ), tL ≤ a₂ → β tL = realMin (p '' Icc 0 1) →
      IsProperCurve bt → bt 0 = 0 → (∀ s ≤ a₂ - tL, g (bt s) = β (tL + s)) →
      (∀ s, a₂ - tL < s → (bt s).im = 0 → (bt s).re < 0) →
      p '' Icc 0 1 ⊆ closedRightSide (gluedCurve β' g bt tL) →
      ∀ w ∈ rightSide bt ∩ H, g w ∈ closedRightSide (gluedCurve β' g bt tL)

/-- The corrected side comparison from the two explicitly identified remaining
topological inputs; the nonjunction case and all real-boundary points are proved
above and are not additional inputs. -/
theorem s5SideUpperStatement_of_junction_interior (hJ : S5JunctionGermStatement)
    (hI : S5InteriorTransportStatement) : S5SideUpperStatement := by
  intro p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi hgf
    tL a₁ aR bt htL hβtL hbt hbt0 hbtβ hreal haRH haR
  have hΓ := isProperCompletion_gluedCurve hp hp0 hpH hβ0 hβ' hA hc hgc hgi
    htL hβtL hbt hbtβ hreal
  have hΓ0 : gluedCurve β' g bt tL 0 = 0 := (hΓ.2.2.2.2 0 zero_le).trans hβ0
  have hAg : p '' Icc 0 1 ⊆ closedRightSide (gluedCurve β' g bt tL) :=
    s5_oldRange_subset_of_junction hp hp0 hpH hβ0 hβ' hA hc hgc hgi htL hβtL hbt hbtβ hreal
      (hJ p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi hgf
        tL bt htL hβtL hbt hbt0 hbtβ hreal)
  have hj : β' tL = g (bt 0) := by
    rw [hbtβ 0 zero_le, add_zero, hβ'.2.2.2.2 tL htL]
  have himage := s5_image_right_upper_of_interior hbt hbt0
    (isProperCurve_of_isProperCompletion hΓ) hΓ0 hgc
    (fun u => Or.inr (Or.inl ⟨tL + u, gluedCurve_add hj u⟩))
    (hI p β β' a₂ hp hp0 hpH hβ0 hβ' hA c g hc hgc hgi hgf
      tL bt htL hβtL hbt hbt0 hbtβ hreal hAg)
  rintro z (hzA | ⟨w, hw, rfl⟩)
  · exact hAg hzA
  · apply himage
    refine ⟨w, ⟨haR hw, ?_⟩, rfl⟩
    obtain ⟨s, hs, rfl⟩ := hw
    exact haRH s hs

/-- Source-facing S5 from the explicit junction and interior orientation inputs. -/
theorem s5Statement_of_junction_interior (hJ : S5JunctionGermStatement)
    (hI : S5InteriorTransportStatement) : S5Statement :=
  s5Statement_of_sideUpper (s5SideUpperStatement_of_junction_interior hJ hI)

end InteractingSLE.Theorem14.SB

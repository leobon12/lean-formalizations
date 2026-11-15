/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField8Flow
import InteractingSLE.GFF.LocalSets.MarkedAvoidance

/-!
# Local sets under a real translation

Packet PROVE-SIDEHEIGHT. A flow line from `x` is coupled with the translated field `h(· + x) + θχ`, so its hulls are
local sets of the translated field, in the chart `z ↦ z − x`. Translating back (`z ↦ z + x`) gives local sets of the
original field:

* `measurable_image_add`: `S ↦ S + c` is measurable for the hitting σ-algebra;
* `isHarmonicDistOn_flowField_neg`, `isCondZeroBoundaryGFF_flowField_neg`: harmonic distributions and conditional
  zero-boundary GFFs are transported (Dirichlet energy and Lebesgue measure are translation invariant,
  `WholeField.zeroGFFTestCov_comp_add`);
* **`IsLocalSet.translate`**: if `A` is a local set of `F`, then `A + c` is a local set of `F(· − c)`
  (`Exist.flowField (−c) 0 F`); the model is the reflection transport of PROVE-WW-B11.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SideHeight

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open LocalSets

/-! ### Translated sets -/

section Sets

theorem add_real_mem_H' {z : ℂ} (hz : z ∈ H) (c : ℝ) : z + c ∈ H := by
  show 0 < (z + c).im
  simpa using (show 0 < z.im from hz)

theorem image_add_inter_nonempty_iff (c : ℝ) (S U : Set ℂ) :
    ((fun z : ℂ => z + c) '' S ∩ U).Nonempty ↔ (S ∩ (fun z : ℂ => z + ((-c : ℝ) : ℂ)) '' U).Nonempty := by
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, hzU⟩
    exact ⟨z, hz, z + c, hzU, by push_cast; ring⟩
  · rintro ⟨z, hz, w, hw, e⟩
    refine ⟨w, ⟨z, hz, ?_⟩, hw⟩
    rw [← e]
    push_cast
    ring

/-- **`S ↦ S + c` is measurable for the hitting σ-algebra.** -/
theorem measurable_image_add (c : ℝ) :
    Measurable[hittingSigma, hittingSigma] fun S : Set ℂ => (fun z : ℂ => z + c) '' S := by
  refine @measurable_generateFrom (Set ℂ) (Set ℂ) hittingSigma _ (fun S : Set ℂ => (fun z : ℂ => z + c) '' S) ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have e : (fun S : Set ℂ => (fun z : ℂ => z + c) '' S) ⁻¹' {A | (A ∩ U).Nonempty} =
      {A | (A ∩ (fun z : ℂ => z + ((-c : ℝ) : ℂ)) '' U).Nonempty} := by
    ext S
    exact image_add_inter_nonempty_iff c S U
  rw [e]
  refine MeasurableSpace.measurableSet_generateFrom ⟨_, ?_, ?_, rfl⟩
  · exact (Homeomorph.addRight ((-c : ℝ) : ℂ)).isOpenMap U hUo
  · rintro _ ⟨w, hw, rfl⟩
    exact add_real_mem_H' (hUH hw) (-c)

theorem image_add_neg_image_add (c : ℝ) (S : Set ℂ) :
    (fun z : ℂ => z + ((-c : ℝ) : ℂ)) '' ((fun z : ℂ => z + c) '' S) = S := by
  rw [image_image]
  push_cast
  simp

/-- `ℍ \ (S + c) = (ℍ \ S) + c`. -/
theorem H_diff_image_add (c : ℝ) (S : Set ℂ) :
    H \ (fun z : ℂ => z + c) '' S = (fun z : ℂ => z + c) '' (H \ S) := by
  ext z
  constructor
  · rintro ⟨hzH, hzS⟩
    refine ⟨z - c, ⟨?_, fun h => hzS ⟨z - c, h, by ring⟩⟩, by ring⟩
    have := add_real_mem_H' hzH (-c)
    simpa [sub_eq_add_neg] using this
  · rintro ⟨w, ⟨hwH, hwS⟩, rfl⟩
    refine ⟨add_real_mem_H' hwH c, ?_⟩
    rintro ⟨v, hv, e⟩
    have hvw : v = w := by simpa using e
    exact hwS (hvw ▸ hv)

/-- The almost sure clause of a local set is preserved by translation. -/
theorem image_add_relClosed (c : ℝ) {S : Set ℂ} (hS : S ⊆ H ∧ IsOpen (H \ S)) :
    (fun z : ℂ => z + c) '' S ⊆ H ∧ IsOpen (H \ (fun z : ℂ => z + c) '' S) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact add_real_mem_H' (hS.1 hz) c
  · rw [H_diff_image_add]
    exact (Homeomorph.addRight (c : ℂ)).isOpenMap _ hS.2

/-- The comap of a measurable map with a measurable left inverse is the σ-algebra itself. -/
theorem comap_comp_of_leftInverse {α β : Type*} {m : MeasurableSpace α} {f g : α → α}
    (hf : Measurable[m, m] f) (hg : Measurable[m, m] g) (hgf : ∀ a, g (f a) = a) (X : β → α) :
    m.comap (f ∘ X) = m.comap X := by
  have hf' : m.comap f = m := by
    refine le_antisymm hf.comap_le ?_
    have e : g ∘ f = id := funext hgf
    calc m = m.comap (g ∘ f) := by rw [e, MeasurableSpace.comap_id]
      _ = (m.comap g).comap f := (MeasurableSpace.comap_comp).symm
      _ ≤ m.comap f := MeasurableSpace.comap_mono hg.comap_le
  rw [← MeasurableSpace.comap_comp, hf']

end Sets

/-! ### Translated fields -/

section Fields

theorem flowField_neg_apply (c : ℝ) (T : DistOn upperHalfPlaneOpens) (φ : TestOn upperHalfPlaneOpens) :
    Exist.flowField (-c) 0 T φ = T (WholeField.shiftTest c φ) := by
  rw [Exist.flowField_apply, zero_mul, add_zero]
  rfl

theorem flowField_neg_add (c : ℝ) (T₁ T₂ : DistOn upperHalfPlaneOpens) :
    Exist.flowField (-c) 0 (T₁ + T₂) = Exist.flowField (-c) 0 T₁ + Exist.flowField (-c) 0 T₂ := by
  ext φ
  simp only [flowField_neg_apply, add_apply]

theorem flowField_neg_neg (c : ℝ) (T : DistOn upperHalfPlaneOpens) :
    Exist.flowField (-(-c)) 0 (Exist.flowField (-c) 0 T) = T := by
  ext φ
  rw [flowField_neg_apply, flowField_neg_apply]
  congr 1
  ext z
  rw [WholeField.shiftTest_apply, WholeField.shiftTest_apply]
  congr 1
  push_cast
  ring

/-- **Harmonic distributions under translation**: if `T` is harmonic on `U ⊆ ℍ` (open), then `T(· − c)` is harmonic on
`U + c`. -/
theorem isHarmonicDistOn_flowField_neg {T : DistOn upperHalfPlaneOpens} {S : Set ℂ} (c : ℝ)
    (hT : IsHarmonicDistOn T (H \ S)) :
    IsHarmonicDistOn (Exist.flowField (-c) 0 T) (H \ (fun z : ℂ => z + c) '' S) := by
  have h := WholeField.isHarmonicDistOn_shift (x := c) (c := 0) (u₀ := fun _ => 0)
    (fun z _ => InnerProductSpace.harmonicAt_const _) hT
  have e : Exist.flowField (-c) (-0) T -
      SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens (fun _ => (0 : ℝ)) =
      Exist.flowField (-c) 0 T := by
    ext φ
    rw [sub_apply, neg_zero, SupercriticalConformalCovariance.GM24.smoothDist_apply continuousOn_const]
    simp
  rwa [e] at h

/-- **The conditional zero-boundary GFF under translation.** -/
theorem isCondZeroBoundaryGFF_flowField_neg {Ω : Type*} {𝒢 : MeasurableSpace Ω} [MeasurableSpace Ω]
    {P : Measure Ω} {A : Ω → Set ℂ} {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ A ω) X) (c : ℝ) :
    IsCondZeroBoundaryGFF P 𝒢 (fun ω => H \ (fun z : ℂ => z + c) '' A ω)
      (fun ω => Exist.flowField (-c) 0 (X ω)) := by
  intro φ
  set ψ := WholeField.shiftTest c φ with hψ
  have h := hX ψ
  have e : (fun ω => Complex.exp (Complex.I * (Exist.flowField (-c) 0 (X ω) φ : ℂ))) =
      fun ω => Complex.exp (Complex.I * (X ω ψ : ℂ)) := by
    funext ω
    rw [flowField_neg_apply]
  rw [e]
  refine h.trans (Eventually.of_forall fun ω => ?_)
  have hψf : ⇑ψ = fun z => φ (z + c) := funext (WholeField.shiftTest_apply c φ)
  have hc : QuantumZipper.zeroGFFTestCov (H \ A ω) ψ ψ =
      QuantumZipper.zeroGFFTestCov (H \ (fun z : ℂ => z + c) '' A ω) φ φ := by
    rw [hψf, ← WholeField.preimage_add_H_diff_image c (A ω)]
    exact WholeField.zeroGFFTestCov_comp_add (c : ℂ) _ φ.continuous φ.continuous
  simp only [hc]

end Fields

/-! ### Local sets under translation -/

section Local

/-- **Local sets under a real translation.** If `A` is a local set of `F`, then `A + c` is a local set of the
translated field `F(· − c)` (`Exist.flowField (−c) 0 F`). -/
theorem IsLocalSet.translate {Ω : Type u} [MeasurableSpace Ω] {A : Ω → Set ℂ} {F : Ω → DistOn upperHalfPlaneOpens}
    {P : Measure Ω} (hA : IsLocalSet A F P) (c : ℝ) :
    IsLocalSet (fun ω => (fun z : ℂ => z + c) '' A ω) (fun ω => Exist.flowField (-c) 0 (F ω)) P := by
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  obtain ⟨hm, hae, Ω', mΩ', P', hP', A', h₁, h₂, hA'm, hh₁, hh₂, hA'c, hhar, hcond, hlaw⟩ := hA
  have hFm : Measurable (Exist.flowField (-c) 0) := Exist.measurable_flowField _ _
  have hFm' : Measurable (Exist.flowField (-(-c)) 0) := Exist.measurable_flowField _ _
  have hF : Measurable fun p : Set ℂ × DistOn upperHalfPlaneOpens =>
      ((fun z : ℂ => z + c) '' p.1, Exist.flowField (-c) 0 p.2) :=
    ((measurable_image_add c).comp measurable_fst).prodMk (hFm.comp measurable_snd)
  have hσ : MeasurableSpace.comap (fun ω' => (fun z : ℂ => z + c) '' A' ω') hittingSigma ⊔
      MeasurableSpace.comap (fun ω' => Exist.flowField (-c) 0 (h₁ ω')) inferInstance =
      MeasurableSpace.comap A' hittingSigma ⊔ MeasurableSpace.comap h₁ inferInstance := by
    have e1 : MeasurableSpace.comap (fun ω' => (fun z : ℂ => z + c) '' A' ω') hittingSigma =
        MeasurableSpace.comap A' hittingSigma :=
      comap_comp_of_leftInverse (measurable_image_add c) (measurable_image_add (-c))
        (image_add_neg_image_add c) A'
    have e2 : MeasurableSpace.comap (fun ω' => Exist.flowField (-c) 0 (h₁ ω')) (inferInstance :
        MeasurableSpace (DistOn upperHalfPlaneOpens)) = MeasurableSpace.comap h₁ inferInstance :=
      comap_comp_of_leftInverse hFm hFm' (flowField_neg_neg c) h₁
    rw [e1, e2]
  refine ⟨hF.comp_aemeasurable hm, hae.mono fun ω hω => image_add_relClosed c hω,
    Ω', mΩ', P', hP', fun ω' => (fun z : ℂ => z + c) '' A' ω', fun ω' => Exist.flowField (-c) 0 (h₁ ω'),
    fun ω' => Exist.flowField (-c) 0 (h₂ ω'), (measurable_image_add c).comp hA'm, hFm.comp hh₁,
    hFm.comp hh₂, fun ω' => image_add_relClosed c (hA'c ω'), ?_, ?_, ?_⟩
  · filter_upwards [hhar] with ω' hω'
    exact isHarmonicDistOn_flowField_neg c hω'
  · rw [hσ]
    exact isCondZeroBoundaryGFF_flowField_neg hcond c
  · have e : (fun ω' => ((fun z : ℂ => z + c) '' A' ω',
        Exist.flowField (-c) 0 (h₁ ω') + Exist.flowField (-c) 0 (h₂ ω'))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => ((fun z : ℂ => z + c) '' p.1, Exist.flowField (-c) 0 p.2)) ∘
          fun ω' => (A' ω', h₁ ω' + h₂ ω') := by
      funext ω'
      simp only [Function.comp_apply, flowField_neg_add]
    have e' : (fun ω => ((fun z : ℂ => z + c) '' A ω, Exist.flowField (-c) 0 (F ω))) =
        (fun p : Set ℂ × DistOn upperHalfPlaneOpens => ((fun z : ℂ => z + c) '' p.1, Exist.flowField (-c) 0 p.2)) ∘
          fun ω => (A ω, F ω) := rfl
    have hm' : Measurable fun ω' => (A' ω', h₁ ω' + h₂ ω') :=
      hA'm.prodMk (LQGMetric.measurable_distOn_iff.2 fun φ => by
        simp only [add_apply]
        exact ((LQGMetric.measurable_distOn_apply φ).comp hh₁).add
          ((LQGMetric.measurable_distOn_apply φ).comp hh₂))
    rw [e, e', ← Measure.map_map hF hm', hlaw, AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hm]

end Local

end SideHeight

end Sec7

end InteractingSLE

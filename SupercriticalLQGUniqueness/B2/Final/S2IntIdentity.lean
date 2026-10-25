import SupercriticalLQGUniqueness.B2.PfeAxioms.S2GFFPlusCont
import SupercriticalLQGUniqueness.B2.Iface.FixedFieldWeyl

 




































set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.Final

 



def FixedFieldPatchIdentification (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (Φ : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ᵐ ω ∂P, ∀ F : C(ℂ, ℝ), ∃ W : LSCMetric, (∀ p, W p = weylScale (ξ : ℝ) F (Φ (h ω)) p) ∧
      Tendsto (fun k => PfeAxioms.patchApprox ξ m e k (addFun (h ω) F)) atTop (𝓝 W.toLSCFun)

 

def PatchWeylIdentity (ξ : Set.Ioi (0 : ℝ)) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (e : ℕ → Set.Ioi (0 : ℝ)) (Φ : DistC → LSCMetric) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
    ∀ᵐ ω ∂P, ∀ F : C(ℂ, ℝ), addFun (h ω) F ∈ PfeAxioms.patchLocus ξ m e ∧
      ∀ p, PfeAxioms.patchWitness ξ m e (addFun (h ω) F) p = weylScale (ξ : ℝ) F (Φ (h ω)) p

section Variants

variable {ξ : Set.Ioi (0 : ℝ)} {m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)}
  {e : ℕ → Set.Ioi (0 : ℝ)} {Φ : DistC → LSCMetric}

 

theorem patchWeylIdentity_of_identification (hId : FixedFieldPatchIdentification ξ m e Φ) :
    PatchWeylIdentity ξ m e Φ := by
  intro Ω _ P _ h hh
  filter_upwards [hId P h hh] with ω hω F
  obtain ⟨W, hW, hT⟩ := hω F
  obtain ⟨hlocus, hWeq⟩ := PfeAxioms.patchWitness_eq_of_tendsto ξ m e hT
  exact ⟨hlocus, fun p => by rw [hWeq, hW]⟩

variable (hKI : PatchWeylIdentity ξ m e Φ) (hgeo : PfeWeyl.NormalizedLimitGeometry Φ)
include hKI hgeo

 

theorem ae_patchWitness_eq_of_identity
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, PfeAxioms.patchWitness ξ m e (h ω) = Φ (h ω) := by
  filter_upwards [hKI P h hh, (hgeo P h hh).1] with ω hω hlen
  obtain ⟨-, hW⟩ := hω 0
  rw [GM.addFun_zero_eq] at hW
  apply LSCMetric.ext
  intro p
  rw [hW p]
  have h0 : (0 : C(ℂ, ℝ)) = ContinuousMap.const ℂ 0 := rfl
  rw [h0, weylScale_const (ξ : ℝ) 0 (Φ (h ω)) hlen p, mul_zero, Real.exp_zero,
    ENNReal.ofReal_one, one_mul]

 
theorem ae_patchWitness_weyl_all_of_identity
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, ∀ F : C(ℂ, ℝ),
      (PfeAxioms.patchWitness ξ m e (addFun (h ω) F)).1 =
        weylScale (ξ : ℝ) F (PfeAxioms.patchWitness ξ m e (h ω)) := by
  filter_upwards [hKI P h hh, ae_patchWitness_eq_of_identity hKI hgeo P h hh] with ω hω hD
  intro F
  rw [hD]
  funext p
  exact (hω F).2 p

 
theorem boundedShiftWeyl_patchWitness_of_identity :
    PfeWeyl.BoundedShiftWeyl ξ (PfeAxioms.patchWitness ξ m e) := by
  intro Ω _ P _ h hh F _ _
  filter_upwards [ae_patchWitness_weyl_all_of_identity hKI hgeo P h hh] with ω hω
  exact hω (F ω)

 
theorem patchWitness_eq_on_normalized_of_identity :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hf : Ω → DistC), IsNormalizedWholePlaneGFF hf P →
      ∀ᵐ ω ∂P, PfeAxioms.patchWitness ξ m e (hf ω) = Φ (hf ω) :=
  fun P _ hf hh => ae_patchWitness_eq_of_identity hKI hgeo P hf hh

 
theorem normalizedLscLimit_patchWitness_of_identity {e' : ℕ → Set.Ioi (0 : ℝ)}
    (hlsc : PfeWeyl.NormalizedLscLimit ξ m e' Φ) :
    PfeWeyl.NormalizedLscLimit ξ m e' (PfeAxioms.patchWitness ξ m e) :=
  PfeWeyl.normalizedLscLimit_congr hlsc (patchWitness_eq_on_normalized_of_identity hKI hgeo)

 
theorem normalizedLimitGeometry_patchWitness_of_identity :
    PfeWeyl.NormalizedLimitGeometry (PfeAxioms.patchWitness ξ m e) := by
  intro Ω _ P _ h hh
  have hD := ae_patchWitness_eq_of_identity hKI hgeo P h hh
  obtain ⟨h1, h2⟩ := hgeo P h hh
  refine ⟨?_, ?_⟩
  · filter_upwards [hD, h1] with ω hω h; rw [hω]; exact h
  · filter_upwards [hD, h2] with ω hω h; rw [hω]; exact h

 
theorem normalizedAcrossTails_patchWitness_of_identity (htail : PfeWeyl.NormalizedAcrossTails Φ) :
    PfeWeyl.NormalizedAcrossTails (PfeAxioms.patchWitness ξ m e) := by
  intro Ω _ P _ h hh k T hT η hη
  have hD := ae_patchWitness_eq_of_identity hKI hgeo P h hh
  filter_upwards [htail P h hh k T hT η hη] with R hR
  refine le_trans (le_of_eq (measure_congr ?_)) hR
  filter_upwards [hD] with ω hω
  simp only [hω]

 
theorem normalizedPointCircles_patchWitness_of_identity {e' : ℕ → Set.Ioi (0 : ℝ)}
    (hpts : PfeWeyl.NormalizedPointCircles ξ m e' Φ) :
    PfeWeyl.NormalizedPointCircles ξ m e' (PfeAxioms.patchWitness ξ m e) := by
  intro Ω _ P _ h hh X hX x y r x' y' r' hr hr' h0
  have hD := ae_patchWitness_eq_of_identity hKI hgeo P h hh
  filter_upwards [hD, hpts P h hh X hX x y r x' y' r' hr hr' h0] with ω hω h
  rw [hω]; exact h

 
theorem subseqLimitNormalized_patchWitness_of_identity {e' : ℕ → Set.Ioi (0 : ℝ)}
    (hS1N : PfeWeyl.SubseqLimitNormalized ξ m e' Φ) :
    PfeWeyl.SubseqLimitNormalized ξ m e' (PfeAxioms.patchWitness ξ m e) := by
  intro Ω _ P _ h hh X hX
  have hD := ae_patchWitness_eq_of_identity hKI hgeo P h hh
  obtain ⟨h1, h2⟩ := hS1N P h hh X hX
  refine ⟨?_, fun O O' hO hO' => ?_⟩
  · filter_upwards [hD, h1] with ω hω h; rw [hω]; exact h
  · filter_upwards [hD, h2 O O' hO hO'] with ω hω h; rw [hω]; exact h

 
theorem fixedFieldWeyl_patchWitness_of_identity {e' : ℕ → Set.Ioi (0 : ℝ)}
    (hW : FixedFieldWeylAllBounded ξ m e' Φ) :
    FixedFieldWeylAllBounded ξ m e' (PfeAxioms.patchWitness ξ m e) := by
  intro Ω _ P _ h hh X hX
  have hD := ae_patchWitness_eq_of_identity hKI hgeo P h hh
  filter_upwards [hD, hW P h hh X hX] with ω hω h
  rw [hω]; exact h

 
theorem exists_decomp_patchWitness_of_identity
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∃ (h₀ : Ω → DistC) (g : Ω → C(ℂ, ℝ)), IsNormalizedWholePlaneGFF h₀ P ∧ Measurable g ∧
      (∀ ω, h ω = addFun (h₀ ω) (g ω)) ∧
      ∀ᵐ ω ∂P, Continuous (PfeWeyl.euclidForget (Φ (h₀ ω))) ∧
        ∀ F : C(ℂ, ℝ), ∀ p,
          PfeAxioms.patchWitness ξ m e (addFun (h₀ ω) F) p = weylScale (ξ : ℝ) F (Φ (h₀ ω)) p := by
  obtain ⟨h₀, g, hh₀, hg, hdec⟩ := LQGMetric.DFGPS.T12.isGFFPlusCont_decomp hh
  have hh₀' : IsNormalizedWholePlaneGFF h₀ P := isNormalizedWholePlaneGFF_iff_old.mpr hh₀
  refine ⟨h₀, g, hh₀', hg, hdec, ?_⟩
  filter_upwards [hKI P h₀ hh₀', (hgeo P h₀ hh₀').2] with ω hω hctrl
  exact ⟨B2.PfeLocal.continuous_euclidForget_of_small_metric _ hctrl, fun F p => (hω F).2 p⟩

 
theorem ae_isLengthSpace_patchWitness_of_identity
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, (PfeAxioms.patchWitness ξ m e (h ω)).IsLengthSpace := by
  obtain ⟨h₀, g, -, -, hdec, hae⟩ := exists_decomp_patchWitness_of_identity hKI hgeo P h hh
  filter_upwards [hae] with ω hω
  rw [hdec ω]
  exact PfeAxioms.isLengthSpace_weylScale (Φ (h₀ ω)) hω.1 ξ ξ.property.le (g ω) _ (hω.2 (g ω))

 
theorem ae_weyl_patchWitness_of_identity
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ), weylScale (ξ : ℝ) f (PfeAxioms.patchWitness ξ m e (h ω)) =
      (PfeAxioms.patchWitness ξ m e (addFun (h ω) f)).1 := by
  obtain ⟨h₀, g, -, -, hdec, hae⟩ := exists_decomp_patchWitness_of_identity hKI hgeo P h hh
  filter_upwards [hae] with ω hω
  intro f
  funext p
  have h1 := hω.2 (g ω + f) p
  have h2 := PfeAxioms.weylScale_comp (Φ (h₀ ω)) _ hω.1 ξ ξ.property.le (g ω) (hω.2 (g ω)) f p
  rw [hdec ω, DFGPS.T12.addFun_addFun', h2, add_comm f (g ω)]
  exact h1.symm

 


theorem ae_translation_patchWitness_of_identity {e' : ℕ → Set.Ioi (0 : ℝ)}
    (hD : SubseqLimit ξ m e' (PfeAxioms.patchWitness ξ m e))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ)) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      PfeAxioms.patchWitness ξ m e (translateDist z (h ω)) (u, v) =
        PfeAxioms.patchWitness ξ m e (h ω) (u + z, v + z) := by
  let g : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (h ω) 1 z)
  have hg : IsNormalizedWholePlaneGFF g P :=
    (B2.DG20Pt.dg20_heat_translate_normalized P h hh z 1 one_pos).1
  have hW : ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      PfeAxioms.patchWitness ξ m e (addConst (g ω) (circleAvg (h ω) 1 z)) p =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * circleAvg (h ω) 1 z)) *
          PfeAxioms.patchWitness ξ m e (g ω) p := by
    filter_upwards [hKI P g hg, ae_patchWitness_eq_of_identity hKI hgeo P g hg,
      (hgeo P g hg).1] with ω hω hDω hlen p
    have h1 := (hω (ContinuousMap.const ℂ (circleAvg (h ω) 1 z))).2 p
    change PfeAxioms.patchWitness ξ m e
        (addFun (g ω) (ContinuousMap.const ℂ (circleAvg (h ω) 1 z))) p = _
    rw [h1, weylScale_const (ξ : ℝ) _ (Φ (g ω)) hlen p, hDω]
  have hT := PfeAxioms.ae_recentered_translation_of_subseqLimit
    ξ m e' (PfeAxioms.patchWitness ξ m e) hD P h hh X hX z
  filter_upwards [hW, hT] with ω hWω hTω
  intro u v
  let c := circleAvg (h ω) 1 z
  have hfield : addConst (g ω) c = translateDist z (h ω) := by
    simp only [g, c, B2.WeakStrong.addConst_addConst,
      neg_add_cancel, B2.Strong.addConst_zero,
      SupercriticalLQGUniqueness.translateDist_eq_affineComp_one]
  have hprod : ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) *
      ENNReal.ofReal (Real.exp (-(ξ : ℝ) * c)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    have hs : (ξ : ℝ) * c + -(ξ : ℝ) * c = 0 := by ring
    rw [hs]
    simp
  calc
    PfeAxioms.patchWitness ξ m e (translateDist z (h ω)) (u, v) =
        PfeAxioms.patchWitness ξ m e (addConst (g ω) c) (u, v) := by rw [hfield]
    _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) * PfeAxioms.patchWitness ξ m e (g ω) (u, v) :=
        hWω (u, v)
    _ = ENNReal.ofReal (Real.exp ((ξ : ℝ) * c)) *
        (ENNReal.ofReal (Real.exp (-(ξ : ℝ) * c)) *
          PfeAxioms.patchWitness ξ m e (h ω) (u + z, v + z)) := by rw [hTω (u, v)]
    _ = PfeAxioms.patchWitness ξ m e (h ω) (u + z, v + z) := by
        rw [← mul_assoc, hprod, one_mul]

 

theorem ae_translate_patchWitness_of_identity {e' : ℕ → Set.Ioi (0 : ℝ)}
    (hD : SubseqLimit ξ m e' (PfeAxioms.patchWitness ξ m e))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsGFFPlusCont h P) (z : ℂ) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ,
      (PfeAxioms.patchWitness ξ m e (translateDist z (h ω))).1 (u, v) =
        (PfeAxioms.patchWitness ξ m e (h ω)).1 (u + z, v + z) := by
  obtain ⟨h₀, g, hh₀, -, hdec, -⟩ := exists_decomp_patchWitness_of_identity hKI hgeo P h hh
  let X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ) := fun δ =>
    (exists_heatVersion hh₀ (δ : ℝ) δ.property).choose
  have hX : ∀ δ, IsHeatSmoothing P h₀ δ (X δ) := fun δ =>
    (exists_heatVersion hh₀ (δ : ℝ) δ.property).choose_spec.2
  have htr := ae_translation_patchWitness_of_identity hKI hgeo hD P h₀ hh₀ X hX z
  have hk : IsGFFPlusCont (fun ω => translateDist z (h₀ ω)) P :=
    WeakStrong.isGFFPlusCont_translate (PfeAxioms.isGFFPlusCont_of_normalized hh₀) z
  have hWk := ae_weyl_patchWitness_of_identity hKI hgeo P _ hk
  have hW0 := ae_weyl_patchWitness_of_identity hKI hgeo P h₀
    (PfeAxioms.isGFFPlusCont_of_normalized hh₀)
  filter_upwards [htr, hWk, hW0] with ω htrω hWkω hW0ω
  intro u v
  have hEq : PfeAxioms.patchWitness ξ m e (translateDist z (h₀ ω)) =
      PfeAxioms.translateMetric z (PfeAxioms.patchWitness ξ m e (h₀ ω)) :=
    LSCMetric.ext fun p => htrω p.1 p.2
  rw [hdec ω, PfeAxioms.translateDist_addFun, ← hWkω, ← hW0ω, hEq]
  exact PfeAxioms.weylScale_translateMetric (ξ : ℝ) _ z (fun _ => rfl) (u, v)

end Variants

end SupercriticalLQGUniqueness.B2.Final

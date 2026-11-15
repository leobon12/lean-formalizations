/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.TransferHull

/-!
# Integrated evolutions transfer along laws

Packet PROVE-FLOWEXIST2, named input (ii) (`Exist.BrownianRealizationStatement`). Let `(W, V, B, ζ)` be processes on a
measurable space `Y` and `g₀ : Ω₀ → Y`, `g : Ω → Y` measurable maps with the same law. If the processes read through
`g₀` form an integrated `SLE_a(ρ)` evolution on `(Ω₀, P₀)` (for some filtration), and on `(Ω, P)` the processes read
through `g` satisfy the pathwise relation and have continuous noise almost surely, then they form an integrated
evolution on `(Ω, P)` for the preimage under `g` of the natural filtration of `(killed (W, V), B)` on `Y`
(**`isIntegratedSLEEvolution_of_map_eq`**): the Brownian finite-dimensional laws and the independence of increments
are properties of the law of `g`.

* `natFiltration`: the natural filtration on `Y` of a killed driving and a process;
* `indep_comap_iff_map`: independence of preimage σ-algebras is independence under the image law.

**`brownianRealizationStatement_of_canonical`**: named input (ii) follows from its form on the canonical space
`(𝒟'(ℍ), μ, id)` (`CanonicalBrownianStatement`): a Brownian noise that is a measurable function of the field.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

open LQGMetric Ito

variable {nL nR : ℕ}

/-- Independence of preimage σ-algebras is independence under the image law. -/
theorem indep_comap_iff_map {Ω Y : Type*} {mΩ : MeasurableSpace Ω} {𝓐 𝓑 : MeasurableSpace Y}
    [mY : MeasurableSpace Y] {P : Measure Ω} {g : Ω → Y} (hg : Measurable g) (h𝓐 : 𝓐 ≤ mY)
    (h𝓑 : 𝓑 ≤ mY) : Indep (𝓐.comap g) (𝓑.comap g) P ↔ Indep 𝓐 𝓑 (P.map g) := by
  rw [Indep_iff, Indep_iff]
  constructor
  · intro h A B hA hB
    rw [Measure.map_apply hg (h𝓐 _ hA), Measure.map_apply hg (h𝓑 _ hB),
      Measure.map_apply hg ((h𝓐 _ hA).inter (h𝓑 _ hB)), preimage_inter]
    exact h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
  · rintro h _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
    have := h A B hA hB
    rwa [Measure.map_apply hg (h𝓐 _ hA), Measure.map_apply hg (h𝓑 _ hB),
      Measure.map_apply hg ((h𝓐 _ hA).inter (h𝓑 _ hB)), preimage_inter] at this

section Nat

variable {Y : Type u} [mY : MeasurableSpace Y] {Wy : ℝ≥0 → Y → ℝ} {VLy : Fin nL → ℝ≥0 → Y → ℝ}
  {VRy : Fin nR → ℝ≥0 → Y → ℝ} {ζy : Y → ℝ≥0∞} {By : ℝ≥0 → Y → ℝ}

/-- The natural filtration of a killed driving `(W, V, ζ)` and a process `B` on `Y`. -/
def natFiltration (hX : IsMeasurableKilledDriving Wy VLy VRy ζy) (hB : ∀ t, Measurable (By t)) :
    Filtration ℝ≥0 mY where
  seq t := killedDrivingFiltration hX t ⊔
    ⨆ (r : ℝ≥0) (_ : r ≤ t), (inferInstance : MeasurableSpace ℝ).comap (By r)
  mono' _ _ hst := sup_le_sup ((killedDrivingFiltration hX).mono hst)
    (iSup₂_mono' fun r hr => ⟨r, hr.trans hst, le_rfl⟩)
  le' t := sup_le ((killedDrivingFiltration hX).le t) (iSup₂_le fun r _ => (hB r).comap_le)

theorem killedDrivingFiltration_le_natFiltration (hX : IsMeasurableKilledDriving Wy VLy VRy ζy)
    (hB : ∀ t, Measurable (By t)) (t : ℝ≥0) : killedDrivingFiltration hX t ≤ natFiltration hX hB t :=
  le_sup_left

theorem measurable_natFiltration (hX : IsMeasurableKilledDriving Wy VLy VRy ζy)
    (hB : ∀ t, Measurable (By t)) (t : ℝ≥0) : Measurable[natFiltration hX hB t] (By t) :=
  Measurable.of_comap_le (le_sup_right.trans' (le_iSup₂_of_le t le_rfl le_rfl))

end Nat

/-- **Integrated evolutions transfer along laws.** Processes on `Y` read through `g₀` form an evolution on `Ω₀`;
`g : Ω → Y` has the law of `g₀`; on `Ω` the processes read through `g` satisfy the pathwise relation and have
continuous noise almost surely. Then they form an evolution on `Ω` for the preimage of the natural filtration. -/
theorem isIntegratedSLEEvolution_of_map_eq {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Y : Type u} [mY : MeasurableSpace Y] {Wy : ℝ≥0 → Y → ℝ}
    {VLy : Fin nL → ℝ≥0 → Y → ℝ} {VRy : Fin nR → ℝ≥0 → Y → ℝ} {ζy : Y → ℝ≥0∞} {By : ℝ≥0 → Y → ℝ}
    (hX : IsMeasurableKilledDriving Wy VLy VRy ζy) (hB : ∀ t, Measurable (By t))
    {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 m₀} {g₀ : Ω₀ → Y}
    (hg₀ : Measurable g₀)
    (hE₀ : IsIntegratedSLEEvolution a xL xR ρL ρR P₀ 𝓕₀ (fun t ω => Wy t (g₀ ω))
      (fun i t ω => VLy i t (g₀ ω)) (fun i t ω => VRy i t (g₀ ω)) (fun t ω => By t (g₀ ω))
      (fun ω => ζy (g₀ ω)))
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {g : Ω → Y} (hg : Measurable g)
    (hlaw : P.map g = P₀.map g₀) (hcont : ∀ᵐ ω ∂P, Continuous fun t => By t (g ω))
    (hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (fun t => Wy t (g ω)) (fun i t => VLy i t (g ω))
      (fun i t => VRy i t (g ω)) (fun t => By t (g ω)) (ζy (g ω))) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P (filtrationComap g hg (natFiltration hX hB))
      (fun t ω => Wy t (g ω)) (fun i t ω => VLy i t (g ω)) (fun i t ω => VRy i t (g ω))
      (fun t ω => By t (g ω)) (fun ω => ζy (g ω)) := by
  set 𝒩 := natFiltration hX hB with h𝒩
  -- the preimage of the natural filtration under `g₀` is inside `𝓕₀`
  have hX₀ := isMeasurableKilledDriving_comp hX hg₀
  have hkd₀ := killedDrivingFiltration_le hE₀.2.1 hE₀.2.2.1 hE₀.2.2.2.1 hX₀
  have hle₀ : ∀ s, (𝒩 s).comap g₀ ≤ 𝓕₀ s := fun s => by
    change (killedDrivingFiltration hX s ⊔
      ⨆ (r : ℝ≥0) (_ : r ≤ s), (inferInstance : MeasurableSpace ℝ).comap (By r)).comap g₀ ≤ 𝓕₀ s
    rw [MeasurableSpace.comap_sup]
    refine sup_le ?_ ?_
    · rw [← filtrationComap_apply g₀ hg₀, ← killedDrivingFiltration_comp hX hg₀]
      exact hkd₀ s
    · rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun r => ?_
      rw [MeasurableSpace.comap_iSup]
      refine iSup_le fun hr => ?_
      rw [MeasurableSpace.comap_comp]
      exact ((hE₀.1.2.1 r).comap_le).trans (𝓕₀.mono hr)
  refine ⟨⟨⟨⟨fun I => ?_⟩, hcont⟩, fun t => ?_, fun s t hst => ?_⟩, fun t A hA => ?_, fun i t A hA => ?_,
    fun i t A hA => ?_, hpath⟩
  · -- Brownian finite-dimensional laws
    have hπ : Measurable fun y => I.restrict fun t => By t y :=
      measurable_pi_iff.2 fun t => hB t.1
    have h0 := hE₀.1.1.hasLaw I
    refine ⟨(hπ.comp hg).aemeasurable, ?_⟩
    have e : P.map (fun ω => I.restrict fun t => By t (g ω)) =
        P₀.map (fun ω => I.restrict fun t => By t (g₀ ω)) := by
      rw [show (fun ω => I.restrict fun t => By t (g ω)) = (fun y => I.restrict fun t => By t y) ∘ g from rfl,
        ← Measure.map_map hπ hg, hlaw, Measure.map_map hπ hg₀]
      rfl
    rw [e]
    exact h0.map_eq
  · -- adapted
    exact (measurable_natFiltration hX hB t).comp (Measurable.of_comap_le le_rfl)
  · -- independence of increments
    set D : Y → ℝ := fun y => By t y - By s y with hD
    have hDm : Measurable D := (hB t).sub (hB s)
    have hcD : (inferInstance : MeasurableSpace ℝ).comap (fun ω => By t (g ω) - By s (g ω)) =
        ((inferInstance : MeasurableSpace ℝ).comap D).comap g := by
      rw [MeasurableSpace.comap_comp]; rfl
    change Indep ((inferInstance : MeasurableSpace ℝ).comap (fun ω => By t (g ω) - By s (g ω)))
      ((𝒩 s).comap g) P
    rw [hcD, indep_comap_iff_map hg hDm.comap_le (𝒩.le s), hlaw,
      ← indep_comap_iff_map hg₀ hDm.comap_le (𝒩.le s)]
    have h1 := hE₀.1.2.2 s t hst
    have e : ((inferInstance : MeasurableSpace ℝ).comap D).comap g₀ =
        (inferInstance : MeasurableSpace ℝ).comap (fun ω => By t (g₀ ω) - By s (g₀ ω)) := by
      rw [MeasurableSpace.comap_comp]; rfl
    rw [e]
    exact indep_of_indep_of_le_right h1 (hle₀ s)
  · -- `W` adapted before `ζ`
    have hset : {ω | (t : ℝ≥0∞) < ζy (g ω) ∧ Wy t (g ω) ∈ A} = g ⁻¹'
        {y | (t : ℝ≥0∞) < ζy y ∧ (Wy t y, (fun i => VLy i t y), fun i => VRy i t y) ∈
          A ×ˢ (univ : Set ((Fin nL → ℝ) × (Fin nR → ℝ)))} := by
      ext ω; simp
    rw [hset]
    refine ⟨_, killedDrivingFiltration_le_natFiltration hX hB t _ ?_, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨t, le_rfl, _, hA.prod MeasurableSet.univ, rfl⟩
  · -- `VL i` adapted before `ζ`
    have hA' : MeasurableSet {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | p.2.1 i ∈ A} :=
      (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd) hA
    have hset : {ω | (t : ℝ≥0∞) < ζy (g ω) ∧ VLy i t (g ω) ∈ A} = g ⁻¹'
        {y | (t : ℝ≥0∞) < ζy y ∧ (Wy t y, (fun i => VLy i t y), fun i => VRy i t y) ∈
          {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | p.2.1 i ∈ A}} := by
      ext ω; simp
    rw [hset]
    refine ⟨_, killedDrivingFiltration_le_natFiltration hX hB t _ ?_, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨t, le_rfl, _, hA', rfl⟩
  · -- `VR i` adapted before `ζ`
    have hA' : MeasurableSet {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | p.2.2 i ∈ A} :=
      (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd) hA
    have hset : {ω | (t : ℝ≥0∞) < ζy (g ω) ∧ VRy i t (g ω) ∈ A} = g ⁻¹'
        {y | (t : ℝ≥0∞) < ζy y ∧ (Wy t y, (fun i => VLy i t y), fun i => VRy i t y) ∈
          {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | p.2.2 i ∈ A}} := by
      ext ω; simp
    rw [hset]
    refine ⟨_, killedDrivingFiltration_le_natFiltration hX hB t _ ?_, rfl⟩
    exact MeasurableSpace.measurableSet_generateFrom ⟨t, le_rfl, _, hA', rfl⟩

/-! ### Named input (ii) from its canonical form -/

/-- **Named input (ii) on the canonical space** (`(𝒟'(ℍ), μ, id)`, `μ` the field law). For a realization datum there
are a noise `β : 𝒟'(ℍ) → (ℝ≥0 → ℝ)`, measurable at each time, and a Borel set `S` of fields of full `μ`-measure on which
`β` is continuous and satisfies the pathwise relation with the history `Ψ`, such that on `(𝒟'(ℍ), μ)` the processes
`Ψ` with the noise `β` form an integrated evolution for some filtration. (The content beyond the history is a
Brownian continuation after a finite lifetime that is a function of the field: AUD-3c N1.) -/
def CanonicalBrownianStatement : Prop :=
  ∀ (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (Ψ : DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ))
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens),
    IsFieldRealizationDatum κ xL xR ρL ρR Ψ P h →
    ∃ (β : DistOn upperHalfPlaneOpens → ℝ≥0 → ℝ) (S : Set (DistOn upperHalfPlaneOpens)),
      (∀ t, Measurable fun f => β f t) ∧ MeasurableSet S ∧ (P.map h) Sᶜ = 0 ∧
      (∀ f ∈ S, Continuous (β f) ∧ IsIntegratedSLEPath κ xL xR ρL ρR (Ψ f).2.1 (Ψ f).2.2.1 (Ψ f).2.2.2
        (β f) (Ψ f).1) ∧
      ∃ 𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (DistOn upperHalfPlaneOpens)),
        IsIntegratedSLEEvolution κ xL xR ρL ρR (P.map h) 𝓕 (fun t f => (Ψ f).2.1 t)
          (fun i t f => (Ψ f).2.2.1 i t) (fun i t f => (Ψ f).2.2.2 i t) (fun t f => β f t) (fun f => (Ψ f).1)

/-- **Named input (ii) follows from its canonical form**: an evolution on the field space with a field-measurable
noise transfers to every space carrying a field of the same law (`isIntegratedSLEEvolution_of_map_eq`). -/
theorem brownianRealizationStatement_of_canonical (hC : CanonicalBrownianStatement.{u}) :
    BrownianRealizationStatement.{u} := by
  intro κ nL nR xL xR ρL ρR Ψ Ω mΩ P hP h hdat
  obtain ⟨β, S, hβm, hSm, hS, hgood, 𝓕c, hEc⟩ := hC κ xL xR ρL ρR Ψ P h hdat
  obtain ⟨-, -, hΨ, hh, -⟩ := hdat
  have hX := isMeasurableKilledDriving_paths hΨ
  have hSΩ : ∀ᵐ ω ∂P, h ω ∈ S := by
    have : ∀ᵐ f ∂(P.map h), f ∈ S := by rw [ae_iff]; simpa only [Set.compl_def] using hS
    exact (ae_map_iff hh.aemeasurable hSm).1 this
  refine ⟨_, fun t ω => β (h ω) t,
    isIntegratedSLEEvolution_of_map_eq (By := fun t f => β f t) hX hβm measurable_id hEc hh
      (Measure.map_id.symm) (hSΩ.mono fun ω hω => (hgood _ hω).1)
      (hSΩ.mono fun ω hω => (hgood _ hω).2)⟩

/-- **Existence of flow lines from Theorems 1.2–1.3 and the canonical Brownian input** (the frozen
`exists_isFlowLine` in provider shape; conditional helper, it is not the provider). -/
theorem exists_isFlowLine_of_thm12_thm13_canonical (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hC : CanonicalBrownianStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  exists_isFlowLine_of_thm12_thm13_brownian h12 h13 (brownianRealizationStatement_of_canonical hC)
    hκ hκ4 hb hh

end Exist

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.TransferHist
import InteractingSLE.Spec.Exist.FlowLine
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# Named input (i) proved: the field clauses of the optional hull specification transfer along the field law

Packet PROVE-FLOWEXIST2, item (1). **`hullClauseTransferStatement : HullClauseTransferStatement`.**

Setting (`IsFieldRealizationDatum`): a reference optional hull coupling `(h₀, W₀, V₀, B₀, ζ₀)` on `Ω₀` whose killed
driving history is almost surely a Borel function `Ψ` of its field, and a field `h` on `(Ω, P)` with `P.map h = P₀.map h₀
= μ`. Given an integrated evolution `(𝓕, Ψ(h), B)` on `Ω`, the field clauses hold on `Ω`:

* **the canonical filtration.** On the field space `𝒟'(ℍ)` the processes `Ψ` have the killed driving filtration `𝒢`.
  The driving filtration of `Ψ(h)` on `Ω` is the usual augmentation of `h⁻¹𝒢` (`drivingFiltration_comp`); that of the
  reference coupling is the usual augmentation of `h₀⁻¹𝒢`, since its generating events are almost surely those of
  `Ψ(h₀)` (`drivingFiltration_congr_ae`);
* **Doob–Dynkin** (`Exist.exists_isStoppingTime_ae_eq_comp`): a stopping time `τ < ζ` on `Ω` is almost surely
  `s ∘ h` for a stopping time `s` of the usual augmentation of `𝒢` under `μ`; `τ₀ = s ∘ h₀` is a stopping time `< ζ₀`
  of the reference coupling;
* **the conditional-law clause**: both conditional expectations are `c ∘ h`, `c ∘ h₀` with `c = E_μ[e^{i(·, φ)} | 𝒢_s]`
  (`Exist.condExp_comp_ae_eq`); the reference clause, read from the history stopped at `τ₀`
  (`IsOptionalHullCoupling.ae_condExp_histAt`) with the Borel history functionals of Aux. lemma 23
  (`Sec4.hasMeasurableHistCharFun`, `Sec4.hasMeasurableHistHull`), is a Borel property of the field, so it holds
  `μ`-almost everywhere and then on `Ω`; at a good stop the history hull is the Loewner hull and the history functional
  is the frozen right-hand side for every bounded harmonic extension (`Exist.histCharFun_eq_of_goodStop`);
* **the local-set clause**: the hull at `τ` is almost surely a hitting-measurable function `A_C` of the field (the
  Borel history hull at `s`), so `(K_τ, h)` and `(K_{τ₀}, h₀)` both have the law `μ.map (A_C, id)` and the local-set
  witness of the reference coupling serves on `Ω`;
* **the GFF clause** transfers along `P.map h = P₀.map h₀` (`Restart.isZBGFFProcess_map`, `Restart.isZBGFFProcess_comp`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Exist

open Sec4 LawUnique LQGMetric Coupling Ito

variable {nL nR : ℕ}

/-! ### Killed drivings read through a map -/

section Comp

variable {Ω Y : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]

/-- A killed driving read through a measurable map is measurable. -/
theorem isMeasurableKilledDriving_comp {W : ℝ≥0 → Y → ℝ} {VL : Fin nL → ℝ≥0 → Y → ℝ}
    {VR : Fin nR → ℝ≥0 → Y → ℝ} {ζ : Y → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {g : Ω → Y}
    (hg : Measurable g) :
    IsMeasurableKilledDriving (fun t ω => W t (g ω)) (fun i t ω => VL i t (g ω)) (fun i t ω => VR i t (g ω))
      (fun ω => ζ (g ω)) := fun r A hA => hg (hX r A hA)

/-- The canonical killed driving of a measurable path-valued map. -/
theorem isMeasurableKilledDriving_paths
    {Ψ : Y → ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ)} (hΨ : Measurable Ψ) :
    IsMeasurableKilledDriving (fun t f => (Ψ f).2.1 t) (fun i t f => (Ψ f).2.2.1 i t)
      (fun i t f => (Ψ f).2.2.2 i t) (fun f => (Ψ f).1) := by
  intro r A hA
  have h1 : Measurable fun f => (Ψ f).1 := measurable_fst.comp hΨ
  have hs : Measurable fun f => (Ψ f).2 := measurable_snd.comp hΨ
  have h2 : Measurable fun f => ((Ψ f).2.1 r, (fun i => (Ψ f).2.2.1 i r), fun i => (Ψ f).2.2.2 i r) := by
    refine ((measurable_pi_apply r).comp (measurable_fst.comp hs)).prodMk ?_
    refine (measurable_pi_iff.2 fun i => ?_).prodMk (measurable_pi_iff.2 fun i => ?_)
    · exact (measurable_pi_apply r).comp ((measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_snd.comp hs)))
    · exact (measurable_pi_apply r).comp ((measurable_pi_apply i).comp
        (measurable_snd.comp (measurable_snd.comp hs)))
  exact (measurableSet_lt measurable_const h1).inter (h2 hA)

end Comp

section CompU

variable {Ω : Type u} {Y : Type*} [mΩ : MeasurableSpace Ω] [mY : MeasurableSpace Y]

/-- The killed driving σ-algebras of a killed driving read through `g` are the preimages. -/
theorem killedDrivingFiltration_comp {W : ℝ≥0 → Y → ℝ} {VL : Fin nL → ℝ≥0 → Y → ℝ}
    {VR : Fin nR → ℝ≥0 → Y → ℝ} {ζ : Y → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {g : Ω → Y}
    (hg : Measurable g) :
    killedDrivingFiltration (isMeasurableKilledDriving_comp hX hg) = filtrationComap g hg (killedDrivingFiltration hX) := by
  refine Filtration.ext (funext fun t => ?_)
  change killedDrivingSigma _ _ _ _ t = (killedDrivingSigma W VL VR ζ t).comap g
  rw [killedDrivingSigma, killedDrivingSigma, MeasurableSpace.comap_generateFrom]
  congr 1
  ext E
  constructor
  · rintro ⟨r, hr, A, hA, rfl⟩; exact ⟨_, ⟨r, hr, A, hA, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨r, hr, A, hA, rfl⟩, rfl⟩; exact ⟨r, hr, A, hA, rfl⟩

/-- **The driving filtration of a killed driving read through `g`** is the usual augmentation of the preimage
filtration. -/
theorem drivingFiltration_comp {W : ℝ≥0 → Y → ℝ} {VL : Fin nL → ℝ≥0 → Y → ℝ}
    {VR : Fin nR → ℝ≥0 → Y → ℝ} {ζ : Y → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ) {g : Ω → Y}
    (hg : Measurable g) (P : Measure Ω) :
    drivingFiltration P (isMeasurableKilledDriving_comp hX hg) = usualAugmentation (filtrationComap g hg (killedDrivingFiltration hX)) P := by
  unfold drivingFiltration
  rw [killedDrivingFiltration_comp]

end CompU

section Congr

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {W₁ W₂ : ℝ≥0 → Ω → ℝ}
  {VL₁ VL₂ : Fin nL → ℝ≥0 → Ω → ℝ} {VR₁ VR₂ : Fin nR → ℝ≥0 → Ω → ℝ} {ζ₁ ζ₂ : Ω → ℝ≥0∞}

/-- Two killed drivings that agree before a common lifetime. -/
def AgreeBefore (W₁ W₂ : ℝ≥0 → Ω → ℝ) (VL₁ VL₂ : Fin nL → ℝ≥0 → Ω → ℝ) (VR₁ VR₂ : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ₁ ζ₂ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  ζ₂ ω = ζ₁ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ₁ ω →
    W₂ t ω = W₁ t ω ∧ (∀ i, VL₂ i t ω = VL₁ i t ω) ∧ ∀ j, VR₂ j t ω = VR₁ j t ω

omit mΩ in
/-- Agreeing killed drivings have the same killed history. -/
theorem killedHistory_eq_of_agreeBefore {ω : Ω} (h : AgreeBefore W₁ W₂ VL₁ VL₂ VR₁ VR₂ ζ₁ ζ₂ ω) :
    killedHistory W₂ VL₂ VR₂ ζ₂ ω = killedHistory W₁ VL₁ VR₁ ζ₁ ω := by
  obtain ⟨hζ, hv⟩ := h
  refine Prod.ext hζ (funext fun p => ?_)
  simp only [killedHistory]
  rw [hζ]
  split_ifs with hp
  · obtain ⟨h1, h2, h3⟩ := hv _ hp
    simp only [h1, h2, h3]
  · rfl

/-- **Killed drivings that agree almost surely have the same driving filtration.** -/
theorem drivingFiltration_congr_ae (hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ ζ₁)
    (hX₂ : IsMeasurableKilledDriving W₂ VL₂ VR₂ ζ₂)
    (hae : ∀ᵐ ω ∂P, AgreeBefore W₁ W₂ VL₁ VL₂ VR₁ VR₂ ζ₁ ζ₂ ω) :
    drivingFiltration P hX₁ = drivingFiltration P hX₂ := by
  have hgen : ∀ (r : ℝ≥0) (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))),
      {ω | (r : ℝ≥0∞) < ζ₁ ω ∧ (W₁ r ω, fun i => VL₁ i r ω, fun i => VR₁ i r ω) ∈ A} =ᵐ[P]
      {ω | (r : ℝ≥0∞) < ζ₂ ω ∧ (W₂ r ω, fun i => VL₂ i r ω, fun i => VR₂ i r ω) ∈ A} := fun r A => by
    filter_upwards [hae] with ω ⟨hζ, hv⟩
    change ((r : ℝ≥0∞) < ζ₁ ω ∧ _ ∈ A) = ((r : ℝ≥0∞) < ζ₂ ω ∧ _ ∈ A)
    rw [hζ]
    by_cases hr : (r : ℝ≥0∞) < ζ₁ ω
    · obtain ⟨h1, h2, h3⟩ := hv r hr
      simp only [h1, h2, h3]
    · simp only [hr, false_and]
  refine usualAugmentation_eq_of_le_nullAugmented (fun t => ?_) (fun t => ?_)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨r, hr, A, hA, rfl⟩
    exact measurableSet_nullAugmented_of_ae_eq (hX₁ r A hA)
      (MeasurableSpace.measurableSet_generateFrom ⟨r, hr, A, hA, rfl⟩) (hgen r A)
  · refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨r, hr, A, hA, rfl⟩
    exact measurableSet_nullAugmented_of_ae_eq (hX₂ r A hA)
      (MeasurableSpace.measurableSet_generateFrom ⟨r, hr, A, hA, rfl⟩) (hgen r A).symm

end Congr

/-- The stopped σ-algebra depends only on the filtration. -/
theorem measurableSpace_congr {Ω : Type*} {m : MeasurableSpace Ω} {𝓕₁ 𝓕₂ : Filtration ℝ≥0 m}
    (h : 𝓕₁ = 𝓕₂) {τ : Ω → WithTop ℝ≥0} (hτ₁ : IsStoppingTime 𝓕₁ τ) (hτ₂ : IsStoppingTime 𝓕₂ τ) :
    hτ₁.measurableSpace = hτ₂.measurableSpace := by
  subst h; rfl

/-- The history stopped at a measurable time is measurable. -/
theorem measurable_stopHistory_const {Y : Type*} [MeasurableSpace Y] {k : Y → HistorySpace nL nR}
    (hk : Measurable k) {s : Y → ℝ≥0} (hs : Measurable s) :
    Measurable fun y => stopHistory (fun _ => s y) (k y) := by
  refine (measurable_coe_nnreal_ennreal.comp hs).prodMk (Measurable.of_eval fun p => ?_)
  exact Measurable.ite (measurableSet_le measurable_const hs)
    ((measurable_pi_apply p).comp (measurable_snd.comp hk)) measurable_const

/-! ### The transfer -/

/-- **Named input (i) (`HullClauseTransferStatement`) holds.** For a realization datum, every integrated evolution
`(𝓕, Ψ(h), B)` on `(Ω, P)` is an optional hull coupling with `h`. -/
theorem hullClauseTransferStatement : HullClauseTransferStatement.{u} := by
  intro κ nL nR xL xR ρL ρR Ψ Ω mΩ P hP h hdat 𝓕 B hE
  obtain ⟨-, -, hΨ, hh, Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hcoup, hae₀, hlaw⟩ := hdat
  have hev : ∀ φ : TestOn upperHalfPlaneOpens, Measurable fun f : DistOn upperHalfPlaneOpens => f φ :=
    fun φ => (measurable_pi_apply φ).comp (Measurable.of_comap_le le_rfl)
  -- the canonical killed driving on the field space
  have hXC := isMeasurableKilledDriving_paths hΨ
  set 𝒢 := killedDrivingFiltration hXC with h𝒢
  set μ := P.map h with hμdef
  have hμ₀ : P₀.map h₀ = μ := hlaw.symm
  have hh₀ : Measurable h₀ := hcoup.2.1
  have hX := isMeasurableKilledDriving_comp hXC hh
  have hDF : drivingFiltration P hX = usualAugmentation (filtrationComap h hh 𝒢) P :=
    drivingFiltration_comp hXC hh P
  obtain ⟨hX₀, hτc₀⟩ := hcoup.2.2.2
  have hagree₀ : ∀ᵐ ω ∂P₀, AgreeBefore W₀ (fun t ω => (Ψ (h₀ ω)).2.1 t) VL₀
      (fun i t ω => (Ψ (h₀ ω)).2.2.1 i t) VR₀ (fun i t ω => (Ψ (h₀ ω)).2.2.2 i t) ζ₀
      (fun ω => (Ψ (h₀ ω)).1) ω := hae₀
  have hDF₀ : drivingFiltration P₀ hX₀ = usualAugmentation (filtrationComap h₀ hh₀ 𝒢) P₀ :=
    (drivingFiltration_congr_ae hX₀ (isMeasurableKilledDriving_comp hXC hh₀) hagree₀).trans
      (drivingFiltration_comp hXC hh₀ P₀)
  have hkh₀ : ∀ᵐ o ∂P₀, killedHistory W₀ VL₀ VR₀ ζ₀ o =
      killedHistory (fun t f => (Ψ f).2.1 t) (fun i t f => (Ψ f).2.2.1 i t)
        (fun i t f => (Ψ f).2.2.2 i t) (fun f => (Ψ f).1) (h₀ o) :=
    hagree₀.mono fun o ho => (killedHistory_eq_of_agreeBefore ho).symm
  refine ⟨hE, hh, ?_, hX, fun τ hτ hτζ => ?_⟩
  · -- the GFF clause
    intro u₀ hu₀
    have h1 := hcoup.2.2.1 u₀ hu₀
    have hm : ∀ φ : TestOn upperHalfPlaneOpens,
        Measurable fun f : DistOn upperHalfPlaneOpens => f φ - ∫ z, u₀ z * φ z :=
      fun φ => (hev φ).sub measurable_const
    have h2 := Restart.isZBGFFProcess_map hh₀ hm h1
    rw [hμ₀] at h2
    exact Restart.isZBGFFProcess_comp hh h2
  -- Doob–Dynkin for `τ`
  have hτ' : IsStoppingTime (usualAugmentation (filtrationComap h hh 𝒢) P) τ := hDF ▸ hτ
  have hms : hτ.measurableSpace = hτ'.measurableSpace := measurableSpace_congr hDF hτ hτ'
  have hτfin : ∀ᵐ ω ∂P, τ ω ≠ ⊤ := hτζ.mono fun ω h1 ht => by
    have := (coe_untopD_of_lt h1).1
    rw [ht] at this
    exact WithTop.coe_ne_top this
  obtain ⟨s, hs, hτs⟩ := exists_isStoppingTime_ae_eq_comp hh rfl hτ' hτfin
  have hsm : Measurable s := by
    refine measurable_of_Iic fun t => ?_
    have h1 := (usualAugmentation 𝒢 μ).le t _ (hs t)
    convert h1 using 1
    ext x
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq, WithTop.coe_le_coe]
  -- the reference stopping time
  set τ₀ : Ω₀ → WithTop ℝ≥0 := fun o => (s (h₀ o) : WithTop ℝ≥0) with hτ₀def
  have hτ₀' : IsStoppingTime (usualAugmentation (filtrationComap h₀ hh₀ 𝒢) P₀) τ₀ :=
    isStoppingTime_comp hh₀ hμ₀ hs
  have hτ₀ : IsStoppingTime (drivingFiltration P₀ hX₀) τ₀ := hDF₀ ▸ hτ₀'
  have hms₀ : hτ₀.measurableSpace = hτ₀'.measurableSpace := measurableSpace_congr hDF₀ hτ₀ hτ₀'
  have hζCm : Measurable fun f : DistOn upperHalfPlaneOpens => (Ψ f).1 := measurable_fst.comp hΨ
  have hSm : MeasurableSet {f : DistOn upperHalfPlaneOpens | (s f : ℝ≥0∞) < (Ψ f).1} :=
    measurableSet_lt (measurable_coe_nnreal_ennreal.comp hsm) hζCm
  have hSΩ : ∀ᵐ ω ∂P, h ω ∈ {f : DistOn upperHalfPlaneOpens | (s f : ℝ≥0∞) < (Ψ f).1} := by
    filter_upwards [hτζ, hτs] with ω h1 h2
    rw [h2] at h1
    exact h1
  have hSμ : ∀ᵐ f ∂μ, f ∈ {f : DistOn upperHalfPlaneOpens | (s f : ℝ≥0∞) < (Ψ f).1} :=
    (ae_map_iff hh.aemeasurable hSm).2 hSΩ
  have hS₀ : ∀ᵐ o ∂P₀, h₀ o ∈ {f : DistOn upperHalfPlaneOpens | (s f : ℝ≥0∞) < (Ψ f).1} := by
    rw [← hμ₀] at hSμ
    exact (ae_map_iff hh₀.aemeasurable hSm).1 hSμ
  have hτ₀ζ : ∀ᵐ o ∂P₀, (τ₀ o : ℝ≥0∞) < ζ₀ o := by
    filter_upwards [hS₀, hae₀] with o h1 h2
    rw [← h2.1]
    exact h1
  have hcl₀ := hτc₀ τ₀ hτ₀ hτ₀ζ
  -- the Borel history functionals and the history at the stop
  obtain ⟨A, hAm, -, hAeq⟩ := hasMeasurableHistHull (nL := nL) (nR := nR)
  obtain ⟨G, hGm, hGeq⟩ := hasMeasurableHistCharFun κ ρL ρR
  set Γ : DistOn upperHalfPlaneOpens → HistorySpace nL nR := fun f =>
    stopHistory (fun _ => s f) (killedHistory (fun t f => (Ψ f).2.1 t) (fun i t f => (Ψ f).2.2.1 i t)
      (fun i t f => (Ψ f).2.2.2 i t) (fun f => (Ψ f).1) f) with hΓdef
  have hΓ : Measurable Γ := measurable_stopHistory_const (measurable_killedHistory hXC) hsm
  -- good stops on both spaces
  have hgood : ∀ᵐ ω ∂P, IsGoodStop (fun _ => s (h ω)) (fun t ω => (Ψ (h ω)).2.1 t)
      (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) (fun ω => (Ψ (h ω)).1) ω := by
    filter_upwards [hSΩ, hE.2.2.2.2] with ω h1 hp
    exact ⟨h1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  have hgood₀ : ∀ᵐ o ∂P₀, IsGoodStop (fun _ => s (h₀ o)) W₀ VL₀ VR₀ ζ₀ o := by
    filter_upwards [hτ₀ζ, hcoup.1.2.2.2.2] with o h1 hp
    exact ⟨h1, hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  have hT : ∀ᵐ ω ∂P, (τ ω).untopD 0 = s (h ω) := hτs.mono fun ω hω => by rw [hω]; rfl
  refine ⟨?_, fun u hu φ => ?_⟩
  · -- the local-set clause
    let _ : MeasurableSpace (Set ℂ) := hittingSigma
    have hAC : Measurable fun f => A (Γ f) :=
      measurable_hitting_of_measurableSet_disjoint fun K hK => hΓ (hAm K hK)
    have hpair : Measurable fun f => (A (Γ f), f) := hAC.prodMk measurable_id
    have hK₀ : ∀ᵐ o ∂P₀, (fwdHull (fun r : ℝ => W₀ r.toNNReal o) ((τ₀ o).untopD 0 : ℝ≥0), h₀ o) =
        (A (Γ (h₀ o)), h₀ o) := by
      filter_upwards [hgood₀, hkh₀] with o hg hk
      refine Prod.ext ?_ rfl
      have e : Γ (h₀ o) = stopHistory (fun _ => s (h₀ o)) (killedHistory W₀ VL₀ VR₀ ζ₀ o) := by
        rw [hk]
      rw [e, hAeq _ (isContHist_stopHistory hg), histHull_eq_fwdHull hg]
      rfl
    have hK : ∀ᵐ ω ∂P, (fwdHull (fun r : ℝ => (Ψ (h ω)).2.1 r.toNNReal) ((τ ω).untopD 0 : ℝ≥0), h ω) =
        (A (Γ (h ω)), h ω) := by
      filter_upwards [hgood, hT] with ω hg hTω
      refine Prod.ext ?_ rfl
      rw [hTω]
      change _ = A (stopHistory (fun _ => s (h ω)) (killedHistory (fun t ω => (Ψ (h ω)).2.1 t)
        (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) (fun ω => (Ψ (h ω)).1) ω))
      rw [hAeq _ (isContHist_stopHistory hg), histHull_eq_fwdHull hg]
    have hmap₀ : P₀.map (fun o => (fwdHull (fun r : ℝ => W₀ r.toNNReal o) ((τ₀ o).untopD 0 : ℝ≥0), h₀ o)) =
        μ.map fun f => (A (Γ f), f) := by
      rw [Measure.map_congr hK₀, ← hμ₀, Measure.map_map hpair hh₀]
      rfl
    have hmap : P.map (fun ω => (fwdHull (fun r : ℝ => (Ψ (h ω)).2.1 r.toNNReal) ((τ ω).untopD 0 : ℝ≥0),
        h ω)) = μ.map fun f => (A (Γ f), f) := by
      rw [Measure.map_congr hK, hμdef, Measure.map_map hpair hh]
      rfl
    obtain ⟨-, -, Ω', mΩ', P', hP', A', h₁, h₂, hA', hh₁, hh₂, hsub, hharm, hgff, hlaw'⟩ := hcl₀.1
    refine ⟨(hpair.comp hh).aemeasurable.congr (hK.mono fun ω hω => hω.symm), ?_,
      Ω', mΩ', P', hP', A', h₁, h₂, hA', hh₁, hh₂, hsub, hharm, hgff, hlaw'.trans (hmap₀.trans hmap.symm)⟩
    filter_upwards [hgood, hT] with ω hg hTω
    rw [hTω]
    have hO := isOpen_H_diff_fwdHull_of_goodStop hg
    exact ⟨fun z hz => hz.1, hO⟩
  · -- the conditional-law clause
    set g : DistOn upperHalfPlaneOpens → ℂ := fun f => Complex.exp (Complex.I * (f φ : ℂ)) with hgdef
    have hgm : Measurable g :=
      Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp (hev φ)))
    have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hh.aemeasurable).2 hP
    have hgi : Integrable g μ := Integrable.of_bound hgm.aestronglyMeasurable 1
      (ae_of_all _ fun f => by simp only [hgdef, Complex.norm_exp_I_mul_ofReal, le_refl])
    set c := μ[g | hs.measurableSpace] with hcdef
    have hcm : Measurable c := (stronglyMeasurable_condExp.mono hs.measurableSpace_le).measurable
    have hc0 := condExp_comp_ae_eq hh₀ hμ₀ hs hτ₀' (ae_of_all _ fun _ => rfl) hgi
    have hc1 := condExp_comp_ae_eq hh rfl hs hτ' hτs hgi
    have href := hcoup.ae_condExp_histAt hAeq hGeq hX₀ hτ₀ hτ₀ζ φ
    set Q : Set (DistOn upperHalfPlaneOpens) :=
      {f | Disjoint (tsupport φ) (A (Γ f))}ᶜ ∪ {f | c f = G φ (Γ f)} with hQdef
    have hQm : MeasurableSet Q :=
      (hΓ (hAm _ φ.hasCompactSupport)).compl.union (measurableSet_eq_fun hcm ((hGm φ).comp hΓ))
    have hQ₀ : ∀ᵐ o ∂P₀, h₀ o ∈ Q := by
      filter_upwards [href, hkh₀, hc0] with o ho hk hco
      have e : stopHistory (fun _ => (τ₀ o).untopD 0) (killedHistory W₀ VL₀ VR₀ ζ₀ o) = Γ (h₀ o) := by
        rw [hk]
        rfl
      rw [e] at ho
      by_cases hdis : Disjoint (tsupport φ) (A (Γ (h₀ o)))
      · refine Or.inr ?_
        change c (h₀ o) = G φ (Γ (h₀ o))
        rw [← ho.2 hdis, hms₀]
        exact hco.symm
      · exact Or.inl hdis
    have hQμ : ∀ᵐ f ∂μ, f ∈ Q := by
      rw [← hμ₀]
      exact (ae_map_iff hh₀.aemeasurable hQm).2 hQ₀
    have hQ : ∀ᵐ ω ∂P, h ω ∈ Q := (ae_map_iff hh.aemeasurable hQm).1 hQμ
    filter_upwards [hQ, hc1, hT, hgood] with ω hQω hcω hTω hg hdis
    have hu' := hu ω
    rw [hTω] at hdis hu' ⊢
    have hcont := isContHist_stopHistory hg
    have hAω : A (Γ (h ω)) = fwdHull (fun r : ℝ => (Ψ (h ω)).2.1 r.toNNReal) (s (h ω)) := by
      change A (stopHistory (fun _ => s (h ω)) (killedHistory (fun t ω => (Ψ (h ω)).2.1 t)
        (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) (fun ω => (Ψ (h ω)).1) ω)) = _
      rw [hAeq _ hcont, histHull_eq_fwdHull hg]
    have hdisA : Disjoint (tsupport φ) (A (Γ (h ω))) := by rw [hAω]; exact hdis
    have hcG : c (h ω) = G φ (Γ (h ω)) := by
      rcases hQω with h1 | h1
      · exact absurd hdisA h1
      · exact h1
    have hhist : Disjoint (tsupport φ) (histHull (stopHistory (fun _ => s (h ω))
        (killedHistory (fun t ω => (Ψ (h ω)).2.1 t) (fun i t ω => (Ψ (h ω)).2.2.1 i t)
          (fun i t ω => (Ψ (h ω)).2.2.2 i t) (fun ω => (Ψ (h ω)).1) ω))) := by
      rw [histHull_eq_fwdHull hg]; exact hdis
    rw [hms, hcω]
    refine hcG.trans ?_
    change G φ (stopHistory (fun _ => s (h ω)) (killedHistory (fun t ω => (Ψ (h ω)).2.1 t)
        (fun i t ω => (Ψ (h ω)).2.2.1 i t) (fun i t ω => (Ψ (h ω)).2.2.2 i t) (fun ω => (Ψ (h ω)).1) ω)) = _
    rw [hGeq _ _ hcont hhist, histCharFun_eq_of_goodStop κ ρL ρR hg hu' hdis]

/-- **Existence of flow lines from Theorems 1.2–1.3 and the Brownian realization input** (the frozen
`exists_isFlowLine` in provider shape; conditional helper, it is not the provider): `exists_isFlowLine_of_thm12_thm13`
with named input (i) discharged by `hullClauseTransferStatement`. -/
theorem exists_isFlowLine_of_thm12_thm13_brownian (h12 : Theorem12Statement.{u})
    (h13 : Theorem13Statement.{u}) (hBM : BrownianRealizationStatement.{u}) {κ : ℝ}
    (hκ : 0 < κ := by assumption) (hκ4 : κ < 4 := by assumption)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps := by assumption)
    {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps := by assumption) :
    ∃ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps x θ P h η ζ :=
  exists_isFlowLine_of_thm12_thm13 h12 h13 hullClauseTransferStatement hBM hκ hκ4 hb hh

end Exist

end InteractingSLE

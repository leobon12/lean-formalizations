/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.J6Locality
import InteractingSLE.WangWu.Prop424Chart

/-!
# Wang–Wu at `κ = 4`, (J7): the conditioning data `Q` of Proposition 4.24

Packet PROVE-WW-B23. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.24
(text dump L1816–1867), last paragraph: with `Q` the two walls and the exterior fields, "(i) `h` is determined by
`(Q, H)`, (ii) the history is determined by `(h, Q)`, (iii) `(history, H)` is independent of `Q`", whence the
determination `F(X) = E[F(X) | Q, H] = E[F(X) | H]` (the specification's Lemma 7.2 (CPF3),
`Sec7.Prop73Ref.isFieldDeterminedHistory_of_cpf3`). Item (J7) of the roadmap in `planning/handoffs/PROVE-WW-B20.md`.

`Q` is the exterior record of the specification's Lemma 7.2 (`Sec7.Lemma72B.pocketRecord`): the two complete walls and
the field off the closed chamber `C̄`. On a three-line space `SeedThree.IsThreeLineSpace` (WW-B22) with a chamber
construction (`Sec7.Lemma71K.IsPocketConstruction`), this file proves:

* **(i)** `isAEDeterminedBy_field_seed`: on a `κ = 4` seed three-line space (`SeedThree.IsSeedThreeSpace`), `h` is
  almost surely a Borel function of `(Q, h_ψ)` — thin-support removal on `∂C ∩ ℍ ⊆ β ∪ α` (the specification's
  `Sec7.Lemma72B.isAEDeterminedBy_field_of_pocket` with its two flow-line inputs replaced by the seed couplings: the
  walls have dimension `< 2` on compacts of `ℍ` (`ae_dimH_range_lt_seed`: each wall is the trace of an `SLE₄(ρL; ρR)`
  word with nonnegative weights, `IsMarkedChain.ae_seedLine`, Aux. lemma 15), and the field satisfies (SR1) and is
  integrable (`sr1_seed`: the middle coupling has the field `h` itself));
* **(iii)** `indepFun_three`: `(killed history, h_ψ)` is independent of `Q` — under every `P[· | G]`, `G ∈ σ(Q)`, the
  chamber pair is a two-seed coupling (`exists_cond_three` and the weight-generic chart pipeline
  `Chamber4.exists_isOptionalHullCoupling_of_chart`), and two-seed couplings have one joint law (Aux. lemmas 50–51,
  `Sec7.Lemma72C.indepFun_of_forall_cond_isTwoSeedCouplingOf`, any `0 < κ < 8`, weights `> −2`).

Item (ii) is `Sec7.Lemma72B.isAEDeterminedBy_killedHistory_of_le_curves` (curve-generic; used in `J7CondMain`).

Conditional helpers (on the (J5) clause); they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Real

open QuantumZipper (H Hbar fwdHull)

universe u

namespace InteractingSLE.WangWu.ChamberCond

open LQGMetric Sec7 Sec7.Lemma71C Sec7.Lemma71D Sec7.Lemma71E Sec7.Lemma71K Sec6 LocalSets WholeField MartChar
  SeedThree LawUnique Chart

/-! ### The seed couplings: dimension of the lines and (SR1) -/

section Seed

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Reparametrizing by `s ↦ s⁺` does not change the range. -/
theorem range_comp_toNNReal (f : ℝ≥0 → ℂ) : range (fun s : ℝ => f s.toNNReal) = range f := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨(t : ℝ), by simp only [Real.toNNReal_coe]⟩

/-- **The dimension of a nonnegative `κ = 4` seed line** (Aux. lemma 15 for the trace of `SLE₄(rL; rR)`, `rL, rR ≥ 0`):
if a curve `η'` is almost surely the seed line of an optional hull coupling with infinite lifetime, then almost surely
`dim_H (range η' ∩ K) < 2 − 2ε` for every `K ⊆ ℍ`, whenever `ε < (1 − 4/8)/4`. -/
theorem ae_dimH_range_lt_of_seedLine {rL rR ε : ℝ} (hL : 0 ≤ rL) (hR : 0 ≤ rR)
    (hε : ε < Dimension.onePointExponent 4 / 4) {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {f : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ f)
    {η' : Ω → ℝ≥0 → ℂ} (hη' : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ Lemma71I.realPath (η' ω) = seedLine ζ W ω) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, K ⊆ H → dimH (range (η' ω) ∩ K) < ENNReal.ofReal (2 - 2 * ε) := by
  filter_upwards [IsMarkedChain.ae_seedLine isOrderedForceWord_twoSeed (hasNonnegCumWeights_twoSeed hL hR) hC.1,
    hC.1.ae_dimH_image_inter_lt (by norm_num) (by norm_num) hε, hη'] with ω hω hd hω'
  obtain ⟨hζ, ⟨η, hη, hline⟩, -⟩ := hω
  have hr : range (η' ω) = η '' univ := by
    rw [image_univ, ← range_comp_toNNReal η, ← hline, ← hω'.2]
    exact (range_comp_toNNReal (η' ω)).symm
  intro K hK
  rw [hr]
  refine hd η (by rwa [hζ]) univ (fun t _ => ?_) K hK
  rw [mem_ofPred_eq, hζ]
  exact le_top

omit mΩ [IsProbabilityMeasure P] in
/-- The heights of a seed three-line space lie between `u₁` and `u₂`, so every seed word is nonnegative. -/
theorem nonneg_of_mem_seed {rL rR u₁ u₂ c : ℝ} {η : Ω → ℝ≥0 → ℂ} {β α γ : Ω → ℝ≥0 → ℂ} (hu₁ : u₁ < 0)
    (hu₂ : 0 < u₂) (hL : 0 ≤ rL - u₂ / wwLambda) (hR : 0 ≤ rR + u₁ / wwLambda)
    (hmem : (c, η) ∈ ({(u₂, β), (u₁, α), (0, γ)} : Set (ℝ × (Ω → ℝ≥0 → ℂ)))) :
    0 ≤ rL - c / wwLambda ∧ 0 ≤ rR + c / wwLambda := by
  have hl : 0 < wwLambda := wwLambda_pos
  have hc : u₁ ≤ c ∧ c ≤ u₂ := by
    rcases hmem with h | h | h
    · rw [Prod.mk.injEq] at h
      exact ⟨h.1 ▸ (hu₁.trans hu₂).le, h.1.le⟩
    · rw [Prod.mk.injEq] at h
      exact ⟨h.1.ge, h.1 ▸ (hu₁.trans hu₂).le⟩
    · rw [mem_singleton_iff, Prod.mk.injEq] at h
      exact ⟨h.1 ▸ hu₁.le, h.1 ▸ hu₂.le⟩
  have h1 : c / wwLambda ≤ u₂ / wwLambda := div_le_div_of_nonneg_right hc.2 hl.le
  have h2 : u₁ / wwLambda ≤ c / wwLambda := div_le_div_of_nonneg_right hc.1 hl.le
  constructor <;> linarith

/-- **The walls of a seed three-line space have dimension `< 2`** (Aux. lemma 15 at `κ = 4`). -/
theorem ae_dimH_range_lt_seed {rL rR u₁ u₂ ε : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    {β α γ : Ω → ℝ≥0 → ℂ} (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ)
    (hε : ε < Dimension.onePointExponent 4 / 4) {c : ℝ} {η : Ω → ℝ≥0 → ℂ}
    (hmem : (c, η) ∈ ({(u₂, β), (u₁, α), (0, γ)} : Set (ℝ × (Ω → ℝ≥0 → ℂ)))) :
    ∀ᵐ ω ∂P, ∀ K : Set ℂ, K ⊆ H → dimH (range (η ω) ∩ K) < ENNReal.ofReal (2 - 2 * ε) := by
  obtain ⟨hu₁, hu₂, hL, hR, -, -, -, hlines⟩ := hS
  obtain ⟨hL', hR'⟩ := nonneg_of_mem_seed hu₁ hu₂ hL hR hmem
  obtain ⟨𝓕, W, VL, VR, B, ζ, hC, hη⟩ := hlines c η hmem
  exact ae_dimH_range_lt_of_seedLine hL' hR' hε hC hη

/-- **(SR1) and integrability of the field on a seed three-line space**: the middle seed coupling has height `0`, i.e.
the field `h` itself. -/
theorem sr1_seed {rL rR u₁ u₂ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    {β α γ : Ω → ℝ≥0 → ℂ} (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ) :
    (∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) P) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ ζc : TestOn upperHalfPlaneOpens, ∫⁻ ω, Sobolev.negSobolevSq ε (h ω) ζc ∂P < ⊤ := by
  obtain ⟨-, -, -, -, -, -, -, hlines⟩ := hS
  obtain ⟨𝓕, W, VL, VR, B, ζ, hC, -⟩ :=
    hlines 0 γ (mem_insert_of_mem _ (mem_insert_of_mem _ (mem_singleton _)))
  have e : (fun ω => Exist.flowField 0 0 (h ω)) = h := funext fun ω => Sec5.GlueCond.flowField_zero_zero (h ω)
  rw [e] at hC
  exact ⟨fun φ => hC.integrable_apply φ, fun hε ζc => hC.lintegral_negSobolevSq_lt_top hε ζc⟩

end Seed

/-! ### (i): the field from `(Q, h_ψ)` -/

section Field

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

-- adapted from `Sec7.Lemma72B.isAEDeterminedBy_field_of_pocket` (flow-line inputs replaced by the seed couplings)
/-- **(i) on a seed three-line space** (Wang–Wu Proposition 4.24; the specification's Lemma 7.2 (i), pp. 226–227): the
field is almost surely a Borel function of the exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})` and the pulled-back field
`h_ψ`. Thin-support removal on `∂C ∩ ℍ ⊆ β ∪ α`: the walls have dimension `< 2` on compacts of `ℍ` and closed ranges,
the field satisfies (SR1); inside the chamber `h` is recorded by `h_ψ` through the chart (a function of `(β, α)`), off
`C̄` by `Q`. -/
theorem isAEDeterminedBy_field_seed {rL rR u₁ u₂ : ℝ} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ}
    {β α γ : Ω → ℝ≥0 → ℂ} (hS : IsSeedThreeSpace rL rR u₁ u₂ P h u₀ β α γ)
    {c : Ω → Chart} (hcc : ∀ ω, (c ω).IsConformal)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | Metric.closedBall z r ⊆ (c ω).dom})
    (hfwd : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hfr : ∀ᵐ ω ∂P, frontier ((c ω).dom : Set ℂ) ∩ H ⊆ range (β ω) ∪ range (α ω))
    {a k : ℝ} {hψ : Ω → DistOn upperHalfPlaneOpens} (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (hψ ω)) :
    Sec7.IsAEDeterminedBy P (fun ω => (Lemma72B.pocketRecord β α (fun ω => ((c ω).dom : Set ℂ)) h ω, hψ ω)) h := by
  classical
  have hS3 := hS.2.2.2.2.2.2.1
  have hh : Measurable h := hS3.1
  obtain ⟨-, -, -, hβ62, hα62, -, hae⟩ := hS3
  have hβm : ∀ t, Measurable fun ω => β ω t := hβ62.2.2.2.1
  have hαm : ∀ t, Measurable fun ω => α ω t := hα62.2.2.2.1
  set C : Ω → Set ℂ := fun ω => ((c ω).dom : Set ℂ) with hCdef
  have hCo : ∀ ω, IsOpen (C ω) := fun ω => (c ω).dom.isOpen
  have hβα : Measurable fun ω => (β ω, α ω) := (measurable_pi_iff.2 hβm).prodMk (measurable_pi_iff.2 hαm)
  have hA0 : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ mΩ := hβα.comap_le
  -- the transported field is measurable
  have hψe : hψ = fun ω => chartTransport (hcc ω) 1 a k (h ω) := funext fun ω =>
    (ht ω).eq_chartTransport (hcc ω)
      (locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω)))
  have hmem0 : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (c ω).dom} :=
    @Lemma71E.measurableSet_mem_of_closedBall Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C hCo
      hCm
  have hψm : Measurable hψ := by
    rw [hψe]
    exact measurable_chartTransport_random' hcc (fun z => hA0 _ (hmem0 z)) (fun z => (hfwd z).mono hA0 le_rfl)
      (fun z => (hliftm z).mono hA0 le_rfl) hliftc hh 1 a k
  -- the exterior record
  have hS0 : ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω))
      inferInstance] {ω | Disjoint (tsupport φ) (closure (C ω))} := fun φ =>
    @Lemma72B.measurableSet_disjoint_closure_of_mem Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance)
      C hCo hmem0 _ φ.hasCompactSupport
  have hQm : Measurable (Lemma72B.pocketRecord β α C h) :=
    Lemma72B.measurable_pocketRecord hβm hαm hh fun φ => hA0 _ (hS0 φ)
  set R : Ω → (((ℝ≥0 → ℂ) × (ℝ≥0 → ℂ)) × (TestOn upperHalfPlaneOpens → ℝ)) × DistOn upperHalfPlaneOpens :=
    fun ω => (Lemma72B.pocketRecord β α C h ω, hψ ω) with hRdef
  have hRm : Measurable R := hQm.prodMk hψm
  have hRle : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ MeasurableSpace.comap R inferInstance := by
    have : Measurable[MeasurableSpace.comap R inferInstance] fun ω => (β ω, α ω) :=
      (measurable_fst.comp measurable_fst).comp (comap_measurable R)
    exact this.comap_le
  -- (SR1), integrability, closed ranges and the dimension of the walls
  obtain ⟨hint, hSR1⟩ := sr1_seed hS
  set ε : ℝ := Dimension.onePointExponent 4 / 8 with hεdef
  have hop := Dimension.onePointExponent_pos (κ := 4) (by norm_num)
  have hop1 := Dimension.onePointExponent_le_one (κ := 4) (by norm_num)
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by rw [hεdef]; linarith
  have hε4 : ε < Dimension.onePointExponent 4 / 4 := by rw [hεdef]; linarith
  set A : Ω → Set ℂ := fun ω => range (β ω) ∪ range (α ω) with hAdef
  have hAcl : ∀ᵐ ω ∂P, closure (A ω) ∩ (upperHalfPlaneOpens : Set ℂ) ⊆ A ω := by
    filter_upwards [hae] with ω hω
    obtain ⟨-, hβs, hαs, -⟩ := hω
    have h1 : IsClosed (range (β ω)) := Theorem15D5.isClosed_range_of_tendsto_norm hβs.1 hβs.2.2.2.2
    have h2 : IsClosed (range (α ω)) := Theorem15D5.isClosed_range_of_tendsto_norm hαs.1 hαs.2.2.2.2
    rw [hAdef, (h1.union h2).closure_eq]
    exact inter_subset_left
  have hdim : ∀ᵐ ω ∂P, ∀ K, IsCompact K → K ⊆ (upperHalfPlaneOpens : Set ℂ) →
      dimH (A ω ∩ K) < ENNReal.ofReal (2 - 2 * ε) := by
    filter_upwards [ae_dimH_range_lt_seed hS hε4 (mem_insert _ _),
      ae_dimH_range_lt_seed hS hε4 (mem_insert_of_mem _ (mem_insert _ _))] with ω h1 h2 K _ hK
    rw [hAdef, union_inter_distrib_right, dimH_union]
    exact max_lt (h1 K hK) (h2 K hK)
  refine Lemma72B.isAEDeterminedBy_of_recorded_sides hRm hh hint hε0 hε1 (fun ζc => hSR1 hε0 ζc) hAcl hdim hCo hfr
    (fun φ => ?_) (fun φ => ?_)
  · -- inside the chamber: the pulled-back field and the chart
    have hψR : Measurable[MeasurableSpace.comap R inferInstance] hψ := measurable_snd.comp (comap_measurable R)
    exact Lemma72B.exists_record_in (𝓡 := MeasurableSpace.comap R inferInstance) hcc (fun z r => hRle _ (hCm z r))
      (fun z => (hfwd z).mono hRle le_rfl) (fun z => (hliftm z).mono hRle le_rfl) hliftc hψR ht φ
  · -- off the closed chamber: the exterior field
    set S : Set Ω := {ω | Disjoint (tsupport φ) (closure (C ω))} with hSdef
    have hSR : MeasurableSet[MeasurableSpace.comap R inferInstance] S := hRle _ (hS0 φ)
    have hgR : Measurable[MeasurableSpace.comap R inferInstance] fun ω => (R ω).1.2 φ :=
      (measurable_pi_apply φ).comp (measurable_snd.comp (measurable_fst.comp (comap_measurable R)))
    refine ⟨S, S.indicator fun ω => (R ω).1.2 φ, hSR, (hgR.indicator hSR).stronglyMeasurable,
      Eventually.of_forall fun ω hω => hω, Eventually.of_forall fun ω hω => ?_⟩
    rw [indicator_of_mem hω]
    exact (Lemma72B.outField_of_disjoint h hω).symm

end Field

/-! ### (iii): `(killed history, h_ψ)` is independent of `Q` -/

section Indep

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

-- adapted from `Sec7.Lemma72C.isTwoSeedCouplingOf_of_pocketChart` (any `κ > 0`, weights `> −2`)
/-- **The chamber pair is a two-seed coupling of `(h_ψ, killed history)`** under the measure `μ`: the clauses of the
chart form of the coupling (with the null sets of `μ` in `𝓖₀`), the chart transport `h_ψ` and the locality of the hulls
for `h_ψ` at the stopping times of `𝓖` before `T` (`Chamber4.exists_isOptionalHullCoupling_of_chart`; the killed driving
history of its global driver is almost surely that of `(W, T)`). -/
theorem isTwoSeedCouplingOf_of_chart {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓖 : Filtration ℝ≥0 mΩ}
    [𝓖.IsRightContinuous] {κ rL rR : ℝ} {γ : Ω → ℝ → ℂ} {W : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ≥0∞}
    {h hψ : Ω → DistOn upperHalfPlaneOpens} {c : Ω → Chart} {a k : ℝ} (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    (hnull : ∀ s, MeasurableSet s → μ s = 0 → MeasurableSet[𝓖 0] s)
    (hγ : ∀ᵐ ω ∂μ, ContinuousOn (γ ω) (Ici 0) ∧ InjOn (γ ω) (Ici 0) ∧ MapsTo (γ ω) (Ici 0) Hbar ∧
      γ ω 0 = 0 ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop ∧
      interior {u ∈ Ici (0 : ℝ) | 0 < u ∧ (γ ω u).im = 0} = ∅)
    (hW0 : ∀ ω, W 0 ω = 0) (hc : ∀ ω, ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < T ω})
    (hWa : AdaptedBefore 𝓖 T W)
    (hK : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ t → ∃ s : ℝ≥0, (s : ℝ≥0∞) < T ω ∧
      fwdHull (fun s : ℝ => W s.toNNReal ω) s = fillH (γ ω '' Icc 0 t))
    (hh : Measurable h) (hcc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hcf : Coupling.MartMeans2.IsChartCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) μ 𝓖 W
      (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T c a k h)
    (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (hψ ω))
    (hloc : ∀ τ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 τ → (∀ᵐ ω ∂μ, (τ ω : ℝ≥0∞) < T ω) →
      IsLocalSet (fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) hψ μ) :
    Lemma72C.IsTwoSeedCouplingOf κ rL rR μ hψ (killedHistory W (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T) := by
  have hψe : hψ = fun ω => chartTransport (hcc ω) 1 a k (h ω) := funext fun ω =>
    IsChartTransport.eq_chartTransport (hcc ω)
      (locallyIntegrableOn_of_continuousOn ((hcc ω).continuousOn_lift_inv (hliftc ω))) (ht ω)
  subst hψe
  obtain ⟨W', B, ζ, hC, htr, hhist⟩ := Chamber4.exists_isOptionalHullCoupling_of_chart hκ hL hR hnull hγ hW0 hc hWa
    hK hh hcc hdom hfwd hliftm hliftc hcf hloc
  exact ⟨𝓖, W', geomL W' LP.twoSeedXL, geomR W' LP.twoSeedXR, B, ζ, hC,
    htr.mono fun ω hω => by obtain ⟨η, hη, -⟩ := hω; exact ⟨η, hη⟩, hhist⟩

variable {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

/-- **The chamber chart is a function of the walls**: closed-ball and membership events of its domain, its forward map
and its (shifted) lift are `σ(β, α)`-measurable, and so are the events `{supp φ ∩ C̄ = ∅}`. -/
theorem measurable_chart_three (hpc : IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) :
    (∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (shiftLift (c ω) (n ω)).dom}) ∧
    (∀ (z : ℂ) (r : ℝ), MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | closedBall z r ⊆ ((shiftLift (c ω) (n ω)).dom : Set ℂ)}) ∧
    (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator fun ω => (shiftLift (c ω) (n ω)).1 z)) ∧
    (∀ z, Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      ({ω | z ∈ (shiftLift (c ω) (n ω)).dom}.indicator fun ω => (shiftLift (c ω) (n ω)).2.2 z)) ∧
    ∀ φ : TestOn upperHalfPlaneOpens, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | Disjoint (tsupport φ) (closure ((shiftLift (c ω) (n ω)).dom : Set ℂ))} := by
  obtain ⟨hC, hCm, -, hdom, hfm, hlm, -⟩ := hpc
  have hdomm : ∀ z, MeasurableSet[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance]
      {ω | z ∈ (shiftLift (c ω) (n ω)).dom} := fun z => by
    have e : {ω | z ∈ (shiftLift (c ω) (n ω)).dom} = {ω | z ∈ C ω} := by
      ext ω
      show z ∈ ((c ω).dom : Set ℂ) ↔ z ∈ C ω
      rw [hdom ω]
    rw [e]
    exact @Lemma71E.measurableSet_mem_of_closedBall Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) C (fun ω => (hC ω).1) hCm z
  refine ⟨hdomm, fun z r => ?_, hfm, fun z => ?_, fun φ => ?_⟩
  · have e : {ω | closedBall z r ⊆ ((shiftLift (c ω) (n ω)).dom : Set ℂ)} = {ω | closedBall z r ⊆ C ω} := by
      ext ω
      show closedBall z r ⊆ ((c ω).dom : Set ℂ) ↔ _
      rw [hdom ω]
      exact Iff.rfl
    rw [e]
    exact hCm z r
  · exact @measurable_indicator_shiftLift Ω (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) c n hn z
      (hdomm z) (hlm z)
  · exact @Lemma72B.measurableSet_disjoint_closure_of_mem Ω
      (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ))
      (fun ω => (shiftLift (c ω) (n ω)).dom.isOpen) hdomm _ φ.hasCompactSupport

/-- The exterior record `Q = ((β, α), h|_{ℍ ∖ C̄})` of the chamber is measurable. -/
theorem measurable_pocketRecord_three (hS : IsThreeLineSpace P h u₀ β α γ)
    (hpc : IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) :
    Measurable (Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h) := by
  obtain ⟨hh, -, -, hβ62, hα62, -, -⟩ := hS
  have hβα : Measurable fun ω => (β ω, α ω) :=
    (measurable_pi_iff.2 hβ62.2.2.2.1).prodMk (measurable_pi_iff.2 hα62.2.2.2.1)
  exact Lemma72B.measurable_pocketRecord hβ62.2.2.2.1 hα62.2.2.2.1 hh fun φ =>
    hβα.comap_le _ ((measurable_chart_three hpc hn).2.2.2.2 φ)

/-- **(iii): `(killed history, h_ψ)` is independent of the exterior record `Q`** (Wang–Wu Proposition 4.24; the
specification's Lemma 7.2 (iii)). On a three-line space with a chamber construction, a `σ(β, α)`-measurable branch and
the fixed-time chart coupling clause of the two-seed word `(rL; rR)` (`0 < κ < 8`, `rL, rR > −2`): under `P` and under
every `P[· | G]`, `G ∈ σ(Q)` of positive probability, the chamber pair is a two-seed coupling (`exists_cond_three`,
`isTwoSeedCouplingOf_of_chart`), so its law does not depend on the conditioning (Aux. lemma 51) and it is independent of
`Q` (`Sec7.Lemma72C.indepFun_of_forall_cond_isTwoSeedCouplingOf`). Conditional helper (on the (J5) clause). -/
theorem indepFun_three [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) (hL : -2 < rL)
    (hR : -2 < rR) (hS : IsThreeLineSpace P h u₀ β α γ) (hpc : IsPocketConstruction P β α γ C c γ')
    {n : Ω → ℤ} (hn : Measurable[MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance] n) {a' k : ℝ}
    (hcf : IsChartCouplingCharFunConst κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) P
      (prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ')
      (fun s ω => segDriver (γ' ω) s) (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL)
      (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR) (fun ω => capLife (γ' ω))
      (fun ω => shiftLift (c ω) (n ω)) a' k h) :
    IndepFun (fun ω => (killedHistory (fun s ω => segDriver (γ' ω) s)
        (geomL (fun s ω => segDriver (γ' ω) s) LP.twoSeedXL) (geomR (fun s ω => segDriver (γ' ω) s) LP.twoSeedXR)
        (fun ω => capLife (γ' ω)) ω, chartField (shiftLift (c ω) (n ω)) a' k (h ω)))
      (Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h) P := by
  have hh : Measurable h := hS.1
  obtain ⟨hdomm, -, hfm', hlm', -⟩ := measurable_chart_three hpc hn
  have hpc' := hpc
  obtain ⟨-, -, hconf, -, -, -, hlc, -, -, -, hseg, -, -⟩ := hpc'
  set 𝓐 := prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' with h𝓐def
  set W : ℝ≥0 → Ω → ℝ := fun s ω => segDriver (γ' ω) s with hWdef
  set T : Ω → ℝ≥0∞ := fun ω => capLife (γ' ω) with hTdef
  have hcc' : ∀ ω, (shiftLift (c ω) (n ω)).IsConformal := fun ω => isConformal_shiftLift (hconf ω) (n ω)
  have hlc' : ∀ ω, ContinuousOn (shiftLift (c ω) (n ω)).2.2 (shiftLift (c ω) (n ω)).dom := fun ω =>
    continuousOn_shiftLift (hlc ω) (n ω)
  have hWc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω} := fun ω =>
    (hseg ω).segDriver_spec.2.1
  have hWa : AdaptedBefore 𝓐 T W := adaptedBefore_three hS hpc
  have h₀ : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ 𝓐 0 :=
    le_prefixFiltrationOf (comap_pair_le_three hS) γ' 0
  have ht : ∀ ω, IsChartTransport (shiftLift (c ω) (n ω)) 1 a' k (h ω)
      (chartField (shiftLift (c ω) (n ω)) a' k (h ω)) := fun ω =>
    isChartTransport_chartField (hcc' ω) (hlc' ω) a' k (h ω)
  have hQm := measurable_pocketRecord_three hS hpc hn
  have hHm : Measurable (killedHistory W (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T) := by
    have hX := Coupling.isMeasurableKilledDriving_of_adaptedBefore hWa
      (fun i => Lemma71C.adaptedBefore_geomL hWc hWa LP.twoSeedXL i)
      (fun i => Lemma71C.adaptedBefore_geomR hWc hWa LP.twoSeedXR i)
    exact measurable_killedHistory hX
  -- the chamber pair under `P[· | G]`
  have hcoup : ∀ G : Set Ω, MeasurableSet[MeasurableSpace.comap
      (Lemma72B.pocketRecord β α (fun ω => ((shiftLift (c ω) (n ω)).dom : Set ℂ)) h) inferInstance] G → P G ≠ 0 →
      Lemma72C.IsTwoSeedCouplingOf κ rL rR (P[|G]) (fun ω => chartField (shiftLift (c ω) (n ω)) a' k (h ω))
        (killedHistory W (geomL W LP.twoSeedXL) (geomR W LP.twoSeedXR) T) := by
    intro G hG hPG
    have : IsProbabilityMeasure (P[|G]) := cond_isProbabilityMeasure hPG
    obtain ⟨𝓖G, h𝓖G, hle, hnullG, hcfG, hlocG⟩ := exists_cond_three hS hpc hn hcf G hG hPG
    have : 𝓖G.IsRightContinuous := h𝓖G
    have h𝓐G : 𝓐 ≤ 𝓖G := le_trans (Ito.le_usualAugmentation 𝓐 P) hle
    have h0G : MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance ≤ 𝓖G 0 := h₀.trans (h𝓐G 0)
    exact isTwoSeedCouplingOf_of_chart hκ hL hR hnullG (Eventually.of_forall fun ω => hseg ω)
      (fun ω => (hseg ω).segDriver_spec.1) hWc (Ito.adaptedBefore_mono h𝓐G hWa)
      (Eventually.of_forall fun ω => (hseg ω).segDriver_spec.2.2) hh hcc' (fun z => h0G _ (hdomm z))
      (fun z => (hfm' z).mono h0G le_rfl) (fun z => (hlm' z).mono h0G le_rfl) hlc' hcfG ht hlocG
  have hPuniv : P univ ≠ 0 := by rw [measure_univ]; exact one_ne_zero
  have hPc := hcoup univ MeasurableSet.univ hPuniv
  rw [cond_univ] at hPc
  exact Lemma72C.indepFun_of_forall_cond_isTwoSeedCouplingOf hQm hκ hκ8 hL hR hHm hPc hcoup

end Indep

end InteractingSLE.WangWu.ChamberCond

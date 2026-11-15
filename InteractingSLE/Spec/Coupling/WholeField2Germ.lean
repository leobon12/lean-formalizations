import InteractingSLE.Spec.Coupling.WholeField2Kernel

/-!
# The history-marked germ σ-algebras `Γ_τ`: hulls are history-measurable, `Γ` is nested and carries the kernel

Packet PROVE-WHOLEFIELD2 (ruling R36), item (3), first step. Specification Aux. lemma 47, proof ("The sigma-algebras
`𝒢⁰_t` are increasing. Indeed, the old hull is a function of the later recorded history and is contained in the later
hull …", p. 228) and Aux. lemma 48 (`Γ_t`: "the raw sigma-algebra of `𝓗_t` and the current full canonical hull germ.
These sigma-algebras are nested and already include the earlier hull germs", p. 230).

The germ σ-algebra of the landed library is `germSigma A h = ⨅ₙ 𝒜_{δₙ}`, `𝒜_δ = σ(A) ∨ σ(h on the δ-neighbourhood of
A)`. Joining the history `𝓕` after the intersection (`germSigma A h ⊔ 𝓕`) does not obviously give nested σ-algebras
(an intersection does not commute with a join). Joining it **before** the intersection does:

`Γ(𝓕, A) = ⨅ₙ (𝓕 ⊔ 𝒜_{δₙ})`  (`histGerm`).

* `measurable_hull_stopping` (**hulls are history-measurable**): for a stopping time `τ < ζ` of the frozen driving
  filtration, every hitting-measurable version of `K_τ` is `𝓕_τ`-measurable. (Each hitting event `{K_τ ∩ U ≠ ∅}` is,
  up to a null set, the union over a compact exhaustion `Cₖ ↑ U` of the complements of the `𝓕_τ`-events
  `{Cₖ ∩ K_τ = ∅}` of `exists_measurableSet_ae_iff_disjoint`, and `𝓕_τ` contains the null sets.)
* `histGerm_mono` (**nesting**): `Γ(𝓕₁, A₁) ≤ Γ(𝓕₂, A₂)` when `𝓕₁ ≤ 𝓕₂`, `A₁` is `𝓕₂`-measurable, `A₁ ⊆ A₂`
  almost surely and `𝓕₂` contains the null sets; for the hulls: `Γ_σ ≤ Γ_τ` for stopping times `σ ≤ τ < ζ`
  (`histGerm_hull_mono`).
* `ae_condExp_histGerm_hull_eq` (**the kernel on `Γ_τ`**): the landed germ law holds for every σ-algebra between
  the germ σ-algebra and the cover σ-algebras (`exists_condExp_germSigmaK`), in particular for `Γ_τ`; hence the frozen
  kernel of `ae_condExp_germSigma_hull_eq` holds given `Γ_τ`. This is (PK1) of Aux. lemma 48 with nested `Γ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric Coupling

/-! ### Null sets and stopping σ-algebras -/

section Null

variable {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A stopping σ-algebra of a filtration containing the null sets contains the null sets. -/
theorem measurableSet_stopping_of_null {𝓖 : Filtration ℝ≥0 mΩ}
    (hnull : ∀ t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝓖 t] N) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime 𝓖 τ) {N : Set Ω} (hN : MeasurableSet N) (h0 : P N = 0) :
    MeasurableSet[hτ.measurableSpace] N :=
  ⟨le_iSup 𝓖 0 _ (hnull 0 N hN h0), fun i => hnull i _ (hN.inter (𝓖.le i _ (hτ i)))
    (measure_mono_null inter_subset_left h0)⟩

/-- A measurable set almost surely equal to a set of a σ-algebra `ℋ ≤ mΩ` containing the null sets belongs to `ℋ`. -/
theorem measurableSet_of_ae_eq (hℋ : ℋ ≤ mΩ)
    (hnull : ∀ N : Set Ω, MeasurableSet[mΩ] N → P N = 0 → MeasurableSet[ℋ] N) {E G : Set Ω}
    (hE : MeasurableSet[mΩ] E) (hG : MeasurableSet[ℋ] G) (hEG : E =ᵐ[P] G) : MeasurableSet[ℋ] E := by
  have hd : MeasurableSet[ℋ] (symmDiff E G) :=
    hnull _ (hE.symmDiff (hℋ _ hG)) (measure_symmDiff_eq_zero_iff.2 hEG)
  have e : E = symmDiff (symmDiff E G) G := by rw [symmDiff_symmDiff_cancel_right]
  rw [e]
  exact hd.symmDiff hG

end Null

/-! ### Compact exhaustion of an open subset of `ℍ` -/

/-- The compact pieces `{z : dist(z, Uᶜ) ≥ 1/(k+1), |z| ≤ k}` of an open set `U`. -/
def openExhaust (U : Set ℂ) (k : ℕ) : Set ℂ :=
  {z | 1 / ((k : ℝ) + 1) ≤ infDist z Uᶜ} ∩ closedBall 0 k

theorem isCompact_openExhaust (U : Set ℂ) (k : ℕ) : IsCompact (openExhaust U k) :=
  (isCompact_closedBall 0 (k : ℝ)).of_isClosed_subset
    ((isClosed_le continuous_const (continuous_infDist_pt _)).inter isClosed_closedBall)
    inter_subset_right

theorem openExhaust_subset {U : Set ℂ} (k : ℕ) : openExhaust U k ⊆ U := by
  intro z hz
  by_contra hzU
  have h0 : infDist z Uᶜ = 0 := infDist_zero_of_mem hzU
  have := hz.1
  rw [mem_ofPred_eq, h0] at this
  exact absurd this (not_le.2 (by positivity))

theorem iUnion_openExhaust {U : Set ℂ} (hU : IsOpen U) (hne : Uᶜ.Nonempty) :
    (⋃ k, openExhaust U k) = U := by
  refine subset_antisymm (iUnion_subset fun k => openExhaust_subset k) fun z hz => ?_
  have hpos : 0 < infDist z Uᶜ := (hU.isClosed_compl.notMem_iff_infDist_pos hne).1 (fun h => h hz)
  obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt hpos
  obtain ⟨k₂, hk₂⟩ := exists_nat_ge ‖z‖
  refine mem_iUnion.2 ⟨max k₁ k₂, ?_, ?_⟩
  · show 1 / (((max k₁ k₂ : ℕ) : ℝ) + 1) ≤ infDist z Uᶜ
    refine le_trans ?_ hk₁.le
    gcongr
    exact_mod_cast le_max_left _ _
  · rw [mem_closedBall_zero_iff]
    exact hk₂.trans (by exact_mod_cast le_max_right _ _)

/-! ### The history-marked germ σ-algebra and its nesting -/

section HistGerm

variable {Ω : Type*} {ℋ ℋ₁ ℋ₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **The history-marked germ σ-algebra** `Γ(ℋ, A) = ⨅ₙ (ℋ ⊔ 𝒜_{1/(n+1)})`: the marks `ℋ` joined to `A` and the
field on the `1/(n+1)`-neighbourhoods of `A`, before the intersection over `n`. -/
@[instance_reducible]
def histGerm (ℋ : MeasurableSpace Ω) (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    MeasurableSpace Ω :=
  ⨅ n : ℕ, ℋ ⊔ germSigmaAt A h (1 / ((n : ℝ) + 1))

omit mΩ in
theorem germSigma_le_histGerm (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) :
    germSigma A h ≤ histGerm ℋ A h :=
  le_iInf fun n => (iInf_le (fun n : ℕ => germSigmaAt A h (1 / ((n : ℝ) + 1))) n).trans le_sup_right

omit mΩ in
theorem le_histGerm (A : Ω → Set ℂ) (h : Ω → DistOn upperHalfPlaneOpens) : ℋ ≤ histGerm ℋ A h :=
  le_iInf fun _ => le_sup_left

theorem histGerm_le {A : Ω → Set ℂ} {h : Ω → DistOn upperHalfPlaneOpens} (hℋ : ℋ ≤ mΩ)
    (hA : Measurable[mΩ, hittingSigma] A) (hh : Measurable h) : histGerm ℋ A h ≤ mΩ :=
  (iInf_le _ 0).trans (sup_le hℋ (germSigmaAt_le' hA hh (by positivity)))

omit mΩ in
/-- The germ neighbourhood is monotone in the set. -/
theorem germNbhd_mono_set {δ : ℝ} {S T : Set ℂ} (hST : S ⊆ T) : germNbhd δ S ⊆ germNbhd δ T := by
  rintro z ⟨hz, h1 | h1⟩
  · exact ⟨hz, Or.inl (thickening_subset_of_subset δ
      (union_subset_union (inter_subset_inter_left H hST) le_rfl) h1)⟩
  · exact ⟨hz, Or.inr h1⟩

/-- **Nesting of the history-marked germ σ-algebras.** If `ℋ₁ ≤ ℋ₂`, the set `A₁` is `ℋ₂`-measurable and almost surely
contained in `A₂`, and `ℋ₂` contains the null sets, then `Γ(ℋ₁, A₁) ≤ Γ(ℋ₂, A₂)`. -/
theorem histGerm_mono (hℋ : ℋ₁ ≤ ℋ₂) (hℋ₂ : ℋ₂ ≤ mΩ)
    (hnull : ∀ N : Set Ω, MeasurableSet[mΩ] N → P N = 0 → MeasurableSet[ℋ₂] N)
    {A₁ A₂ : Ω → Set ℂ} (hA₁ : Measurable[ℋ₂, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h) (hsub : ∀ᵐ ω ∂P, A₁ ω ⊆ A₂ ω) :
    histGerm ℋ₁ A₁ h ≤ histGerm ℋ₂ A₂ h := by
  refine le_iInf fun n => (iInf_le _ n).trans (sup_le (hℋ.trans le_sup_left) ?_)
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  have hle : ℋ₂ ⊔ germSigmaAt A₂ h δ ≤ mΩ := sup_le hℋ₂ (germSigmaAt_le' hA₂ hh hδ)
  refine sup_le (hA₁.comap_le.trans le_sup_left) (MeasurableSpace.generateFrom_le ?_)
  rintro _ ⟨φ, B, hB, rfl⟩
  have hS := measurableSet_subset_germNbhd φ.hasCompactSupport.isCompact φ.tsupport_subset hδ
  have hA₁m : Measurable[mΩ, hittingSigma] A₁ := hA₁.mono hℋ₂ le_rfl
  have hE : MeasurableSet[mΩ] ({ω | tsupport φ ⊆ germNbhd δ (A₁ ω)} ∩ (fun ω => h ω φ) ⁻¹' B) :=
    (hA₁m hS).inter ((measurable_distOn_apply φ).comp hh hB)
  have hG₁ : MeasurableSet[ℋ₂ ⊔ germSigmaAt A₂ h δ] {ω | tsupport φ ⊆ germNbhd δ (A₁ ω)} :=
    le_sup_left (α := MeasurableSpace Ω) _ (hA₁ hS)
  have hG₂ : MeasurableSet[ℋ₂ ⊔ germSigmaAt A₂ h δ]
      ({ω | tsupport φ ⊆ germNbhd δ (A₂ ω)} ∩ (fun ω => h ω φ) ⁻¹' B) :=
    le_sup_right (α := MeasurableSpace Ω) _ (le_sup_right (α := MeasurableSpace Ω) _
      (MeasurableSpace.measurableSet_generateFrom ⟨φ, B, hB, rfl⟩))
  refine measurableSet_of_ae_eq hle (fun N hN h0 => le_sup_left (α := MeasurableSpace Ω) _ (hnull N hN h0))
    hE (hG₁.inter hG₂) ?_
  filter_upwards [hsub] with ω hω
  apply propext
  simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
  exact ⟨fun h' => ⟨h'.1, h'.1.trans (germNbhd_mono_set hω), h'.2⟩, fun h' => ⟨h'.1, h'.2.2⟩⟩

end HistGerm

/-- Conditional expectations given `𝒦₁ ≤ 𝒦₂` agree when the one given `𝒦₂` has a `𝒦₁`-measurable version. -/
theorem condExp_ae_eq_of_le_of_ae_eq {Ω : Type*} {𝒦₁ 𝒦₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h12 : 𝒦₁ ≤ 𝒦₂) (h2 : 𝒦₂ ≤ mΩ) {f g : Ω → E} (hg : StronglyMeasurable[𝒦₁] g)
    (hfg : P[f | 𝒦₂] =ᵐ[P] g) : P[f | 𝒦₁] =ᵐ[P] g := by
  have hgi : Integrable g P := integrable_condExp.congr hfg
  calc P[f | 𝒦₁] =ᵐ[P] P[P[f | 𝒦₂] | 𝒦₁] := (condExp_condExp_of_le h12 h2).symm
    _ =ᵐ[P] P[g | 𝒦₁] := condExp_congr_ae hfg
    _ = g := condExp_of_stronglyMeasurable (h12.trans h2) hg hgi

/-! ### The frozen coupling -/

section Coupling

universe u

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- A stopping σ-algebra of the frozen driving filtration contains the null sets. -/
theorem measurableSet_stopping_driving_of_null (hX : IsMeasurableKilledDriving W VL VR ζ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ) {N : Set Ω}
    (hN : MeasurableSet N) (h0 : P N = 0) : MeasurableSet[hτ.measurableSpace] N :=
  measurableSet_stopping_of_null (fun t _ hN h0 => Ito.measurableSet_usualAugmentation_of_null hN h0 t) hτ
    hN h0

omit [IsProbabilityMeasure P] in
/-- **Hulls are history-measurable.** For a stopping time `τ < ζ` of the frozen driving filtration, every
hitting-measurable version `A` of `K_τ` is measurable for the stopped history `𝓕_τ`. -/
theorem measurable_hull_stopping (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : ℕ → Ω → ℝ≥0}
    (hσ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :
    Measurable[hτ.measurableSpace, hittingSigma] A := by
  refine @measurable_generateFrom _ _ hτ.measurableSpace _ _ ?_
  rintro _ ⟨U, hU, hUH, rfl⟩
  have hne : Uᶜ.Nonempty := ⟨0, fun h0 => by
    have : (0 : ℝ) < (0 : ℂ).im := hUH h0
    simp at this⟩
  choose G hGm hGiff using fun k => exists_measurableSet_ae_iff_disjoint hE hX hσ hτ hτζ
    (isCompact_openExhaust U k) ((openExhaust_subset k).trans hUH)
  refine measurableSet_of_ae_eq hτ.measurableSpace_le
    (fun N hN h0 => measurableSet_stopping_driving_of_null hX hτ hN h0)
    (hA (measurableSet_hitting hU hUH)) (MeasurableSet.iInter fun k => hGm k).compl ?_
  filter_upwards [ae_all_iff.2 hGiff, hAK] with ω h1 h2
  apply propext
  simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff, mem_iInter, not_forall, h1, h2]
  constructor
  · rintro ⟨z, hzA, hzU⟩
    rw [← iUnion_openExhaust hU hne] at hzU
    obtain ⟨k, hk⟩ := mem_iUnion.1 hzU
    exact ⟨k, fun hd => Set.disjoint_left.1 hd hk hzA⟩
  · rintro ⟨k, hk⟩
    obtain ⟨z, hzC, hzK⟩ := Set.not_disjoint_iff.1 hk
    exact ⟨z, hzK, openExhaust_subset k hzC⟩

omit [IsProbabilityMeasure P] in
/-- **Nesting along the hulls**: for stopping times `σ ≤ τ < ζ` of the frozen driving filtration and
hitting-measurable versions `A_σ`, `A_τ` of the hulls, `Γ(𝓕_σ, A_σ) ≤ Γ(𝓕_τ, A_τ)`. -/
theorem histGerm_hull_mono (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ₀) {σ τ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hστ : σ ≤ τ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {Aσ Aτ : Ω → Set ℂ} (hAσ : Measurable[mΩ, hittingSigma] Aσ) (hAτ : Measurable[mΩ, hittingSigma] Aτ)
    (hAσK : ∀ᵐ ω ∂P, Aσ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0))
    (hAτK : ∀ᵐ ω ∂P, Aτ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hh : Measurable h) :
    histGerm hσ.measurableSpace Aσ h ≤ histGerm hτ.measurableSpace Aτ h := by
  refine histGerm_mono (P := P) (hσ.measurableSpace_mono hτ hστ) hτ.measurableSpace_le
    (fun N hN h0 => measurableSet_stopping_driving_of_null hX hτ hN h0)
    ((measurable_hull_stopping hE hX hσ₀ hσ hσζ hAσ hAσK).mono (hσ.measurableSpace_mono hτ hστ) le_rfl)
    hAτ hh ?_
  filter_upwards [hAσK, hAτK, hτζ] with ω h1 h2 h3
  rw [h1, h2]
  refine (QuantumZipper.fwdHull_mono).1 ?_
  have hτtop : τ ω ≠ ⊤ := fun h' => by rw [h'] at h3; exact absurd h3 (not_lt.2 le_top)
  have hle := hστ ω
  rw [← coe_untopD_of_ne_top hτtop] at hle
  have hσtop : σ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
  rw [← coe_untopD_of_ne_top hσtop] at hle
  exact NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 hle)

/-- **The frozen kernel given `Γ_τ`** ((PK1) of Aux. lemma 48 with the nested σ-algebras `Γ_τ = Γ(𝓕_τ, A)`). Under the
hypotheses of `ae_condExp_germSigma_hull_eq`, the same conditional mean and characteristic function hold given
`Γ_τ`, almost surely on `{supp φ ∩ K_τ = ∅}`. -/
theorem ae_condExp_histGerm_hull_eq (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hAK : ∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    {u : Ω → ℂ → ℝ}
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (φ : TestOn upperHalfPlaneOpens) :
    (∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => centredField h u₀ ω' φ | histGerm hτ.measurableSpace A (centredField h u₀)]) ω =
        (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) -
          ∫ z, u₀ z * φ z) ∧
    ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A ω) →
      (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
          histGerm hτ.measurableSpace A (centredField h u₀)]) ω =
        Complex.exp (Complex.I * (((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
          ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z) - ∫ z, u₀ z * φ z : ℝ) : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ A ω) φ φ) : ℝ) : ℂ) := by
  have hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  have hℋ : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hτ hτζ hA hAK
  have hmk := isCoverMarking_history hh0 hA hℋ hloc
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := by
    filter_upwards [((hC.2.2.2.choose_spec τ hτ hτζ).1).2.1, hAK] with ω h1 h2
    rw [h2]
    exact h1
  have h𝒦tr : ∀ j, histGerm hτ.measurableSpace A (centredField h u₀) ≤
      aeSigma (coverSigmaM (MeasurableSpace.comap A hittingSigma ⊔ hτ.measurableSpace) j A
        (centredField h u₀)) P := by
    intro j
    refine (iInf_le _ (j + 1)).trans (sup_le ?_ ?_)
    · exact (le_sup_right : hτ.measurableSpace ≤ MeasurableSpace.comap A hittingSigma ⊔ hτ.measurableSpace).trans
        ((le_sup_left : _ ≤ coverSigmaM _ j A (centredField h u₀)).trans (le_aeSigma _ P))
    · rw [← coverRad_eq j]
      exact germSigmaAt_le_aeSigmaM hh0 le_sup_left j
  have h𝒦le := histGerm_le (h := centredField h u₀) hℋ hA hh0.measurable
  obtain ⟨M, hMg, -, hM1, hM2⟩ := exists_condExp_germSigmaK hh0 hA hmk hAc
    (germSigma_le_histGerm A (centredField h u₀)) h𝒦le h𝒦tr φ
  have h12 : germSigma A (centredField h u₀) ⊔ hτ.measurableSpace ≤
      histGerm hτ.measurableSpace A (centredField h u₀) :=
    sup_le (germSigma_le_histGerm A _) (le_histGerm A _)
  -- the two conditional means agree
  have hmean : P[fun ω' => centredField h u₀ ω' φ | histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      P[fun ω' => centredField h u₀ ω' φ | germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] := by
    have hM' : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] M :=
      hMg.mono le_sup_left le_rfl
    have hMs : StronglyMeasurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] M :=
      hM'.stronglyMeasurable
    exact hM1.symm.trans (condExp_ae_eq_of_le_of_ae_eq h12 h𝒦le hMs hM1.symm).symm
  have hchar : P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
        histGerm hτ.measurableSpace A (centredField h u₀)] =ᵐ[P]
      P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' φ : ℂ)) |
        germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] := by
    have hv : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]
        fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) φ φ :=
      (measurable_comap_zeroGFFTestCov_compl A φ φ).mono
        ((comap_le_germSigma A _).trans le_sup_left) le_rfl
    have hM' : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace] M :=
      hMg.mono le_sup_left le_rfl
    have hF : Measurable[germSigma A (centredField h u₀) ⊔ hτ.measurableSpace]
        fun ω => Complex.exp (Complex.I * (M ω : ℂ)) *
          ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (A ω)) φ φ) : ℝ) : ℂ) := by
      refine Measurable.mul ?_ ?_
      · exact Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hM'))
      · exact Complex.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul hv))
    have hFs := hF.stronglyMeasurable
    exact hM2.symm.trans (condExp_ae_eq_of_le_of_ae_eq h12 h𝒦le hFs hM2.symm).symm
  obtain ⟨k1, k2⟩ := ae_condExp_germSigma_hull_eq hC hκ hu₀ hX hτ hτζ hA hAK hu φ
  refine ⟨?_, ?_⟩
  · filter_upwards [k1, hmean] with ω h1 h2 hdis
    rw [h2]
    exact h1 hdis
  · filter_upwards [k2, hchar] with ω h1 h2 hdis
    rw [h2]
    exact h1 hdis

/-- **(GB2) in martingale form: the frozen mean is a martingale in the stopped germ filtration** (Aux. lemma 47,
proof, (GB2): "`E[(h, φ) | 𝒢⁰_{t∧σ}] = M_{t∧σ}(z)`. The right side is a square-integrable martingale in this stopped
germ filtration"). For a stopping time `σ < ζ` of the frozen driving filtration there are hitting-measurable versions
`A t` of the hulls `K_{t∧σ}` such that `𝒢 t = Γ(𝓕_{t∧σ}, A t)` is a filtration (nested by `histGerm_hull_mono`)
containing the stopped history, and for every test function `φ` the Doob martingale `E[(h⁰, φ) | 𝒢 t]` equals,
almost surely on `{supp φ ∩ K_{t∧σ} = ∅}`, the frozen mean `(𝔥_{t∧σ} − 𝔥₀, φ)` (for any bounded harmonic
extensions `u t ω` of the data at `t ∧ σ`). -/
theorem exists_germFiltration_martingale (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) :
    ∃ (A : ℝ≥0 → Ω → Set ℂ) (𝒢 : Filtration ℝ≥0 mΩ),
      (∀ t, Measurable[mΩ, hittingSigma] (A t)) ∧
      (∀ t, ∀ᵐ ω ∂P, A t ω = fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0)) ∧
      (∀ t, 𝒢 t = histGerm (hσ.min_const t).measurableSpace (A t) (centredField h u₀)) ∧
      (∀ t, (hσ.min_const t).measurableSpace ≤ 𝒢 t) ∧
      ∀ φ : TestOn upperHalfPlaneOpens,
        Martingale (fun t => P[fun ω => centredField h u₀ ω φ | 𝒢 t]) 𝒢 P ∧
        ∀ (u : ℝ≥0 → Ω → ℂ → ℝ), (∀ (t : ℝ≥0) (ω : Ω), IsBoundedHarmonicExtension
            (forceBoundaryData κ ρL ρR
              (fun i => VL i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω)
              (fun i => VR i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω))
            (forceJumpSet
              (fun i => VL i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω)
              (fun i => VR i ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω -
                W ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0) ω)) (u t ω)) →
          ∀ t : ℝ≥0, ∀ᵐ ω ∂P, Disjoint (tsupport φ) (A t ω) →
            (P[fun ω' => centredField h u₀ ω' φ | 𝒢 t]) ω =
              (∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) (u t ω) z * φ z) - ∫ z, u₀ z * φ z := by
  have hτ : ∀ t : ℝ≥0, IsStoppingTime (drivingFiltration P hX) fun ω => min (σ ω) (t : WithTop ℝ≥0) :=
    fun t => hσ.min_const t
  have hτζ : ∀ t : ℝ≥0, ∀ᵐ ω ∂P, ((min (σ ω) (t : WithTop ℝ≥0) : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
    intro t
    filter_upwards [hσζ] with ω hω
    exact lt_of_le_of_lt (min_le_left _ _) hω
  have hh0m := measurable_centredField hC.2.1 u₀
  have hE := hC.1
  have hker := hC.2.2.2.choose_spec
  -- versions of the hulls
  have hver : ∀ t : ℝ≥0, ∃ A' : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A' ∧
      A' =ᵐ[P] fun ω => fwdHull (fun s : ℝ => W s.toNNReal ω)
        ((min (σ ω) (t : WithTop ℝ≥0)).untopD 0 : ℝ≥0) := fun t => by
    obtain ⟨A', hA'm, hA'e, -⟩ := IsLocalSet.exists_measurable_version
      ((hker _ (hτ t) (hτζ t)).1) hC.2.1
    exact ⟨A', hA'm, hA'e⟩
  choose A hAm hAK using hver
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exfalso
    have hF : ∀ᵐ ω ∂P, False := by
      filter_upwards [hE.2.2.2.2, hσζ] with ω hp hlt
      rw [WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold hp hseed] at hlt
      exact ENNReal.not_lt_zero hlt
    obtain ⟨_, h'⟩ := hF.exists
    exact h'
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, -⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  -- the stopped germ filtration
  let 𝒢 : Filtration ℝ≥0 mΩ :=
    { seq := fun t => histGerm (hτ t).measurableSpace (A t) (centredField h u₀)
      mono' := fun s t hst => histGerm_hull_mono hE hX hσ₀ (hτ s) (hτ t)
        (fun ω => min_le_min le_rfl (WithTop.coe_le_coe.2 hst)) (hτζ s) (hτζ t) (hAm s) (hAm t) (hAK s)
          (hAK t) hh0m
      le' := fun t => histGerm_le (hτ t).measurableSpace_le (hAm t) hh0m }
  refine ⟨A, 𝒢, hAm, hAK, fun t => rfl, fun t => le_histGerm _ _, fun φ => ⟨?_, ?_⟩⟩
  · exact martingale_condExp _ 𝒢 P
  · intro u hu t
    exact (ae_condExp_histGerm_hull_eq hC hκ hu₀ hX (hτ t) (hτζ t) (hAm t) (hAK t) (hu t) φ).1

end Coupling

end WholeField

end InteractingSLE

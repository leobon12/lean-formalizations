/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField5Life
import InteractingSLE.Spec.Sec2.RestartLaw

/-!
# (WF7): the restarted driving law given the germ

Packet PROVE-WHOLEFIELD5, (WF7) (follow-up note C.2, `ig1_followup_proofs.txt` L1527–1541: "At an own-filtration stop
`τ < T_*`, the future state and noise solve the same restarted integrated system under conditional laws given `𝒢_τ`
… The future Brownian increments are independent of `𝒢_τ`, and the current state is `H_τ`-measurable").

**Statement** (`exists_restart_germ`). For the frozen coupling, a driving stop `T < ζ` (positive, or a separated force
word) and every event `A` of the germ `Γ(𝓕_T, K_T)`:

  `ℙ[A ∩ {t_j < ζ − T, (W_{T+t_j} − W_T, V_{T+t_j} − W_T, B_{T+t_j} − B_T) ∈ K_j ∀ j}] = ∫_A g dℙ`

with one `𝓕_T`-measurable `g` (almost surely the canonical restart law `restartLaw(V_T − W_T)` of Theorem 2.2): the
conditional law of the restarted future given the germ depends only on the stopped driving history.

**Proof (added here).** On `Ω × Ω` with `P ⊗ P`, complete the noise of the lifetime germ filtration
(`exists_lifetimeGerm`) by an independent Brownian motion (`IsTCExpMartingale.isFilteredBrownianReal_complNoise`): the
completed noise `β` is a Brownian motion of the usual augmentation `𝓖` of `𝒢 ⊗ 𝓦`, and equals `B` before `ζ`. The
lifted driving process `(W, V)∘fst` with noise `β` and lifetime `ζ∘fst` is then an integrated `SLE_κ(ρ)` evolution of
`(Ω × Ω, 𝓖, P ⊗ P)` (the pathwise conditions only involve the noise before `ζ`). Theorem 2.2's restart law in this
filtration (`Sec2.Restart.measure_restart_killedState`) applies to the lifted germ events (`fst⁻¹ A ∈ 𝓖_T`, since the
germ lies in the stopping σ-algebra of `𝒢` at `T`). Projecting back (`Measure.prod_prod`) gives the identity. Theorem
2.2's weak uniqueness is not used, only its pathwise uniqueness inside the restart law; the Brownian increments after
`T` are independent of the germ because they are Brownian in a filtration containing it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric Coupling Sec2 Sec2.Restart Sec2.Assembly

universe u

/-! ### Lifting stopping σ-algebras to a product -/

section Lift

variable {Ω Ω₀ : Type*} [mΩ : MeasurableSpace Ω] [m₀ : MeasurableSpace Ω₀]

/-- A stopping σ-algebra lifts along the first projection into any filtration containing the lifted one. -/
theorem measurableSet_stopping_fst {𝒢 : Filtration ℝ≥0 mΩ}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))}
    (hle : ∀ t, (𝒢 t).comap Prod.fst ≤ 𝓖 t) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝒢 τ)
    (hτ' : IsStoppingTime 𝓖 fun p => τ p.1) {S : Set Ω} (hS : MeasurableSet[hτ.measurableSpace] S) :
    MeasurableSet[hτ'.measurableSpace] (Prod.fst ⁻¹' S) := by
  rw [IsStoppingTime.measurableSet] at hS ⊢
  refine ⟨?_, fun t => hle t _ ⟨_, hS.2 t, rfl⟩⟩
  have h1 : MeasurableSet[MeasurableSpace.comap (Prod.fst : Ω × Ω₀ → Ω) (⨆ t, (𝒢 t : MeasurableSpace Ω))]
      ((Prod.fst : Ω × Ω₀ → Ω) ⁻¹' S) := ⟨S, hS.1, rfl⟩
  rw [MeasurableSpace.comap_iSup] at h1
  exact iSup_mono hle _ h1

/-- The lift of a stopping time along the first projection. -/
theorem isStoppingTime_fst {𝒢 : Filtration ℝ≥0 mΩ}
    {𝓖 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))}
    (hle : ∀ t, (𝒢 t).comap Prod.fst ≤ 𝓖 t) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝒢 τ) :
    IsStoppingTime 𝓖 fun p : Ω × Ω₀ => τ p.1 := fun t => hle t _ ⟨_, hτ t, rfl⟩

end Lift

/-! ### The restart identity given the germ -/

section Coupling

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- An evolution whose lifetime exceeds a time `T` almost surely has an admissible seed. -/
theorem not_threshold_seed_of_ae_lt (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    {T : Ω → ℝ≥0} (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) :
    ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
  intro hth
  obtain ⟨ω, hp, hω⟩ := (hE.2.2.2.2.and hTζ).exists
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by simp) hω
  obtain ⟨hw0, hL0, hR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -, -⟩ := hp
  have := hnt 0 h0
  rw [hw0, funext hL0, funext hR0] at this
  exact this hth

/-- **(WF7): the restarted driving law given the germ.** For the frozen coupling, a driving stop `T < ζ` that is
positive (or a separated force word), times `t_j` and Borel sets `K_j`, there is one `𝓕_T`-measurable `g`
(almost surely the canonical restart law `restartLaw(V_T − W_T)` of Theorem 2.2) such that for every event `A` of
the germ `Γ(𝓕_T, K_T)`:
`ℙ[A ∩ {t_j < ζ − T, (W_{T+t_j} − W_T, V_{T+t_j} − W_T, B_{T+t_j} − B_T) ∈ K_j ∀ j}] = ∫_A g dℙ`. -/
theorem exists_restart_germ (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hTζ : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω) (hT0 : ∀ᵐ ω ∂P, 0 < T ω ∨ ∀ i j, xL i < xR j)
    {AT : Ω → Set ℂ} (hAT : Measurable[mΩ, hittingSigma] AT)
    (hATK : ∀ᵐ ω ∂P, AT ω = fwdHull (fun s : ℝ => W s.toNNReal ω) (T ω : ℝ)) {n : ℕ}
    (ts : Fin n → ℝ≥0) {K : Fin n → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)}
    (hK : ∀ j, MeasurableSet (K j)) :
    ∃ g : Ω → ℝ≥0∞, Measurable[hT.measurableSpace] g ∧
      (∀ᵐ ω ∂P, g ω = restartLaw κ ρL ρR ts K
        ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω)) ∧
      ∀ A, MeasurableSet[histGerm hT.measurableSpace AT (centredField h u₀)] A →
        P (A ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
          (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
            (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j}) =
          ∫⁻ ω in A, g ω ∂P := by
  have hE := hC.1
  have hseed := not_threshold_seed_of_ae_lt hE hTζ
  obtain ⟨𝒢, N, ℓ, hTC, hnull, hNB, hWa, hVLa, hVRa, hstop⟩ := exists_lifetimeGerm hC hκ hu₀ hX hseed
  obtain ⟨hT𝒢, hgerm⟩ := hstop (fun ω => (T ω : WithTop ℝ≥0)) hT hTζ
  have hATK' : ∀ᵐ ω ∂P, AT ω =
      fwdHull (fun s : ℝ => W s.toNNReal ω) (((T ω : WithTop ℝ≥0)).untopD 0 : ℝ≥0) := by
    filter_upwards [hATK] with ω hω
    rw [hω, WithTop.untopD_coe]
  have hgermT := hgerm AT hAT hATK'
  -- the measurable version of the state at `T`
  set 𝓓 := drivingFiltration P hX with h𝓓
  have hWd : AdaptedBefore 𝓓 ζ W :=
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX)
  have hVLd : ∀ i, AdaptedBefore 𝓓 ζ (VL i) := fun i =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i)
  have hVRd : ∀ j, AdaptedBefore 𝓓 ζ (VR j) := fun j =>
    Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX j)
  set st : Ω → (Fin nL → ℝ) × (Fin nR → ℝ) := fun ω =>
    ((fun i => progVersion ζ (VL i) (T ω) ω - progVersion ζ W (T ω) ω),
      fun j => progVersion ζ (VR j) (T ω) ω - progVersion ζ W (T ω) ω) with hst
  have hstT : Measurable[hT.measurableSpace] st :=
    @measurable_start_aux nL nR Ω hT.measurableSpace _ _ _
      (measurable_eval_stop (isStronglyProgressive_progVersion hWd) hT)
      (fun i => measurable_eval_stop (isStronglyProgressive_progVersion (hVLd i)) hT)
      (fun j => measurable_eval_stop (isStronglyProgressive_progVersion (hVRd j)) hT)
  have hstm : Measurable st := hstT.mono hT.measurableSpace_le le_rfl
  set g : Ω → ℝ≥0∞ := fun ω => restartLaw κ ρL ρR ts K (st ω) with hg
  have hgT : Measurable[hT.measurableSpace] g := (measurable_restartLaw ts hK).comp hstT
  have hgm : Measurable g := (measurable_restartLaw ts hK).comp hstm
  -- the good event
  set good : Ω → Prop := fun ω => (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j) ∧
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → ℓ u ω = u ∧ N u ω = B u ω) ∧
    st ω = ((fun i => VL i (T ω) ω - W (T ω) ω), fun j => VR j (T ω) ω - W (T ω) ω) with hgood
  have hae : ∀ᵐ ω ∂P, good ω := by
    filter_upwards [hTζ, hT0, hNB, hE.2.2.2.2] with ω h1 h2 h3 hp
    refine ⟨h1, h2, h3, ?_⟩
    obtain ⟨e1, e2, e3⟩ := restart_values hp h1
    simp only [hst, e1, e2, e3]
  obtain ⟨G, hGm, hGc, hGgood⟩ : ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, good ω := by
    refine ⟨(toMeasurable P {ω | ¬ good ω})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_,
      fun ω hω => ?_⟩
    · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
    · by_contra h'; exact hω (subset_toMeasurable _ _ h')
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  refine ⟨g, hgT, ?_, fun A hA => ?_⟩
  · filter_upwards [hGae] with ω hω
    simp only [hg, (hGgood ω hω).2.2.2]
  -- the completed noise on `Ω × Ω`
  obtain ⟨B₀, hB₀m, hB₀c, hB₀0, hB₀, -⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  have hFB := hB₀.toIsPreBrownianReal.isFilteredPreBrownian hB₀m
  set 𝓦 := Filtration.natural B₀ fun t => (hB₀m t).stronglyMeasurable with h𝓦
  obtain ⟨hβ, -⟩ := IsTCExpMartingale.isFilteredBrownianReal_complNoise hTC hFB hB₀c hB₀0
  set Q : Measure (Ω × Ω) := P.prod P with hQ
  set 𝓖 := usualAugmentation (prodFiltration 𝒢 𝓦) Q with h𝓖
  have hle : ∀ t, (𝒢 t).comap Prod.fst ≤ 𝓖 t := fun t =>
    (comap_fst_le_prodFiltration 𝒢 𝓦 t).trans (Ito.le_usualAugmentation _ Q t)
  -- the lifted evolution
  have hÊ : IsIntegratedSLEEvolution κ xL xR ρL ρR Q 𝓖 (fun t p => W t p.1) (fun i t p => VL i t p.1)
      (fun j t p => VR j t p.1) (complNoise N ℓ B₀) (fun p => ζ p.1) := by
    refine ⟨Ito.isFilteredBrownianReal_usualAugmentation hβ, fun t A' hA' => hle t _ ⟨_, hWa t A' hA', rfl⟩,
      fun i t A' hA' => hle t _ ⟨_, hVLa i t A' hA', rfl⟩,
      fun j t A' hA' => hle t _ ⟨_, hVRa j t A' hA', rfl⟩, ?_⟩
    have hpath : ∀ᵐ ω ∂P, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) (fun t => B t ω) (ζ ω) ∧
        ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → ℓ u ω = u ∧ N u ω = B u ω := by
      filter_upwards [hE.2.2.2.2, hNB] with ω h1 h2 using ⟨h1, h2⟩
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hpath] with p hp
    exact isIntegratedSLEPath_congr hp.1 rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ _ => rfl) fun t ht => by
        rw [complNoise_of_eq (hp.2 t ht).1, (hp.2 t ht).2]
  -- the lifted event
  have hTQ := isStoppingTime_fst hle hT𝒢
  have hAm : MeasurableSet A := histGerm_le hT.measurableSpace_le hAT
    (measurable_centredField hC.2.1 u₀) _ hA
  have hAG : MeasurableSet[hT𝒢.measurableSpace] (A ∩ G) := by
    refine (hgermT _ hA).inter ?_
    have hGc' : MeasurableSet[hT𝒢.measurableSpace] Gᶜ :=
      measurableSet_stopping_of_null hnull hT𝒢 hGm.compl hGc
    simpa using hGc'.compl
  have hÂ := measurableSet_stopping_fst hle hT𝒢 hTQ hAG
  have hres := measure_restart_killedState (P := Q) (T := fun p => T p.1) hκ hÊ hTQ hÂ
    (fun p hp => ⟨(hGgood p.1 hp.2).1, (hGgood p.1 hp.2).2.1⟩) ts hK
  -- back to `Ω`: the left side
  have hset : Prod.fst ⁻¹' (A ∩ G) ∩ {p : Ω × Ω | ∀ j, (ts j : ℝ≥0∞) < ζ p.1 - T p.1 ∧
      (W (T p.1 + ts j) p.1 - W (T p.1) p.1, (fun i => VL i (T p.1 + ts j) p.1 - W (T p.1) p.1),
        (fun i => VR i (T p.1 + ts j) p.1 - W (T p.1) p.1),
        complNoise N ℓ B₀ (T p.1 + ts j) p - complNoise N ℓ B₀ (T p.1) p) ∈ K j} =
      ((A ∩ G) ∩ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ ω - T ω ∧
        (W (T ω + ts j) ω - W (T ω) ω, (fun i => VL i (T ω + ts j) ω - W (T ω) ω),
          (fun i => VR i (T ω + ts j) ω - W (T ω) ω), B (T ω + ts j) ω - B (T ω) ω) ∈ K j}) ×ˢ
        (univ : Set Ω) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, mem_prod, mem_univ, and_true]
    refine and_congr_right fun hpAG => forall_congr' fun j => and_congr_right fun hlt => ?_
    obtain ⟨hTζω, -, hNBω, -⟩ := hGgood p.1 hpAG.2
    have hsum : ((T p.1 + ts j : ℝ≥0) : ℝ≥0∞) < ζ p.1 := by
      rw [ENNReal.coe_add, add_comm]
      exact lt_tsub_iff_right.1 hlt
    rw [complNoise_of_eq (hNBω _ hsum).1, (hNBω _ hsum).2, complNoise_of_eq (hNBω _ hTζω).1,
      (hNBω _ hTζω).2]
  rw [hset, Measure.prod_prod, measure_univ, mul_one] at hres
  -- back to `Ω`: the right side
  have hrhs : ∫⁻ p in Prod.fst ⁻¹' (A ∩ G), restartLaw κ ρL ρR ts K
      ((fun i => VL i (T p.1) p.1 - W (T p.1) p.1), fun j => VR j (T p.1) p.1 - W (T p.1) p.1) ∂Q =
      ∫⁻ ω in A, g ω ∂P := by
    have hAGm : MeasurableSet (A ∩ G) := hAm.inter hGm
    rw [setLIntegral_congr_fun (measurable_fst hAGm) (g := fun p => g p.1) fun p hp => by
      simp only [hg, (hGgood p.1 hp.2).2.2.2]]
    rw [← lintegral_indicator (measurable_fst hAGm)]
    have e : (Prod.fst ⁻¹' (A ∩ G)).indicator (fun p : Ω × Ω => g p.1) =
        fun p => (A ∩ G).indicator g p.1 := by
      funext p
      rfl
    rw [e, ← lintegral_map (hgm.indicator hAGm) measurable_fst, hQ, Measure.map_fst_prod, measure_univ,
      one_smul, lintegral_indicator hAGm]
    refine setLIntegral_congr ?_
    filter_upwards [hGae] with ω hω
    simp only [mem_inter_iff, hω, and_true]
  rw [hrhs] at hres
  rw [← hres]
  refine measure_congr ?_
  filter_upwards [hGae] with ω hω
  simp only [mem_inter_iff, hω, and_true]

end Coupling

end WholeField

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField5Germ
import InteractingSLE.Spec.Coupling.WholeField4Bracket
import InteractingSLE.Spec.Coupling.WholeField2Hull

/-!
# The germ filtration up to the lifetime of the frozen coupling

Packet PROVE-WHOLEFIELD5, (WF7), first half (follow-up note C.2, `ig1_followup_proofs.txt` L1522–1550; additional note
§7.4, Aux. 47, `ig1_additional_proofs.txt` L3078–3121).

For the frozen coupling with an admissible seed, along an announcing sequence `σ₀ₘ ↑ ζ` (bounded, `σ₀ₘ ≤ m`), the germ
filtrations `𝒢^{(m)}_u = Γ(𝓕_{σ₀ₘ ∧ u}, K_{σ₀ₘ ∧ u})` of PROVE-WHOLEFIELD4 increase in `m`, and their supremum
`𝒢^∞_u = ⋁ₘ 𝒢^{(m)}_u` (`exists_lifetimeGerm`):

* carries the driving noise up to the lifetime: the exponential-martingale data `IsTCExpMartingale` hold for the noise
  `B_{u ∧ ζ}` (a continuous version) and the clock `u ∧ ζ`, so the completion of `WholeField5Ext` is a Brownian motion
  of `𝒢^∞ ⊗ 𝓦`;
* contains the null sets, and the driving coordinates `W, V` are adapted to it before `ζ`;
* has every driving stop `τ < ζ` as a stopping time, and contains the germ `Γ(𝓕_τ, K_τ)` in its stopping σ-algebra at
  `τ` (`histGerm_le_stopping`, from `measurableSet_histGerm_inter`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LocalSets QuantumZipper LQGMetric Coupling

universe u

/-! ### Stopping times and adaptedness through an announcing sequence -/

section Announce

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ζ : Ω → ℝ≥0∞} {𝓓 𝒢 : Filtration ℝ≥0 mΩ}
  {σ : ℕ → Ω → ℝ≥0}

/-- A time strictly before `ζ` is a finite time strictly before `ζ`. -/
theorem exists_coe_of_lt {τ : WithTop ℝ≥0} {T : ℝ≥0∞} (h : (τ : ℝ≥0∞) < T) :
    ∃ t : ℝ≥0, τ = t ∧ (t : ℝ≥0∞) < T := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h)
  refine ⟨t, ht.symm, ?_⟩
  have : ((t : WithTop ℝ≥0) : ℝ≥0∞) < T := ht ▸ h
  exact this

/-- **Adaptedness through an announcing sequence.** If `𝒢_u` contains the stopping σ-algebras `𝓓_{σₘ ∧ u}` and the null
sets, and `σ` exhausts `[0, ζ)`, a process adapted to `𝓓` before `ζ` is adapted to `𝒢` before `ζ`. -/
theorem adaptedBefore_of_announce (hσ : ∀ m, IsStoppingTime 𝓓 fun ω => (σ m ω : WithTop ℝ≥0))
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ m, t ≤ σ m ω)
    (h𝒢 : ∀ m u, ((hσ m).min_const u).measurableSpace ≤ 𝒢 u)
    (hnull : ∀ u (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 u] N)
    {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓓 ζ X) : AdaptedBefore 𝒢 ζ X := by
  intro u A hA
  have hEu : MeasurableSet[𝓓 u] {ω | (u : ℝ≥0∞) < ζ ω ∧ X u ω ∈ A} := hX u A hA
  have hEm : ∀ m, MeasurableSet[𝒢 u] ({ω | (u : ℝ≥0∞) < ζ ω ∧ X u ω ∈ A} ∩
      {ω | ((u : ℝ≥0) : WithTop ℝ≥0) ≤ min (σ m ω : WithTop ℝ≥0) u}) := by
    intro m
    have hc := isStoppingTime_const 𝓓 u
    have h1 := IsStoppingTime.measurableSet_inter_le hc ((hσ m).min_const u) _
      (by rw [IsStoppingTime.measurableSpace_const]; exact hEu)
    exact h𝒢 m u _ ((IsStoppingTime.measurableSpace_mono (hc.min ((hσ m).min_const u))
      ((hσ m).min_const u) fun ω => min_le_right _ _) _ h1)
  refine measurableSet_of_ae_eq (𝒢.le u) (hnull u) ((𝓓.le u) _ hEu) (MeasurableSet.iUnion hEm) ?_
  filter_upwards [hexh] with ω hω
  apply propext
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  constructor
  · intro hω'
    obtain ⟨m, hm⟩ := hω u hω'.1
    exact ⟨m, hω', le_min (WithTop.coe_le_coe.2 hm) le_rfl⟩
  · rintro ⟨m, hω', -⟩
    exact hω'

/-- **Stopping times through an announcing sequence.** Under the hypotheses of `adaptedBefore_of_announce`, every
stopping time `τ < ζ` of `𝓓` is a stopping time of `𝒢`. -/
theorem isStoppingTime_of_announce (hσ : ∀ m, IsStoppingTime 𝓓 fun ω => (σ m ω : WithTop ℝ≥0))
    (hexh : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ m, t ≤ σ m ω)
    (h𝒢 : ∀ m u, ((hσ m).min_const u).measurableSpace ≤ 𝒢 u)
    (hnull : ∀ u (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 u] N)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓓 τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) :
    IsStoppingTime 𝒢 τ := by
  intro u
  have hm : ∀ m, MeasurableSet[𝒢 u] {ω | τ ω ≤ min (σ m ω : WithTop ℝ≥0) u} := fun m =>
    h𝒢 m u _ (hτ.measurableSet_stopping_time_le ((hσ m).min_const u))
  refine measurableSet_of_ae_eq (𝒢.le u) (hnull u) ((𝓓.le u) _ (hτ.measurableSet_le u))
    (MeasurableSet.iUnion hm) ?_
  filter_upwards [hexh, hτζ] with ω hω hτω
  apply propext
  simp only [mem_iUnion, mem_ofPred_eq, le_min_iff]
  constructor
  · intro hle
    obtain ⟨t, ht, htζ⟩ := exists_coe_of_lt hτω
    obtain ⟨m, hm⟩ := hω t htζ
    exact ⟨m, by rw [ht]; exact WithTop.coe_le_coe.2 hm, hle⟩
  · rintro ⟨m, -, hle⟩
    exact hle

end Announce

/-! ### The frozen coupling -/

section Coupling

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

omit [IsProbabilityMeasure P] in
/-- **The germ at a driving stop `τ`, restricted to `{τ ≤ π}`, lies in the germ at `π`.** -/
theorem measurableSet_histGerm_inter_le (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ₀) {τ π : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hπ : IsStoppingTime (drivingFiltration P hX) π)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) (hπζ : ∀ᵐ ω ∂P, (π ω : ℝ≥0∞) < ζ ω)
    {Aτ Aπ : Ω → Set ℂ} (hAτ : Measurable[mΩ, hittingSigma] Aτ) (hAπ : Measurable[mΩ, hittingSigma] Aπ)
    (hAτK : ∀ᵐ ω ∂P, Aτ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hAπK : ∀ᵐ ω ∂P, Aπ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((π ω).untopD 0 : ℝ≥0))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : Measurable g) {E : Set Ω}
    (hEm : MeasurableSet[histGerm hτ.measurableSpace Aτ g] E) :
    MeasurableSet[histGerm hπ.measurableSpace Aπ g] (E ∩ {ω | τ ω ≤ π ω}) := by
  refine measurableSet_histGerm_inter (P := P) (hτ.measurableSet_stopping_time_le hπ) (fun E' hE' => ?_)
    hπ.measurableSpace_le (fun N hN h0 => measurableSet_stopping_driving_of_null hX hπ hN h0)
    (measurable_hull_stopping hE hX hσ₀ hτ hτζ hAτ hAτK) hAπ hg ?_ hEm
  · exact IsStoppingTime.measurableSpace_mono (hτ.min hπ) hπ (fun ω => min_le_right _ _) _
      (IsStoppingTime.measurableSet_inter_le hτ hπ E' hE')
  · filter_upwards [hAτK, hAπK, hπζ] with ω h1 h2 h3 hle
    rw [h1, h2]
    refine (QuantumZipper.fwdHull_mono).1 ?_
    have hπtop : π ω ≠ ⊤ := fun h' => by rw [h'] at h3; exact absurd h3 (not_lt.2 le_top)
    have hle' : τ ω ≤ π ω := hle
    rw [← coe_untopD_of_ne_top hπtop] at hle'
    have hτtop : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle'
    rw [← coe_untopD_of_ne_top hτtop] at hle'
    exact NNReal.coe_le_coe.2 (WithTop.coe_le_coe.1 hle')

omit [IsProbabilityMeasure P] in
/-- **The germ at a driving stop lies in the stopping σ-algebra of the germ filtration.** Let `𝒢_u` contain the
germs `Γ(𝓕_{σ₀ₘ ∧ u}, K_{σ₀ₘ ∧ u})` and the null sets. For a driving stop `τ < ζ` that is also a stopping time of `𝒢`,
`Γ(𝓕_τ, K_τ) ≤ 𝒢_τ`. -/
theorem histGerm_le_stopping (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ₀ : ℕ → Ω → ℝ≥0}
    (hσ₀ : IsAnnouncingSeq (drivingFiltration P hX) P ζ σ₀) {𝒢 : Filtration ℝ≥0 mΩ}
    {A : ℕ → ℝ≥0 → Ω → Set ℂ} (hAm : ∀ m u, Measurable[mΩ, hittingSigma] (A m u))
    (hAK : ∀ m u, ∀ᵐ ω ∂P, A m u ω =
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (σ₀ m ω : WithTop ℝ≥0) u).untopD 0 : ℝ≥0))
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : Measurable g)
    (h𝒢 : ∀ m u, histGerm ((hσ₀.1 m).min_const u).measurableSpace (A m u) g ≤ 𝒢 u)
    (hnull : ∀ u (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 u] N)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (drivingFiltration P hX) τ)
    (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) {Aτ : Ω → Set ℂ} (hAτ : Measurable[mΩ, hittingSigma] Aτ)
    (hAτK : ∀ᵐ ω ∂P, Aτ ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))
    (hτ𝒢 : IsStoppingTime 𝒢 τ) :
    histGerm hτ.measurableSpace Aτ g ≤ hτ𝒢.measurableSpace := by
  intro E hEm
  have hEm' : MeasurableSet[mΩ] E := histGerm_le hτ.measurableSpace_le hAτ hg _ hEm
  have hσζ : ∀ m u, ∀ᵐ ω ∂P, ((min (σ₀ m ω : WithTop ℝ≥0) u : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    fun m u => (hσ₀.2.2.1 m).mono fun ω hω => lt_of_le_of_lt (min_le_left _ _) hω
  have hint : ∀ u : ℝ≥0, MeasurableSet[𝒢 u] (E ∩ {ω | τ ω ≤ u}) := by
    intro u
    have hm : ∀ m, MeasurableSet[𝒢 u] (E ∩ {ω | τ ω ≤ min (σ₀ m ω : WithTop ℝ≥0) u}) := fun m =>
      h𝒢 m u _ (measurableSet_histGerm_inter_le hE hX hσ₀ hτ ((hσ₀.1 m).min_const u) hτζ (hσζ m u)
        hAτ (hAm m u) hAτK (hAK m u) hg hEm)
    refine measurableSet_of_ae_eq (𝒢.le u) (hnull u)
      (hEm'.inter ((drivingFiltration P hX).le u _ (hτ.measurableSet_le u))) (MeasurableSet.iUnion hm) ?_
    filter_upwards [hσ₀.2.2.2, hτζ] with ω hω hτω
    apply propext
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, le_min_iff]
    constructor
    · rintro ⟨hE', hle⟩
      obtain ⟨t, ht, htζ⟩ := exists_coe_of_lt hτω
      obtain ⟨m, hm⟩ := hω t htζ
      exact ⟨m, hE', by rw [ht]; exact WithTop.coe_le_coe.2 hm, hle⟩
    · rintro ⟨m, hE', -, hle⟩
      exact ⟨hE', hle⟩
  rw [IsStoppingTime.measurableSet]
  refine ⟨?_, hint⟩
  refine measurableSet_of_ae_eq (iSup_le 𝒢.le) (fun N hN h0 => le_iSup 𝒢 0 _ (hnull 0 N hN h0)) hEm'
    (MeasurableSet.iUnion fun n : ℕ => le_iSup 𝒢 (n : ℝ≥0) _ (hint n)) ?_
  filter_upwards [hτζ] with ω hτω
  apply propext
  simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
  constructor
  · intro hE'
    obtain ⟨t, ht, -⟩ := exists_coe_of_lt hτω
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact ⟨n, hE', by rw [ht]; exact WithTop.coe_le_coe.2 (by exact_mod_cast hn)⟩
  · rintro ⟨n, hE', -⟩
    exact hE'

/-- **The germ filtration up to the lifetime** (follow-up note C.2: "Brownian in the enlarged germ filtration up to
`T_*`"). For the frozen coupling with an admissible seed there are a filtration `𝒢` (the supremum of the germ
filtrations of PROVE-WHOLEFIELD4 along an announcing sequence of `ζ`), a noise `N` and a clock `ℓ` such that:
1. the exponential-martingale data `IsTCExpMartingale P 𝒢 N ℓ` hold (so the completion of `N` by an independent
   Brownian motion is a Brownian motion of `𝒢 ⊗ 𝓦`, `IsTCExpMartingale.isFilteredBrownianReal_complNoise`);
2. `𝒢` contains the null sets;
3. almost surely, before `ζ`: `ℓ_u = u` and `N_u = B_u`;
4. `W`, `V^{i,L}`, `V^{j,R}` are adapted to `𝒢` before `ζ`;
5. every driving stop `τ < ζ` is a stopping time of `𝒢`, and the germ `Γ(𝓕_τ, K_τ)` lies in its stopping σ-algebra. -/
theorem exists_lifetimeGerm (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    ∃ (𝒢 : Filtration ℝ≥0 mΩ) (N : ℝ≥0 → Ω → ℝ) (ℓ : ℝ≥0 → Ω → ℝ≥0),
      Sec6.Prop65.IsTCExpMartingale P 𝒢 N ℓ ∧
      (∀ u (M : Set Ω), MeasurableSet M → P M = 0 → MeasurableSet[𝒢 u] M) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ≥0∞) < ζ ω → ℓ u ω = u ∧ N u ω = B u ω) ∧
      AdaptedBefore 𝒢 ζ W ∧ (∀ i, AdaptedBefore 𝒢 ζ (VL i)) ∧ (∀ j, AdaptedBefore 𝒢 ζ (VR j)) ∧
      ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime (drivingFiltration P hX) τ),
        (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
        ∃ hτ' : IsStoppingTime 𝒢 τ, ∀ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A →
          (∀ᵐ ω ∂P, A ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
          histGerm hτ.measurableSpace A (centredField h u₀) ≤ hτ'.measurableSpace := by
  have hE := hC.1
  have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  obtain ⟨σ₀, hσ₀, hσ₀n⟩ := exists_isAnnouncingSeq_of_adapted (𝓖 := drivingFiltration P hX) (B := B)
    (κ := κ) (xL := xL) (xR := xR) (fun s hs h0 => Ito.measurableSet_usualAugmentation_of_null hs h0 0)
    (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i))
    (fun i => Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX i))
    hE.2.2.2.2 (hE.ae_tendsto_threshold hκ) hseed
  have key := fun m => martingale_stoppedNoise_germ_exp hC hκ hu₀ hX (hσ₀.1 m) (hσ₀.2.2.1 m) (hσ₀n m)
  choose A 𝒢 hAm hAK h𝒢 h𝓓𝒢 Y hYm hYc hY0 hYB hY2 hYexp using key
  have hnull : ∀ m t (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[𝒢 m t] N :=
    fun m t N hN h0 => h𝓓𝒢 m t _ (measurableSet_stopping_driving_of_null hX ((hσ₀.1 m).min_const t) hN h0)
  have hAK' : ∀ m u, ∀ᵐ ω ∂P, A m u ω =
      fwdHull (fun s : ℝ => W s.toNNReal ω) ((min (σ₀ m ω : WithTop ℝ≥0) u).untopD 0 : ℝ≥0) := by
    intro m u
    filter_upwards [hAK m u] with ω hω
    rw [hω, ← WithTop.coe_min, WithTop.untopD_coe]
  have hσζ : ∀ m u, ∀ᵐ ω ∂P, ((min (σ₀ m ω : WithTop ℝ≥0) u : WithTop ℝ≥0) : ℝ≥0∞) < ζ ω :=
    fun m u => (hσ₀.2.2.1 m).mono fun ω hω => lt_of_le_of_lt (min_le_left _ _) hω
  have hh0 : Measurable (centredField h u₀) := measurable_centredField hC.2.1 u₀
  -- the germ filtrations increase in `m`
  have hmono : ∀ u, Monotone fun m => 𝒢 m u := by
    intro u
    refine monotone_nat_of_le_succ fun m => ?_
    rw [h𝒢 m u, h𝒢 (m + 1) u]
    exact histGerm_hull_mono hE hX hσ₀ ((hσ₀.1 m).min_const u) ((hσ₀.1 (m + 1)).min_const u)
      (fun ω => min_le_min (WithTop.coe_le_coe.2 (hσ₀.2.1 ω (Nat.le_succ m))) le_rfl) (hσζ m u)
      (hσζ (m + 1) u) (hAm m u) (hAm (m + 1) u) (hAK' m u) (hAK' (m + 1) u) hh0
  -- the continuous version of the noise
  obtain ⟨Bv, hBvm, hBvc, hBv0, -, hBvae⟩ := QuantumZipper.RS.exists_good_version0 hE.1.1
  -- the clock `u ∧ σ₀ₘ`
  have hSm : ∀ m u, Measurable[𝒢 m u] fun ω => min u (σ₀ m ω) := by
    intro m u
    have h1 := (WithTop.measurable_untopD (0 : ℝ≥0)).comp ((hσ₀.1 m).min_const u).measurable
    have e : (fun ω => min u (σ₀ m ω)) = (fun x : WithTop ℝ≥0 => x.untopD 0) ∘
        fun ω => min (σ₀ m ω : WithTop ℝ≥0) u := by
      funext ω
      simp only [Function.comp_apply, ← WithTop.coe_min, WithTop.untopD_coe, min_comm]
    rw [e]
    exact h1.mono (h𝓓𝒢 m u) le_rfl
  have hBvj : Measurable (Function.uncurry fun s ω => Bv s ω) :=
    measurable_uncurry_of_continuous_of_measurable hBvc hBvm
  -- the exponential martingales of the continuous version
  have hexp : ∀ m (a : ℝ), Martingale (fun t ω => Real.exp (a * Bv (min t (σ₀ m ω)) ω -
      a ^ 2 * ((min t (σ₀ m ω) : ℝ≥0) : ℝ) / 2)) (𝒢 m) P := by
    intro m a
    refine martingale_of_ae_eq_of_null (hYexp m a) (fun t => ?_) (fun t => ?_) (hnull m)
    · have hc : Measurable fun ω => min t (σ₀ m ω) := (hSm m t).mono ((𝒢 m).le t) le_rfl
      exact Real.measurable_exp.comp (((hBvj.comp (hc.prodMk measurable_id)).const_mul a).sub
        (((measurable_coe_nnreal_real.comp hc).const_mul _).div_const _))
    · filter_upwards [hYB m, hBvae] with ω h1 h2
      simp only [h1 t, h2]
  have hTC := isTCExpMartingale_annClock hmono (fun ω => hσ₀.2.1 ω) hSm hBvc hBv0 hexp
  have hnullI : ∀ u (N : Set Ω), MeasurableSet N → P N = 0 → MeasurableSet[iSupFiltration 𝒢 u] N :=
    fun u N hN h0 => le_iSupFiltration 𝒢 0 u _ (hnull 0 u N hN h0)
  have hleI : ∀ m u, ((hσ₀.1 m).min_const u).measurableSpace ≤ iSupFiltration 𝒢 u :=
    fun m u => (h𝓓𝒢 m u).trans (le_iSupFiltration 𝒢 m u)
  refine ⟨iSupFiltration 𝒢, fun u ω => Bv (annClock σ₀ u ω) ω, annClock σ₀, hTC, hnullI, ?_,
    adaptedBefore_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_W hX)),
    fun i => adaptedBefore_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VL hX i)),
    fun j => adaptedBefore_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI
      (Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (adaptedBefore_killedDriving_VR hX j)), ?_⟩
  · filter_upwards [hσ₀.2.2.2, hBvae] with ω hω hBv u hu
    obtain ⟨m, hm⟩ := hω u hu
    have hℓ : annClock σ₀ u ω = u := annClock_eq_of_le hm
    exact ⟨hℓ, by simp only [hℓ, hBv u]⟩
  · intro τ hτ hτζ
    have hτ' := isStoppingTime_of_announce hσ₀.1 hσ₀.2.2.2 hleI hnullI hτ hτζ
    refine ⟨hτ', fun Aτ hAτ hAτK => ?_⟩
    exact histGerm_le_stopping hE hX hσ₀ hAm hAK' hh0
      (fun m u => by rw [← h𝒢 m u]; exact le_iSupFiltration 𝒢 m u) hnullI hτ hτζ hAτ hAτK hτ'

end Coupling

end WholeField

end InteractingSLE

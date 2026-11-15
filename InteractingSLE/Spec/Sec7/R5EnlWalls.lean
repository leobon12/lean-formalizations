/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5EnlPocket
import InteractingSLE.Spec.Sec7.PocketStopWallsFinStop
import InteractingSLE.Spec.Sec7.PocketWordPerQSigma
import InteractingSLE.Spec.Sec7.R5SameRef

/-!
# The walls law at a marked stop with its whole stopped information as marks (`T` and `T ∨ s`)

Packet PROVE-R5-ENLARGED (continued). The landed producer `PocketStopWallsFin.pocketStopWallsLaw_regHull` gives the
walls–hull law at a marked stop `T` with the relative-prefix marks `locPrefixSigma 𝓦 A γ q`. Lemma R.5 (Aux. 35)
needs the law to retain the **stopped counterflow history** at `T` and at `T ∨ s` (`R5EnlStop.markedStopSigma`):
those marks contain the prefix marks (`le_markedStopSigma`), so the prefix σ-algebra built on them collapses to them
and is a mark σ-algebra of the stop.

* `isMarkedStop_mono_marks`, `isMarkedStop_bot_of`;
* `locPrefixSigma_markedStopSigma_le`, `isMarkedStop_locPrefixSigma_markedStopSigma`;
* `isMarkedStop_max_const`, `isMarkedStop_locPrefixSigma_max` (the stop `T ∨ s` with the prefix marks and `𝓕_s`);
* **`pocketStopWallsLaw_markedStopSigma`** — the walls law at `T` with marks `markedStopSigma 𝓕 X T`;
* **`pocketStopWallsLaw_markedStopSigma_max`** — the walls law at `T ∨ s` with marks `markedStopSigma 𝓕 X (T ∨ s)`;
* `wallsSigma_le_markedStopSigma`, **`pocketStopUnionLaw_cfPocket_markedStopSigma`** — the change pocket's union law
  with the stopped information as marks;
* **`measurable_refSet_refInfo`** — the reference set is measurable for `σ(walls) ∨ 𝓕_s` (`hBs`).

Conditional helpers with distinct names; nothing here uses Theorem 1.2/1.3 or any `*_of_param` (R43, R48).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Enl

open PocketStopWallsFin PocketCoupling

section Marks

variable {Ω 𝒳 : Type*} [MeasurableSpace 𝒳] {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {X : Ω → 𝒳}

/-- Fewer marks keep a marked stop. -/
theorem isMarkedStop_mono_marks {ℳ ℳ' : MeasurableSpace Ω} {T : Ω → ℝ≥0∞} (h : IsMarkedStop ℳ 𝓕 X T)
    (hle : ℳ' ≤ ℳ) : IsMarkedStop ℳ' 𝓕 X T :=
  fun σ hσ M hM => h σ hσ M (hle M hM)

/-- A marked stop is a marked stop without marks. -/
theorem isMarkedStop_bot_of {ℳ : MeasurableSpace Ω} {T : Ω → ℝ≥0∞} (h : IsMarkedStop ℳ 𝓕 X T) :
    IsMarkedStop ⊥ 𝓕 X T :=
  isMarkedStop_mono_marks h bot_le

/-- The prefix σ-algebra on the stopped information is the stopped information, once the prefix marks are marks of
the stop. -/
theorem locPrefixSigma_markedStopSigma_le {𝓦 : MeasurableSpace Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0}
    {T : Ω → ℝ≥0∞} (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) 𝓕 X T)
    (hS0 : locPrefixSigma 𝓦 A γ q ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t) :
    locPrefixSigma (markedStopSigma 𝓕 X T) A γ q ≤ markedStopSigma 𝓕 X T :=
  sup_le le_rfl ((le_sup_right.trans le_rfl : MeasurableSpace.generateFrom _ ≤ locPrefixSigma 𝓦 A γ q).trans
    (le_markedStopSigma hG hS0))

/-- **The prefix marks on the stopped information form a mark σ-algebra of the stop.** -/
theorem isMarkedStop_locPrefixSigma_markedStopSigma {𝓦 : MeasurableSpace Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {q : ℝ≥0} {T : Ω → ℝ≥0∞} (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) 𝓕 X T)
    (hS0 : locPrefixSigma 𝓦 A γ q ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t) :
    IsMarkedStop (locPrefixSigma (markedStopSigma 𝓕 X T) A γ q) 𝓕 X T ∧
      locPrefixSigma (markedStopSigma 𝓕 X T) A γ q ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t :=
  ⟨isMarkedStop_mono_marks (isMarkedStop_markedStopSigma (isMarkedStop_bot_of hG))
    (locPrefixSigma_markedStopSigma_le hG hS0),
    (locPrefixSigma_markedStopSigma_le hG hS0).trans (markedStopSigma_le T)⟩

/-- The stop `T ∨ s` (a constant `s`) is a marked stop for the marks of `T` joined with `𝓕_s`. -/
theorem isMarkedStop_max_const {ℳ : MeasurableSpace Ω} {T : Ω → ℝ≥0∞} (hG : IsMarkedStop ℳ 𝓕 X T) (s : ℝ≥0) :
    IsMarkedStop (ℳ ⊔ 𝓕 s) 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)) := by
  have h := PocketStopSide.isMarkedStop_max_ordinary hG (isStoppingTime_const 𝓕 s)
  rwa [IsStoppingTime.measurableSpace_const] at h

/-- The prefix marks at the stop `T ∨ s`: the prefix σ-algebra with `𝓕_s` added, and its `hS0`. -/
theorem isMarkedStop_locPrefixSigma_max {𝓦 : MeasurableSpace Ω} {A : Set Ω} {γ : Ω → ℝ → ℂ} {q : ℝ≥0}
    {T : Ω → ℝ≥0∞} (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) 𝓕 X T)
    (hS0 : locPrefixSigma 𝓦 A γ q ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t) (s : ℝ≥0) :
    IsMarkedStop (locPrefixSigma (𝓦 ⊔ 𝓕 s) A γ q) 𝓕 X (fun ω => max (T ω) (s : ℝ≥0∞)) ∧
      locPrefixSigma (𝓦 ⊔ 𝓕 s) A γ q ≤ MeasurableSpace.comap X inferInstance ⊔ ⨆ t, 𝓕 t := by
  rw [PocketStopSide.locPrefixSigma_sup_info]
  exact ⟨isMarkedStop_max_const hG s, sup_le hS0 ((le_iSup (fun t => 𝓕 t) s).trans le_sup_right)⟩

end Marks

/-! ### The walls laws at `T` and `T ∨ s` with the stopped information -/

section Walls

open WholeField PocketStopField PocketStopWalls Lemma71C

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω 𝒳 : Type*} [MeasurableSpace 𝒳]

/-- **The walls–hull law at a marked stop `T` with the stopped information of `T` as marks**
(`pocketStopWallsLaw_regHull` with `𝓦 := markedStopSigma`). -/
theorem pocketStopWallsLaw_markedStopSigma {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    {A : Set Ω} {γ : Ω → ℝ → ℂ} {Γ F : Ω → Set ℂ} {q : ℝ≥0}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => LocalSets.markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T : Ω → ℝ≥0∞}
    (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → T ω < ⊤ ∧ F ω = regHull W ζ (T ω).toNNReal ω)
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) (drivingFiltration P hX) X T)
    (hS0 : locPrefixSigma 𝓦 A γ q ≤
      MeasurableSpace.comap X inferInstance ⊔ ⨆ t, drivingFiltration P hX t) :
    PocketStopWallsLaw (markedStopSigma (drivingFiltration P hX) X T) P A γ Γ F (centredField h u₀) q := by
  obtain ⟨hG', hS0'⟩ := isMarkedStop_locPrefixSigma_markedStopSigma hG hS0
  exact pocketStopWallsLaw_regHull hC hκ hu₀ hX hζ hXm hΓ hW hT hG' fun M hM => hS0' M hM

/-- **The walls–hull law at `T ∨ s` with the stopped information of `T ∨ s` as marks** (the enlarged stop of
Lemma R.5; `hT` for the hull at `T ∨ s`). -/
theorem pocketStopWallsLaw_markedStopSigma_max {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} {A : Set Ω} {γ : Ω → ℝ → ℂ} {Γ F : Ω → Set ℂ} {q : ℝ≥0}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {X : Ω → 𝒳} (hXm : Measurable X) (hΓ : Measurable[mΩ, hittingSigma] Γ)
    (hW : ∀ (U : TopologicalSpace.Opens ℂ) (G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens),
      (U : Set ℂ) ⊆ H → Measurable G →
      GFF.IsMarkovDecomposition U upperHalfPlaneOpens (centredField h u₀) (fun ω => G (centredField h u₀ ω)) P →
      ∀ B : Set 𝒳, MeasurableSet B → ∃ B' : Set (DistOn upperHalfPlaneOpens), MeasurableSet B' ∧
        {ω | Disjoint (Γ ω) U} ∩ X ⁻¹' B =ᵐ[P] (fun ω => LocalSets.markovCompl G (centredField h u₀ ω)) ⁻¹' B')
    {T : Ω → ℝ≥0∞} (s : ℝ≥0)
    (hT : ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      T ω < ⊤ ∧ F ω = regHull W ζ (max (T ω) (s : ℝ≥0∞)).toNNReal ω)
    (hG : IsMarkedStop (locPrefixSigma 𝓦 A γ q) (drivingFiltration P hX) X T)
    (hS0 : locPrefixSigma 𝓦 A γ q ≤
      MeasurableSpace.comap X inferInstance ⊔ ⨆ t, drivingFiltration P hX t) :
    PocketStopWallsLaw (markedStopSigma (drivingFiltration P hX) X (fun ω => max (T ω) (s : ℝ≥0∞))) P A γ Γ F
      (centredField h u₀) q := by
  obtain ⟨hGm, hS0m⟩ := isMarkedStop_locPrefixSigma_max hG hS0 s
  exact pocketStopWallsLaw_markedStopSigma hC hκ hu₀ hX hζ hXm hΓ hW
    (fun ω hω hq => ⟨max_lt (hT ω hω hq).1 ENNReal.coe_lt_top, (hT ω hω hq).2⟩) hGm hS0m

end Walls

/-! ### The pocket union laws with the stopped information (change pocket) -/

section Pocket

open WholeField PocketStopField PocketStopWalls PocketWordPerQ PocketCoord PocketStop PocketJordan
open InteractingSLE.WangWu (negInv)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The walls' σ-algebra (walls and null sets) lies in the stopped information of every marked stop of the walls'
information and the driving filtration. -/
theorem wallsSigma_le_markedStopSigma {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ)
    {R L : Ω → ℝ≥0 → ℂ} {T : Ω → ℝ≥0∞}
    (hT : IsMarkedStop ⊥ (drivingFiltration P hX) (fullHist ![R, L]) T) :
    wallsSigma P R L ≤ markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T := by
  have h0 := le_markedStopSigma_max hT 0
  have e : (fun ω => max (T ω) ((0 : ℝ≥0) : ℝ≥0∞)) = T := funext fun ω => max_eq_left (by simp)
  rw [e] at h0
  exact (wallsSigma_le_drivingFiltration hX R L).trans (sup_le (comap_le_markedStopSigma hT) h0)

/-- **The pocket union law of the change pocket with the stopped information of a marked stop as marks**, from the
walls law with the same marks (`pocketStopWallsLaw_markedStopSigma(_max)`; `PocketStopField.pocketStopUnionLaw_cfPocket`
with `𝓦 := markedStopSigma`). -/
theorem pocketStopUnionLaw_cfPocket_markedStopSigma {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hX : IsMeasurableKilledDriving W VL VR ζ)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    (hRm : ∀ t, Measurable fun ω => R ω t) (hLm : ∀ t, Measurable fun ω => L ω t)
    {T : Ω → ℝ≥0∞} (hT : IsMarkedStop ⊥ (drivingFiltration P hX) (fullHist ![R, L]) T)
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0}
    (hpre : locPrefixSigma (markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T) A γ q ≤ mΩ)
    {F : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (hW : PocketStopWallsLaw (markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T) P A γ
      (fun ω => negInv '' (range (R ω) ∪ range (L ω))) F h₀ q) :
    PocketStopUnionLaw (markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T) P A γ
      (fun ω => cfPocket (R ω) (L ω) r) F h₀ q := by
  have hle := wallsSigma_le_markedStopSigma hX hT
  have h𝓦 : markedStopSigma (drivingFiltration P hX) (fullHist ![R, L]) T ≤ mΩ := by
    refine (markedStopSigma_le T).trans (sup_le ?_ (iSup_le fun t => (drivingFiltration P hX).le t))
    refine (measurable_fullHist fun i t => ?_).comap_le
    fin_cases i
    · exact hRm t
    · exact hLm t
  exact pocketStopUnionLaw_cfPocket h𝓦 (fun t => (measurable_right_wallsSigma hRc hLc t).mono hle le_rfl)
    (fun t => (measurable_left_wallsSigma hRc hLc t).mono hle le_rfl) (hle _ hGm) hG (hle _ hA) hAG hpre hW

end Pocket

/-! ### The reference set is measurable for the reference record -/

section RefSet

open WholeField PocketStopField PocketStopWalls PocketWordPerQ PocketCoord PocketStop PocketJordan PocketTraversal
  PocketAdapt Lemma71C

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **R.5's reference set `(ℍ ∖ C) ∪ K̃_s` is hitting-measurable for the reference record `σ(walls) ∨ 𝓕_s`**
(`hBs` of `hasOldChartIncrementLawOn_of_pocketLaws_stop`): the pocket exterior is walls-measurable
(`R5Same.measurableSet_disjoint_pocketExt`, `Lemma725RefMarks.measurableSet_subset_cfPocket`) and the regularized
hull at
the deterministic time `s` is `𝓕_s`-measurable (`PocketStopWallsFin.measurableSet_disjoint_regHull`). -/
theorem measurable_refSet_refInfo {𝓕₀ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕₀ W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {R L : Ω → ℝ≥0 → ℂ} (hRc : ∀ ω, Continuous (R ω)) (hLc : ∀ ω, Continuous (L ω))
    {r : ℝ≥0} {G A : Set Ω} (hGm : MeasurableSet[wallsSigma P R L] G)
    (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) (hA : MeasurableSet[wallsSigma P R L] A) (hAG : A ⊆ G)
    {γ : Ω → ℝ → ℂ} (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (s : ℝ≥0) :
    Measurable[MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX s, hittingSigma]
      (liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W ζ s) 0) := by
  have hw : wallsSigma P R L ≤
      MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX s :=
    (wallsSigma_le_drivingFiltration hX R L).trans
    (sup_le_sup_left ((drivingFiltration P hX).mono (show (0 : ℝ≥0) ≤ s from zero_le)) _)
  refine @measurable_generateFrom Ω (Set ℂ)
    (MeasurableSpace.comap (fullHist ![R, L]) inferInstance ⊔ drivingFiltration P hX s) _ _ ?_
  rintro _ ⟨U, hUo, hUH, rfl⟩
  have hKH : ∀ ω, regHull W ζ s ω ⊆ H := fun _ _ hz => hz.1
  have e : liveExt A γ (fun ω => cfPocket (R ω) (L ω) r) (regHull W ζ s) 0 ⁻¹' {S : Set ℂ | (S ∩ U).Nonempty} =
      {ω | Disjoint (R5Same.pocketExt A γ (fun ω => cfPocket (R ω) (L ω) r) ω) U}ᶜ ∪
        {ω | Disjoint (regHull W ζ s ω) U}ᶜ := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, mem_union, mem_compl_iff, ← R5Same.pocketExt_union hKH ω,
      union_inter_distrib_right, union_nonempty, Set.not_disjoint_iff_nonempty_inter]
  rw [e]
  refine (hw _ (R5Same.measurableSet_disjoint_pocketExt hγ (fun V hVo hVH =>
    Lemma725RefMarks.measurableSet_subset_cfPocket (measurable_right_wallsSigma hRc hLc)
      (measurable_left_wallsSigma hRc hLc) hGm hG hA hAG hVo hVH) hUo hUH)).compl.union ?_
  exact (le_sup_right (a := MeasurableSpace.comap (fullHist ![R, L]) inferInstance) _
    (measurableSet_disjoint_regHull hC hκ hX hζ s U hUo hUH)).compl

end RefSet

end InteractingSLE.Sec7.R5Enl

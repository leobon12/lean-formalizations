import InteractingSLE.Spec.Coupling.CompactTransfer
import InteractingSLE.Spec.Ito.FiltrationBasic
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Theorem 1.1 without a standard Borel sample space: transport and rational-time coordinates

Packet PROVE-T11-LOC, item 2 (`planning/handoffs/PROVE-T11-ASM.md` §4 item 2). The compactness step needs every event
of the stopped σ-algebras of the family to be, up to a null set, a function of countably many real coordinates
`G : Ω₀ → Y` (`Y` standard Borel). The frozen Theorem 2.2 gives an evolution on an arbitrary `Ω : Type`. Here:

* `IsIntegratedSLEEvolution.comap`: the evolution pulls back along every measurable map `π` with `P'.map π = P`
  (in particular to `ULift Ω`, any universe);
* `IsAeGen P G m`: every event of `m` is almost surely `G⁻¹ C` for a measurable `C`; preserved by the usual augmentation
  and by the stopped σ-algebras of real stopping times (`IsAeGen.usualAugmentation`, `IsAeGen.stopped`);
* `coordVal`, `coordMap`, `coordFiltration`: the rational-time coordinates `(1_{q<ζ}, 1_{q<ζ}(W, V^L, V^R)_q, B_q)` and
  the filtration they generate; `isIntegratedSLEEvolution_coordFiltration`: the evolution is an integrated evolution for
  the usual augmentation of the coordinate filtration (right limits of rational coordinates, continuity before `ζ`;
  the Brownian increments stay independent because the coordinate filtration is smaller than the evolution's).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

open Ito

/-! ### Pull-back along a measure-preserving map -/

section Comap

variable {Ω₀ Ω' : Type*} {mΩ₀ : MeasurableSpace Ω₀} [mΩ' : MeasurableSpace Ω']

/-- The filtration `𝓕₀ ∘ π`. -/
def filtrationComap (𝓕₀ : Filtration ℝ≥0 mΩ₀) {π : Ω' → Ω₀} (hπ : Measurable π) : Filtration ℝ≥0 mΩ' where
  seq t := (𝓕₀ t).comap π
  mono' _ _ hst := MeasurableSpace.comap_mono (𝓕₀.mono hst)
  le' t := (MeasurableSpace.comap_mono (𝓕₀.le t)).trans hπ.comap_le

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

/-- **The evolution pulls back** along every measurable map carrying the law to the law. -/
theorem IsIntegratedSLEEvolution.comap {P₀ : Measure Ω₀} {P' : Measure Ω'} {π : Ω' → Ω₀}
    (hπ : Measurable π) (hμ : P'.map π = P₀) {𝓕₀ : Filtration ℝ≥0 mΩ₀}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P' (filtrationComap 𝓕₀ hπ) (fun t p => W t (π p))
      (fun i t p => VL i t (π p)) (fun i t p => VR i t (π p)) (fun t p => B t (π p))
      (fun p => ζ (π p)) := by
  obtain ⟨⟨hBB, hBa, hBi⟩, hWa, hVLa, hVRa, hpath⟩ := hE
  have hlaw : HasLaw π P₀ P' := ⟨hπ.aemeasurable, hμ⟩
  have hBm : ∀ t, Measurable (B t) := fun t => (hBa t).mono (𝓕₀.le t) le_rfl
  refine ⟨⟨⟨⟨fun I => (hBB.hasLaw I).comp hlaw⟩, ?_⟩, fun t => ?_, fun s t hst => ?_⟩,
    fun t A hA => ?_, fun i t A hA => ?_, fun i t A hA => ?_, ?_⟩
  · rw [← hμ] at hBB
    exact ae_of_ae_map hπ.aemeasurable hBB.cont
  · exact @Measurable.comp _ _ _ ((𝓕₀ t).comap π) (𝓕₀ t) _ _ _ (hBa t) (comap_measurable π)
  · rw [Indep_iff]
    intro t1 t2 ht1 ht2
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht1
    obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 ht2
    have hS' : MeasurableSet ((fun ω => B t ω - B s ω) ⁻¹' S) := ((hBm t).sub (hBm s)) hS
    have hT' : MeasurableSet T := 𝓕₀.le s _ hT
    have hind := (Indep_iff _ _ _).1 (hBi s t hst) _ T
      (MeasurableSpace.measurableSet_comap.2 ⟨S, hS, rfl⟩) hT
    have e : (fun p : Ω' => B t (π p) - B s (π p)) ⁻¹' S = π ⁻¹' ((fun ω => B t ω - B s ω) ⁻¹' S) := rfl
    rw [e, ← preimage_inter, ← Measure.map_apply hπ (hS'.inter hT'), ← Measure.map_apply hπ hS',
      ← Measure.map_apply hπ hT', hμ]
    exact hind
  · exact MeasurableSpace.measurableSet_comap.2 ⟨_, hWa t A hA, rfl⟩
  · exact MeasurableSpace.measurableSet_comap.2 ⟨_, hVLa i t A hA, rfl⟩
  · exact MeasurableSpace.measurableSet_comap.2 ⟨_, hVRa i t A hA, rfl⟩
  · rw [← hμ] at hpath
    exact ae_of_ae_map hπ.aemeasurable hpath

end Comap

/-! ### σ-algebras generated, up to null sets, by countably many coordinates -/

section AeGen

variable {Ω₀ Y : Type*} [mY : MeasurableSpace Y]

/-- Every event of `m` is almost surely `G⁻¹ C` for a measurable `C ⊆ Y`. -/
def IsAeGen {mΩ₀ : MeasurableSpace Ω₀} (P₀ : Measure Ω₀) (G : Ω₀ → Y) (m : MeasurableSpace Ω₀) : Prop :=
  ∀ A : Set Ω₀, MeasurableSet[m] A → ∃ C : Set Y, MeasurableSet C ∧ A =ᵐ[P₀] G ⁻¹' C

variable {mΩ₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} {G : Ω₀ → Y}

theorem isAeGen_comap : IsAeGen P₀ G (MeasurableSpace.comap G mY) := fun A hA => by
  obtain ⟨C, hC, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  exact ⟨C, hC, EventuallyEq.rfl⟩

theorem IsAeGen.mono {m m' : MeasurableSpace Ω₀} (h : IsAeGen P₀ G m') (hle : m ≤ m') : IsAeGen P₀ G m :=
  fun A hA => h A (hle A hA)

/-- **The usual augmentation of an a.e.-generated filtration is a.e. generated.** -/
theorem IsAeGen.usualAugmentation {𝓒 : Filtration ℝ≥0 mΩ₀} (h : ∀ t, IsAeGen P₀ G (𝓒 t)) (t : ℝ≥0) :
    IsAeGen P₀ G (InteractingSLE.usualAugmentation 𝓒 P₀ t) := fun A hA => by
  obtain ⟨A', hA', hAA'⟩ := exists_ae_eq_of_measurableSet_usualAugmentation (lt_add_one t) hA
  obtain ⟨C, hC, hA'C⟩ := h (t + 1) A' hA'
  exact ⟨C, hC, hAA'.trans hA'C⟩

/-- **Stopped σ-algebras of real stopping times of an a.e.-generated filtration are a.e. generated.** -/
theorem IsAeGen.stopped {𝓖 : Filtration ℝ≥0 mΩ₀} (h : ∀ t, IsAeGen P₀ G (𝓖 t)) {s : Ω₀ → ℝ≥0}
    (hs : IsStoppingTime 𝓖 fun ω => (s ω : WithTop ℝ≥0)) : IsAeGen P₀ G hs.measurableSpace := by
  intro A hA
  rw [IsStoppingTime.measurableSet] at hA
  have hn : ∀ n : ℕ, ∃ C : Set Y, MeasurableSet C ∧
      A ∩ {ω | (s ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[P₀] G ⁻¹' C := fun n =>
    h n _ (hA.2 n)
  choose C hC hAC using hn
  refine ⟨⋃ n, C n, MeasurableSet.iUnion hC, ?_⟩
  have hAU : A = ⋃ n : ℕ, A ∩ {ω | (s ω : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext ω
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, WithTop.coe_le_coe]
    constructor
    · intro hω
      obtain ⟨n, hn⟩ := exists_nat_ge (s ω)
      exact ⟨n, hω, hn⟩
    · rintro ⟨n, hω, -⟩; exact hω
  rw [hAU, preimage_iUnion]
  exact EventuallyEqSet.countable_iUnion hAC

end AeGen

/-! ### Killed values and right limits -/

section Killed

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀}

/-- The value at `t` of a process killed at `ζ` (zero from the lifetime on). -/
def killedVal (ζ : Ω₀ → ℝ≥0∞) (X : ℝ≥0 → Ω₀ → ℝ) (t : ℝ≥0) (ω : Ω₀) : ℝ :=
  if (t : ℝ≥0∞) < ζ ω then X t ω else 0

theorem measurable_killedVal {m : MeasurableSpace Ω₀} {ζ : Ω₀ → ℝ≥0∞} {X : ℝ≥0 → Ω₀ → ℝ} {t : ℝ≥0}
    (hX : ∀ A : Set ℝ, MeasurableSet A → MeasurableSet[m] {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A}) :
    Measurable[m] (killedVal ζ X t) := by
  intro A hA
  have hζ : MeasurableSet[m] {ω | (t : ℝ≥0∞) < ζ ω} := by
    simpa using hX univ MeasurableSet.univ
  by_cases h0 : (0 : ℝ) ∈ A
  · have e : killedVal ζ X t ⁻¹' A = {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∪ {ω | (t : ℝ≥0∞) < ζ ω}ᶜ := by
      ext ω
      by_cases hω : (t : ℝ≥0∞) < ζ ω <;> simp [killedVal, hω, h0]
    rw [e]
    exact (hX A hA).union hζ.compl
  · have e : killedVal ζ X t ⁻¹' A = {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} := by
      ext ω
      by_cases hω : (t : ℝ≥0∞) < ζ ω <;> simp [killedVal, hω, h0]
    rw [e]
    exact hX A hA

/-- The killed value is a right limit: along times `r n ↓ t`, `killedVal (r n) → killedVal t` whenever the path is
continuous before `ζ`. -/
theorem tendsto_killedVal {ζ : Ω₀ → ℝ≥0∞} {X : ℝ≥0 → Ω₀ → ℝ} {ω : Ω₀}
    (hX : ContinuousOn (fun t => X t ω) {t | (t : ℝ≥0∞) < ζ ω}) {t : ℝ≥0} {r : ℕ → ℝ≥0}
    (hr : Tendsto r atTop (𝓝 t)) (hrt : ∀ n, t ≤ r n) :
    Tendsto (fun n => killedVal ζ X (r n) ω) atTop (𝓝 (killedVal ζ X t ω)) := by
  by_cases ht : (t : ℝ≥0∞) < ζ ω
  · have hO : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} :=
      isOpen_lt ENNReal.continuous_coe continuous_const
    have hev : ∀ᶠ n in atTop, (r n : ℝ≥0∞) < ζ ω := hr (hO.mem_nhds ht)
    have hc : Tendsto (fun n => X (r n) ω) atTop (𝓝 (X t ω)) :=
      ((hX.continuousAt (hO.mem_nhds ht)).tendsto).comp hr
    simp only [killedVal, ht, ↓reduceIte]
    refine hc.congr' ?_
    filter_upwards [hev] with n hn
    simp [hn]
  · have hn : ∀ n, ¬ ((r n : ℝ≥0∞) < ζ ω) := fun n h =>
      ht (lt_of_le_of_lt (by exact_mod_cast hrt n) h)
    simp only [killedVal, ht, hn, ↓reduceIte]
    exact tendsto_const_nhds

/-- An almost sure limit of `m`-measurable real functions is almost surely equal to an `m`-measurable function. -/
theorem exists_measurable_ae_eq_of_tendsto {P₀ : Measure Ω₀} {m : MeasurableSpace Ω₀}
    {f : ℕ → Ω₀ → ℝ} (hf : ∀ n, Measurable[m] (f n)) {g : Ω₀ → ℝ}
    (hlim : ∀ᵐ ω ∂P₀, Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    ∃ g' : Ω₀ → ℝ, Measurable[m] g' ∧ g =ᵐ[P₀] g' :=
  ⟨fun ω => limUnder atTop fun n => f n ω,
    (@StronglyMeasurable.limUnder ℕ Ω₀ ℝ m _ _ atTop _ f _ _ fun n =>
      (hf n).stronglyMeasurable).measurable,
    hlim.mono fun _ hω => hω.limUnder_eq.symm⟩

/-- An event measurable and almost surely equal to an event of `𝓒 u` for every `u > t` is an event of the usual
augmentation at `t`. -/
theorem measurableSet_usualAugmentation_of_forall_lt {𝓒 : Filtration ℝ≥0 mΩ₀} {P₀ : Measure Ω₀}
    {t : ℝ≥0} {A : Set Ω₀} (hA : MeasurableSet A)
    (h : ∀ u, t < u → ∃ C, MeasurableSet[𝓒 u] C ∧ A =ᵐ[P₀] C) :
    MeasurableSet[usualAugmentation 𝓒 P₀ t] A := by
  rw [usualAugmentation_apply]
  simp only [MeasurableSpace.measurableSet_iInf]
  intro u hu
  obtain ⟨C, hC, hAC⟩ := h u hu
  exact measurableSet_nullAugmented_of_ae_eq hA hC hAC

/-- Rational times decreasing to `t` below `u > t`. -/
theorem exists_rat_seq_tendsto {t u : ℝ≥0} (hu : t < u) :
    ∃ q : ℕ → ℚ, (∀ n, t < ((q n : ℝ)).toNNReal) ∧ (∀ n, ((q n : ℝ)).toNNReal ≤ u) ∧
      Tendsto (fun n => ((q n : ℝ)).toNNReal) atTop (𝓝 t) := by
  have hex : ∀ n : ℕ, ∃ q : ℚ, (t : ℝ) < q ∧ (q : ℝ) < min (u : ℝ) ((t : ℝ) + 1 / ((n : ℝ) + 1)) := fun n =>
    exists_rat_btwn (lt_min (by exact_mod_cast hu) (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith))
  choose q hq1 hq2 using hex
  have hq0 : ∀ n, (0 : ℝ) ≤ q n := fun n => le_trans t.coe_nonneg (hq1 n).le
  refine ⟨q, fun n => ?_, fun n => ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hq0 n)]; exact hq1 n
  · rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hq0 n)]; exact (hq2 n).le.trans (min_le_left _ _)
  · rw [← NNReal.tendsto_coe]
    have hlim : Tendsto (fun n : ℕ => (t : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 (t : ℝ)) := by
      simpa using (tendsto_const_nhds (x := (t : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => ?_) (fun n => ?_)
    · simp only [Real.coe_toNNReal _ (hq0 n)]; exact (hq1 n).le
    · simp only [Real.coe_toNNReal _ (hq0 n)]; exact (hq2 n).le.trans (min_le_right _ _)

/-- **Adaptedness before `ζ` to the usual augmentation of a coordinate filtration.** If the killed values of `X` and of
the constant `1` at rational times `q` are `𝓒 q`-measurable and the paths of `X` are almost surely continuous before
`ζ`, then `X` is adapted before `ζ` to the usual augmentation of `𝓒`. -/
theorem adaptedBefore_usualAugmentation_of_rat {𝓒 : Filtration ℝ≥0 mΩ₀} {P₀ : Measure Ω₀}
    {ζ : Ω₀ → ℝ≥0∞} {X : ℝ≥0 → Ω₀ → ℝ}
    (hXm : ∀ t, Measurable (killedVal ζ X t))
    (h1m : ∀ t, Measurable (killedVal ζ (fun _ _ => (1 : ℝ)) t))
    (hXc : ∀ q : ℚ, Measurable[𝓒 ((q : ℝ)).toNNReal] (killedVal ζ X ((q : ℝ)).toNNReal))
    (h1c : ∀ q : ℚ, Measurable[𝓒 ((q : ℝ)).toNNReal]
      (killedVal ζ (fun _ _ => (1 : ℝ)) ((q : ℝ)).toNNReal))
    (hcont : ∀ᵐ ω ∂P₀, ContinuousOn (fun t => X t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    AdaptedBefore (usualAugmentation 𝓒 P₀) ζ X := by
  intro t A hA
  have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} =
      killedVal ζ (fun _ _ => (1 : ℝ)) t ⁻¹' {1} ∩ killedVal ζ X t ⁻¹' A := by
    ext ω
    by_cases hω : (t : ℝ≥0∞) < ζ ω <;> simp [killedVal, hω]
  rw [e]
  refine measurableSet_usualAugmentation_of_forall_lt
    ((h1m t (measurableSet_singleton 1)).inter (hXm t hA)) fun u hu => ?_
  obtain ⟨q, hqt, hqu, hqlim⟩ := exists_rat_seq_tendsto hu
  have hmono : ∀ n, 𝓒 ((q n : ℝ)).toNNReal ≤ 𝓒 u := fun n => 𝓒.mono (hqu n)
  obtain ⟨gX, hgXm, hgX⟩ := exists_measurable_ae_eq_of_tendsto (P₀ := P₀) (m := 𝓒 u)
    (f := fun n => killedVal ζ X ((q n : ℝ)).toNNReal) (fun n => (hXc (q n)).mono (hmono n) le_rfl)
    (hcont.mono fun ω hω => tendsto_killedVal hω hqlim fun n => (hqt n).le)
  obtain ⟨g1, hg1m, hg1⟩ := exists_measurable_ae_eq_of_tendsto (P₀ := P₀) (m := 𝓒 u)
    (f := fun n => killedVal ζ (fun _ _ => (1 : ℝ)) ((q n : ℝ)).toNNReal)
    (fun n => (h1c (q n)).mono (hmono n) le_rfl)
    (Eventually.of_forall fun ω => tendsto_killedVal (X := fun _ _ => (1 : ℝ)) continuousOn_const
      hqlim fun n => (hqt n).le)
  refine ⟨g1 ⁻¹' {1} ∩ gX ⁻¹' A, (hg1m (measurableSet_singleton 1)).inter (hgXm hA), ?_⟩
  filter_upwards [hgX, hg1] with ω h1 h2
  simp only [mem_inter_iff, mem_preimage, h1, h2]

end Killed

/-! ### The rational-time coordinates and their filtration -/

section CoordDef

variable {Ω₀ : Type*} {nL nR : ℕ}

/-- The coordinate space: for every rational time, the killed indicator of `{q < ζ}`, the killed driving values and
`B`. -/
abbrev CoordSpace (nL nR : ℕ) : Type := ℚ → ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ

/-- The coordinate space is standard Borel (a countable product; instance search does not find it unaided). -/
instance instStandardBorelSpaceCoordSpace (nL nR : ℕ) : StandardBorelSpace (CoordSpace nL nR) :=
  @StandardBorelSpace.pi_countable ℚ _ (fun _ => ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ) _
    fun _ => inferInstance

/-- The coordinates at time `t`: `(1_{t<ζ}, 1_{t<ζ} W_t, 1_{t<ζ} V^L_t, 1_{t<ζ} V^R_t, B_t)`. -/
def coordVal (W : ℝ≥0 → Ω₀ → ℝ) (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ)
    (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞) (t : ℝ≥0) (ω : Ω₀) :
    ℝ × ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ :=
  (killedVal ζ (fun _ _ => 1) t ω, killedVal ζ W t ω, fun i => killedVal ζ (VL i) t ω,
    fun i => killedVal ζ (VR i) t ω, B t ω)

/-- All rational-time coordinates. -/
def coordMap (W : ℝ≥0 → Ω₀ → ℝ) (VL : Fin nL → ℝ≥0 → Ω₀ → ℝ) (VR : Fin nR → ℝ≥0 → Ω₀ → ℝ)
    (B : ℝ≥0 → Ω₀ → ℝ) (ζ : Ω₀ → ℝ≥0∞) (ω : Ω₀) : CoordSpace nL nR :=
  fun q => coordVal W VL VR B ζ ((q : ℝ)).toNNReal ω

variable {W : ℝ≥0 → Ω₀ → ℝ} {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ}
  {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

theorem measurable_coordVal_of {m : MeasurableSpace Ω₀} {t : ℝ≥0}
    (hW : ∀ A : Set ℝ, MeasurableSet A → MeasurableSet[m] {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ A})
    (hVL : ∀ i (A : Set ℝ), MeasurableSet A → MeasurableSet[m] {ω | (t : ℝ≥0∞) < ζ ω ∧ VL i t ω ∈ A})
    (hVR : ∀ i (A : Set ℝ), MeasurableSet A → MeasurableSet[m] {ω | (t : ℝ≥0∞) < ζ ω ∧ VR i t ω ∈ A})
    (hB : Measurable[m] (B t)) : Measurable[m] (coordVal W VL VR B ζ t) := by
  have h1 : ∀ A : Set ℝ, MeasurableSet A →
      MeasurableSet[m] {ω | (t : ℝ≥0∞) < ζ ω ∧ (fun _ _ => (1 : ℝ)) t ω ∈ A} := fun A _ => by
    have e : {ω | (t : ℝ≥0∞) < ζ ω ∧ (fun _ _ => (1 : ℝ)) t ω ∈ A} =
        {ω | (t : ℝ≥0∞) < ζ ω ∧ W t ω ∈ univ} ∩ {_ω | (1 : ℝ) ∈ A} := by
      ext ω; simp
    rw [e]
    exact (hW univ MeasurableSet.univ).inter (MeasurableSet.const _)
  exact (measurable_killedVal h1).prodMk ((measurable_killedVal hW).prodMk
    ((measurable_pi_iff.2 fun i => measurable_killedVal (hVL i)).prodMk
      ((measurable_pi_iff.2 fun i => measurable_killedVal (hVR i)).prodMk hB)))

end CoordDef

section Coord

variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {nL nR : ℕ} {W : ℝ≥0 → Ω₀ → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B : ℝ≥0 → Ω₀ → ℝ} {ζ : Ω₀ → ℝ≥0∞}

/-- The filtration generated by the rational-time coordinates. -/
def coordFiltration (hc : ∀ t, Measurable (coordVal W VL VR B ζ t)) : Filtration ℝ≥0 mΩ₀ where
  seq t := ⨆ (q : ℚ) (_ : ((q : ℝ)).toNNReal ≤ t),
    MeasurableSpace.comap (coordVal W VL VR B ζ ((q : ℝ)).toNNReal) inferInstance
  mono' _ _ hst := iSup₂_mono' fun q hq => ⟨q, hq.trans hst, le_rfl⟩
  le' _ := iSup₂_le fun _ _ => (hc _).comap_le

theorem comap_coordVal_le (hc : ∀ t, Measurable (coordVal W VL VR B ζ t)) (q : ℚ) :
    MeasurableSpace.comap (coordVal W VL VR B ζ ((q : ℝ)).toNNReal) inferInstance ≤
      coordFiltration hc ((q : ℝ)).toNNReal :=
  le_iSup₂ (f := fun (q' : ℚ) (_ : ((q' : ℝ)).toNNReal ≤ ((q : ℝ)).toNNReal) =>
    MeasurableSpace.comap (coordVal W VL VR B ζ ((q' : ℝ)).toNNReal) inferInstance) q le_rfl

theorem measurable_coordMap (hc : ∀ t, Measurable (coordVal W VL VR B ζ t)) :
    Measurable (coordMap W VL VR B ζ) :=
  measurable_pi_iff.2 fun _ => hc _

theorem coordFiltration_le_comap (hc : ∀ t, Measurable (coordVal W VL VR B ζ t)) (t : ℝ≥0) :
    coordFiltration hc t ≤ MeasurableSpace.comap (coordMap W VL VR B ζ) inferInstance :=
  iSup₂_le fun q _ => ((measurable_pi_apply q).comp (comap_measurable (coordMap W VL VR B ζ))).comap_le

theorem isAeGen_coordFiltration {P₀ : Measure Ω₀} (hc : ∀ t, Measurable (coordVal W VL VR B ζ t))
    (t : ℝ≥0) : IsAeGen P₀ (coordMap W VL VR B ζ) (coordFiltration hc t) :=
  isAeGen_comap.mono (coordFiltration_le_comap hc t)

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {P₀ : Measure Ω₀} {𝓕₀ : Filtration ℝ≥0 mΩ₀}

theorem measurable_coordVal_filt (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
    (t : ℝ≥0) : Measurable[𝓕₀ t] (coordVal W VL VR B ζ t) := by
  obtain ⟨⟨-, hBa, -⟩, hWa, hVLa, hVRa, -⟩ := hE
  exact measurable_coordVal_of (hWa t) (fun i => hVLa i t) (fun i => hVRa i t) (hBa t)

theorem measurable_coordVal (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ)
    (t : ℝ≥0) : Measurable (coordVal W VL VR B ζ t) :=
  (measurable_coordVal_filt hE t).mono (𝓕₀.le t) le_rfl

theorem coordFiltration_le (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ) :
    coordFiltration (measurable_coordVal hE) ≤ 𝓕₀ := fun _ =>
  iSup₂_le fun _ hq => ((measurable_coordVal_filt hE _).comap_le).trans (𝓕₀.mono hq)

/-- **The evolution is an integrated evolution for the usual augmentation of its coordinate filtration.** -/
theorem isIntegratedSLEEvolution_coordFiltration
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W VL VR B ζ) :
    IsIntegratedSLEEvolution κ xL xR ρL ρR P₀
      (usualAugmentation (coordFiltration (measurable_coordVal hE)) P₀) W VL VR B ζ := by
  have hc := measurable_coordVal hE
  have hle := coordFiltration_le hE
  set 𝓒 := coordFiltration hc with h𝓒
  have hq : ∀ q : ℚ, Measurable[𝓒 ((q : ℝ)).toNNReal] (coordVal W VL VR B ζ ((q : ℝ)).toNNReal) :=
    fun q => (comap_measurable _).mono (comap_coordVal_le hc q) le_rfl
  have h1c : ∀ q : ℚ, Measurable[𝓒 ((q : ℝ)).toNNReal]
      (killedVal ζ (fun _ _ => (1 : ℝ)) ((q : ℝ)).toNNReal) := fun q => measurable_fst.comp (hq q)
  have hWc : ∀ q : ℚ, Measurable[𝓒 ((q : ℝ)).toNNReal] (killedVal ζ W ((q : ℝ)).toNNReal) :=
    fun q => measurable_fst.comp (measurable_snd.comp (hq q))
  have hVLc : ∀ i (q : ℚ), Measurable[𝓒 ((q : ℝ)).toNNReal] (killedVal ζ (VL i) ((q : ℝ)).toNNReal) :=
    fun i q => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (hq q))))
  have hVRc : ∀ i (q : ℚ), Measurable[𝓒 ((q : ℝ)).toNNReal] (killedVal ζ (VR i) ((q : ℝ)).toNNReal) :=
    fun i q => (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (hq q)))))
  have hBc : ∀ q : ℚ, Measurable[𝓒 ((q : ℝ)).toNNReal] (B ((q : ℝ)).toNNReal) :=
    fun q => measurable_snd.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (hq q))))
  have hm : ∀ {X : ℝ≥0 → Ω₀ → ℝ}, AdaptedBefore 𝓕₀ ζ X → ∀ t, Measurable (killedVal ζ X t) :=
    fun hX t => measurable_killedVal fun A hA => 𝓕₀.le t _ (hX t A hA)
  have h1m : ∀ t, Measurable (killedVal ζ (fun _ _ => (1 : ℝ)) t) := fun t =>
    measurable_fst.comp (hc t)
  obtain ⟨hB, hWa, hVLa, hVRa, hpath⟩ := hE
  refine ⟨⟨hB.1, fun t => ?_, fun s t hst => ?_⟩, ?_, fun i => ?_, fun i => ?_, hpath⟩
  · -- `B` is adapted: the killed version with `ζ = ∞`
    have hBkill : ∀ t, killedVal (fun _ : Ω₀ => (⊤ : ℝ≥0∞)) B t = B t := fun t => by
      funext ω; simp [killedVal]
    have h1kill : ∀ t, killedVal (fun _ : Ω₀ => (⊤ : ℝ≥0∞)) (fun _ _ => (1 : ℝ)) t = fun _ => 1 := fun _ => by
      funext ω; simp [killedVal]
    have hBm : ∀ t, Measurable (B t) := fun t => (hB.2.1 t).mono (𝓕₀.le t) le_rfl
    have hA := adaptedBefore_usualAugmentation_of_rat (𝓒 := 𝓒) (P₀ := P₀) (ζ := fun _ => ⊤) (X := B)
      (fun t => by rw [hBkill]; exact hBm t) (fun t => by rw [h1kill]; exact measurable_const)
      (fun q => by rw [hBkill]; exact hBc q) (fun q => by rw [h1kill]; exact measurable_const)
      (hB.1.cont.mono fun ω h => h.continuousOn)
    intro A hA'
    have e : {ω | (t : ℝ≥0∞) < (fun _ : Ω₀ => (⊤ : ℝ≥0∞)) ω ∧ B t ω ∈ A} = B t ⁻¹' A := by
      ext ω; simp
    rw [← e]
    exact hA t A hA'
  · exact indep_of_indep_of_le_right ((isFilteredBrownianReal_usualAugmentation hB).2.2 s t hst)
      (usualAugmentation_mono hle P₀ s)
  · exact adaptedBefore_usualAugmentation_of_rat (hm hWa) h1m hWc h1c
      (hpath.mono fun ω h => h.2.2.2.1)
  · exact adaptedBefore_usualAugmentation_of_rat (hm (hVLa i)) h1m (hVLc i) h1c
      (hpath.mono fun ω h => h.2.2.2.2.1 i)
  · exact adaptedBefore_usualAugmentation_of_rat (hm (hVRa i)) h1m (hVRc i) h1c
      (hpath.mono fun ω h => h.2.2.2.2.2.1 i)

end Coord

end Coupling

end InteractingSLE

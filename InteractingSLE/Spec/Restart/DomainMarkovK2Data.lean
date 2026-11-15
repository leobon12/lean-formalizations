/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovLocMain

/-!
# K2, part 1: the data of a general continuation, modified on a null set

Packet PROVE-DOMAINMARKOV5, item (K2). PROVE-DOMAINMARKOV2/3 built the single-curve kernel coupling (Aux. lemma 53 in
kernel form) for the restart of one coupling at a stopping time `T`, conditioning on `𝓓_T`. Every two-curve consumer
(Lemma G7's retained pair, the first-contact restart, GB6, Lemma 7.6's continuation) needs the same assembly with a
different conditioning σ-algebra `𝒢` (the joint stopped σ-algebra of the two prefixes) and a different continuation
(the continuation of one path read in the retained chart). This family of files does that assembly **once, for an
arbitrary sub-σ-algebra `𝒢` and arbitrary continuation processes**, from `P`-side inputs only.

This file fixes the continuation data:

* `kData N F W VL VR`: the continuation coordinates on the live event `F` (`0` off `F`), set to `0` on a null set `N`
  (`kW`, `kVL`, `kVR`);
* `kF N F ζ W VL VR`: their countably generated data filtration (Aux. lemma 122's `dataFilt`, no Brownian coordinate);
* `IsKGood N F ζ W VL VR`: off `N`, on `F`, the continuation paths have the null-modification-stable path properties
  (`IsWeakPath`), so that every path of the modified data has them (`IsKGood.isWeakPath`);
* `exists_isKGood`: such an `N` exists as soon as the weak properties hold almost surely on `F`;
* measurability: `dataMeas_k`, `kF_eq`, `adaptedBefore_kData`, `measurableSet_safeU_kF`, `measurable_Y_kF`, and
  `exists_version_of_measurableSet_kF` (an event of `kF t` agrees off `N` with an event of the `P`-side filtration
  `𝓗 t` in which the continuation is adapted).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.DomainMarkov.K2

open Coupling Ito Sec7.Aux122Disint

/-! ### The modified continuation data -/

section Data

variable {Ω : Type*} {nL nR : ℕ}

/-- The continuation coordinates on the live event `F` (`0` off `F`), set to `0` on the null set `N`. -/
def kData (N F : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (i : Option (Fin nL ⊕ Fin nR)) : ℝ≥0 → Ω → ℝ :=
  zeroOn N (wordData F W VL VR i)

/-- The modified driver. -/
def kW (N F : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) :
    ℝ≥0 → Ω → ℝ :=
  kData N F W VL VR none

/-- The modified left marks. -/
def kVL (N F : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) :
    Fin nL → ℝ≥0 → Ω → ℝ :=
  fun i => kData N F W VL VR (some (Sum.inl i))

/-- The modified right marks. -/
def kVR (N F : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) :
    Fin nR → ℝ≥0 → Ω → ℝ :=
  fun j => kData N F W VL VR (some (Sum.inr j))

variable {N F : Set Ω} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {ω : Ω}

theorem kData_of_mem (h : ω ∈ N) (i : Option (Fin nL ⊕ Fin nR)) (t : ℝ≥0) : kData N F W VL VR i t ω = 0 :=
  zeroOn_of_mem h t

theorem kData_of_notMem_F (hF : ω ∉ F) (i : Option (Fin nL ⊕ Fin nR)) (t : ℝ≥0) :
    kData N F W VL VR i t ω = 0 := by
  by_cases h : ω ∈ N
  · exact kData_of_mem h i t
  · rcases i with _ | i | j <;> simp only [kData, wordData, zeroOn_of_notMem h, onF_of_notMem hF]

theorem kW_eq (h : ω ∉ N) (hF : ω ∈ F) (t : ℝ≥0) : kW N F W VL VR t ω = W t ω := by
  simp only [kW, kData, wordData, zeroOn_of_notMem h, onF_of_mem hF]

theorem kVL_eq (h : ω ∉ N) (hF : ω ∈ F) (i : Fin nL) (t : ℝ≥0) : kVL N F W VL VR i t ω = VL i t ω := by
  simp only [kVL, kData, wordData, zeroOn_of_notMem h, onF_of_mem hF]

theorem kVR_eq (h : ω ∉ N) (hF : ω ∈ F) (j : Fin nR) (t : ℝ≥0) : kVR N F W VL VR j t ω = VR j t ω := by
  simp only [kVR, kData, wordData, zeroOn_of_notMem h, onF_of_mem hF]

/-- **The good paths off `N`**: on the live event `F`, the continuation paths have the weak path properties. -/
def IsKGood (N F : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ ω, ω ∉ N → ω ∈ F → IsWeakPath (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω)

/-- **Every path of the modified data has the weak properties.** -/
theorem IsKGood.isWeakPath (hN : IsKGood N F ζ W VL VR) (ω : Ω) :
    IsWeakPath (fun t => kW N F W VL VR t ω) (fun i t => kVL N F W VL VR i t ω)
      (fun j t => kVR N F W VL VR j t ω) (ζ ω) := by
  by_cases hωN : ω ∈ N
  · simp only [kW, kVL, kVR, kData_of_mem hωN]
    exact isWeakPath_zero _
  by_cases hωF : ω ∈ F
  · simp only [kW_eq hωN hωF, kVL_eq hωN hωF, kVR_eq hωN hωF]
    exact hN ω hωN hωF
  · simp only [kW, kVL, kVR, kData_of_notMem_F hωF]
    exact isWeakPath_zero _

/-- Continuity of the (unmodified) data before `ζ`, off `N`. -/
theorem IsKGood.continuousOn_wordData (hN : IsKGood N F ζ W VL VR) :
    ∀ ω, ω ∉ N → ∀ i, ContinuousOn (fun t => wordData F W VL VR i t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  intro ω hω i
  by_cases hωF : ω ∈ F
  · have hp := hN ω hω hωF
    rcases i with _ | i | j
    · simp only [wordData, onF_of_mem hωF]
      exact hp.2.1
    · simp only [wordData, onF_of_mem hωF]
      exact hp.2.2.1 i
    · simp only [wordData, onF_of_mem hωF]
      exact hp.2.2.2.1 j
  · rcases i with _ | i | j <;> simp only [wordData, onF_of_notMem hωF] <;> exact continuousOn_const

variable [mΩ : MeasurableSpace Ω]

/-- **A good null set exists** as soon as the weak properties hold almost surely on `F`; it can be chosen to exclude
any further null event. -/
theorem exists_isKGood {P : Measure Ω}
    (hp : ∀ᵐ ω ∂P, ω ∈ F → IsWeakPath (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (ζ ω))
    {p : Ω → Prop} (hp' : ∀ᵐ ω ∂P, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ IsKGood N F ζ W VL VR ∧ ∀ ω, ω ∉ N → p ω := by
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 (hp.and hp'))
  have hoff : ∀ ω, ω ∉ N → (ω ∈ F → IsWeakPath (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (ζ ω)) ∧ p ω := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  exact ⟨N, hNm, hN0, fun ω hω hF => (hoff ω hω).1 hF, fun ω hω => (hoff ω hω).2⟩

end Data

/-! ### Measurability -/

section Meas

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {N F : Set Ω} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {𝓗 : Filtration ℝ≥0 mΩ}

/-- The data filtration of the modified continuation (driving coordinates only, no Brownian coordinate). -/
abbrev kF (N F : Set Ω) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) : Filtration ℝ≥0 mΩ :=
  dataFilt N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR)

/-- The lifetime events of a process adapted before `ζ`. -/
theorem measurableSet_lt_of_adaptedBefore (hW : AdaptedBefore 𝓗 ζ W) (t : ℝ≥0) :
    MeasurableSet[𝓗 t] {ω | (t : ℝ≥0∞) < ζ ω} := by
  simpa using hW t univ MeasurableSet.univ

/-- The killed continuation data are `𝓗`-adapted. -/
theorem measurable_killAt_wordData (hF0 : MeasurableSet[𝓗 0] F) (hW : AdaptedBefore 𝓗 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j))
    (i : Option (Fin nL ⊕ Fin nR)) (t : ℝ≥0) : Measurable[𝓗 t] (killAt ζ (wordData F W VL VR i) t) := by
  have hFt : MeasurableSet[𝓗 t] F := 𝓗.mono (zero_le (a := t)) _ hF0
  rcases i with _ | i | j
  · exact measurable_killAt_onF hW hFt
  · exact measurable_killAt_onF (hVL i) hFt
  · exact measurable_killAt_onF (hVR j) hFt

/-- **The standing measurability of the modified continuation data.** -/
theorem dataMeas_k (hNm : MeasurableSet N) (hF0 : MeasurableSet[𝓗 0] F) (hW : AdaptedBefore 𝓗 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j)) :
    DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) :=
  ⟨hNm, fun t => 𝓗.le t _ (measurableSet_lt_of_adaptedBefore hW t), fun _ => measurable_const,
    fun i t => (measurable_killAt_wordData hF0 hW hVL hVR i t).mono (𝓗.le t) le_rfl⟩

/-- The data filtration at time `t` is generated by the finite intersections of its generating events. -/
theorem kF_eq (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR)) (t : ℝ≥0) :
    kF N F ζ W VL VR t = MeasurableSpace.generateFrom
      (piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) t)) := by
  rw [generateFrom_piClosure]
  exact inf_eq_left.2 (MeasurableSpace.generateFrom_le fun A hA => hdm.measurableSet_of_mem hA)

theorem measurableSet_kF_of_mem_piClosure (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR))
    {t : ℝ≥0} {A : Set Ω} (hA : A ∈ piClosure (dataGens N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR) t)) :
    MeasurableSet[kF N F ζ W VL VR t] A := by
  obtain ⟨T', hT', hT'S, rfl⟩ := hA
  exact @Set.Finite.measurableSet_sInter Ω (kF N F ζ W VL VR t) T' hT'
    fun C hC => hdm.measurableSet_dataFilt (hT'S hC)

/-- **The modified continuation data are adapted before `ζ` to their data filtration.** -/
theorem adaptedBefore_kData (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR))
    (hN : IsKGood N F ζ W VL VR) (i : Option (Fin nL ⊕ Fin nR)) :
    AdaptedBefore (kF N F ζ W VL VR) ζ (kData N F W VL VR i) :=
  hdm.adaptedBefore_zeroOn hN.continuousOn_wordData i

theorem adaptedBefore_kW (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR))
    (hN : IsKGood N F ζ W VL VR) : AdaptedBefore (kF N F ζ W VL VR) ζ (kW N F W VL VR) :=
  adaptedBefore_kData hdm hN none

theorem adaptedBefore_kVL (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR))
    (hN : IsKGood N F ζ W VL VR) (i : Fin nL) : AdaptedBefore (kF N F ζ W VL VR) ζ (kVL N F W VL VR i) :=
  adaptedBefore_kData hdm hN (some (Sum.inl i))

theorem adaptedBefore_kVR (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR))
    (hN : IsKGood N F ζ W VL VR) (j : Fin nR) : AdaptedBefore (kF N F ζ W VL VR) ζ (kVR N F W VL VR j) :=
  adaptedBefore_kData hdm hN (some (Sum.inr j))

/-- **An event of the data filtration agrees off `N` with an event of the `P`-side filtration.** -/
theorem exists_version_of_measurableSet_kF (hF0 : MeasurableSet[𝓗 0] F) (hW : AdaptedBefore 𝓗 ζ W)
    (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j)) {t : ℝ≥0} {A : Set Ω}
    (hA : MeasurableSet[kF N F ζ W VL VR t] A) : ∃ A', MeasurableSet[𝓗 t] A' ∧ A \ N = A' \ N :=
  exists_eq_diff_of_measurableSet_dataFilt (measurableSet_lt_of_adaptedBefore hW) (fun _ => measurable_const)
    (measurable_killAt_wordData hF0 hW hVL hVR) hA

omit mΩ in
/-- The bounded harmonic extension of the modified data is one at every time. -/
theorem isBoundedHarmonicExtension_bheProc_k (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ω : Ω) (s : ℝ≥0) :
    IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => kVL N F W VL VR i s ω - kW N F W VL VR s ω)
        (fun j => kVR N F W VL VR j s ω - kW N F W VL VR s ω))
      (forceJumpSet (fun i => kVL N F W VL VR i s ω - kW N F W VL VR s ω)
        (fun j => kVR N F W VL VR j s ω - kW N F W VL VR s ω))
      (bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR) ω s) :=
  isBoundedHarmonicExtension_bheProc ω s

variable (hdm : DataMeas N ζ (fun _ _ => (0 : ℝ)) (wordData F W VL VR)) (hN : IsKGood N F ζ W VL VR)

include hdm hN in
theorem measurableSet_safeU_kF (G : Set Ω) (hG : MeasurableSet[kF N F ζ W VL VR 0] G)
    (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    MeasurableSet[kF N F ζ W VL VR q] (safeU (kW N F W VL VR) ζ G ψ q) :=
  measurableSet_safeU hN.isWeakPath (adaptedBefore_kW hdm hN) hG ψ q

include hdm hN in
/-- `1_S cfAt q` is `kF q`-measurable. -/
theorem measurable_Y_kF (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0) :
    Measurable[kF N F ζ W VL VR q] ((safeU (kW N F W VL VR) ζ univ ψ q).indicator
      (cfAt κ (kW N F W VL VR) (bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR)) ψ 1
        fun _ => q)) :=
  measurable_safeU_indicator_cfAt_of_weak hN.isWeakPath (adaptedBefore_kW hdm hN) MeasurableSet.univ _
    (fun ω s => isBoundedHarmonicExtension_bheProc_k κ ρL ρR ω s) (adaptedBefore_kVL hdm hN)
    (adaptedBefore_kVR hdm hN) ψ q

omit mΩ in
include hN in
/-- `1_S cfAt q` has modulus at most one. -/
theorem norm_Y_le (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ψ : TestOn upperHalfPlaneOpens) (q : ℝ≥0)
    (ω : Ω) :
    ‖(safeU (kW N F W VL VR) ζ univ ψ q).indicator
      (cfAt κ (kW N F W VL VR) (bheProc κ ρL ρR (kW N F W VL VR) (kVL N F W VL VR) (kVR N F W VL VR)) ψ 1
        fun _ => q) ω‖ ≤ 1 := by
  by_cases hω : ω ∈ safeU (kW N F W VL VR) ζ univ ψ q
  · rw [indicator_of_mem hω]
    exact norm_cfAt_le_one_of_mem_safeU' hN.isWeakPath _ ψ hω
  · rw [indicator_of_notMem hω, norm_zero]
    exact zero_le_one

end Meas

end InteractingSLE.Restart.DomainMarkov.K2

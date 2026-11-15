/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Wire
import InteractingSLE.Spec.Sec7.Lemma725RefK2

/-!
# The stopped K2 with announcing stops read from a conditioning record

Packet PROVE-Q3-REL4 (Theorem 1.4's GB6 relative stopped coupling, step (D)). The stopped K2
(`Restart.StoppedK2.ae_isStoppedHullCoupling_k`) proves the conditional-law clause of a coupling through a stop `V`
at every stopping time `τ ≤ V` from below, along stopping times `σₙ < V` announcing `V`. It asks the `σₙ` to be
stopping times of the `P`-side driving filtration of the continuation, which does not contain the conditioning
σ-algebra `𝒢`. In GB6 the stops of the relative versions are read from the record of the flow prefix (a `𝒢`-variable)
and the relative path, so their announcing stops depend on the record too.

Under the regular conditional law `ν = condExpKernel P 𝒢 ω₀` the record is almost surely constant, so a record-path
rule is a stopping time of the `ν`-side driving filtration. This file proves the stopped K2 with exactly that
hypothesis:

* `IsKernelStop`: `σ` is, for almost every `ω₀` in the live event, a stopping time of the `ν`-side driving filtration
  of every version agreeing `ν`-almost surely with the continuation before `V` (the conclusion of the landed transfer
  `StoppedK2.ae_isStoppingTime_of_agree`, which is `isKernelStop_of_isStoppingTime`);
* `measurableSet_killedDrivingSigma_path`: on `{t < V}`, every event of the driver path determined by the path on
  `[0, t]` is an event of the killed driving σ-algebra at `t`;
* **`isKernelStop_of_pathRule`**: a record-path rule `σ = ρ(rec, W)` (unchanged when the path changes after its value,
  `rec` a `𝒢`-measurable record in a countably separated space) with `σ < V` on the live event is a kernel stop;
* **`ae_isStoppedHullCoupling_kk`**, **`ae_isStoppedHullCoupling_kk_prod`**: the stopped K2 (on `Ω` and on the
  enlargement `Ω × Ω₀`) with kernel stops instead of `P`-side driving stopping times. The proofs are those of
  `StoppedK2.ae_isStoppedHullCoupling_k(_prod)`, with the one transfer step replaced by the hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Supp8.Q3Stop

open Restart Restart.StoppedK2

/-! ### Path events in the killed driving σ-algebra -/

section Path

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {V : Ω → ℝ≥0∞}

/-- The live event `{t < V}` is an event of the killed driving σ-algebra at `t`. -/
theorem measurableSet_killedDrivingSigma_live (t : ℝ≥0) :
    MeasurableSet[killedDrivingSigma W VL VR V t] {ω | (t : ℝ≥0∞) < V ω} := by
  refine MeasurableSpace.measurableSet_generateFrom ⟨t, le_rfl, univ, MeasurableSet.univ, ?_⟩
  ext ω
  simp only [mem_ofPred_eq, mem_univ, and_true]

/-- **Path events on the live event.** If `S` is a measurable set of paths determined by the path on `[0, t]`, then
`{t < V, W ∈ S}` is an event of the killed driving σ-algebra at `t`. -/
theorem measurableSet_killedDrivingSigma_path (t : ℝ≥0) {S : Set (ℝ≥0 → ℝ)} (hS : MeasurableSet S)
    (hdet : ∀ w w' : ℝ≥0 → ℝ, (∀ u ≤ t, w u = w' u) → (w ∈ S ↔ w' ∈ S)) :
    MeasurableSet[killedDrivingSigma W VL VR V t] {ω | (t : ℝ≥0∞) < V ω ∧ (fun u => W u ω) ∈ S} := by
  set Y : Ω → ℝ≥0 → ℝ := fun ω u => W (min u t) ω with hY
  have hlive := measurableSet_killedDrivingSigma_live (W := W) (VL := VL) (VR := VR) (V := V) t
  let m' : MeasurableSpace (ℝ≥0 → ℝ) :=
    { MeasurableSet' := fun S' =>
        MeasurableSet[killedDrivingSigma W VL VR V t] {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ S'}
      measurableSet_empty := by
        simp only [mem_empty_iff_false, and_false, ofPred_false]
        exact @MeasurableSet.empty Ω (killedDrivingSigma W VL VR V t)
      measurableSet_compl := fun S' h => by
        have e : {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ S'ᶜ} =
            {ω | (t : ℝ≥0∞) < V ω} \ {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ S'} := by
          ext ω
          simp only [mem_ofPred_eq, mem_compl_iff, Set.mem_sdiff]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 h.2⟩
          · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 ⟨h1, h⟩⟩
        rw [e]
        exact hlive.diff h
      measurableSet_iUnion := fun f hf => by
        have e : {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ ⋃ i, f i} = ⋃ i, {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ f i} := by
          ext ω
          simp only [mem_ofPred_eq, mem_iUnion]
          constructor
          · rintro ⟨h1, i, h2⟩; exact ⟨i, h1, h2⟩
          · rintro ⟨i, h1, h2⟩; exact ⟨h1, i, h2⟩
        rw [e]
        exact MeasurableSet.iUnion hf }
  have hle : (MeasurableSpace.pi : MeasurableSpace (ℝ≥0 → ℝ)) ≤ m' := by
    rw [MeasurableSpace.pi_eq_generateFrom_projections]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨u, A, hA, rfl⟩
    show MeasurableSet[killedDrivingSigma W VL VR V t] {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ Function.eval u ⁻¹' A}
    have hut : min u t ≤ t := min_le_right _ _
    have e : {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ Function.eval u ⁻¹' A} = {ω | (t : ℝ≥0∞) < V ω} ∩
        {ω | ((min u t : ℝ≥0) : ℝ≥0∞) < V ω ∧
          (W (min u t) ω, fun i => VL i (min u t) ω, fun j => VR j (min u t) ω) ∈ A ×ˢ (univ : Set
            ((Fin nL → ℝ) × (Fin nR → ℝ)))} := by
      ext ω
      simp only [mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.eval, mem_prod, mem_univ, and_true, hY]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 hut) h1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    rw [e]
    exact hlive.inter (MeasurableSpace.measurableSet_generateFrom
      ⟨min u t, hut, A ×ˢ univ, hA.prod MeasurableSet.univ, rfl⟩)
  have hSY : {ω | (t : ℝ≥0∞) < V ω ∧ (fun u => W u ω) ∈ S} = {ω | (t : ℝ≥0∞) < V ω ∧ Y ω ∈ S} := by
    ext ω
    simp only [mem_ofPred_eq]
    rw [hdet (fun u => W u ω) (Y ω) fun u hu => by simp only [hY, min_eq_left hu]]
  rw [hSY]
  exact hle S hS

end Path

/-! ### Kernel stops -/

section KernelStop

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {P : Measure Ω}

/-- **A kernel stop**: for almost every `ω₀` in the live event `F`, `σ` is a stopping time of the driving
filtration, under the regular conditional law `condExpKernel P 𝒢 ω₀` and killed at `V`, of every version agreeing
almost surely with `(W, VL, VR)` before `V`. -/
def IsKernelStop {Ω' : Type*} (𝒢' : MeasurableSpace Ω') [MeasurableSpace Ω'] [StandardBorelSpace Ω']
    (Q : Measure Ω') [IsFiniteMeasure Q] (F : Set Ω')
    (W : ℝ≥0 → Ω' → ℝ) (VL : Fin nL → ℝ≥0 → Ω' → ℝ) (VR : Fin nR → ℝ≥0 → Ω' → ℝ) (V : Ω' → ℝ≥0∞)
    (σ : Ω' → WithTop ℝ≥0) : Prop :=
  ∀ᵐ ω₀ ∂Q, ω₀ ∈ F → ∀ (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ) (VR' : Fin nR → ℝ≥0 → Ω' → ℝ)
    (hX' : IsMeasurableKilledDriving W' VL' VR' V),
    (∀ᵐ ω ∂(condExpKernel Q 𝒢' ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W' t ω = W t ω ∧
      (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) →
    IsStoppingTime (drivingFiltration (condExpKernel Q 𝒢' ω₀) hX') σ

/-- A stopping time of the `P`-side driving filtration is a kernel stop (`StoppedK2.ae_isStoppingTime_of_agree`). -/
theorem isKernelStop_of_isStoppingTime [StandardBorelSpace Ω] [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    (hXP : IsMeasurableKilledDriving W VL VR V) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hXP) σ) (F : Set Ω) : IsKernelStop 𝒢 P F W VL VR V σ := by
  filter_upwards [ae_isStoppingTime_of_agree (𝒢 := 𝒢) (P := P) h𝒢 hXP hσ] with ω₀ h _ using h

/-- **A record-path rule is a kernel stop.** Let `rec` be a `𝒢`-measurable record with values in a countably
separated space and `ρ` a measurable rule on (record, path) whose value does not change when the path changes after
it. If `ρ(rec, W) < V` almost surely on the live event `F ∈ 𝒢`, then `σ = ρ(rec, W)` is a kernel stop: under almost
every conditional law the record is constant, and `{σ ≤ t}` is, up to a null set, `{V ≤ t} ∪ {t < V, W ∈ S_t}` with
`S_t` an event of the path on `[0, t]`. -/
theorem isKernelStop_of_pathRule [StandardBorelSpace Ω] [IsProbabilityMeasure P] (h𝒢 : 𝒢 ≤ mΩ)
    {ε : Type*} [MeasurableSpace ε] [MeasurableSpace.CountablySeparated ε] {rec : Ω → ε}
    (hrec : Measurable[𝒢] rec) {ρ : ε × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ)
    (hρ : ∀ (r : ε) (w w' : ℝ≥0 → ℝ), (∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ ρ (r, w) → w u = w' u) → ρ (r, w') = ρ (r, w))
    (hWm : ∀ t, Measurable (W t)) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    (hlt : ∀ᵐ ω ∂P, ω ∈ F → ρ (rec ω, fun u => W u ω) < V ω) :
    IsKernelStop 𝒢 P F W VL VR V fun ω => (ρ (rec ω, fun u => W u ω) : WithTop ℝ≥0) := by
  have hpath : Measurable fun ω => (rec ω, fun u => W u ω) :=
    (hrec.mono h𝒢 le_rfl).prodMk (measurable_pi_iff.2 hWm)
  have hσm : Measurable fun ω => ρ (rec ω, fun u => W u ω) := hρm.comp hpath
  filter_upwards [Sec7.Lemma725RefK2.ae_ae_condExpKernel_eq_self (P := P) h𝒢 hrec,
    Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 hlt,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := P) h𝒢 hF] with ω₀ hrec₀ hlt₀ hF₀ hω₀F
    W' VL' VR' hX' hag
  set ν := condExpKernel P 𝒢 ω₀ with hν
  set r₀ := rec ω₀ with hr₀
  intro t
  -- the path event at the record `r₀`
  set S : Set (ℝ≥0 → ℝ) := {w | ρ (r₀, w) ≤ (t : ℝ≥0∞)} with hSdef
  have hSm : MeasurableSet S := measurableSet_le (hρm.comp measurable_prodMk_left) measurable_const
  have hdet : ∀ w w' : ℝ≥0 → ℝ, (∀ u ≤ t, w u = w' u) → (w ∈ S ↔ w' ∈ S) := by
    intro w w' hww'
    simp only [hSdef, mem_ofPred_eq]
    constructor
    · intro h
      rw [hρ r₀ w w' fun u hu => hww' u (ENNReal.coe_le_coe.1 (hu.trans h))]
      exact h
    · intro h
      rw [hρ r₀ w' w fun u hu => (hww' u (ENNReal.coe_le_coe.1 (hu.trans h))).symm]
      exact h
  set C : Set Ω := {ω | (t : ℝ≥0∞) < V ω}ᶜ ∪ {ω | (t : ℝ≥0∞) < V ω ∧ (fun u => W' u ω) ∈ S} with hCdef
  have hC : MeasurableSet[killedDrivingFiltration hX' t] C :=
    (measurableSet_killedDrivingSigma_live (W := W') (VL := VL') (VR := VR') t).compl.union
      (measurableSet_killedDrivingSigma_path t hSm hdet)
  have hE : MeasurableSet {ω | (ρ (rec ω, fun u => W u ω) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} :=
    measurableSet_le hσm measurable_const
  have hEC : {ω | (ρ (rec ω, fun u => W u ω) : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} =ᵐ[ν] C := by
    filter_upwards [hrec₀, hlt₀, hF₀ hω₀F, hag] with ω hrω hltω hFω hagω
    have hlt' := hltω hFω
    rw [hrω] at hlt'
    change (ρ (rec ω, fun u => W u ω) ≤ (t : ℝ≥0∞)) = (ω ∈ C)
    rw [hrω]
    simp only [hCdef, hSdef, mem_union, mem_compl_iff, mem_ofPred_eq, not_lt]
    apply propext
    by_cases htV : (t : ℝ≥0∞) < V ω
    · have hpw : ∀ u ≤ t, W u ω = W' u ω := fun u hu =>
        ((hagω u (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) htV)).1).symm
      have := hdet (fun u => W u ω) (fun u => W' u ω) hpw
      simp only [hSdef, mem_ofPred_eq] at this
      rw [this]
      exact ⟨fun h => Or.inr ⟨htV, h⟩, fun h => h.elim (fun h' => absurd h' (not_le.2 htV)) fun h' => h'.2⟩
    · exact ⟨fun _ => Or.inl (not_lt.1 htV), fun _ => (le_of_lt hlt').trans (not_lt.1 htV)⟩
  have h1 := Coupling.measurableSet_nullAugmented_of_ae_eq (𝓕 := killedDrivingFiltration hX') (P := ν) hE hC hEC
  exact Ito.nullAugmented_le_usualAugmentation _ ν t _ h1

end KernelStop

/-! ### The stopped K2 with kernel stops -/

section Main

open Coupling Ito Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7 Sec7.Aux122Disint
open Restart.DomainMarkov.Aux79 (IsForceReg)
open QuantumZipper (H fwdHull)
open SupercriticalConformalCovariance.GM24 (smoothDist)

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {nL nR : ℕ}
  {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {V : Ω → ℝ≥0∞} {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The stopped K2 with kernel stops** (`StoppedK2.ae_isStoppedHullCoupling_k` with its announcing stops only
required to be kernel stops, `IsKernelStop`; same proof). From (E-stop), (S) and (L) with lifetime `V`, and kernel
stops `σₙ < V` announcing `V` on `F`: for `P`-almost every `ω₀ ∈ F`, under `condExpKernel P 𝒢 ω₀`, processes equal
almost surely to the continuation on `[0, V]` form, with the field `X`, a coupling through `V` of the word
`(ΘL ω₀, ΘR ω₀)`; the driver of the coupling is frozen after a finite `V`. -/
theorem ae_isStoppedHullCoupling_kk
    (hE : IsRandomWordEvolutionUpTo κ P 𝒢 F ΘL ΘR ρL ρR 𝓗 W VL VR B V)
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω)
    {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0) (hW' : AdaptedBefore 𝓗' V W)
    (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i)) (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X) (hmem : HasSafeMembers P 𝓗' F V W X)
    {σ : ℕ → Ω → WithTop ℝ≥0} (hT : ∀ n, IsKernelStop 𝒢 P F W VL VR V (σ n))
    (hσm : ∀ ω, Monotone fun n => σ n ω) (hσV : ∀ᵐ ω ∂P, ω ∈ F → ∀ n, (σ n ω : ℝ≥0∞) < V ω)
    (hσlim : ∀ᵐ ω ∂P, ω ∈ F → Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω))) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        StoppedExtend.IsStoppedHullCoupling κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B' V X ∧
        (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V ω →
          W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ∀ t : ℝ≥0, T ≤ t → W' t ω = W' T ω := by
  obtain ⟨NE, 𝓖, W'', VL'', VR'', B'', -, hNE0, hagE, hev⟩ := exists_ae_condExpKernel_agree_upTo hE
  obtain ⟨h0, hF, -, -, -, -, -, -, hpath⟩ := hE
  have h𝒢m : 𝒢 ≤ mΩ := h0.trans (𝓗.le 0)
  have hweakP : ∀ᵐ ω ∂P, ω ∈ F →
      IsWeakPath (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (V ω) := by
    filter_upwards [hpath] with ω h hωF
    have hp := h hωF
    exact ⟨hp.w_zero, hp.continuousOn_w, hp.continuousOn_vL, hp.continuousOn_vR,
      fun t ht i => hp.vL_le_w ht i, fun t ht j => hp.w_le_vR ht j⟩
  obtain ⟨N, hNm, hN0, hN, -⟩ := exists_isKGood hweakP (p := fun _ => True) (ae_of_all _ fun _ => trivial)
  have hS := ae_isDyadicSampled_k h𝒢' hF hW' hVL' hVR' hX hNm hN0 hN hlaw
  have hR := ae_hasRatMembers_k h𝒢' hF hW' hVL' hVR' hX hNm hN0 hN hmem
  filter_upwards [hev, hS, hR, ae_all_iff.2 hT,
    ae_ae_condExpKernel h𝒢m (measure_eq_zero_iff_ae_notMem.1 hN0),
    ae_ae_condExpKernel h𝒢m (measure_eq_zero_iff_ae_notMem.1 hNE0),
    ae_ae_condExpKernel_mem (P := P) h𝒢m hF, ae_ae_condExpKernel h𝒢m hV0, ae_ae_condExpKernel h𝒢m hcont,
    ae_ae_condExpKernel h𝒢m hσV, ae_ae_condExpKernel h𝒢m hσlim] with ω₀ hev0 hS0 hR0 hT0 hNν hNEν hmemF hV0ν
    hcontν hσVν hσlimν hω₀F
  set ν := condExpKernel P 𝒢 ω₀ with hν
  have hE'' := hev0 hω₀F
  have hFν : ∀ᵐ ω ∂ν, ω ∈ F := hmemF hω₀F
  have hgood : ∀ᵐ ω ∂ν, ω ∈ F ∧ ω ∉ N ∧ ω ∉ NE ∧ 0 < V ω := by
    filter_upwards [hFν, hNν, hNEν, hV0ν] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4 h1⟩
  have hWW : ∀ ω, ω ∉ NE → ω ∈ F → ∀ t, W'' t ω = W t ω ∧ (∀ i, VL'' i t ω = VL i t ω) ∧
      ∀ j, VR'' j t ω = VR j t ω := fun ω h1 h2 t => by
    obtain ⟨e1, e2, e3, -⟩ := hagE ω h1 h2 t
    exact ⟨e1, e2, e3⟩
  -- the version frozen after `V`
  set W₁ : ℝ≥0 → Ω → ℝ := frz V W'' with hW₁
  set VL₁ : Fin nL → ℝ≥0 → Ω → ℝ := fun i => frz V (VL'' i) with hVL₁
  set VR₁ : Fin nR → ℝ≥0 → Ω → ℝ := fun j => frz V (VR'' j) with hVR₁
  have hag₁ : AgreeBefore V W'' VL'' VR'' W₁ VL₁ VR₁ := agreeBefore_frz
  have hE₁ : Sec2.IsSLEEvolutionUpTo κ (ΘL ω₀) (ΘR ω₀) ρL ρR ν 𝓖 W₁ VL₁ VR₁ B'' V := by
    refine ⟨hE''.brownian, adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).1) hE''.adapted_W,
      fun i => adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).2.1 i) (hE''.adapted_VL i),
      fun j => adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).2.2 j) (hE''.adapted_VR j), ?_⟩
    filter_upwards [hE''.ae_path, hgood] with ω hp hg
    exact isSLEPathUpTo_congr hg.2.2.2 (fun t ht => (hag₁ ω t ht).1) (fun t ht i => (hag₁ ω t ht).2.1 i)
      (fun t ht j => (hag₁ ω t ht).2.2 j) hp
  have hX₁ : IsMeasurableKilledDriving W₁ VL₁ VR₁ V :=
    isMeasurableKilledDriving_of_adaptedBefore hE₁.adapted_W hE₁.adapted_VL hE₁.adapted_VR
  have hX'' : IsMeasurableKilledDriving W'' VL'' VR'' V :=
    isMeasurableKilledDriving_of_adaptedBefore hE''.adapted_W hE''.adapted_VL hE''.adapted_VR
  -- continuity of the version on `[0, V]`
  have hcont'' : ∀ᵐ ω ∂ν, V ω ≠ ⊤ → ContinuousOn (W'' · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL'' i · ω) (Iic (V ω).toNNReal)) ∧
        ∀ j, ContinuousOn (VR'' j · ω) (Iic (V ω).toNNReal) := by
    filter_upwards [hgood, hcontν] with ω hg hc hVt
    obtain ⟨c1, c2, c3⟩ := hc hg.1 hVt
    exact ⟨c1.congr fun t _ => (hWW ω hg.2.2.1 hg.1 t).1, fun i => (c2 i).congr fun t _ =>
      (hWW ω hg.2.2.1 hg.1 t).2.1 i, fun j => (c3 j).congr fun t _ => (hWW ω hg.2.2.1 hg.1 t).2.2 j⟩
  -- regularity of the frozen version
  have hreg : ∀ᵐ ω ∂ν, IsForceReg W₁ VL₁ VR₁ (fun _ => ⊤) ω ∧ IsForceReg W₁ VL₁ VR₁ V ω := by
    filter_upwards [hE₁.ae_path, hE''.ae_path, hgood, hcont''] with ω hp₁ hp hg hc
    have hr'' : IsForceReg W'' VL'' VR'' V ω := ⟨hp.w_zero, hp.continuousOn_w, hp.continuousOn_vL,
      hp.continuousOn_vR, fun t ht => ⟨fun i => hp.vL_le_w ht i, fun j => hp.w_le_vR ht j⟩⟩
    exact ⟨isForceReg_frz_top hg.2.2.2 hr'' (fun h => (hc h).1) (fun h => (hc h).2.1) (fun h => (hc h).2.2),
      ⟨hp₁.w_zero, hp₁.continuousOn_w, hp₁.continuousOn_vL, hp₁.continuousOn_vR,
        fun t ht => ⟨fun i => hp₁.vL_le_w ht i, fun j => hp₁.w_le_vR ht j⟩⟩⟩
  -- K2's transferred identities for the frozen version
  have hagK : ∀ᵐ ω ∂ν, ∀ t, W'' t ω = kW N F W VL VR t ω ∧ (∀ i, VL'' i t ω = kVL N F W VL VR i t ω) ∧
      ∀ j, VR'' j t ω = kVR N F W VL VR j t ω := by
    filter_upwards [hgood] with ω hg t
    obtain ⟨e1, e2, e3⟩ := hWW ω hg.2.2.1 hg.1 t
    exact ⟨by rw [e1, kW_eq hg.2.1 hg.1], fun i => by rw [e2 i, kVL_eq hg.2.1 hg.1],
      fun j => by rw [e3 j, kVR_eq hg.2.1 hg.1]⟩
  have hdy₁ : IsDyadicSampled κ W₁ (bheProc κ ρL ρR W₁ VL₁ VR₁) ν hX₁ X :=
    isDyadicSampled_congr hX'' hX₁ hag₁ (hS0 hω₀F W'' VL'' VR'' hX'' hagK)
  have hXm' : ∀ ψ, Measurable fun ω => X ω ψ := fun ψ => (LQGMetric.measurable_distOn_apply ψ).comp hX
  have hcf : MartMeans.IsCouplingCharFun κ ρL ρR ν (drivingFiltration ν hX₁) W₁ VL₁ VR₁ V X :=
    isCouplingCharFun_of_dyadic_reg hX₁ X hXm' hdy₁ (hreg.mono fun ω h => h.2)
  have h0' : ∀ᵐ ω ∂ν, 0 < V ω ∧ ContinuousOn (fun t => W₁ t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W₁ 0 ω = 0 ∧
      (∀ i, VL₁ i 0 ω = ΘL ω₀ i) ∧ ∀ j, VR₁ j 0 ω = ΘR ω₀ j := by
    filter_upwards [hE₁.ae_path, hgood] with ω hp hg
    exact ⟨hg.2.2.2, hp.continuousOn_w, hp.w_zero, hp.vL_zero, hp.vR_zero⟩
  have hgff : ∀ u₀ : ℂ → ℝ, IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR (ΘL ω₀) (ΘR ω₀))
      (forceJumpSet (ΘL ω₀) (ΘR ω₀)) u₀ →
      LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) ν :=
    fun u₀ hu₀ => Lemma71J.isZBGFFProcess_of_isCouplingCharFun hcf hX h0' hu₀
  -- the field, centred
  have hu₀ := LocalExt.isBoundedHarmonicExtension_bheAt κ ρL ρR (ΘL ω₀) (ΘR ω₀)
  set u₀ := LocalExt.bheAt κ ρL ρR (ΘL ω₀) (ΘR ω₀) with hu₀def
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hXgff := isZeroBoundaryGFF_sub_smoothDist hX hu₀c (hgff u₀ hu₀)
  have hsm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H :=
    WholeField.isHarmonicDistOn_smoothDist hu₀.1
  have hagK₁ : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W₁ t ω = kW N F W VL VR t ω ∧
      (∀ i, VL₁ i t ω = kVL N F W VL VR i t ω) ∧ ∀ j, VR₁ j t ω = kVR N F W VL VR j t ω := by
    filter_upwards [hagK] with ω hω t ht
    obtain ⟨e1, e2, e3⟩ := hag₁ ω t ht
    obtain ⟨f1, f2, f3⟩ := hω t
    exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
  have hmb₁ := hR0 hω₀F u₀ hu₀.1 (hgff u₀ hu₀) W₁ VL₁ VR₁ hX₁ hagK₁
  have hagP₁ : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W₁ t ω = W t ω ∧
      (∀ i, VL₁ i t ω = VL i t ω) ∧ ∀ j, VR₁ j t ω = VR j t ω := by
    filter_upwards [hgood] with ω hg t ht
    obtain ⟨e1, e2, e3⟩ := hag₁ ω t ht
    obtain ⟨f1, f2, f3⟩ := hWW ω hg.2.2.1 hg.1 t
    exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
  have hσν : ∀ n, IsStoppingTime (drivingFiltration ν hX₁) (σ n) := fun n => hT0 n hω₀F W₁ VL₁ VR₁ hX₁ hagP₁
  have hσVν' : ∀ᵐ ω ∂ν, ∀ n, (σ n ω : ℝ≥0∞) < V ω := by
    filter_upwards [hσVν, hFν] with ω h1 h2 using h1 h2
  have hσlimν' : ∀ᵐ ω ∂ν, Tendsto (fun n => (σ n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
    filter_upwards [hσlimν, hFν] with ω h1 h2 using h1 h2
  have hWa : AdaptedBefore (killedDrivingFiltration hX₁) (fun _ => ⊤) W₁ :=
    adaptedBefore_frz (adaptedBefore_congr (fun ω t ht => (hag₁ ω t ht).1.symm) (adaptedBefore_killedDriving_W hX₁))
  have hcontT : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W₁ t ω) {t | (t : ℝ≥0∞) < ⊤} ∧ W₁ 0 ω = 0 :=
    hreg.mono fun ω h => ⟨h.1.2.1, h.1.1⟩
  have hpath₁ : ∀ᵐ ω ∂ν, ContinuousOn (fun t => W₁ t ω) {t | (t : ℝ≥0∞) < V ω} ∧ W₁ 0 ω = 0 :=
    hreg.mono fun ω h => ⟨h.2.2.1, h.2.1⟩
  have hV0' : ∀ᵐ ω ∂ν, 0 < V ω := hgood.mono fun ω h => h.2.2.2
  refine ⟨𝓖, W₁, VL₁, VR₁, B'', ⟨hE₁, ?_, hX, hgff, hX₁, fun τ hτ hτV => ⟨?_, fun u hu φ => ?_⟩⟩, ?_, ?_⟩
  · -- the state is continuous through a finite stop
    filter_upwards [hreg] with ω h T _
    have cW : Continuous (W₁ · ω) := continuousOn_univ.1 (h.1.2.1.mono fun t _ => ENNReal.coe_lt_top)
    have cL : ∀ i, Continuous (VL₁ i · ω) := fun i =>
      continuousOn_univ.1 ((h.1.2.2.1 i).mono fun t _ => ENNReal.coe_lt_top)
    have cR : ∀ j, Continuous (VR₁ j · ω) := fun j =>
      continuousOn_univ.1 ((h.1.2.2.2.1 j).mono fun t _ => ENNReal.coe_lt_top)
    exact (cW.prodMk ((continuous_pi cL).prodMk (continuous_pi cR))).continuousOn
  · -- locality, from below
    have h2 := IsLocalSet.add_dist (isLocalSet_hull_le_stop hX₁ hXgff hmb₁ hpath₁ hV0' hWa hcontT hσν hσm
      hσVν' hσlimν' hτ hτV) hsm
    have e : (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀ + smoothDist upperHalfPlaneOpens u₀) = X :=
      funext fun ω => sub_add_cancel _ _
    rw [e] at h2
    exact h2
  · -- the conditional law, from below
    exact condExp_cexp_eq_of_le_stop hX₁ hXm' hcf (hreg.mono fun ω h => h.1) hσν hσm hσVν' hσlimν' hτ hτV u hu φ
  · -- agreement on `[0, V]`
    filter_upwards [hgood, hcont''] with ω hg hc t ht
    rcases ht.lt_or_eq with htV | htV
    · obtain ⟨e1, e2, e3⟩ := hag₁ ω t htV
      obtain ⟨f1, f2, f3⟩ := hWW ω hg.2.2.1 hg.1 t
      exact ⟨e1.trans f1, fun i => (e2 i).trans (f2 i), fun j => (e3 j).trans (f3 j)⟩
    · have hVt : V ω ≠ ⊤ := htV ▸ ENNReal.coe_ne_top
      have hta : t = (V ω).toNNReal := by rw [← htV, ENNReal.toNNReal_coe]
      obtain ⟨c1, c2, c3⟩ := hc hVt
      obtain ⟨f1, f2, f3⟩ := hWW ω hg.2.2.1 hg.1 t
      have hmin : min t (V ω).toNNReal = t := by rw [← hta, min_self]
      refine ⟨?_, fun i => ?_, fun j => ?_⟩
      · rw [hW₁, frz_eq_min hg.2.2.2 hVt c1, hmin, f1]
      · simp only [hVL₁]
        rw [frz_eq_min hg.2.2.2 hVt (c2 i), hmin, f2 i]
      · simp only [hVR₁]
        rw [frz_eq_min hg.2.2.2 hVt (c3 j), hmin, f3 j]
  · -- the driver is frozen after `V`
    filter_upwards [hgood, hcont''] with ω hg hc T hT t hTt
    have hVt : V ω ≠ ⊤ := hT ▸ ENNReal.coe_ne_top
    have hTa : (V ω).toNNReal = T := by rw [← hT, ENNReal.toNNReal_coe]
    rw [hW₁, frz_eq_min hg.2.2.2 hVt (hc hVt).1, frz_eq_min hg.2.2.2 hVt (hc hVt).1, hTa, min_eq_right hTt,
      min_self]


end Main

/-! ### The stopped K2 with kernel stops on the enlargement -/

section K2Prod

open Restart.DomainMarkov Restart.DomainMarkov.K2 ConverseBefore

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Ω₀ : Type*}
  [m₀ : MeasurableSpace Ω₀] [StandardBorelSpace Ω₀] {P : Measure Ω} [IsProbabilityMeasure P] {P₀ : Measure Ω₀}
  [IsProbabilityMeasure P₀] {nL nR : ℕ} {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {F : Set Ω}
  {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **The stopped K2 with kernel stops on the enlargement `Ω × Ω₀`** (`StoppedK2.ae_isStoppedHullCoupling_k_prod`
with kernel stops of the enlargement): (E-stop) on the enlargement, (S), (L), adaptedness, continuity through the
stop and positivity on `Ω`, and kernel stops on the enlargement announcing the stop on the live event. -/
theorem ae_isStoppedHullCoupling_kk_prod
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))} {B : ℝ≥0 → Ω × Ω₀ → ℝ}
    (hE : IsRandomWordEvolutionUpTo κ (P.prod P₀) (𝒢.comap Prod.fst) (Prod.fst ⁻¹' F) (fun p => ΘL p.1)
      (fun p => ΘR p.1) ρL ρR 𝓕 (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B
      (fun p => V p.1))
    (hcont : ∀ᵐ ω ∂P, ω ∈ F → V ω ≠ ⊤ → ContinuousOn (W · ω) (Iic (V ω).toNNReal) ∧
      (∀ i, ContinuousOn (VL i · ω) (Iic (V ω).toNNReal)) ∧ ∀ j, ContinuousOn (VR j · ω) (Iic (V ω).toNNReal))
    (hX : Measurable X) (hV0 : ∀ᵐ ω ∂P, ω ∈ F → 0 < V ω) {𝓗' : Filtration ℝ≥0 mΩ} (h𝒢' : 𝒢 ≤ 𝓗' 0)
    (hW' : AdaptedBefore 𝓗' V W) (hVL' : ∀ i, AdaptedBefore 𝓗' V (VL i))
    (hVR' : ∀ j, AdaptedBefore 𝓗' V (VR j))
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗' F V W VL VR X) (hmem : HasSafeMembers P 𝓗' F V W X)
    {σ : ℕ → Ω × Ω₀ → WithTop ℝ≥0}
    (hT : ∀ n, IsKernelStop (𝒢.comap Prod.fst) (P.prod P₀) (Prod.fst ⁻¹' F) (fun t p => W t p.1)
      (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) (fun p => V p.1) (σ n))
    (hσm : ∀ p, Monotone fun n => σ n p)
    (hσV : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ F → ∀ n, (σ n p : ℝ≥0∞) < V p.1)
    (hσlim : ∀ᵐ p ∂(P.prod P₀), p.1 ∈ F → Tendsto (fun n => (σ n p : ℝ≥0∞)) atTop (𝓝 (V p.1))) :
    ∀ᵐ p₀ ∂(P.prod P₀), p₀.1 ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × Ω₀))) (W' : ℝ≥0 → Ω × Ω₀ → ℝ)
        (VL' : Fin nL → ℝ≥0 → Ω × Ω₀ → ℝ) (VR' : Fin nR → ℝ≥0 → Ω × Ω₀ → ℝ) (B' : ℝ≥0 → Ω × Ω₀ → ℝ),
        StoppedExtend.IsStoppedHullCoupling κ (ΘL p₀.1) (ΘR p₀.1) ρL ρR
          (condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀) 𝓕' W' VL' VR' B' (fun p => V p.1) (fun p => X p.1) ∧
        (∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ V p.1 →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = VL i t p.1) ∧ ∀ j, VR' j t p = VR j t p.1) ∧
        ∀ᵐ p ∂(condExpKernel (P.prod P₀) (𝒢.comap Prod.fst) p₀), ∀ T : ℝ≥0, (T : ℝ≥0∞) = V p.1 →
          ∀ t : ℝ≥0, T ≤ t → W' t p = W' T p :=
  ae_isStoppedHullCoupling_kk (𝒢 := 𝒢.comap Prod.fst) hE (ae_fst_of_ae (P₀ := P₀) hcont)
    (hX.comp measurable_fst) (ae_fst_of_ae (P₀ := P₀) hV0) (𝓗' := Coupling.filtrationComap 𝓗' measurable_fst)
    (MeasurableSpace.comap_mono h𝒢') (adaptedBefore_fst hW') (fun i => adaptedBefore_fst (hVL' i))
    (fun j => adaptedBefore_fst (hVR' j)) (hasSafeLaw_fst hlaw) (hasSafeMembers_fst hmem) hT hσm hσV hσlim

end K2Prod

end InteractingSLE.Supp8.Q3Stop

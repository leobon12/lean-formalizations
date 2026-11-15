/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovK2
import InteractingSLE.Spec.Restart.StoppedK2Dyadic

/-!
# The stopped K2, part 6: the transfer to the regular conditional law, before the stop

Packet PROVE-STOPPEDK2. The `P`-side inputs of the stopped K2 and their transfer to `ν = condExpKernel P 𝒢 ω₀`:

* `IsRandomWordEvolutionUpTo`: (E-stop), K2's input (E) (`Aux122Disint.IsRandomWordEvolution`) with the integrated
  path replaced by a local one before the stop (`Sec2.IsSLEPathUpTo`);
* `exists_ae_condExpKernel_agree_upTo`: Aux. lemma 122 for it (copy of `DomainMarkov.exists_ae_condExpKernel_agree`
  with `IsSLEPathUpTo`): a local evolution before the stop under almost every conditional law;
* congruence before the stop: `killedDrivingSigma_congr`, `isSLEPathUpTo_congr`, `isDyadicSampled_congr` (processes
  equal before `ζ` have the same killed driving filtration, local path conditions and dyadic protected-kernel law);
* `ae_hasRatMembers_k`: the member identities at rational times under almost every conditional law, for versions
  agreeing with the continuation before the stop (the first half of `DomainMarkov.K2.ae_isLocalSet_k`);
* `isStoppingTime_of_agree`: stopping times of the `P`-side killed driving filtration are, under almost every
  conditional law, stopping times of the killed driving filtration of every version agreeing before the stop.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Restart.StoppedK2

open Sec7.Aux122Disint

/-! ### (E-stop) and its disintegration -/

section Disint

variable {Ω : Type*} {𝓔 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]

/-- **(E-stop): a local evolution of an initially measurable random word before the stop `ζ`** (K2's input (E),
`Aux122Disint.IsRandomWordEvolution`, with the integrated path replaced by `Sec2.IsSLEPathUpTo` before `ζ`). -/
def IsRandomWordEvolutionUpTo (a : ℝ) {nL nR : ℕ} (P : Measure Ω) (𝓔 : MeasurableSpace Ω) (F : Set Ω)
    (ΘL : Ω → Fin nL → ℝ) (ΘR : Ω → Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (𝓕 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  𝓔 ≤ 𝓕 0 ∧ MeasurableSet[𝓔] F ∧ Measurable[𝓔] ΘL ∧ Measurable[𝓔] ΘR ∧
    IsFilteredBrownianReal 𝓕 B P ∧ AdaptedBefore 𝓕 ζ W ∧ (∀ i, AdaptedBefore 𝓕 ζ (VL i)) ∧
      (∀ i, AdaptedBefore 𝓕 ζ (VR i)) ∧
        ∀ᵐ ω ∂P, ω ∈ F → Sec2.IsSLEPathUpTo a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
          (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)

variable [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ}
  {nL nR : ℕ} {F : Set Ω} {ΘL : Ω → Fin nL → ℝ} {ΘR : Ω → Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Aux. lemma 122 before the stop** (`DomainMarkov.exists_ae_condExpKernel_agree` with the local path conditions
`Sec2.IsSLEPathUpTo`, same proof): modified processes, equal to the given ones off a measurable null set `N` on `F`
at every time, form under almost every conditional law a local evolution of the word `(ΘL ω₀, ΘR ω₀)` before `ζ`. -/
theorem exists_ae_condExpKernel_agree_upTo
    (h : IsRandomWordEvolutionUpTo a P 𝓔 F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ) :
    ∃ (N : Set Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
      MeasurableSet N ∧ P N = 0 ∧ (∀ ω, ω ∉ N → ω ∈ F → ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧
        (∀ j, VR' j t ω = VR j t ω) ∧ B' t ω = B t ω) ∧
      ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
        Sec2.IsSLEEvolutionUpTo a (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel P 𝓔 ω₀) 𝓖 W' VL' VR' B' ζ := by
  obtain ⟨h0, hF, hΘL, hΘR, hB, hW, hVL, hVR, hpath⟩ := h
  have hgood : ∀ᵐ ω ∂P, (Continuous (fun t => B t ω) ∧ B 0 ω = 0) ∧
      (ω ∈ F → Sec2.IsSLEPathUpTo a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) :=
    (hB.1.cont.and hB.1.toIsPreBrownianReal.eval_zero_ae_eq_zero).and hpath
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hoff : ∀ ω, ω ∉ N → (Continuous (fun t => B t ω) ∧ B 0 ω = 0) ∧
      (ω ∈ F → Sec2.IsSLEPathUpTo a (ΘL ω) (ΘR ω) ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (fun t => B t ω) (ζ ω)) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  set X := wordData F W VL VR with hX
  have hF𝓕 : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] F := fun t => 𝓕.mono (by positivity) _ (h0 _ hF)
  have hlt : ∀ t : ℝ≥0, MeasurableSet[𝓕 t] {ω | (t : ℝ≥0∞) < ζ ω} := fun t => by
    have := hW t univ MeasurableSet.univ
    simpa using this
  have hkill : ∀ i t, Measurable[𝓕 t] (killAt ζ (X i) t) := by
    rintro (_ | i | j) t
    · exact measurable_killAt_onF hW (hF𝓕 t)
    · exact measurable_killAt_onF (hVL i) (hF𝓕 t)
    · exact measurable_killAt_onF (hVR j) (hF𝓕 t)
  have hS : DisintSetting P 𝓔 𝓕 B N ζ X :=
    ⟨h0, hB, hNm, hN0, fun ω hω => (hoff ω hω).1.1, fun ω hω => (hoff ω hω).1.2, hlt, hkill⟩
  have hXc : ∀ ω, ω ∉ N → ∀ i, ContinuousOn (fun t => X i t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
    intro ω hω i
    by_cases hωF : ω ∈ F
    · have hp := (hoff ω hω).2 hωF
      rcases i with _ | i | j
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.continuousOn_w
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.continuousOn_vL i
      · simp only [hX, wordData, onF_of_mem hωF]
        exact hp.continuousOn_vR j
    · rcases i with _ | i | j <;> simp only [hX, wordData, onF_of_notMem hωF] <;> exact continuousOn_const
  have hle : 𝓔 ≤ mΩ := hS.le_mΩ
  refine ⟨N, dataFilt N ζ B X, zeroOn N (X none), fun i => zeroOn N (X (some (Sum.inl i))),
    fun j => zeroOn N (X (some (Sum.inr j))), zeroOn N B, hNm, hN0, ?_, ?_⟩
  · intro ω hω hωF t
    simp only [zeroOn_of_notMem hω, hX, wordData, onF_of_mem hωF, implies_true, and_self]
  filter_upwards [hS.ae_isFilteredBrownianReal, hS.ae_condExpKernel_N, ae_ae_condExpKernel_mem hle hF,
    ae_ae_condExpKernel_eq hle hΘL, ae_ae_condExpKernel_eq hle hΘR] with ω₀ hBr hνN hmemF hL hR hω₀F
  refine ⟨hBr, hS.dataMeas.adaptedBefore_zeroOn hXc none,
    fun i => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inl i)),
    fun j => hS.dataMeas.adaptedBefore_zeroOn hXc (some (Sum.inr j)), ?_⟩
  filter_upwards [hmemF hω₀F, hL, hR, measure_eq_zero_iff_ae_notMem.1 hνN] with ω hωF hωL hωR hωN
  have hp := (hoff ω hωN).2 hωF
  rw [hωL, hωR] at hp
  have e1 : (fun t => zeroOn N (X none) t ω) = fun t => W t ω := funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e2 : (fun i t => zeroOn N (X (some (Sum.inl i))) t ω) = fun i t => VL i t ω := funext fun i => funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e3 : (fun j t => zeroOn N (X (some (Sum.inr j))) t ω) = fun j t => VR j t ω := funext fun j => funext fun t => by
    simp only [zeroOn_of_notMem hωN, hX, wordData, onF_of_mem hωF]
  have e4 : (fun t => zeroOn N B t ω) = fun t => B t ω := funext fun t => zeroOn_of_notMem hωN t
  rw [e1, e2, e3, e4]
  exact hp


end Disint

/-! ### Congruence before the stop -/

section Congr

open QuantumZipper (fwdHull)
open Coupling DomainMarkov Ito

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {W W' : ℝ≥0 → Ω → ℝ}
  {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- Two families of coordinates agree, at every sample, at every time before `ζ`. -/
def AgreeBefore (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ ω (t : ℝ≥0), (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω ∧ (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω

omit mΩ in
/-- Coordinates agreeing before `ζ` generate the same killed driving σ-algebras. -/
theorem killedDrivingSigma_congr (h : AgreeBefore ζ W VL VR W' VL' VR') (t : ℝ≥0) :
    killedDrivingSigma W' VL' VR' ζ t = killedDrivingSigma W VL VR ζ t := by
  unfold killedDrivingSigma
  congr 1
  ext E
  have key : ∀ (r : ℝ≥0) (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))),
      {ω | (r : ℝ≥0∞) < ζ ω ∧ (W' r ω, fun i => VL' i r ω, fun i => VR' i r ω) ∈ A} =
        {ω | (r : ℝ≥0∞) < ζ ω ∧ (W r ω, fun i => VL i r ω, fun i => VR i r ω) ∈ A} := fun r A => by
    ext ω
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨hr, hA⟩
      obtain ⟨e1, e2, e3⟩ := h ω r hr
      refine ⟨hr, ?_⟩
      rwa [e1, funext e2, funext e3] at hA
    · rintro ⟨hr, hA⟩
      obtain ⟨e1, e2, e3⟩ := h ω r hr
      refine ⟨hr, ?_⟩
      rwa [e1, funext e2, funext e3]
  constructor
  · rintro ⟨r, hr, A, hA, rfl⟩
    exact ⟨r, hr, A, hA, key r A⟩
  · rintro ⟨r, hr, A, hA, rfl⟩
    exact ⟨r, hr, A, hA, (key r A).symm⟩

omit mΩ in
/-- The driver as a real path agrees with another on `[0, q]` when the two agree before `ζ > q`. -/
theorem eqOn_rpath_of_agree {w w' : ℝ≥0 → ℝ} {z : ℝ≥0∞} (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < z → w' t = w t) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < z) : EqOn (fun s : ℝ => w s.toNNReal) (fun s : ℝ => w' s.toNNReal) (Icc 0 (q : ℝ)) :=
  fun s hs => (h _ (lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) hq)).symm

omit mΩ in
theorem couplingMean_congr_Icc {w w' : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t) (h : EqOn w w' (Icc 0 t)) (κ : ℝ)
    (u : ℂ → ℝ) (z : ℂ) : couplingMean κ w t u z = couplingMean κ w' t u z := by
  unfold couplingMean
  rw [Ito.fwdMap_congr_of_eqOn_of_le h le_rfl, Ito.logDerivFwd_congr_of_eqOn h ht le_rfl]

omit mΩ in
theorem loewnerGreenEnergy_congr_Icc {w w' : ℝ → ℝ} {t : ℝ} (h : EqOn w w' (Icc 0 t)) (φ : ℂ → ℝ) :
    loewnerGreenEnergy w t φ = loewnerGreenEnergy w' t φ := by
  unfold loewnerGreenEnergy
  simp only [Ito.fwdMap_congr_of_eqOn_of_le h le_rfl]

omit mΩ in
/-- The avoidance events before `ζ` agree. -/
theorem mem_avoidSet_congr (h : AgreeBefore ζ W VL VR W' VL' VR') (ψ : ℂ → ℝ) (q : ℝ≥0) (ω : Ω) :
    ω ∈ avoidSet W' ζ ψ q ↔ ω ∈ avoidSet W ζ ψ q := by
  simp only [avoidSet, mem_ofPred_eq]
  constructor
  · rintro ⟨hq, hd⟩
    refine ⟨hq, ?_⟩
    rwa [fwdHull_rpath_congr_of_lt (w := (W' · ω)) (w' := (W · ω)) (fun t ht => (h ω t ht).1) hq] at hd
  · rintro ⟨hq, hd⟩
    refine ⟨hq, ?_⟩
    rwa [fwdHull_rpath_congr_of_lt (w := (W' · ω)) (w' := (W · ω)) (fun t ht => (h ω t ht).1) hq]

omit mΩ in
/-- `cfAt` at a time before `ζ` agrees. -/
theorem cfAt_congr_of_agree {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (h : AgreeBefore ζ W VL VR W' VL' VR')
    (ψ : ℂ → ℝ) {q : ℝ≥0} {ω : Ω} (hq : (q : ℝ≥0∞) < ζ ω) :
    cfAt κ W' (bheProc κ ρL ρR W' VL' VR') ψ 1 (fun _ => q) ω =
      cfAt κ W (bheProc κ ρL ρR W VL VR) ψ 1 (fun _ => q) ω := by
  obtain ⟨e1, e2, e3⟩ := h ω q hq
  have hb : bheProc κ ρL ρR W' VL' VR' ω q = bheProc κ ρL ρR W VL VR ω q := by
    simp only [bheProc, e1, e2, e3]
  have hE := eqOn_rpath_of_agree (w := (W · ω)) (w' := (W' · ω)) (fun t ht => (h ω t ht).1) hq
  simp only [cfAt]
  rw [hb, loewnerGreenEnergy_congr_Icc hE]
  congr 4
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [couplingMean_congr_Icc q.coe_nonneg hE]

/-- **The dyadic protected-kernel law only depends on the coordinates before `ζ`.** -/
theorem isDyadicSampled_congr {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {ν : Measure Ω}
    {X : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hX' : IsMeasurableKilledDriving W' VL' VR' ζ) (h : AgreeBefore ζ W VL VR W' VL' VR')
    (hdy : IsDyadicSampled κ W (bheProc κ ρL ρR W VL VR) ν hX X) :
    IsDyadicSampled κ W' (bheProc κ ρL ρR W' VL' VR') ν hX' X := by
  intro ψ n k A hA hAav
  have e : nullAugmented (killedDrivingFiltration hX') ν (dyT n k) =
      nullAugmented (killedDrivingFiltration hX) ν (dyT n k) := by
    rw [Ito.nullAugmented_apply, Ito.nullAugmented_apply]
    congr 1
    exact killedDrivingSigma_congr h _
  have hA' : MeasurableSet[nullAugmented (killedDrivingFiltration hX) ν (dyT n k)] A := e ▸ hA
  have hAm : MeasurableSet A := (nullAugmented (killedDrivingFiltration hX) ν).le _ _ hA'
  rw [hdy ψ n k A hA' fun ω hω => (mem_avoidSet_congr h ψ _ ω).1 (hAav hω)]
  refine setIntegral_congr_fun hAm fun ω hω => ?_
  exact (cfAt_congr_of_agree h ψ (hAav hω).1).symm

end Congr

/-! ### Local path conditions before the stop -/

section PathCongr

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}

/-- **The local path conditions only see the path before `τ`** (and at time `0`, `τ > 0`). -/
theorem isSLEPathUpTo_congr (hτ : 0 < τ) (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w' t = w t)
    (hvL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → ∀ i, vL' i t = vL i t)
    (hvR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → ∀ j, vR' j t = vR j t)
    (h : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) : Sec2.IsSLEPathUpTo a xL xR ρL ρR w' vL' vR' b τ := by
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < τ := by rw [ENNReal.coe_zero]; exact hτ
  have hle : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ s : ℝ, s ∈ uIcc 0 (t : ℝ) → (s.toNNReal : ℝ≥0∞) < τ :=
    fun {t} ht s hs => lt_of_le_of_lt (by
      rw [uIcc_of_le t.coe_nonneg] at hs
      exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2) ht
  have hgapL : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ i, EqOn (fun s : ℝ => (w s.toNNReal - vL i s.toNNReal)⁻¹)
      (fun s : ℝ => (w' s.toNNReal - vL' i s.toNNReal)⁻¹) (uIcc 0 (t : ℝ)) := fun ht i s hs => by
    simp only [hw _ (hle ht s hs), hvL _ (hle ht s hs) i]
  have hgapR : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < τ → ∀ j, EqOn (fun s : ℝ => (w s.toNNReal - vR j s.toNNReal)⁻¹)
      (fun s : ℝ => (w' s.toNNReal - vR' j s.toNNReal)⁻¹) (uIcc 0 (t : ℝ)) := fun ht j s hs => by
    simp only [hw _ (hle ht s hs), hvR _ (hle ht s hs) j]
  refine ⟨by rw [hw 0 h0]; exact h.w_zero, fun i => by rw [hvL 0 h0 i]; exact h.vL_zero i,
    fun j => by rw [hvR 0 h0 j]; exact h.vR_zero j,
    h.continuousOn_w.congr fun t ht => hw t ht, fun i => (h.continuousOn_vL i).congr fun t ht => hvL t ht i,
    fun j => (h.continuousOn_vR j).congr fun t ht => hvR t ht j, fun {t} ht => ?_, fun {t} ht i => ?_,
    fun {t} ht j => ?_, fun {t} ht => ?_, fun {t} ht i => ?_, fun {t} ht j => ?_, fun {t} ht => ?_,
    fun {t} ht i => ?_, fun {t} ht j => ?_, fun i => ?_, fun j => ?_, fun {t} ht => ?_⟩
  · have e : (fun i => vL' i t) = fun i => vL i t := funext (hvL t ht)
    rw [e]; exact h.antitone_vL ht
  · rw [hvL t ht i, hw t ht]; exact h.vL_le_w ht i
  · rw [hvR t ht j, hw t ht]; exact h.w_le_vR ht j
  · have e : (fun j => vR' j t) = fun j => vR j t := funext (hvR t ht)
    rw [e]; exact h.monotone_vR ht
  · exact (h.integrable_gapL ht i).congr fun s hs => hgapL ht i (uIoc_subset_uIcc hs)
  · exact (h.integrable_gapR ht j).congr fun s hs => hgapR ht j (uIoc_subset_uIcc hs)
  · have s1 : (∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal)) =
        ∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w' s.toNNReal - vL' i s.toNNReal) :=
      Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr fun s hs => by
        simp only [hw _ (hle ht s hs), hvL _ (hle ht s hs) i]
    have s2 : (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal)) =
        ∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w' s.toNNReal - vR' j s.toNNReal) :=
      Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr fun s hs => by
        simp only [hw _ (hle ht s hs), hvR _ (hle ht s hs) j]
    rw [hw t ht, h.w_eq ht, s1, s2]
  · rw [hvL t ht i, h.vL_eq ht i]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hw _ (hle ht s hs), hvL _ (hle ht s hs) i]
  · rw [hvR t ht j, h.vR_eq ht j]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [hw _ (hle ht s hs), hvR _ (hle ht s hs) j]
  · refine measure_mono_null (fun s hs => ?_) (h.volume_collisionL i)
    obtain ⟨hs0, hsτ, he⟩ := hs
    exact ⟨hs0, hsτ, by rw [← hw _ hsτ, ← hvL _ hsτ i]; exact he⟩
  · refine measure_mono_null (fun s hs => ?_) (h.volume_collisionR j)
    obtain ⟨hs0, hsτ, he⟩ := hs
    exact ⟨hs0, hsτ, by rw [← hw _ hsτ, ← hvR _ hsτ j]; exact he⟩
  · have eL : (fun i => vL' i t) = fun i => vL i t := funext (hvL t ht)
    have eR : (fun j => vR' j t) = fun j => vR j t := funext (hvR t ht)
    rw [hw t ht, eL, eR]
    exact h.not_threshold ht

end PathCongr

/-! ### The member identities under the conditional law, before the stop -/

section Members

open QuantumZipper (H fwdHull zeroGFFTestCov)
open LQGMetric LQGMetric.MarkovZB LocalSets Coupling Ito Sec7 Sec2.Restart Sec5.Markov LocalExt
open QuantumZipper.K3 QuantumZipper.Thm11Asm DomainMarkov DomainMarkov.K2
open SupercriticalConformalCovariance.GM24 (smoothDist)
open TopologicalSpace
open scoped RealInnerProductSpace

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ} {N F : Set Ω}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {X : Ω → DistOn upperHalfPlaneOpens} {𝓗 : Filtration ℝ≥0 mΩ} {P : Measure Ω}
  [StandardBorelSpace Ω] [IsProbabilityMeasure P]

/-- **The member identities at rational times under almost every conditional law** (the first half of
`DomainMarkov.K2.ae_isLocalSet_k`, same proof): for `P`-almost every `ω₀ ∈ F`, if the field is a Gaussian free field
with harmonic mean `u₀` under `ν = condExpKernel P 𝒢 ω₀`, every version of the modified continuation agreeing with it
`ν`-almost surely before `ζ` has the member identities `HasRatMembers` for the centred field. -/
theorem ae_hasRatMembers_k (h𝒢 : 𝒢 ≤ 𝓗 0) (hF : MeasurableSet[𝒢] F)
    (hW : AdaptedBefore 𝓗 ζ W) (hVL : ∀ i, AdaptedBefore 𝓗 ζ (VL i)) (hVR : ∀ j, AdaptedBefore 𝓗 ζ (VR j))
    (hX : Measurable X) (hNm : MeasurableSet N) (hN0 : P N = 0) (hN : IsKGood N F ζ W VL VR)
    (hmem : HasSafeMembers P 𝓗 F ζ W X) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F → ∀ u₀ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u₀ H →
      IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => X ω φ - ∫ z, u₀ z * φ z) (condExpKernel P 𝒢 ω₀) →
      ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
        (hX' : IsMeasurableKilledDriving W' VL' VR' ζ),
        (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = kW N F W VL VR t ω ∧
          (∀ i, VL' i t ω = kVL N F W VL VR i t ω) ∧ ∀ j, VR' j t ω = kVR N F W VL VR j t ω) →
        HasRatMembers (condExpKernel P 𝒢 ω₀) (killedDrivingFiltration hX') W' ζ
          (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀) := by
  have hF0 : MeasurableSet[𝓗 0] F := h𝒢 _ hF
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hdm := dataMeas_k hNm hF0 hW hVL hVR
  have hVH : ∀ Fb : Finset (ℚ × ℚ × ℚ), ballsK Fb ⊆ H → ((ballsOpen Fb : Opens ℂ) : Set ℂ) ⊆ H :=
    fun Fb hFb z hz => hFb (ballsU_subset_ballsK Fb hz)
  -- Borel versions of the projections onto `H(ballsU Fb)` and Dirichlet approximations, chosen once
  have hGex : ∀ Fb : Finset (ℚ × ℚ × ℚ), ∃ G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens,
      ballsK Fb ⊆ H → Measurable G ∧
        GFF.IsMarkovDecomposition (ballsOpen Fb) upperHalfPlaneOpens id G (zbLaw upperHalfPlaneOpens) := by
    intro Fb
    by_cases hFb : ballsK Fb ⊆ H
    · obtain ⟨G, hGm, hGd⟩ := exists_markovMap_zbLaw (ballsOpen Fb) (hVH Fb hFb)
      exact ⟨G, fun _ => ⟨hGm, hGd⟩⟩
    · exact ⟨id, fun h => absurd h hFb⟩
  choose G hG using hGex
  have hfex : ∀ (Fb : Finset (ℚ × ℚ × ℚ)) (k : RatComb), ∃ f : ℕ → zsSub (ballsU Fb), ballsK Fb ⊆ H →
      Tendsto (fun m => gradFeat (ballsU Fb) (f m).1) atTop
        (𝓝 (covVec (ballsU Fb) (ratComb upperHalfPlaneOpens k))) ∧
      ∀ᵐ g ∂zbLaw upperHalfPlaneOpens,
        Tendsto (fun m => g (lapTest (ballsOpen Fb) (f m))) atTop (𝓝 (G Fb g (ratComb upperHalfPlaneOpens k))) := by
    intro Fb k
    by_cases hFb : ballsK Fb ⊆ H
    · obtain ⟨f, hf1, hf2⟩ := exists_tendsto_ae_zbLaw (hG Fb hFb).1 (hG Fb hFb).2 (hVH Fb hFb)
        (ratComb upperHalfPlaneOpens k)
      exact ⟨f, fun _ => ⟨hf1, hf2⟩⟩
    · exact ⟨fun _ => 0, fun h => absurd h hFb⟩
  choose fam hfam using hfex
  have htr := ae_setIntegral_shift_k h𝒢 hF hW hVL hVR hX hNm hN0 hN hmem fam
  filter_upwards [htr, ae_ae_condExpKernel_mem (P := P) h𝒢m hF] with ω₀ htr0 hmemF hω₀F u₀ hu₀ hp
    W' VL' VR' hX' hagZ
  have hFν : ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ω ∈ F := hmemF hω₀F
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀ z hz).1.continuousAt.continuousWithinAt
  have hlaw := map_eq_fieldLaw0_of_isZBGFFProcess hX hu₀c hp
  have hsm : IsHarmonicDistOn (smoothDist upperHalfPlaneOpens u₀) H := WholeField.isHarmonicDistOn_smoothDist hu₀
  -- the member identities under `ν`
  intro r s hrs Fb hFH
  have hSm : MeasurableSet (safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0)) :=
    (kF N F ζ W VL VR).le _ _ (measurableSet_safeU_indK (adaptedBefore_kW hdm hN)
      (fun ω => (hN.isWeakPath ω).2.1) hFH _)
  refine ⟨safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0), hSm, ?_, fun D hD => ?_⟩
  · filter_upwards [hagZ] with ω hω
    have hw := hN.isWeakPath ω
    refine propext ((mem_safeU_indK_iff hw.2.1 hw.1 hFH _).trans ?_)
    constructor
    · rintro ⟨hlt, hd⟩
      exact ⟨hlt, by rwa [fwdHull_rpath_congr_of_lt (fun t ht => (hω t ht).1) hlt]⟩
    · rintro ⟨hlt, hd⟩
      exact ⟨hlt, by rwa [← fwdHull_rpath_congr_of_lt (fun t ht => (hω t ht).1) hlt]⟩
  · obtain ⟨A', hA', hDA'⟩ := nullAugmented_le_of_agree (adaptedBefore_kW hdm hN) (adaptedBefore_kVL hdm hN)
      (adaptedBefore_kVR hdm hN) hX' hagZ (s : ℝ≥0) _
      (usualAugmentation_le_nullAugmented (killedDrivingFiltration hX') (by exact_mod_cast hrs) _ hD)
    have hpi := isProjIndepMeasure_k_of_shift hdm hN hFν hX hu₀ hlaw hFH (hG Fb hFH).1 (hG Fb hFH).2
      (fam Fb) (fun k => (hfam Fb k hFH).1) (fun k => (hfam Fb k hFH).2) (s : ℝ≥0)
      (fun k m A => htr0 s Fb hFH k m A) hA'
    have hres : (condExpKernel P 𝒢 ω₀).restrict (D ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0)) =
        (condExpKernel P 𝒢 ω₀).restrict (A' ∩ safeU (kW N F W VL VR) ζ univ (indK Fb) (s : ℝ≥0)) :=
      Measure.restrict_congr_set (hDA'.inter (EventuallyEq.refl _ _))
    have ecomp : (fun ω => X ω - smoothDist upperHalfPlaneOpens u₀) =
        (fun x => x - smoothDist upperHalfPlaneOpens u₀) ∘ X := rfl
    rw [hres, ecomp, ← Measure.map_map (measurable_sub_distOnConst _) hX]
    exact IsProjIndepMeasure.map_sub (hVH Fb hFH) hpi hsm

end Members

/-! ### Stopping times of the killed driving filtration under the conditional law -/

section Stop

open Ito Coupling DomainMarkov DomainMarkov.K2

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {P : Measure Ω} [StandardBorelSpace Ω] [IsProbabilityMeasure P]

omit mΩ [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- `σ ≤ t` iff `σ ≤ q` for every rational `q ∈ (t, u)`. -/
theorem setOf_le_eq_iInter (σ : Ω → WithTop ℝ≥0) {t u : ℝ≥0} (htu : t < u) :
    {ω | σ ω ≤ t} = ⋂ q : {q : ℚ // (t : ℝ) < q ∧ (q : ℝ) < u},
      {ω | σ ω ≤ (((q.1 : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} := by
  ext ω
  simp only [mem_ofPred_eq, mem_iInter, Subtype.forall]
  constructor
  · intro h q hq
    refine h.trans (WithTop.coe_le_coe.2 ?_)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (t.coe_nonneg.trans hq.1.le)]
    exact hq.1.le
  · intro h
    by_contra hlt
    push Not at hlt
    have hm : (t : WithTop ℝ≥0) < min (σ ω) (u : WithTop ℝ≥0) := lt_min hlt (WithTop.coe_lt_coe.2 htu)
    obtain ⟨c, hc⟩ : ∃ c : ℝ≥0, (c : WithTop ℝ≥0) = min (σ ω) (u : WithTop ℝ≥0) :=
      WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _))
    rw [← hc, WithTop.coe_lt_coe] at hm
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (t : ℝ) < c from hm)
    have hq0 : (0 : ℝ) ≤ q := t.coe_nonneg.trans hq1.le
    have hcu : (c : ℝ) ≤ u := by
      have : (c : WithTop ℝ≥0) ≤ u := hc ▸ min_le_right _ _
      exact_mod_cast WithTop.coe_le_coe.1 this
    have h1 := h q ⟨hq1, hq2.trans_le hcu⟩
    have h2 : (c : WithTop ℝ≥0) ≤ σ ω := hc ▸ min_le_left _ _
    have h3 := WithTop.coe_le_coe.1 (h2.trans h1)
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0] at h3
    exact absurd h3 (not_le.2 hq2)

/-- **Stopping times transfer to the killed driving filtration of versions.** A stopping time of the `P`-side driving
filtration of `(W, VL, VR)` killed at `ζ` is, for `P`-almost every `ω₀`, a stopping time of the driving filtration under
`ν = condExpKernel P 𝒢 ω₀` of every version agreeing `ν`-almost surely with `(W, VL, VR)` before `ζ` (at rational
times `q < s`, `{σ ≤ q}` is `P`-almost surely an event of the killed filtration at `s`; the countably many null sets are
`ν`-null for almost every `ω₀`; the killed filtrations of agreeing processes agree up to `ν`-null sets). -/
theorem ae_isStoppingTime_of_agree (h𝒢 : 𝒢 ≤ mΩ) (hXP : IsMeasurableKilledDriving W VL VR ζ)
    {σ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime (drivingFiltration P hXP) σ) :
    ∀ᵐ ω₀ ∂P, ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
      (hX' : IsMeasurableKilledDriving W' VL' VR' ζ),
      (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω ∧
        (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) →
      IsStoppingTime (drivingFiltration (condExpKernel P 𝒢 ω₀) hX') σ := by
  set 𝓚 := killedDrivingFiltration hXP with h𝓚
  have hver : ∀ q s : ℚ, ∃ K : Set Ω, (q : ℝ).toNNReal < (s : ℝ).toNNReal →
      MeasurableSet[𝓚 (s : ℝ).toNNReal] K ∧ {ω | σ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[P] K := by
    intro q s
    by_cases hqs : (q : ℝ).toNNReal < (s : ℝ).toNNReal
    · have h1 := usualAugmentation_le_nullAugmented (P := P) 𝓚 hqs _ (hσ (q : ℝ).toNNReal)
      obtain ⟨K, hK, hEK⟩ := exists_ae_eq_of_measurableSet_nullAugmented h1
      exact ⟨K, fun _ => ⟨hK, hEK⟩⟩
    · exact ⟨∅, fun h => absurd h hqs⟩
  choose K hK using hver
  have hall : ∀ᵐ ω₀ ∂P, ∀ q s : ℚ, (q : ℝ).toNNReal < (s : ℝ).toNNReal →
      {ω | σ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[condExpKernel P 𝒢 ω₀] K q s := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun s => ?_
    by_cases hqs : (q : ℝ).toNNReal < (s : ℝ).toNNReal
    · have h := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 (hK q s hqs).2
      filter_upwards [h] with ω₀ hω₀ _ using hω₀
    · exact Eventually.of_forall fun _ h => absurd h hqs
  filter_upwards [hall] with ω₀ hω₀ W' VL' VR' hX' hag
  set ν := condExpKernel P 𝒢 ω₀ with hν
  have hsym : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω = W' t ω ∧
      (∀ i, VL i t ω = VL' i t ω) ∧ ∀ j, VR j t ω = VR' j t ω := by
    filter_upwards [hag] with ω hω t ht
    obtain ⟨e1, e2, e3⟩ := hω t ht
    exact ⟨e1.symm, fun i => (e2 i).symm, fun j => (e3 j).symm⟩
  have hle := fun s => nullAugmented_le_of_agree (adaptedBefore_killedDriving_W hX')
    (fun i => adaptedBefore_killedDriving_VL hX' i) (fun j => adaptedBefore_killedDriving_VR hX' j) hXP hsym s
  intro t
  show MeasurableSet[usualAugmentation (killedDrivingFiltration hX') ν t] _
  rw [usualAugmentation_apply]
  refine MeasurableSpace.measurableSet_iInf.2 fun u => MeasurableSpace.measurableSet_iInf.2 fun htu => ?_
  rw [setOf_le_eq_iInter σ htu]
  refine MeasurableSet.iInter fun q => ?_
  have hq0 : (0 : ℝ) ≤ q.1 := t.coe_nonneg.trans q.2.1.le
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn q.2.2
  have hs0 : (0 : ℝ) ≤ s := hq0.trans hs1.le
  have hqs : (q.1 : ℝ).toNNReal < (s : ℝ).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0, Real.coe_toNNReal _ hs0]; exact hs1
  have hsu : (s : ℝ).toNNReal ≤ u := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs2.le
  obtain ⟨K', hK', hKK'⟩ := hle _ _ (le_nullAugmented 𝓚 ν _ _ (hK q.1 s hqs).1)
  have hEm : MeasurableSet {ω | σ ω ≤ (((q.1 : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} :=
    (drivingFiltration P hXP).le _ _ (hσ _)
  have h1 := Coupling.measurableSet_nullAugmented_of_ae_eq (𝓕 := killedDrivingFiltration hX') (P := ν) hEm hK'
    ((hω₀ q.1 s hqs).trans hKK')
  exact (nullAugmented (killedDrivingFiltration hX') ν).mono hsu _ h1

end Stop

end InteractingSLE.Restart.StoppedK2

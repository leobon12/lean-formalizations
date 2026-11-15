/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtOPiece

/-!
# The restart coupling's locality input: `RestartLocalityInput κ` and `RestartSeedCouplingStatement κ`

Packet PROVE-LOCEXT-O. PROVE-LOCEXT-M reduced Theorem 1.2's restart coupling to `RestartLocalityInput κ`: at every stop
`τ ≤ S₀` of the restarted filtration, the restarted hull is a local set of the recoded restarted field under
`Q = restartQ`. This file proves it for every `κ > 0`:

* `exists_condLocal_history` (the shared core, also for `KernelRestartLocalityStatement`): locality conditional on the
  recorded history at a stopping time `σ < ζ`, with the history (hence any word read from it) in the conditioning
  σ-algebra, under every `P[· | E]`, `E ∈ 𝒜_B ∨ 𝓓_σ`;
* the pieces: `τ₁ = (τ ∧ S₀)` on `D` (`0` off `D`) is finite; with an announcing sequence `ρ_n` of `ζ`, the pieces
  `E_{n,m} = D ∩ {T + τ₁ ≤ ρ_n} ∖ ⋃_{j<n} {T + τ₁ ≤ ρ_j} ∩ {⌊energy⌋ = m}` are events of `𝓓_{(T+τ₁) ∧ ρ_n}` on which
  `exists_condLocal_restart_piece` applies;
* gluing (`isLocalSet_of_pieces`) and the almost sure identification of the hull;
* **`restartLocalityInput`**: `RestartLocalityInput κ` for `κ > 0`;
* **`restartSeedCouplingStatement`**: `RestartSeedCouplingStatement κ` for `κ > 0` (with PROVE-LOCEXT-M's
  `restartSeedCouplingStatement_of_locality`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Function
open QuantumZipper (H fwdHull zeroGFFTestCov)
open scoped ENNReal NNReal

universe u

namespace InteractingSLE

namespace LocalExt

open LQGMetric LocalSets WholeField Sec7 Sec5.Markov Sec2.Restart

/-! ### Generic helpers -/

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open Classical in
/-- A stopping time replaced by `0` off an event of `𝓕₀` is a stopping time. -/
theorem isStoppingTime_piecewise_zero {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ)
    {D : Set Ω} (hD : MeasurableSet[𝓕 0] D) : IsStoppingTime 𝓕 (D.piecewise τ fun _ => 0) := by
  intro t
  have e : {ω | (D.piecewise τ fun _ => 0) ω ≤ (t : WithTop ℝ≥0)} = (D ∩ {ω | τ ω ≤ t}) ∪ Dᶜ := by
    ext ω
    by_cases hω : ω ∈ D
    · simp [hω]
    · simp only [Set.piecewise_eq_of_notMem _ _ _ hω, mem_ofPred_eq, mem_union, mem_inter_iff, hω, false_and,
        mem_compl_iff, not_false_eq_true, or_true, iff_true]
      exact zero_le
  have h0t : (0 : ℝ≥0) ≤ t := zero_le
  rw [e]
  exact ((𝓕.mono h0t _ hD).inter (hτ t)).union (𝓕.mono h0t _ hD).compl

/-- Almost sure statements under `Q[· | E]` hold `Q`-almost surely on `E`. -/
theorem ae_imp_of_ae_cond {Q : Measure Ω} [IsFiniteMeasure Q] {E : Set Ω} (hE : MeasurableSet E) {p : Ω → Prop}
    (h : ∀ᵐ ω ∂(Q[|E]), p ω) : ∀ᵐ ω ∂Q, ω ∈ E → p ω := by
  rw [← ae_restrict_iff' hE]
  rw [ae_iff] at h ⊢
  rw [ProbabilityTheory.cond, Measure.smul_apply, smul_eq_mul] at h
  rcases mul_eq_zero.1 h with h0 | h0
  · exact absurd h0 (ENNReal.inv_ne_zero.2 (measure_ne_top Q E))
  · exact h0

open Classical in
/-- **The pieces.** For a stopping time `σ'`, a monotone sequence of stopping times `ρ_n`, an event `D` and a function
`cb` of `𝓕_{σ'}`, the events `E_{(n,m)} = D ∩ {σ' ≤ ρ_n} ∩ {⌊cb⌋ = m} ∖ ⋃_{j<n} {σ' ≤ ρ_j}` are disjoint, lie in
`𝓕_{σ' ∧ ρ_n}`, and cover the points of `D` with `σ' ≤ ρ_n` for some `n` and `cb ≥ 0`. -/
theorem exists_pieces {𝓕 : Filtration ℝ≥0 mΩ} {σ' : Ω → WithTop ℝ≥0} (hσ' : IsStoppingTime 𝓕 σ')
    {ρ : ℕ → Ω → ℝ≥0} (hρ : ∀ n, IsStoppingTime 𝓕 fun ω => (ρ n ω : WithTop ℝ≥0))
    (hρm : ∀ ω, Monotone fun n => ρ n ω) {D : Set Ω} (hD : MeasurableSet[hσ'.measurableSpace] D) {cb : Ω → ℝ}
    (hcb : Measurable[hσ'.measurableSpace] cb) :
    ∃ E : ℕ → Set Ω, (∀ k, MeasurableSet[(hσ'.min (hρ (Nat.unpair k).1)).measurableSpace] (E k)) ∧
      Pairwise (Disjoint on E) ∧ (∀ k, E k ⊆ D) ∧ (∀ k, ∀ ω ∈ E k, σ' ω ≤ ρ (Nat.unpair k).1 ω) ∧
      (∀ k, ∀ ω ∈ E k, cb ω ≤ (Nat.unpair k).2 + 1) ∧
      ∀ ω ∈ D, (∃ n, σ' ω ≤ ρ n ω) → 0 ≤ cb ω → ∃ k, ω ∈ E k := by
  set F : ℕ → ℕ → Set Ω := fun n m =>
    ((D ∩ {ω | ⌊cb ω⌋₊ = m}) ∩ {ω | σ' ω ≤ ρ n ω}) \ ⋃ j ∈ Finset.range n, {ω | σ' ω ≤ ρ j ω} with hFdef
  refine ⟨fun k => F (Nat.unpair k).1 (Nat.unpair k).2, fun k => ?_, ?_, fun k ω hω => hω.1.1.1, fun k ω hω => hω.1.2,
    fun k ω hω => ?_, ?_⟩
  · set n := (Nat.unpair k).1
    set m := (Nat.unpair k).2
    have hDm : MeasurableSet[hσ'.measurableSpace] (D ∩ {ω | ⌊cb ω⌋₊ = m}) :=
      hD.inter ((Nat.measurable_floor (R := ℝ)).comp hcb (measurableSet_singleton m))
    have h1 := IsStoppingTime.measurableSet_inter_le hσ' (hρ n) _ hDm
    refine h1.diff (MeasurableSet.biUnion (Finset.range n).countable_toSet fun j hj => ?_)
    have h2 := IsStoppingTime.measurableSet_inter_le hσ' (hρ j) univ MeasurableSet.univ
    rw [univ_inter] at h2
    have hjn : j ≤ n := (Finset.mem_range.1 hj).le
    exact IsStoppingTime.measurableSpace_mono _ _ (fun ω => min_le_min le_rfl (WithTop.coe_le_coe.2 (hρm ω hjn))) _ h2
  · intro k k' hkk'
    refine Set.disjoint_left.2 fun ω hω hω' => hkk' ?_
    rw [← Nat.pair_unpair k, ← Nat.pair_unpair k']
    have hm : (Nat.unpair k).2 = (Nat.unpair k').2 := hω.1.1.2.symm.trans hω'.1.1.2
    have hn : (Nat.unpair k).1 = (Nat.unpair k').1 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact hω'.2 (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hlt)) hω.1.2)
      · exact hω.2 (mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hlt)) hω'.1.2)
    rw [hn, hm]
  · have h1 := (Nat.lt_floor_add_one (cb ω)).le
    rw [hω.1.1.2] at h1
    exact_mod_cast h1
  · intro ω hωD hex hcb0
    refine ⟨Nat.pair (Nat.find hex) ⌊cb ω⌋₊, ?_⟩
    simp only [Nat.unpair_pair]
    refine ⟨⟨⟨hωD, rfl⟩, Nat.find_spec hex⟩, ?_⟩
    simp only [mem_iUnion, Finset.mem_range, mem_ofPred_eq, not_exists]
    exact fun j hj hle => Nat.find_min hex hj hle

end Helpers

/-! ### The energy of the source of a word -/

section Energy

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {r : ℝ}

/-- The energy bound `covBound` of the source test functions of a word is a Borel function of the word. -/
theorem measurable_covBound_srcTestW :
    Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => covBound (srcTestW κ ρL ρR r x) := by
  have hψ : ∀ z, Measurable fun x : (Fin nL → ℝ) × (Fin nR → ℝ) => srcTestW κ ρL ρR r x 0 z := fun z => by
    have h := (measurable_srcTestW_apply κ ρL ρR r 0).comp
      ((measurable_id (α := (Fin nL → ℝ) × (Fin nR → ℝ))).prodMk (measurable_const (a := z)))
    exact h
  have hcov := measurable_zeroGFFTestCov_random (Ω := (Fin nL → ℝ) × (Fin nR → ℝ)) (U := fun _ => H)
    (fun _ => ⟨QuantumZipper.isOpen_H, subset_rfl⟩) (fun j => MeasurableSet.const _) hψ hψ
  exact (hcov.sqrt).add_const 1

end Energy

/-! ### Locality conditional on the history at a stopping time -/

section Core

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Locality conditional on the history at a stopping time, with the history in the σ-algebra** (Aux. lemma 53's
locality half; specification p. 245, "History marking permits retention of the canonical germ of `K_τ` … independent
of the germ conditionally on the history"). For a frozen coupling (`κ > 0`) and a stopping time `σ < ζ` of its driving
filtration `𝓓`, there are a hitting-measurable, relatively closed version `B` of `K_σ` and a germ-measurable `h₁`,
harmonic off `B`, such that under every `P[· | E]`, `E ∈ 𝒢 = 𝒜_B ∨ 𝓓_σ` of positive probability, the centred field minus
`h₁` is conditionally a zero-boundary GFF on `ℍ ∖ B` given `𝒢`. The σ-algebra `𝒢` contains `𝓓_σ`, hence the recorded
history at `σ` and at every earlier stop (and any word read from it): this is the form used at a restart
(`exists_condDecomp_restart_piece`) and the one `KernelRestartLocalityStatement` needs. -/
theorem exists_condLocal_history (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX) σ) (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω) :
    ∃ (Bv : Ω → Set ℂ) (h₁ : Ω → DistOn upperHalfPlaneOpens), Measurable[mΩ, hittingSigma] Bv ∧
      (∀ ω, Bv ω ⊆ H ∧ IsOpen (H \ Bv ω)) ∧
      (∀ᵐ ω ∂P, Bv ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
      Measurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR))] h₁ ∧
      (∀ᵐ ω ∂P, IsHarmonicDistOn (h₁ ω) (H \ Bv ω)) ∧
      ∀ E : Set Ω, MeasurableSet[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace] E →
        P E ≠ 0 → IsCondZeroBoundaryGFF (P[|E])
          (germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace) (fun ω => H \ Bv ω)
          (fun ω => centredField h (bheAt κ ρL ρR xL xR) ω - h₁ ω) := by
  have hpath : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 := by
    filter_upwards [hC.1.2.2.2.2] with ω hp using ⟨hp.2.2.2.1, hp.1⟩
  obtain ⟨A₀, hA₀m, hA₀K, -⟩ := Coupling.exists_hittingVersion_hull hX hpath hσ hσζ
  have hσζ' : ∀ᵐ ω ∂P, (((σ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω :=
    hσζ.mono fun ω h => Coupling.coe_untopD_lt_zeta h
  obtain ⟨Bv, hBm, hBc, hBK⟩ : ∃ Bv : Ω → Set ℂ, Measurable[mΩ, hittingSigma] Bv ∧
      (∀ ω, Bv ω ⊆ H ∧ IsOpen (H \ Bv ω)) ∧
      ∀ᵐ ω ∂P, Bv ω = fwdHull (fun s : ℝ => W s.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) := by
    refine ⟨fun ω => relClosureH (A₀ ω), measurable_relClosureH.comp hA₀m,
      fun ω => ⟨relClosureH_subset _, isOpen_H_diff_relClosureH _⟩, ?_⟩
    filter_upwards [hA₀K, Coupling.ae_hull_subset_isOpen (hpath.mono fun ω h => h.1) hσζ'] with ω h1 h2
    rw [h1]
    exact relClosureH_eq h2.1 h2.2
  have hu₀ := isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  have hloc := isHistoryAvoidanceLocal_hull hC hκ hu₀ hX hσ hσζ hBm hBK
  have hh0 := isZeroBoundaryGFF_centredField hC hu₀
  have hh0m := measurable_centredField hC.2.1 (bheAt κ ρL ρR xL xR)
  obtain ⟨h₁, hh₁, hharm, hcond⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh0 hBm hσ.measurableSpace_le hloc (ae_of_all _ hBc)
  have h𝒢 : germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace ≤ mΩ :=
    sup_le (germSigma_le hBm hh0m) hσ.measurableSpace_le
  have hh₁m : Measurable h₁ := hh₁.mono (germSigma_le hBm hh0m) le_rfl
  have hXm : Measurable fun ω => centredField h (bheAt κ ρL ρR xL xR) ω - h₁ ω :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hh0m).sub ((measurable_distOn_apply φ).comp hh₁m)
  refine ⟨Bv, h₁, hBm, hBc, hBK, hh₁, hharm, fun E hE hPE φ => ?_⟩
  have hcov : Measurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace]
      fun ω => zeroGFFTestCov (H \ relClosureH (Bv ω)) φ φ :=
    (measurable_comap_zeroGFFTestCov_compl Bv φ φ).mono
      ((comap_le_germSigma Bv (centredField h (bheAt κ ρL ρR xL xR))).trans le_sup_left) le_rfl
  have hc'm : StronglyMeasurable[germSigma Bv (centredField h (bheAt κ ρL ρR xL xR)) ⊔ hσ.measurableSpace]
      fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (Bv ω)) φ φ) : ℝ) : ℂ) :=
    (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
  have hcB : ∀ ω, ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (Bv ω)) φ φ) : ℝ) : ℂ) =
      ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ Bv ω) φ φ) : ℝ) : ℂ) := fun ω => by
    rw [relClosureH_eq (hBc ω).1 (hBc ω).2]
  have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ Bv ω) φ φ) : ℝ) : ℂ)) =ᵐ[P]
      fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (Bv ω)) φ φ) : ℝ) : ℂ) :=
    Eventually.of_forall fun ω => (hcB ω).symm
  have hc'i : Integrable (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (Bv ω)) φ φ) : ℝ) : ℂ))
      P := (integrable_condExp.congr (hcond φ)).congr hcc'
  have hXi : Integrable (fun ω => Complex.exp (Complex.I *
      (((centredField h (bheAt κ ρL ρR xL xR) ω - h₁ ω) φ : ℝ) : ℂ))) P :=
    GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hXm)
  have key := condExp_cond_ae_eq le_rfl h𝒢 hE hPE hXi hc'm hc'i ((hcond φ).trans hcc')
  exact key.trans (Eventually.of_forall fun ω => hcB ω)

end Core

/-! ### Gluing the pieces of a restart -/

section Restart

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens} {G : Set Ω} {T : Ω → ℝ≥0}
  {SL : Finset (Fin nL)} {SR : Finset (Fin nR)} {r : ℝ} {D : Set Ω}

/-- **Locality of the restarted hull under `Q` at a finite restarted stop `τ₁ ≤ S₀`.** For the data of
`RestartLocalityInput` and a stop `τ₁` of the restarted filtration, finite everywhere and at most the capped local stop on
the cell, the restarted hull (read from the stopped restarted history) is a local set of the recoded restarted field
under `Q = restartQ`. -/
theorem isLocalSet_restart_tsHull (hκ : 0 < κ) (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hD : MeasurableSet[hT.measurableSpace] D) (hPD : P D ≠ 0) (hDp : IsRestartCell W VL VR ζ G T SL SR r D)
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ ω, IsIntegratedSLEPath κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (fun t => B t ω) (ζ ω) → (T ω : ℝ≥0∞) < ζ ω →
        K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (hτfin : ∀ ω, τ ω ≠ ⊤) (hτD : ∀ ω ∈ D, τ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω) :
    IsLocalSet (fun ω => tsHull (restartHist ζ W T τ ω)) (fun ω => restartRecode κ ρL ρR r (h ω, K ω))
      (restartQ κ ρL ρR r P D K h) := by
  classical
  have hrc : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → ∀ t, MeasurableSet[drivingFiltration P hX t] s :=
    fun s hs h0 t => Ito.measurableSet_usualAugmentation_of_null hs h0 t
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  have hcf := isCouplingCharFun_restartWord hC hκ hX hT hG hD hPD hDp hKm hK
  have hhK := measurable_restartField_word hC hX hT hKm
  have hcw0 := measurable_restartWord_zero (r := r) hX hT hKm
  have hadm : ∀ ω, IsAdmWord r (restartWord r K ω) := isAdmWord_restartWord hPD hDp
  have hgood := ae_isWordPath_restart hX hT hG hD hDp hK
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hQprob : IsProbabilityMeasure (restartQ κ ρL ρR r P D K h) :=
    isProbabilityMeasure_wordMeasure hcf hhK hcw0 hadm hgood
  have hQac : restartQ κ ρL ρR r P D K h ≪ P[|D] := withDensity_absolutelyContinuous _ _
  have hDac : P[|D] ≪ P := cond_absolutelyContinuous
  -- the seed is admissible (the cell is not null)
  have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := by
    intro hth
    obtain ⟨ω, hω⟩ := nonempty_of_measure_ne_zero hPD
    obtain ⟨hωG, hTζ, -⟩ := hDp ω hω
    have h0 := WangWu.IsIntegratedSLEPath.lifetime_eq_zero_of_threshold (hG ω hωG).1 hth
    rw [h0] at hTζ
    exact ENNReal.not_lt_zero hTζ
  obtain ⟨ρ, hρ, -⟩ := hC.1.exists_isAnnouncingSeq_drivingFiltration hκ hseed hX
  -- the restart time `σ' = T + τ` and the pieces
  have hσ' := isStoppingTime_restartTime hT hnull hτ (ae_of_all _ hτfin)
  have hTσ' : (fun ω => ((T ω : ℝ≥0) : WithTop ℝ≥0)) ≤ restartTime T τ := fun ω =>
    WithTop.coe_le_coe.2 le_self_add
  have hTle := IsStoppingTime.measurableSpace_mono hT hσ' hTσ'
  have hcbm : Measurable[hσ'.measurableSpace] fun ω => covBound (srcTestW κ ρL ρR r (restartWord r K ω)) :=
    (measurable_covBound_srcTestW.comp (measurable_restartWord (m := hT.measurableSpace) r hKm)).mono hTle le_rfl
  obtain ⟨E, hEm, hdisj, hED, hEρ, hEC, hcov⟩ := exists_pieces hσ' hρ.1 hρ.2.1 (hTle _ hD) hcbm
  have hEm' : ∀ k, MeasurableSet (E k) := fun k => (hσ'.min (hρ.1 (Nat.unpair k).1)).measurableSpace_le _ (hEm k)
  have hK''m : Measurable[mΩ, hittingSigma] fun ω => tsHull (restartHist ζ W T τ ω) :=
    (measurable_tsHull_comp (measurable_restartHist hX hT hτ hτfin)).mono hτ.measurableSpace_le le_rfl
  -- the data of each piece
  have hdata : ∀ k, ∃ (𝒢 : MeasurableSpace Ω) (h₁ : Ω → DistOn upperHalfPlaneOpens), 𝒢 ≤ mΩ ∧
      MeasurableSet[𝒢] (E k) ∧
      (∃ A : Ω → Set ℂ, Measurable[𝒢, hittingSigma] A ∧ ∀ ω ∈ E k, A ω = tsHull (restartHist ζ W T τ ω)) ∧
      Measurable[𝒢] h₁ ∧
      (restartQ κ ρL ρR r P D K h (E k) ≠ 0 →
        (∀ᵐ ω ∂((restartQ κ ρL ρR r P D K h)[|E k]),
          IsHarmonicDistOn (h₁ ω) (H \ tsHull (restartHist ζ W T τ ω))) ∧
        @IsCondZeroBoundaryGFF Ω mΩ ((restartQ κ ρL ρR r P D K h)[|E k]) 𝒢
          (fun ω => H \ tsHull (restartHist ζ W T τ ω)) (fun ω => restartRecode κ ρL ρR r (h ω, K ω) - h₁ ω)) := by
    intro k
    by_cases hQk : restartQ κ ρL ρR r P D K h (E k) = 0
    · exact ⟨mΩ, 0, le_rfl, hEm' k, ⟨_, hK''m, fun _ _ => rfl⟩, measurable_const, fun hne => absurd hQk hne⟩
    · have hσnζ : ∀ᵐ ω ∂P, ((min (restartTime T τ ω) ((ρ (Nat.unpair k).1 ω : ℝ≥0) : WithTop ℝ≥0) :
          WithTop ℝ≥0) : ℝ≥0∞) < ζ ω := by
        filter_upwards [hρ.2.2.1 (Nat.unpair k).1] with ω hω
        exact lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hω
      have hEσ : ∀ ω ∈ E k, min (restartTime T τ ω) ((ρ (Nat.unpair k).1 ω : ℝ≥0) : WithTop ℝ≥0) =
          restartTime T τ ω := fun ω hω => min_eq_left (hEρ k ω hω)
      obtain ⟨𝒢, h₁, h𝒢, hE𝒢, hA, hh₁, hharm, hcond⟩ := exists_condLocal_restart_piece hκ hC hX hT hG hD hPD hDp
        hKm hK hτ hτfin hτD (hσ'.min (hρ.1 (Nat.unpair k).1)) hσnζ (hEm k) (hED k) hEσ (C := (Nat.unpair k).2 + 1)
        (hEC k) hQk
      exact ⟨𝒢, h₁, h𝒢, hE𝒢, hA, hh₁, fun _ => ⟨hharm, hcond⟩⟩
  choose 𝒢s h₁s h𝒢s hE𝒢s hAs hh₁s hpieces using hdata
  -- the pieces cover `Q`-almost everything
  have hτlt : ∀ ω ∈ D, (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω := fun ω hω => by
    obtain ⟨hωG, hTζ, -, -, hrad⟩ := hDp ω hω
    have h1 := capStop_restart_lt (hG ω hωG) hTζ hωG hrad
    have h2 := hτD ω hω
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (hτfin ω)
    rw [← hv, WithTop.untopD_coe]
    rw [← hv] at h2
    exact lt_of_le_of_lt (by exact_mod_cast h2) h1
  have hcovQ : restartQ κ ρL ρR r P D K h (⋃ k, E k)ᶜ = 0 := by
    refine hQac (ae_iff.1 ?_)
    filter_upwards [ae_cond_mem hDm, hDac.ae_le hρ.2.2.2] with ω hωD hann
    obtain ⟨k, hk⟩ := hcov ω hωD (hann _ ((coe_lt_sub_iff _ _).1 (hτlt ω hωD)) |>.imp fun n hn => by
      rw [restartTime]
      exact WithTop.coe_le_coe.2 hn) (covBound_pos).le
    exact mem_iUnion.2 ⟨k, hk⟩
  have hK''m' : Measurable[pieceSigma hE𝒢s, hittingSigma] fun ω => tsHull (restartHist ζ W T τ ω) :=
    @measurable_pieceSigma_of_eqOn Ω mΩ E 𝒢s (Set ℂ) hittingSigma hE𝒢s _ hK''m _ (fun k => (hAs k).choose_spec.1)
      (fun k ω hω => ((hAs k).choose_spec.2 ω hω).symm)
  have hh : Measurable fun ω => restartRecode κ ρL ρR r (h ω, K ω) := by
    have h1 := (measurable_restartRecode (nL := nL) (nR := nR) κ ρL ρR r).comp
      (hC.2.1.prodMk (hKm.mono hT.measurableSpace_le le_rfl))
    exact h1
  have hh₁ := measurable_pieceGlue hE𝒢s h𝒢s hdisj hh₁s 0
  have hharmk : ∀ k, ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), ω ∈ E k →
      IsHarmonicDistOn (pieceGlue E h₁s 0 ω) (H \ tsHull (restartHist ζ W T τ ω)) := by
    intro k
    by_cases hQk : restartQ κ ρL ρR r P D K h (E k) = 0
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hQk] with ω hω h' using absurd h' hω
    · filter_upwards [ae_imp_of_ae_cond (hEm' k) (hpieces k hQk).1] with ω hω hωE
      rw [pieceGlue_of_mem hdisj h₁s 0 hωE]
      exact hω hωE
  have hharm : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h),
      IsHarmonicDistOn (pieceGlue E h₁s 0 ω) (H \ tsHull (restartHist ζ W T τ ω)) := by
    have hU : ∀ᵐ ω ∂(restartQ κ ρL ρR r P D K h), ω ∈ ⋃ k, E k := by
      rw [ae_iff]
      exact hcovQ
    filter_upwards [hU, ae_all_iff.2 hharmk] with ω hω hk
    obtain ⟨k, hωk⟩ := mem_iUnion.1 hω
    exact hk k hωk
  refine isLocalSet_of_pieces (Q := restartQ κ ρL ρR r P D K h) hE𝒢s h𝒢s hdisj hcovQ hK''m'
    (fun ω => tsHull_relClosed _) hh hh₁ hharm fun k hQk => ?_
  refine IsCondZeroBoundaryGFF.congr_ae (hpieces k hQk).2 (ae_of_all _ fun _ => rfl) ?_
  filter_upwards [ae_cond_mem (hEm' k)] with ω hω
  rw [pieceGlue_of_mem hdisj h₁s 0 hω]

end Restart

/-! ### The restart coupling's locality input -/

section Main

/-- **`RestartLocalityInput κ` for every `κ > 0`** (Aux. lemma 55, step 5, at a restart; Aux. lemma 53's locality
conditionally on the recorded history, specification pp. 245, 250). At every stop `τ ≤ S₀` of the restarted filtration
(`Q`-almost surely), the restarted hull is a local set of the recoded restarted field under `Q = restartQ`.

Proof: replace `τ` by `τ₁ = τ ∧ S₀` on the cell `D` and `0` off it (a finite stop of the restarted filtration, equal to `τ`
`Q`-almost surely), apply `isLocalSet_restart_tsHull`, and identify the hull read from the stopped restarted history with
the hull of `r0W` at `τ` (`tsHull_restartHist`). -/
theorem restartLocalityInput {κ : ℝ} (hκ : 0 < κ) : RestartLocalityInput.{u} κ := by
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX T hT G hGm hG0 hG SL SR r hSL hSR D hD hPD hDp K hKm hK
    τ hτ hτS
  classical
  have hS₀ := isStoppingTime_capStop_restart hX hT hGm hG0 hG r
  have hD0 : MeasurableSet[restartFiltration (drivingFiltration P hX) T hT 0] D := by
    rw [restartFiltration_zero]; exact hD
  obtain ⟨τ₁, hτ₁def⟩ : ∃ τ₁ : Ω → WithTop ℝ≥0,
      τ₁ = D.piecewise (fun ω => min (τ ω) (capStop r G (restartLife ζ T) (restartDrv W T) ω)) fun _ => 0 :=
    ⟨_, rfl⟩
  have hτ₁ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ₁ := by
    rw [hτ₁def]; exact isStoppingTime_piecewise_zero (hτ.min hS₀) hD0
  have hτ₁fin : ∀ ω, τ₁ ω ≠ ⊤ := fun ω => by
    rw [hτ₁def]
    by_cases hω : ω ∈ D
    · rw [Set.piecewise_eq_of_mem _ _ _ hω]
      exact ne_top_of_le_ne_top (capStop_restart_ne_top ω) (min_le_right _ _)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω]
      exact WithTop.zero_ne_top
  have hτ₁D : ∀ ω ∈ D, τ₁ ω ≤ capStop r G (restartLife ζ T) (restartDrv W T) ω := fun ω hω => by
    rw [hτ₁def, Set.piecewise_eq_of_mem _ _ _ hω]
    exact min_le_right _ _
  have hloc := isLocalSet_restart_tsHull hκ hC hX hT hG hD hPD hDp hKm hK hτ₁ hτ₁fin hτ₁D
  have hQac : restartQ κ ρL ρR r P D K h ≪ P[|D] := withDensity_absolutelyContinuous _ _
  have hDac : P[|D] ≪ P := cond_absolutelyContinuous
  have hDm : MeasurableSet D := hT.measurableSpace_le _ hD
  refine Coupling.IsLocalSet.congr_set hloc ?_
  filter_upwards [hτS, hQac.ae_le (ae_cond_mem hDm), (hQac.trans hDac).ae_le hC.1.2.2.2.2] with ω hτω hωD hp
  obtain ⟨hωG, hTζ, -, -, hrad⟩ := hDp ω hωD
  have hτeq : τ₁ ω = τ ω := by
    rw [hτ₁def, Set.piecewise_eq_of_mem _ _ _ hωD]
    exact min_eq_left hτω
  have hlt : (((τ₁ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < restartLife ζ T ω := by
    have h1 := capStop_restart_lt (hG ω hωG) hTζ hωG hrad
    have h2 := hτ₁D ω hωD
    obtain ⟨v, hv⟩ := WithTop.ne_top_iff_exists.1 (hτ₁fin ω)
    rw [← hv, WithTop.untopD_coe]
    rw [← hv] at h2
    exact lt_of_le_of_lt (by exact_mod_cast h2) h1
  have hr0 : (fun s : ℝ => r0W G W T s.toNNReal ω) = fun s : ℝ => restartDrv W T s.toNNReal ω := by
    funext s
    simp only [r0W, hωG, ↓reduceIte]
  rw [hr0, ← hτeq]
  exact (tsHull_restartHist hp.2.2.2.1 hlt).symm

/-- **Theorem 1.2's restart coupling for every `κ > 0`**: `RestartSeedCouplingStatement κ` (PROVE-LOCEXT-M's
`restartSeedCouplingStatement_of_locality` with `restartLocalityInput`). -/
theorem restartSeedCouplingStatement {κ : ℝ} (hκ : 0 < κ) : RestartSeedCouplingStatement.{u} κ :=
  restartSeedCouplingStatement_of_locality hκ (restartLocalityInput hκ)

end Main


end LocalExt

end InteractingSLE

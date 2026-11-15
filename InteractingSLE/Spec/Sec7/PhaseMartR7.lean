/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseMartMeans
import InteractingSLE.Spec.Sec7.PhaseSideR7

/-!
# Aux. lemma 122 with a nonzero phase, part 4: the phase at time zero, and R.7's retained hypothesis (M)

Packet PROVE-PHASEMART (follow-up 5 §3.2, `source/external/AstraIG1/ig1_followup5.txt` L456–L475: "The adopted mean
continuity and the continuous Loewner coordinates make the quotient in (3.2) continuous in positive time. It is
lattice-valued, hence constant on the positive lifetime. […] Right continuity of the retained filtration makes this
constant measurable at time zero."; specification Aux. lemma 122, pp. 389–391).

* **`measurable_zero_of_adaptedBefore_const`**: a phase adapted before the lifetime and constant on the positive
  lifetime has a value measurable at time zero, in a right-continuous filtration (the last sentence quoted above);
* **`twoSeedPhaseMeans_of_phaseCharFun`**: PROVE-PHASE's retained hypothesis (M) on one two-seed R.7 pocket test
  (`PhaseSide.TwoSeedPhaseMeans`), for the phase `n · 2πχ` with an integer `n` measurable at time zero, from the
  conditional-law clause of the phase-shifted two-seed word on the test event (`IsPhaseCouplingCharFun`);
* **`twoSeedPhaseMeans_of_phaseCharFun_adapted`**: the same for any phase adapted before the lifetime and constant on
  the positive lifetime with lattice values.

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseMart

open MartChar Coupling PocketTraversal PocketMartLife PhaseSel PocketPhaseMeans Lemma71C

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### A phase constant on the positive lifetime is measurable at time zero -/

section Zero

/-- **A phase adapted before the lifetime and constant on the positive lifetime has a value measurable at time zero**,
in a right-continuous filtration, when the lifetime is positive (follow-up 5 §3.2: "Right continuity of the retained
filtration makes this constant measurable at time zero"). The preimage of a Borel set is the union over `k` of the
events `{j/(k+1) < T, d_{j/(k+1)} ∈ B}`, measurable at time `j`, for every `j > 0`. -/
theorem measurable_zero_of_adaptedBefore_const {𝓖 : Filtration ℝ≥0 mΩ} [𝓖.IsRightContinuous] {T : Ω → ℝ≥0∞}
    (hT0 : ∀ ω, 0 < T ω) {d : ℝ≥0 → Ω → ℝ} (hda : AdaptedBefore 𝓖 T d) {c : Ω → ℝ}
    (hdc : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < T ω → d t ω = c ω) : Measurable[𝓖 0] c := by
  intro B hB
  refine measurableSet_zero_of_forall_pos fun j hj => ?_
  have hpos : ∀ k : ℕ, 0 < j / ((k : ℝ≥0) + 1) := fun k => div_pos hj (by positivity)
  have e : c ⁻¹' B = ⋃ k : ℕ, {ω | ((j / ((k : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) < T ω ∧ d (j / ((k : ℝ≥0) + 1)) ω ∈ B} := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq]
    constructor
    · intro hω
      obtain ⟨ε, hε0, hεT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hT0 ω)
      have hε : 0 < ε := ENNReal.coe_pos.1 hε0
      obtain ⟨k, hk⟩ := exists_nat_gt ((j : ℝ) / ε)
      have hlt : j / ((k : ℝ≥0) + 1) < ε := by
        rw [← NNReal.coe_lt_coe, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one,
          div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by exact_mod_cast hε)] at hk
        have : (0 : ℝ) ≤ ε := ε.coe_nonneg
        nlinarith
      have hT : ((j / ((k : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) < T ω := lt_trans (ENNReal.coe_lt_coe.2 hlt) hεT
      refine ⟨k, hT, ?_⟩
      rw [hdc ω _ (hpos k) hT]
      exact hω
    · rintro ⟨k, hT, hB'⟩
      rwa [hdc ω _ (hpos k) hT] at hB'
  rw [e]
  refine MeasurableSet.iUnion fun k => 𝓖.mono ?_ _ (hda _ B hB)
  exact div_le_self zero_le (le_add_of_nonneg_left zero_le)

end Zero

/-! ### R.7's retained hypothesis (M) on one two-seed pocket test -/

section R7

open scoped Classical in
/-- The lattice phase `n · 2πχ` of an integer on the test event `A`, extended by `0` off `A`. -/
def latticePhase (κ : ℝ) {A : Set Ω} (n : A → ℤ) : ℝ≥0 → Ω → ℝ :=
  fun _ ω => if hω : ω ∈ A then (n ⟨ω, hω⟩ : ℝ) * phaseStep κ else 0

theorem latticePhase_of_mem (κ : ℝ) {A : Set Ω} (n : A → ℤ) (t : ℝ≥0) (ω : A) :
    latticePhase κ n t ω = (n ω : ℝ) * phaseStep κ := by
  unfold latticePhase
  simp only [ω.2, ↓reduceDIte]

/-- **R.7's retained hypothesis (M) on one two-seed pocket test, for a nonzero lattice phase** (specification
p. 389; follow-up 5 §3.2): on a measurable test event `A` of positive probability on which the traversal `γ` is a
driven curve with points of `ℍ` of arbitrarily large modulus, let `𝓕` be a right-continuous filtration on `A` (a
subtype, under `condSub P A`) containing the null sets at time zero, in which the filled prefixes are adapted, and
`n` an integer measurable at time zero. If a random distribution `h` on `A` with integrable pairings satisfies the
conditional-law clause of the two-seed word `(r_L; r_R)` with the exposed interval raised by `n · 2πχ`, at the seeds'
geometric images along the canonical driver, with the relative lifetime (`IsPhaseCouplingCharFun`), then
`PhaseSide.TwoSeedPhaseMeans` holds for the phase `n · 2πχ`. -/
theorem twoSeedPhaseMeans_of_phaseCharFun {P : Measure Ω} [IsProbabilityMeasure P] {κ rL rR : ℝ} (hκ : 0 < κ)
    {A : Set Ω} (hA : MeasurableSet A) (hPA : P A ≠ 0) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace A)) [𝓕.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → condSub P A s = 0 → MeasurableSet[𝓕 0] s)
    (hpre : IsPrefixAdapted 𝓕 (fun ω : A => γ ω)) {h : A → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) (condSub P A))
    {n : A → ℤ} (hn : Measurable[𝓕 0] n)
    (hcf : IsPhaseCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (condSub P A) 𝓕
      (fun t (ω : A) => segDriver (γ ω) t) (geomLW (fun t (ω : A) => segDriver (γ ω) t) (fun _ => LP.twoSeedXL))
      (geomRW (fun t (ω : A) => segDriver (γ ω) t) (fun _ => LP.twoSeedXR)) (fun _ ω => (n ω : ℝ) * phaseStep κ)
      (fun ω : A => capLife (γ ω)) h) :
    PhaseSide.TwoSeedPhaseMeans κ rL rR P A γ (latticePhase κ n) := by
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA hPA
  have hγA : ∀ ω : A, IsDrivenCurve (γ ω) := fun ω => (hγ ω ω.2).1
  have hcm : Measurable[𝓕 0] fun ω : A => (n ω : ℝ) * phaseStep κ :=
    (Measurable.of_discrete (f := fun m : ℤ => (m : ℝ) * phaseStep κ)).comp hn
  refine ⟨fun ω hω t _ _ => ⟨n ⟨ω, hω⟩, latticePhase_of_mem κ n t ⟨ω, hω⟩⟩, 𝓕, inferInstance, hpre, ?_⟩
  exact hasPhaseMeansBefore_of_phaseCharFun (P := condSub P A) (𝓖 := 𝓕) (W := fun t (ω : A) => segDriver (γ ω) t)
    (T := fun ω : A => capLife (γ ω)) (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) hκ hnull
    (fun ω => (hγA ω).segDriver_spec.1) (fun ω => capLife_pos (hγA ω)) (fun ω => (hγA ω).segDriver_spec.2.1)
    (adaptedBefore_segDriver_of_isDrivenCurve hγA hpre)
    (Eventually.of_forall fun ω hfin C => PocketLife.exists_lt_abs_segDriver (hγA ω) (hγ ω ω.2).2 hfin C)
    measurable_const measurable_const hint hcm (fun ω t _ => latticePhase_of_mem κ n t ω) hcf

end R7

/-! ### The phase at time zero does not matter when the exposed interval is empty -/

section Congr

variable {nL nR : ℕ}

/-- With the right seed not to the right of the left seed, the exposed interval is empty and the phase-shifted data do
not depend on the phase. -/
theorem phaseData_eq_of_le {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {vL : Fin (nL + 1) → ℝ}
    {vR : Fin (nR + 1) → ℝ} (h : vR 0 ≤ vL 0) (d d' : ℝ) : phaseData k ρL ρR vL vR d = phaseData k ρL ρR vL vR d' := by
  funext x
  simp only [phaseData, Ioo_eq_empty (not_lt.2 h), indicator_empty, mul_zero]

/-- **Aux. lemma 122's hypotheses only see the phase at positive times when the seeds start together**: if at time `0`
the right seed's geometric image is not to the right of the left one, two phases agreeing at positive times before
`T` have the same `HasPhaseMeansBefore`. -/
theorem hasPhaseMeansBefore_congr_pos {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {k : ℝ} {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin (nR + 1) → ℝ} {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    {T : Ω → WithTop ℝ≥0} {d d' : ℝ≥0 → Ω → ℝ}
    (h0 : ∀ ω, ((0 : ℝ≥0) : WithTop ℝ≥0) < T ω → geomRW W xR 0 0 ω ≤ geomLW W xL 0 0 ω)
    (hdd : ∀ ω (t : ℝ≥0), 0 < t → (t : WithTop ℝ≥0) < T ω → d t ω = d' t ω)
    (hM : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d T) : HasPhaseMeansBefore k ρL ρR P 𝓕 W xL xR d' T := by
  intro U hU
  refine hM U fun ω t ht => ?_
  rcases eq_zero_or_pos t with rfl | htp
  · rw [phaseData_eq_of_le (sub_le_sub_right (h0 ω ht) _) (d 0 ω) (d' 0 ω)]
    exact hU ω 0 ht
  · rw [hdd ω t htp ht]
    exact hU ω t ht

/-- At time `0` the geometric images of seeds at `0` along a driver started at `0` and continuous before a positive
lifetime are `0`. -/
theorem geomLW_geomRW_zero_of_seed {T : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, ContinuousOn (fun s => W s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < T ω}) {xL : Ω → Fin (nL + 1) → ℝ}
    {xR : Ω → Fin (nR + 1) → ℝ} (hseedL : ∀ ω, xL ω 0 = 0) (hseedR : ∀ ω, xR ω 0 = 0) {ω : Ω} (hT : 0 < T ω) :
    geomLW W xL 0 0 ω = 0 ∧ geomRW W xR 0 0 ω = 0 := by
  have hT' : ((0 : ℝ≥0) : ℝ≥0∞) < T ω := by rwa [ENNReal.coe_zero]
  have hf0 : ∀ ω, Lemma71C.frz W T 0 0 ω = 0 := fun ω => by
    simp only [Lemma71C.frz, min_self]
    split_ifs <;> simp [hW0 ω]
  have hfc := Lemma71C.continuous_frz hc 0
  refine ⟨?_, ?_⟩
  · rw [geomLW_eq_frz hc xL 0 hT' le_rfl, geomLW_zero hfc hf0 (le_of_eq (hseedL ω)), hseedL ω]
  · rw [geomRW_eq_frz hc xR 0 hT' le_rfl, geomRW_zero hfc hf0 (le_of_eq (hseedR ω).symm), hseedR ω]

end Congr

/-! ### R.7's retained hypothesis (M) for an adapted phase -/

section Adapted

/-- **R.7's retained hypothesis (M) on one two-seed pocket test, for a phase adapted before the lifetime** (follow-up 5
§3.2: the phase is lattice-valued and constant on the positive lifetime, and "right continuity of the retained
filtration makes this constant measurable at time zero"). As `twoSeedPhaseMeans_of_phaseCharFun`, for a phase `δ`
adapted before the relative lifetime in `𝓕`, equal on the positive lifetime to a lattice-valued `c` for which the
conditional-law clause of the phase-shifted word holds. The value of `δ` at time `0` is arbitrary. -/
theorem twoSeedPhaseMeans_of_phaseCharFun_adapted {P : Measure Ω} [IsProbabilityMeasure P] {κ rL rR : ℝ}
    (hκ : 0 < κ) {A : Set Ω} (hA : MeasurableSet A) (hPA : P A ≠ 0) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω) ∧ ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace A)) [𝓕.IsRightContinuous]
    (hnull : ∀ s, MeasurableSet s → condSub P A s = 0 → MeasurableSet[𝓕 0] s)
    (hpre : IsPrefixAdapted 𝓕 (fun ω : A => γ ω)) {h : A → DistOn upperHalfPlaneOpens}
    (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => h ω φ) (condSub P A))
    {δ : ℝ≥0 → Ω → ℝ} (hδa : AdaptedBefore 𝓕 (fun ω : A => capLife (γ ω)) (fun t (ω : A) => δ t ω))
    {c : A → ℝ} (hlat : ∀ ω, ∃ n : ℤ, c ω = n * phaseStep κ)
    (hδc : ∀ (ω : A) (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < capLife (γ ω) → δ t ω = c ω)
    (hcf : IsPhaseCouplingCharFun κ (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (condSub P A) 𝓕
      (fun t (ω : A) => segDriver (γ ω) t) (geomLW (fun t (ω : A) => segDriver (γ ω) t) (fun _ => LP.twoSeedXL))
      (geomRW (fun t (ω : A) => segDriver (γ ω) t) (fun _ => LP.twoSeedXR)) (fun _ ω => c ω)
      (fun ω : A => capLife (γ ω)) h) :
    PhaseSide.TwoSeedPhaseMeans κ rL rR P A γ δ := by
  have : IsProbabilityMeasure (condSub P A) := isProbabilityMeasure_condSub hA hPA
  have hγA : ∀ ω : A, IsDrivenCurve (γ ω) := fun ω => (hγ ω ω.2).1
  have hT0 : ∀ ω : A, 0 < capLife (γ ω) := fun ω => capLife_pos (hγA ω)
  have hc : ∀ ω : A, ContinuousOn (fun s => segDriver (γ ω) s) {s : ℝ≥0 | (s : ℝ≥0∞) < capLife (γ ω)} :=
    fun ω => (hγA ω).segDriver_spec.2.1
  have hcm : Measurable[𝓕 0] c := measurable_zero_of_adaptedBefore_const hT0 hδa hδc
  refine ⟨fun ω hω t ht htT => ?_, 𝓕, inferInstance, hpre, ?_⟩
  · obtain ⟨n, hn⟩ := hlat ⟨ω, hω⟩
    exact ⟨n, (hδc ⟨ω, hω⟩ t ht htT).trans hn⟩
  have hM := hasPhaseMeansBefore_of_phaseCharFun (P := condSub P A) (𝓖 := 𝓕)
    (W := fun t (ω : A) => segDriver (γ ω) t) (T := fun ω : A => capLife (γ ω)) (xL := fun _ => LP.twoSeedXL)
    (xR := fun _ => LP.twoSeedXR) (d := fun _ ω => c ω) hκ hnull (fun ω => (hγA ω).segDriver_spec.1) hT0 hc
    (adaptedBefore_segDriver_of_isDrivenCurve hγA hpre)
    (Eventually.of_forall fun ω hfin C => PocketLife.exists_lt_abs_segDriver (hγA ω) (hγ ω ω.2).2 hfin C)
    measurable_const measurable_const hint hcm (fun _ _ _ => rfl) hcf
  refine hasPhaseMeansBefore_congr_pos (fun ω hω => ?_) (fun ω t ht htT => (hδc ω t ht htT).symm) hM
  obtain ⟨hL, hR⟩ := geomLW_geomRW_zero_of_seed (T := fun ω : A => capLife (γ ω))
    (W := fun t (ω : A) => segDriver (γ ω) t) (fun ω => (hγA ω).segDriver_spec.1) hc
    (xL := fun _ => LP.twoSeedXL) (xR := fun _ => LP.twoSeedXR) (fun _ => rfl) (fun _ => rfl) (hT0 ω)
  rw [hL, hR]

end Adapted

end InteractingSLE.Sec7.PhaseMart

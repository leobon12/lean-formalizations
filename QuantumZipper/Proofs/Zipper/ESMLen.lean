import QuantumZipper.Proofs.Zipper.B5LRID
import QuantumZipper.Proofs.Zipper.ESMInst

/-!
# E-SM-inst with the `ν`-length process (decision D21)

Node **E-SM-inst (b)** of `blueprint/E_BRANCH_BLUEPRINT.md` (node E-SM), instantiated with the
length process chosen in `DECISIONS.md` D21: the right side of B5-V,
`lenRHS s = ν_{h⁰}[0₋(T), 0₋(T − s)]` (`B5.lenRHS`), clamped at time `T` and set to `0` off the
full-probability event `lenGood` on which it is continuous and nondecreasing on `[0,T]`
(`B5.ae_lengthRHS_props`). The intrinsic left length `L⁻_s = (unzipLengths √κ 𝒵 s).1`
(`ESM.lenMinus`) enters only through adaptedness: at each **fixed** `s ∈ [0,T]`, B5-V says
`L⁻_s = lenRHS s` a.s., so `lenA s` is `𝓕_s`-measurable as soon as `𝓕` is augmented by the
`P`-null sets (the usual conditions).

* `lenA`, `continuous_lenA`, `monotone_lenA`: the length process, continuous and nondecreasing
  for **every** `ω` (the hypotheses `hAc`, `hAmono` of E-SM-abs).
* `ae_mem_lenGood`, `ae_lenA_eq`: a.s. `lenA s = lenRHS (min s T)` for all `s`.
* `adapted_lenA`: adaptedness from fixed-time B5-V (explicit hypothesis `hB5V`), adaptedness of
  `L⁻` (hypothesis `hLad`) and null-completeness of `𝓕 0` (hypothesis `hnull`).
* **`lintegral_levelTime_strongMarkov_lenA`**: E-SM-inst (b) with `A = lenA`, horizon `S = T`.

Sources: Sheffield, arXiv:1012.4797, proof of Lemma 5.6 / Thm 1.8 (strong Markov property of the
driver at stopping times); E-SM-abs is `LengthMarkov.lintegral_levelTime_strongMarkov`. The
modification on a null set and the augmentation are standard bookkeeping (own).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ESM

open LengthMarkov StrongMarkov

variable {Ω : Type}

/-- The event on which `s ↦ ν_{h⁰}[0₋(T), 0₋(T − s)]` is continuous and nondecreasing on
`[0,T]`. -/
def lenGood (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) : Set Ω :=
  {ω | ContinuousOn (B5.lenRHS κ T B X ω) (Icc 0 T) ∧ MonotoneOn (B5.lenRHS κ T B X ω) (Icc 0 T)}

/-- **The E-SM length process (D21).** `lenA s ω = ν_{h⁰}[0₋(T), 0₋(T − min(s,T))]` on
`lenGood`, and `0` off it. -/
def lenA (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (lenGood κ T B X).indicator (fun ω => B5.lenRHS κ T B X ω (min (s : ℝ) T)) ω

variable {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

lemma min_mem_Icc_of_nonneg (hT : 0 ≤ T) (s : ℝ≥0) : min (s : ℝ) T ∈ Icc 0 T :=
  ⟨le_min s.2 hT, min_le_right _ _⟩

lemma lenA_of_mem {ω : Ω} (hω : ω ∈ lenGood κ T B X) (s : ℝ≥0) :
    lenA κ T B X s ω = B5.lenRHS κ T B X ω (min (s : ℝ) T) := by
  simp only [lenA, indicator_of_mem hω]

lemma lenA_of_notMem {ω : Ω} (hω : ω ∉ lenGood κ T B X) (s : ℝ≥0) : lenA κ T B X s ω = 0 := by
  simp only [lenA, indicator_of_notMem hω]

/-- `s ↦ lenA s ω` is continuous for every `ω`. -/
lemma continuous_lenA (hT : 0 ≤ T) : ∀ ω, Continuous fun s => lenA κ T B X s ω := by
  intro ω
  by_cases hω : ω ∈ lenGood κ T B X
  · simp only [lenA_of_mem hω]
    exact hω.1.comp_continuous (NNReal.continuous_coe.min continuous_const)
      (min_mem_Icc_of_nonneg hT)
  · simp only [lenA_of_notMem hω]
    exact continuous_const

/-- `s ↦ lenA s ω` is nondecreasing for every `ω`. -/
lemma monotone_lenA (hT : 0 ≤ T) : ∀ ω, Monotone fun s => lenA κ T B X s ω := by
  intro ω s t hst
  by_cases hω : ω ∈ lenGood κ T B X
  · simp only [lenA_of_mem hω]
    exact hω.2 (min_mem_Icc_of_nonneg hT s) (min_mem_Icc_of_nonneg hT t)
      (min_le_min_right _ (by exact_mod_cast hst))
  · simp only [lenA_of_notMem hω, le_refl]

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- A function a.e. equal to an `m`-measurable one is `m`-measurable when `m` contains every
`P`-null set. -/
lemma measurable_of_ae_eq_of_null {β : Type*} [MeasurableSpace β] {m : MeasurableSpace Ω}
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[m] N) {f g : Ω → β} (hg : Measurable[m] g)
    (hfg : f =ᵐ[P] g) : Measurable[m] f := by
  intro U hU
  set E : Set Ω := {ω | ¬ f ω = g ω} with hEdef
  have hE : P E = 0 := ae_iff.1 hfg
  have hsplit : f ⁻¹' U = (g ⁻¹' U ∩ Eᶜ) ∪ (f ⁻¹' U ∩ E) := by
    ext ω
    by_cases h : ω ∈ E
    · simp [h]
    · have hfg' : f ω = g ω := by simpa [hEdef] using h
      simp [h, hfg']
  rw [hsplit]
  exact ((hg hU).inter (hnull E hE).compl).union
    (hnull _ (measure_mono_null inter_subset_right hE))

variable [IsProbabilityMeasure P]

/-- A.s. `ω ∈ lenGood` (from B3(a) and `RohdeSchrammSimple`, via `B5.ae_lengthRHS_props`). -/
theorem ae_mem_lenGood (hReg : Blueprint.RevCouplingBoundaryMeasureRegular)
    (hRSS : Blueprint.RohdeSchrammSimple) (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ω ∈ lenGood κ T B X := by
  filter_upwards [B5.ae_lengthRHS_props hReg hRSS hκ hκ4 hT hB hX hind] with ω h
  exact ⟨h.2.2, h.2.1.monotoneOn⟩

omit [IsProbabilityMeasure P] in
/-- **Adaptedness of `lenA` from fixed-time B5-V.** If `𝓕 0` contains the `P`-null sets, `L⁻`
is adapted, and B5-V holds at each fixed `s ∈ [0,T]` (a.s., the null set depending on `s`), then
`lenA` is adapted. -/
theorem adapted_lenA {𝓕 : Filtration ℝ≥0 mΩ} (hT : 0 ≤ T)
    (hgood : ∀ᵐ ω ∂P, ω ∈ lenGood κ T B X)
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[𝓕 0] N)
    (hLad : ∀ s, Measurable[𝓕 s] (lenMinus κ B X s))
    (hB5V : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∀ᵐ ω ∂P, lenMinus κ B X s ω = B5.lenRHS κ T B X ω s) :
    ∀ s, Measurable[𝓕 s] (lenA κ T B X s) := by
  intro s
  set s' : ℝ≥0 := min s T.toNNReal with hs'
  have hs'c : (s' : ℝ) = min (s : ℝ) T := by
    rw [hs', NNReal.coe_min, Real.coe_toNNReal _ hT]
  have hae : lenA κ T B X s =ᵐ[P] lenMinus κ B X s' := by
    filter_upwards [hgood, hB5V s' (by rw [hs'c]; exact min_le_right _ _)] with ω hω hV
    rw [lenA_of_mem hω, hV, hs'c]
  exact measurable_of_ae_eq_of_null (fun N hN => 𝓕.mono (zero_le : (0 : ℝ≥0) ≤ s) _ (hnull N hN))
    ((hLad s').mono (𝓕.mono (min_le_left _ _)) le_rfl) hae

/-- **E-SM-inst (b) with the `ν`-length process (D21).** Strong Markov property of the driver at
the length times `T_ℓ = levelTime lenA T ℓ`: for `H ℓ` jointly measurable and
`𝓕_{T_ℓ}`-measurable, any s-finite `μ` on levels and any measurable `Ψ ≥ 0` on drivers,
`∫∫ 1{ℓ ≤ lenA T} H ℓ ω Ψ((zipCapDown √κ T_ℓ 𝒵).2) dμ(ℓ) dP
  = E[Ψ(√κ B)] · ∫∫ 1{ℓ ≤ lenA T} H ℓ ω dμ(ℓ) dP`.
Missing inputs are explicit: `hnull` (augmented filtration), `hLad` (`L⁻` adapted), `hB5V`
(fixed-time B5-V). -/
theorem lintegral_levelTime_strongMarkov_lenA {𝓕 : Filtration ℝ≥0 mΩ}
    (hReg : Blueprint.RevCouplingBoundaryMeasureRegular) (hRSS : Blueprint.RohdeSchrammSimple)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (hBad : ∀ t, Measurable[𝓕 t] (B t))
    (hindF : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (smPath B (fun _ => t))
      MeasurableSpace.pi) P)
    (hnull : ∀ N : Set Ω, P N = 0 → MeasurableSet[𝓕 0] N)
    (hLad : ∀ s, Measurable[𝓕 s] (lenMinus κ B X s))
    (hB5V : ∀ s : ℝ≥0, (s : ℝ) ≤ T →
      ∀ᵐ ω ∂P, lenMinus κ B X s ω = B5.lenRHS κ T B X ω s)
    (μ : Measure ℝ≥0) [SFinite μ]
    {H : ℝ≥0 → Ω → ℝ≥0∞} (hH : Measurable (fun p : ℝ≥0 × Ω => H p.1 p.2))
    (hHT : ∀ ℓ, Measurable[(isStoppingTime_levelTime (continuous_lenA hT.le)
      (monotone_lenA hT.le) (adapted_lenA hT.le
        (ae_mem_lenGood hReg hRSS hκ hκ4 hT hB hX hind) hnull hLad hB5V)
      T.toNNReal ℓ).measurableSpace] (H ℓ))
    {Ψ : (ℝ → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω *
        Ψ (zipCapDown (Real.sqrt κ) (levelTime (lenA κ T B X) T.toNNReal ℓ ω)
          (B2.cfg κ B X ω)).2 ∂μ ∂P =
      (∫⁻ ω, Ψ (drive κ B ω) ∂P) *
        ∫⁻ ω, ∫⁻ ℓ, {ω | (ℓ : ℝ≥0∞) ≤ lenA κ T B X T.toNNReal ω}.indicator (H ℓ) ω ∂μ ∂P := by
  have h := lintegral_levelTime_strongMarkov hB.toIsPreBrownianReal hBc hBad hindF
    (continuous_lenA hT.le) (monotone_lenA hT.le)
    (adapted_lenA hT.le (ae_mem_lenGood hReg hRSS hκ hκ4 hT hB hX hind) hnull hLad hB5V)
    T.toNNReal μ hH hHT (hΨ.comp (measurable_drvMap κ))
  simp only [Function.comp_apply, drvMap_path] at h
  simp only [zipCapDown_cfg_snd κ B X (levelTime (lenA κ T B X) T.toNNReal _)]
  exact h

/-! ## Bridge to LR-ID and the reduction of uniform B5-V -/

omit [IsProbabilityMeasure P] mΩ in
/-- **Level times agree (bridge E-SM ↔ LR-ID).** On `lenGood`, at every level `ℓ` whose
`lenRHS`-level time `tᴸ ℓ` (the one of `B5.ae_lr_id_rhs`) lies in `(0,T)`, the E-SM level time
`levelTime lenA T ℓ` equals `tᴸ ℓ`. -/
theorem levelTime_lenA_eq_lenTime (hT : 0 ≤ T) {ω : Ω} (hω : ω ∈ lenGood κ T B X) {ℓ : ℝ≥0}
    (h0 : 0 < lenTime (B5.lenRHS κ T B X ω) ℓ) (hlt : lenTime (B5.lenRHS κ T B X ω) ℓ < T) :
    (levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ) = lenTime (B5.lenRHS κ T B X ω) ℓ := by
  set R := B5.lenRHS κ T B X ω with hRdef
  set S1 : Set ℝ := {s | 0 ≤ s ∧ ENNReal.ofReal ℓ ≤ R s} with hS1def
  have hS1 : lenTime R ℓ = sInf S1 := rfl
  set t := lenTime R ℓ with ht
  have hne : S1.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [hS1, h, Real.sInf_empty] at h0
    exact lt_irrefl _ h0
  have hbdd : BddBelow S1 := ⟨0, fun s hs => hs.1⟩
  set K : Set ℝ := Icc 0 T ∩ R ⁻¹' Ici (ENNReal.ofReal ℓ) with hKdef
  have hK : IsClosed K := hω.1.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  obtain ⟨s0, hs0, hs0T⟩ := exists_lt_of_csInf_lt hne (hS1 ▸ hlt)
  have hs0K : s0 ∈ K := ⟨⟨hs0.1, hs0T.le⟩, hs0.2⟩
  have hKbdd : BddBelow K := ⟨0, fun s hs => hs.1.1⟩
  have htK : sInf K = t := by
    apply le_antisymm
    · by_contra h
      push Not at h
      obtain ⟨s, hs, hslt⟩ := exists_lt_of_csInf_lt hne (hS1 ▸ (lt_min h hlt : t < min (sInf K) T))
      have hsK : s ∈ K := ⟨⟨hs.1, (hslt.trans_le (min_le_right _ _)).le⟩, hs.2⟩
      exact absurd (csInf_le hKbdd hsK) (not_le.2 (hslt.trans_le (min_le_left _ _)))
    · rw [hS1]
      exact le_csInf ⟨s0, hs0K⟩ fun s hs => csInf_le hbdd ⟨hs.1.1, hs.2⟩
  have htmem : t ∈ K := htK ▸ hK.csInf_mem ⟨s0, hs0K⟩ hKbdd
  have hmemA : ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      ((ℓ : ℝ≥0∞) ≤ lenA κ T B X u ω ↔ ENNReal.ofReal ℓ ≤ R u) := by
    intro u hu
    rw [lenA_of_mem hω, min_eq_left hu, ENNReal.ofReal_coe_nnreal]
  have htt : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ h0.le
  apply le_antisymm
  · have hle : levelTime (lenA κ T B X) T.toNNReal ℓ ω ≤ t.toNNReal :=
      (levelTime_le_iff (continuous_lenA hT) (monotone_lenA hT) _ _ _ _).2
        (Or.inl ((hmemA _ (by rw [htt]; exact hlt.le)).2 (by rw [htt]; exact htmem.2)))
    have := NNReal.coe_le_coe.2 hle
    rwa [htt] at this
  · by_contra hcon
    push Not at hcon
    set u := levelTime (lenA κ T B X) T.toNNReal ℓ ω
    have hu := (levelTime_le_iff (continuous_lenA hT) (monotone_lenA hT) T.toNNReal ℓ u ω).1
      le_rfl
    have huT : (u : ℝ) < T := hcon.trans hlt
    rcases hu with hu | hu
    · have hmem : (u : ℝ) ∈ S1 := ⟨u.2, (hmemA u huT.le).1 hu⟩
      exact absurd (csInf_le hbdd hmem) (not_le.2 (hS1 ▸ hcon))
    · have := NNReal.coe_le_coe.2 hu
      rw [Real.coe_toNNReal _ hT] at this
      linarith

end ESM
end QuantumZipper

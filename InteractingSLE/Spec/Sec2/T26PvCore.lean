/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.T26PvStop
import InteractingSLE.Spec.Sec2.T26PvLevy
import InteractingSLE.Spec.Supplement.BR6ProofSeed
import InteractingSLE.Spec.Sec2.Assembly2Exist

/-!
# Theorem 2.6, the provider, part 7: the core, for a continuous adapted driver

Packet PROVE-T26-PROVIDER. Specification §2.3, Theorem 2.6 and its proof (`source/spec/p001-048.md` L970–L986), for an
everywhere continuous driver `W` from `0`, adapted to a usual augmentation `𝓖`, with the geometric force points
`geomLW`/`geomRW` of a deterministic ordered word. Let `σ = min (τ_z, T_*)` and `X = 𝔥(z)` the explicit coupling mean.
If `X` and `X² − A` (`A` the explicit conformal-radius clock `Aexp`) are continuous local martingales before `σ`, then
on `Ω × (ℕ → ℝ)` there is an integrated `SLE_κ(ρ)` evolution whose driver and force points agree almost surely with
those of `Ω` before `σ` (**`exists_evolution_eqOn_core`**):

* the one-point semimartingale argument (`isCLMBefore_martProc_of_onePoint`) gives `M` and `M² − κ t`;
* Lévy before `σ` and the elimination of the singular motions (`isRandomWordEvolutionUpTo_prod_of_martProc`) give a
  local evolution before `σ`;
* if the seed is a threshold state, `T_* = 0` and the zero-lifetime evolution of Theorem 2.2 is used
  (`Assembly2.isIntegratedSLEPath_of_threshold`); otherwise `σ > 0`, a positive stop below `σ` exists
  (`exists_pos_stop_lt`), at which the word seen from the driver is good, and the local evolution continues to a full
  integrated evolution on the same space (`Sec7.SeedStop.exists_isIntegratedSLEEvolution_of_stop`: "restart and
  concatenation").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec2.T26Pv

open Sec7 MartChar PhaseSelFull PocketTraversal

section Core

variable {nL nR : ℕ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The explicit coupling mean is the mean formula (2.5) with `c = (π/2)(1 + ∑ ρ^R)`. -/
theorem isMeanFormula_coupProc {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω)
    (hordL : ∀ ω t i, VL i t ω ≤ W t ω) (hordR : ∀ ω t j, W t ω ≤ VR j t ω) {z : ℂ} (hz : z ∈ H)
    {ω : Ω} {t : ℝ≥0} (ht : t ∈ befSw W z ω) :
    IsMeanFormula κ (Real.pi / 2 * (1 + ∑ j, ρR j)) (jointρ ρL ρR) W (jointV VL VR) z
      (coupProc κ ρL ρR W VL VR z) ω t := by
  have hf : QuantumZipper.fwdMap (wpath W ω) t z ∈ H := im_fwdMap_pos_of_lt (hWc ω) hz ht
  have hwt : wpath W ω t = W t ω := wpath_coe W ω t
  unfold IsMeanFormula
  have hrp : (Ito.rpath fun x => W x ω) = wpath W ω := rfl
  rw [hrp]
  rw [show coupProc κ ρL ρR W VL VR z t ω = couplingMean κ (wpath W ω) t
      (meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω)) z from rfl,
    show meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun i => VR i t ω) =
      meanExt κ ρL ρR (wpath W ω t) (fun i => VL i t ω) (fun i => VR i t ω) by rw [hwt],
    couplingMean_meanExt_eq κ ρL ρR (fun i => by rw [hwt]; exact hordL ω t i)
      (fun j => by rw [hwt]; exact hordR ω t j) hf]
  simp only [harmPart, hwt]
  rcases eq_or_ne (Real.sqrt κ) 0 with hsk | hsk
  · simp [hsk]
  · show _ = 2 / Real.sqrt κ * (Real.pi / 2 * (1 + ∑ j, ρR j) - Complex.arg (QuantumZipper.fwdMap (wpath W ω) t z)
      - 1 / 2 * ∑ j, jointρ ρL ρR j * Complex.arg (QuantumZipper.fwdMap (wpath W ω) t z + (W t ω : ℂ) -
        (jointV VL VR j t ω : ℂ))) - QuantumZipper.chiC κ * (QuantumZipper.logDerivFwd (wpath W ω) t z).im
    have hjv : ∀ x, jointV (fun i => VL i t ω) (fun i => VR i t ω) x = jointV VL VR x t ω := fun x => by
      cases x <;> rfl
    simp only [hjv]
    field_simp
    ring

/-- At a positive time before the continuation threshold, the word seen from the driver is good. -/
theorem goodWord_of_lt_thresholdTime {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) {ω : Ω}
    {s : ℝ≥0} (hs0 : 0 < s)
    (hsT : (s : ℝ≥0∞) < thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W (fun _ => xL) i t ω)
      (fun j t => geomRW W (fun _ => xR) j t ω)) :
    Assembly2.GoodWord ρL ρR ((fun i => geomLW W (fun _ => xL) i s ω - W s ω),
      (fun j => geomRW W (fun _ => xR) j s ω - W s ω)) := by
  refine ⟨fun i j => ?_, ⟨fun i k hik => ?_, fun i => ?_, fun j k hjk => ?_, fun j => ?_⟩, ?_⟩
  · have hL := geomLW_le hWc (fun _ => xL) ω s i
    have hR := le_geomRW hWc (fun _ => xR) ω s j
    by_cases h : geomLW W (fun _ => xL) i s ω = W s ω
    · have hne := geom_sep hWc (fun _ => xL) (fun _ => xR) ω s hs0 i j h
      have : W s ω < geomRW W (fun _ => xR) j s ω := lt_of_le_of_ne hR (Ne.symm hne)
      simp only
      linarith
    · have : geomLW W (fun _ => xL) i s ω < W s ω := lt_of_le_of_ne hL h
      simp only
      linarith
  · simp only [sub_le_sub_iff_right]
    exact antitone_index_geomLW hWc (xL := fun _ => xL) (ω := ω) hF.1 s hik
  · simp only [sub_nonpos]
    exact geomLW_le hWc (fun _ => xL) ω s i
  · simp only [sub_le_sub_iff_right]
    exact monotone_index_geomRW hWc (xR := fun _ => xR) (ω := ω) hF.2.2.1 s hjk
  · simp only [sub_nonneg]
    exact le_geomRW hWc (fun _ => xR) ω s j
  · have h := notMem_thresholdSet_of_lt hsT
    intro hthr
    refine h ?_
    have e : (0 : ℝ) = W s ω - W s ω := (sub_self _).symm
    rw [e, ForceWord.thresholdCondition_sub_iff] at hthr
    exact hthr

/-- **Theorem 2.6, the core** (see the module docstring). -/
theorem exists_evolution_eqOn_core [IsProbabilityMeasure P] {κ : ℝ} (hκ : 0 < κ)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    {𝓗 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} (hWc : ∀ ω, Continuous fun t => W t ω) (hW0 : ∀ ω, W 0 ω = 0)
    (hWa : StronglyAdapted (usualAugmentation 𝓗 P) W) {z : ℂ} (hz : z ∈ H)
    (hX : IsContLocalMartingaleBefore (usualAugmentation 𝓗 P) P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)
        (thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W (fun _ => xL) i t ω)
          (fun j t => geomRW W (fun _ => xR) j t ω)))
      (coupProc κ ρL ρR W (geomLW W fun _ => xL) (geomRW W fun _ => xR) z))
    (hXA : IsContLocalMartingaleBefore (usualAugmentation 𝓗 P) P
      (fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)
        (thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W (fun _ => xL) i t ω)
          (fun j t => geomRW W (fun _ => xR) j t ω)))
      (fun t ω => coupProc κ ρL ρR W (geomLW W fun _ => xL) (geomRW W fun _ => xR) z t ω ^ 2 - Aexp W z t ω)) :
    ∃ (P₀ : Measure (ℕ → ℝ)) (_ : IsProbabilityMeasure P₀)
      (𝓕' : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω × (ℕ → ℝ))))
      (W' : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ) (VL' : Fin nL → ℝ≥0 → Ω × (ℕ → ℝ) → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω × (ℕ → ℝ) → ℝ) (B : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ) (ζ : Ω × (ℕ → ℝ) → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR (P.prod P₀) 𝓕' W' VL' VR' B ζ ∧
        ∀ᵐ p ∂(P.prod P₀), ∀ t : ℝ≥0, (t : WithTop ℝ≥0) <
          min (QuantumZipper.swallowTime (wpath W p.1) z : WithTop ℝ≥0)
            (thresholdTime ρL ρR (fun t => W t p.1) (fun i t => geomLW W (fun _ => xL) i t p.1)
              (fun j t => geomRW W (fun _ => xR) j t p.1)) →
          W' t p = W t p.1 ∧ (∀ i, VL' i t p = geomLW W (fun _ => xL) i t p.1) ∧
            ∀ j, VR' j t p = geomRW W (fun _ => xR) j t p.1 := by
  classical
  set 𝓖 := usualAugmentation 𝓗 P with h𝓖
  set VL := geomLW W (fun _ : Ω => xL) with hVLd
  set VR := geomRW W (fun _ : Ω => xR) with hVRd
  set Tst : Ω → WithTop ℝ≥0 := fun ω => (thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) : ℝ≥0∞) with hTstd
  set σ : Ω → WithTop ℝ≥0 := fun ω => min (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0) (Tst ω)
    with hσd
  have hVLa : ∀ i, StronglyAdapted 𝓖 (VL i) := fun i => stronglyAdapted_geomLW hWa hWc measurable_const i
  have hVRa : ∀ j, StronglyAdapted 𝓖 (VR j) := fun j => stronglyAdapted_geomRW hWa hWc measurable_const j
  have hpathL : ∀ ω i, MartChar.IsForcePath (fun t => W t ω) (fun t => VL i t ω) := fun ω i =>
    isForcePath_geomLW hWc _ ω i
  have hpathR : ∀ ω j, MartChar.IsForcePath (fun t => W t ω) (fun t => VR j t ω) := fun ω j =>
    isForcePath_geomRW hWc _ ω j
  have hordL : ∀ ω t i, VL i t ω ≤ W t ω := fun ω t i => geomLW_le hWc _ ω t i
  have hordR : ∀ ω t j, W t ω ≤ VR j t ω := fun ω t j => le_geomRW hWc _ ω t j
  have hTst : IsStoppingTime 𝓖 Tst := fun t =>
    MartChar.measurableSet_thresholdTime_le hWc (fun i ω => (hpathL ω i).1) (fun j ω => (hpathR ω j).1)
      hWa hVLa hVRa (fun ω i j s t hst h => geomLW_merge hWc _ ω i j s t hst h)
      (fun ω i j s t hst h => geomRW_merge hWc _ ω i j s t hst h) t
  have hσst : IsStoppingTime 𝓖 σ := (isStoppingTime_swallowTime hWa hWc hz).min hTst
  have hσsw : ∀ ω (t : ℝ≥0), (t : WithTop ℝ≥0) < σ ω → t ∈ befSw W z ω := fun ω t ht =>
    lt_of_lt_of_le ht (min_le_left _ _)
  -- (1) the one-point semimartingale argument
  set ε : Fin nL ⊕ Fin nR → ℝ := Sum.elim (fun _ => -1) (fun _ => 1) with hεd
  have hε : ∀ j, ε j * ε j = 1 := fun j => by cases j <;> simp [hεd]
  have hVc : ∀ ω j, Continuous fun t => jointV VL VR j t ω := fun ω j => by
    cases j with
    | inl i => exact (hpathL ω i).1
    | inr i => exact (hpathR ω i).1
  have hVa : ∀ j, StronglyAdapted 𝓖 (jointV VL VR j) := fun j => by
    cases j with
    | inl i => exact hVLa i
    | inr i => exact hVRa i
  have hU : ∀ ω j, Monotone fun t => ε j * jointV VL VR j t ω := fun ω j => by
    cases j with
    | inl i =>
      intro a b hab
      have := antitone_geomLW hWc (fun _ => xL) ω i hab
      simp only [hεd, Sum.elim_inl, jointV]
      linarith
    | inr i =>
      intro a b hab
      have := monotone_geomRW hWc (fun _ => xR) ω i hab
      simp only [hεd, Sum.elim_inr, jointV]
      linarith
  have hsign : ∀ ω j u, 0 ≤ ε j * (jointV VL VR j u ω - W u ω) := fun ω j u => by
    cases j with
    | inl i =>
      have := hordL ω u i
      simp only [hεd, Sum.elim_inl, jointV]
      linarith
    | inr i =>
      have := hordR ω u i
      simp only [hεd, Sum.elim_inr, jointV]
      linarith
  have hpath : ∀ ω j, MartChar.IsForcePath (fun t => W t ω) (fun t => jointV VL VR j t ω) := fun ω j => by
    cases j with
    | inl i => exact hpathL ω i
    | inr i => exact hpathR ω i
  obtain ⟨hM, hM2⟩ := isCLMBefore_martProc_of_onePoint (P := P) (𝓖 := 𝓖) (κ := κ)
    (c := Real.pi / 2 * (1 + ∑ j, ρR j)) hκ (ρ := jointρ ρL ρR) hε hWc hWa hVc hVa hU hsign hpath hz
    (ζ := σ) hσsw (X := coupProc κ ρL ρR W VL VR z)
    (fun ω t ht => isMeanFormula_coupProc hWc hordL hordR hz (hσsw ω t ht)) hX hXA
  -- (2) the landed local-martingale form
  have hM0 : martProc (jointρ ρL ρR) W (jointV VL VR) 0 = fun _ => 0 := funext fun ω => by
    simp [martProc, martValue]
  have hMl := Certify2426.IsContLocalMartingaleBefore.isLocalMartingaleBefore hM
    (by rw [hM0]; exact stronglyMeasurable_const) (by rw [hM0]; exact integrable_const _)
  have hM20 : (fun ω => martProc (jointρ ρL ρR) W (jointV VL VR) 0 ω ^ 2 - κ * ((0 : ℝ≥0) : ℝ)) =
      fun _ => (0 : ℝ) := by
    funext ω
    simp [martProc, martValue]
  have hM2l := Certify2426.IsContLocalMartingaleBefore.isLocalMartingaleBefore hM2
    (by rw [hM20]; exact stronglyMeasurable_const) (by rw [hM20]; exact integrable_const _)
  -- (3) Lévy and the local evolution before `σ`
  obtain ⟨P₀, hP₀, 𝓦, B, hE, -, -⟩ := isRandomWordEvolutionUpTo_prod_of_martProc (𝒢 := ⊥) (F := univ)
    hκ bot_le MeasurableSet.univ measurable_const measurable_const (fun _ => hF.2.1) (fun _ => hF.2.2.2)
    (fun _ => hF.1) (fun _ => hF.2.2.1) hW0 hWc hWa hσst hMl hM2l
    (ae_of_all _ fun ω _ => min_le_right _ _)
  obtain ⟨-, -, -, -, hB, hWb, hVLb, hVRb, hpathE⟩ := hE
  have hUpTo : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR (P.prod P₀) (WholeField.prodFiltration 𝓖 𝓦)
      (fun t p => W t p.1) (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) B (fun p => (σ p.1 : ℝ≥0∞)) :=
    ⟨hB, hWb, hVLb, hVRb, hpathE.mono fun p hp => hp (mem_preimage.2 (mem_univ _))⟩
  have hVL0 : ∀ ω i, VL i 0 ω = xL i := fun ω i => geomLW_zero hWc hW0 (hF.2.1 i)
  have hVR0 : ∀ ω j, VR j 0 ω = xR j := fun ω j => geomRW_zero hWc hW0 (hF.2.2.2 j)
  have hseed : ∀ ω, (0 : ℝ≥0) ∈ thresholdSet ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) ↔
      ForceWord.ThresholdCondition ρL ρR 0 xL xR := fun ω => by
    show ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω) ↔ _
    rw [hW0 ω]
    simp only [hVL0, hVR0]
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- the threshold seed: `T_* = 0`, the zero-lifetime evolution
    have hσ0 : ∀ ω, σ ω = 0 := fun ω => by
      have hle : thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) ≤
          ((0 : ℝ≥0) : ℝ≥0∞) :=
        (thresholdTime_le_iff (hWc ω) (fun i => (hpathL ω i).1) (fun j => (hpathR ω j).1)
          (fun i j s t hst h => geomLW_merge hWc _ ω i j s t hst h)
          (fun i j s t hst h => geomRW_merge hWc _ ω i j s t hst h) 0).2 ⟨0, le_rfl, (hseed ω).2 hthr⟩
      refine le_antisymm ((min_le_right _ _).trans ?_) bot_le
      exact hle
    have hadapt : ∀ X : ℝ≥0 → Ω × (ℕ → ℝ) → ℝ, AdaptedBefore (WholeField.prodFiltration 𝓖 𝓦) (fun _ => 0) X :=
      fun X t A _ => by
        have : {p : Ω × (ℕ → ℝ) | (t : ℝ≥0∞) < 0 ∧ X t p ∈ A} = ∅ :=
          eq_empty_of_forall_notMem fun p hp => absurd hp.1 (not_lt.2 bot_le)
        rw [this]
        exact @MeasurableSet.empty _ (WholeField.prodFiltration 𝓖 𝓦 t)
    refine ⟨P₀, hP₀, WholeField.prodFiltration 𝓖 𝓦, fun _ _ => 0, fun i _ _ => xL i, fun j _ _ => xR j, B,
      fun _ => 0, ⟨hB, hadapt _, fun _ => hadapt _, fun _ => hadapt _,
        ae_of_all _ fun p => Assembly2.isIntegratedSLEPath_of_threshold hthr _⟩, ae_of_all _ fun p t ht => ?_⟩
    have h0 : σ p.1 = 0 := hσ0 p.1
    exact absurd (lt_of_lt_of_eq ht h0) (not_lt.2 bot_le)
  · -- a positive stop below `σ`, at which the word is good: continue the local evolution
    have hσpos : ∀ ω, 0 < σ ω := fun ω => by
      refine lt_min ?_ ?_
      · exact QuantumZipper.swallowTime_pos (continuous_wpath hWc ω) hz
      · rcases eq_or_ne (thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω))
          ((0 : ℝ≥0) : ℝ≥0∞) with h0 | h0
        · have hmem := thresholdTime_mem_thresholdSet (hWc ω) (fun i => (hpathL ω i).1)
            (fun j => (hpathR ω j).1) (fun i j s t hst h => geomLW_merge hWc _ ω i j s t hst h)
            (fun i j s t hst h => geomRW_merge hWc _ ω i j s t hst h) h0
          exact absurd ((hseed ω).1 hmem) hthr
        · show (0 : ℝ≥0∞) < _
          exact pos_iff_ne_zero.2 (by simpa using h0)
    obtain ⟨-, σn, hσn, hσnζ, hσnex, -⟩ := hX
    obtain ⟨T, hT, hT0, hTσ⟩ := exists_pos_stop_lt (P := P) hσpos hσn hσnζ hσnex
    set Q := P.prod P₀ with hQ
    have hT' : IsStoppingTime (usualAugmentation (WholeField.prodFiltration 𝓖 𝓦) Q)
        (fun p : Ω × (ℕ → ℝ) => ((T p.1 : ℝ≥0) : WithTop ℝ≥0)) := fun t =>
      Ito.le_usualAugmentation _ _ t _ (isStoppingTime_fst (Ω₀ := ℕ → ℝ) (𝓦 := 𝓦) hT t)
    have hTσ' : ∀ᵐ p ∂Q, (T p.1 : ℝ≥0∞) < (σ p.1 : ℝ≥0∞) :=
      Measure.quasiMeasurePreserving_fst.ae hTσ
    have hgood : ∀ᵐ p ∂Q, Assembly2.GoodWord ρL ρR (Assembly2.contWord (fun t p => W t p.1)
        (fun i t p => VL i t p.1) (fun j t p => VR j t p.1) (fun p => T p.1) p) := by
      filter_upwards [hTσ'] with p hp
      exact goodWord_of_lt_thresholdTime hF hWc (hT0 p.1) (lt_of_lt_of_le hp (min_le_right _ _))
    obtain ⟨𝓕', W', VL', VR', B', ζ', hEv, hag⟩ := SeedStop.exists_isIntegratedSLEEvolution_of_stop hκ hUpTo
      hT' (fun p => hT0 p.1) hTσ' hgood
    refine ⟨P₀, hP₀, 𝓕', W', VL', VR', B', ζ', hEv, ?_⟩
    filter_upwards [hag] with p hp t ht
    obtain ⟨h1, h2, h3⟩ := hp.2 t ht
    exact ⟨h1.symm, fun i => (h2 i).symm, fun j => (h3 j).symm⟩

end Core

end InteractingSLE.Sec2.T26Pv

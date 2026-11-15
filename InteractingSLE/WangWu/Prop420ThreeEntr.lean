/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField9Entr

/-!
# Lemma 6.2's history locality for a line of a translated and shifted field (any `0 < κ ≤ 4`)

Packet PROVE-WW-B22. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, ruling R31), Proposition 4.20
(text dump L1701–1745): "If either line is stopped in the filtration enlarged by the other line, the same rule holds
on all exposed sides. The statement also holds for three ordered seed lines, one of which may be stopped in the
filtration enlarged by the other two." Exposing a stopped line in the filtration enlarged by complete lines is
Lemma 4.5 / the specification's Lemma 6.2, whose hypothesis on each curve is the history-sensitive locality at first
entrance times (`Sec6.IsEntranceHistoryLocal`).

For flow lines (`0 < κ < 4`) this is PROVE-WHOLEFIELD9's `WholeField.retainedRangeEntranceStatement` (Aux. lemma 56
at first entrance times). Its proof uses the flow line only through
* the field transformation `h' = h(· + x) + c` (`IsTranslateAddConst x c`; for a flow line `c = θχ`),
* the optional hull coupling of `h'` with some force word, and
* a continuous generating trace (Aux. lemma 16's kernel `hasRetainedRangeKernel_of_trace`, valid for `κ ≤ 4`).

This file states and proves it in that generality (`isEntranceKilledHistoryLocal_of_translate`), so that it applies to
Wang–Wu's seed lines at `κ = 4`: the level line of `h + u` is the line of the coupling field `flowField 0 u h`
(`x = 0`, `c = u`), whose centred field is that of `h` (`SeedField.centredField_flowField_eq`). The proof is
PROVE-WHOLEFIELD9's, with the flow-line data replaced by these three hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Sec6 Restart

/-- **Aux. lemma 56 at the first entrance times of a capped line of a translated and shifted field** (any
`0 < κ ≤ 4`, any force word). Let `h' = h(· + x) + c` be coupled with an integrated `SLE_κ(ρ)` evolution as an
optional hull coupling, with a continuous generating trace `η − x` almost surely, and let `ηc` be a version of `η`
frozen after the cap `m` (continuous for every `ω`, measurable at each time). Then `ηc` has Lemma 6.2's
history-sensitive
locality at first entrance times, with its killing record, for the centred field `h − u₀` (`u₀` harmonic on `ℍ`).
This is `retainedRangeEntranceStatement` without the flow-line packaging. -/
theorem isEntranceKilledHistoryLocal_of_translate {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {h h' : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {x c : ℝ} (htrans : ∀ ω, IsTranslateAddConst x c (h ω) (h' ω))
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h') {η : Ω → ℝ≥0 → ℂ}
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x)) (hhm : Measurable h)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) (m : ℝ≥0) {ηc : Ω → ℝ≥0 → ℂ}
    (hcont : ∀ ω, Continuous (ηc ω)) (hηcm : ∀ t, Measurable fun ω => ηc ω t)
    (hηc : ∀ᵐ ω ∂P, ∀ t, ηc ω t = η ω (capTime m (ζ ω) t)) :
    IsEntranceKilledHistoryLocal ηc (fun ω => cutLife (ζ ω) m) (centredField h u₀) P := by
  intro U G hUH hG hd
  classical
  have hζm : Measurable ζ := measurable_of_adaptedBefore hC.1.2.1
  have hh0 : Measurable (centredField h u₀) := measurable_centredField hhm u₀
  have hXm : Measurable fun ω => G (centredField h u₀ ω) := hG.comp hh0
  have hYm : Measurable fun ω => markovCompl G (centredField h u₀ ω) := (measurable_markovCompl hG).comp hh0
  have hUo : IsOpen (U : Set ℂ) := U.isOpen
  have hUm : MeasurableSet (U : Set ℂ) := hUo.measurableSet
  have hU' : U ≤ upperHalfPlaneOpens := hUH
  have hxU : ((x : ℝ) : ℂ) ∉ (U : Set ℂ) := fun hx => ofReal_notMem_H x (hUH hx)
  -- the marks
  have hcm : Measurable fun ω => pathCoord (ηc ω) := Measurable.of_eval fun q => hηcm q
  have hFm := measurable_firstEntrance (U := (U : Set ℂ)) hUm
  have hkm : Measurable fun p : (ℚ≥0 → ℂ) × ℝ≥0∞ => khistOf p.1 p.2 (firstEntrance U p.1) :=
    (measurable_histOf.comp ((hFm.comp measurable_fst).prodMk measurable_fst)).prodMk
      (measurable_lifeRec.comp (measurable_snd.prodMk (hFm.comp measurable_fst)))
  have hYkm : Measurable fun ω =>
      khistOf (pathCoord (ηc ω)) (cutLife (ζ ω) m) (firstEntrance U (pathCoord (ηc ω))) :=
    hkm.comp (hcm.prodMk ((measurable_cutLife m).comp hζm))
  have hEeq : {ω | AvoidsUpTo (ηc ω) (firstEntrance U (pathCoord (ηc ω))) U} =
      (fun ω => ηc ω 0) ⁻¹' (U : Set ℂ)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_preimage, mem_compl_iff]
    exact ⟨fun h => h 0 (by simp), fun h0 t ht => notMem_of_le_firstEntrance hUo (hcont ω) h0 ht⟩
  have hEm : MeasurableSet {ω | AvoidsUpTo (ηc ω) (firstEntrance U (pathCoord (ηc ω))) U} := by
    rw [hEeq]; exact hηcm 0 hUm.compl
  have h𝓜 : markedHistSigma {ω | AvoidsUpTo (ηc ω) (firstEntrance U (pathCoord (ηc ω))) U}
      (fun ω => khistOf (pathCoord (ηc ω)) (cutLife (ζ ω) m) (firstEntrance U (pathCoord (ηc ω)))) ≤ mΩ := by
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨B, hB, rfl⟩
    exact hEm.inter (hYkm hB)
  -- it suffices to produce the sequence of σ-algebras
  suffices key : ∃ 𝒦 : ℕ → MeasurableSpace Ω, Monotone 𝒦 ∧ (∀ n, 𝒦 n ≤ mΩ) ∧
      (∀ n m', MeasurableSet[𝒦 n] m' → FactorsOn P (fun ω => G (centredField h u₀ ω))
        (fun ω => markovCompl G (centredField h u₀ ω)) m') ∧
      (∀ᵐ ω ∂P, ηc ω 0 ∉ (U : Set ℂ)) ∧
      Measurable[aeSigma (⨆ n, 𝒦 n) P] fun ω =>
        khistOf (pathCoord (ηc ω)) (cutLife (ζ ω) m) (firstEntrance U (pathCoord (ηc ω))) by
    obtain ⟨𝒦, hmono, h𝒦, hfac, hE0, hYae⟩ := key
    refine condIndepEv_of_seq hXm hYm h𝓜 hmono h𝒦 hfac ?_
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨B, hB, rfl⟩
    have hEa : MeasurableSet[aeSigma (⨆ n, 𝒦 n) P]
        {ω | AvoidsUpTo (ηc ω) (firstEntrance U (pathCoord (ηc ω))) U} := by
      refine ⟨univ, MeasurableSet.univ, ae_eq_univ.2 (ae_iff.1 ?_)⟩
      filter_upwards [hE0] with ω hω
      exact fun t ht => notMem_of_le_firstEntrance hUo (hcont ω) hω ht
    exact hEa.inter (hYae hB)
  have hE' := hC.1
  obtain ⟨hX, -⟩ := hC.2.2.2
  have hKc : HasRetainedRangeKernel P W VL VR ζ h' hX :=
    hasRetainedRangeKernel_of_trace hC hκ hκ4 (htr.mono fun ω hω => ⟨_, hω⟩) hX
  -- the start of the capped path
  have hstart : ∀ ω, IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x) →
      (∀ t, ηc ω t = η ω (capTime m (ζ ω) t)) → ηc ω 0 = x := fun ω htrω hηcω => by
    rw [hηcω 0, show capTime m (ζ ω) 0 = 0 from min_eq_left zero_le]
    exact sub_eq_zero.1 htrω.1
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: the lifetime is `0` and the capped path is constant
    have hζ0 := hE'.ae_lifetime_eq_zero_of_threshold hseed
    have hconst : ∀ᵐ ω ∂P, ζ ω = 0 ∧ ηc ω = fun _ => ((x : ℝ) : ℂ) := by
      filter_upwards [hζ0, htr, hηc] with ω h0 htrω hηcω
      refine ⟨h0, funext fun t => ?_⟩
      have h1 := hηcω t
      rw [h0, show capTime m 0 t = 0 by simp [capTime]] at h1
      rw [h1, ← hstart ω htrω hηcω, hηcω 0, show capTime m (ζ ω) 0 = 0 from min_eq_left zero_le]
    refine ⟨fun _ => ⊥, fun _ _ _ => le_rfl, fun _ => bot_le, fun n m' hm' => factorsOn_of_bot hh0 hG hd m' hm',
      ?_, ?_⟩
    · filter_upwards [hconst] with ω hω
      rw [hω.2]; exact hxU
    · refine measurable_aeSigma_of_ae_eq' (Z := fun _ => khistOf (pathCoord fun _ => ((x : ℝ) : ℂ))
        (cutLife 0 m) (firstEntrance U (pathCoord fun _ => ((x : ℝ) : ℂ)))) measurable_const ?_
      filter_upwards [hconst] with ω hω
      simp only [hω.1, hω.2]
  · -- an admissible seed: the stops `τₙ = R ∧ m ∧ σₙ`
    obtain ⟨σ, hσ, hσm, hσζ, hσex⟩ := exists_isAnnouncingSeq_driving hE' hκ hX hseed
    have : (drivingFiltration P hX).IsRightContinuous := Ito.isRightContinuous_usualAugmentation _ _
    have hW : AdaptedBefore (drivingFiltration P hX) ζ W :=
      Ito.adaptedBefore_mono (Ito.le_usualAugmentation _ _) (Coupling.adaptedBefore_killedDriving_W hX)
    have hτ := isStoppingTime_tauN (x := x) (m := m) hW hUm hσ
    -- the good event
    have hgood : ∀ᵐ ω ∂P, (∀ n, (σ n ω : ℝ≥0∞) < ζ ω) ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ σ n ω) ∧
        IsGeneratingTrace (fun t => W t ω) (ζ ω) (fun t => η ω t - x) ∧
        ContinuousOn (fun t => W t ω) {s | (s : ℝ≥0∞) < ζ ω} ∧ W 0 ω = 0 ∧
        ∀ t, ηc ω t = η ω (capTime m (ζ ω) t) := by
      filter_upwards [ae_all_iff.2 hσζ, hσex, htr, hE'.2.2.2.2, hηc] with ω h1 h2 h3 hp h5
      exact ⟨h1, h2, h3, hp.2.2.2.1, hp.1, h5⟩
    have hg : ∀ᵐ ω ∂P, (∀ n, (σ n ω : ℝ≥0∞) < ζ ω) ∧ (∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ σ n ω) ∧
        ηc ω 0 ∉ (U : Set ℂ) ∧ (∀ t, ηc ω t = ηc ω (min t (min (ζ ω) m).toNNReal)) ∧
        (∀ s : ℝ≥0, s ≤ m → (s : ℝ≥0∞) < ζ ω → traceVal W ζ x s ω = ηc ω s) ∧
        (∀ s : ℝ≥0, s ≤ m → (s : ℝ≥0∞) < ζ ω → ηc ω s = η ω s) := by
      filter_upwards [hgood] with ω hgω
      obtain ⟨g1, g2, htrω, hwc, hw0, hηcω⟩ := hgω
      have hcap : ∀ s : ℝ≥0, s ≤ m → (s : ℝ≥0∞) < ζ ω → ηc ω s = η ω s := fun s hsm hsζ => by
        rw [hηcω s, capTime_of_le m (ζ ω) (le_min hsζ.le (ENNReal.coe_le_coe.2 hsm))]
      refine ⟨g1, g2, by rw [hstart ω htrω hηcω]; exact hxU, fun t => ?_, fun s hsm hsζ => ?_, hcap⟩
      · rw [hηcω t, hηcω (min t _)]
        congr 1
        simp only [capTime]
        rw [min_eq_left (min_le_right _ _)]
      · rw [traceVal_eq htrω hwc hw0 hsζ, hcap s hsm hsζ]
        ring
    refine ⟨fun n => (hτ n).measurableSpace, fun n k hnk => ?_, fun n => (hτ n).measurableSpace_le,
      fun n m' hm' => ?_, ?_, ?_⟩
    · exact IsStoppingTime.measurableSpace_mono (hτ n) (hτ k) fun ω =>
        WithTop.coe_le_coe.2 (monotone_tauN hσm ω hnk)
    · -- the kernel at `τₙ`
      obtain ⟨M, hMh, hMk⟩ := exists_flowKernel hKc htrans hu₀ (tauN W ζ x U m σ n) (hτ n)
        ⟨m, fun ω => seqStop_le_m n⟩ ((hσζ n).mono fun ω hω =>
          lt_of_le_of_lt (ENNReal.coe_le_coe.2 (seqStop_le_σ n)) hω)
      set V : Ω → Set ℂ := fun ω =>
        H \ (fun z => z + (x : ℂ)) '' ((fun t => η ω t - x) '' Icc 0 (tauN W ζ x U m σ n ω)) with hVdef
      have htrn : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (tauN W ζ x U m σ n ω) (fun t => η ω t - x) := by
        filter_upwards [hgood] with ω hgω
        obtain ⟨g1, -, htrω, -⟩ := hgω
        exact htrω.mono_horizon ((ENNReal.coe_le_coe.2 (seqStop_le_σ n)).trans (g1 n).le)
      have hV : ∀ᵐ ω ∂P, IsOpen (V ω) ∧ V ω ⊆ H ∧ (U : Set ℂ) ⊆ V ω ∧ IsHarmonicDistOn (M ω) (V ω) := by
        filter_upwards [hgood, hg, htrn, hMh] with ω hgω hgω' htrnω hMω
        obtain ⟨g1, -, htrω, -⟩ := hgω
        obtain ⟨-, -, g3, g4, g5, hcap⟩ := hgω'
        refine ⟨?_, sdiff_subset, fun z hz => ⟨hUH hz, ?_⟩, hMω _ htrnω⟩
        · refine isOpen_H.sdiff (IsCompact.isClosed ?_)
          refine (isCompact_Icc.image_of_continuousOn (htrω.2.1.mono fun t ht => ?_)).image
            (continuous_id.add continuous_const)
          exact (ENNReal.coe_le_coe.2 (ht.2.trans (seqStop_le_σ n))).trans (g1 n).le
        · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
          have htm : t ≤ m := ht.2.trans (seqStop_le_m n)
          have htζ : (t : ℝ≥0∞) < ζ ω :=
            lt_of_le_of_lt (ENNReal.coe_le_coe.2 (ht.2.trans (seqStop_le_σ n))) (g1 n)
          have hnot := notMem_of_le_tauN (W := W) (x := x) (σ := σ) hUo (hcont ω) g3 g4 g5 n ht.2
          rw [hcap t htm htζ] at hnot
          exact hnot (by simpa using hz)
      have hker : ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
          (P[fun ω' => Complex.exp (Complex.I * (centredField h u₀ ω' χ : ℂ)) | (hτ n).measurableSpace]) ω =
            rangeKerCF (M ω) (V ω) χ := fun χ => by
        filter_upwards [hMk χ, htrn] with ω hω htrnω
        exact hω _ htrnω
      exact fun Φ Ψ => setIntegral_exp_markov_of_kernel (hτ n).measurableSpace_le hU' hV hker hh0 hG hd Φ Ψ m' hm'
    · filter_upwards [hg] with ω hgω
      exact hgω.2.2.1
    · refine measurable_aeSigma_of_ae_eq' (measurable_khistV hW hUm hσ hσm) ?_
      filter_upwards [hg] with ω hgω
      obtain ⟨g1, g2, g3, g4, g5, -⟩ := hgω
      exact khist_eq_khistV hUo (hcont ω) g1 g2 g3 g4 g5

end WholeField

end InteractingSLE

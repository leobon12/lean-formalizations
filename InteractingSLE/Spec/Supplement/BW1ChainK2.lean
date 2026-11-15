/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1ChainCond
import InteractingSLE.Spec.Sec7.PocketWordEvol
import InteractingSLE.Spec.Restart.StoppedK2Evol
import InteractingSLE.Spec.Restart.DomainMarkovAux79Stop
import InteractingSLE.Spec.Restart.FCDet

/-!
# The relative chain, part 2: mean martingales, Theorem 2.4 and K2 for an infinite relative lifetime

Packet PROVE-BW1-CHAIN (Proposition BW1, supplement pp. 613–615: "Relative capacity is adapted, continuous and
strictly increasing […] Theorem 2.4 identifies the relative driver […] Its relative capacity lifetime is infinite").
The generic probabilistic core of BW1 (and of every relative continuation whose relative lifetime is infinite): a
continuation `W` in a retained chart, with a random initial word `(xL, xR)` measurable for the retained past `𝒢`,
geometric force points, live event `F ∈ 𝒢`, and

* (S) its protected-kernel law and (L) its member identities at every deterministic relative time, for a filtration
  `𝓗` with `𝒢 ≤ 𝓗 0`, **with infinite lifetime** (`HasSafeLaw … F ⊤`, `HasSafeMembers … F ⊤`),
* no continuation threshold on `F` (almost surely),

is, under almost every regular conditional law given `𝒢` on `F`, an optional hull coupling of its word with the field
(**`ae_isOptionalHullCoupling_of_hasSafeLaw_top`**). The chain:

1. condition on `F` (`BW1ChainCond`: under `Q = P[·|F]` the live event is everything, (S) and (L) transfer);
2. (S) ⇒ the conditional-law clause at stopping times of the usual augmentation
   (`Aux79.isCouplingCharFun_of_hasSafeLaw`) ⇒ the coupling means are local martingales until swallowing
   (`MartMeans2.exists_isLocalMartingaleBefore_meanProcOn` with the deterministic announcing times `n`: the mean
   martingales);
3. Theorem 2.4 with a random initial word on `Ω` itself (`PocketWord.isRandomWordEvolution_of_coupProc`: `M/√κ` is a
   Brownian motion by Lévy, the coordinates solve the integrated equations up to the threshold) — no enlargement is
   needed because the lifetime is infinite: the relative evolution (E);
4. K2 (`DomainMarkov.K2.ae_isOptionalHullCoupling_k`) under `Q`, with lifetime the threshold (`= ⊤` a.s.);
5. back to `P`: the kernels of `Q` and `P` given `𝒢` agree on `F` (`ae_condExpKernel_cond_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Chain

open Restart.DomainMarkov Restart.DomainMarkov.K2 Sec7 Sec7.PocketTraversal MartChar

section Lifetime

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {F : Set Ω} {nL nR : ℕ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓗 : Filtration ℝ≥0 mΩ} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {X : Ω → DistOn upperHalfPlaneOpens}

/-- (S) with infinite lifetime gives (S) with any lifetime (its safe events are smaller). -/
theorem hasSafeLaw_of_top (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F (fun _ => ⊤) W VL VR X) :
    HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X := by
  intro ψ q D hD hDs
  refine hlaw ψ q D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF, hlt, hdis⟩ := h1 hωD
  exact ⟨hF, ENNReal.coe_lt_top, hdis⟩

/-- (L) with infinite lifetime gives (L) with any lifetime (its safe events are smaller). -/
theorem hasSafeMembers_of_top (hmem : HasSafeMembers P 𝓗 F (fun _ => ⊤) W X) :
    HasSafeMembers P 𝓗 F ζ W X := by
  intro s Fb hFb D hD hDs
  refine hmem s Fb hFb D hD ?_
  filter_upwards [hDs] with ω h1 hωD
  obtain ⟨hF, -, hdis⟩ := h1 hωD
  exact ⟨hF, ENNReal.coe_lt_top, hdis⟩

/-- The deterministic integer times announce an infinite lifetime. -/
theorem isAnnouncingSeq_nat (𝓖 : Filtration ℝ≥0 mΩ) (Q : Measure Ω) :
    Coupling.IsAnnouncingSeq 𝓖 Q (fun _ => ⊤) (fun n _ => (n : ℝ≥0)) := by
  refine ⟨fun n => isStoppingTime_const 𝓖 (n : ℝ≥0), fun ω n m hnm => ?_,
    fun n => ae_of_all _ fun ω => ENNReal.coe_lt_top, ae_of_all _ fun ω t _ => ?_⟩
  · show (n : ℝ≥0) ≤ (m : ℝ≥0)
    exact_mod_cast hnm
  · obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ)
    exact ⟨n, by exact_mod_cast hn⟩

/-- (S) only sees the field almost surely on the live event. -/
theorem hasSafeLaw_congr_ae {X' : Ω → DistOn upperHalfPlaneOpens} (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X)
    (he : ∀ᵐ ω ∂P, ω ∈ F → X ω = X' ω) : HasSafeLaw κ ρL ρR P 𝓗 F ζ W VL VR X' := by
  intro ψ q D hD hDs
  rw [← hlaw ψ q D hD hDs]
  refine setIntegral_congr_ae (𝓗.le q _ hD) ?_
  filter_upwards [hDs, he] with ω h1 h2 hωD
  rw [h2 (h1 hωD).1]

/-- (L) only sees the field almost surely on the live event. -/
theorem hasSafeMembers_congr_ae {X' : Ω → DistOn upperHalfPlaneOpens} (hmem : HasSafeMembers P 𝓗 F ζ W X)
    (he : ∀ᵐ ω ∂P, ω ∈ F → X ω = X' ω) : HasSafeMembers P 𝓗 F ζ W X' := by
  intro s Fb hFb D hD hDs f Ξ
  have hD' : ∀ᵐ ω ∂P, ω ∈ D → X ω = X' ω := by
    filter_upwards [hDs, he] with ω h1 h2 hωD using h2 (h1 hωD).1
  have hI : ∀ Ξ' : TestOn upperHalfPlaneOpens, ∫ ω in D, Complex.exp (Complex.I * (X' ω Ξ' : ℂ)) ∂P =
      ∫ ω in D, Complex.exp (Complex.I * (X ω Ξ' : ℂ)) ∂P := fun Ξ' =>
    setIntegral_congr_ae (𝓗.le s _ hD) (hD'.mono fun ω h hωD => by rw [h hωD])
  rw [hI, hI]
  exact hmem s Fb hFb D hD hDs f Ξ

end Lifetime

section Main

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ}

/-- **The relative chain for an infinite relative lifetime: mean martingales, Theorem 2.4 and K2.** Let `𝓗` be a
filtration whose time-zero σ-algebra contains the retained past `𝒢`, `F ∈ 𝒢` the live event, `(xL, xR)` a
`𝒢`-measurable ordered initial word, and `W` a continuous `𝓗`-adapted driver from `0` with the geometric force points
of that word. Suppose the field `X` has K2's protected-kernel law (S) and member identities (L) on `F` with infinite
lifetime, and the word reaches no continuation threshold on `F` (almost surely). Then for `P`-almost every `ω₀ ∈ F`,
under `condExpKernel P 𝒢 ω₀`, processes equal to the coordinates (kernel-almost surely, at every time) form with `X`
an optional hull coupling of the word `(xL ω₀, xR ω₀)`, with lifetime the continuation threshold. -/
theorem ae_isOptionalHullCoupling_of_hasSafeLaw_top {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {𝓗 : Filtration ℝ≥0 mΩ} (h𝒢 : 𝒢 ≤ 𝓗 0) {F : Set Ω} (hF : MeasurableSet[𝒢] F)
    {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} (hxL : Measurable[𝒢] xL) (hxR : Measurable[𝒢] xR)
    (hxL0 : ∀ ω i, xL ω i ≤ 0) (hxR0 : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) {W : ℝ≥0 → Ω → ℝ} (hW0 : ∀ ω, W 0 ω = 0)
    (hWc : ∀ ω, Continuous fun t => W t ω) (hWa : StronglyAdapted 𝓗 W) {X : Ω → DistOn upperHalfPlaneOpens}
    (hX : Measurable X) (hint : ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun ω => X ω φ) P)
    (hlaw : HasSafeLaw κ ρL ρR P 𝓗 F (fun _ => ⊤) W (geomLW W xL) (geomRW W xR) X)
    (hmem : HasSafeMembers P 𝓗 F (fun _ => ⊤) W X)
    (hthr : ∀ᵐ ω ∂P, ω ∈ F → thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
      (fun j t => geomRW W xR j t ω) = ⊤) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
      ∃ (𝓕' : Filtration ℝ≥0 mΩ) (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ),
        IsOptionalHullCoupling κ (xL ω₀) (xR ω₀) ρL ρR (condExpKernel P 𝒢 ω₀) 𝓕' W' VL' VR' B'
          (fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => geomLW W xL i t ω)
            (fun j t => geomRW W xR j t ω)) X ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t, W' t ω = W t ω ∧ (∀ i, VL' i t ω = geomLW W xL i t ω) ∧
          ∀ j, VR' j t ω = geomRW W xR j t ω := by
  have h𝒢m : 𝒢 ≤ mΩ := h𝒢.trans (𝓗.le 0)
  have hFm : MeasurableSet F := h𝒢m _ hF
  by_cases hPF : P F = 0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hPF] with ω hω hωF
    exact absurd hωF hω
  set Q := ProbabilityTheory.cond P F with hQ
  have : IsProbabilityMeasure Q := ProbabilityTheory.cond_isProbabilityMeasure hPF
  set VL := geomLW W xL with hVLdef
  set VR := geomRW W xR with hVRdef
  set thr : Ω → ℝ≥0∞ := fun ω => thresholdTime ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
    (fun j t => VR j t ω) with hthrdef
  -- the deterministic properties of geometric force points
  have hxL₀ : Measurable[𝓗 0] xL := hxL.mono h𝒢 le_rfl
  have hxR₀ : Measurable[𝓗 0] xR := hxR.mono h𝒢 le_rfl
  have hVLa : ∀ i, StronglyAdapted 𝓗 (VL i) := fun i => stronglyAdapted_geomLW hWa hWc hxL₀ i
  have hVRa : ∀ j, StronglyAdapted 𝓗 (VR j) := fun j => stronglyAdapted_geomRW hWa hWc hxR₀ j
  have hordL : ∀ ω t i, VL i t ω ≤ W t ω := fun ω t i => geomLW_le hWc xL ω t i
  have hordR : ∀ ω t j, W t ω ≤ VR j t ω := fun ω t j => le_geomRW hWc xR ω t j
  have hpathL : ∀ ω i, IsForcePath (fun t => W t ω) (fun t => VL i t ω) := fun ω i =>
    isForcePath_geomLW hWc xL ω i
  have hpathR : ∀ ω j, IsForcePath (fun t => W t ω) (fun t => VR j t ω) := fun ω j =>
    isForcePath_geomRW hWc xR ω j
  have hVLc : ∀ i ω, Continuous fun t => VL i t ω := fun i ω => (hpathL ω i).1
  have hVRc : ∀ j ω, Continuous fun t => VR j t ω := fun j ω => (hpathR ω j).1
  have hmergeL : ∀ ω i j s t, s ≤ t → VL i s ω = VL j s ω → VL i t ω = VL j t ω :=
    fun ω i j s t hst h => geomLW_merge hWc xL ω i j s t hst h
  have hmergeR : ∀ ω i j s t, s ≤ t → VR i s ω = VR j s ω → VR i t ω = VR j t ω :=
    fun ω i j s t hst h => geomRW_merge hWc xR ω i j s t hst h
  -- (S) and (L) under the conditioned measure, live event `univ`
  have hlawQ : HasSafeLaw κ ρL ρR Q 𝓗 univ (fun _ => ⊤) W VL VR X := hasSafeLaw_cond (h𝒢 _ hF) hlaw
  have hmemQ : HasSafeMembers Q 𝓗 univ (fun _ => ⊤) W X := hasSafeMembers_cond (h𝒢 _ hF) hmem
  have hthrQ : ∀ᵐ ω ∂Q, thr ω = ⊤ := ae_cond_of_ae hFm hthr
  -- (1) the conditional-law clause at stopping times of the usual augmentation
  set 𝓖 := usualAugmentation 𝓗 Q with h𝓖
  have hXψ : ∀ ψ : TestOn upperHalfPlaneOpens, Measurable fun ω => X ω ψ := fun ψ =>
    ((measurable_pi_apply ψ).comp (Measurable.of_comap_le le_rfl)).comp hX
  have hstopT : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω : Ω | (⊤ : ℝ≥0∞) ≤ t} := fun t => by
    have e : {ω : Ω | (⊤ : ℝ≥0∞) ≤ t} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, top_le_iff, ENNReal.coe_ne_top, mem_empty_iff_false]
    rw [e]
    exact @MeasurableSet.empty _ (𝓗 t)
  have hWaT : AdaptedBefore 𝓗 (fun _ => ⊤) W := adaptedBefore_of_stronglyAdapted hstopT hWa
  have hVLaT : ∀ i, AdaptedBefore 𝓗 (fun _ => ⊤) (VL i) := fun i =>
    adaptedBefore_of_stronglyAdapted hstopT (hVLa i)
  have hVRaT : ∀ j, AdaptedBefore 𝓗 (fun _ => ⊤) (VR j) := fun j =>
    adaptedBefore_of_stronglyAdapted hstopT (hVRa j)
  have hcf := Aux79.isCouplingCharFun_of_hasSafeLaw X hXψ hlawQ
    (ae_of_all _ (Restart.FCDet.isForceReg_thr hW0 hWc xL xR _)) (ae_of_all _ fun ω h => absurd (mem_univ ω) h)
    hWaT hVLaT hVRaT
  -- (2) the mean martingales
  have hnull : ∀ s, MeasurableSet s → Q s = 0 → MeasurableSet[𝓖 0] s := fun s hs h0 =>
    Ito.measurableSet_usualAugmentation_of_null hs h0 0
  have hstopG : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] {ω : Ω | (⊤ : ℝ≥0∞) ≤ t} := fun t =>
    Ito.le_usualAugmentation 𝓗 Q t _ (hstopT t)
  have hWaG : StronglyAdapted 𝓖 W := fun t => (hWa t).mono (Ito.le_usualAugmentation 𝓗 Q t)
  have hVLaG : ∀ i, StronglyAdapted 𝓖 (VL i) := fun i t =>
    (hVLa i t).mono (Ito.le_usualAugmentation 𝓗 Q t)
  have hVRaG : ∀ j, StronglyAdapted 𝓖 (VR j) := fun j t =>
    (hVRa j t).mono (Ito.le_usualAugmentation 𝓗 Q t)
  have hmart : ∀ z ∈ H, IsLocalMartingaleBefore 𝓖 Q
      (fun ω => (QuantumZipper.swallowTime (wpath W ω) z : WithTop ℝ≥0)) (coupProc κ ρL ρR W VL VR z) := by
    intro z hz
    obtain ⟨G, hG, hGae, hloc⟩ := Coupling.MartMeans2.exists_isLocalMartingaleBefore_meanProcOn hnull
      (adaptedBefore_of_stronglyAdapted hstopG hWaG)
      (fun i => adaptedBefore_of_stronglyAdapted hstopG (hVLaG i))
      (fun j => adaptedBefore_of_stronglyAdapted hstopG (hVRaG j))
      (Eventually.of_forall fun ω => ⟨hW0 ω, (hWc ω).continuousOn,
        ⟨fun i => (hVLc i ω).continuousOn, fun j => (hVRc j ω).continuousOn⟩,
        fun t _ => ⟨fun i => hordL ω t i, fun j => hordR ω t j⟩⟩)
      (isAnnouncingSeq_nat 𝓖 Q) (fun φ => integrable_cond (hint φ)) hcf
      (fun ω t => meanExt κ ρL ρR (W t ω) (fun i => VL i t ω) (fun j => VR j t ω))
      (fun ω t => isBoundedHarmonicExtension_meanExt κ ρL ρR _ _ _) hz
    have h := Restart.ConverseBefore.isLocalMartingaleBefore_coupProc_of_meanProcOn hnull hG hGae
      (Restart.ConverseBefore.measurable_coupProc_zero hW0 (fun i => ((hVLa i 0).measurable.mono (𝓗.le 0) le_rfl))
        (fun j => ((hVRa j 0).measurable.mono (𝓗.le 0) le_rfl)) hz) hloc
    exact PhaseSelAdapt.isLocalMartingaleBefore_congr_life (fun ω => min_top_right _) h
  -- (3) Theorem 2.4 with a random initial word: the relative evolution
  have hantiL : ∀ ω i, Antitone fun t => VL i t ω := fun ω i => antitone_geomLW hWc xL ω i
  have hmonoR : ∀ ω j, Monotone fun t => VR j t ω := fun ω j => monotone_geomRW hWc xR ω j
  have hidxL : ∀ ω t, Antitone fun i => VL i t ω := fun ω t => antitone_index_geomLW hWc (hxLa ω) t
  have hidxR : ∀ ω t, Monotone fun j => VR j t ω := fun ω t => monotone_index_geomRW hWc (hxRm ω) t
  have hsep : ∀ ω t, 0 < t → ∀ i j, VL i t ω = W t ω → VR j t ω ≠ W t ω :=
    fun ω t ht i j h => geom_sep hWc xL xR ω t ht i j h
  obtain ⟨-, -, -, -, hB, hWthr, hVLthr, hVRthr, hpath⟩ := PocketWord.isRandomWordEvolution_of_coupProc hκ hW0
    hWc hWaG hVLaG hVRaG hordL hordR hpathL hpathR hantiL hmonoR hidxL hidxR hmergeL hmergeR hsep hmart
  have hE : Aux122Disint.IsRandomWordEvolution κ Q 𝒢 univ xL xR ρL ρR 𝓖 W VL VR
      (fun t ω => martProc (jointρ ρL ρR) W (jointV VL VR) t ω / Real.sqrt κ) thr := by
    refine ⟨h𝒢.trans (Ito.le_usualAugmentation 𝓗 Q 0), MeasurableSet.univ, hxL, hxR, hB, hWthr, hVLthr,
      hVRthr, ?_⟩
    filter_upwards [hpath] with ω hp _
    have eL : (fun i => VL i 0 ω) = xL ω := funext fun i => geomLW_zero hWc hW0 (hxL0 ω i)
    have eR : (fun j => VR j 0 ω) = xR ω := funext fun j => geomRW_zero hWc hW0 (hxR0 ω j)
    have h1 := hp (mem_univ ω)
    rwa [eL, eR] at h1
  -- (4) K2 under the conditioned measure, lifetime the threshold
  have hζ0 : ∀ᵐ ω ∂Q, ω ∈ univ → 0 < thr ω := by
    filter_upwards [hthrQ] with ω h _
    rw [h]
    exact ENNReal.zero_lt_top
  have hstopthr : ∀ t : ℝ≥0, MeasurableSet[𝓗 t] {ω | thr ω ≤ t} :=
    measurableSet_thresholdTime_le hWc hVLc hVRc hWa hVLa hVRa hmergeL hmergeR
  have hK := ae_isOptionalHullCoupling_k hE hX hζ0 h𝒢 (adaptedBefore_of_stronglyAdapted hstopthr hWa)
    (fun i => adaptedBefore_of_stronglyAdapted hstopthr (hVLa i))
    (fun j => adaptedBefore_of_stronglyAdapted hstopthr (hVRa j)) (hasSafeLaw_of_top hlawQ)
    (hasSafeMembers_of_top hmemQ)
  -- (5) back to `P`
  filter_upwards [ae_of_ae_cond hFm hK, ae_condExpKernel_cond_eq h𝒢m hF] with ω₀ hk he hω₀
  rw [← he hω₀]
  exact hk hω₀ (mem_univ ω₀)

end Main

end InteractingSLE.Theorem14.BW1Chain

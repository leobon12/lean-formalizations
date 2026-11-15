/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly3Entr
import InteractingSLE.Spec.Sec7.CounterflowProbTransfer
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Sec7.TraceCodingUse

/-!
# §7.4, Aux. lemma 126: removing the distant marks of a reference (the change of measure)

Packet PROVE-AUX126. Aux. lemma 126's proof (`source/spec/p385-432.md` L256–L316, pp. 399–401), its first part
"An exact stopped two-seed coupling": from a reference evolution with seeds of weights `r_L, r_R > −2` at `0^∓` and
finitely many other marks strictly separated from `0`, whose trace is continuous before its lifetime, the change of
measure (FS11.2)–(FS11.3) removes the force drift of the distant marks through the buffered stop `S_r` (FS11.1),
and the stopped pair is extended to a full two-seed evolution ("Aux. lemma 54 extends our stopped pair …").

This file proves the named input `Sec7.Aux126GirsanovStatement` **outright**, on the driving process alone. The
conclusion of the named input is a statement about the driver of one two-seed evolution, so the whole-field change of
measure is not needed; the driver-level route is the one of Theorem 2.2's uniqueness proof for the admissible
entrances (PROVE-SEC2-PATCH4, `Sec2.Assembly3.exists_twoSeed_cover`):

1. the reference evolution is changed on a null set into a good one (`exists_good_modification_ae`: as
   `Sec2.Assembly3.exists_good_modification`, recording also that the driver and the lifetime are unchanged
   almost surely);
2. choose `r > 0` with `8r` below the distances of the non-seed marks to `0` and `r ≤ 1`, and put `δ = 7r`. Up to the
   localization time `T` (the first time a non-seed mark comes within `δ` of the driver, or the lifetime, capped at
   `1`), Girsanov's theorem (`Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights`) sets the non-seed weights to `0`; under
   the changed measure `Q ≪ P` the seeds form a local two-seed evolution up to `T`, continued after `T` by the maximal
   solution to a full two-seed evolution `G` whose driver agrees with the reference driver on `[0, T]`
   (`exists_twoSeed_cover`, decoded by `driver_eq_of_obsOfCode_eq`);
3. **the buffered stop comes before `T`** (`bufferedStop_le_entT`): the non-seed marks move away from `0`
   (`vL ≤ xL`, `xR ≤ vR`) and the driver stays in `(−r/4, r/4)` before `S_r`, so every non-seed gap exceeds
   `8r − r/4 > δ` through `S_r`; this is the source's "all changed groups stay a positive distance from `W` through
   this stop";
4. `T` is before the lifetime almost surely (Aux. lemma 3, `Sec2.Assembly3.ae_entT_lt_lifetime`), so the reference
   trace through `T` restricts to a trace of `G`'s driver through `S_r` ("Equivalence in (FS11.2) preserves
   continuity of the reference trace through `S_r`").

## Main results

* `Sec7.Aux126.aux126GirsanovStatement : Sec7.Aux126GirsanovStatement`.
* `Sec7.Aux126.aux126StoppedTraceStatement_of_jacobi`, `Sec7.Aux126.lemma725TraceStatement_of_reference`: the
  downstream statements with this input discharged.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec7

namespace Aux126

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 Girsanov

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-! ### Step 1: a good modification with the same driver -/

open Classical in
/-- **A good modification of an evolution, with the same driver and lifetime almost surely**
(`Sec2.Assembly3.exists_good_modification`, whose proof this repeats, records only the killed laws): changed on a
null set, in the usual augmentation, every path is continuous before the lifetime, every Brownian path is
continuous, the initial values hold for every `ω`, the lifetime is positive and null sets are in every `𝓖 t`. -/
theorem exists_good_modification_ae (hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (_ : 𝓖.IsRightContinuous) (W' : ℝ≥0 → Ω → ℝ)
      (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ) (B' : ℝ≥0 → Ω → ℝ)
      (ζ' : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓖 W' VL' VR' B' ζ' ∧
      (∀ ω, ContinuousOn (W' · ω) {t | (t : ℝ≥0∞) < ζ' ω}) ∧
      (∀ i ω, ContinuousOn (VL' i · ω) {t | (t : ℝ≥0∞) < ζ' ω}) ∧
      (∀ j ω, ContinuousOn (VR' j · ω) {t | (t : ℝ≥0∞) < ζ' ω}) ∧
      (∀ ω, Continuous (B' · ω)) ∧ (∀ ω, W' 0 ω = 0) ∧ (∀ i ω, VL' i 0 ω = xL i) ∧
      (∀ j ω, VR' j 0 ω = xR j) ∧ (∀ ω, 0 < ζ' ω) ∧
      (∀ N : Set Ω, MeasurableSet N → P N = 0 → ∀ t, MeasurableSet[𝓖 t] N) ∧
      ∀ᵐ ω ∂P, ζ' ω = ζ ω ∧ ∀ t, W' t ω = W t ω := by
  have hgood : ∀ᵐ ω ∂P, IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) ∧ Continuous (B · ω) :=
    hE.2.2.2.2.and hE.1.1.cont
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodω : ∀ ω, ω ∉ N → IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) ∧ Continuous (B · ω) := fun ω hω => by
    by_contra hc
    exact hω (hNsub hc)
  obtain ⟨hB', hB'c⟩ := Ito.isFilteredBrownianReal_modify hE.1 hNm.compl (by simpa using hN0)
    fun ω hω => (hgoodω ω hω).2
  set 𝓖 := usualAugmentation (Ito.nullAugmented 𝓕 P) P with h𝓖
  have h𝓤 : usualAugmentation 𝓕 P ≤ 𝓖 :=
    Ito.usualAugmentation_mono (Ito.le_nullAugmented 𝓕 P) P
  have hnull : ∀ N' : Set Ω, MeasurableSet N' → P N' = 0 → ∀ t, MeasurableSet[𝓖 t] N' :=
    fun N' hm h0 t => Ito.measurableSet_usualAugmentation_of_null hm h0 t
  have hNt : ∀ t, MeasurableSet[𝓖 t] N := hnull N hNm hN0
  set ζ' : Ω → ℝ≥0∞ := fun ω => if ω ∈ N then ⊤ else ζ ω with hζ'
  have hadapt : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X → ∀ c : ℝ,
      AdaptedBefore 𝓖 ζ' (fun t ω => if ω ∈ N then c else X t ω) := fun {X} hX c t A hA => by
    have e : {ω | (t : ℝ≥0∞) < ζ' ω ∧ (if ω ∈ N then c else X t ω) ∈ A} =
        ({ω | (t : ℝ≥0∞) < ζ ω ∧ X t ω ∈ A} ∩ Nᶜ) ∪ (N ∩ {_ω | c ∈ A}) := by
      ext ω
      by_cases hω : ω ∈ N <;> simp [hζ', hω]
    rw [e]
    exact (h𝓤 t _ (((Ito.le_usualAugmentation 𝓕 P t) _ (hX t A hA)))).inter (hNt t).compl
      |>.union ((hNt t).inter (MeasurableSet.const _))
  have hpathω : ∀ ω, ω ∉ N → IsIntegratedSLEPath a xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (ζ ω) := fun ω hω => (hgoodω ω hω).1
  refine ⟨𝓖, inferInstance, fun t ω => if ω ∈ N then 0 else W t ω,
    fun i t ω => if ω ∈ N then xL i else VL i t ω,
    fun j t ω => if ω ∈ N then xR j else VR j t ω,
    fun t ω => @ite ℝ (ω ∈ Nᶜ) (Classical.propDecidable (ω ∈ Nᶜ)) (B t ω) 0, ζ',
    ⟨Ito.isFilteredBrownianReal_usualAugmentation hB', hadapt hE.2.1 0,
      fun i => hadapt (hE.2.2.1 i) (xL i), fun j => hadapt (hE.2.2.2.1 j) (xR j), ?_⟩,
    fun ω => ?_, fun i ω => ?_, fun j ω => ?_, hB'c, fun ω => ?_, fun i ω => ?_, fun j ω => ?_,
    fun ω => ?_, hnull, ?_⟩
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    have hω' : ω ∈ Nᶜ := hω
    simp only [hω, hω', hζ', ↓reduceIte]
    exact hpathω ω hω
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simp only [hω, hζ', ↓reduceIte]; exact (hpathω ω hω).isForcePath.continuousOn_w
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simp only [hω, hζ', ↓reduceIte]; exact (hpathω ω hω).isForcePath.continuousOn_vL i
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]; exact continuousOn_const
    · simp only [hω, hζ', ↓reduceIte]; exact (hpathω ω hω).isForcePath.continuousOn_vR j
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hpathω ω hω).isForcePath.w_zero
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hpathω ω hω).isForcePath.vL_zero i
  · by_cases hω : ω ∈ N
    · simp only [hω, ↓reduceIte]
    · simp only [hω, ↓reduceIte]; exact (hpathω ω hω).isForcePath.vR_zero j
  · by_cases hω : ω ∈ N
    · simp only [hζ', hω, ↓reduceIte]; exact ENNReal.zero_lt_top
    · simp only [hζ', hω, ↓reduceIte]
      refine pos_iff_ne_zero.2 fun h0 => hthr ?_
      exact (hpathω ω hω).isForcePath.threshold_of_eq_zero h0
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
    simp only [hζ', hω, ↓reduceIte, implies_true, and_self]

/-! ### Step 2: the buffer radius and the seed weights -/

/-- **The buffer radius** (Aux. lemma 126's proof, p. 399: "Choose `r > 0` so that `8r < min_{j∈J} |x_j|`; if `J`
is empty choose any positive `r`"), with `r ≤ 1` so that the buffered stop is before the cap `1` of the
localization time. -/
theorem exists_radius (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ)
    (hL : ∀ i, xL i ≠ 0 → xL i < 0) (hR : ∀ j, xR j ≠ 0 → 0 < xR j) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (∀ i, xL i ≠ 0 → 8 * r < -xL i) ∧ ∀ j, xR j ≠ 0 → 8 * r < xR j := by
  classical
  set gL : Fin (nL + 1) → ℝ := fun i => if xL i = 0 then 1 else -xL i with hgL
  set gR : Fin (nR + 1) → ℝ := fun j => if xR j = 0 then 1 else xR j with hgR
  set mL := Finset.univ.inf' Finset.univ_nonempty gL with hmL
  set mR := Finset.univ.inf' Finset.univ_nonempty gR with hmR
  have hpL : ∀ i, 0 < gL i := fun i => by
    simp only [hgL]
    split_ifs with h
    · exact one_pos
    · linarith [hL i h]
  have hpR : ∀ j, 0 < gR j := fun j => by
    simp only [hgR]
    split_ifs with h
    · exact one_pos
    · exact hR j h
  have hmL0 : 0 < mL := (Finset.lt_inf'_iff _).2 fun i _ => hpL i
  have hmR0 : 0 < mR := (Finset.lt_inf'_iff _).2 fun j _ => hpR j
  have hm0 : 0 < min mL mR := lt_min hmL0 hmR0
  have hr : min 1 (min mL mR / 16) ≤ min mL mR / 16 := min_le_right _ _
  refine ⟨min 1 (min mL mR / 16), lt_min one_pos (by positivity), min_le_left _ _, fun i hi => ?_,
    fun j hj => ?_⟩
  · have h1 : mL ≤ gL i := Finset.inf'_le _ (Finset.mem_univ i)
    have h2 : gL i = -xL i := by simp only [hgL, hi, ↓reduceIte]
    have h3 : min mL mR ≤ mL := min_le_left _ _
    linarith
  · have h1 : mR ≤ gR j := Finset.inf'_le _ (Finset.mem_univ j)
    have h2 : gR j = xR j := by simp only [hgR, hj, ↓reduceIte]
    have h3 : min mL mR ≤ mR := min_le_right _ _
    linarith

/-- The seed group of a word whose only mark at `0` is the first one has the weight of that mark. -/
theorem seedSum_eq {n : ℕ} {x ρ : Fin (n + 1) → ℝ} (h0 : x 0 = 0) (hne : ∀ i, i ≠ 0 → x i ≠ 0) :
    seedSum x ρ = ρ 0 := by
  unfold seedSum
  refine Finset.sum_eq_single_of_mem 0 (by simp [h0]) fun i hi hi0 => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  exact absurd hi (hne i hi0)

/-! ### Step 3: decoding the cover, and the buffered stop before the localization time -/

/-- **The two-seed driver agrees with the reference driver before the localization time**: decoding the identity
`obsOfCode (stCode G) = observe T W …` of `Sec2.Assembly3.exists_twoSeed_cover` (the driver coordinate before the
time coordinate). -/
theorem driver_eq_of_obsOfCode_eq {Ω : Type*} {δ : ℝ} {τ ζG : Ω → ℝ≥0∞} {W Gw Bh : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {Gl Gr : Fin 1 → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hζG : ζG ω = ⊤) (hGw : Continuous (Gw · ω))
    (h : obsOfCode δ xL xR (stCode ζG Gw Gl Gr Bh ω) = Sec2.observe τ W VL VR Bh ω)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ ω) : Gw t ω = W t ω := by
  have h1 := congrArg (fun e : ObsSpace nL nR => (e.1 t).1) h
  have h2 := congrArg (fun e : ObsSpace nL nR => e.2) h
  simp only [obsOfCode, Sec2.observe] at h1 h2
  rw [killed_of_lt ht] at h1
  rw [killed_of_lt (show (t : ℝ≥0∞) < codeT δ xL xR (stCode ζG Gw Gl Gr Bh ω) by rw [h2]; exact ht)] at h1
  rw [← h1]
  have hk : ∀ (X : ℝ≥0 → Ω → ℝ) (u : ℝ≥0), killed ζG X u ω = X u ω := fun X u =>
    killed_of_lt (by rw [hζG]; exact ENNReal.coe_lt_top)
  have hcW : cW (stCode ζG Gw Gl Gr Bh ω) = enc (Gw · ω) := by
    funext n k
    simp [cW, stCode, hk, enc]
  rw [codeW, hcW]
  exact (dec_enc hGw.continuousAt.continuousWithinAt).symm

/-- **The buffered stop comes before the localization time** (Aux. lemma 126's proof, p. 399: "A nonseed right
coordinate is at least `x_j > 8r` and a nonseed left coordinate is at most `x_j < −8r`, so all changed groups stay a
positive distance from `W` through this stop"). Let `T` be the localization time at level `7r` and suppose `T` is
before the lifetime. If a path `w` agrees with the driver up to `T`, then `S_r(w) ≤ T`: otherwise `T < r²/64 ≤ 1`, so
`T` is the first time a non-seed gap is `≤ 7r`, while `|w| < r/4` on `[0, T]` and the non-seed marks have only moved
away from `0`, which keeps every non-seed gap above `8r − r/4`. -/
theorem bufferedStop_le_entT [Nonempty (Fin nL ⊕ Fin nR)] {Ω : Type*} {ζ : Ω → ℝ≥0∞}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ω : Ω} {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hxL : ∀ i, xL i ≠ 0 → 8 * r < -xL i)
    (hxR : ∀ j, xR j ≠ 0 → 8 * r < xR j)
    (hp : IsSLEPathUpTo a xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω)
      (ζ ω))
    (hWc : ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVLc : ∀ i, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hVRc : ∀ j, ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hTζ : entT (7 * r) xL xR ζ W VL VR ω < ζ ω) {w : ℝ≥0 → ℝ}
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ entT (7 * r) xL xR ζ W VL VR ω → w t = W t ω) :
    Dilation.bufferedStop r w ≤ entT (7 * r) xL xR ζ W VL VR ω := by
  by_contra hcon
  rw [not_le] at hcon
  set T := entT (7 * r) xL xR ζ W VL VR ω with hTdef
  set Tn : ℝ≥0 := T.toNNReal with hTndef
  have hTn : (Tn : ℝ≥0∞) = T := ENNReal.coe_toNNReal (entT_ne_top ω)
  rw [Dilation.bufferedStop, lt_min_iff] at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  -- the driver is small up to `T`
  have hsmall : ∀ u : ℝ≥0, u ≤ Tn → |W u ω| < r / 4 := by
    intro u hu
    have huT : (u : ℝ≥0∞) ≤ T := by rw [← hTn]; exact_mod_cast hu
    rw [← hw u huT]
    by_contra hle
    rw [not_lt] at hle
    have hex : Dilation.exitTime r w ≤ u := iInf₂_le u hle
    exact absurd (lt_of_lt_of_le hb2 (hex.trans huT)) (lt_irrefl _)
  -- `T < 1`, so `T` is the hitting time of the gaps
  have hT1 : T < 1 := by
    refine lt_of_lt_of_le hb1 ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : r ^ 2 ≤ 1 := by nlinarith
    linarith
  have hhit : hitTime (killedFam ζ (gapFam (7 * r) xL xR W VL VR)) (7 * r) ω ≤ Tn := by
    rw [hTn]
    have e : T = min (hitTime (killedFam ζ (gapFam (7 * r) xL xR W VL VR)) (7 * r) ω) 1 := rfl
    rcases le_total (hitTime (killedFam ζ (gapFam (7 * r) xL xR W VL VR)) (7 * r) ω) 1 with h | h
    · rw [e, min_eq_left h]
    · rw [e, min_eq_right h] at hT1
      exact absurd hT1 (lt_irrefl _)
  obtain ⟨t, htT, k, hk⟩ := (hitTime_le_iff_of_isClosed
    (isClosed_killedFam (by linarith) (continuousOn_gapFam hWc hVLc hVRc))).1 hhit
  have htζ : (t : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by rw [← hTn]; exact_mod_cast htT) hTζ
  rw [killedFam, killed_of_lt htζ] at hk
  have hwt := abs_lt.1 (hsmall t htT)
  rcases k with i | j
  · simp only [gapFam, Sum.elim_inl] at hk
    split_ifs at hk with hi
    · linarith
    · have := hp.vL_le_xL htζ i
      linarith [hxL i hi]
  · simp only [gapFam, Sum.elim_inr] at hk
    split_ifs at hk with hj
    · linarith
    · have := hp.xR_le_vR htζ j
      linarith [hxR j hj]

/-! ### Step 4: the driving part of the reference, and Aux. lemma 126's change of measure -/

/-- **The driving part of the hypothesis of Aux. lemma 126** (`Aux126Reference` without the field): an ordered force
word whose first mark on each side sits at the origin with weight `rL`, `rR` and whose other marks are strictly
separated from `0`, and one integrated evolution of it (on a probability space in `Type v`) whose driver almost surely
has a generating trace on `[0, T]` for every `T` before the lifetime. The change of measure of Aux. lemma 126 uses
only this. -/
def Aux126DriverReference (κ rL rR : ℝ) : Prop :=
  ∃ (nL nR : ℕ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ),
    IsOrderedForceWord xL xR ∧ xL 0 = 0 ∧ xR 0 = 0 ∧ (∀ i, i ≠ 0 → xL i < 0) ∧
      (∀ i, i ≠ 0 → 0 < xR i) ∧ ρL 0 = rL ∧ ρR 0 = rR ∧
      ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ ∧
          ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
            ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η

/-- The hypothesis of Aux. lemma 126 contains its driving part (`IsOptionalHullCoupling` contains the evolution). -/
theorem aux126DriverReference_of_reference {κ rL rR : ℝ} (href : Aux126Reference.{v} κ rL rR) :
    Aux126DriverReference.{v} κ rL rR := by
  obtain ⟨nL, nR, xL, xR, ρL, ρR, hF, hxL0, hxR0, hxLn, hxRp, hρL, hρR, Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ,
    _, hC, htr, -⟩ := href
  exact ⟨nL, nR, xL, xR, ρL, ρR, hF, hxL0, hxR0, hxLn, hxRp, hρL, hρR, Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ,
    hC.1, htr⟩

/-- **Aux. lemma 126, the change of measure, from the driving part of the reference** (pp. 399–401, (FS11.1)–(FS11.3)
and the extension of the stopped pair): there are a buffer radius `r > 0` and one integrated two-seed evolution with
the seed weights `r_L, r_R` whose driver almost surely has a generating trace through its buffered stop `S_r`. -/
theorem exists_twoSeed_bufferedTrace {κ : ℝ} (hκ : 0 < κ) {rL rR : ℝ} (hrL : -2 < rL) (hrR : -2 < rR)
    (href : Aux126DriverReference.{v} κ rL rR) :
    ∃ r : ℝ, 0 < r ∧
      ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
        (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ ∧
          ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
            IsGeneratingTrace (fun t => W t ω) (Dilation.bufferedStop r fun t => W t ω) η := by
  obtain ⟨nL, nR, xL, xR, ρL, ρR, hF, hxL0, hxR0, hxLn, hxRp, hρL, hρR, Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ,
    hE, htr⟩ := href
  have hxL : ∀ i, xL i ≠ 0 → xL i < 0 := fun i hi => hxLn i fun h0 => hi (h0 ▸ hxL0)
  have hxR : ∀ j, xR j ≠ 0 → 0 < xR j := fun j hj => hxRp j fun h0 => hj (h0 ▸ hxR0)
  have hsL : seedSum xL ρL = rL := by
    rw [seedSum_eq hxL0 fun i hi => (hxLn i hi).ne, hρL]
  have hsR : seedSum xR ρR = rR := by
    rw [seedSum_eq hxR0 fun j hj => (hxRp j hj).ne', hρR]
  have hthr : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR :=
    (not_thr_iff_seedSum xL xR ρL ρR).2 ⟨by rw [hsL]; exact hrL, by rw [hsR]; exact hrR⟩
  obtain ⟨r, hr0, hr1, hrL', hrR'⟩ := exists_radius xL xR hxL hxR
  have hδ : 0 < 7 * r := by linarith
  have hδL : ∀ i, xL i ≠ 0 → 7 * r < -xL i := fun i hi => by linarith [hrL' i hi]
  have hδR : ∀ j, xR j ≠ 0 → 7 * r < xR j := fun j hj => by linarith [hrR' j hj]
  -- Step 1: a good modification
  obtain ⟨𝓖, h𝓖, W', VL', VR', B', ζ', hE', hWc, hVLc, hVRc, hBc, hW0, hVL0, hVR0, hζ0, hnull, hae⟩ :=
    exists_good_modification_ae hthr hE
  have := h𝓖
  set T := entT (7 * r) xL xR ζ' W' VL' VR' with hTdef
  set θ := weightDrift κ (7 * r) ρL (seedW xL ρL) ρR (seedW xR ρR) T ζ' W' VL' VR' with hθdef
  set Q := girsanovMeasure P 𝓖 B' θ (1 + 1) with hQdef
  have hQP : Q ≪ P := withDensity_absolutelyContinuous _ _
  -- Step 2: Girsanov and the continuation to a two-seed evolution
  obtain ⟨Gw, Gl, Gr, ζG, hQ, hG, hobs⟩ := exists_twoSeed_cover hκ hF hδ hδL hδR hxL0 hxR0 hthr hE' hWc hVLc
    hVRc hBc hW0 hVL0 hVR0 hζ0 hnull
  simp only [hsL, hsR] at hG
  refine ⟨r, hr0, Ω, mΩ, Q, hQ, 𝓖, Gw, Gl, Gr, girsanovProcess B' θ, ζG, hG, ?_⟩
  -- Step 3: the reference trace through `T` is a trace of the two-seed driver through `S_r`
  have hTlt : ∀ᵐ ω ∂P, T ω < ζ' ω := ae_entT_lt_lifetime hκ hδ hxL0 hthr hE' hxR0
  have htr' : ∀ᵐ ω ∂P, ∀ T' : ℝ≥0, (T' : ℝ≥0∞) < ζ' ω →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) T' η := by
    filter_upwards [htr, hae] with ω hω hω'
    intro T' hT'
    rw [hω'.1] at hT'
    obtain ⟨η, hη⟩ := hω T' hT'
    have e : (fun t => W' t ω) = fun t => W t ω := funext hω'.2
    exact ⟨η, e ▸ hη⟩
  have hζG : ∀ᵐ ω ∂Q, ζG ω = ⊤ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed hκ hG hrL hrR
  have hT0 : ∀ ω, 0 < T ω := (entT_good hδ hδL hδR 0 hE'.2.1 hE'.2.2.1 hE'.2.2.2.1 hWc hVLc hVRc hW0 hVL0
    hVR0 hζ0).2.2.1
  filter_upwards [hobs, hζG, hG.2.2.2.2, hQP.ae_le hTlt, hQP.ae_le htr', hQP.ae_le hE'.2.2.2.2]
    with ω hob hζω hpG hlt htrω hp
  -- continuity of the two-seed driver
  have hpG' := hpG.isForcePath
  rw [hζω] at hpG'
  have huniv : {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} = univ := eq_univ_of_forall fun _ => ENNReal.coe_lt_top
  have hGwc : Continuous (Gw · ω) := continuousOn_univ.1 (huniv ▸ hpG'.continuousOn_w)
  -- agreement with the reference driver on `[0, T]`
  have hlt' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T ω → Gw t ω = W' t ω := fun t ht =>
    driver_eq_of_obsOfCode_eq hζω hGwc hob ht
  set Tn : ℝ≥0 := (T ω).toNNReal with hTndef
  have hTn : (Tn : ℝ≥0∞) = T ω := ENNReal.coe_toNNReal (entT_ne_top ω)
  have hle' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T ω → Gw t ω = W' t ω := by
    intro t ht
    have ht' : t ≤ Tn := by rw [← hTn] at ht; exact_mod_cast ht
    rcases lt_or_eq_of_le ht' with h' | h'
    · exact hlt' t (by rw [← hTn]; exact_mod_cast h')
    · rw [h']
      have hTn0 : 0 < Tn := by
        have : (0 : ℝ≥0∞) < Tn := by rw [hTn]; exact hT0 ω
        exact_mod_cast this
      have hIic : Iic Tn ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ' ω} := fun s hs =>
        lt_of_le_of_lt (by rw [← hTn]; exact_mod_cast hs) hlt
      exact eq_of_eqOn_Iio hTn0 hGwc.continuousOn ((hWc ω).mono hIic) fun s hs =>
        hlt' s (by rw [← hTn]; exact_mod_cast hs)
  have hS : Dilation.bufferedStop r (fun t => Gw t ω) ≤ T ω :=
    bufferedStop_le_entT hr0 hr1 hrL' hrR' (hp.isSLEPathUpTo le_rfl) (hWc ω) (fun i => hVLc i ω)
      (fun j => hVRc j ω) hlt hle'
  obtain ⟨η, hη⟩ := htrω Tn (by rw [hTn]; exact hlt)
  exact ⟨η, IsGeneratingTrace.congr_lt (hη.mono (by rw [hTn]; exact hS)) fun t ht =>
    hlt' t (lt_of_lt_of_le ht hS)⟩


/-- **Aux. lemma 126, the change of measure** (`Sec7.Aux126GirsanovStatement`; pp. 399–401): from a reference as in
`Aux126Reference` there are a buffer radius `r > 0` and one integrated two-seed evolution with the seed weights
`r_L, r_R` whose driver almost surely has a generating trace through its buffered stop `S_r`. The reference's field
and its determination are not used: the conclusion concerns the driving process only. -/
theorem aux126GirsanovStatement : Aux126GirsanovStatement.{v} :=
  fun _ hκ _ _ hrL hrR href => exists_twoSeed_bufferedTrace hκ hrL hrR (aux126DriverReference_of_reference href)

/-! ### Consequences: Lemma 7.25's trace from the driving part of its reference -/

/-- **The driving part of the reference of Lemma 7.25** (`Lemma725ReferenceStatement` with `Aux126DriverReference`
in place of `Aux126Reference`): for `κ' > 4` and `ρ^L, ρ^R ∈ (−2, κ'/2 − 4)` some word with these seed weights and
separated other marks has an evolution whose trace is continuous before its lifetime. -/
def Lemma725DriverReferenceStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
    Aux126DriverReference.{v} κ rL rR

theorem lemma725DriverReferenceStatement_of_reference (h : Lemma725ReferenceStatement.{v}) :
    Lemma725DriverReferenceStatement.{v} :=
  fun κ hκ rL rR hL hLd hR hRd => aux126DriverReference_of_reference (h κ hκ rL rR hL hLd hR hRd)

/-- **Aux. lemma 126, the stopped transfer, from the driving part of the reference**: every integrated two-seed
evolution with the seed weights almost surely has a generating trace through the buffered stop `S_r`
(`exists_twoSeed_bufferedTrace`, then the law transfer `ae_transfer_of_coding` through the proved measurable coding
`Coding.stoppedTraceCodingStatement`). -/
theorem exists_bufferedStop_trace_of_driverReference {κ : ℝ} (hκ : 0 < κ) {rL rR : ℝ} (hL : -2 < rL)
    (hR : -2 < rR) (href : Aux126DriverReference.{v} κ rL rR) :
    ∃ r : ℝ, 0 < r ∧ ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ,
          IsGeneratingTrace (fun t => W t ω) (Dilation.bufferedStop r fun t => W t ω) η := by
  obtain ⟨r, hr, Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀, htr₀⟩ :=
    exists_twoSeed_bufferedTrace hκ hL hR href
  obtain ⟨G, hG, hGp⟩ := Coding.stoppedTraceCodingStatement r hr
  refine ⟨r, hr, fun P _ 𝓕 W VL VR B ζ hE => ?_⟩
  exact ae_transfer_of_coding (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR jacobiDiffusionExistsStatement hG
    hGp hE₀ htr₀ hE

/-- **Lemma 7.25, finite-time continuity** (p. 413), `LP.Lemma725TraceStatement`, from the driving part of its
reference alone: the stopped transfer (`exists_bufferedStop_trace_of_driverReference`), the infinite two-seed lifetime
and the dilation step (`Dilation.ae_isGeneratingTrace_of_bufferedStop`). -/
theorem lemma725TraceStatement_of_driverReference (hRef : Lemma725DriverReferenceStatement.{v}) :
    LP.Lemma725TraceStatement.{u} := by
  intro κ hκ rL rR hL hLd hR hRd Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨r, hr, hstop⟩ :=
    exists_bufferedStop_trace_of_driverReference (by linarith) hL hR (hRef κ hκ rL rR hL hLd hR hRd)
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := Sec2.Assembly2.ae_lifetime_eq_top_twoSeed (by linarith) hE hL hR
  exact Dilation.ae_isGeneratingTrace_of_bufferedStop hr hstop hE hζ

/-- **Aux. lemma 126, the stopped transfer** (`Aux126StoppedTraceStatement`), with every input discharged. -/
theorem aux126StoppedTraceStatement : Aux126StoppedTraceStatement.{u, v} :=
  aux126StoppedTraceStatement_of_aux126Girsanov aux126GirsanovStatement

/-- **Lemma 7.25, finite-time continuity** (p. 413), `LP.Lemma725TraceStatement`, from the reference of Lemma 7.25
(Aux. lemmas 130, 119–125, 127) alone: the change of measure of Aux. lemma 126 is proved. -/
theorem lemma725TraceStatement_of_reference (hRef : Lemma725ReferenceStatement.{v}) :
    LP.Lemma725TraceStatement.{u} :=
  lemma725TraceStatement_of_driverReference (lemma725DriverReferenceStatement_of_reference hRef)

end Aux126

end Sec7

end InteractingSLE

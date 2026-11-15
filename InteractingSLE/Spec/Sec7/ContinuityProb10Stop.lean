import InteractingSLE.Spec.Sec7.LocalExtJCont
import InteractingSLE.Spec.Sec7.ContinuityProb4Band
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart

/-!
# A local evolution of a complete word has a trace up to its horizon, at any start, given a good stop

Packet PROVE-TRACECLOSE (the two-sided seed of LP9). PROVE-SEC7-C10's R5
(`Sec2.IsSLEEvolutionUpTo.ae_trace_of_complete`) needs a separated start: it compares the local evolution with a full
evolution on another space through pathwise uniqueness, which fails at a two-sided seed. Here the full evolution is
built on the same space: if a positive finite stopping time `T` lies almost surely before the horizon `τ` and the word
seen from the driver is good at `T`, the local evolution stopped at `T` and continued by the maximal solution driven
by the increments of the Brownian motion after `T` (`Sec2.Assembly3.isIntegratedSLEEvolution_contClosed`, as in
`LocalExt.IsStoppedSeedCoupling.exists_seedCont`) is an integrated evolution `G` of the same word. Completeness gives
`G` a trace up to its lifetime; `G` agrees with the local evolution before `T`, it lives past `T`
(`lt_lifetime_of_agree`: an admissible continuous left limit is not a lifetime), and after `T` both solve the equations
from the same good word with the same Brownian increments, so they agree before `τ` and `τ ≤ ζ_G`
(`Band.le_lifetime_of_upTo` for the restarted paths, `Sec2.IsSLEPathUpTo.shift`, `IsIntegratedSLEPath.shift`).

## Main results

* `SeedStop.lt_lifetime_of_agree`;
* **`SeedStop.ae_trace_of_complete_of_stop`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace SeedStop

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 LocalExt

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A full solution agreeing with a local one before a time `T` strictly inside the local horizon lives past
`T`**: otherwise the state of the full solution would have the admissible continuous left limit of the local one at
its lifetime (or the lifetime would be `0` with a threshold at the start). -/
theorem lt_lifetime_of_agree {w w' : ℝ≥0 → ℝ} {vL vL' : Fin nL → ℝ≥0 → ℝ} {vR vR' : Fin nR → ℝ≥0 → ℝ}
    {b b' : ℝ≥0 → ℝ} {τ ζ : ℝ≥0∞} (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    (h' : IsIntegratedSLEPath a xL xR ρL ρR w' vL' vR' b' ζ) {T : ℝ≥0} (hTτ : (T : ℝ≥0∞) < τ)
    (hag : ∀ t : ℝ≥0, t < T → w t = w' t ∧ (∀ i, vL i t = vL' i t) ∧ ∀ j, vR j t = vR' j t) :
    (T : ℝ≥0∞) < ζ := by
  by_contra hle
  rw [not_lt] at hle
  have hfin : ζ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  set Z := ζ.toNNReal with hZ
  have hZ' : (Z : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hfin
  have hZT : Z ≤ T := by rw [← ENNReal.coe_le_coe, hZ']; exact hle
  have hZτ : (Z : ℝ≥0∞) < τ := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hZT) hTτ
  have hp := h'.isForcePath
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ Z) with h0 | h0
  · have hz : ζ = 0 := by rw [← hZ', ← h0]; rfl
    have hthr := hp.threshold_of_eq_zero hz
    have hnt := h.not_threshold (t := 0) (by rw [← h0] at hZτ; exact_mod_cast hZτ)
    rw [h.w_zero] at hnt
    have e1 : (fun i => vL i 0) = xL := funext h.vL_zero
    have e2 : (fun j => vR j 0) = xR := funext h.vR_zero
    rw [e1, e2] at hnt
    exact hnt hthr
  · have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < τ} := isOpen_lt ENNReal.continuous_coe continuous_const
    have hca : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < τ} → ContinuousAt f Z :=
      fun hf => hf.continuousAt (hopen.mem_nhds hZτ)
    have hcont : ContinuousAt (fun t => (w t, fun i => vL i t, fun j => vR j t)) Z :=
      (hca h.continuousOn_w).prodMk ((continuousAt_pi.2 fun i => hca (h.continuousOn_vL i)).prodMk
        (continuousAt_pi.2 fun j => hca (h.continuousOn_vR j)))
    have hlim : Tendsto (fun t => (w' t, fun i => vL' i t, fun j => vR' j t)) (𝓝[<] Z)
        (𝓝 (w Z, fun i => vL i Z, fun j => vR j Z)) := by
      refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      obtain ⟨e1, e2, e3⟩ := hag t (lt_of_lt_of_le ht hZT)
      simp only [e1, e2, e3]
    exact h.not_threshold hZτ (hp.threshold_of_tendsto h0 hZ' hlim)


open Classical in
/-- **R5 at any start, given a good stop.** Let `(W, V, B)` be a local integrated `SLE_κ(ρ)` evolution before `τ` of a
complete word, and `T` a positive finite stopping time (of the usual augmentation) almost surely before `τ` at which
the word seen from the driver is almost surely good. Then almost surely the driver has a generating trace on
`[0, τ]`, transient when `τ = ∞`. -/
theorem ae_trace_of_complete_of_stop {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓘 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞} (hκ : 0 < κ)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR Q 𝓘 W VL VR B τ)
    (hc : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (usualAugmentation 𝓘 Q) fun ω => (T ω : WithTop ℝ≥0)) (hT0 : ∀ ω, 0 < T ω)
    (hTτ : ∀ᵐ ω ∂Q, (T ω : ℝ≥0∞) < τ ω) (hgood : ∀ᵐ ω ∂Q, GoodWord ρL ρR (contWord W VL VR T ω)) :
    ∀ᵐ ω ∂Q, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (τ ω) η ∧
      (τ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  set 𝓖 := usualAugmentation 𝓘 Q with h𝓖
  have h𝓘𝓖 : 𝓘 ≤ 𝓖 := Ito.le_usualAugmentation 𝓘 Q
  obtain ⟨B', -, hB'c, hB'br, hB'ae⟩ := Sec2.Restart.exists_continuous_version hE.brownian
  -- the good event
  have hgoodAll : ∀ᵐ ω ∂Q, IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (τ ω) ∧ (T ω : ℝ≥0∞) < τ ω ∧
      GoodWord ρL ρR (contWord W VL VR T ω) ∧ ∀ t, B' t ω = B t ω := by
    filter_upwards [hE.ae_path, hTτ, hgood, hB'ae] with ω h1 h2 h3 h4 using ⟨h1, h2, h3, h4⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgoodAll)
  have hgoodN : ∀ ω, ω ∉ N → IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (fun t => B t ω) (τ ω) ∧ (T ω : ℝ≥0∞) < τ ω ∧
      GoodWord ρL ρR (contWord W VL VR T ω) ∧ ∀ t, B' t ω = B t ω :=
    fun ω hω => not_not.1 fun h => hω (hNsub h)
  have hN𝓖 : ∀ t, MeasurableSet[𝓖 t] N := fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hNae : ∀ᵐ ω ∂Q, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the stop, `1` on the null set
  set Sn : Ω → ℝ≥0 := fun ω => if ω ∈ N then 1 else T ω with hSn
  have hSnT : ∀ ω, ω ∉ N → Sn ω = T ω := fun ω hω => by simp only [hSn, hω, ↓reduceIte]
  have hTlt : ∀ (t : ℝ≥0), MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < (T ω : ℝ≥0∞)} := fun t => by
    have h := (hT t).compl
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, not_le, ENNReal.coe_lt_coe]
    exact WithTop.coe_lt_coe.symm
  have hS : IsStoppingTime 𝓖 fun ω => (Sn ω : WithTop ℝ≥0) := fun t => by
    have e : {ω | (Sn ω : WithTop ℝ≥0) ≤ t} = (N ∩ {_ω | (1 : ℝ≥0) ≤ t}) ∪ (Nᶜ ∩ {ω | (T ω : WithTop ℝ≥0) ≤ t}) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp only [hSn, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and, mem_compl_iff,
          not_true_eq_false, false_and, or_false, WithTop.coe_le_coe]
      · simp only [hSn, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, false_and, mem_compl_iff,
          not_false_eq_true, true_and, false_or]
    rw [e]
    exact ((hN𝓖 t).inter (MeasurableSet.const _)).union ((hN𝓖 t).compl.inter (hT t))
  have hS0 : ∀ ω, 0 < Sn ω := fun ω => by
    by_cases hω : ω ∈ N
    · simp [hSn, hω]
    · rw [hSnT ω hω]; exact hT0 ω
  -- the processes killed on `N`, adapted before the stop
  set kill : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ := fun X t ω => if ω ∈ N then 0 else X t ω with hkill
  have hkillA : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓘 τ X →
      AdaptedBefore 𝓖 (fun ω => ((Sn ω : WithTop ℝ≥0) : ℝ≥0∞)) (kill X) := by
    intro X hX t A hA
    have e : {ω | (t : ℝ≥0∞) < ((Sn ω : WithTop ℝ≥0) : ℝ≥0∞) ∧ kill X t ω ∈ A} =
        (N ∩ {_ω | (t : ℝ≥0∞) < ((1 : ℝ≥0) : ℝ≥0∞) ∧ (0 : ℝ) ∈ A}) ∪
          (Nᶜ ∩ ({ω | (t : ℝ≥0∞) < (T ω : ℝ≥0∞)} ∩ {ω | (t : ℝ≥0∞) < τ ω ∧ X t ω ∈ A})) := by
      ext ω
      by_cases hω : ω ∈ N
      · simp only [hSn, hkill, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, true_and, mem_compl_iff,
          not_true_eq_false, false_and, or_false]
        rfl
      · have hTτ' := (hgoodN ω hω).2.1
        simp only [hSn, hkill, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_inter_iff, false_and, mem_compl_iff,
          not_false_eq_true, true_and, false_or]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h1.trans hTτ', h2⟩
        · rintro ⟨h1, -, h2⟩
          exact ⟨h1, h2⟩
    rw [e]
    exact ((hN𝓖 t).inter (MeasurableSet.const _)).union ((hN𝓖 t).compl.inter ((hTlt t).inter
      (h𝓘𝓖 t _ (hX t A hA))))
  -- the stopped processes
  set mod : (ℝ≥0 → Ω → ℝ) → ℝ≥0 → Ω → ℝ :=
    fun X t ω => if ω ∈ N then 0 else stopVal (kill X) (fun ω => (Sn ω : WithTop ℝ≥0)) t ω with hmod
  have hmodm : ∀ X : ℝ≥0 → Ω → ℝ, AdaptedBefore 𝓘 τ X → ∀ t, Measurable[𝓖 t] (mod X t) := fun X hX t => by
    let _ : MeasurableSpace Ω := 𝓖 t
    exact Measurable.ite (hN𝓖 t) measurable_const (measurable_stopVal_le hS (hkillA X hX) t)
  have hcontX : ∀ ω, ω ∉ N → ∀ X : ℝ≥0 → Ω → ℝ, ContinuousOn (fun t => X t ω) (Iic (T ω)) →
      ∀ t, mod X t ω = X (min t (T ω)) ω := fun ω hω X hX t => by
    have hSω : (Sn ω : WithTop ℝ≥0) = ((T ω : ℝ≥0) : WithTop ℝ≥0) := by rw [hSnT ω hω]
    have hk : (fun t => kill X t ω) = fun t => X t ω := funext fun t => by simp only [hkill, hω, ↓reduceIte]
    have hc : ContinuousOn (fun t => kill X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (Sn ω : WithTop ℝ≥0)} := by
      rw [hk, hSω]
      refine hX.mono fun s hs => ?_
      exact WithTop.coe_le_coe.1 hs
    simp only [hmod, hω, ↓reduceIte]
    rw [stopVal_eq (S := fun ω => (Sn ω : WithTop ℝ≥0)) (ω := ω) (WithTop.coe_pos.2 (hS0 ω)) WithTop.coe_ne_top hc t,
      stopAt_of_eq_coe (τ := fun ω => (Sn ω : WithTop ℝ≥0)) (ω := ω) hSω t]
    simp only [hkill, hω, ↓reduceIte]
  -- continuity of the local coordinates on `[0, T]`
  have hIic : ∀ ω, ω ∉ N → ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < τ ω} →
      ContinuousOn f (Iic (T ω)) := fun ω hω f hf =>
    hf.mono fun s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) (hgoodN ω hω).2.1
  have hcW : ∀ ω, ω ∉ N → ContinuousOn (fun t => W t ω) (Iic (T ω)) := fun ω hω =>
    hIic ω hω (hgoodN ω hω).1.continuousOn_w
  have hcVL : ∀ i ω, ω ∉ N → ContinuousOn (fun t => VL i t ω) (Iic (T ω)) := fun i ω hω =>
    hIic ω hω ((hgoodN ω hω).1.continuousOn_vL i)
  have hcVR : ∀ j ω, ω ∉ N → ContinuousOn (fun t => VR j t ω) (Iic (T ω)) := fun j ω hω =>
    hIic ω hω ((hgoodN ω hω).1.continuousOn_vR j)
  have hcmod : ∀ X : ℝ≥0 → Ω → ℝ, (∀ ω, ω ∉ N → ContinuousOn (fun t => X t ω) (Iic (T ω))) →
      ∀ ω, Continuous (mod X · ω) := fun X hX ω => by
    by_cases hω : ω ∈ N
    · simp only [hmod, hω, ↓reduceIte]; exact continuous_const
    · have e : (mod X · ω) = fun t => X (min t (T ω)) ω := funext (hcontX ω hω X (hX ω hω))
      rw [e]
      exact (hX ω hω).comp_continuous (continuous_id.min continuous_const) fun t => mem_Iic.2 (min_le_right _ _)
  have hmod_lt : ∀ ω, ω ∉ N → ∀ X : ℝ≥0 → Ω → ℝ, ContinuousOn (fun t => X t ω) (Iic (T ω)) →
      ∀ t : ℝ≥0, t ≤ T ω → mod X t ω = X t ω := fun ω hω X hX t ht => by
    rw [hcontX ω hω X hX, min_eq_left ht]
  set W' := mod W with hW'
  set VL' : Fin nL → ℝ≥0 → Ω → ℝ := fun i => mod (VL i) with hVL'
  set VR' : Fin nR → ℝ≥0 → Ω → ℝ := fun j => mod (VR j) with hVR'
  -- the local path up to the stop and the good word there
  have hpath : ∀ᵐ ω ∂Q, IsSLEPathUpTo κ xL xR ρL ρR (W' · ω) (fun i t => VL' i t ω) (fun j t => VR' j t ω)
      (B' · ω) (Sn ω) := by
    filter_upwards [hNae] with ω hω
    obtain ⟨hp, hTτ', -, hB'⟩ := hgoodN ω hω
    rw [hSnT ω hω]
    have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (T ω : ℝ≥0∞) → t ≤ T ω := fun t ht => (ENNReal.coe_lt_coe.1 ht).le
    refine isSLEPathUpTo_congr (hp.mono hTτ'.le) (hmod_lt ω hω W (hcW ω hω) 0 zero_le)
      (fun i => hmod_lt ω hω _ (hcVL i ω hω) 0 zero_le) (fun j => hmod_lt ω hω _ (hcVR j ω hω) 0 zero_le)
      (fun t ht => hmod_lt ω hω W (hcW ω hω) t (hle t ht))
      (fun t ht i => hmod_lt ω hω _ (hcVL i ω hω) t (hle t ht))
      (fun t ht j => hmod_lt ω hω _ (hcVR j ω hω) t (hle t ht)) (fun t _ => hB' t)
  have hword : ∀ ω, ω ∉ N → contWord W' VL' VR' Sn ω = contWord W VL VR T ω := fun ω hω => by
    simp only [contWord, hW', hVL', hVR', hSnT ω hω, hmod_lt ω hω W (hcW ω hω) _ le_rfl,
      hmod_lt ω hω _ (hcVL _ ω hω) _ le_rfl, hmod_lt ω hω _ (hcVR _ ω hω) _ le_rfl]
  have hgw : ∀ᵐ ω ∂Q, GoodWord ρL ρR (contWord W' VL' VR' Sn ω) := by
    filter_upwards [hNae] with ω hω
    rw [hword ω hω]
    exact (hgoodN ω hω).2.2.1
  -- the continuation is an integrated evolution
  have hG := isIntegratedSLEEvolution_contClosed (P := Q) (𝓕 := 𝓖) hκ hB'br hB'c (hmodm W hE.adapted_W)
    (fun i => hmodm _ (hE.adapted_VL i)) (fun j => hmodm _ (hE.adapted_VR j)) (hcmod W hcW)
    (fun i => hcmod _ (hcVL i)) (fun j => hcmod _ (hcVR j)) hpath hS hS0 hgw
  have htr := hc Q 𝓖 _ _ _ B' _ hG
  filter_upwards [htr, hG.2.2.2.2, hNae] with ω hηω hGp hω
  obtain ⟨η, hη, htrans⟩ := hηω
  obtain ⟨hp, hTτ', hgw', hB'⟩ := hgoodN ω hω
  set gw : ℝ≥0 → ℝ := fun t => (contState κ ρL ρR W' VL' VR' B' Sn t ω).1 with hgw
  set gL : Fin nL → ℝ≥0 → ℝ := fun i t => (contState κ ρL ρR W' VL' VR' B' Sn t ω).2.1 i with hgL
  set gR : Fin nR → ℝ≥0 → ℝ := fun j t => (contState κ ρL ρR W' VL' VR' B' Sn t ω).2.2 j with hgR
  set ζG : ℝ≥0∞ := (Sn ω : ℝ≥0∞) + contLife κ ρL ρR W' VL' VR' B' Sn ω with hζG
  have hSlt : ∀ t : ℝ≥0, t < T ω → t < Sn ω := fun t ht => by rw [hSnT ω hω]; exact ht
  -- agreement before the stop
  have hagT : ∀ t : ℝ≥0, t < T ω → W t ω = gw t ∧ (∀ i, VL i t ω = gL i t) ∧ ∀ j, VR j t ω = gR j t := by
    intro t ht
    refine ⟨?_, fun i => ?_, fun j => ?_⟩
    · show W t ω = concatAt (Sn ω) (W' · ω) _ _ t
      rw [concatAt_of_lt (hSlt t ht)]; exact (hmod_lt ω hω W (hcW ω hω) t ht.le).symm
    · show VL i t ω = concatAt (Sn ω) (VL' i · ω) _ _ t
      rw [concatAt_of_lt (hSlt t ht)]; exact (hmod_lt ω hω _ (hcVL i ω hω) t ht.le).symm
    · show VR j t ω = concatAt (Sn ω) (VR' j · ω) _ _ t
      rw [concatAt_of_lt (hSlt t ht)]; exact (hmod_lt ω hω _ (hcVR j ω hω) t ht.le).symm
  have hTζ : ((T ω : ℝ≥0) : ℝ≥0∞) < ζG := lt_lifetime_of_agree hp hGp hTτ' hagT
  -- the continuation equals the local solution at the stop
  have hGI : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζG} → ContinuousOn f (Iic (T ω)) := fun hf =>
    hf.mono fun s hs => lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) hTζ
  have hGT : gw (T ω) = W (T ω) ω := (eq_of_eqOn_Iio (hT0 ω) (hcW ω hω) (hGI (hGp.isSLEPathUpTo le_rfl).continuousOn_w)
    fun s hs => (hagT s hs).1).symm
  have hGLT : ∀ i, gL i (T ω) = VL i (T ω) ω := fun i => (eq_of_eqOn_Iio (hT0 ω) (hcVL i ω hω)
    (hGI ((hGp.isSLEPathUpTo le_rfl).continuousOn_vL i)) fun s hs => (hagT s hs).2.1 i).symm
  have hGRT : ∀ j, gR j (T ω) = VR j (T ω) ω := fun j => (eq_of_eqOn_Iio (hT0 ω) (hcVR j ω hω)
    (hGI ((hGp.isSLEPathUpTo le_rfl).continuousOn_vR j)) fun s hs => (hagT s hs).2.2 j).symm
  -- after the stop: both solve from the same good word with the same increments
  have hLs := hp.shift hTτ'
  have hGs := hGp.shift hTζ
  have eL : (fun i => gL i (T ω) - gw (T ω)) = fun i => VL i (T ω) ω - W (T ω) ω :=
    funext fun i => by rw [hGLT i, hGT]
  have eR : (fun j => gR j (T ω) - gw (T ω)) = fun j => VR j (T ω) ω - W (T ω) ω :=
    funext fun j => by rw [hGRT j, hGT]
  have eB : (fun t => B' t ω) = fun t => B t ω := funext hB'
  rw [eL, eR, eB, hB' (T ω)] at hGs
  have hsep : ∀ i j, VL i (T ω) ω - W (T ω) ω < VR j (T ω) ω - W (T ω) ω := hgw'.1
  obtain ⟨hle, hag⟩ := Band.le_lifetime_of_upTo hsep hLs hGs
  have hτζ : τ ω ≤ ζG := by
    calc τ ω = (T ω : ℝ≥0∞) + (τ ω - T ω) := (add_tsub_cancel_of_le hTτ'.le).symm
      _ ≤ (T ω : ℝ≥0∞) + (ζG - T ω) := add_le_add le_rfl hle
      _ = ζG := add_tsub_cancel_of_le hTζ.le
  have hall : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω → W t ω = gw t := by
    intro t ht
    rcases lt_or_ge t (T ω) with h | h
    · exact (hagT t h).1
    · obtain ⟨s, rfl⟩ : ∃ s, t = T ω + s := ⟨t - T ω, (add_tsub_cancel_of_le h).symm⟩
      have hs : (s : ℝ≥0∞) < τ ω - T ω := Assembly2.coe_lt_sub_iff.2 ht
      have h1 := (hag s hs).1
      simp only [shiftAt] at h1
      rw [hGT] at h1
      linarith
  exact ⟨η, IsGeneratingTrace.congr_lt (hη.mono_horizon hτζ) hall,
    fun htop => htrans (top_le_iff.1 (htop ▸ hτζ))⟩

end SeedStop

end Sec7

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtJCont
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# (CONT), the positive part: continuing a local evolution after a positive stop

Packet PROVE-WFS0, input (CONT) of `planning/handoffs/PROVE-DOMAINMARKOV10.md` §4.1. A local integrated evolution
before a random time `V` (`Sec2.IsSLEEvolutionUpTo`), continuous through a finite `V`, is continued on the same space,
in the usual augmentation of its filtration, on the event `{V > 0}`:

* where `V = ∞` the local path is already complete (`isIntegratedSLEPath_top_of_isSLEPathUpTo`);
* where `0 < V < ∞` and the word seen from the driver is bad at `V`, the lifetime is `V` itself: the word is separated
  and ordered there (`sep_ordered_at`), so it satisfies the threshold condition, which is the maximality clause at the
  (unique, by continuity) left limit (`isIntegratedSLEPath_of_bad`);
* where `0 < V < ∞` and the word is good at `V`, the local path is followed by the maximal solution driven by the
  increments of a continuous version of the Brownian motion after `V` (as in
  `Sec2.Assembly3.isIntegratedSLEEvolution_contClosed`; the strong Markov property is applied at the bounded stopping
  times `V ∧ m`, `m ∈ ℕ`, and the continued state is adapted because, on `{V ≤ t}`, it is the continued state at
  `V ∧ t`).

The main result is **`exists_posCont`**. The case `V = 0` is treated in `StoppedCont` with an independent evolution.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace StoppedCont

open Sec2 Sec2.Assembly Sec2.Assembly2 Sec2.Assembly3 LocalExt QuantumZipper.StrongMarkov

/-! ### The word at a positive stop -/

section Path

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **At a positive stop through which a local path of an ordered word is continuous, the word seen from the driver is
separated and ordered.** -/
theorem sep_ordered_at {T : ℝ≥0} (hp : IsSLEPathUpTo a xL xR ρL ρR w vL vR b T) (hF : IsOrderedForceWord xL xR)
    (hT0 : 0 < T) (hcw : ContinuousOn w (Iic T)) (hcL : ∀ i, ContinuousOn (vL i) (Iic T))
    (hcR : ∀ j, ContinuousOn (vR j) (Iic T)) :
    (∀ i j, vL i T - w T < vR j T - w T) ∧
      IsOrderedForceWord (fun i => vL i T - w T) (fun j => vR j T - w T) := by
  have hlt : ∀ {t : ℝ≥0}, t < T → (t : ℝ≥0∞) < (T : ℝ≥0∞) := fun ht => by exact_mod_cast ht
  have hT2 : T / 2 < T := NNReal.half_lt_self hT0.ne'
  have hT20 : 0 < T / 2 := by positivity
  have hmonoR : ∀ j t, T / 2 ≤ t → t < T → vR j (T / 2) ≤ vR j t := fun j t h1 h2 => by
    have e := hp.vR_sub h1 (hlt h2) j
    have hnn : 0 ≤ ∫ r in ((T / 2 : ℝ≥0) : ℝ)..t, 2 / (vR j r.toNNReal - w r.toNNReal) := by
      refine intervalIntegral.integral_nonneg (by exact_mod_cast h1) fun u hu => ?_
      have hu0 : 0 ≤ u := le_trans (NNReal.coe_nonneg _) hu.1
      have hut : u.toNNReal < T := by
        rw [Real.toNNReal_lt_iff_lt_coe hu0]
        exact lt_of_le_of_lt hu.2 (by exact_mod_cast h2)
      exact div_nonneg zero_le_two (sub_nonneg.2 (hp.w_le_vR (hlt hut) j))
    linarith
  have hmonoL : ∀ i t, T / 2 ≤ t → t < T → vL i t ≤ vL i (T / 2) := fun i t h1 h2 => by
    have e := hp.vL_sub h1 (hlt h2) i
    have hnp : 0 ≤ ∫ r in ((T / 2 : ℝ≥0) : ℝ)..t, -(2 / (vL i r.toNNReal - w r.toNNReal)) := by
      refine intervalIntegral.integral_nonneg (by exact_mod_cast h1) fun u hu => ?_
      have hu0 : 0 ≤ u := le_trans (NNReal.coe_nonneg _) hu.1
      have hut : u.toNNReal < T := by
        rw [Real.toNNReal_lt_iff_lt_coe hu0]
        exact lt_of_le_of_lt hu.2 (by exact_mod_cast h2)
      exact neg_nonneg.2 (div_nonpos_of_nonneg_of_nonpos zero_le_two (sub_nonpos.2 (hp.vL_le_w (hlt hut) i)))
    rw [intervalIntegral.integral_neg] at hnp
    linarith
  refine ⟨fun i j => ?_, fun i k hik => ?_, fun i => ?_, fun j k hjk => ?_, fun j => ?_⟩
  · have h1 := le_at_of_continuousOn_Iic hT2 (hcR j) fun t h1 h2 => hmonoR j t h1 h2
    have h2 := ge_at_of_continuousOn_Iic hT2 (hcL i) fun t h1 h2 => hmonoL i t h1 h2
    have h3 := hp.vL_lt_vR_of_pos hF hT20 (hlt hT2) i j
    linarith
  · have := ge_at_of_continuousOn_Iic (f := fun t => vL k t - vL i t) (c := 0) hT0 ((hcL k).sub (hcL i))
      fun t _ ht => sub_nonpos.2 (hp.antitone_vL (hlt ht) hik)
    simp only at this ⊢
    linarith
  · have := ge_at_of_continuousOn_Iic (f := fun t => vL i t - w t) (c := 0) hT0 ((hcL i).sub hcw)
      fun t _ ht => sub_nonpos.2 (hp.vL_le_w (hlt ht) i)
    simpa using this
  · have := le_at_of_continuousOn_Iic (f := fun t => vR k t - vR j t) (c := 0) hT0 ((hcR k).sub (hcR j))
      fun t _ ht => sub_nonneg.2 (hp.monotone_vR (hlt ht) hjk)
    simp only at this ⊢
    linarith
  · have := le_at_of_continuousOn_Iic (f := fun t => vR j t - w t) (c := 0) hT0 ((hcR j).sub hcw)
      fun t _ ht => sub_nonneg.2 (hp.w_le_vR (hlt ht) j)
    simpa using this

/-- **A local path stopped where the word is bad is an integrated path with lifetime the stop**: at a positive finite
stop through which the path is continuous, if the word seen from the driver is not good, it satisfies the threshold
condition (it is separated and ordered), and the left limit of the state at the stop is its value there. -/
theorem isIntegratedSLEPath_of_bad {T : ℝ≥0} (hp : IsSLEPathUpTo a xL xR ρL ρR w vL vR b T)
    (hF : IsOrderedForceWord xL xR) (hT0 : 0 < T) (hc : ContinuousOn (fun t => (w t, fun i => vL i t,
      fun j => vR j t)) (Iic T))
    (hbad : ¬ GoodWord ρL ρR (fun i => vL i T - w T, fun j => vR j T - w T)) :
    IsIntegratedSLEPath a xL xR ρL ρR w vL vR b T := by
  have hcw : ContinuousOn w (Iic T) := continuous_fst.comp_continuousOn hc
  have hcL : ∀ i, ContinuousOn (vL i) (Iic T) := fun i =>
    (continuous_apply i).comp_continuousOn (continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn hc))
  have hcR : ∀ j, ContinuousOn (vR j) (Iic T) := fun j =>
    (continuous_apply j).comp_continuousOn (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn hc))
  obtain ⟨hsep, hord⟩ := sep_ordered_at hp hF hT0 hcw hcL hcR
  have hthr : ForceWord.ThresholdCondition ρL ρR (w T) (fun i => vL i T) (fun j => vR j T) := by
    by_contra hn
    refine hbad ⟨hsep, hord, ?_⟩
    have e := thr_sub_iff (ρL := ρL) (ρR := ρR) (w T) (w T) (fun i => vL i T) (fun j => vR j T)
    rw [sub_self] at e
    exact fun h => hn (e.1 h)
  refine ⟨hp.w_zero, hp.vL_zero, hp.vR_zero, hp.continuousOn_w, hp.continuousOn_vL, hp.continuousOn_vR,
    fun _ ht => hp.antitone_vL ht, fun _ ht => hp.vL_le_w ht, fun _ ht => hp.w_le_vR ht,
    fun _ ht => hp.monotone_vR ht, fun _ ht => hp.integrable_gapL ht, fun _ ht => hp.integrable_gapR ht,
    fun _ ht => hp.w_eq ht, fun _ ht => hp.vL_eq ht, fun _ ht => hp.vR_eq ht, hp.volume_collisionL,
    hp.volume_collisionR, fun _ ht => hp.not_threshold ht, fun h0 => absurd h0 (by exact_mod_cast hT0.ne'),
    fun T' _ hT' w₀ vL₀ vR₀ hlim => ?_⟩
  have hTT : T' = T := by exact_mod_cast hT'
  subst hTT
  have hne : (𝓝[<] T').NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  have ht : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T')
      (𝓝 (w T', fun i => vL i T', fun j => vR j T')) :=
    (hc T' (mem_Iic.2 le_rfl)).tendsto.mono_left (nhdsWithin_mono _ Iio_subset_Iic_self)
  have e := tendsto_nhds_unique hlim ht
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2, e3⟩ := e
  rw [e1, e2, e3]
  exact hthr

end Path

/-! ### The continued state depends on the stop only through its value -/

section Congr

variable {Ω : Type*} {a : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {T T' : Ω → ℝ≥0} {ω : Ω}

theorem contWord_congr (h : T ω = T' ω) : contWord W VL VR T ω = contWord W VL VR T' ω := by
  simp only [contWord, h]

theorem smPath_congr (h : T ω = T' ω) : smPath B T ω = smPath B T' ω := by
  funext s
  simp only [smPath, smShift, h]

theorem contLife_congr (h : T ω = T' ω) :
    contLife a ρL ρR W VL VR B T ω = contLife a ρL ρR W VL VR B T' ω := by
  simp only [contLife, contWord_congr h, smPath_congr h]

theorem contState_congr (h : T ω = T' ω) (t : ℝ≥0) :
    contState a ρL ρR W VL VR B T t ω = contState a ρL ρR W VL VR B T' t ω := by
  simp only [contState, contCode, contWord_congr h, smPath_congr h, h]

end Congr


/-! ### Stopping a process at `V` -/

section Stop

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞} {N : Set Ω}

/-- **The stop of a local evolution is a stopping time**: `{t < V} ∈ 𝓕_t` (adaptedness before `V`, with `A = univ`). -/
theorem isStoppingTime_of_adaptedBefore {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 V X) :
    IsStoppingTime 𝓕 (fun ω => (V ω : WithTop ℝ≥0)) := by
  intro t
  have h := (hX t univ MeasurableSet.univ).compl
  convert h using 1
  ext ω
  simp only [mem_ofPred_eq, mem_univ, and_true, mem_compl_iff, not_lt]
  rfl

open Classical in
/-- A process stopped at `V` (`stopVal`, measurable without continuity), set to `0` on `N`. -/
def stopN (N : Set Ω) (V : Ω → ℝ≥0∞) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ N then 0 else stopVal X (fun ω => (V ω : WithTop ℝ≥0)) t ω

/-- The stop `V ∧ m` as a real time. -/
def capV (V : Ω → ℝ≥0∞) (m : ℝ≥0) (ω : Ω) : ℝ≥0 := (min (V ω) (m : ℝ≥0∞)).toNNReal

theorem coe_capV (m : ℝ≥0) (ω : Ω) : (capV V m ω : ℝ≥0∞) = min (V ω) (m : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top).ne

theorem capV_le (m : ℝ≥0) (ω : Ω) : capV V m ω ≤ m := by
  have h := coe_capV (V := V) m ω
  have h2 : (capV V m ω : ℝ≥0∞) ≤ m := h ▸ min_le_right _ _
  exact_mod_cast h2

theorem capV_eq {m : ℝ≥0} {ω : Ω} (h : V ω ≤ m) : capV V m ω = (V ω).toNNReal := by
  simp only [capV, min_eq_left h]

theorem isStoppingTime_capV (hV : IsStoppingTime 𝓕 (fun ω => (V ω : WithTop ℝ≥0))) (m : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => (capV V m ω : WithTop ℝ≥0)) := by
  have h := hV.min_const m
  convert h using 2 with ω
  exact coe_capV m ω

theorem stopN_of_lt {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∉ N) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < V ω) :
    stopN N V X t ω = X t ω := by
  have ht' : (t : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0) := ht
  simp only [stopN, hω, ↓reduceIte, stopVal, ht']

theorem stopN_of_coe {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (hω : ω ∉ N) {s : ℝ≥0} (hs0 : 0 < s) (hs : (s : ℝ≥0∞) = V ω)
    (hc : ContinuousOn (X · ω) (Iic s)) (t : ℝ≥0) : stopN N V X t ω = X (min t s) ω := by
  have hS : (fun ω => (V ω : WithTop ℝ≥0)) ω = (s : WithTop ℝ≥0) := hs.symm
  have hpos : (0 : WithTop ℝ≥0) < (fun ω => (V ω : WithTop ℝ≥0)) ω := by
    rw [hS]; exact_mod_cast hs0
  have hfin : (fun ω => (V ω : WithTop ℝ≥0)) ω ≠ ⊤ := by rw [hS]; exact WithTop.coe_ne_top
  have hc' : ContinuousOn (fun t => X t ω) {t : ℝ≥0 | (t : WithTop ℝ≥0) ≤ (fun ω => (V ω : WithTop ℝ≥0)) ω} := by
    rw [hS]
    refine hc.mono fun r hr => ?_
    exact WithTop.coe_le_coe.1 hr
  simp only [stopN, hω, ↓reduceIte]
  rw [stopVal_eq hpos hfin hc' t, Sec7.stopAt_of_eq_coe hS t]

theorem stopN_of_zero {X : ℝ≥0 → Ω → ℝ} {ω : Ω} (h0 : V ω = 0) (t : ℝ≥0) :
    stopN N V X t ω = stopN N V X 0 ω := by
  have h1 : ¬ ((t : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0)) := by
    rw [h0]; exact ENNReal.not_lt_zero
  have h2 : ¬ (((0 : ℝ≥0) : WithTop ℝ≥0) < (V ω : WithTop ℝ≥0)) := by
    rw [h0]; exact ENNReal.not_lt_zero
  simp only [stopN, stopVal, h1, h2, ↓reduceIte]

/-- **The stopped process is continuous** when the process is continuous before `V` and through a finite `V`. -/
theorem continuous_stopN {X : ℝ≥0 → Ω → ℝ}
    (hX1 : ∀ ω, ω ∉ N → ContinuousOn (X · ω) {t | (t : ℝ≥0∞) < V ω})
    (hX2 : ∀ ω, ω ∉ N → ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (X · ω) (Iic T)) (ω : Ω) :
    Continuous (stopN N V X · ω) := by
  classical
  by_cases hω : ω ∈ N
  · have e : (stopN N V X · ω) = fun _ => 0 := funext fun t => by simp only [stopN, hω, ↓reduceIte]
    rw [e]; exact continuous_const
  by_cases h0 : V ω = 0
  · have e : (stopN N V X · ω) = fun _ => stopN N V X 0 ω := funext fun t => stopN_of_zero h0 t
    rw [e]; exact continuous_const
  by_cases htop : V ω = ⊤
  · have e : (stopN N V X · ω) = (X · ω) := funext fun t => stopN_of_lt hω (by rw [htop]; exact ENNReal.coe_lt_top)
    rw [e]
    have hu : {t : ℝ≥0 | (t : ℝ≥0∞) < V ω} = univ := by
      ext t; simp only [mem_ofPred_eq, htop, ENNReal.coe_lt_top, mem_univ]
    rw [← continuousOn_univ, ← hu]
    exact hX1 ω hω
  · set s := (V ω).toNNReal with hsdef
    have hs : (s : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal htop
    have hs0 : 0 < s := by
      have : (0 : ℝ≥0∞) < s := by rw [hs]; exact pos_iff_ne_zero.2 h0
      exact_mod_cast this
    have e : (stopN N V X · ω) = fun t => X (min t s) ω :=
      funext fun t => stopN_of_coe hω hs0 hs (hX2 ω hω s hs) t
    rw [e]
    exact (hX2 ω hω s hs).comp_continuous (continuous_id.min continuous_const)
      fun t => mem_Iic.2 (min_le_right _ _)

/-- **The stopped process is adapted** (to any larger filtration containing `N`). -/
theorem measurable_stopN {𝓖 : Filtration ℝ≥0 mΩ} (h𝓕𝓖 : 𝓕 ≤ 𝓖)
    (hV : IsStoppingTime 𝓕 (fun ω => (V ω : WithTop ℝ≥0))) (hN : ∀ t, MeasurableSet[𝓖 t] N)
    {X : ℝ≥0 → Ω → ℝ} (hX : AdaptedBefore 𝓕 V X) (t : ℝ≥0) : Measurable[𝓖 t] (stopN N V X t) := by
  classical
  let _ : MeasurableSpace Ω := 𝓖 t
  exact Measurable.ite (hN t) measurable_const ((measurable_stopVal_le hV hX t).mono (h𝓕𝓖 t) le_rfl)

end Stop


/-! ### The positive part -/

section Main

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}

/-- **The continuation of a local evolution on `{V > 0}`.** A local integrated evolution before `V`, continuous through
a finite `V`, extends on the same space, in the usual augmentation of its filtration and driven by a continuous version
`B₁` of its Brownian motion, to processes adapted before a lifetime `ζ₁` that, almost surely on `{V > 0}`, form an
integrated path of Definition 2.1 with `ζ₁ ≥ V` and agree with the local coordinates before `V`. -/
theorem exists_posCont [IsProbabilityMeasure P] (hκ : 0 < κ) (hF : IsOrderedForceWord xL xR)
    (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR P 𝓕 W VL VR B V)
    (hc : ∀ᵐ ω ∂P, ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
      ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T)) :
    ∃ (B₁ W₁ : ℝ≥0 → Ω → ℝ) (VL₁ : Fin nL → ℝ≥0 → Ω → ℝ) (VR₁ : Fin nR → ℝ≥0 → Ω → ℝ) (ζ₁ : Ω → ℝ≥0∞),
      IsFilteredBrownianReal (usualAugmentation 𝓕 P) B₁ P ∧ AdaptedBefore (usualAugmentation 𝓕 P) ζ₁ W₁ ∧
      (∀ i, AdaptedBefore (usualAugmentation 𝓕 P) ζ₁ (VL₁ i)) ∧
      (∀ j, AdaptedBefore (usualAugmentation 𝓕 P) ζ₁ (VR₁ j)) ∧
      ∀ᵐ ω ∂P, 0 < V ω → IsIntegratedSLEPath κ xL xR ρL ρR (W₁ · ω) (fun i t => VL₁ i t ω)
        (fun j t => VR₁ j t ω) (B₁ · ω) (ζ₁ ω) ∧ V ω ≤ ζ₁ ω ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < V ω → W₁ t ω = W t ω ∧ (∀ i, VL₁ i t ω = VL i t ω) ∧
          ∀ j, VR₁ j t ω = VR j t ω := by
  classical
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have h𝓕𝓖 : 𝓕 ≤ 𝓖 := Ito.le_usualAugmentation 𝓕 P
  have hVst : IsStoppingTime 𝓕 (fun ω => (V ω : WithTop ℝ≥0)) := isStoppingTime_of_adaptedBefore hE.adapted_W
  have hVst𝓖 : IsStoppingTime 𝓖 (fun ω => (V ω : WithTop ℝ≥0)) := fun t => h𝓕𝓖 t _ (hVst t)
  obtain ⟨B₁, -, hB₁c, hB₁, hB₁ae⟩ := Sec2.Restart.exists_continuous_version hE.brownian
  have hB₁a : ∀ t, Measurable[𝓖 t] (B₁ t) := hB₁.2.1
  -- the good event
  have hgood : ∀ᵐ ω ∂P, IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
      (B · ω) (V ω) ∧ (∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
        ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T)) ∧
      ∀ t, B₁ t ω = B t ω := by
    filter_upwards [hE.ae_path, hc, hB₁ae] with ω h1 h2 h3 using ⟨h1, h2, h3⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ ω, ω ∉ N → IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω) (B · ω) (V ω) ∧ (∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω →
        ContinuousOn (fun t => (W t ω, fun i => VL i t ω, fun j => VR j t ω)) (Iic T)) ∧
      ∀ t, B₁ t ω = B t ω := fun ω hω => not_not.1 fun h => hω (hNsub h)
  have hN𝓖 : ∀ t, MeasurableSet[𝓖 t] N := fun t => Ito.measurableSet_usualAugmentation_of_null hNm hN0 t
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- continuity of the coordinates
  have hcW1 : ∀ ω, ω ∉ N → ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < V ω} := fun ω hω =>
    (hgoodN ω hω).1.continuousOn_w
  have hcL1 : ∀ i ω, ω ∉ N → ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < V ω} := fun i ω hω =>
    (hgoodN ω hω).1.continuousOn_vL i
  have hcR1 : ∀ j ω, ω ∉ N → ContinuousOn (VR j · ω) {t | (t : ℝ≥0∞) < V ω} := fun j ω hω =>
    (hgoodN ω hω).1.continuousOn_vR j
  have hcW2 : ∀ ω, ω ∉ N → ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (W · ω) (Iic T) := fun ω hω T hT =>
    continuous_fst.comp_continuousOn ((hgoodN ω hω).2.1 T hT)
  have hcL2 : ∀ i ω, ω ∉ N → ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (VL i · ω) (Iic T) :=
    fun i ω hω T hT => (continuous_apply i).comp_continuousOn
      (continuous_fst.comp_continuousOn (continuous_snd.comp_continuousOn ((hgoodN ω hω).2.1 T hT)))
  have hcR2 : ∀ j ω, ω ∉ N → ∀ T : ℝ≥0, (T : ℝ≥0∞) = V ω → ContinuousOn (VR j · ω) (Iic T) :=
    fun j ω hω T hT => (continuous_apply j).comp_continuousOn
      (continuous_snd.comp_continuousOn (continuous_snd.comp_continuousOn ((hgoodN ω hω).2.1 T hT)))
  -- the stopped processes
  set YW : ℝ≥0 → Ω → ℝ := stopN N V W with hYW
  set YL : Fin nL → ℝ≥0 → Ω → ℝ := fun i => stopN N V (VL i) with hYL
  set YR : Fin nR → ℝ≥0 → Ω → ℝ := fun j => stopN N V (VR j) with hYR
  have hYWa : ∀ t, Measurable[𝓖 t] (YW t) := measurable_stopN h𝓕𝓖 hVst hN𝓖 hE.adapted_W
  have hYLa : ∀ i t, Measurable[𝓖 t] (YL i t) := fun i => measurable_stopN h𝓕𝓖 hVst hN𝓖 (hE.adapted_VL i)
  have hYRa : ∀ j t, Measurable[𝓖 t] (YR j t) := fun j => measurable_stopN h𝓕𝓖 hVst hN𝓖 (hE.adapted_VR j)
  have hYWc : ∀ ω, Continuous (YW · ω) := continuous_stopN hcW1 hcW2
  have hYLc : ∀ i ω, Continuous (YL i · ω) := fun i => continuous_stopN (hcL1 i) (hcL2 i)
  have hYRc : ∀ j ω, Continuous (YR j · ω) := fun j => continuous_stopN (hcR1 j) (hcR2 j)
  -- the stops
  set Ti : Ω → ℝ≥0 := fun ω => (V ω).toNNReal with hTi
  have hTm : ∀ m : ℝ≥0, IsStoppingTime 𝓖 (fun ω => (capV V m ω : WithTop ℝ≥0)) := isStoppingTime_capV hVst𝓖
  -- the good event of the continuation
  set Gd : Set Ω := {ω | ω ∉ N ∧ 0 < V ω ∧ V ω < ⊤ ∧ GoodWord ρL ρR (contWord YW YL YR Ti ω)} with hGd
  set ζ₁ : Ω → ℝ≥0∞ := fun ω => if ω ∈ Gd then (Ti ω : ℝ≥0∞) + contLife κ ρL ρR YW YL YR B₁ Ti ω else V ω
    with hζ₁
  set W₁ : ℝ≥0 → Ω → ℝ := fun t ω => if ω ∈ Gd then (contState κ ρL ρR YW YL YR B₁ Ti t ω).1 else W t ω
    with hW₁
  set VL₁ : Fin nL → ℝ≥0 → Ω → ℝ := fun i t ω => if ω ∈ Gd then (contState κ ρL ρR YW YL YR B₁ Ti t ω).2.1 i
    else VL i t ω with hVL₁
  set VR₁ : Fin nR → ℝ≥0 → Ω → ℝ := fun j t ω => if ω ∈ Gd then (contState κ ρL ρR YW YL YR B₁ Ti t ω).2.2 j
    else VR j t ω with hVR₁
  -- adaptedness
  have hGt : ∀ t : ℝ≥0, MeasurableSet[𝓖 t] (Gd ∩ {ω | V ω ≤ t}) := by
    intro t
    have e : Gd ∩ {ω | V ω ≤ t} = Nᶜ ∩ {ω | 0 < V ω ∧ W 0 ω ∈ univ} ∩ {ω | (V ω : WithTop ℝ≥0) ≤ t} ∩
        (contWord YW YL YR (capV V t)) ⁻¹' {s | GoodWord ρL ρR s} := by
      ext ω
      simp only [hGd, mem_inter_iff, mem_ofPred_eq, mem_compl_iff, mem_univ, and_true, mem_preimage]
      constructor
      · rintro ⟨⟨hω, h0, -, hg⟩, hVt⟩
        refine ⟨⟨⟨hω, h0⟩, hVt⟩, ?_⟩
        rw [contWord_congr (T := capV V t) (T' := Ti) (ω := ω) (capV_eq hVt)]
        exact hg
      · rintro ⟨⟨⟨hω, h0⟩, hVt⟩, hg⟩
        have hVt' : V ω ≤ t := hVt
        refine ⟨⟨hω, h0, lt_of_le_of_lt hVt' ENNReal.coe_lt_top, ?_⟩, hVt'⟩
        rw [← contWord_congr (T := capV V t) (T' := Ti) (ω := ω) (capV_eq hVt')]
        exact hg
    rw [e]
    refine (((hN𝓖 t).compl.inter ?_).inter (hVst𝓖 t)).inter ?_
    · exact h𝓕𝓖 t _ (𝓕.mono (zero_le : (0 : ℝ≥0) ≤ t) _ (hE.adapted_W 0 univ MeasurableSet.univ))
    · exact measurable_contWord_le hYWa hYLa hYRa hYWc hYLc hYRc (hTm t) (capV_le t) measurableSet_goodWord
  have hkey : ∀ (t : ℝ≥0) (D : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))), MeasurableSet D →
      MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < V ω ∧ (W t ω, fun i => VL i t ω, fun j => VR j t ω) ∈ D} →
      MeasurableSet[𝓖 t] {ω | (t : ℝ≥0∞) < ζ₁ ω ∧ (W₁ t ω, fun i => VL₁ i t ω, fun j => VR₁ j t ω) ∈ D} := by
    intro t D hD hD0
    have hS := measurableSet_contState (a := κ) (ρL := ρL) (ρR := ρR) hYWa hYLa hYRa hYWc hYLc hYRc hB₁a hB₁c
      (hTm t) t hD
    have e : {ω | (t : ℝ≥0∞) < ζ₁ ω ∧ (W₁ t ω, fun i => VL₁ i t ω, fun j => VR₁ j t ω) ∈ D} =
        {ω | (t : ℝ≥0∞) < V ω ∧ (W t ω, fun i => VL i t ω, fun j => VR j t ω) ∈ D} ∪
          ((Gd ∩ {ω | V ω ≤ t}) ∩ {ω | (t : ℝ≥0∞) < (capV V t ω : ℝ≥0∞) +
            contLife κ ρL ρR YW YL YR B₁ (capV V t) ω ∧ contState κ ρL ρR YW YL YR B₁ (capV V t) t ω ∈ D}) := by
      ext ω
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff]
      by_cases hG : ω ∈ Gd
      · have hG' := hG
        obtain ⟨hω, -, hVtop, -⟩ := hG'
        have hTiV : (Ti ω : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hVtop.ne
        have hst : (W₁ t ω, fun i => VL₁ i t ω, fun j => VR₁ j t ω) =
            contState κ ρL ρR YW YL YR B₁ Ti t ω := by
          simp only [hW₁, hVL₁, hVR₁, hG, ↓reduceIte]
        have hζ : ζ₁ ω = (Ti ω : ℝ≥0∞) + contLife κ ρL ρR YW YL YR B₁ Ti ω := by
          simp only [hζ₁, hG, ↓reduceIte]
        rw [hst, hζ]
        by_cases htV : (t : ℝ≥0∞) < V ω
        · have htT : t < Ti ω := by rw [← hTiV] at htV; exact_mod_cast htV
          have hcs : contState κ ρL ρR YW YL YR B₁ Ti t ω = (W t ω, fun i => VL i t ω, fun j => VR j t ω) := by
            simp only [contState, concatAt_of_lt htT, hYW, hYL, hYR, stopN_of_lt hω htV]
          rw [hcs]
          have hlt : (t : ℝ≥0∞) < (Ti ω : ℝ≥0∞) + contLife κ ρL ρR YW YL YR B₁ Ti ω :=
            lt_of_lt_of_le (hTiV ▸ htV) le_self_add
          have hnot : ¬ V ω ≤ t := not_le.2 htV
          simp only [hlt, htV, true_and, hnot, and_false, false_and, or_false]
        · have hVt : V ω ≤ t := not_lt.1 htV
          have hcap : capV V t ω = Ti ω := capV_eq hVt
          rw [contLife_congr (T := capV V t) (T' := Ti) (ω := ω) hcap,
            contState_congr (T := capV V t) (T' := Ti) (ω := ω) hcap, hcap]
          simp only [htV, false_and, hG, hVt, true_and, false_or]
      · have hst : (W₁ t ω, fun i => VL₁ i t ω, fun j => VR₁ j t ω) =
            (W t ω, fun i => VL i t ω, fun j => VR j t ω) := by
          simp only [hW₁, hVL₁, hVR₁, hG, ↓reduceIte]
        have hζ : ζ₁ ω = V ω := by simp only [hζ₁, hG, ↓reduceIte]
        rw [hst, hζ]
        simp only [hG, false_and, or_false]
    rw [e]
    exact hD0.union ((hGt t).inter hS)
  have hWad : AdaptedBefore 𝓖 ζ₁ W₁ := fun t A hA =>
    hkey t {p | p.1 ∈ A} (measurable_fst hA) (h𝓕𝓖 t _ (hE.adapted_W t A hA))
  have hLad : ∀ i, AdaptedBefore 𝓖 ζ₁ (VL₁ i) := fun i t A hA =>
    hkey t {p | p.2.1 i ∈ A} (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) hA)
      (h𝓕𝓖 t _ (hE.adapted_VL i t A hA))
  have hRad : ∀ j, AdaptedBefore 𝓖 ζ₁ (VR₁ j) := fun j t A hA =>
    hkey t {p | p.2.2 j ∈ A} (((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd)) hA)
      (h𝓕𝓖 t _ (hE.adapted_VR j t A hA))
  refine ⟨B₁, W₁, VL₁, VR₁, ζ₁, hB₁, hWad, hLad, hRad, ?_⟩
  -- the strong Markov property at the stops `V ∧ m`
  have hgp : ∀ m : ℕ, ∀ᵐ ω ∂P, (contWord YW YL YR (capV V m) ω, smPath B₁ (capV V m) ω) ∈ GoodPair κ ρL ρR :=
    fun m => ae_mem_of_strongMarkov hB₁ hB₁c (hTm m)
      (measurable_contWord hYWa hYLa hYRa hYWc hYLc hYRc (hTm m)) measurableSet_goodPair
      (ae_mem_goodPair hκ hB₁ hB₁c)
  filter_upwards [ae_all_iff.2 hgp, hNae] with ω hgpω hω hV0
  obtain ⟨hp, hcI, hBB⟩ := hgoodN ω hω
  have hp₁ : IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B₁ · ω) (V ω) :=
    isSLEPathUpTo_congr hp rfl (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ _ => rfl)
      (fun _ _ _ => rfl) fun t _ => hBB t
  have hV0' : ((0 : ℝ≥0) : ℝ≥0∞) < V ω := by rw [ENNReal.coe_zero]; exact hV0
  by_cases hG : ω ∈ Gd
  · have hG' := hG
    obtain ⟨-, -, hVtop, hgw⟩ := hG'
    have hTiV : (Ti ω : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hVtop.ne
    have hT0 : 0 < Ti ω := by
      have : (0 : ℝ≥0∞) < Ti ω := by rw [hTiV]; exact hV0
      exact_mod_cast this
    obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt hVtop.ne
    have hcap : capV V (m : ℝ≥0) ω = Ti ω := capV_eq (by exact_mod_cast hm.le)
    have hgp' := hgpω m
    have e1 : contWord YW YL YR (capV V (m : ℝ≥0)) ω = contWord YW YL YR Ti ω :=
      contWord_congr (T := capV V (m : ℝ≥0)) (T' := Ti) (ω := ω) hcap
    have e2 : smPath B₁ (capV V (m : ℝ≥0)) ω = smPath B₁ Ti ω :=
      smPath_congr (T := capV V (m : ℝ≥0)) (T' := Ti) (ω := ω) hcap
    have hgp'' : (contWord YW YL YR Ti ω, smPath B₁ Ti ω) ∈ GoodPair κ ρL ρR := by
      rw [← e1, ← e2]; exact hgp'
    obtain ⟨hl0, hNb⟩ := hgp'' hgw
    have hgc : Continuous (smPath B₁ Ti ω) :=
      ((hB₁c ω).comp (continuous_const.add continuous_id)).sub continuous_const
    have h₂ := isIntegratedSLEPath_maxCode_of_good (a := κ) hgw hgc hl0 hNb
    have h₁ : IsSLEPathUpTo κ xL xR ρL ρR (YW · ω) (fun i t => YL i t ω) (fun j t => YR j t ω) (B₁ · ω)
        (Ti ω) := by
      rw [hTiV]
      exact isSLEPathUpTo_congr hp₁ (stopN_of_lt hω hV0') (fun i => stopN_of_lt hω hV0')
        (fun j => stopN_of_lt hω hV0') (fun t ht => stopN_of_lt hω ht) (fun t ht i => stopN_of_lt hω ht)
        (fun t ht j => stopN_of_lt hω ht) fun _ _ => rfl
    have hcY : ContinuousAt (fun t => (YW t ω, fun i => YL i t ω, fun j => YR j t ω)) (Ti ω) :=
      ((hYWc ω).prodMk ((continuous_pi fun i => hYLc i ω).prodMk
        (continuous_pi fun j => hYRc j ω))).continuousAt
    have h := h₁.isIntegratedSLEPath_concat_closed hT0 hcY (hB₁c ω).continuousAt h₂ fun t => rfl
    refine ⟨?_, ?_, fun t ht => ?_⟩
    · simp only [hW₁, hVL₁, hVR₁, hζ₁, hG, ↓reduceIte]
      exact h
    · simp only [hζ₁, hG, ↓reduceIte]
      rw [hTiV]
      exact le_self_add
    · have htT : t < Ti ω := by rw [← hTiV] at ht; exact_mod_cast ht
      simp only [hW₁, hVL₁, hVR₁, hG, ↓reduceIte, contState, concatAt_of_lt htT, hYW, hYL, hYR,
        stopN_of_lt hω ht, implies_true, and_self]
  · have hζe : ζ₁ ω = V ω := by simp only [hζ₁, hG, ↓reduceIte]
    refine ⟨?_, by rw [hζe], fun t _ => ?_⟩
    · simp only [hW₁, hVL₁, hVR₁, hζ₁, hG, ↓reduceIte]
      by_cases htop : V ω = ⊤
      · rw [htop] at hp₁ ⊢
        exact isIntegratedSLEPath_top_of_isSLEPathUpTo hp₁
      · set s : ℝ≥0 := (V ω).toNNReal with hsdef
        have hs : (s : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal htop
        have hs0 : 0 < s := by
          have : (0 : ℝ≥0∞) < s := by rw [hs]; exact hV0
          exact_mod_cast this
        have hbad : ¬ GoodWord ρL ρR (fun i => VL i s ω - W s ω, fun j => VR j s ω - W s ω) := by
          intro hg
          refine hG ⟨hω, hV0, lt_top_iff_ne_top.2 htop, ?_⟩
          have e : contWord YW YL YR Ti ω = (fun i => VL i s ω - W s ω, fun j => VR j s ω - W s ω) := by
            refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
            · show stopN N V (VL i) s ω - stopN N V W s ω = VL i s ω - W s ω
              rw [stopN_of_coe hω hs0 hs (hcL2 i ω hω s hs), stopN_of_coe hω hs0 hs (hcW2 ω hω s hs), min_self]
            · show stopN N V (VR j) s ω - stopN N V W s ω = VR j s ω - W s ω
              rw [stopN_of_coe hω hs0 hs (hcR2 j ω hω s hs), stopN_of_coe hω hs0 hs (hcW2 ω hω s hs), min_self]
          rw [e]
          exact hg
        have hp₂ : IsSLEPathUpTo κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B₁ · ω)
            (s : ℝ≥0∞) := by rw [hs]; exact hp₁
        have := isIntegratedSLEPath_of_bad hp₂ hF hs0 (hcI s hs) hbad
        rw [← hs]
        exact this
    · simp only [hW₁, hVL₁, hVR₁, hG, ↓reduceIte, implies_true, and_self]

end Main

end StoppedCont

end Restart

end InteractingSLE

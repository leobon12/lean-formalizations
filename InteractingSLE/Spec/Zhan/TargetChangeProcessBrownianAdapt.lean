/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianNoise

/-!
# `b̃` is a Brownian motion, part 8: the transformed paths are adapted to the new filtration

Packet PROVE-SEC7-C9. The transformed driver and marks at the new time `t < T̃` are explicit functions of the
coordinates at the original time `C⁻¹(t)` (`phiW`, `phiVL`, `phiVR`: `M(v) = β + α/(V_k − v)`, `W` by (N1)). For
`t < S_n` that original time is `newT t ∧ σ_n`, and the coordinates there are `𝓗_t`-measurable (stopped value of a
continuous adapted process). Hence the transformed paths are adapted to `𝓗` before the horizon
`τ = T̃` on the good event (`0` off it) (`adaptedBefore_newW`, `adaptedBefore_newVL`, `adaptedBefore_newVR`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### The transformed paths as functions of the coordinates -/

section Phi

variable {nL j m : ℕ} (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (ρL : Fin nL → ℝ)
  (ρR : Fin (j + 1 + m) → ℝ)

/-- The transformed driver `M(W) = β + α/(V_k − W)` with `W` from (N1). -/
def phiW (p : RCoord nL (j + 1 + m) × ℝ) : ℝ :=
  p.1.2.2.2.1 + p.1.2.2.1 / (p.1.2.1 (LP.retargetIdx j m) - drv κ xL xR ρL ρR p)

/-- The transformed left marks. -/
def phiVL (i : Fin (nL + (m + 1))) (p : RCoord nL (j + 1 + m) × ℝ) : ℝ :=
  Fin.append (fun i => p.1.2.2.2.1 + p.1.2.2.1 / (p.1.2.1 (LP.retargetIdx j m) - p.1.1 i))
    (Fin.cons p.1.2.2.2.1 fun l : Fin m =>
      p.1.2.2.2.1 + p.1.2.2.1 / (p.1.2.1 (LP.retargetIdx j m) - p.1.2.1 (Fin.natAdd (j + 1) l.rev))) i

/-- The transformed right marks. -/
def phiVR (i : Fin j) (p : RCoord nL (j + 1 + m) × ℝ) : ℝ :=
  p.1.2.2.2.1 + p.1.2.2.1 / (p.1.2.1 (LP.retargetIdx j m) - p.1.2.1 (Fin.castAdd m i.castSucc))

theorem measurable_phiW : Measurable (phiW κ xL xR ρL ρR) := by
  unfold phiW drv; fun_prop

theorem measurable_phiVL (i : Fin (nL + (m + 1))) : Measurable (phiVL (nL := nL) (j := j) (m := m) i) := by
  induction i using Fin.addCases with
  | left i' =>
    unfold phiVL
    simp only [Fin.append_left]
    fun_prop
  | right l =>
    unfold phiVL
    simp only [Fin.append_right]
    induction l using Fin.cases with
    | zero => simp only [Fin.cons_zero]; fun_prop
    | succ l' => simp only [Fin.cons_succ]; fun_prop

theorem measurable_phiVR (i : Fin j) : Measurable (phiVR (nL := nL) (m := m) i) := by
  unfold phiVR; fun_prop

end Phi

section PhiEq

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}

theorem newW_eq_phiW (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) {u : ℝ≥0}
    (hs0 : 0 ≤ invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u)
    (hsT : (((invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal : ℝ≥0) : ℝ≥0∞) < T) :
    newW xR w vR u = phiW κ xL xR ρL ρR (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR
      (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal,
      b (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal) := by
  rw [phiW, drv_rCoordAt hp hsT, rCoordAt_toNNReal hs0]
  rfl

theorem newVL_eq_phiVL {u : ℝ≥0} (hs0 : 0 ≤ invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u)
    (i : Fin (nL + (m + 1))) :
    newVL xR w vL vR i u = phiVL i (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR
      (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal,
      b (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal) := by
  rw [rCoordAt_toNNReal hs0]
  rfl

theorem newVR_eq_phiVR {u : ℝ≥0} (hs0 : 0 ≤ invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u)
    (i : Fin j) :
    newVR xR w vR i u = phiVR i (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR
      (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal,
      b (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal) := by
  rw [rCoordAt_toNNReal hs0]
  rfl

end PhiEq

/-! ### Adaptedness before the horizon -/

section Adapt

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {nL j m : ℕ}
  {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

open scoped Classical in
/-- The horizon on the good event (`0` off it). -/
def horG (xR : Fin (j + 1 + m) → ℝ) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VR : Fin (j + 1 + m) → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  if ω ∈ G then horT xR W VR ζ ω else 0

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T)
  (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)

include hE hGm hGc hgood hT in
theorem measurable_brownG_stopped_r (n : ℕ) (t : ℝ≥0) :
    Measurable[usualAugmentation 𝓕 P t] fun ω =>
      Sec2.TwoSeed.brownG G B (min t (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω := by
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hB' := isFilteredBrownianReal_brownG_r hE hGm hGc hgood
  have h := Ito.measurable_stopped_of_agree (X := Sec2.TwoSeed.brownG G B)
    (isStoppingTime_rLoc hE hGm hGc hgood hT n (k := LP.retargetIdx j m)) hB'.2.1 hG0 (0 : ℝ)
    (fun ω _ s _ => rfl) (fun ω _ => (continuous_brownG_r hgood ω).continuousOn) t
  convert h using 2 with ω
  by_cases hω : ω ∈ G <;> simp [Sec2.TwoSeed.brownG, hω]

include hE hGm hGc hgood hT hD hj in
/-- The coordinates at the original time `newT t ∧ σ_n` are `𝓗_t`-measurable. -/
theorem measurable_coords_capTime (n : ℕ) (t : ℝ≥0) :
    Measurable[filtH hE hGm hGc hgood hT hD hj t] fun ω =>
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
          (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
       Sec2.TwoSeed.brownG G B (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
          (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) := by
  set Z : ℝ≥0 → Ω → RCoord nL (j + 1 + m) × ℝ := fun r ω =>
    (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
      (min r (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
     Sec2.TwoSeed.brownG G B (min r (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) with hZ
  have hZa : StronglyAdapted (usualAugmentation 𝓕 P) Z := fun r =>
    ((measurable_rCoord_stopped hE hGm hGc hgood hT hD hj n r).prodMk
      (measurable_brownG_stopped_r hE hGm hGc hgood hT n r)).stronglyMeasurable
  have hZc : ∀ ω, Continuous fun r => Z r ω := fun ω =>
    (continuous_rCoord_stopped hgood hD hj n ω).prodMk (continuous_brownG_stopped_r hgood n ω)
  have hprog : IsStronglyProgressive (usualAugmentation 𝓕 P) Z :=
    StronglyAdapted.isStronglyProgressive_of_continuous hZa hZc
  have hN := isStoppingTime_const (usualAugmentation 𝓕 P) (n : ℝ≥0)
  have hτ := isStoppingTime_newT hE hGm hGc hgood hT hD hj t
  have hc := Sec2.TwoSeed.isStoppingTime_capTime hN hτ
  have h := measurable_stoppedValue hprog hc
  have e : stoppedValue Z (fun ω => (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω :
      WithTop ℝ≥0)) = fun ω => Z (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω) ω := by
    funext ω; simp only [stoppedValue, WithTop.untopA, WithTop.untopD_coe]
  rw [e] at h
  show Measurable[(isStoppingTime_newT hE hGm hGc hgood hT hD hj t).measurableSpace] _
  exact h.mono (IsStoppingTime.measurableSpace_mono hc hτ fun ω =>
    Sec2.TwoSeed.capTime_le_right _ _ ω) le_rfl

include hE hGm hGc hgood hT hD hj in
/-- **A process given before the horizon by a measurable function of the coordinates at `C⁻¹(t)` is adapted to
`𝓗` before the horizon.** -/
theorem adaptedBefore_of_coords {X : ℝ≥0 → Ω → ℝ} {Φ : RCoord nL (j + 1 + m) × ℝ → ℝ} (hΦ : Measurable Φ)
    (hX : ∀ ω ∈ G, ∀ t : ℝ≥0, (t : ℝ≥0∞) < horT xR W VR ζ ω →
      X t ω = Φ (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) (W · ω) (fun i t => VL i t ω)
        (fun i t => VR i t ω) (invClk (rateT xR W VR ω) t).toNNReal, B (invClk (rateT xR W VR ω) t).toNNReal ω)) :
    AdaptedBefore (filtH hE hGm hGc hgood hT hD hj) (horG xR G W VR ζ) X := by
  intro t A hA
  set H := filtH hE hGm hGc hgood hT hD hj with hHdef
  -- the good event is in `𝓗_t`
  have hGH : MeasurableSet[H t] G := by
    have h0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
    have hc0 := isStoppingTime_const (usualAugmentation 𝓕 P) (0 : ℝ≥0)
    have hle : hc0.measurableSpace ≤ (isStoppingTime_newT hE hGm hGc hgood hT hD hj t).measurableSpace :=
      IsStoppingTime.measurableSpace_mono hc0 _ fun ω => by
        simp only [WithTop.coe_zero]; exact bot_le
    rw [IsStoppingTime.measurableSpace_const] at hle
    exact hle _ h0
  have hS : ∀ n, MeasurableSet[H t] {ω | t < newS xR G T W VL VR B ζ n ω} := fun n => by
    have := (isStoppingTime_newS hE hGm hGc hgood hT hD hj n t).compl
    convert this using 1
    ext ω; simp only [mem_ofPred_eq, mem_compl_iff, WithTop.coe_le_coe, not_le]
  have hZ : ∀ n : ℕ, MeasurableSet[H t] ((fun ω => Φ
      (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
        (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
          (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
       Sec2.TwoSeed.brownG G B (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
          (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω)) ⁻¹' A) := fun n =>
    (hΦ.comp (measurable_coords_capTime hE hGm hGc hgood hT hD hj n t)) hA
  have e : {ω | (t : ℝ≥0∞) < horG xR G W VR ζ ω ∧ X t ω ∈ A} = G ∩ ⋃ n,
      ({ω | t < newS xR G T W VL VR B ζ n ω} ∩ ((fun ω => Φ
        (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
          (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
            (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
         Sec2.TwoSeed.brownG G B (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
            (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω)) ⁻¹' A)) := by
    ext ω
    by_cases hω : ω ∈ G
    · have hval : ∀ n, t ≤ newS xR G T W VL VR B ζ n ω →
          Φ (rCoord xL xR (LP.retargetPos xR) (LP.retargetIdx j m) G W VL VR
            (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
              (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω,
           Sec2.TwoSeed.brownG G B (min (Sec2.TwoSeed.capTime (fun _ => (n : ℝ≥0)) (newT xR G W VR ζ t) ω)
              (rLoc (LP.retargetIdx j m) G T W VL VR B ζ n ω)) ω) = X t ω := fun n hn => by
        rw [rCoord_capTime_eq hgood hD hj, brownG_capTime_eq hgood hD hj, min_eq_left hn,
          hX ω hω t (lt_of_le_of_lt (by exact_mod_cast hn) (newS_lt_horT hgood hD hj hω n))]
        simp only [rCoord, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
      simp only [horG, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, true_and, mem_iUnion, mem_preimage]
      constructor
      · rintro ⟨ht, hXA⟩
        obtain ⟨t', htt', ht'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
        obtain ⟨n, hn⟩ := exists_le_newS hgood hD hj hT.2.1 hω ht'
        have htn : t < newS xR G T W VL VR B ζ n ω := lt_of_lt_of_le (by exact_mod_cast htt') hn
        exact ⟨n, htn, by rw [hval n htn.le]; exact hXA⟩
      · rintro ⟨n, htn, hA'⟩
        refine ⟨lt_of_le_of_lt (by exact_mod_cast htn.le) (newS_lt_horT hgood hD hj hω n), ?_⟩
        rw [← hval n htn.le]; exact hA'
    · simp only [horG, hω, ↓reduceIte, mem_ofPred_eq, mem_inter_iff, false_and, iff_false, not_and]
      intro h; exact absurd h (not_lt.2 bot_le)
  rw [e]
  exact hGH.inter (MeasurableSet.iUnion fun n => (hS n).inter (hZ n))

end Adapt

end Retarget

end Zhan

end InteractingSLE

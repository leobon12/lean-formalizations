/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1GoodHull
import InteractingSLE.Spec.ZhanGT4.A1RefBridge

/-!
# Zhan's A.1: good times from disjoint closed hulls

Packet PROVE-A1-GOODTIME. `A1Ref.IsGoodTime 0 wj ζj xk wk τ T` (`0 < T` and `T` strictly before the first contact of
the CLOSED hulls, capped by `ζj`) is the hypothesis `hgood` of every identification lemma between the canonical image
data and the seeded capacity coordinates (A1-FAMILY, A1-FORCES, A1-MULTIMARK, A1-SEEDGEOM). With the right-continuity
of the closed hulls (`A1GoodHull`) it follows from disjointness of the closed hulls AT `T`:

* `ofReal_lt_contactTime_of_forall`: a margin `δ > 0` of disjointness after `T` puts `T` before the contact time;
* **`isGoodTime_of_disjoint`**: continuous image driver, `0 < T`, `T < ζj`, and the closed hulls disjoint at `T`;
* **`isGoodTime_of_disjoint_loc`**: the same for an image driver continuous on `[0, T']` only, `T < T'`;
* **`isGoodTime_of_sep`**: the hulls lie in sets at positive distance (the separated enclosures of the rectangles).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Good

open QuantumZipper (H fwdHull)
open A2X

/-- **A disjointness margin after `T` puts `T` before the contact time.** -/
theorem ofReal_lt_contactTime_of_forall {wj : ℝ → ℝ} {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ T δ : ℝ} (hT : 0 < T)
    (hδ : 0 < δ) (hTζ : ENNReal.ofReal T < ζj)
    (h : ∀ s : ℝ≥0, (s : ℝ) < T + δ → Disjoint (closure (physHull 0 wj s)) (closure (physHull xk wk τ))) :
    ENNReal.ofReal T < contactTime 0 wj ζj xk wk τ := by
  have hlt : ENNReal.ofReal T < ENNReal.ofReal (T + δ) :=
    ENNReal.ofReal_lt_ofReal_iff'.2 (show T < T + δ ∧ 0 < T + δ from ⟨by linarith, by linarith⟩)
  refine lt_min hTζ (hlt.trans_le (le_iInf₂ fun s hs => ?_))
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (not_lt.1 fun hlt => ?_)
  exact (Set.not_disjoint_iff_nonempty_inter.2 hs) (h s hlt)

/-- **A good time from disjoint closed hulls** (image driver continuous). -/
theorem isGoodTime_of_disjoint {wj : ℝ → ℝ} (hj : Continuous wj) {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ T : ℝ}
    (hT : 0 < T) (hTζ : ENNReal.ofReal T < ζj)
    (hd : Disjoint (closure (physHull 0 wj T)) (closure (physHull xk wk τ))) :
    A1Ref.IsGoodTime 0 wj ζj xk wk τ T := by
  rw [A1Ref.physHull_zero] at hd
  obtain ⟨δ, hδ, hdisj⟩ := exists_pos_disjoint_closure_fwdHull_of_isClosed hj hT isClosed_closure hd.symm
  refine ⟨hT, ofReal_lt_contactTime_of_forall hT hδ hTζ fun s hs => ?_⟩
  rw [A1Ref.physHull_zero]
  exact (hdisj.mono_right (closure_mono ((QuantumZipper.fwdHull_mono (W := wj)).1 hs.le))).symm

/-- **A good time from disjoint closed hulls** (image driver continuous on `[0, T']`, `T < T'`). -/
theorem isGoodTime_of_disjoint_loc {wj : ℝ → ℝ} {T T' : ℝ} (hTT' : T < T') (hj : ContinuousOn wj (Icc 0 T'))
    {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ} (hT : 0 < T) (hTζ : ENNReal.ofReal T < ζj)
    (hd : Disjoint (closure (physHull 0 wj T)) (closure (physHull xk wk τ))) :
    A1Ref.IsGoodTime 0 wj ζj xk wk τ T := by
  set w' := A1Ref.stopDrv wj T' with hw'
  have hT'0 : 0 ≤ T' := hT.le.trans hTT'.le
  have hw'c : Continuous w' := A1Ref.continuous_stopDrv hj hT'0
  have heq : EqOn wj w' (Icc 0 T') := (A1Ref.stopDrv_eqOn wj T').symm
  have hcongr : ∀ s : ℝ, 0 ≤ s → s < T' → physHull 0 wj s = physHull 0 w' s :=
    fun s hs hsT => A1Ref.physHull_congr hs hsT heq
  rw [hcongr T hT.le hTT', A1Ref.physHull_zero] at hd
  obtain ⟨δ, hδ, hdisj⟩ := exists_pos_disjoint_closure_fwdHull_of_isClosed hw'c hT isClosed_closure hd.symm
  set δ' := min δ ((T' - T) / 2) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (by linarith)
  refine ⟨hT, ofReal_lt_contactTime_of_forall hT hδ'pos hTζ fun s hs => ?_⟩
  have hsT' : (s : ℝ) < T' := by linarith [min_le_right δ ((T' - T) / 2)]
  rw [hcongr s s.coe_nonneg hsT', A1Ref.physHull_zero]
  refine (hdisj.mono_right (closure_mono ((QuantumZipper.fwdHull_mono (W := w')).1 ?_))).symm
  linarith [min_le_left δ ((T' - T) / 2)]

/-- Sets at positive distance have disjoint closures. -/
theorem disjoint_closure_of_sep {A B : Set ℂ} {δ : ℝ} (hδ : 0 < δ) (h : ∀ a ∈ A, ∀ b ∈ B, δ ≤ ‖a - b‖) :
    Disjoint (closure A) (closure B) := by
  have hc : ∀ a ∈ closure A, ∀ b ∈ closure B, δ ≤ ‖a - b‖ := by
    have hcl : IsClosed {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} :=
      isClosed_le continuous_const (continuous_fst.sub continuous_snd).norm
    intro a ha b hb
    have hsub : A ×ˢ B ⊆ {p : ℂ × ℂ | δ ≤ ‖p.1 - p.2‖} := fun p hp => h p.1 hp.1 p.2 hp.2
    exact closure_minimal hsub hcl (show (a, b) ∈ closure (A ×ˢ B) by rw [closure_prod_eq]; exact ⟨ha, hb⟩)
  refine Set.disjoint_left.2 fun z hzA hzB => ?_
  have := hc z hzA z hzB
  rw [sub_self, norm_zero] at this
  linarith

/-- **A good time from separated enclosures** (image driver continuous on `[0, T']`, `T < T'`): the two hulls lie in
sets at distance `≥ δ > 0`. -/
theorem isGoodTime_of_sep {wj : ℝ → ℝ} {T T' : ℝ} (hTT' : T < T') (hj : ContinuousOn wj (Icc 0 T'))
    {ζj : ℝ≥0∞} {xk : ℝ} {wk : ℝ → ℝ} {τ : ℝ} (hT : 0 < T) (hTζ : ENNReal.ofReal T < ζj) {A B : Set ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hA : physHull 0 wj T ⊆ A) (hB : physHull xk wk τ ⊆ B) (h : ∀ a ∈ A, ∀ b ∈ B, δ ≤ ‖a - b‖) :
    A1Ref.IsGoodTime 0 wj ζj xk wk τ T :=
  isGoodTime_of_disjoint_loc hTT' hj hT hTζ
    ((disjoint_closure_of_sep hδ h).mono (closure_mono hA) (closure_mono hB))

end InteractingSLE.ZhanGT4.A1Good

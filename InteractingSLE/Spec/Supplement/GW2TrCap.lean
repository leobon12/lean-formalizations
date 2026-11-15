/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TnExport
import InteractingSLE.Spec.Supplement.GW2SdePrefix
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GW2RootH29Causal

/-!
# Decision D35 (D-b): candidates with one angle share the flow line up to the shorter cap

Packet PROVE-GW2-RELDET (round 29). BUF's clause (iii) lets the candidate's cap and buffer grow along candidates of
one angle; this needs that such candidates explore the same flow line up to the shorter cap. The candidate's piece is
the canonical piece of the future program, whose driver depends on the angles and the EARLIER own times only
(`canonState_congr₂`); its cap only stops the record. So:

* `joinedDriver_append_last_eq`, `joinedRead_append_last_eq` (any programs): two programs differing only in the time of
  their last instruction have the same joined driver up to the earlier of the two last times, when the earlier pieces
  agree and the last pieces agree up to that time;
* `canonDrive_congr_angle`: the canonical piece depends on the angles up to it and the own times before it;
* **`futFam_eq_of_angle`** / **`candLife_eq_of_angle`** (every sample): one angle ⇒ the same candidate piece, the same
  lifetime; **`nextRecord_eq_of_angle`**: the next record is the common piece stopped at the candidate's cap;
* **`futureJoined_eq_of_angle`** (every sample with good records) and **`ae_schedW_eq_of_angle`** (almost surely,
  for all histories and all pairs of candidates of one angle): the explored drivers agree up to `T + min caps`;
* **`ae_futurePair_eq_of_angle`**: on the history's success, the future pair of the shorter-cap candidate is the
  longer-cap candidate's joined driver recorded at the shorter last time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513TreeExtract Sec5.Prop513Schedule Sec7.StripSideHeightProb

/-! ### Joined drivers of programs differing in their last time -/

section Joined

/-- **Two programs differing only in the time of their last instruction have the same joined driver up to the
earlier last time**, when the earlier pieces agree and the last pieces agree up to that time. -/
theorem joinedDriver_append_last_eq {Ω : Type*} {E F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (ω : Ω) (y y' : ℝ × ℝ≥0) :
    ∀ (l : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0), (∀ i, j ≤ i → i < j + l.length → E i ω = F i ω) →
      (∀ u : ℝ≥0, u ≤ min y.2 y'.2 - lastTime a l → (E (j + l.length) ω).1 u = (F (j + l.length) ω).1 u) →
      ∀ t : ℝ≥0, t ≤ min y.2 y'.2 - a → joinedDriver E j a (l ++ [y]) ω t = joinedDriver F j a (l ++ [y']) ω t
  | [], j, a, _, hlast, t, ht => by
    change catPath (E j ω).1 (y.2 - a) (joinedDriver E (j + 1) y.2 [] ω) t =
      catPath (F j ω).1 (y'.2 - a) (joinedDriver F (j + 1) y'.2 [] ω) t
    have h1 : t ≤ y.2 - a := ht.trans (tsub_le_tsub_right (min_le_left _ _) _)
    have h2 : t ≤ y'.2 - a := ht.trans (tsub_le_tsub_right (min_le_right _ _) _)
    rw [catPath_of_le h1, catPath_of_le h2]
    exact hlast t ht
  | p :: l, j, a, he, hlast, t, ht => by
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 (l ++ [y]) ω) t =
      catPath (F j ω).1 (p.2 - a) (joinedDriver F (j + 1) p.2 (l ++ [y']) ω) t
    rw [he j le_rfl (by simp only [List.length_cons]; omega)]
    by_cases htp : t ≤ p.2 - a
    · simp only [catPath, htp, ↓reduceIte]
    · simp only [catPath, htp, ↓reduceIte]
      congr 1
      have hlen : j + (p :: l).length = j + 1 + l.length := by simp only [List.length_cons]; omega
      refine joinedDriver_append_last_eq ω y y' l (j + 1) p.2
        (fun i hji hi => he i (by omega) (by simp only [List.length_cons]; omega)) (fun u hu => ?_) _ ?_
      · have h := hlast u hu
        rw [hlen] at h
        exact h
      · exact tsub_le_iff_right.2 (ht.trans tsub_le_tsub_add_tsub)

/-- **ROOT2's joined read of two programs differing in their last time** agrees up to the earlier last time. -/
theorem joinedRead_append_last_eq (L : List (ℝ × ℝ≥0)) (y y' : ℝ × ℝ≥0) (R : Fin (L ++ [y]).length → RecData)
    (R' : Fin (L ++ [y']).length → RecData)
    (hR : ∀ (i : ℕ) (_ : i < L.length) (hi₁ : i < (L ++ [y]).length) (hi₂ : i < (L ++ [y']).length),
      R ⟨i, hi₁⟩ = R' ⟨i, hi₂⟩)
    (hlast : ∀ u : ℝ≥0, u ≤ min y.2 y'.2 - lastTime 0 L → recordDriver R L.length u = recordDriver R' L.length u)
    {t : ℝ≥0} (ht : t ≤ min y.2 y'.2) : joinedRead (L ++ [y]) R t = joinedRead (L ++ [y']) R' t := by
  unfold joinedRead
  rw [GW2Sde.joinedDriver_eq_const _ R, GW2Sde.joinedDriver_eq_const _ R']
  refine joinedDriver_append_last_eq () y y' L 0 0 (fun i _ _hi => ?_) (fun u hu => ?_) t (by rwa [tsub_zero])
  · have hiL : i < L.length := by omega
    have hi₁ : i < (L ++ [y]).length := by rw [List.length_append]; omega
    have hi₂ : i < (L ++ [y']).length := by rw [List.length_append]; omega
    simp only [recordDriver, hi₁, hi₂, ↓reduceDIte, hR i hiL hi₁ hi₂]
  · simpa only [zero_add] using hlast u hu

end Joined

/-! ### The canonical piece of one angle -/

section Canon

variable {κ : ℝ} (hκ : 0 < κ) (h12p : Theorem12ParamStatement.{u})
  (βA : BoundaryWord × ℝ × RecData → BoundaryWord) (c₀ : BoundaryWord) (x₀ : ℝ)

/-- **The canonical piece depends on the angles up to it and the own times before it.** -/
theorem canonDrive_congr_angle {θ θ' : ℕ → ℝ} {Δ Δ' : ℕ → ℝ≥0∞} (f : LQGMetric.DistOn upperHalfPlaneOpens) {k : ℕ}
    (hθ : ∀ j ≤ k, θ j = θ' j) (hΔ : ∀ j < k, Δ j = Δ' j) :
    canonDrive hκ h12p βA c₀ x₀ θ Δ f k = canonDrive hκ h12p βA c₀ x₀ θ' Δ' f k := by
  simp only [canonDrive, canonState_congr₂ hκ h12p βA c₀ x₀ f (k := k) (fun j hj => hθ j hj.le) hΔ,
    hθ k le_rfl]

end Canon

/-! ### Candidates of one angle -/

section Cand

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- The angles of the future programs of two candidates of one angle agree up to the candidate's index. -/
theorem specAngle_future_eq_of_angle {a a' : ℕ} (hθ : candidateAngle c r a = candidateAngle c r a') :
    ∀ j ≤ (historyProgram c r l).length, specAngle (schedSpec (rootPt r.1) (futureProgram c r l a)) j =
      specAngle (schedSpec (rootPt r.1) (futureProgram c r l a')) j := by
  intro j hj
  unfold futureProgram
  rcases lt_or_eq_of_le hj with h | rfl
  · rw [specAngle_schedSpec_append _ _ h, specAngle_schedSpec_append _ _ h]
  · rw [RootH29.specAngle_last, RootH29.specAngle_last, hθ]

/-- The own times of the future programs agree before the candidate's index. -/
theorem specDelta_future_eq (a a' : ℕ) :
    ∀ j < (historyProgram c r l).length, specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)) j =
      specDelta (schedSpec (rootPt r.1) (futureProgram c r l a')) j := by
  intro j hj
  unfold futureProgram
  rw [specDelta_schedSpec_append _ _ hj, specDelta_schedSpec_append _ _ hj]

/-- The candidate's own time in its future program is its cap. -/
theorem specDelta_future_last (a : ℕ) :
    specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)) (historyProgram c r l).length =
      (candidateCap c r a : ℝ≥0∞) := by
  unfold futureProgram
  rw [RootH29.specDelta_last]
  congr 1
  change historyTime c r l + candidateCap c r a - historyTime c r l = candidateCap c r a
  exact add_tsub_cancel_left _ _

/-- **Candidates of one angle have the same canonical piece** (every sample). -/
theorem futFam_eq_of_angle {a a' : ℕ} (hθ : candidateAngle c r a = candidateAngle c r a') (ω : Ω) :
    GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω = GW2Olm.futFam c r l a' (GW2Olm.curIdx c r l) ω :=
  canonDrive_congr_angle c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (c.h ω)
    (specAngle_future_eq_of_angle c r l hθ) (specDelta_future_eq c r l a a')

/-- **Candidates of one angle have the same lifetime** (every sample). -/
theorem candLife_eq_of_angle {a a' : ℕ} (hθ : candidateAngle c r a = candidateAngle c r a') (ω : Ω) :
    candLife c r l a ω = candLife c r l a' ω := by
  unfold candLife
  rw [futFam_eq_of_angle c r l hθ ω]

/-- **The next record of a candidate is the common piece of its angle stopped at its cap** (every sample). -/
theorem nextRecord_eq_of_angle {a a' : ℕ} (hθ : candidateAngle c r a = candidateAngle c r a') (ω : Ω) :
    nextRecord c r l a ω = recOf (candidateCap c r a : ℝ≥0∞) (GW2Olm.futFam c r l a' (GW2Olm.curIdx c r l) ω) := by
  rw [← futFam_eq_of_angle c r l hθ ω, ← specDelta_future_last c r l a]
  rfl

/-- The record driver of a good stopped record is the stopped driver. -/
theorem rdrv_recOf_of_good {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (hg : LocalExt.IsDrvGood (recHist (recOf t e))) (u : ℝ≥0) :
    rdrv (recOf t e) u = e.1 (min (u : ℝ≥0∞) (min t e.2)).toNNReal := by
  change LocalExt.histDrv (recHist (recOf t e)) ((u : ℝ).toNNReal) = _
  rw [Real.toNNReal_coe, histDrv_recHist he hg]
  rfl

/-- **Candidates of one angle explore the same flow line up to the shorter cap** (every sample whose records are
good). -/
theorem futureJoined_eq_of_angle {a a' : ℕ} (hθ : candidateAngle c r a = candidateAngle c r a') (ω : Ω)
    (hg : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    (hg' : ∀ (j : ℕ) (hj : j < (futureProgram c r l a').length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a') ω ⟨j, hj⟩)))
    {t : ℝ≥0} (ht : t ≤ historyTime c r l + min (candidateCap c r a) (candidateCap c r a')) :
    Gm.futureJoined c r l a ω t = Gm.futureJoined c r l a' ω t := by
  set k := (historyProgram c r l).length with hk
  have hkn : k < (historyProgram c r l ++
      [((candidateAngle c r a : ℝ), historyTime c r l + candidateCap c r a)]).length := by
    simp only [hk, List.length_append, List.length_singleton]; omega
  have hkn' : k < (historyProgram c r l ++
      [((candidateAngle c r a' : ℝ), historyTime c r l + candidateCap c r a')]).length := by
    simp only [hk, List.length_append, List.length_singleton]; omega
  have hdrive : canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1)
      (specAngle (schedSpec (rootPt r.1) (futureProgram c r l a)))
      (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a))) (c.h ω) k =
      canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1)
      (specAngle (schedSpec (rootPt r.1) (futureProgram c r l a')))
      (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a'))) (c.h ω) k :=
    canonDrive_congr_angle c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (c.h ω)
      (specAngle_future_eq_of_angle c r l hθ) (specDelta_future_eq c r l a a')
  unfold Gm.futureJoined
  refine joinedRead_append_last_eq (historyProgram c r l) _ _ _ _ (fun i hi hi₁ hi₂ => ?_) (fun u hu => ?_) ?_
  · change stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r l a)) i ω =
      stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r l a')) i ω
    unfold futureProgram
    rw [stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hi ω,
      stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hi ω]
  · simp only [recordDriver, ← hk, hkn, hkn', ↓reduceDIte]
    have hg1 := hg k hkn
    have hg2 := hg' k hkn'
    change LocalExt.IsDrvGood (recHist (recOf (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)) k)
      (canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle (schedSpec (rootPt r.1) (futureProgram c r l a)))
        (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a))) (c.h ω) k))) at hg1
    change LocalExt.IsDrvGood (recHist (recOf (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a')) k)
      (canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle (schedSpec (rootPt r.1) (futureProgram c r l a')))
        (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a'))) (c.h ω) k))) at hg2
    change rdrv (recOf (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)) k)
      (canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle (schedSpec (rootPt r.1) (futureProgram c r l a)))
        (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a))) (c.h ω) k)) u =
      rdrv (recOf (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a')) k)
      (canonDrive c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (specAngle (schedSpec (rootPt r.1) (futureProgram c r l a')))
        (specDelta (schedSpec (rootPt r.1) (futureProgram c r l a'))) (c.h ω) k)) u
    rw [rdrv_recOf_of_good (isRegularDriver_canonDrive _ _ _ _ _ _ _ _ _) hg1,
      rdrv_recOf_of_good (isRegularDriver_canonDrive _ _ _ _ _ _ _ _ _) hg2, hdrive,
      specDelta_future_last c r l a, specDelta_future_last c r l a']
    have hu' : u ≤ min (candidateCap c r a) (candidateCap c r a') := by
      have h := hu
      change u ≤ min (historyTime c r l + candidateCap c r a) (historyTime c r l + candidateCap c r a') -
        lastTime 0 (historyProgram c r l) at h
      rwa [← GW2Sde.historyTime_eq_lastTime, min_add_add_left, add_tsub_cancel_left] at h
    rw [← min_assoc, ← min_assoc, min_eq_left (ENNReal.coe_le_coe.2 (hu'.trans (min_le_left _ _))),
      min_eq_left (ENNReal.coe_le_coe.2 (hu'.trans (min_le_right _ _)))]
  · change t ≤ min (historyTime c r l + candidateCap c r a) (historyTime c r l + candidateCap c r a')
    rwa [min_add_add_left]

end Cand

/-! ### Almost surely, for all histories and all pairs of candidates of one angle -/

section Ae

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)

include h13 in
/-- **D35 (D-b): candidates of one angle explore the same flow line up to the shorter cap**, almost surely, for every
history and every pair of candidates of one angle. -/
theorem ae_schedW_eq_of_angle :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a a' : ℕ), candidateAngle c r a = candidateAngle c r a' →
      ∀ t : ℝ≥0, t ≤ historyTime c r l + min (candidateCap c r a) (candidateCap c r a') →
        schedW c r l a t ω = schedW c r l a' t ω := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hω l a a' hθ t ht
  unfold schedW
  by_cases hold : oldSuccess c r l ω
  · simp only [hold, ↓reduceIte]
    exact futureJoined_eq_of_angle c r l hθ ω (hω l a hold).1 (hω l a' hold).1 ht
  · simp only [hold, ↓reduceIte]

include h13 in
/-- **D35 (D-b), the future pairs**: on the history's success, the future pair of the shorter-cap candidate of one
angle is the longer-cap candidate's joined driver recorded at the shorter last time. -/
theorem ae_futurePair_eq_of_angle :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a a' : ℕ), candidateAngle c r a = candidateAngle c r a' →
      candidateCap c r a ≤ candidateCap c r a' → oldSuccess c r l ω →
        futurePair c r l a ω = ((futurePair c r l a' ω).1,
          StagedEntrance.Strip.recOfDriver (historyTime c r l + candidateCap c r a) (Gm.futureJoined c r l a' ω)) := by
  filter_upwards [Gm.ae_futureJoined_trace h13 c r] with ω hω l a a' hθ hcap hold
  refine Prod.ext rfl ?_
  rw [Gm.futurePair_snd, Gm.lastTime_futureProgram]
  unfold StagedEntrance.Strip.recOfDriver
  congr 2
  funext q
  refine futureJoined_eq_of_angle c r l hθ ω (hω l a hold).1 (hω l a' hold).1 ?_
  rw [min_eq_left hcap]
  exact min_le_right _ _

end Ae

end InteractingSLE.Theorem14.GW2Rd

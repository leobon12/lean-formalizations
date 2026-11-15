/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.Words
import InteractingSLE.Spec.Zhan.WordsGroup
import InteractingSLE.Spec.Zhan.Avoid

/-!
# The merge energy: side errors, merging, reflection

Packet PROVE-ZHAN-B4. The change of drift of the merge (`Words.lean`) is the sum of the two *side errors*
`sideErr ρ w v = ∑ᵢ ρᵢ ((w − v_last)⁻¹ − (w − vᵢ)⁻¹)` (the coth errors of Astra §3, L1590–L1594, in chordal form).
This file reduces `MergeEnergyStatement` to the bounded energy of the left side error for words whose marks are
strictly ordered on both sides:

* the side error is unchanged by merging two adjacent coincident marks (`sideErr_mergeAdj`), so by induction on the
  number of marks it suffices to treat strictly ordered words (`leftEnergyStatement_of_strict`);
* the right side error is the left side error of the reflected evolution, up to sign (`sideErr_neg`);
* `(a + b)² ≤ 2a² + 2b²` (`mergeEnergyStatement_of_leftEnergy`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Zhan

open Sec2 Girsanov

variable {n nL nR : ℕ}

/-- **The side error**: `∑ᵢ ρᵢ ((w − v_last)⁻¹ − (w − vᵢ)⁻¹)`, the drift removed by moving every weight of a side onto
its outermost mark. -/
def sideErr (ρ : Fin n → ℝ) (w : ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i, ρ i * ((w - v (lastOf i))⁻¹ - (w - v i)⁻¹)

theorem sum_outerW_sub_div (ρ : Fin n → ℝ) (w : ℝ) (v : Fin n → ℝ) :
    ∑ i, (outerW ρ i - ρ i) / (w - v i) = sideErr ρ w v := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sideErr]
  set l : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ with hl
  have hlast : ∀ i : Fin n, lastOf i = l := fun i => rfl
  have h1 : ∑ i, outerW ρ i / (w - v i) = (∑ i, ρ i) * (w - v l)⁻¹ := by
    rw [Finset.sum_congr rfl fun i _ => outerW_div_eq i (fun k => w - v k)]
    simp only [hlast, div_eq_mul_inv, ← Finset.sum_mul, sum_outerW]
  rw [Finset.sum_congr rfl fun i _ => sub_div (outerW ρ i) (ρ i) (w - v i), Finset.sum_sub_distrib, h1]
  simp only [sideErr, hlast, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, div_eq_mul_inv]

/-- The side error of the reflected side: `sideErr ρ (−w) (−v) = −sideErr ρ w v`. -/
theorem sideErr_neg (ρ : Fin n → ℝ) (w : ℝ) (v : Fin n → ℝ) :
    sideErr ρ (-w) (fun i => -v i) = -sideErr ρ w v := by
  simp only [sideErr, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show -w - -v (lastOf i) = -(w - v (lastOf i)) by ring, show -w - -v i = -(w - v i) by ring,
    inv_neg, inv_neg]
  ring

theorem lastOf_eq_last (i : Fin (n + 1)) : lastOf i = Fin.last n := by
  ext; simp [lastOf]

theorem succAbove_last_eq (j : Fin (n + 1)) (v : Fin (n + 2) → ℝ) (hv : v j.castSucc = v j.succ) :
    v (j.succ.succAbove (Fin.last n)) = v (Fin.last (n + 1)) := by
  by_cases hj : j = Fin.last n
  · subst hj
    rw [Fin.succ_last, Fin.succAbove_last, hv, Fin.succ_last]
  · have hle : j.succ ≤ (Fin.last n).castSucc := by
      rw [Fin.le_def]
      simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_last]
      have := Fin.val_lt_last hj
      omega
    rw [Fin.succAbove_of_le_castSucc _ _ hle, Fin.succ_last]

/-- **The side error is unchanged by merging two adjacent coincident marks.** -/
theorem sideErr_mergeAdj (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) (w : ℝ) (v : Fin (n + 2) → ℝ)
    (hv : v j.castSucc = v j.succ) :
    sideErr (mergeAdj ρ j) w (fun k => v (j.succ.succAbove k)) = sideErr ρ w v := by
  simp only [sideErr, lastOf_eq_last, mul_sub, Finset.sum_sub_distrib]
  rw [succAbove_last_eq j v hv, ← Finset.sum_mul, ← Finset.sum_mul, sum_mergeAdj]
  congr 1
  exact sum_mergeAdj_mul ρ j (fun i => (w - v i)⁻¹) (by simp only [hv])

/-! ### Side energies -/

/-- The side error along a path at time `s`. -/
def sideErrAt (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) (s : ℝ≥0) : ℝ :=
  sideErr ρ (w s) (fun i => v i s)

/-- **Bounded side energy**: the square of the side error is integrable on bounded intervals and its integrals
are bounded uniformly in the horizon. -/
def HasBoundedSideEnergy (ρ : Fin n → ℝ) (w : ℝ≥0 → ℝ) (v : Fin n → ℝ≥0 → ℝ) : Prop :=
  ∃ m : ℝ, ∀ T : ℝ≥0, IntervalIntegrable (fun s : ℝ => sideErrAt ρ w v s.toNNReal ^ 2) volume 0 T ∧
    ∫ s in (0 : ℝ)..T, sideErrAt ρ w v s.toNNReal ^ 2 ≤ m

theorem HasBoundedSideEnergy.congr {n' : ℕ} {ρ : Fin n → ℝ} {ρ' : Fin n' → ℝ} {w w' : ℝ≥0 → ℝ}
    {v : Fin n → ℝ≥0 → ℝ} {v' : Fin n' → ℝ≥0 → ℝ} (h : HasBoundedSideEnergy ρ w v)
    (he : ∀ s, sideErrAt ρ' w' v' s ^ 2 = sideErrAt ρ w v s ^ 2) : HasBoundedSideEnergy ρ' w' v' := by
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun T => ⟨(hm T).1.congr fun s _ => (he _).symm, ?_⟩⟩
  rw [intervalIntegral.integral_congr fun s _ => he s.toNNReal]
  exact (hm T).2

theorem HasBoundedSideEnergy.of_mergeAdj {ρ : Fin (n + 2) → ℝ} {w : ℝ≥0 → ℝ} {v : Fin (n + 2) → ℝ≥0 → ℝ}
    (j : Fin (n + 1)) (hv : ∀ s, v j.castSucc s = v j.succ s)
    (h : HasBoundedSideEnergy (mergeAdj ρ j) w (fun k => v (j.succ.succAbove k))) :
    HasBoundedSideEnergy ρ w v := by
  refine HasBoundedSideEnergy.congr h fun s => ?_
  have e := sideErr_mergeAdj ρ j (w s) (fun i => v i s) (hv s)
  unfold sideErrAt
  rw [← e]

/-- **The merge energy is the energy of the sum of the two side errors.** -/
theorem changeEnergy_eq {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    changeEnergy κ ρL (outerW ρL) ρR (outerW ρR) W VL VR T ω =
      1 / κ * ∫ s in (0 : ℝ)..T, (sideErrAt ρL (fun t => W t ω) (fun i t => VL i t ω) s.toNNReal +
        sideErrAt ρR (fun t => W t ω) (fun i t => VR i t ω) s.toNNReal) ^ 2 := by
  unfold changeEnergy
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  rw [Fin.sum_univ_add]
  simp only [weightDiff, allMarks, Fin.addCases_left, Fin.addCases_right, sum_outerW_sub_div, sideErrAt]

/-- The merge energy is bounded when both side energies are. -/
theorem exists_changeEnergy_le {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hL : HasBoundedSideEnergy ρL (fun t => W t ω) (fun i t => VL i t ω))
    (hR : HasBoundedSideEnergy ρR (fun t => W t ω) (fun i t => VR i t ω)) :
    ∃ m : ℝ, ∀ T : ℝ≥0, changeEnergy κ ρL (outerW ρL) ρR (outerW ρR) W VL VR T ω ≤ m := by
  obtain ⟨mL, hmL⟩ := hL
  obtain ⟨mR, hmR⟩ := hR
  refine ⟨1 / κ * (2 * max mL 0 + 2 * max mR 0), fun T => ?_⟩
  rw [changeEnergy_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set a := fun s : ℝ => sideErrAt ρL (fun t => W t ω) (fun i t => VL i t ω) s.toNNReal
  set b := fun s : ℝ => sideErrAt ρR (fun t => W t ω) (fun i t => VR i t ω) s.toNNReal
  have hsum : IntervalIntegrable (fun s => 2 * a s ^ 2 + 2 * b s ^ 2) volume 0 T :=
    ((hmL T).1.const_mul 2).add ((hmR T).1.const_mul 2)
  have hbound : ∫ s in (0 : ℝ)..T, (2 * a s ^ 2 + 2 * b s ^ 2) ≤ 2 * max mL 0 + 2 * max mR 0 := by
    rw [intervalIntegral.integral_add ((hmL T).1.const_mul 2) ((hmR T).1.const_mul 2),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have := (hmL T).2
    have := (hmR T).2
    nlinarith [le_max_left mL 0, le_max_left mR 0]
  by_cases hint : IntervalIntegrable (fun s => (a s + b s) ^ 2) volume 0 T
  · refine le_trans (intervalIntegral.integral_mono_on (NNReal.coe_nonneg T) hint hsum
      fun s _ => ?_) hbound
    nlinarith [sq_nonneg (a s - b s)]
  · rw [intervalIntegral.integral_undef hint]
    positivity

/-! ### Reduction of the merge energy to the left side of strictly ordered words -/

/-- **Bounded energy of the left side error** for every ordered admissible word with marks separated from the seed. -/
def LeftEnergyStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsOrderedForceWord xL xR → Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR → (∀ i, xL i < 0) →
      (∀ j, 0 < xR j) → IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, HasBoundedSideEnergy ρL (fun t => W t ω) (fun i t => VL i t ω)

/-- The same for words whose marks are strictly ordered on both sides. -/
def StrictLeftEnergyStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    StrictAnti xL → StrictMono xR →
    IsOrderedForceWord xL xR → Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR → (∀ i, xL i < 0) →
      (∀ j, 0 < xR j) → IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, HasBoundedSideEnergy ρL (fun t => W t ω) (fun i t => VL i t ω)

/-- **The merge energy from the left energy** (the right side by reflection). -/
theorem mergeEnergyStatement_of_leftEnergy {κ : ℝ} (hκ : 0 < κ) (h : LeftEnergyStatement.{u} κ) :
    MergeEnergyStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hF hadm hxL hxR hE
  have hL := h xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hxL hxR hE
  have hR := h (-xR) (-xL) ρR ρL P 𝓕 (-W) (fun i => -VR i) (fun i => -VL i) (-B) ζ
    (isOrderedForceWord_reflect hF) (hasAdmissiblePartialSums_reflect hF hadm)
    (fun j => by simpa using hxR j) (fun i => by simpa using hxL i)
    (InteractingSLE.IsIntegratedSLEEvolution.reflect hE)
  filter_upwards [hL, hR] with ω hLω hRω
  refine exists_changeEnergy_le hκ hLω (hRω.congr fun s => ?_)
  simp only [sideErrAt, Pi.neg_apply]
  rw [sideErr_neg, neg_sq]

/-! ### Merging preserves the hypotheses -/

theorem sum_filter_mergeAdj (ρ : Fin (n + 2) → ℝ) (j : Fin (n + 1)) (p : Fin (n + 2) → Prop) [DecidablePred p]
    (hp : p j.castSucc ↔ p j.succ) :
    (∑ k ∈ Finset.univ.filter (fun k => p (j.succ.succAbove k)), mergeAdj ρ j k) =
      ∑ i ∈ Finset.univ.filter p, ρ i := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have h := sum_mergeAdj_mul ρ j (fun i => if p i then 1 else 0) (by simp only [hp])
  simp only [mul_ite, mul_one, mul_zero] at h
  exact h

theorem hasAdmissiblePartialSums_mergeAdjL {k : ℝ} {xL ρL : Fin (n + 2) → ℝ} {xR ρR : Fin nR → ℝ}
    (j : Fin (n + 1)) (hj : xL j.castSucc = xL j.succ) (h : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) :
    Sec4.HasAdmissiblePartialSums k (mergeAdj ρL j) ρR (fun m => xL (j.succ.succAbove m)) xR := by
  refine ⟨fun x hx ⟨m, hm⟩ => ?_, h.2⟩
  rw [sum_filter_mergeAdj ρL j (fun i => x < xL i) (by rw [hj])]
  exact h.1 x hx ⟨_, hm⟩

theorem hasAdmissiblePartialSums_mergeAdjR {k : ℝ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin (n + 2) → ℝ}
    (j : Fin (n + 1)) (hj : xR j.castSucc = xR j.succ) (h : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) :
    Sec4.HasAdmissiblePartialSums k ρL (mergeAdj ρR j) xL (fun m => xR (j.succ.succAbove m)) := by
  refine ⟨h.1, fun x hx ⟨m, hm⟩ => ?_⟩
  rw [sum_filter_mergeAdj ρR j (fun i => xR i ≤ x) (by rw [hj])]
  exact h.2 x hx ⟨_, hm⟩

theorem exists_adj_eq_of_not_strictMono {f : Fin (n + 2) → ℝ} (hm : Monotone f) (hs : ¬ StrictMono f) :
    ∃ j : Fin (n + 1), f j.castSucc = f j.succ := by
  rw [Fin.strictMono_iff_lt_succ] at hs
  push Not at hs
  obtain ⟨j, hj⟩ := hs
  exact ⟨j, le_antisymm (hm (Fin.castSucc_le_succ j)) hj⟩

theorem exists_adj_eq_of_not_strictAnti {f : Fin (n + 2) → ℝ} (hm : Antitone f) (hs : ¬ StrictAnti f) :
    ∃ j : Fin (n + 1), f j.castSucc = f j.succ := by
  rw [Fin.strictAnti_iff_succ_lt] at hs
  push Not at hs
  obtain ⟨j, hj⟩ := hs
  exact ⟨j, le_antisymm hj (hm (Fin.castSucc_le_succ j))⟩

theorem strictMono_of_le_one {m : ℕ} (hm : m ≤ 1) (f : Fin m → ℝ) : StrictMono f := fun i j hij => by
  exfalso; have := i.2; have := j.2; rw [Fin.lt_def] at hij; omega

theorem strictAnti_of_le_one {m : ℕ} (hm : m ≤ 1) (f : Fin m → ℝ) : StrictAnti f := fun i j hij => by
  exfalso; have := i.2; have := j.2; rw [Fin.lt_def] at hij; omega

/-- **Reduction to strictly ordered words** (merging adjacent coincident marks, by induction on their number). -/
theorem leftEnergyStatement_of_strict {κ : ℝ} (hκ : 0 < κ) (h : StrictLeftEnergyStatement.{u} κ) :
    LeftEnergyStatement.{u} κ := by
  suffices H : ∀ N : ℕ, ∀ {nL nR : ℕ}, nL + nR = N → ∀ (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
      (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsOrderedForceWord xL xR → Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR → (∀ i, xL i < 0) →
        (∀ j, 0 < xR j) → IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
          ∀ᵐ ω ∂P, HasBoundedSideEnergy ρL (fun t => W t ω) (fun i t => VL i t ω) by
    intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ
    exact H (nL + nR) rfl xL xR ρL ρR P 𝓕 W VL VR B ζ
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro nL nR hN xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hF hadm hxL hxR hE
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ xL xR ρL ρR P 𝓕 W VL VR B ζ hF hadm hE).mono fun _ h => h.1
  by_cases hsL : StrictAnti xL
  · by_cases hsR : StrictMono xR
    · exact h xL xR ρL ρR P 𝓕 W VL VR B ζ hsL hsR hF hadm hxL hxR hE
    · rcases nR with _ | _ | m
      · exact absurd (strictMono_of_le_one (by norm_num) xR) hsR
      · exact absurd (strictMono_of_le_one le_rfl xR) hsR
      · obtain ⟨j, hj⟩ := exists_adj_eq_of_not_strictMono hF.2.2.1 hsR
        have hE' := IsIntegratedSLEEvolution.mergeAdjR j hj hE hζ
        exact ih (nL + (m + 1)) (by omega) rfl xL (fun k => xR (j.succ.succAbove k)) ρL (mergeAdj ρR j) P 𝓕 W VL
          (fun k => VR (j.succ.succAbove k)) B ζ
          ⟨hF.1, hF.2.1, Monotone.comp hF.2.2.1 (Fin.strictMono_succAbove _).monotone, fun k => hF.2.2.2 _⟩
          (hasAdmissiblePartialSums_mergeAdjR j hj hadm) hxL (fun k => hxR _) hE'
  · rcases nL with _ | _ | m
    · exact absurd (strictAnti_of_le_one (by norm_num) xL) hsL
    · exact absurd (strictAnti_of_le_one le_rfl xL) hsL
    · obtain ⟨j, hj⟩ := exists_adj_eq_of_not_strictAnti hF.1 hsL
      have hE' := IsIntegratedSLEEvolution.mergeAdjL j hj hE hζ
      have hih := ih ((m + 1) + nR) (by omega) rfl (fun k => xL (j.succ.succAbove k)) xR (mergeAdj ρL j) ρR P 𝓕
        W (fun k => VL (j.succ.succAbove k)) VR B ζ
        ⟨Antitone.comp_monotone hF.1 (Fin.strictMono_succAbove _).monotone, fun k => hF.2.1 _, hF.2.2.1, hF.2.2.2⟩
        (hasAdmissiblePartialSums_mergeAdjL j hj hadm) (fun k => hxL _) hxR hE'
      filter_upwards [hih, hE.2.2.2.2, hζ] with ω hω hp hζω
      rw [hζω] at hp
      exact HasBoundedSideEnergy.of_mergeAdj j
        (fun s => InteractingSLE.IsIntegratedSLEPath.vL_eq_of_xL_eq hp ENNReal.coe_lt_top hj) hω

/-- **The merge energy from strictly ordered words.** -/
theorem mergeEnergyStatement_of_strict {κ : ℝ} (hκ : 0 < κ) (h : StrictLeftEnergyStatement.{u} κ) :
    MergeEnergyStatement.{u} κ :=
  mergeEnergyStatement_of_leftEnergy hκ (leftEnergyStatement_of_strict hκ h)

/-- `SeparatedTransienceStatement κ` (`0 < κ ≤ 4`) from the left energy of strictly ordered words. -/
theorem separatedTransienceStatement_of_strictLeftEnergy {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (h : StrictLeftEnergyStatement.{u} κ) : SeparatedTransienceStatement.{u} κ :=
  separatedTransienceStatement_of_mergeEnergy hκ hκ4 (mergeEnergyStatement_of_strict hκ h)

/-- Aux. lemma 7 (`0 < κ ≤ 4`) from the left energy of strictly ordered words. -/
theorem aux7Statement_of_strictLeftEnergy {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (h : StrictLeftEnergyStatement.{u} κ) : Sec4.Aux7Statement.{u} κ :=
  aux7Statement_of_mergeEnergy hκ hκ4 (mergeEnergyStatement_of_strict hκ h)

/-- Wang–Wu's input 8.3 from the left energy of strictly ordered words at `κ = 4`. -/
theorem zhanNonboundaryTransience_of_strictLeftEnergy (h : StrictLeftEnergyStatement.{u} 4) :
    WangWu.ZhanNonboundaryTransience.{u} :=
  zhanNonboundaryTransience_of_mergeEnergy (mergeEnergyStatement_of_strict (by norm_num) h)

end InteractingSLE.Zhan

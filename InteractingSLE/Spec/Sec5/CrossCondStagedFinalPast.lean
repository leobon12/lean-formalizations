/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalImage
import InteractingSLE.Spec.Sec5.CrossCondStagedMeanCat

/-!
# The staged cross-conditioning law: the stage word read off the records, and the identification per sample

Packet PROVE-CROSSCOND-STAGED4 (S2). Combines the level invariant of the iterated stop word
(`CrossCondStagedFinalWord`), the identification of its levels with the base images of the shifted chain
(`CrossCondStagedFinalLevels`) and the per-sample identification with the image stage word
(`CrossCondStagedFinalImage`):

* `chartAL_neg_of_isProperArc`, `chartAR_pos_of_isProperArc`: the base images of a proper-arc trace stay off the
  driver at positive times (the left base goes to `0 ≠ η(t)`); so do those of every shifted chain
  (`futureArc`), which discharges the gap hypotheses of the flow property;
* **`isLeftLevels_pastWord_chartAL`**, **`isRightLevels_pastWord_chartAR`**: if the record drivers are the pieces of
  one driver `V` whose trace is a proper arc, the iterated stop word `pastWord (stopWord κ) c₀ x₀ θ k u` has the side
  heights `∓λ − θ_j χ` between the base images `chartAL/AR (shiftDrive V (S j)) (S k − S j)` of the shifted chain;
* `catN_add_start`, `shiftDrive_rpath_catN`: the concatenated record driver of `CrossCondStagedMeanCat` restarts with
  piece `i` at its start time (the hypothesis of the levels for the staged chart `catChartN`);
* **`eqOn_imgChart_pastWord`**: the per-sample staged mean identification for the iterated stop word of records whose
  drivers are the pieces of the prefix driver `Wα`.

Deterministic; R48: no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open QuantumZipper.RS (shiftDrive)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal Real

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

open WangWu hiding ratPt exists_ratPt_dist_lt
open GlueImg Theta Cond44Ref Word49 Sec7.StripSysField StagedLaw
open MartChar.RealFlow Restart.RetAux79 Restart Exist.StagedLaw Exist.Staged Staged Theorem14.GW2Schedule
open Sec7.StripSideHeightProb (catPath catPath_of_le)

/-! ### The base images of a proper-arc trace stay off the driver -/

section Gap

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

theorem chartAL_neg_of_isProperArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) : chartAL W T < 0 := by
  rcases (chartAL_nonpos hW hT.le (W' := W)).lt_or_eq with h | h
  · exact h
  · have h1 := extendFrom_chartAL_eq_zero hη hγ hW hW0 hT
    rw [h, Complex.ofReal_zero, WangWu.extendFrom_zero hη hW hW0 hT.le] at h1
    have h2 := hγ.mem_H T hT
    rw [h1] at h2
    exact absurd h2 (by simp [QuantumZipper.H])

theorem chartAR_pos_of_isProperArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {T : ℝ} (hT : 0 < T) : 0 < chartAR W T := by
  rcases (chartAR_nonneg hW hT.le (W' := W)).lt_or_eq with h | h
  · exact h
  · have h1 := extendFrom_chartAR_eq_zero hη hγ hW hW0 hT
    rw [← h, Complex.ofReal_zero, WangWu.extendFrom_zero hη hW hW0 hT.le] at h1
    have h2 := hγ.mem_H T hT
    rw [h1] at h2
    exact absurd h2 (by simp [QuantumZipper.H])

/-- The shifted chains of a proper-arc trace have their base images off the driver at positive times. -/
theorem chartA_shiftDrive_of_isProperArc (hη : IsLoewnerTrace W η) (hγ : IsProperArc η) (hW : Continuous W)
    (hW0 : W 0 = 0) {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) :
    chartAL (shiftDrive W a) r < 0 ∧ 0 < chartAR (shiftDrive W a) r := by
  have hη' := StagedLaw.isLoewnerTrace_futureArc hη hW hW0 ha
  have hγ' := WangWu.isProperArc_futureArc hη hγ hW hW0 ha
  have hWs := QuantumZipper.RS.continuous_shiftDrive hW a
  exact ⟨chartAL_neg_of_isProperArc hη' hγ' hWs (shiftDrive_zero_apply W a) hr,
    chartAR_pos_of_isProperArc hη' hγ' hWs (shiftDrive_zero_apply W a) hr⟩

end Gap

/-! ### The levels of the iterated stop word are the base images -/

section Levels

theorem IsLeftLevels.congr_lev {c : BoundaryWord} {k : ℕ} {p p' ht : ℕ → ℝ} (h : IsLeftLevels c k p ht)
    (he : ∀ j ≤ k, p j = p' j) : IsLeftLevels c k p' ht := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(he k le_rfl) ▸ h1, fun j hj => ?_, fun y hy hy0 hy1 => ?_, fun j hj y hy1 hy2 hyJ => ?_⟩
  · rw [← he j hj.le, ← he (j + 1) hj]; exact h2 j hj
  · obtain ⟨j, hj1, hjk, rfl⟩ := h3 y hy (by rw [he 0 (Nat.zero_le k)]; exact hy0) hy1
    exact ⟨j, hj1, hjk, he j hjk.le⟩
  · exact h4 j hj y (by rw [he j hj.le]; exact hy1) (by rw [he (j + 1) hj]; exact hy2) hyJ

theorem IsRightLevels.congr_lev {c : BoundaryWord} {k : ℕ} {q q' ht : ℕ → ℝ} (h : IsRightLevels c k q ht)
    (he : ∀ j ≤ k, q j = q' j) : IsRightLevels c k q' ht := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨(he k le_rfl) ▸ h1, fun j hj => ?_, fun y hy hy0 hy1 => ?_, fun j hj y hy1 hy2 hyJ => ?_⟩
  · rw [← he j hj.le, ← he (j + 1) hj]; exact h2 j hj
  · obtain ⟨j, hj1, hjk, rfl⟩ := h3 y hy hy0 (by rw [he 0 (Nat.zero_le k)]; exact hy1)
    exact ⟨j, hj1, hjk, he j hjk.le⟩
  · exact h4 j hj y (by rw [he (j + 1) hj]; exact hy1) (by rw [he j hj.le]; exact hy2) hyJ

theorem recSeqT_nonneg {k : ℕ} (u : PastData k) (i : ℕ) : 0 ≤ recSeqT u i := by
  unfold recSeqT
  split_ifs
  · exact rtime_nonneg _
  · exact le_rfl

theorem start_nonneg {k : ℕ} (u : PastData k) (j : ℕ) : 0 ≤ startT (recSeqT u) j := by
  have := startT_mono (recSeqT_nonneg u) (Nat.zero_le j)
  rwa [startT_zero] at this

variable {κ : ℝ} (c₀ : BoundaryWord) (x₀ : ℝ) (θ : ℕ → ℝ) {V : ℝ → ℝ} {η : ℝ → ℂ}

/-- **The left side heights of the iterated stop word at the base images of the shifted chain.** -/
theorem isLeftLevels_pastWord_chartAL (hκ : 0 < κ) {k : ℕ} (u : PastData k) (hη : IsLoewnerTrace V η)
    (hγ : IsProperArc η) (hV : Continuous V) (hV0 : V 0 = 0)
    (hw : ∀ i, EqOn (recSeqW u i) (shiftDrive V (startT (recSeqT u) i)) (Icc 0 (recSeqT u i))) :
    IsLeftLevels (pastWord (stopWord κ) c₀ x₀ θ k u) k
      (fun j => chartAL (shiftDrive V (startT (recSeqT u) j)) (startT (recSeqT u) k - startT (recSeqT u) j))
      (fun j => -sleLambda κ - θ j * chiC κ) := by
  have h := isLeftLevels_pastWord c₀ x₀ θ hκ k u
  rw [levL_eq_levLs] at h
  refine h.congr_lev fun j hj => levLs_eq_chartAL hV (recSeqT_nonneg u) hw (K := k)
    (fun j' _ r hr _ => (chartA_shiftDrive_of_isProperArc hη hγ hV hV0 (start_nonneg u j') hr).1) k le_rfl j hj
/-- **The right side heights of the iterated stop word at the base images of the shifted chain.** -/
theorem isRightLevels_pastWord_chartAR (hκ : 0 < κ) {k : ℕ} (u : PastData k) (hη : IsLoewnerTrace V η)
    (hγ : IsProperArc η) (hV : Continuous V) (hV0 : V 0 = 0)
    (hw : ∀ i, EqOn (recSeqW u i) (shiftDrive V (startT (recSeqT u) i)) (Icc 0 (recSeqT u i))) :
    IsRightLevels (pastWord (stopWord κ) c₀ x₀ θ k u) k
      (fun j => chartAR (shiftDrive V (startT (recSeqT u) j)) (startT (recSeqT u) k - startT (recSeqT u) j))
      (fun j => sleLambda κ - θ j * chiC κ) := by
  have h := isRightLevels_pastWord c₀ x₀ θ hκ k u
  rw [levR_eq_levRs] at h
  refine h.congr_lev fun j hj => levRs_eq_chartAR hV (recSeqT_nonneg u) hw (K := k)
    (fun j' _ r hr _ => (chartA_shiftDrive_of_isProperArc hη hγ hV hV0 (start_nonneg u j') hr).2) k le_rfl j hj

end Levels

/-! ### The concatenated record driver restarts with each piece -/

section Cat

variable {w : ℕ → ℝ≥0 → ℝ} {T : ℕ → ℝ≥0}

/-- The start of piece `i` in `ℝ≥0`. -/
def startN (T : ℕ → ℝ≥0) (i : ℕ) : ℝ≥0 := ∑ j ∈ Finset.range i, T j

theorem startN_succ (T : ℕ → ℝ≥0) (i : ℕ) : startN T (i + 1) = startN T i + T i := by
  simp only [startN, Finset.sum_range_succ]

theorem startN_mono (T : ℕ → ℝ≥0) {i j : ℕ} (hij : i ≤ j) : startN T i ≤ startN T j :=
  Finset.sum_le_sum_of_subset (Finset.range_mono hij)

theorem cumT_eq_startN (T : ℕ → ℝ≥0) (k : ℕ) : cumT T k = startN T (k + 1) := rfl

theorem coe_startN (T : ℕ → ℝ≥0) (i : ℕ) : (startN T i : ℝ) = startT (fun j => (T j : ℝ)) i := by
  simp only [startN, startT, NNReal.coe_sum]

/-- **The concatenation restarts with piece `i`**: `catN w T k (S i + r) = catN w T k (S i) + w i r` for `i ≤ k`,
`r ≤ T i`. -/
theorem catN_add_start (hw0 : ∀ j, w j 0 = 0) : ∀ k i, i ≤ k → ∀ r : ℝ≥0, r ≤ T i →
    catN w T k (startN T i + r) = catN w T k (startN T i) + w i r
  | 0, i, hi, r, _ => by
    obtain rfl := Nat.le_zero.1 hi
    simp only [startN, Finset.range_zero, Finset.sum_empty, zero_add]
    change w 0 r = w 0 0 + w 0 r
    rw [hw0, zero_add]
  | k + 1, i, hi, r, hr => by
    change catPath (catN w T k) (cumT T k) (w (k + 1)) (startN T i + r) =
      catPath (catN w T k) (cumT T k) (w (k + 1)) (startN T i) + w i r
    rcases Nat.lt_or_ge i (k + 1) with hik | hik
    · have hik' := Nat.lt_succ_iff.1 hik
      have h1 : startN T i + r ≤ cumT T k := by
        rw [cumT_eq_startN]
        calc startN T i + r ≤ startN T i + T i := add_le_add_right hr _
          _ = startN T (i + 1) := (startN_succ T i).symm
          _ ≤ startN T (k + 1) := startN_mono T (by omega)
      have h2 : startN T i ≤ cumT T k := le_trans le_self_add h1
      rw [catPath_of_le h1, catPath_of_le h2]
      exact catN_add_start hw0 k i hik' r (hr.trans le_rfl)
    · obtain rfl : i = k + 1 := le_antisymm hi hik
      rw [← cumT_eq_startN, catPath_of_le le_rfl]
      by_cases hle : cumT T k + r ≤ cumT T k
      · have hr0 : r = 0 := le_antisymm (by simpa using hle) (zero_le (a := r))
        rw [hr0, add_zero, catPath_of_le le_rfl, hw0, add_zero]
      · simp only [catPath, hle, ↓reduceIte, add_tsub_cancel_left]

/-- **The shifted concatenated record driver is the record driver of piece `i`** on `[0, T i]` (`i ≤ k`). -/
theorem shiftDrive_rpath_catN (hw0 : ∀ j, w j 0 = 0) {k i : ℕ} (hi : i ≤ k) :
    EqOn (Ito.rpath (w i)) (shiftDrive (Ito.rpath (catN w T k)) (startT (fun j => (T j : ℝ)) i))
      (Icc 0 (T i : ℝ)) := by
  intro r hr
  have hr' : r.toNNReal ≤ T i := Real.toNNReal_le_iff_le_coe.2 hr.2
  have e : (startT (fun j => (T j : ℝ)) i + r).toNNReal = startN T i + r.toNNReal := by
    rw [← coe_startN, Real.toNNReal_add (NNReal.coe_nonneg _) hr.1, Real.toNNReal_coe]
  simp only [Ito.rpath, shiftDrive]
  rw [e, ← coe_startN, Real.toNNReal_coe, catN_add_start hw0 k i hi _ hr']
  ring

end Cat
/-! ### The staged mean identification for the iterated stop word, per sample -/

section Assembly

variable {nL nR : ℕ} {κ : ℝ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (θ : ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {Wα ω W' : ℝ → ℝ} {t s T : ℝ} {ang : ℕ → ℝ} {ℓ : ℕ}

/-- **The image times of the switch points** (`StagedLaw.exists_imgTime` at every switch). -/
theorem exists_imgTimes {α η' : ℝ → ℂ} (hα : IsLoewnerTrace Wα α) (hαp : IsProperArc α) (ht : 0 ≤ t)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 ≤ T) (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t)) {S : ℕ → ℝ}
    (hS : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < S m ∧ S m < t) :
    ∃ A : ℕ → ℝ, ∀ m, 1 ≤ m → m ≤ ℓ → 0 < A m ∧ A m < T ∧ η' (A m) = revChart ω s (α (S m)) := by
  classical
  have h : ∀ m, ∃ A : ℝ, 1 ≤ m → m ≤ ℓ → 0 < A ∧ A < T ∧ η' A = revChart ω s (α (S m)) := by
    intro m
    by_cases hm : 1 ≤ m ∧ m ≤ ℓ
    · obtain ⟨A, hA⟩ := exists_imgTime hα hαp ht hω hω0 hs hη' hη'p hT hdisj hK' htip (hS m hm.1 hm.2).1
        (hS m hm.1 hm.2).2
      exact ⟨A, fun _ _ => hA⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hm⟩
  choose A hA using h
  exact ⟨A, hA⟩

/-- The switch times of records with positive own times lie strictly inside the prefix's time. -/
theorem startT_pos_lt {k : ℕ} (u : PastData (k + 1)) (hpos : ∀ i ≤ k, 0 < recSeqT u i) :
    ∀ m, 1 ≤ m → m ≤ k → 0 < startT (recSeqT u) m ∧ startT (recSeqT u) m < startT (recSeqT u) (k + 1) := by
  intro m hm1 hmk
  have hT := recSeqT_nonneg u
  refine ⟨?_, ?_⟩
  · have h1 := startT_mono hT hm1
    rw [startT_succ, startT_zero, zero_add] at h1
    exact (hpos 0 (Nat.zero_le k)).trans_le h1
  · have h1 := startT_mono hT hmk
    rw [startT_succ]
    linarith [hpos k le_rfl]

/-- **The staged mean identification for the iterated stop word, per sample** (S2 for the actual staged words). Let
`u` be the records of the pieces `0, …, ℓ` (positive own times), whose drivers are the pieces of the prefix driver
`Wα` (`hw`), `t` the total own time, `c = pastWord (stopWord κ) c₀ x₀ θ (ℓ + 1) u` the word of the field after the
pieces (the explicit witness of `GW2Schedule.stageWitness_all`), `A m` the image times of the switch points. Under
the counterflow-side hypotheses of CROSSCOND-THETA, the flow side's limit with `c`'s mean (`hFl`) and Aux. 28's
uniqueness, the union mean is the image stage word's candidate minus `θ_ℓ χ`. -/
theorem eqOn_imgChart_pastWord (c₀ : BoundaryWord) (x₀ : ℝ) {α : ℝ → ℂ} (hα : IsLoewnerTrace Wα α)
    (hαp : IsProperArc α) (hWα : Continuous Wα) (hWα0 : Wα 0 = 0) (ht : 0 < t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hκ : 0 < κ)
    (hω : Continuous ω) (hω0 : ω 0 = 0) (hs : 0 ≤ s) (hB : HasBdryLimits (fwdMapInv ω s))
    (hKs : ∀ z ∈ closure (fwdHull ω s), z.im = 0 → z = 0) (hjL : 0 < rightImg ω 0 s - ω s)
    (hjR : -rightImg (fun r => -ω r) 0 s - ω s < 0) (hGc : IsClosed (negInv '' fwdHull ω s))
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s))
    (hdis : Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)))
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {M mG v : ℂ → ℝ}
    (hv : IsBoundedHarmonicExtension (cfDataAt κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)
        (cfMarkR κ (bDataT ρL ρR xL xR θ κ) (forceJumpFinset xL xR) ω s)) v)
    (hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0))
    (hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0))
    (hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (logDerivPsi ω s z).im = retMean κ v (revChart ω s z))
    (hW' : Continuous W') (hW'0 : W' 0 = 0) {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η')
    (hT : 0 < T) (hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t) (htip : η' T = revChart ω s (α t))
    (u : PastData (ℓ + 1)) (hpos : ∀ i ≤ ℓ, 0 < recSeqT u i) (htS : startT (recSeqT u) (ℓ + 1) = t)
    (hw : ∀ i, EqOn (recSeqW u i) (shiftDrive Wα (startT (recSeqT u) i)) (Icc 0 (recSeqT u i)))
    (hang0 : ang 0 = 0) {A : ℕ → ℝ}
    (hA : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < A m ∧ A m < T ∧ η' (A m) = revChart ω s (α (startT (recSeqT u) m)))
    {uI : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData κ (imgStageRhoL κ θ ρL ang ℓ) (imgStageRhoR κ θ ρR ang ℓ)
      (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ))
      (forceJumpSet (imgStageVL xL ω s W' T A ℓ) (imgStageVR xR ω s W' T A ℓ)) uI)
    (hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + θ * chiC κ -
        ((pastWord (stopWord κ) c₀ x₀ ang (ℓ + 1) u).mean (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (α v)) (𝓝 0))
    {w u₀ : ℂ → ℝ} (hMw : ∀ z, M z + θ * chiC κ = w z + u₀ z)
    (huniq : ∀ z₀ ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      IsConformalBijection f (ball 0 1) (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      IsConformalBijection φc (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z) :
    ∀ z ∈ H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s), w z + u₀ z =
      (uI (fwdMap W' T (revChart ω s z)) - ang ℓ * chiC κ) -
        chiC κ * ((logDerivFwd W' T (revChart ω s z)).im + (logDerivPsi ω s z).im) := by
  have hS : ∀ m, 1 ≤ m → m ≤ ℓ → 0 < startT (recSeqT u) m ∧ startT (recSeqT u) m < t := fun m h1 h2 => by
    rw [← htS]; exact startT_pos_lt u hpos m h1 h2
  have hgapI : ∀ r ∈ Ioc 0 T, chartAL W' r < 0 ∧ 0 < chartAR W' r := fun r hr =>
    ⟨chartAL_neg_of_isProperArc hη' hη'p hW' hW'0 hr.1, chartAR_pos_of_isProperArc hη' hη'p hW' hW'0 hr.1⟩
  have hLc := isLeftLevels_pastWord_chartAL c₀ x₀ ang hκ u hα hαp hWα hWα0 hw
  have hRc := isRightLevels_pastWord_chartAR c₀ x₀ ang hκ u hα hαp hWα hWα0 hw
  rw [htS] at hLc hRc
  exact eqOn_imgChart_stage ρL ρR θ hα hαp hWα hWα0 ht hKt hκ hω hω0 hs hB hKs hjL hjR hGc hdisj hdis hxL hxR hv
    hG hInf hId hW' hW'0 hη' hη'p hT hK' htip (startT_zero _) hS hA hgapI hang0 (isSorted_stopWord κ _) hLc hRc hu
    hFl hMw huniq

end Assembly

end InteractingSLE.Sec5.CrossCond.StagedFinal

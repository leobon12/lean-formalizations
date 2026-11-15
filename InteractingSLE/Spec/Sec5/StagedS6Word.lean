/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Theta
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalPast
import InteractingSLE.Spec.Sec5.StagedS5Stop

/-!
# Proposition 5.9 at depth `ℓ`, step S6 (a): the restarted word in tree order is a killed word

Packet PROVE-STAGED-S6 (`planning/handoffs/PROVE-STAGED-S5.md` §5.2, steps 1–2). The restarted image word of S3
(`s3W`, `s3VL`, `s3VR`, `s3ζ`) lists its left marks in `Fin.append` order: the born marks of the switches, oldest
first, then the root marks. The killed-word form of Lemma 2.11 (`ImgDrv.IsKilledWord`) needs the left marks
antitone in the index, so the born block is reversed; the resulting **tree order** (newest born mark first, then the
root marks, index type `Fin (n + ℓ)`) is the order of PROVE-PROP59-PIECES' `TreeData.marks` and of `consAlt`.

* `treeIdx ℓ n : Fin (n + ℓ) ≃ Fin (ℓ + n)`: the tree order read in `Fin.append` order;
* `forceBoundaryData_comp_equiv`, `forceJumpSet_comp_equiv`, **`IsChartCouplingCharFunConst.comp_equiv`**: the
  chart clause is invariant under a simultaneous permutation of marks and weights;
* `imgBornL_le_imgBornL`, `rootVL_le_imgBornL`, … : the order of the image stage marks (a mark born later is closer
  to the driver; the real Loewner flow preserves the order), **`antitone_imgStageVL_treeIdx`**,
  **`monotone_imgStageVR_treeIdx`**;
* **`isKilledWord_arc`**: the arc piece of a family of killed arcs, from a start before the terminal capacity, with
  initial left marks `≤ 0` (antitone) and right marks `≥ 0` (monotone), is a killed word (strict separation at
  positive times from the proper-arc trace of the restarted chain, `chartA_shiftDrive_of_isProperArc`);
* **`isKilledWord_s6`**: the restarted word in tree order is a killed word at every glued sample.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped NNReal ENNReal Real
open QuantumZipper (H fwdHull chiC)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec5.CrossCond.StagedS6

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Word49 StagedS3 StagedFinal
open MartChar.RealFlow Prop59Pieces Prop59NodeTree
open Sec7.Lemma71C (capClock)

/-! ### The tree order -/

section Idx

/-- **The tree order read in `Fin.append` order**: index `i < ℓ` is the born mark `ℓ − 1 − i` (newest first), index
`i ≥ ℓ` is the root mark `i − ℓ`. -/
def treeIdx (ℓ n : ℕ) : Fin (n + ℓ) ≃ Fin (ℓ + n) where
  toFun i := if h : (i : ℕ) < ℓ then ⟨ℓ - 1 - i, by omega⟩ else ⟨i, by omega⟩
  invFun i := if h : (i : ℕ) < ℓ then ⟨ℓ - 1 - i, by omega⟩ else ⟨i, by omega⟩
  left_inv i := by
    by_cases h : (i : ℕ) < ℓ
    · have h' : ℓ - 1 - (i : ℕ) < ℓ := by omega
      simp only [h, h', ↓reduceDIte]
      ext
      simp only
      omega
    · simp only [h, ↓reduceDIte]
  right_inv i := by
    by_cases h : (i : ℕ) < ℓ
    · have h' : ℓ - 1 - (i : ℕ) < ℓ := by omega
      simp only [h, h', ↓reduceDIte]
      ext
      simp only
      omega
    · simp only [h, ↓reduceDIte]

variable {ℓ n : ℕ}

theorem treeIdx_of_lt {i : Fin (n + ℓ)} (h : (i : ℕ) < ℓ) :
    treeIdx ℓ n i = Fin.castAdd n (⟨ℓ - 1 - i, by omega⟩ : Fin ℓ) := by
  ext
  simp only [treeIdx, Equiv.coe_fn_mk, h, ↓reduceDIte, Fin.val_castAdd]

theorem treeIdx_of_ge {i : Fin (n + ℓ)} (h : ℓ ≤ (i : ℕ)) :
    treeIdx ℓ n i = Fin.natAdd ℓ (⟨i - ℓ, by omega⟩ : Fin n) := by
  have h' : ¬ (i : ℕ) < ℓ := not_lt.2 h
  ext
  simp only [treeIdx, Equiv.coe_fn_mk, h', ↓reduceDIte, Fin.val_natAdd]
  omega

theorem append_treeIdx_of_lt {α : Type*} (b : Fin ℓ → α) (r : Fin n → α) {i : Fin (n + ℓ)} (h : (i : ℕ) < ℓ) :
    Fin.append b r (treeIdx ℓ n i) = b ⟨ℓ - 1 - i, by omega⟩ := by
  rw [treeIdx_of_lt h, Fin.append_left]

theorem append_treeIdx_of_ge {α : Type*} (b : Fin ℓ → α) (r : Fin n → α) {i : Fin (n + ℓ)} (h : ℓ ≤ (i : ℕ)) :
    Fin.append b r (treeIdx ℓ n i) = r ⟨i - ℓ, by omega⟩ := by
  rw [treeIdx_of_ge h, Fin.append_right]

/-- **Antitone in tree order**: born marks increasing in the birth index (later births closer to the driver), root
marks antitone, every root mark below every born mark. -/
theorem antitone_append_treeIdx {b : Fin ℓ → ℝ} {r : Fin n → ℝ} (hb : Monotone b) (hr : Antitone r)
    (hbr : ∀ j k, r k ≤ b j) : Antitone fun i => Fin.append b r (treeIdx ℓ n i) := by
  intro i i' hii
  have hii' : (i : ℕ) ≤ i' := hii
  by_cases h' : (i' : ℕ) < ℓ
  · have h : (i : ℕ) < ℓ := lt_of_le_of_lt hii' h'
    simp only [append_treeIdx_of_lt b r h, append_treeIdx_of_lt b r h']
    exact hb (show (ℓ - 1 - (i' : ℕ)) ≤ ℓ - 1 - (i : ℕ) by omega)
  · by_cases h : (i : ℕ) < ℓ
    · simp only [append_treeIdx_of_lt b r h, append_treeIdx_of_ge b r (not_lt.1 h')]
      exact hbr _ _
    · simp only [append_treeIdx_of_ge b r (not_lt.1 h), append_treeIdx_of_ge b r (not_lt.1 h')]
      exact hr (show (i : ℕ) - ℓ ≤ (i' : ℕ) - ℓ by omega)

/-- **Monotone in tree order** (the right marks). -/
theorem monotone_append_treeIdx {b : Fin ℓ → ℝ} {r : Fin n → ℝ} (hb : Antitone b) (hr : Monotone r)
    (hbr : ∀ j k, b j ≤ r k) : Monotone fun i => Fin.append b r (treeIdx ℓ n i) := by
  have h := antitone_append_treeIdx (b := fun j => -b j) (r := fun k => -r k) (fun _ _ h => neg_le_neg (hb h))
    (fun _ _ h => neg_le_neg (hr h)) fun j k => neg_le_neg (hbr j k)
  intro i i' hii
  have := h hii
  have e : ∀ m, Fin.append (fun j => -b j) (fun k => -r k) m = -Fin.append b r m := fun m => by
    refine Fin.addCases (fun j => ?_) (fun k => ?_) m
    · simp only [Fin.append_left]
    · simp only [Fin.append_right]
  simp only [e] at this
  linarith

end Idx

/-! ### The chart clause is invariant under a permutation of the marks -/

section Perm

variable {κ : ℝ} {nL nR mL mR : ℕ}

theorem forceBoundaryData_comp_equiv (eL : Fin mL ≃ Fin nL) (eR : Fin mR ≃ Fin nR) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    forceBoundaryData κ (fun i => ρL (eL i)) (fun j => ρR (eR j)) (fun i => vL (eL i)) (fun j => vR (eR j)) =
      forceBoundaryData κ ρL ρR vL vR := by
  funext x
  simp only [forceBoundaryData, Finset.sum_filter]
  rw [Equiv.sum_comp eL (fun i => if x < vL i then ρL i else 0),
    Equiv.sum_comp eR (fun j => if vR j ≤ x then ρR j else 0)]

theorem forceJumpSet_comp_equiv (eL : Fin mL ≃ Fin nL) (eR : Fin mR ≃ Fin nR) (vL : Fin nL → ℝ)
    (vR : Fin nR → ℝ) :
    forceJumpSet (fun i => vL (eL i)) (fun j => vR (eR j)) = forceJumpSet vL vR := by
  have hL : range (fun i => vL (eL i)) = range vL := eL.surjective.range_comp vL
  have hR : range (fun j => vR (eR j)) = range vR := eR.surjective.range_comp vR
  simp only [forceJumpSet, hL, hR]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓐 : Filtration ℝ≥0 mΩ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The chart clause at fixed times only sees the boundary data**, which is invariant under a simultaneous
permutation of the marks and the weights. -/
theorem isChartCouplingCharFunConst_comp_equiv
    (hcf : Sec7.Lemma71D.IsChartCouplingCharFunConst κ ρL ρR P 𝓐 W VL VR ζ c a k h)
    (eL : Fin mL ≃ Fin nL) (eR : Fin mR ≃ Fin nR) :
    Sec7.Lemma71D.IsChartCouplingCharFunConst κ (fun i => ρL (eL i)) (fun j => ρR (eR j)) P 𝓐 W
      (fun i => VL (eL i)) (fun j => VR (eR j)) ζ c a k h := by
  intro t u hu φ
  refine hcf t u (fun ω => ?_) φ
  have h1 := forceBoundaryData_comp_equiv (κ := κ) eL eR ρL ρR (fun i => VL i t ω - W t ω)
    (fun j => VR j t ω - W t ω)
  have h2 := forceJumpSet_comp_equiv eL eR (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)
  have := hu ω
  rw [h1, h2] at this
  exact this

end Perm

/-! ### The order of the image stage marks -/

section Order

variable {nL nR ℓ : ℕ} {w : ℝ → ℝ} {T : ℝ} {A : ℕ → ℝ}

theorem shiftDrv_neg_eq (w : ℝ → ℝ) (S : ℝ) : shiftDrv (fun s => -w s) S = fun s => -shiftDrive w S s := by
  funext r
  simp only [shiftDrv, shiftDrive]
  ring

theorem shiftDrv_eq_shiftDrive (w : ℝ → ℝ) (S : ℝ) : shiftDrv w S = shiftDrive w S := rfl

/-- A left mark born later lies closer to the driver. -/
theorem imgBornL_le_imgBornL (hw : Continuous w) {a b : ℕ} (hab : A a ≤ A b) (hT : A b ≤ T) :
    imgBornL w T A a ≤ imgBornL w T A b := by
  have h := chartAL_shift hw (a := A a) (S := A b) (r := T - A b) hab (sub_nonneg.2 hT)
  rw [show A b + (T - A b) - A a = T - A a by ring] at h
  simp only [imgBornL]
  rw [← h]
  have hc : Continuous (shiftDrv (fun s => -w s) (A b)) := continuous_shiftDrv hw.neg _
  have hle : (0 : ℝ) ≤ -chartAL (shiftDrive w (A a)) (A b - A a) :=
    neg_nonneg.2 (chartAL_nonpos (QuantumZipper.RS.continuous_shiftDrive hw _) (sub_nonneg.2 hab))
  have hm := rightImg_mono_index hc (sub_nonneg.2 hT) hle
  have e : chartAL (shiftDrive w (A b)) (T - A b) =
      -rightImg (shiftDrv (fun s => -w s) (A b)) 0 (T - A b) - shiftDrv w (A b) (T - A b) := by
    rw [shiftDrv_neg_eq, shiftDrv_eq_shiftDrive]
    rfl
  rw [e]
  linarith

/-- Every left mark that has flowed from time `0` lies left of every mark born at `S ∈ [0, T]`. -/
theorem relL_le_chartAL (hw : Continuous w) {S : ℝ} (hS : 0 ≤ S) (hT : S ≤ T) (x : ℝ) :
    -rightImg (fun s => -w s) x T - w T ≤ chartAL (shiftDrive w S) (T - S) := by
  have h := relL_shift hw (S := S) (r := T - S) hS (sub_nonneg.2 hT) x
  rw [show S + (T - S) = T by ring] at h
  rw [← h]
  have hc : Continuous (shiftDrv (fun s => -w s) S) := continuous_shiftDrv hw.neg _
  have hle : (0 : ℝ) ≤ -(-rightImg (fun s => -w s) x S - w S) := by
    have := le_rightImg (w := fun s => -w s) hw.neg x hS
    linarith
  have hm := rightImg_mono_index hc (sub_nonneg.2 hT) hle
  have e : chartAL (shiftDrive w S) (T - S) =
      -rightImg (shiftDrv (fun s => -w s) S) 0 (T - S) - shiftDrv w S (T - S) := by
    rw [shiftDrv_neg_eq, shiftDrv_eq_shiftDrive]
    rfl
  rw [e]
  linarith

/-- A right mark born later lies closer to the driver. -/
theorem imgBornR_le_imgBornR (hw : Continuous w) {a b : ℕ} (hab : A a ≤ A b) (hT : A b ≤ T) :
    imgBornR w T A b ≤ imgBornR w T A a := by
  have h := chartAR_shift hw (a := A a) (S := A b) (r := T - A b) hab (sub_nonneg.2 hT)
  rw [show A b + (T - A b) - A a = T - A a by ring] at h
  simp only [imgBornR]
  rw [← h]
  have hc : Continuous (shiftDrv w (A b)) := continuous_shiftDrv hw _
  have hle : (0 : ℝ) ≤ chartAR (shiftDrive w (A a)) (A b - A a) :=
    chartAR_nonneg (QuantumZipper.RS.continuous_shiftDrive hw _) (sub_nonneg.2 hab)
  have hm := rightImg_mono_index hc (sub_nonneg.2 hT) hle
  have e : chartAR (shiftDrive w (A b)) (T - A b) =
      rightImg (shiftDrv w (A b)) 0 (T - A b) - shiftDrv w (A b) (T - A b) := rfl
  rw [e]
  linarith

/-- Every right mark that has flowed from time `0` lies right of every mark born at `S ∈ [0, T]`. -/
theorem chartAR_le_relR (hw : Continuous w) {S : ℝ} (hS : 0 ≤ S) (hT : S ≤ T) (x : ℝ) :
    chartAR (shiftDrive w S) (T - S) ≤ rightImg w x T - w T := by
  have h := relR_shift hw (S := S) (r := T - S) hS (sub_nonneg.2 hT) x
  rw [show S + (T - S) = T by ring] at h
  rw [← h]
  have hc : Continuous (shiftDrv w S) := continuous_shiftDrv hw _
  have hle : (0 : ℝ) ≤ rightImg w x S - w S := by
    have := le_rightImg hw x hS
    linarith
  have hm := rightImg_mono_index hc (sub_nonneg.2 hT) hle
  have e : chartAR (shiftDrive w S) (T - S) = rightImg (shiftDrv w S) 0 (T - S) - shiftDrv w S (T - S) := rfl
  rw [e]
  linarith

/-- **The left image stage marks are antitone in tree order.** -/
theorem antitone_imgStageVL_treeIdx (hw : Continuous w) (xL : Fin nL → ℝ) (ω : ℝ → ℝ) (s : ℝ) (hT : 0 ≤ T)
    (hA0 : ∀ j : Fin ℓ, 0 ≤ A (j + 1)) (hAT : ∀ j : Fin ℓ, A (j + 1) ≤ T)
    (hAm : Monotone fun j : Fin ℓ => A (j + 1)) (hx : Antitone (GlueImg.imgMarkL xL ω s)) :
    Antitone fun i => imgStageVL xL ω s w T A ℓ (treeIdx ℓ (nL + 1) i) := by
  refine antitone_append_treeIdx (fun j j' hjj => imgBornL_le_imgBornL hw (hAm hjj) (hAT j'))
    (fun k k' hkk => ?_) fun j k => ?_
  · simp only [rootVL]
    have := rightImg_mono_index (w := fun r => -w r) hw.neg hT (neg_le_neg (hx hkk))
    linarith
  · simp only [rootVL, imgBornL]
    exact relL_le_chartAL hw (hA0 j) (hAT j) _

/-- **The right image stage marks are monotone in tree order.** -/
theorem monotone_imgStageVR_treeIdx (hw : Continuous w) (xR : Fin nR → ℝ) (ω : ℝ → ℝ) (s : ℝ) (hT : 0 ≤ T)
    (hA0 : ∀ j : Fin ℓ, 0 ≤ A (j + 1)) (hAT : ∀ j : Fin ℓ, A (j + 1) ≤ T)
    (hAm : Monotone fun j : Fin ℓ => A (j + 1)) (hx : Monotone (GlueImg.imgMarkR xR ω s)) :
    Monotone fun i => imgStageVR xR ω s w T A ℓ (treeIdx ℓ (nR + 1) i) := by
  refine monotone_append_treeIdx (fun j j' hjj => imgBornR_le_imgBornR hw (hAm hjj) (hAT j'))
    (fun k k' hkk => ?_) fun j k => ?_
  · simp only [rootVR]
    have := rightImg_mono_index hw hT (hx hkk)
    linarith
  · simp only [rootVR, imgBornR]
    exact chartAR_le_relR hw (hA0 j) (hAT j) _

end Order

/-! ### The arc piece of a family of killed arcs is a killed word -/

section Arc

variable {Ω : Type*} {nL nR : ℕ} {γ : Ω → ℝ → ℂ} {P : Ω → Set ℝ} {S₀ : Ω → ℝ≥0}

/-- The lifetime of an arc piece with alive set `univ`, as a `WithTop ℝ≥0`-valued time. -/
def arcT (γ : Ω → ℝ → ℂ) (P : Ω → Set ℝ) (S₀ : Ω → ℝ≥0) : Ω → WithTop ℝ≥0 := fun ω => arcζ γ P S₀ univ ω

theorem realPath_coe' (X : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ≥0) : Bessel.realPath X ω (t : ℝ) = X t ω := by
  simp only [Bessel.realPath, Real.toNNReal_coe]

theorem isLocCont_arcW (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (ω : Ω) :
    IsLocCont (Bessel.realPath (arcW γ P S₀ univ) ω) (arcT γ P S₀ ω) :=
  isLocCont_realPath (continuousOn_arcW hγ ω)

theorem arcW_zero (ω : Ω) : arcW γ P S₀ univ 0 ω = 0 := by
  classical
  simp only [arcW, add_zero, sub_self, ite_self]

/-- **Strict separation on the left**: at positive times before the lifetime, the images of marks `≤ 0` lie strictly
left of the restarted driver. -/
theorem arcVL_lt_arcW (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {xL : Ω → Fin nL → ℝ} (hxL : ∀ ω i, xL ω i ≤ 0)
    {ω : Ω} {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < arcζ γ P S₀ univ ω) (i : Fin nL) :
    arcVL γ P S₀ univ xL i t ω < arcW γ P S₀ univ t ω := by
  have hlt := (lt_arcζ_iff.1 ht).2
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := (hγ ω).exists_kPath_trace hlt
  have hEq' : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + t : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have hd := arcVL_sub_arcW (xL := xL) (mem_univ ω) hlt hw hEq' i
  have hsep := (chartA_shiftDrive_of_isProperArc hηL hηP hw hw0 (S₀ ω).coe_nonneg
    (show (0 : ℝ) < t from ht0)).1
  have hc : Continuous (shiftDrv (fun s => -w s) (S₀ ω)) := continuous_shiftDrv hw.neg _
  have hm := rightImg_mono_index hc t.coe_nonneg (neg_nonneg.2 (hxL ω i))
  have e : chartAL (shiftDrive w (S₀ ω)) t =
      -rightImg (shiftDrv (fun s => -w s) (S₀ ω)) 0 t - shiftDrv w (S₀ ω) t := by
    rw [shiftDrv_neg_eq, shiftDrv_eq_shiftDrive]
    rfl
  rw [e] at hsep
  linarith

/-- **Strict separation on the right.** -/
theorem arcW_lt_arcVR (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {xR : Ω → Fin nR → ℝ} (hxR : ∀ ω j, 0 ≤ xR ω j)
    {ω : Ω} {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) < arcζ γ P S₀ univ ω) (j : Fin nR) :
    arcW γ P S₀ univ t ω < arcVR γ P S₀ univ xR j t ω := by
  have hlt := (lt_arcζ_iff.1 ht).2
  obtain ⟨S, -, -, htS, w, hw, hw0, hEq, η, hηL, hηP, -⟩ := (hγ ω).exists_kPath_trace hlt
  have hEq' : EqOn (kPath (γ ω) (P ω)) w (Icc 0 ((S₀ ω + t : ℝ≥0) : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have hd := arcVR_sub_arcW (xR := xR) (mem_univ ω) hlt hw hEq' j
  have hsep := (chartA_shiftDrive_of_isProperArc hηL hηP hw hw0 (S₀ ω).coe_nonneg
    (show (0 : ℝ) < t from ht0)).2
  have hc : Continuous (shiftDrv w (S₀ ω)) := continuous_shiftDrv hw _
  have hm := rightImg_mono_index hc t.coe_nonneg (hxR ω j)
  have e : chartAR (shiftDrive w (S₀ ω)) t = rightImg (shiftDrv w (S₀ ω)) 0 t - shiftDrv w (S₀ ω) t := rfl
  rw [e] at hsep
  linarith

theorem arcVL_eq_kImg {xL : Ω → Fin nL → ℝ} {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < arcζ γ P S₀ univ ω)
    (i : Fin nL) :
    arcVL γ P S₀ univ xL i t ω = -kImg (fun r => -Bessel.realPath (arcW γ P S₀ univ) ω r) (-xL ω i) t := by
  simp only [arcVL, ht, ↓reduceIte]
  rfl

theorem arcVR_eq_kImg {xR : Ω → Fin nR → ℝ} {ω : Ω} {t : ℝ≥0} (ht : (t : ℝ≥0∞) < arcζ γ P S₀ univ ω)
    (j : Fin nR) :
    arcVR γ P S₀ univ xR j t ω = kImg (Bessel.realPath (arcW γ P S₀ univ) ω) (xR ω j) t := by
  simp only [arcVR, ht, ↓reduceIte]
  rfl

/-- **The arc piece of a family of killed arcs is a killed word**: started at `S₀` with alive set `univ`, initial
left marks `≤ 0` antitone in the index and right marks `≥ 0` monotone in the index. -/
theorem isKilledWord_arc (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ}
    (hxL : ∀ ω i, xL ω i ≤ 0) (hxR : ∀ ω j, 0 ≤ xR ω j) (hxLa : ∀ ω, Antitone (xL ω))
    (hxRm : ∀ ω, Monotone (xR ω)) :
    ImgDrv.IsKilledWord (arcW γ P S₀ univ) (arcVL γ P S₀ univ xL) (arcVR γ P S₀ univ xR) (arcT γ P S₀) := by
  set p : Ω → ℝ → ℝ := fun ω => Bessel.realPath (arcW γ P S₀ univ) ω with hpdef
  have hp : ∀ ω, IsLocCont (p ω) (arcT γ P S₀ ω) := isLocCont_arcW hγ
  have hpc : ∀ ω (t : ℝ≥0), p ω t = arcW γ P S₀ univ t ω := fun ω t => realPath_coe' _ ω t
  have hraw : ImgDrv.IsKilledWord (arcW γ P S₀ univ)
      (fun i t ω => -kImg (fun r => -p ω r) (-xL ω i) t) (fun j t ω => kImg (p ω) (xR ω j) t)
      (arcT γ P S₀) :=
    { w_zero := fun ω => arcW_zero ω
      contW := fun ω => continuousOn_arcW hγ ω
      ordL := fun ω t i ht => by
        have := (hp ω).neg.le_kImg ht (-xL ω i)
        rw [hpc] at this
        linarith
      ordR := fun ω t j ht => by
        have := (hp ω).le_kImg ht (xR ω j)
        rwa [hpc] at this
      pathL := fun ω i => by
        have h := isForcePathBefore_neg ((hp ω).neg.isForcePathBefore (-xL ω i) fun t ht0 ht => by
          have h1 := arcVL_lt_arcW (S₀ := S₀) hγ hxL ht0 ht i
          rw [arcVL_eq_kImg ht i] at h1
          show -p ω t < _
          rw [hpc]
          linarith)
        simp only [neg_neg, hpc] at h
        exact h
      pathR := fun ω j => by
        have h := (hp ω).isForcePathBefore (xR ω j) fun t ht0 ht => by
          have h1 := arcW_lt_arcVR (S₀ := S₀) hγ hxR ht0 ht j
          rw [arcVR_eq_kImg ht j] at h1
          rw [hpc]
          exact h1
        simp only [hpc] at h
        exact h
      antiL := fun ω i a ha b hb hab => by
        have := (hp ω).neg.kImg_mono_time hb hab (-xL ω i)
        show -kImg _ _ _ ≤ -kImg _ _ _
        linarith
      monoR := fun ω j a ha b hb hab => (hp ω).kImg_mono_time hb hab (xR ω j)
      idxL := fun ω t ht a b hab => by
        have := (hp ω).neg.kImg_mono_index ht (neg_le_neg (hxLa ω hab))
        show -kImg _ _ _ ≤ -kImg _ _ _
        linarith
      idxR := fun ω t ht a b hab => (hp ω).kImg_mono_index ht (hxRm ω hab)
      mergeL := fun ω i j s t hst ht heq => by
        have heq' : kImg (fun r => -p ω r) (-xL ω i) s = kImg (fun r => -p ω r) (-xL ω j) s := neg_inj.1 heq
        show -kImg _ _ _ = -kImg _ _ _
        rw [(hp ω).neg.kImg_merge hst ht heq']
      mergeR := fun ω i j s t hst ht heq => (hp ω).kImg_merge hst ht heq
      sepL := fun ω t ht0 ht i => by
        have h1 := arcVL_lt_arcW (S₀ := S₀) hγ hxL ht0 ht i
        rwa [arcVL_eq_kImg ht i] at h1
      sepR := fun ω t ht0 ht j => by
        have h1 := arcW_lt_arcVR (S₀ := S₀) hγ hxR ht0 ht j
        rwa [arcVR_eq_kImg ht j] at h1 }
  exact hraw.congr_marks (fun ω i t ht => arcVL_eq_kImg ht i) fun ω j t ht => arcVR_eq_kImg ht j

theorem zero_lt_arcζ (hS₀ : ∀ ω, (S₀ ω : WithTop ℝ≥0) < kLife (γ ω) (P ω)) (ω : Ω) :
    (0 : ℝ≥0∞) < arcζ γ P S₀ univ ω := by
  refine lt_arcζ_iff.2 ⟨mem_univ _, ?_⟩
  rw [add_zero]
  exact hS₀ ω

/-- **The arc piece starts at its initial left marks.** -/
theorem arcVL_zero (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (hS₀ : ∀ ω, (S₀ ω : WithTop ℝ≥0) < kLife (γ ω) (P ω))
    {xL : Ω → Fin nL → ℝ} (hxL : ∀ ω i, xL ω i ≤ 0) (ω : Ω) (i : Fin nL) :
    arcVL γ P S₀ univ xL i 0 ω = xL ω i := by
  have h0 := zero_lt_arcζ hS₀ ω
  rw [arcVL_eq_kImg h0 i]
  obtain ⟨c, hc, w, hw, hEq⟩ := (isLocCont_arcW (S₀ := S₀) hγ ω).neg 0 h0
  have hw0 : w 0 = 0 := by
    have := hEq ⟨le_rfl, hc.le⟩
    rw [← this]
    simp only [Bessel.realPath, Real.toNNReal_zero, arcW_zero, neg_zero]
  rw [kImg_eq hw hEq (by exact_mod_cast hc.le) (-xL ω i)]
  rw [NNReal.coe_zero, MartChar.RealFlow.rightImg_zero hw hw0 (neg_nonneg.2 (hxL ω i)), neg_neg]

/-- **The arc piece starts at its initial right marks.** -/
theorem arcVR_zero (hγ : ∀ ω, IsKilledArc (γ ω) (P ω)) (hS₀ : ∀ ω, (S₀ ω : WithTop ℝ≥0) < kLife (γ ω) (P ω))
    {xR : Ω → Fin nR → ℝ} (hxR : ∀ ω j, 0 ≤ xR ω j) (ω : Ω) (j : Fin nR) :
    arcVR γ P S₀ univ xR j 0 ω = xR ω j := by
  have h0 := zero_lt_arcζ hS₀ ω
  rw [arcVR_eq_kImg h0 j]
  obtain ⟨c, hc, w, hw, hEq⟩ := (isLocCont_arcW (S₀ := S₀) hγ ω) 0 h0
  have hw0 : w 0 = 0 := by
    have := hEq ⟨le_rfl, hc.le⟩
    rw [← this]
    simp only [Bessel.realPath, Real.toNNReal_zero, arcW_zero]
  rw [kImg_eq hw hEq (by exact_mod_cast hc.le) (xR ω j)]
  rw [NNReal.coe_zero, MartChar.RealFlow.rightImg_zero hw hw0 (hxR ω j)]

end Arc

/-! ### The restarted word in tree order -/

section S6

variable {Ω : Type*} {nL nR : ℕ} {s : ℝ≥0} {Wj : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)} {τ : ℝ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {τs : ℕ → ℝ} {ℓ : ℕ}

/-- **The restarted left marks in tree order** (newest born mark first, then the root marks). -/
def s6VL (xL : Fin nL → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) : Fin ((nL + 1) + ℓ) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun i => s3VL xL τs ℓ s Wj E τ (treeIdx ℓ (nL + 1) i)

/-- **The restarted right marks in tree order.** -/
def s6VR (xR : Fin nR → ℝ) (τs : ℕ → ℝ) (ℓ : ℕ) (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (τ : ℝ) : Fin ((nR + 1) + ℓ) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun j => s3VR xR τs ℓ s Wj E τ (treeIdx ℓ (nR + 1) j)

/-- The restarted lifetime as a `WithTop ℝ≥0`-valued time. -/
def s6T (s : ℝ≥0) (Wj : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) (τ : ℝ) :
    Ω × HistorySpace 0 0 → WithTop ℝ≥0 := fun p => s3ζ s Wj E τ p

/-- On the alive event the initial marks are the image stage marks of a continuous extension of the chain driver. -/
theorem exists_s3X_eq (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) :
    ∃ w : ℝ → ℝ, Continuous w ∧
      s3XL xL τs ℓ s Wj E τ p = imgStageVL xL (cfDrv0 s p.2) s w (s3Start s Wj E τ p)
        (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ ∧
      s3XR xR τs ℓ s Wj E τ p = imgStageVR xR (cfDrv0 s p.2) s w (s3Start s Wj E τ p)
        (fun m => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs m)) ℓ := by
  classical
  have hγ := isKilledArc_gCurve hEg p
  obtain ⟨S, -, -, htS, w, hw, -, hEq, -⟩ := hγ.exists_kPath_trace (StagedS4.s3Start_lt_kLife hEg hp)
  have hEq' : EqOn (kPath (gCurve s (fun _ => ⊤) Wj E p) (gPre s (fun _ => ⊤) Wj E p)) w
      (Icc 0 (s3Start s Wj E τ p : ℝ)) := hEq.mono (Icc_subset_Icc_right htS.le)
  have hA := s3_switch hEg hp hτs
  refine ⟨w, hw, ?_, ?_⟩
  · simp only [s3XL, hp, ↓reduceIte]
    exact imgStageVL_congr hw hEq' xL _ _ hA (s3Start s Wj E τ p).coe_nonneg
  · simp only [s3XR, hp, ↓reduceIte]
    exact imgStageVR_congr hw hEq' xR _ _ hA (s3Start s Wj E τ p).coe_nonneg

theorem s3XL_nonpos (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (p : Ω × HistorySpace 0 0) (i : Fin (ℓ + (nL + 1))) :
    s3XL xL τs ℓ s Wj E τ p i ≤ 0 := by
  classical
  by_cases hp : p ∈ s3Alive s Wj E τ
  · obtain ⟨w, hw, hL, -⟩ := exists_s3X_eq (xL := xL) (xR := (Fin.elim0 : Fin 0 → ℝ)) hEg hp hτs
    rw [hL]
    exact imgStageVL_nonpos hw xL _ _ (s3Start s Wj E τ p).coe_nonneg (fun j => (s3_switch hEg hp hτs j).2) i
  · simp only [s3XL, hp, ↓reduceIte, Pi.zero_apply, le_refl]

theorem s3XR_nonneg (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (p : Ω × HistorySpace 0 0) (j : Fin (ℓ + (nR + 1))) :
    0 ≤ s3XR xR τs ℓ s Wj E τ p j := by
  classical
  by_cases hp : p ∈ s3Alive s Wj E τ
  · obtain ⟨w, hw, -, hR⟩ := exists_s3X_eq (xL := (Fin.elim0 : Fin 0 → ℝ)) (xR := xR) hEg hp hτs
    rw [hR]
    exact imgStageVR_nonneg hw xR _ _ (s3Start s Wj E τ p).coe_nonneg (fun j => (s3_switch hEg hp hτs j).2) j
  · simp only [s3XR, hp, ↓reduceIte, Pi.zero_apply, le_refl]

/-- The switch capacities are monotone in the switch index. -/
theorem monotone_capClock_switch (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) {p : Ω × HistorySpace 0 0}
    (hp : p ∈ s3Alive s Wj E τ) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : Monotone fun j : Fin ℓ => τs (j + 1)) :
    Monotone fun j : Fin ℓ => capClock (gCurve s (fun _ => ⊤) Wj E p) (τs (j + 1)) := by
  have hγ := isKilledArc_gCurve hEg p
  have hτP : τ ∈ gPre s (fun _ => ⊤) Wj E p := hp.2
  intro j j' hjj
  exact hγ.strictMonoOn_capClock.monotoneOn (hγ.icc τ hτP (hτs j)) (hγ.icc τ hτP (hτs j')) (hτm hjj)

theorem antitone_s3XL_treeIdx (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hxL : ∀ i, xL i ≤ 0)
    (hxLa : Antitone xL) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : Monotone fun j : Fin ℓ => τs (j + 1)) (p : Ω × HistorySpace 0 0) :
    Antitone fun i => s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i) := by
  classical
  by_cases hp : p ∈ s3Alive s Wj E τ
  · obtain ⟨w, hw, hL, -⟩ := exists_s3X_eq (xL := xL) (xR := (Fin.elim0 : Fin 0 → ℝ)) hEg hp hτs
    rw [hL]
    obtain ⟨-, -, hj, -, -⟩ := hEg p hp.1
    have hc := continuous_cfDrv0 s p.2
    have hx : Antitone (GlueImg.imgMarkL xL (cfDrv0 s p.2) s) :=
      antitone_snoc (fun i i' hii => psiL_mono hc s.coe_nonneg hj (hxL i) (hxLa hii))
        (fun i => junL_le_psiL hc s.coe_nonneg hj (hxL i))
    exact antitone_imgStageVL_treeIdx hw xL _ _ (s3Start s Wj E τ p).coe_nonneg
      (fun j => (s3_switch hEg hp hτs j).1) (fun j => (s3_switch hEg hp hτs j).2)
      (monotone_capClock_switch hEg hp hτs hτm) hx
  · simp only [s3XL, hp, ↓reduceIte, Pi.zero_apply]
    exact antitone_const

theorem monotone_s3XR_treeIdx (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hxR : ∀ j, 0 ≤ xR j)
    (hxRm : Monotone xR) (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ)
    (hτm : Monotone fun j : Fin ℓ => τs (j + 1)) (p : Ω × HistorySpace 0 0) :
    Monotone fun j => s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j) := by
  classical
  by_cases hp : p ∈ s3Alive s Wj E τ
  · obtain ⟨w, hw, -, hR⟩ := exists_s3X_eq (xL := (Fin.elim0 : Fin 0 → ℝ)) (xR := xR) hEg hp hτs
    rw [hR]
    obtain ⟨-, -, -, hj, -⟩ := hEg p hp.1
    have hc := continuous_cfDrv0 s p.2
    have hx : Monotone (GlueImg.imgMarkR xR (cfDrv0 s p.2) s) :=
      monotone_snoc (fun j j' hjj => psiR_mono hc s.coe_nonneg hj (hxR j) (hxRm hjj))
        (fun j => psiR_le_junR hc s.coe_nonneg hj (hxR j))
    exact monotone_imgStageVR_treeIdx hw xR _ _ (s3Start s Wj E τ p).coe_nonneg
      (fun j => (s3_switch hEg hp hτs j).1) (fun j => (s3_switch hEg hp hτs j).2)
      (monotone_capClock_switch hEg hp hτs hτm) hx
  · simp only [s3XR, hp, ↓reduceIte, Pi.zero_apply]
    exact monotone_const

/-- **The restarted word in tree order is a killed word** at every glued sample. -/
theorem isKilledWord_s6 (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hxL : ∀ i, xL i ≤ 0)
    (hxLa : Antitone xL) (hxR : ∀ j, 0 ≤ xR j) (hxRm : Monotone xR)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτm : Monotone fun j : Fin ℓ => τs (j + 1)) :
    ImgDrv.IsKilledWord (s3W s Wj E τ) (s6VL xL τs ℓ s Wj E τ) (s6VR xR τs ℓ s Wj E τ) (s6T s Wj E τ) :=
  isKilledWord_arc (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E) (S₀ := s3Start s Wj E τ)
    (xL := fun p i => s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i))
    (xR := fun p j => s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j))
    (fun p => isKilledArc_gCurve hEg p) (fun p _ => s3XL_nonpos hEg hτs p _)
    (fun p _ => s3XR_nonneg hEg hτs p _) (antitone_s3XL_treeIdx hEg hxL hxLa hτs hτm)
    (monotone_s3XR_treeIdx hEg hxR hxRm hτs hτm)

/-- **The restarted word starts at the image stage marks in tree order.** -/
theorem s6VL_zero (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (p : Ω × HistorySpace 0 0) (i : Fin ((nL + 1) + ℓ)) :
    s6VL xL τs ℓ s Wj E τ i 0 p = s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i) :=
  arcVL_zero (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E) (S₀ := s3Start s Wj E τ)
    (xL := fun p i => s3XL xL τs ℓ s Wj E τ p (treeIdx ℓ (nL + 1) i)) (fun p => isKilledArc_gCurve hEg p)
    (fun p => StagedS5.s3Start_lt_kLife' hEg τ p) (fun p _ => s3XL_nonpos hEg hτs p _) p i

theorem s6VR_zero (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (p : Ω × HistorySpace 0 0) (j : Fin ((nR + 1) + ℓ)) :
    s6VR xR τs ℓ s Wj E τ j 0 p = s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j) :=
  arcVR_zero (γ := gCurve s (fun _ => ⊤) Wj E) (P := gPre s (fun _ => ⊤) Wj E) (S₀ := s3Start s Wj E τ)
    (xR := fun p j => s3XR xR τs ℓ s Wj E τ p (treeIdx ℓ (nR + 1) j)) (fun p => isKilledArc_gCurve hEg p)
    (fun p => StagedS5.s3Start_lt_kLife' hEg τ p) (fun p _ => s3XR_nonneg hEg hτs p _) p j

/-- **The start of the restarted word in tree order is an ordered force word** at every glued sample. -/
theorem isOrderedForceWord_s6Start (hEg : ∀ p ∈ E, IsGood49 s (fun _ => ⊤) Wj p) (hxL : ∀ i, xL i ≤ 0)
    (hxLa : Antitone xL) (hxR : ∀ j, 0 ≤ xR j) (hxRm : Monotone xR)
    (hτs : ∀ j : Fin ℓ, 0 ≤ τs (j + 1) ∧ τs (j + 1) ≤ τ) (hτm : Monotone fun j : Fin ℓ => τs (j + 1))
    (p : Ω × HistorySpace 0 0) :
    IsOrderedForceWord (fun i => s6VL xL τs ℓ s Wj E τ i 0 p) (fun j => s6VR xR τs ℓ s Wj E τ j 0 p) := by
  simp only [s6VL_zero hEg hτs p, s6VR_zero hEg hτs p]
  exact ⟨antitone_s3XL_treeIdx hEg hxL hxLa hτs hτm p, fun i => s3XL_nonpos hEg hτs p _,
    monotone_s3XR_treeIdx hEg hxR hxRm hτs hτm p, fun j => s3XR_nonneg hEg hτs p _⟩

end S6

end InteractingSLE.Sec5.CrossCond.StagedS6

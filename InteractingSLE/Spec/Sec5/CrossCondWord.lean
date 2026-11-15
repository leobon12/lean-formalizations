/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondLaw
import InteractingSLE.Spec.Sec5.GlueCondHit
import InteractingSLE.WangWu.ReverseContactMartGlue

/-!
# The cross-conditioning law at general `κ`: the image word of the flow line given the counterflow prefix

Packet PROVE-GLUECOND5, G4 for Proposition 4.9's direction (specification §4.2, proof of Proposition 4.9 and Remark
4.10, pp. 119–121; Astra's Part E.1 and E.6 at general `κ`). On the glued space of `Prop411Q.CfGlueAE`, with the
counterflow prefix `η′([0, s])` revealed (`s ≥ 0` fixed), the flow line `η` is mapped by the chart
`Ψ = revChart W′ s = R ∘ f′_s ∘ R` of `ℍ ∖ R(K′_s)` (the counterflow's own Loewner map in the chart `R`, centred, read
from the counterflow history stopped at `s`; `Ψ(0) = 0`, the counterflow tip goes to `∞`). Before its first contact
with `R(K′_s)` the image `Ψ ∘ η` is a simple arc in `ℍ` from `0` (WangWu's `isKilledArc_imgCurve`, generic in the
obstacle), so WangWu's killed-arc machinery gives its **killed image word** in capacity time.

**The image word** (Remark 4.10: "the actual centered coupling of `h − πχ/2` … gives the following new upper heights
for the transported flow background: `−λ′ + πχ/2 = −λ + πχ` on the exposed left side, `λ′ + πχ/2 = λ` on the exposed
right side"). The marks are the images `Ψ(x_{i,L})`, `Ψ(x_{j,R})` of the flow word's marks, with their weights, and one
junction on each side: `Ψ(∞⁻) = −1/(f′_s(0⁺) − W′_s)` (left; beyond it the counterflow's exposed left side) and
`Ψ(∞⁺) = −1/(f′_s(0⁻) − W′_s)` (right). The junction weights are fixed by the heights of `forceBoundaryData`:
`−λ(1 + Σρ_L + ρ′_L) = −λ + πχ`, i.e. **`ρ′_L = κ/2 − 2 − Σρ_L`**, and `λ(1 + Σρ_R + ρ′_R) = λ`, i.e.
**`ρ′_R = −Σρ_R`** (`πχ/λ = 2 − κ/2`). At `κ = 4` this is WangWu's two-seed image word `(r, −r)`.

* `cfDrv0 s y`: the counterflow driver of the history stopped at `s`, recentred at `0` (continuous for every history,
  measurable for the stopped history);
* `psiL`, `psiR`: the images of real points of the chart `Q` under `Ψ`, through the real Loewner flow (`rightImg`);
* `IsGood49`: a good glued sample (the flow line is a simple proper arc, `R(K′_s)` is closed, both junction gaps
  are strict);
* `gCurve`, `gPre`, `gXL`, `gXR`, `imgρL`, `imgρR`, and the killed image word `imgW`, `imgVL`, `imgVR`, `imgT`;
* **`isKilledArc_gCurve`**, **`isKilledWord_img`**: the image is a killed arc and its word a killed word
  (`ImgDrv.IsKilledWord`) at every glued sample.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond MartChar.RealFlow Cond44Ref CfRegQ Prop411Q

namespace Word49

/-! ### The counterflow chart read from the stopped history -/

section Chart

/-- **The counterflow driver of the history stopped at `s`**, recentred at `0` (the counterflow's driver on `[0, s]`
on good histories). -/
def cfDrv0 (s : ℝ≥0) (y : HistorySpace 0 0) (t : ℝ) : ℝ :=
  Ito.rpath (Sec4.regPath (cfStop s y)) t - Ito.rpath (Sec4.regPath (cfStop s y)) 0

theorem continuous_cfDrv0 (s : ℝ≥0) (y : HistorySpace 0 0) : Continuous (cfDrv0 s y) :=
  (Sec4.continuous_rpath_regPath _).sub continuous_const

theorem cfDrv0_zero (s : ℝ≥0) (y : HistorySpace 0 0) : cfDrv0 s y 0 = 0 := sub_self _

theorem measurable_cfDrv0_apply (s : ℝ≥0) (t : ℝ) :
    Measurable[stopSigma s] fun y : HistorySpace 0 0 => cfDrv0 s y t := by
  have h : ∀ r : ℝ, Measurable[stopSigma s] fun y : HistorySpace 0 0 => Ito.rpath (Sec4.regPath (cfStop s y)) r :=
    fun r => (Sec4.measurable_regPath_apply r.toNNReal).comp (comap_measurable _)
  exact (h t).sub (h 0)

theorem measurable_cfDrv0_apply' (s : ℝ≥0) (t : ℝ) : Measurable fun y : HistorySpace 0 0 => cfDrv0 s y t :=
  (measurable_cfDrv0_apply s t).mono (stopSigma_le s) le_rfl

/-- **The image of a left real point** `x ≤ 0` of the chart `Q` under `Ψ = R ∘ f_s ∘ R` (`R x = −1/x` lies right of
`0` in the chart `R`; its image under the centred map is `rightImg w (−1/x) s − w s`); `0` is fixed. -/
def psiL (w : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ := if x = 0 then 0 else -1 / (rightImg w (-1 / x) s - w s)

/-- **The image of a right real point** `x ≥ 0` of the chart `Q` under `Ψ` (through the reflected flow). -/
def psiR (w : ℝ → ℝ) (s : ℝ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else -1 / (-rightImg (fun r => -w r) (1 / x) s - w s)

/-- **The left junction** `Ψ(∞⁻) = −1/(f_s(0⁺) − w_s)`. -/
def junL (w : ℝ → ℝ) (s : ℝ) : ℝ := -1 / (rightImg w 0 s - w s)

/-- **The right junction** `Ψ(∞⁺) = −1/(f_s(0⁻) − w_s)`. -/
def junR (w : ℝ → ℝ) (s : ℝ) : ℝ := -1 / (-rightImg (fun r => -w r) 0 s - w s)

variable {w : ℝ → ℝ} {s : ℝ}

theorem neg_one_div_le_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : -1 / a ≤ -1 / b := by
  have := one_div_le_one_div_of_le ha hab
  rw [neg_div, neg_div]
  linarith

theorem neg_one_div_le_of_neg {a b : ℝ} (hb : b < 0) (hab : a ≤ b) : -1 / a ≤ -1 / b := by
  have := one_div_le_one_div_of_neg_of_le hb hab
  rw [neg_div, neg_div]
  linarith

theorem rightImg_sub_ge (hw : Continuous w) (hs : 0 ≤ s) {y : ℝ} (hy : 0 ≤ y) :
    rightImg w 0 s - w s ≤ rightImg w y s - w s := by
  linarith [rightImg_mono_index hw (x := 0) (x' := y) hs hy]

theorem neg_rightImg_neg_sub_le (hw : Continuous w) (hs : 0 ≤ s) {y : ℝ} (hy : 0 ≤ y) :
    -rightImg (fun r => -w r) y s - w s ≤ -rightImg (fun r => -w r) 0 s - w s := by
  have h := rightImg_mono_index (w := fun r => -w r) (by fun_prop) (x := 0) (x' := y) hs hy
  linarith

theorem psiL_nonpos (hw : Continuous w) (hs : 0 ≤ s) (hj : 0 < rightImg w 0 s - w s) {x : ℝ} (hx : x ≤ 0) :
    psiL w s x ≤ 0 := by
  unfold psiL
  split_ifs with h0
  · exact le_rfl
  · have hy : 0 ≤ -1 / x := div_nonneg_of_nonpos (by norm_num) hx
    have hc := (rightImg_sub_ge hw hs hy)
    rw [neg_div]
    exact neg_nonpos.2 (div_pos one_pos (hj.trans_le hc)).le

theorem junL_le_psiL (hw : Continuous w) (hs : 0 ≤ s) (hj : 0 < rightImg w 0 s - w s) {x : ℝ} (hx : x ≤ 0) :
    junL w s ≤ psiL w s x := by
  unfold junL psiL
  split_ifs with h0
  · rw [neg_div]; exact neg_nonpos.2 (div_pos one_pos hj).le
  · have hy : 0 ≤ -1 / x := div_nonneg_of_nonpos (by norm_num) hx
    have hc := rightImg_sub_ge hw hs hy
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact one_div_le_one_div_of_le hj hc

theorem psiL_mono (hw : Continuous w) (hs : 0 ≤ s) (hj : 0 < rightImg w 0 s - w s) {x x' : ℝ} (hx : x ≤ 0)
    (hxx : x' ≤ x) : psiL w s x' ≤ psiL w s x := by
  by_cases h0 : x = 0
  · rw [h0, show psiL w s 0 = 0 by simp [psiL]]
    exact psiL_nonpos hw hs hj (hxx.trans hx)
  · have hxn : x < 0 := lt_of_le_of_ne hx h0
    have hx'n : x' < 0 := hxx.trans_lt hxn
    have hy : 0 ≤ -1 / x := div_nonneg_of_nonpos (by norm_num) hx
    have hyy : -1 / x' ≤ -1 / x := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact one_div_le_one_div_of_neg_of_le hxn hxx
    have hc := rightImg_mono_index hw (x := -1 / x') (x' := -1 / x) hs hyy
    have hpos : 0 < rightImg w (-1 / x') s - w s :=
      hj.trans_le (rightImg_sub_ge hw hs (div_nonneg_of_nonpos (by norm_num) hx'n.le))
    have e1 : psiL w s x' = -1 / (rightImg w (-1 / x') s - w s) := by simp only [psiL, hx'n.ne, ↓reduceIte]
    have e2 : psiL w s x = -1 / (rightImg w (-1 / x) s - w s) := by simp only [psiL, h0, ↓reduceIte]
    rw [e1, e2]
    exact neg_one_div_le_of_pos hpos (by linarith)

theorem psiR_nonneg (hw : Continuous w) (hs : 0 ≤ s) (hj : -rightImg (fun r => -w r) 0 s - w s < 0) {x : ℝ}
    (hx : 0 ≤ x) : 0 ≤ psiR w s x := by
  unfold psiR
  split_ifs with h0
  · exact le_rfl
  · have hy : 0 ≤ 1 / x := div_nonneg zero_le_one hx
    have hc := neg_rightImg_neg_sub_le hw hs hy
    rw [neg_div, ← div_neg]
    exact (div_pos one_pos (neg_pos.2 (hc.trans_lt hj))).le

theorem psiR_le_junR (hw : Continuous w) (hs : 0 ≤ s) (hj : -rightImg (fun r => -w r) 0 s - w s < 0) {x : ℝ}
    (hx : 0 ≤ x) : psiR w s x ≤ junR w s := by
  by_cases h0 : x = 0
  · have e : psiR w s x = 0 := by simp only [psiR, h0, ↓reduceIte]
    rw [e, junR, neg_div, ← div_neg]
    exact (div_pos one_pos (neg_pos.2 hj)).le
  · have hy : 0 ≤ 1 / x := div_nonneg zero_le_one hx
    have hc := neg_rightImg_neg_sub_le hw hs hy
    have e : psiR w s x = -1 / (-rightImg (fun r => -w r) (1 / x) s - w s) := by simp only [psiR, h0, ↓reduceIte]
    rw [e, junR]
    exact neg_one_div_le_of_neg hj hc

theorem psiR_mono (hw : Continuous w) (hs : 0 ≤ s) (hj : -rightImg (fun r => -w r) 0 s - w s < 0) {x x' : ℝ}
    (hx : 0 ≤ x) (hxx : x ≤ x') : psiR w s x ≤ psiR w s x' := by
  by_cases h0 : x = 0
  · rw [h0, show psiR w s 0 = 0 by simp [psiR]]
    exact psiR_nonneg hw hs hj (hx.trans hxx)
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have hx'p : 0 < x' := hxp.trans_le hxx
    have hyy : 1 / x' ≤ 1 / x := one_div_le_one_div_of_le hxp hxx
    have hc := rightImg_mono_index (w := fun r => -w r) (by fun_prop) (x := 1 / x') (x' := 1 / x) hs hyy
    have hneg : -rightImg (fun r => -w r) (1 / x) s - w s < 0 :=
      (neg_rightImg_neg_sub_le hw hs (div_nonneg zero_le_one hx)).trans_lt hj
    have hneg' : -rightImg (fun r => -w r) (1 / x') s - w s < 0 :=
      (neg_rightImg_neg_sub_le hw hs (div_nonneg zero_le_one hx'p.le)).trans_lt hj
    have e1 : psiR w s x = -1 / (-rightImg (fun r => -w r) (1 / x) s - w s) := by simp only [psiR, h0, ↓reduceIte]
    have e2 : psiR w s x' = -1 / (-rightImg (fun r => -w r) (1 / x') s - w s) := by
      simp only [psiR, hx'p.ne', ↓reduceIte]
    rw [e1, e2]
    exact neg_one_div_le_of_neg hneg' (by linarith)

end Chart

/-! ### Appending a mark -/

section Snoc

theorem antitone_snoc {n : ℕ} {f : Fin n → ℝ} (hf : Antitone f) {x : ℝ} (hx : ∀ i, x ≤ f i) :
    Antitone (Fin.snoc f x : Fin (n + 1) → ℝ) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_le_castSucc_iff.1 hij)
    · exact absurd hij (not_le.2 (Fin.castSucc_lt_last j'))
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx i'
    · exact le_rfl

theorem monotone_snoc {n : ℕ} {f : Fin n → ℝ} (hf : Monotone f) {x : ℝ} (hx : ∀ i, f i ≤ x) :
    Monotone (Fin.snoc f x : Fin (n + 1) → ℝ) := by
  intro i j hij
  rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc]
      exact hf (Fin.castSucc_le_castSucc_iff.1 hij)
    · exact absurd hij (not_le.2 (Fin.castSucc_lt_last j'))
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · simp only [Fin.snoc_castSucc, Fin.snoc_last]
      exact hx i'
    · exact le_rfl

theorem snoc_le {n : ℕ} {f : Fin n → ℝ} {x c : ℝ} (hf : ∀ i, f i ≤ c) (hx : x ≤ c) (i : Fin (n + 1)) :
    (Fin.snoc f x : Fin (n + 1) → ℝ) i ≤ c := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]; exact hf i'
  · simp only [Fin.snoc_last]; exact hx

theorem le_snoc {n : ℕ} {f : Fin n → ℝ} {x c : ℝ} (hf : ∀ i, c ≤ f i) (hx : c ≤ x) (i : Fin (n + 1)) :
    c ≤ (Fin.snoc f x : Fin (n + 1) → ℝ) i := by
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
  · simp only [Fin.snoc_castSucc]; exact hf i'
  · simp only [Fin.snoc_last]; exact hx

end Snoc

/-! ### The image word on the glued space -/

section Word

variable {Ω : Type*} {nL nR : ℕ}

/-- **A good glued sample** for the counterflow time `s`: the flow line is a simple proper arc, the reflected
counterflow hull `R(K′_s)` (read from the stopped history) is closed, both junction gaps are strict, and GLUECOND's
history-level hull `cfHullQ s` is `R(K′_s)`. -/
def IsGood49 (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (p : Ω × HistorySpace 0 0) : Prop :=
  IsProperArc (seedLine ζ W p.1) ∧ IsClosed (negInv '' fwdHull (cfDrv0 s p.2) s) ∧
    0 < rightImg (cfDrv0 s p.2) 0 s - cfDrv0 s p.2 s ∧
    -rightImg (fun r => -cfDrv0 s p.2 r) 0 s - cfDrv0 s p.2 s < 0 ∧
    cfHullQ s p.2 = negInv '' fwdHull (cfDrv0 s p.2) s

open scoped Classical in
/-- **The image curve** `Ψ ∘ η` on `E`, the vertical ray elsewhere. -/
def gCurve (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (p : Ω × HistorySpace 0 0) : ℝ → ℂ :=
  if p ∈ E then imgCurve (cfDrv0 s p.2) s (seedLine ζ W p.1) else vRay

open scoped Classical in
/-- **The pre-contact times** of the flow line with `R(K′_s)` (GLUECOND's `cfHullQ s`, hitting-measurable) on `E`,
`[0, ∞)` elsewhere. -/
def gPre (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (p : Ω × HistorySpace 0 0) : Set ℝ :=
  if p ∈ E then preContact (seedLine ζ W p.1) (cfHullQ s p.2) else Ici 0

open scoped Classical in
/-- **The left marks of the image word**: the images `Ψ(x_{i,L})` and the left junction `Ψ(∞⁻)` (`0` off `E`). -/
def gXL (xL : Fin nL → ℝ) (s : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) (p : Ω × HistorySpace 0 0) :
    Fin (nL + 1) → ℝ :=
  if p ∈ E then Fin.snoc (fun i => psiL (cfDrv0 s p.2) s (xL i)) (junL (cfDrv0 s p.2) s) else fun _ => 0

open scoped Classical in
/-- **The right marks of the image word**: the images `Ψ(x_{j,R})` and the right junction `Ψ(∞⁺)`. -/
def gXR (xR : Fin nR → ℝ) (s : ℝ≥0) (E : Set (Ω × HistorySpace 0 0)) (p : Ω × HistorySpace 0 0) :
    Fin (nR + 1) → ℝ :=
  if p ∈ E then Fin.snoc (fun j => psiR (cfDrv0 s p.2) s (xR j)) (junR (cfDrv0 s p.2) s) else fun _ => 0

/-- **The left weights of the image word**: the flow word's weights and the junction weight `κ/2 − 2 − Σρ_L`
(the exposed left side of the counterflow has the flattened height `−λ + πχ`, Remark 4.10). -/
def imgρL (κ : ℝ) (ρL : Fin nL → ℝ) : Fin (nL + 1) → ℝ := Fin.snoc ρL (κ / 2 - 2 - ∑ i, ρL i)

/-- **The right weights of the image word**: the flow word's weights and the junction weight `−Σρ_R` (the exposed
right side has the height `λ`). -/
def imgρR (ρR : Fin nR → ℝ) : Fin (nR + 1) → ℝ := Fin.snoc ρR (-∑ j, ρR j)

/-- **The killed image driver.** -/
def imgW (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) :
    ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun t p => kW (gCurve s ζ W E p) (gPre s ζ W E p) t

/-- **The images of the left marks.** -/
def imgVL (xL : Fin nL → ℝ) (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) :
    Fin (nL + 1) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun i t p => kVL (gCurve s ζ W E p) (gPre s ζ W E p) (gXL xL s E p) i t

/-- **The images of the right marks.** -/
def imgVR (xR : Fin nR → ℝ) (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) :
    Fin (nR + 1) → ℝ≥0 → Ω × HistorySpace 0 0 → ℝ :=
  fun j t p => kVR (gCurve s ζ W E p) (gPre s ζ W E p) (gXR xR s E p) j t

/-- **The terminal capacity of the image** (the killing time: the capacity of the first contact). -/
def imgT (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0)) :
    Ω × HistorySpace 0 0 → WithTop ℝ≥0 :=
  fun p => kLife (gCurve s ζ W E p) (gPre s ζ W E p)

/-- **The image trace in capacity time.** -/
def imgTr (s : ℝ≥0) (ζ : Ω → ℝ≥0∞) (W : ℝ≥0 → Ω → ℝ) (E : Set (Ω × HistorySpace 0 0))
    (p : Ω × HistorySpace 0 0) : ℝ≥0 → ℂ :=
  kTrace (gCurve s ζ W E p) (gPre s ζ W E p)

variable {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}

theorem gCurve_of_mem {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    gCurve s ζ W E p = imgCurve (cfDrv0 s p.2) s (seedLine ζ W p.1) := by
  simp only [gCurve, hp, ↓reduceIte]

theorem gPre_of_mem {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    gPre s ζ W E p = preContact (seedLine ζ W p.1) (cfHullQ s p.2) := by
  simp only [gPre, hp, ↓reduceIte]

theorem gXL_of_mem {xL : Fin nL → ℝ} {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    gXL xL s E p = Fin.snoc (fun i => psiL (cfDrv0 s p.2) s (xL i)) (junL (cfDrv0 s p.2) s) := by
  simp only [gXL, hp, ↓reduceIte]

theorem gXR_of_mem {xR : Fin nR → ℝ} {p : Ω × HistorySpace 0 0} (hp : p ∈ E) :
    gXR xR s E p = Fin.snoc (fun j => psiR (cfDrv0 s p.2) s (xR j)) (junR (cfDrv0 s p.2) s) := by
  simp only [gXR, hp, ↓reduceIte]

/-- **On good samples the image is a killed arc** (WangWu's `isKilledArc_imgCurve` with the obstacle `R(K′_s)`);
elsewhere the vertical ray. -/
theorem isKilledArc_gCurve (hE : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) :
    IsKilledArc (gCurve s ζ W E p) (gPre s ζ W E p) := by
  by_cases hp : p ∈ E
  · obtain ⟨hα, hG, -, -, hQ⟩ := hE p hp
    rw [gCurve_of_mem hp, gPre_of_mem hp, hQ]
    exact isKilledArc_imgCurve (continuous_cfDrv0 s p.2) (cfDrv0_zero s p.2) s.coe_nonneg hG hα
  · simp only [gCurve, gPre, hp, ↓reduceIte]
    exact isKilledArc_vRay

theorem gXL_nonpos {xL : Fin nL → ℝ} (hxL : ∀ i, xL i ≤ 0) (hE : ∀ p ∈ E, IsGood49 s ζ W p)
    (p : Ω × HistorySpace 0 0) (i : Fin (nL + 1)) : gXL xL s E p i ≤ 0 := by
  by_cases hp : p ∈ E
  · obtain ⟨-, -, hj, -, -⟩ := hE p hp
    rw [gXL_of_mem hp]
    have hw := continuous_cfDrv0 s p.2
    exact snoc_le (fun i => psiL_nonpos hw s.coe_nonneg hj (hxL i))
      ((junL_le_psiL hw s.coe_nonneg hj le_rfl).trans (psiL_nonpos hw s.coe_nonneg hj le_rfl)) i
  · simp [gXL, hp]

theorem gXR_nonneg {xR : Fin nR → ℝ} (hxR : ∀ j, 0 ≤ xR j) (hE : ∀ p ∈ E, IsGood49 s ζ W p)
    (p : Ω × HistorySpace 0 0) (j : Fin (nR + 1)) : 0 ≤ gXR xR s E p j := by
  by_cases hp : p ∈ E
  · obtain ⟨-, -, -, hj, -⟩ := hE p hp
    rw [gXR_of_mem hp]
    have hw := continuous_cfDrv0 s p.2
    exact le_snoc (fun j => psiR_nonneg hw s.coe_nonneg hj (hxR j))
      ((psiR_nonneg hw s.coe_nonneg hj le_rfl).trans (psiR_le_junR hw s.coe_nonneg hj le_rfl)) j
  · simp [gXR, hp]

theorem antitone_gXL {xL : Fin nL → ℝ} (hxL : ∀ i, xL i ≤ 0) (hxLa : Antitone xL)
    (hE : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) : Antitone (gXL xL s E p) := by
  by_cases hp : p ∈ E
  · obtain ⟨-, -, hj, -, -⟩ := hE p hp
    rw [gXL_of_mem hp]
    have hw := continuous_cfDrv0 s p.2
    exact antitone_snoc (fun i i' hii => psiL_mono hw s.coe_nonneg hj (hxL i) (hxLa hii))
      (fun i => junL_le_psiL hw s.coe_nonneg hj (hxL i))
  · simp only [gXL, hp, ↓reduceIte]
    exact antitone_const

theorem monotone_gXR {xR : Fin nR → ℝ} (hxR : ∀ j, 0 ≤ xR j) (hxRm : Monotone xR)
    (hE : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) : Monotone (gXR xR s E p) := by
  by_cases hp : p ∈ E
  · obtain ⟨-, -, -, hj, -⟩ := hE p hp
    rw [gXR_of_mem hp]
    have hw := continuous_cfDrv0 s p.2
    exact monotone_snoc (fun j j' hjj => psiR_mono hw s.coe_nonneg hj (hxR j) (hxRm hjj))
      (fun j => psiR_le_junR hw s.coe_nonneg hj (hxR j))
  · simp only [gXR, hp, ↓reduceIte]
    exact monotone_const

/-- **The image word is a killed word** at every glued sample (for an ordered flow word). -/
theorem isKilledWord_img {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR)
    (hE : ∀ p ∈ E, IsGood49 s ζ W p) :
    ImgDrv.IsKilledWord (imgW s ζ W E) (imgVL xL s ζ W E) (imgVR xR s ζ W E) (imgT s ζ W E) :=
  isKilledWord_kW (isKilledArc_gCurve hE) (gXL_nonpos hF.2.1 hE) (gXR_nonneg hF.2.2.2 hE)
    (antitone_gXL hF.2.1 hF.1 hE) (monotone_gXR hF.2.2.2 hF.2.2.1 hE)

/-- **The image trace** is a simple trace in `ℍ` generating the killed image chain before the terminal capacity. -/
theorem isGeneratingTraceIcc_imgTr (hE : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < imgT s ζ W E p) :
    Sec7.IsGeneratingTraceIcc (imgW s ζ W E · p) t (imgTr s ζ W E p) :=
  (isKilledArc_gCurve hE p).isGeneratingTraceIcc_kTrace ht

theorem imgTr_inj (hE : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) {a b : ℝ≥0}
    (ha : (a : WithTop ℝ≥0) < imgT s ζ W E p) (hb : (b : WithTop ℝ≥0) < imgT s ζ W E p)
    (hab : imgTr s ζ W E p a = imgTr s ζ W E p b) : a = b :=
  (isKilledArc_gCurve hE p).kTrace_injOn ha hb hab

theorem imgTr_mem_H (hE : ∀ p ∈ E, IsGood49 s ζ W p) (p : Ω × HistorySpace 0 0) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : WithTop ℝ≥0) < imgT s ζ W E p) : imgTr s ζ W E p t ∈ H :=
  (isKilledArc_gCurve hE p).kTrace_mem_H ht0 ht

end Word

/-! ### Almost every glued sample is good -/

section Good

theorem cfDrv0_toNNReal (s : ℝ≥0) (y : HistorySpace 0 0) (r : ℝ) :
    cfDrv0 s y ((r.toNNReal : ℝ≥0) : ℝ) = cfDrv0 s y r := by
  simp only [cfDrv0, Ito.rpath, Real.toNNReal_coe]

/-- The real Loewner flow of `sg · cfDrv0` is measurable in the history. -/
theorem measurable_rightImg_cfDrv0 (s : ℝ≥0) (sg x : ℝ) (t : ℝ≥0) :
    Measurable fun y : HistorySpace 0 0 => rightImg (fun r => sg * cfDrv0 s y r) x t := by
  have h := Sec7.PocketTraversal.measurable_rightImg_realPath_of_measurable
    (𝓕 := Sec4.histFiltration (nL := 0) (nR := 0)) (W := fun r y => sg * cfDrv0 s y r)
    (fun r => ((measurable_cfDrv0_apply' s r).const_mul sg).mono (Sec4.histFiltration_apply r).le le_rfl)
    (fun y => ((continuous_cfDrv0 s y).comp NNReal.continuous_coe).const_smul sg) (x := fun _ => x)
    measurable_const t
  have e : ∀ y : HistorySpace 0 0, Bessel.realPath (fun r y => sg * cfDrv0 s y r) y = fun r => sg * cfDrv0 s y r :=
    fun y => funext fun r => by simp only [Bessel.realPath, cfDrv0_toNNReal]
  simp_rw [e] at h
  exact h.mono (Sec4.histFiltration_apply t).ge le_rfl

/-- **The good histories for the counterflow time `s`**: good hitting histories (GLUECOND3) with strict junction
gaps. -/
def goodSet49 (s : ℝ≥0) : Set (HistorySpace 0 0) :=
  goodHitSet ∩ {y | 0 < rightImg (cfDrv0 s y) 0 s - cfDrv0 s y s ∧
    -rightImg (fun r => -cfDrv0 s y r) 0 s - cfDrv0 s y s < 0}

theorem measurableSet_goodSet49 (s : ℝ≥0) : MeasurableSet (goodSet49 s) := by
  have h1 : Measurable fun y : HistorySpace 0 0 => rightImg (cfDrv0 s y) 0 s := by
    have := measurable_rightImg_cfDrv0 s 1 0 s
    simpa only [one_mul] using this
  have h2 : Measurable fun y : HistorySpace 0 0 => rightImg (fun r => -cfDrv0 s y r) 0 s := by
    have := measurable_rightImg_cfDrv0 s (-1) 0 s
    simpa only [neg_one_mul] using this
  have h3 : Measurable fun y : HistorySpace 0 0 => cfDrv0 s y s := measurable_cfDrv0_apply' s s
  exact measurableSet_goodHitSet.inter ((measurableSet_lt measurable_const (h1.sub h3)).inter
    (measurableSet_lt ((h2.neg).sub h3) measurable_const))

/-- On good histories the stopped driver is the counterflow driver on `[0, s]`. -/
theorem cfDrv0_eq_cfDrv {y : HistorySpace 0 0} (hy : y ∈ goodCfSet) {s : ℝ≥0} {t : ℝ} (ht : t ∈ Icc 0 (s : ℝ)) :
    cfDrv0 s y t = cfDrv y t := by
  have h0 := (CfRegQ.reg_of_mem_goodCfSet hy).2.2.1
  have hts : t.toNNReal ≤ s := by
    rw [Real.toNNReal_le_iff_le_coe]; exact ht.2
  simp only [cfDrv0, Ito.rpath, regPath_cfStop_of_mem_goodCfSet hy, min_eq_left hts, Real.toNNReal_zero,
    zero_le, min_eq_left]
  rw [CfRegQ.cfDrv_eq_hDrv] at h0 ⊢
  simp only [Real.toNNReal_zero] at h0
  rw [h0, sub_zero]

/-- On good histories `R(K′_s)` read through the stopped driver is closed. -/
theorem isClosed_of_mem_goodSet49 {s : ℝ≥0} {y : HistorySpace 0 0} (hy : y ∈ goodSet49 s) :
    IsClosed (negInv '' fwdHull (cfDrv0 s y) s) := by
  have hg : y ∈ goodCfSet := hy.1.1
  have hc := (CfRegQ.reg_of_mem_goodCfSet hg).2.1
  have e : fwdHull (cfDrv0 s y) s = fwdHull (cfDrv y) s :=
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_cfDrv0 s y) hc s.coe_nonneg fun r hr => cfDrv0_eq_cfDrv hg hr
  rw [e]
  exact (isClosed_negInv_fwdHull_of_mem_goodHitSet hy.1 s.coe_nonneg).1

theorem cfHullQ_eq_of_mem_goodSet49 {s : ℝ≥0} {y : HistorySpace 0 0} (hy : y ∈ goodSet49 s) :
    cfHullQ s y = negInv '' fwdHull (cfDrv0 s y) s := by
  have hg : y ∈ goodCfSet := hy.1.1
  have hc := (CfRegQ.reg_of_mem_goodCfSet hg).2.1
  rw [cfHullQ_eq_of_mem_goodCfSet hg,
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_cfDrv0 s y) hc s.coe_nonneg fun r hr => cfDrv0_eq_cfDrv hg hr]

theorem isGood49_of_mem {Ω : Type*} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {p : Ω × HistorySpace 0 0}
    (hα : IsProperArc (seedLine ζ W p.1)) (hy : p.2 ∈ goodSet49 s) : IsGood49 s ζ W p :=
  ⟨hα, isClosed_of_mem_goodSet49 hy, hy.2.1, hy.2.2, cfHullQ_eq_of_mem_goodSet49 hy⟩

/-- **On the counterflow's space, the counterflow history is good at every positive time `s`**: the seed marks of
the counterflow word are strictly separated from the driver (Aux. lemma 6), and they are the real images of `0⁺`,
`0⁻` (`WangWu.vR_eq_rightImg`). -/
theorem cfHistory_mem_goodSet49 {Ω₂ : Type*} {W₂ : ℝ≥0 → Ω₂ → ℝ} {ζ₂ : Ω₂ → ℝ≥0∞} {ω : Ω₂} {mL mR : ℕ}
    {yL : Fin mL → ℝ} {yR : Fin mR → ℝ} {σL : Fin mL → ℝ} {σR : Fin mR → ℝ} {a : ℝ}
    {vL : Fin mL → ℝ≥0 → ℝ} {vR : Fin mR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hp : IsIntegratedSLEPath a yL yR σL σR (fun t => W₂ t ω) vL vR b (ζ₂ ω)) (hζ : ζ₂ ω = ⊤)
    (hw : Continuous fun t => W₂ t ω) (hsep : ∀ t : ℝ≥0, 0 < t → (∀ i, vL i t < W₂ t ω) ∧ ∀ i, W₂ t ω < vR i t)
    {iL : Fin mL} (hiL : yL iL = 0) {iR : Fin mR} (hiR : yR iR = 0)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun t => W₂ t ω) ⊤ η)
    (hne : ∀ t : ℝ≥0, 0 < t → ∀ x : ℝ, x ≠ 0 → η t ≠ x) {s : ℝ≥0} (hs : 0 < s) :
    cfHistory W₂ ζ₂ ω ∈ goodSet49 s := by
  have hw0 : W₂ 0 ω = 0 := hp.1
  refine ⟨cfHistory_mem_goodHitSet hζ hw hw0 hη hne, ?_⟩
  set y := cfHistory W₂ ζ₂ ω with hy
  have hrw : Continuous (Ito.rpath fun t => W₂ t ω) := hw.comp continuous_real_toNNReal
  have hEq : EqOn (cfDrv0 s y) (Ito.rpath fun t => W₂ t ω) (Icc 0 (s : ℝ)) := by
    intro r hr
    have hrs : r.toNNReal ≤ s := by rw [Real.toNNReal_le_iff_le_coe]; exact hr.2
    simp only [cfDrv0, Ito.rpath, hy, regPath_cfStop_cfHistory hζ hw0 hw, min_eq_left hrs,
      Real.toNNReal_zero, zero_le, min_eq_left, hw0, sub_zero]
  have hEqn : EqOn (fun r => -cfDrv0 s y r) (fun r => -Ito.rpath (fun t => W₂ t ω) r) (Icc 0 (s : ℝ)) :=
    fun r hr => by simp only [hEq hr]
  have hs' : ((s : ℝ≥0) : ℝ≥0∞) < ζ₂ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hR := WangWu.vR_eq_rightImg hp hw hs' iR
  have hL := WangWu.vL_eq_neg_rightImg hp hw hs' iL
  rw [hiR] at hR
  rw [hiL, neg_zero] at hL
  have e1 : rightImg (cfDrv0 s y) 0 s = rightImg (Ito.rpath fun t => W₂ t ω) 0 s :=
    Sec7.Lemma71B.rightImg_congr hrw s.coe_nonneg hEq 0
  have e2 : rightImg (fun r => -cfDrv0 s y r) 0 s = rightImg (fun r => -Ito.rpath (fun t => W₂ t ω) r) 0 s :=
    Sec7.Lemma71B.rightImg_congr hrw.neg s.coe_nonneg hEqn 0
  have e3 : cfDrv0 s y s = W₂ s ω := by
    rw [hEq ⟨s.coe_nonneg, le_rfl⟩]; simp [Ito.rpath]
  obtain ⟨hsL, hsR⟩ := hsep s hs
  refine ⟨?_, ?_⟩
  · rw [e1, e3, ← hR]; linarith [hsR iR]
  · rw [e2, e3]
    have := hsL iL
    rw [hL] at this
    linarith

end Good

/-! ### On the glued space -/

section GlueAE

universe u

/-- **G4, Proposition 4.9's direction: almost every glued sample is good at a positive counterflow time `s`** (in the
setting of `Prop411Q.CfGlueAE`): the flow line is a simple proper arc, and the counterflow history is a good hitting
history (GLUECOND3) whose two junction gaps at time `s` are strict (Aux. lemma 6 for the seed marks of the
counterflow word). Hence `IsGood49 s ζ W p` almost surely (`isGood49_of_mem`). -/
theorem cfGlueAE_isGood49 (s : ℝ≥0) (hs : 0 < s) :
    CfGlueAE.{u} fun η y => IsProperArc η ∧ y ∈ goodSet49 s := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hX₂ := isMeasurableKilledDriving_of_isCenteredCounterflowDriver hcf
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  have hΩ₂ : ∀ᵐ ω ∂P₂, cfHistory W₂ ζ₂ ω ∈ goodSet49 s := by
    obtain ⟨mL, mR, yL, yR, σL, σR, 𝓕₂, VL₂, VR₂, B₂, hF', hadm', hE, ⟨iL, hiL⟩, ⟨iR, hiR⟩⟩ :=
      exists_seed_admissible_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw
    have hk' : 0 < 16 / κ := by positivity
    filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk' hF' hadm' hE,
      hE.2.2.2.2, ae_trace_ne_real_of_isCenteredCounterflowDriver hκ hκ4 hF h44 hC hcf hlaw]
      with ω ⟨hζ, hsep, η, hη⟩ hp hne
    have hw : Continuous fun t => W₂ t ω := by
      have := hp.2.2.2.1
      rw [hζ] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    exact cfHistory_mem_goodSet49 hp hζ hw hsep hiL hiR hη (fun t _ x hx => hne η hη t x hx) hs
  have h2 := ae_glue_snd hXm (measurable_of_isCenteredCounterflowDriver hcf) (measurable_cfHistory hX₂) hlaw k hk
    (measurableSet_goodSet49 s) hΩ₂
  filter_upwards [hline, h2] with p hp1 hp2
  exact ⟨hp1.2.2, hp2⟩

end GlueAE

end Word49

end InteractingSLE.Sec5.CrossCond

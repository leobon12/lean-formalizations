/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInWordBdry
import InteractingSLE.Spec.Supplement.RelTransHull

/-!
# BR4a's relative words: the two-sided real flow and its conjugation (deterministic)

Packet PROVE-T14-BR4A3. For a continuous driver `w` from `0`, the real points off the closed hull `K_t` (other than
`0`) flow to real images: `flowVal w t y = Re g_t(y)` is `g_t(y)` on the right (`y > 0`, alive) and
`−g̃_t(−y)` (reflected driver) on the left.

* `flowVal_spec`, `flowVal_ofReal`: the two cases;
* **`flowVal_lt_flowVal`**: the real flow is strictly increasing on the real points off the closed hull;
* `rightImg_le_flowVal`, `flowVal_le_leftImg`: the images of the alive points lie outside `[L₀, R₀]`, the images of
  `0⁻`, `0⁺`;
* **`flowVal_conj`**: under the conjugation of `BR4aIn.exists_conj`, `flowVal u q (mob v y) = N(flowVal w t y)`;
* `nfR_lt_nfR`, `lt_nfR`, `nfR_lt`: the real Möbius map `N x = α − κN/(x − P)` is increasing on each side of `P`,
  above `α` left of `P` and below `α` right of it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain ConformalImage ConformalImageFull Supp8.HullDetGen Sec5.CrossRestart MartChar.RealFlow

/-! ### The real Möbius map -/

section Nf

variable {α κN P : ℝ}

theorem nfR_lt_nfR (hκN : 0 < κN) {a b : ℝ} (hab : a < b) (hP : b < P ∨ P < a) :
    α - κN / (a - P) < α - κN / (b - P) := by
  rcases hP with hb | ha
  · have h1 : a - P < 0 := by linarith
    have h2 : b - P < 0 := by linarith
    have hprod : 0 < (a - P) * (b - P) := mul_pos_of_neg_of_neg h1 h2
    have key : κN / (a - P) - κN / (b - P) = κN * (b - a) / ((a - P) * (b - P)) := by
      rw [div_sub_div _ _ h1.ne h2.ne]
      congr 1
      ring
    have : 0 < κN * (b - a) / ((a - P) * (b - P)) := div_pos (mul_pos hκN (by linarith)) hprod
    linarith
  · have h1 : 0 < a - P := by linarith
    have h2 : 0 < b - P := by linarith
    have : κN / (b - P) < κN / (a - P) := div_lt_div_of_pos_left hκN h1 (by linarith)
    linarith

theorem nfR_le_nfR (hκN : 0 < κN) {a b : ℝ} (hab : a ≤ b) (hP : b < P ∨ P < a) :
    α - κN / (a - P) ≤ α - κN / (b - P) := by
  rcases hab.lt_or_eq with h | h
  · exact (nfR_lt_nfR hκN h hP).le
  · rw [h]

theorem lt_nfR (hκN : 0 < κN) {x : ℝ} (hx : x < P) : α < α - κN / (x - P) := by
  have : κN / (x - P) < 0 := div_neg_of_pos_of_neg hκN (by linarith)
  linarith

theorem nfR_lt (hκN : 0 < κN) {x : ℝ} (hx : P < x) : α - κN / (x - P) < α := by
  have : 0 < κN / (x - P) := div_pos hκN (by linarith)
  linarith

theorem nf_ofReal (x : ℝ) : nf α κN P (x : ℂ) = ((α - κN / (x - P) : ℝ) : ℂ) := by
  simp only [nf]
  push_cast
  rfl

end Nf

/-! ### The two-sided real flow -/

section Flow

variable {w : ℝ → ℝ} {t : ℝ}

/-- The real image `Re g_t(y)` of a real point. -/
def flowVal (w : ℝ → ℝ) (t y : ℝ) : ℝ := (bdryVal w y t).re

/-- **The two cases of the real flow** of a real point `y ≠ 0` off the closed hull: alive on the right, or alive on
the left for the reflected driver. -/
theorem flowVal_spec (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : y ≠ 0) :
    bdryVal w y t = (flowVal w t y : ℂ) ∧
      ((0 < y ∧ Alive w y t ∧ flowVal w t y = gImg w y t) ∨
        (y < 0 ∧ Alive (fun s => -w s) (-y) t ∧ flowVal w t y = -gImg (fun s => -w s) (-y) t)) := by
  obtain ⟨f, hf⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure hw hw0 ht hy hy0
  have hb := bdryVal_eq_of_isForwardSol hw ht hf
  rcases Restart.FCAux79.isForwardSol_real_cases hw hw0 ht hf with ⟨hpos, hal, hv⟩ | ⟨hneg, hal, hv⟩
  · have hval : bdryVal w y t = ((gImg w y t : ℝ) : ℂ) := by rw [hb, hv]; push_cast; ring
    have hfl : flowVal w t y = gImg w y t := by rw [flowVal, hval, Complex.ofReal_re]
    exact ⟨by rw [hval, hfl], Or.inl ⟨hpos, hal, hfl⟩⟩
  · have hval : bdryVal w y t = ((-gImg (fun s => -w s) (-y) t : ℝ) : ℂ) := by rw [hb, hv]; push_cast; ring
    have hfl : flowVal w t y = -gImg (fun s => -w s) (-y) t := by rw [flowVal, hval, Complex.ofReal_re]
    exact ⟨by rw [hval, hfl], Or.inr ⟨hneg, hal, hfl⟩⟩

/-- The real flow is a forward-solution value. -/
theorem flowVal_eq_of_isForwardSol (hw : Continuous w) (ht : 0 ≤ t) {y : ℝ} {f : ℝ → ℂ}
    (hf : QuantumZipper.IsForwardSol w (y : ℂ) t f) (hfr : (f t).im = 0) :
    f t + w t = (flowVal w t y : ℂ) := by
  have hb := bdryVal_eq_of_isForwardSol hw ht hf
  unfold flowVal
  rw [hb]
  apply Complex.ext
  · simp
  · simp [hfr]

/-- **The real flow is strictly increasing** on the real points off the closed hull. -/
theorem flowVal_lt_flowVal (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) {y₁ y₂ : ℝ}
    (hy₁ : (y₁ : ℂ) ∉ closure (fwdHull w t)) (hy₁0 : y₁ ≠ 0) (hy₂ : (y₂ : ℂ) ∉ closure (fwdHull w t))
    (hy₂0 : y₂ ≠ 0) (h12 : y₁ < y₂) : flowVal w t y₁ < flowVal w t y₂ := by
  have hwn : Continuous fun s => -w s := hw.neg
  rcases (flowVal_spec hw hw0 ht hy₁ hy₁0).2 with ⟨hp₁, ha₁, hf₁⟩ | ⟨hn₁, ha₁, hf₁⟩ <;>
    rcases (flowVal_spec hw hw0 ht hy₂ hy₂0).2 with ⟨hp₂, ha₂, hf₂⟩ | ⟨hn₂, ha₂, hf₂⟩
  · rw [hf₁, hf₂]
    exact Restart.FCAux79.gImg_lt_gImg hw ht ha₁ h12
  · linarith
  · have h1 := ha₁.lt_gImg hwn ⟨ht, le_rfl⟩
    have h2 := ha₂.lt_gImg hw ⟨ht, le_rfl⟩
    rw [hf₁, hf₂]
    linarith
  · rw [hf₁, hf₂]
    have := Restart.FCAux79.gImg_lt_gImg hwn ht ha₂ (neg_lt_neg h12)
    linarith

/-- Right alive images lie above the image `R₀` of `0⁺`. -/
theorem rightImg_le_flowVal (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : 0 < y) : rightImg w 0 t ≤ flowVal w t y := by
  rcases (flowVal_spec hw hw0 ht hy hy0.ne').2 with ⟨-, ha, hf⟩ | ⟨hn, -, -⟩
  · rw [hf]
    exact rightImg_le_gImg hw ht hy0 ha
  · linarith

/-- Left alive images lie below the image `L₀` of `0⁻`. -/
theorem flowVal_le_leftImg (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : y < 0) :
    flowVal w t y ≤ -rightImg (fun s => -w s) 0 t := by
  rcases (flowVal_spec hw hw0 ht hy hy0.ne).2 with ⟨hp, -, -⟩ | ⟨-, ha, hf⟩
  · linarith
  · rw [hf]
    have hwn : Continuous fun s => -w s := hw.neg
    have := rightImg_le_gImg hwn ht (neg_pos.2 hy0) ha
    linarith

/-- Right images lie right of the driver, left images left of it. -/
theorem flowVal_pos_side (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : 0 < y) : w t < flowVal w t y := by
  have h := rightImg_le_flowVal hw hw0 ht hy hy0
  have h0 := le_rightImg hw 0 ht
  rcases (flowVal_spec hw hw0 ht hy hy0.ne').2 with ⟨-, ha, hf⟩ | ⟨hn, -, -⟩
  · rw [hf]; exact ha.lt_gImg hw ⟨ht, le_rfl⟩
  · linarith

theorem flowVal_neg_side (hw : Continuous w) (hw0 : w 0 = 0) (ht : 0 ≤ t) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : y < 0) : flowVal w t y < w t := by
  rcases (flowVal_spec hw hw0 ht hy hy0.ne).2 with ⟨hp, -, -⟩ | ⟨-, ha, hf⟩
  · linarith
  · rw [hf]
    have hwn : Continuous fun s => -w s := hw.neg
    have := ha.lt_gImg hwn ⟨ht, le_rfl⟩
    linarith

end Flow

/-! ### The conjugation of the real flows -/

section Conj

variable {w u : ℝ → ℝ} {t q v α κN P : ℝ}

/-- **The conjugation of the real flows**: `flowVal u q (mob v y) = N(flowVal w t y)` for `y ≠ 0` off the closed hull
and off the pole, with `g_t(y) ≠ P`. -/
theorem flowVal_conj (hw : Continuous w) (hw0 : w 0 = 0) (hu : Continuous u) (hu0 : u 0 = 0) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (hK : mob v '' fwdHull w t = fwdHull u q)
    (hconj : ∀ z ∈ H \ fwdHull w t, gmap u q (mob v z) = nf α κN P (gmap w t z)) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fwdHull w t)) (hy0 : y ≠ 0) (hyp : v * y + 1 ≠ 0) (hP : flowVal w t y ≠ P) :
    ((y / (v * y + 1) : ℝ) : ℂ) ∉ closure (fwdHull u q) ∧ y / (v * y + 1) ≠ 0 ∧
      flowVal u q (y / (v * y + 1)) = α - κN / (flowVal w t y - P) := by
  have hmy : ((y / (v * y + 1) : ℝ) : ℂ) ∉ closure (fwdHull u q) := by
    rw [← mob_ofReal]; exact notMem_closure_mob hK hy hyp
  have hmy0 : y / (v * y + 1) ≠ 0 := div_ne_zero hy0 hyp
  refine ⟨hmy, hmy0, ?_⟩
  obtain ⟨f, hf⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure hw hw0 ht hy hy0
  obtain ⟨g, hg⟩ := Supp8.BHMean.exists_isForwardSol_of_notMem_closure hu hu0 hq hmy hmy0
  have hfr : (f t).im = 0 := InteractingSLE.im_eq_zero_of_isForwardSol_real hw hf ⟨ht, le_rfl⟩
  have hgr : (g q).im = 0 := InteractingSLE.im_eq_zero_of_isForwardSol_real hu hg ⟨hq, le_rfl⟩
  have hfv := flowVal_eq_of_isForwardSol hw ht hf hfr
  have hgv := flowVal_eq_of_isForwardSol hu hq hg hgr
  have hg' : QuantumZipper.IsForwardSol u (mob v (y : ℂ)) q g := by rw [mob_ofReal]; exact hg
  have hfP : f t + w t ≠ (P : ℂ) := by
    rw [hfv]; exact fun h => hP (Complex.ofReal_injective h)
  have h := conj_flow hw hu ht hq hconj hy hyp hf hg' hfP
  rw [hgv, hfv, nf_ofReal] at h
  exact Complex.ofReal_injective h

end Conj

end InteractingSLE.Theorem14.BR4aIn

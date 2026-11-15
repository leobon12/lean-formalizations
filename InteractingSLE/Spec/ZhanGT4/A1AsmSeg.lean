/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1AsmCofG
import InteractingSLE.Spec.ZhanGT4.A2TipSepGeom
import InteractingSLE.Spec.ZhanGT4.A2Part3IDHull
import InteractingSLE.Spec.ZhanGT4.CrosscutInterior

/-!
# Zhan's A.1 (G3): exhaustion by the segment family from mark-free prefixes

Packet PROVE-A1-ASSEMBLE. Source: Astra, *Follow-up proofs*, §A.1.5 (`ig1_followup_proofs.txt` L409–L425: "Any pair
of disjoint compact prefixes is contained in a member of the countable enclosure family"); R38.

`exists_rect_leG` (`A1AsmCofG`) needs, besides A1-COMMON's hypotheses for `exists_rect_le`, that the large prefix miss
the real segment `[0, qlo]` and that the small prefix miss `qlo`. For the G3 configuration (`qlo = x − y` is the
ordinary mark, left of the large source `−y`) both follow from "the mark avoids both prefixes": a real point left of an
alive real point is alive (the order of the real Loewner flow), and alive real points are off the closed hull.

* `notMem_closure_fwdHull_of_le` (deterministic): if `r₀ < 0` is off the closed hull of a continuous driver from `0`,
  so is every `r ≤ r₀`;
* `notMem_closure_fwdHull_shift_of_le`: the same for the hull of a path's driver shifted to its source `x₂ > r₀`;
* **`exists_rect_leG_of_marks`**: the G3 exhaustion with exactly the hypotheses of A1-COMMON's `exists_rect_le` (for
  the source `−y` and the mark `x − y`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Asm

open QuantumZipper (H fwdHull IsForwardSol)
open A1EightSeed A1Common

/-- **Real points left of a negative real point off the closed hull are off the closed hull** (for a continuous driver
from `0`): the point `r₀ ≠ 0` is alive, real points left of an alive negative point are alive, and alive real points
are off the closed hull. -/
theorem notMem_closure_fwdHull_of_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {r₀ : ℝ} (hr₀ : r₀ < 0) (h : (r₀ : ℂ) ∉ closure (fwdHull W T)) {r : ℝ} (hr : r ≤ r₀) :
    (r : ℂ) ∉ closure (fwdHull W T) := by
  rcases hr.eq_or_lt with rfl | hlt
  · exact h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl (r₀ : ℂ) h
  have hd : Disjoint (ball (r₀ : ℂ) ε) (fwdHull W T) :=
    Set.disjoint_left.2 fun z hz hzK => hball hz (subset_closure hzK)
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_disjoint_ball hW hW0 hr₀.ne hT hε hd
  obtain ⟨v, hv⟩ := A2P3ID.exists_isForwardSol_of_lt_left hW hW0 hT hr₀ hlt hu
  exact A2TipSep.not_mem_closure_fwdHull_of_isForwardSol hW hT hv

/-- **The shifted form**: for a path driver `w` (continuous before its lifetime, `w 0 = 0`) shifted to its source `x₂`,
at a time `t` before the lifetime, if a real point `c < x₂` is off the closed hull then so is every `r ≤ c`, and no such
`r` is the source. -/
theorem notMem_closure_fwdHull_shift_of_le {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {x₂ c : ℝ} (hc : c < x₂)
    (h : (c : ℂ) ∉ closure (fwdHull (Strip.extPath fun u => w u + x₂) t)) {r : ℝ} (hr : r ≤ c) :
    (r : ℂ) ∉ closure (fwdHull (Strip.extPath fun u => w u + x₂) t) ∪ {(x₂ : ℂ)} := by
  obtain ⟨R, htR, -, hcR⟩ := exists_real_btwn_continuousOn hwc ht
  have hR0 : 0 ≤ R := t.coe_nonneg.trans htR.le
  set W := A1Ref.stopDrv (Strip.extPath w) R with hWdef
  have hW : Continuous W := A1Ref.continuous_stopDrv hcR hR0
  have hW0 : W 0 = 0 := by
    rw [hWdef, A1Ref.stopDrv_eqOn _ _ ⟨le_rfl, hR0⟩]
    simp [Strip.extPath, hw0]
  have hK : fwdHull (Strip.extPath fun u => w u + x₂) t = (fun z : ℂ => z + x₂) '' fwdHull W t := by
    have e1 : (Strip.extPath fun u => w u + x₂) = fun s => Strip.extPath w s + x₂ := rfl
    rw [e1, ConformalImageFull.fwdHull_add_const, LocalExt.fwdHull_congr_of_eqOn_of_lt t.coe_nonneg htR
      fun u hu => (A1Ref.stopDrv_eqOn _ R hu).symm]
  have hcl : closure (fwdHull (Strip.extPath fun u => w u + x₂) t) =
      (fun z : ℂ => z + x₂) '' closure (fwdHull W t) := by
    rw [hK]
    exact ((Homeomorph.addRight (x₂ : ℂ)).image_closure (fwdHull W t)).symm
  have hmem : ∀ q : ℝ, (q : ℂ) ∈ closure (fwdHull (Strip.extPath fun u => w u + x₂) t) →
      ((q - x₂ : ℝ) : ℂ) ∈ closure (fwdHull W t) := fun q hq => by
    rw [hcl] at hq
    obtain ⟨z, hz, hzq⟩ := hq
    have : z = ((q - x₂ : ℝ) : ℂ) := by push_cast; rw [← hzq]; ring
    rw [← this]
    exact hz
  have hc' : ((c - x₂ : ℝ) : ℂ) ∉ closure (fwdHull W t) := fun hm => h (by
    rw [hcl]
    exact ⟨_, hm, by push_cast; ring⟩)
  rintro (hr' | hr')
  · exact notMem_closure_fwdHull_of_le hW hW0 t.coe_nonneg (by linarith) hc' (by linarith) (hmem r hr')
  · have := congrArg Complex.re (show (r : ℂ) = x₂ from hr')
    simp only [Complex.ofReal_re] at this
    linarith

/-- **Exhaustion by the G3 segment family from mark-free prefixes.** For the source `−y` and the ordinary mark
`x − y` (`y < x < 0`): if at times `s < ζ₁`, `t < ζ₂` the prefixes `closure K₁(s) ∪ {0}` and
`closure K₂(t) ∪ {−y}` (large curve shifted to `−y`, `w₂ 0 = 0`) are disjoint and avoid the mark, some member `m` of
the segment family has `s ≤ S₁ m` and `t ≤ S₂ m` — the hypotheses of A1-COMMON's `exists_rect_le`. -/
theorem exists_rect_leG_of_marks {x y : ℝ} (hyx : y < x) (hx : x < 0) {w₁ w₂ : ℝ≥0 → ℝ} {ζ₁ ζ₂ : ℝ≥0∞}
    (hw₁ : ContinuousOn w₁ {t | (t : ℝ≥0∞) < ζ₁}) (hw₂ : ContinuousOn w₂ {t | (t : ℝ≥0∞) < ζ₂}) (hw₂0 : w₂ 0 = 0)
    {s t : ℝ≥0} (hs : (s : ℝ≥0∞) < ζ₁) (ht : (t : ℝ≥0∞) < ζ₂)
    (hdisj : Disjoint (closure (fwdHull (Strip.extPath w₁) s) ∪ {0})
      (closure (fwdHull (Strip.extPath fun u => w₂ u + -y) t) ∪ {((-y : ℝ) : ℂ)}))
    (hp : ∀ j, (((![x - y] : Fin 1 → ℝ) j : ℝ) : ℂ) ∉ (closure (fwdHull (Strip.extPath w₁) s) ∪ {0}) ∪
      (closure (fwdHull (Strip.extPath fun u => w₂ u + -y) t) ∪ {((-y : ℝ) : ℂ)})) :
    ∃ m : ℕ, s ≤ lifeExit w₁ ζ₁ (cofGH₁ (-y) (x - y) ![x - y] m) (cofGN (-y) (x - y) ![x - y] m) ∧
      t ≤ lifeExit (fun u => w₂ u + -y) ζ₂ (cofGH₂ (-y) (x - y) ![x - y] m) (cofGN (-y) (x - y) ![x - y] m) := by
  have hp0 := hp 0
  simp only [Matrix.cons_val_zero] at hp0
  have hq₁ : ((x - y : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath w₁) s) ∪ {0} := fun h => hp0 (Or.inl h)
  have hq₂ : ((x - y : ℝ) : ℂ) ∉ closure (fwdHull (Strip.extPath fun u => w₂ u + -y) t) :=
    fun h => hp0 (Or.inr (Or.inl h))
  exact exists_rect_leG (by linarith) (by linarith) hw₁ hw₂ hs ht hdisj hp
    (fun r hr => notMem_closure_fwdHull_shift_of_le hw₂ hw₂0 ht (by linarith) hq₂ hr.2) hq₁

end InteractingSLE.ZhanGT4.A1Asm

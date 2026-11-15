/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux22StripHit
import InteractingSLE.Spec.Sec5.Aux22StripAe
import InteractingSLE.Spec.Sec7.ContinuityProb9Trace
import InteractingSLE.Spec.Sec2.CriticalLifetime

/-!
# Aux. lemma 22 in the strip, step 5: the first contact with a span, for a chordal word

Packet PROVE-SEC5-L (specification §4.1, Aux. lemma 22 and its proof, pp. 113–115). The chordal form of the proof of
Aux. lemma 22: an integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, with all marks off the source
(`xL < 0 < xR`, distinct positions), whose right marks `x_{j'} < x_k` (consecutive, `k = LP.retargetIdx (j' + 1) m`)
bound the span `(x_{j'}, x_k)`. After the change of target `ψ(z) = z/(x_k − z)` the span becomes `(e, ∞)`,
`e = ψ(x_{j'})`, and after reflection and dilation by `e²` the upper boundary `(−∞, −1)` of an R36 strip word. If that
strip word satisfies Zhan's hypotheses (lower prefix sums at least `κ/2 − 2`, `|q₊ − q₋| < 2`; stated on LP9's
transformed word), then (**`ae_exists_hit_of_retarget`**) almost surely every generating trace of the original driver
reaches a point of `(x_{j'}, x_k)` at a finite time `t ≤ ζ`, and never visits `ℝ \ {0}` before `t`.

This is the source's argument: the map (UC11) "maps the strip onto the strip of height `π`, with the seed at zero and
`I` as the upper boundary"; Aux. lemma 21 (here Zhan's strip endpoint theorem, the case of one height on `I`) "gives an
actual limit at a finite point of the new upper boundary"; noncollision of the new lower marks keeps the old boundary
arcs off the trace; "the actual endpoint pulls back as asserted".
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec5

namespace Aux22Strip

open Zhan.Retarget Strip

/-! ### `ψ` on the real line -/

theorem targetChangeReal_pos {xk x : ℝ} (hx : 0 < x) (hxk : x < xk) : 0 < Sec7.targetChangeReal xk x :=
  div_pos hx (sub_pos.2 hxk)

theorem targetChangeReal_neg_of_neg {xk x : ℝ} (hx : x < 0) (hxk : 0 < xk) : Sec7.targetChangeReal xk x < 0 :=
  div_neg_of_neg_of_pos hx (by linarith)

theorem targetChangeReal_neg_of_gt {xk x : ℝ} (hxk : 0 < xk) (hx : xk < x) : Sec7.targetChangeReal xk x < 0 :=
  div_neg_of_pos_of_neg (by linarith) (by linarith)

/-- `ψ⁻¹` maps `(ψ(x'), ∞)` into `(x', x_k)`. -/
theorem mem_Ioo_targetChangeInv {xk x' y : ℝ} (hx' : 0 < x') (hx'k : x' < xk)
    (hy : Sec7.targetChangeReal xk x' < y) : x' < xk * y / (1 + y) ∧ xk * y / (1 + y) < xk := by
  have hd : 0 < xk - x' := sub_pos.2 hx'k
  have he : 0 < x' / (xk - x') := div_pos hx' hd
  have hy0 : 0 < y := he.trans hy
  have h1y : 0 < 1 + y := by linarith
  have hy' : x' < y * (xk - x') := by
    have := (div_lt_iff₀ hd).1 hy
    linarith
  constructor
  · rw [lt_div_iff₀ h1y]; nlinarith
  · rw [div_lt_iff₀ h1y]; nlinarith [hx'.trans hx'k]

/-! ### The theorem -/

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + 1 + m) → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin (j + 1 + 1 + m) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The right mark before the target, `x_{j'}`. -/
abbrev spanLeft (xR : Fin (j + 1 + 1 + m) → ℝ) : ℝ := xR (Fin.castAdd m (Fin.castSucc (Fin.last j)))

/-- **The first contact with the span `(x_{j'}, x_k)`** (chordal form of Aux. lemma 22, `0 < κ ≤ 4`). -/
theorem ae_exists_hit_of_retarget (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hD : LP.IsDistinctForceWord xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ i, 0 < xR i)
    (hpre : HasStripPrefixSums κ (Fin.init (LP.retargetρR ρR)) (LP.retargetρL κ ρL ρR))
    (hq : |chargePlus κ (Fin.init (LP.retargetρR ρR)) (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR (Fin.last j)) -
      chargeMinus (Fin.init (LP.retargetρR ρR)) (LP.retargetρR ρR (Fin.last j))| < 2) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η s ≠ z) ∧
        ∃ x : ℝ, spanLeft xR < x ∧ x < LP.retargetPos xR ∧ η t = x := by
  have hj : 1 ≤ j + 1 := Nat.le_add_left 1 j
  have hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR := fun h => by
    rcases exists_eq_of_thresholdCondition h with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact (hxL i).ne hi
    · exact (hxR i).ne' hi
  obtain ⟨𝓖, B', gW, gL, gR, ζG, hG, hag⟩ := exists_retarget_integrated hκ hD hj hE hseed
  have hDT := LP.isDistinctForceWord_retarget hD hj
  have hxk : spanLeft xR < LP.retargetPos xR := hD.2.2 (by
    rw [Fin.lt_def]; simp [LP.retargetIdx])
  have he : 0 < LP.retargetXR xR (Fin.last j) := targetChangeReal_pos (hxR _) hxk
  have hR0 : ∀ k : Fin j, 0 < LP.retargetXR xR k.castSucc := fun k =>
    targetChangeReal_pos (hxR _) (hD.2.2 (by rw [Fin.lt_def]; simp [LP.retargetIdx]))
  have hL0 : ∀ i, LP.retargetXL xL xR i < 0 := by
    intro i
    have hxk0 : 0 < LP.retargetPos xR := (hxR _)
    refine Fin.addCases (fun i => ?_) (fun l => ?_) i
    · simp only [LP.retargetXL, Fin.append_left]
      exact targetChangeReal_neg_of_neg (hxL i) hxk0
    · simp only [LP.retargetXL, Fin.append_right]
      refine Fin.cases ?_ (fun l => ?_) l
      · simp
      · simp only [Fin.cons_succ]
        exact targetChangeReal_neg_of_gt hxk0 (hD.2.2 (by rw [Fin.lt_def]; simp [LP.retargetIdx]; omega))
  have hstrip := ae_exists_stripEnd_of_integrated hκ hκ4 hG he hDT.2.2 hR0 hDT.2.1 hL0 hpre hq
  have hfst := Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)
  refine Sec7.ae_of_ae_prod_fst (Φ := fun ω => ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
      ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ (∀ s : ℝ≥0, s < t → ∀ z : ℝ, z ≠ 0 → η s ≠ z) ∧
        ∃ x : ℝ, spanLeft xR < x ∧ x < LP.retargetPos xR ∧ η t = x) ?_
  filter_upwards [hag, hstrip, hfst.ae hE.2.2.2.2, hfst.ae (hE.ae_tendsto_threshold hκ)] with p hagp hsp hpath hlim
  intro η hη
  obtain ⟨S, ηG, y, hS0, hey, -, hgenG, havoid, hconv⟩ := hsp
  have hgen : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < retargetHorizon xR (fun t => W t p.1) (fun i t => VR i t p.1) (ζ p.1) →
      IsGeneratingTrace (newW xR (fun t => W t p.1) (fun i t => VR i t p.1)) u ηG := fun u hu hut =>
    Sec7.IsGeneratingTrace.congr_lt (hgenG u hu) fun t ht => (hagp.2 t (ht.trans hut)).1
  have hcontG : ∀ u : ℝ≥0, u < S → ContinuousAt ηG u := by
    intro u hu
    obtain ⟨u', huu', hu'S⟩ := exists_between hu
    have hopen : IsOpen {r : ℝ≥0 | (r : ℝ≥0∞) < u'} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact (hgenG u' hu'S).2.1.continuousAt (Filter.mem_of_superset (hopen.mem_nhds (ENNReal.coe_lt_coe.2 huu'))
      fun r hr => show (r : ℝ≥0∞) ≤ u' from le_of_lt hr)
  have hG0 : ηG 0 = 0 := (hgenG 0 hS0).1
  have hy : y ≠ -1 := by linarith
  obtain ⟨t, htζ, havt, hηt⟩ := exists_hit_of_retarget hpath hD hj hxL hxR hlim hη hS0 hG0 hy hgen hcontG havoid hconv
  have hmem := mem_Ioo_targetChangeInv (hxR _) hxk hey
  refine ⟨t, htζ, havt, _, hmem.1, hmem.2, ?_⟩
  rw [hηt, targetChangeInv_ofReal]

end Aux22Strip

end Sec5

end InteractingSLE

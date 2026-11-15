/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop55Half
import InteractingSLE.Spec.Restart.ChartGauss
import InteractingSLE.Spec.Restart.ChartSpace
import InteractingSLE.Spec.Supplement.RLCFAvgCode

/-!
# Aux. lemma 94's complete conditional reference paths in the exact two-height sector

Packet PROVE-RLC-I. Source: Aux. lemma 94 (specification p. 315, `source/spec/p289-336.md#aux-94`), its hypothesis
(TH1)–(TH2) and the first claim of its proof, "Complete conditional reference paths" (pp. 316): in the first-contact
chart the conditional field has exactly the two boundary values

  `c_L = −λ − θ₂χ` on `(−∞, 0)`, `c_R = λ − θ₁χ` on `(0, ∞)`                                       (TH2)

"with no other surviving boundary-height jumps"; the angle-`θ₁` and angle-`θ₂` paths from `0` have seed weights `(d; 0)`
and `(0; d)`, `d = (θ₂ − θ₁)χ/λ`, are complete, continuous, proper and simple, every noninitial point lies in `ℍ`, and
"if `θ₁ < θ₂`, apply the earlier half-plane assertion of Proposition 5.5. For the heights (TH2), its angular bounds are
exactly `θ₁` and `θ₂ + π`, so its hypothesis holds […] the complete higher-angle path lies to the left of the complete
lower-angle path." This is the part of Aux. lemma 94 that the proof of Lemma G2 uses (supplement p. 491: "Its two
complete conditional continuations have weights `(d; 0)` and `(0; d)` and are ordered proper interior curves, by
Proposition 5.5 as used in that auxiliary lemma"). The later-contact restart (the remaining conclusions of Lemma 7.9
in this sector, Claims 2–4 of the proof) is not needed by G2 and is not formalized here.

In Lean the (TH2) mean is the word `twoHeightWord κ θ₁ θ₂` (one jump at `0`). A restart datum is identified with it
only through its harmonic mean, so the statements are made for every word in the Borel class `twoHeightSet` of sorted
words whose mean is the (TH2) mean: such a word is the (TH2) datum off its jump candidates, with a genuine jump at `0`.

## Main results

* `twoHeightWord`, `twoHeightWord_mean`, `twoHeightSet`, `measurableSet_twoHeightSet`, `eqOn_mean_of_mem_twoHeightSet`;
* `isGFFWithBoundaryData_prop74Data_of_mem`, `isFlowLine_prop74Data_of_mem`: a datum of the class is the
  `prop74Data (λ + θ₂χ) (λ − θ₁χ)` datum of Proposition 5.5 for the GFF and flow-line predicates;
* **`aux94_twoHeight_reference`**: Aux. lemma 94's complete conditional reference paths with Proposition 5.5's order
  (named input `Sec7.Lemma71H.Prop55HalfPlaneStatement`);
* `twoHeightGood`, `measurableSet_twoHeightGood`, `mem_twoHeightGood`, `twoHeightGood_spec`: the Borel event of the
  canonical restart space carrying these path properties (for the transfer through a disintegrating kernel).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Real

open QuantumZipper (H chiC)

universe v

namespace InteractingSLE

namespace RLC

open Restart
open Sec7 (prop74Data isPiecewiseConstant_prop74Data)
open Sec5.Prop55Half (IsSeedProper orderCodeSet)
open Theorem15D5 (encC ratPt)

/-! ### The exact two-height word -/

/-- The two-height word with heights `hL` on `(−∞, 0)` and `hR` on `(0, ∞)`. -/
def twoHeightWordOf (hL hR : ℝ) : BoundaryWord :=
  (1, fun _ => 0, fun i => if i = 0 then hL else hR)

/-- **The exact two-height word (TH2)** of Aux. lemma 94: `c_L = −λ − θ₂χ` on `(−∞, 0)`, `c_R = λ − θ₁χ` on
`(0, ∞)`. -/
def twoHeightWord (κ θ₁ θ₂ : ℝ) : BoundaryWord :=
  twoHeightWordOf (-sleLambda κ - θ₂ * chiC κ) (sleLambda κ - θ₁ * chiC κ)

/-- The lower value `a` of the `prop74Data a b` form of (TH2): `−a = −λ − θ₂χ`. -/
def twoHeightA (κ θ₂ : ℝ) : ℝ := sleLambda κ + θ₂ * chiC κ

/-- The upper value `b` of the `prop74Data a b` form of (TH2). -/
def twoHeightB (κ θ₁ : ℝ) : ℝ := sleLambda κ - θ₁ * chiC κ

theorem twoHeightWordOf_isSorted (hL hR : ℝ) : (twoHeightWordOf hL hR).IsSorted := by
  intro i j _ _
  exact le_rfl

theorem twoHeightWordOf_jumps (hL hR : ℝ) : (twoHeightWordOf hL hR).jumps = {0} := by
  ext y
  simp [BoundaryWord.jumps, twoHeightWordOf]

theorem twoHeightWordOf_mean (hL hR : ℝ) (z : ℂ) :
    (twoHeightWordOf hL hR).mean z = hR + (hL - hR) * (Complex.arg z / Real.pi) := by
  simp [BoundaryWord.mean, twoHeightWordOf]

theorem twoHeightWordOf_fn_of_neg (hL hR : ℝ) {y : ℝ} (hy : y < 0) : (twoHeightWordOf hL hR).fn y = hL := by
  simp [BoundaryWord.fn, BoundaryWord.index, twoHeightWordOf, not_lt.2 hy.le]

theorem twoHeightWordOf_fn_of_pos (hL hR : ℝ) {y : ℝ} (hy : 0 < y) : (twoHeightWordOf hL hR).fn y = hR := by
  simp [BoundaryWord.fn, BoundaryWord.index, twoHeightWordOf, hy]

theorem twoHeightWord_fn {κ θ₁ θ₂ y : ℝ} (hy : y ≠ 0) :
    (twoHeightWord κ θ₁ θ₂).fn y = prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁) y := by
  rcases lt_or_gt_of_ne hy with h | h
  · rw [twoHeightWord, twoHeightWordOf_fn_of_neg _ _ h]
    simp only [prop74Data, h, ↓reduceIte, twoHeightA]
    ring
  · rw [twoHeightWord, twoHeightWordOf_fn_of_pos _ _ h]
    simp only [prop74Data, not_lt.2 h.le, ↓reduceIte, twoHeightB]

/-! ### The Borel class of words with the (TH2) mean -/

/-- **The words with the (TH2) mean**: sorted words whose explicit harmonic mean agrees with the (TH2) mean at every
rational point of `ℍ` (hence on `ℍ`, `eqOn_mean_of_mem_twoHeightSet`). -/
def twoHeightSet (κ θ₁ θ₂ : ℝ) : Set BoundaryWord :=
  {c | c.IsSorted ∧ ∀ q : ℚ × ℚ, (0 : ℝ) < q.2 → c.mean (ratPt q) = (twoHeightWord κ θ₁ θ₂).mean (ratPt q)}

theorem measurable_isSorted : Measurable fun c : BoundaryWord => c.IsSorted := by
  refine Measurable.forall fun i => Measurable.forall fun j => measurable_const.imp ?_
  refine Measurable.imp ?_ ?_
  · exact measurableSet_setOfPred.mp (measurableSet_lt measurable_const measurable_fst)
  · exact measurableSet_setOfPred.mp (measurableSet_le ((measurable_pi_apply i).comp (measurable_fst.comp
      measurable_snd)) ((measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)))

theorem measurable_mean_apply (z : ℂ) : Measurable fun c : BoundaryWord => c.mean z :=
  BoundaryWord.measurable_mean.comp (measurable_id.prodMk measurable_const)

theorem measurableSet_twoHeightSet (κ θ₁ θ₂ : ℝ) : MeasurableSet (twoHeightSet κ θ₁ θ₂) := by
  refine measurableSet_setOfPred.mpr (measurable_isSorted.and ?_)
  refine Measurable.forall fun q => measurable_const.imp ?_
  exact measurableSet_setOfPred.mp (measurableSet_eq_fun (measurable_mean_apply _) measurable_const)

theorem continuousOn_mean_H {c : BoundaryWord} (hc : c.IsSorted) : ContinuousOn c.mean H := fun z hz =>
  ((c.isBoundedHarmonicExtension_mean hc).1 z hz).1.continuousAt.continuousWithinAt

/-- The rational points of `ℍ` are dense in `ℍ`. -/
theorem H_subset_closure_ratPt : H ⊆ closure (ratPt '' {q : ℚ × ℚ | (0 : ℝ) < q.2}) := by
  intro z hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hz' : (0 : ℝ) < z.im := hz
  obtain ⟨q, hq⟩ := Theorem15D5.exists_ratPt_dist_lt z (lt_min hε hz')
  refine ⟨ratPt q, ⟨q, ?_, rfl⟩, ?_⟩
  · have h1 : |(ratPt q - z).im| ≤ ‖ratPt q - z‖ := Complex.abs_im_le_norm _
    rw [← Complex.dist_eq] at h1
    have h2 : (ratPt q).im = (q.2 : ℝ) := rfl
    have h3 := lt_of_le_of_lt h1 (lt_of_lt_of_le hq (min_le_right _ _))
    rw [Complex.sub_im, h2, abs_lt] at h3
    show (0 : ℝ) < (q.2 : ℝ)
    linarith [h3.1]
  · rw [dist_comm]
    exact lt_of_lt_of_le hq (min_le_left _ _)

theorem eqOn_mean_of_mem_twoHeightSet {κ θ₁ θ₂ : ℝ} {c : BoundaryWord} (hc : c ∈ twoHeightSet κ θ₁ θ₂) :
    EqOn c.mean (twoHeightWord κ θ₁ θ₂).mean H := by
  refine EqOn.of_subset_closure (s := ratPt '' {q : ℚ × ℚ | (0 : ℝ) < q.2}) ?_ (continuousOn_mean_H hc.1)
    (continuousOn_mean_H (twoHeightWordOf_isSorted _ _)) ?_ H_subset_closure_ratPt
  · rintro _ ⟨q, hq, rfl⟩
    exact hc.2 q hq
  · rintro _ ⟨q, hq, rfl⟩
    exact hq

theorem mem_twoHeightSet_of_eqOn {κ θ₁ θ₂ : ℝ} {c : BoundaryWord} (hc : c.IsSorted)
    (h : EqOn c.mean (twoHeightWord κ θ₁ θ₂).mean H) : c ∈ twoHeightSet κ θ₁ θ₂ :=
  ⟨hc, fun q hq => h (show (0 : ℝ) < (ratPt q).im from hq)⟩

/-! ### A word of the class is the (TH2) datum -/

/-- Off its jump candidates, piecewise-constant data have equal one-sided limits. -/
theorem leftLim_eq_rightLim_of_notMem' {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    {y : ℝ} (hy : y ∉ J) :
    PiecewiseConstantBoundaryData.leftLim b y = PiecewiseConstantBoundaryData.rightLim b y := by
  have hc := hb y hy
  have h1 : Tendsto b (𝓝[<] y) (𝓝 (b y)) :=
    tendsto_const_nhds.congr' ((hc.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  have h2 : Tendsto b (𝓝[>] y) (𝓝 (b y)) :=
    tendsto_const_nhds.congr' ((hc.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.symm)
  show limUnder (𝓝[<] y) b = limUnder (𝓝[>] y) b
  rw [h1.limUnder_eq, h2.limUnder_eq]

theorem leftLim_prop74Data_zero (a b : ℝ) : PiecewiseConstantBoundaryData.leftLim (prop74Data a b) 0 = -a := by
  have h : Tendsto (prop74Data a b) (𝓝[<] 0) (𝓝 (-a)) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z (hz : z < 0) => by
      simp [prop74Data, hz])
  exact h.limUnder_eq

theorem rightLim_prop74Data_zero (a b : ℝ) : PiecewiseConstantBoundaryData.rightLim (prop74Data a b) 0 = b := by
  have h : Tendsto (prop74Data a b) (𝓝[>] 0) (𝓝 b) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun z (hz : 0 < z) => by
      simp [prop74Data, not_lt.2 hz.le])
  exact h.limUnder_eq

/-- The two (TH2) heights differ: `−λ − θ₂χ < λ − θ₁χ` for `θ₁ < θ₂`. -/
theorem twoHeight_ne {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) :
    -twoHeightA κ θ₂ ≠ twoHeightB κ θ₁ := by
  have hχ := Sec4.chiC_pos hκ hκ4
  have hlam := Sec4.sleLambda_pos hκ
  have h12 : θ₁ * chiC κ < θ₂ * chiC κ := mul_lt_mul_of_pos_right hθ hχ
  unfold twoHeightA twoHeightB
  intro h
  linarith

theorem nhdsWithin_H_ofReal_neBot (y : ℝ) : (𝓝[H] (y : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(y : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · show (0 : ℝ) < ((y : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    linarith
  · rw [Complex.dist_eq]
    simp only [sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (half_pos hε)]
    linarith

/-- **A word of the class is the (TH2) datum off its jump candidates**: the boundary limits of the two equal means. -/
theorem fn_eq_of_mem_twoHeightSet {κ θ₁ θ₂ : ℝ} {c : BoundaryWord} (hc : c ∈ twoHeightSet κ θ₁ θ₂) {y : ℝ}
    (hy : y ∉ c.jumps) (hy0 : y ≠ 0) : c.fn y = prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁) y := by
  have heq := eqOn_mean_of_mem_twoHeightSet hc
  have t₁ := (c.isBoundedHarmonicExtension_mean hc.1).2.2 y (by exact_mod_cast hy)
  have t₂ := ((twoHeightWord κ θ₁ θ₂).isBoundedHarmonicExtension_mean (twoHeightWordOf_isSorted _ _)).2.2 y
    (by rw [twoHeightWord, twoHeightWordOf_jumps]; simpa using hy0)
  have t₁' : Tendsto (twoHeightWord κ θ₁ θ₂).mean (𝓝[H] (y : ℂ)) (𝓝 (c.fn y)) :=
    t₁.congr' (eventually_nhdsWithin_of_forall fun z hz => heq hz)
  have := nhdsWithin_H_ofReal_neBot y
  rw [tendsto_nhds_unique t₁' t₂, twoHeightWord_fn hy0]

/-- **A word of the class has a genuine jump at `0`.** -/
theorem zero_mem_jumps_of_mem_twoHeightSet {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    {c : BoundaryWord} (hc : c ∈ twoHeightSet κ θ₁ θ₂) : (0 : ℝ) ∈ c.jumps := by
  by_contra h0
  have hfn : ∀ y ∉ insert (0 : ℝ) c.jumps, c.fn y = prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁) y := by
    intro y hy
    rw [Finset.mem_insert, not_or] at hy
    exact fn_eq_of_mem_twoHeightSet hc hy.2 hy.1
  have hL := congrFun (leftLim_congr hfn) 0
  have hR := congrFun (rightLim_congr hfn) 0
  have hLR := leftLim_eq_rightLim_of_notMem' c.isPiecewiseConstantBoundaryData h0
  rw [hL, hR, leftLim_prop74Data_zero, rightLim_prop74Data_zero] at hLR
  exact twoHeight_ne hκ hκ4 hθ hLR

/-- Off the jump candidates of a word of the class, the word is the (TH2) datum. -/
theorem fn_eq_of_mem_twoHeightSet' {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {c : BoundaryWord}
    (hc : c ∈ twoHeightSet κ θ₁ θ₂) : ∀ y ∉ c.jumps, c.fn y = prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁) y :=
  fun _ hy => fn_eq_of_mem_twoHeightSet hc hy fun h => hy (h ▸ zero_mem_jumps_of_mem_twoHeightSet hκ hκ4 hθ hc)

/-- **The GFF predicate for a word of the class is the (TH2) one.** -/
theorem isGFFWithBoundaryData_prop74Data_of_mem {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    {c : BoundaryWord} (hc : c ∈ twoHeightSet κ θ₁ θ₂) {S : Type*} [MeasurableSpace S] {Q : Measure S}
    {F : S → LQGMetric.DistOn upperHalfPlaneOpens} (hF : IsGFFWithBoundaryData Q F c.fn c.jumps) :
    IsGFFWithBoundaryData Q F (prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁)) (({0} : Finset ℝ) : Set ℝ) := by
  have h0 := zero_mem_jumps_of_mem_twoHeightSet hκ hκ4 hθ hc
  have hfn := fn_eq_of_mem_twoHeightSet' hκ hκ4 hθ hc
  refine ⟨hF.1, fun u hu => hF.2 u ⟨hu.1, hu.2.1, fun x hx => ?_⟩⟩
  have hx' : x ∉ c.jumps := by exact_mod_cast hx
  rw [hfn x hx']
  refine hu.2.2 x fun hx0 => hx' ?_
  rw [Finset.coe_singleton, mem_singleton_iff] at hx0
  exact hx0 ▸ h0

/-- **The flow-line predicate for a word of the class is the (TH2) one.** -/
theorem isFlowLine_prop74Data_of_mem {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    {c : BoundaryWord} (hc : c ∈ twoHeightSet κ θ₁ θ₂) {θ : ℝ} {S : Type*} [MeasurableSpace S] {Q : Measure S}
    {F : S → LQGMetric.DistOn upperHalfPlaneOpens} {γ : S → ℝ≥0 → ℂ} {U : S → ℝ≥0∞}
    (hγ : IsFlowLine κ c.fn c.jumps 0 θ Q F γ U) :
    IsFlowLine κ (prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁)) {0} 0 θ Q F γ U := by
  have h0 := zero_mem_jumps_of_mem_twoHeightSet hκ hκ4 hθ hc
  have hfn : ∀ y ∉ c.jumps, prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁) y = c.fn y :=
    fun y hy => (fn_eq_of_mem_twoHeightSet' hκ hκ4 hθ hc y hy).symm
  have hL := leftLim_congr hfn
  have hR := rightLim_congr hfn
  have hJ : PiecewiseConstantBoundaryData.jumpSet (prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁)) {0} =
      PiecewiseConstantBoundaryData.jumpSet c.fn c.jumps := by
    ext y
    simp only [PiecewiseConstantBoundaryData.jumpSet, Finset.mem_filter, Finset.mem_singleton]
    rw [hL, hR]
    constructor
    · rintro ⟨rfl, hne⟩
      exact ⟨h0, hne⟩
    · rintro ⟨-, hne⟩
      refine ⟨?_, hne⟩
      by_contra hy0
      rw [← hL, ← hR] at hne
      exact hne (leftLim_eq_rightLim_of_notMem' (isPiecewiseConstant_prop74Data _ _)
        (by simpa using hy0))
  exact (isFlowLine_congr hJ hL hR).2 hγ

/-! ### Aux. lemma 94: the complete conditional reference paths and their order -/

/-- **Aux. lemma 94, "Complete conditional reference paths", with Proposition 5.5's order** (specification
pp. 315–316; supplement p. 491, proof of Lemma G2). For `0 < κ < 4`, `θ₁ < θ₂`, a GFF on `ℍ` whose datum is a word with
the (TH2) mean and its angle-`θ₁`, angle-`θ₂` flow lines from `0`: almost surely both are complete (infinite
lifetimes), simple proper curves from `0` whose noninitial points lie in `ℍ` (seed weights `(d; 0)`, `(0; d)` with
`d > 0`, Remark 4.1's regime), and the higher-angle path lies in the closed left side of the lower-angle one
(Proposition 5.5 for the heights (TH2): its angular bounds are `θ₁` and `θ₂ + π`). Named input: the half-plane
Proposition 5.5 (`Sec7.Lemma71H.Prop55HalfPlaneStatement`). -/
theorem aux94_twoHeight_reference (h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{v}) {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ : θ₁ < θ₂) {c : BoundaryWord} (hc : c ∈ twoHeightSet κ θ₁ θ₂) {S : Type v}
    [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q] (F : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (γ₁ γ₂ : S → ℝ≥0 → ℂ) (U₁ U₂ : S → ℝ≥0∞) (hF : IsGFFWithBoundaryData Q F c.fn c.jumps)
    (h₁ : IsFlowLine κ c.fn c.jumps 0 θ₁ Q F γ₁ U₁) (h₂ : IsFlowLine κ c.fn c.jumps 0 θ₂ Q F γ₂ U₂) :
    ∀ᵐ s ∂Q, U₁ s = ⊤ ∧ U₂ s = ⊤ ∧ IsSeedProper (γ₁ s) ∧ IsSeedProper (γ₂ s) ∧
      range (γ₂ s) ⊆ closedLeftSide (γ₁ s) := by
  have hF' := isGFFWithBoundaryData_prop74Data_of_mem hκ hκ4 hθ hc hF
  have h₁' := isFlowLine_prop74Data_of_mem hκ hκ4 hθ hc h₁
  have h₂' := isFlowLine_prop74Data_of_mem hκ hκ4 hθ hc h₂
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 ≤ π * chiC κ := mul_nonneg Real.pi_pos.le hχ.le
  have hb : sleLambda κ - θ₁ * chiC κ ≤ twoHeightB κ θ₁ := le_rfl
  have ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ twoHeightA κ θ₂ := by
    unfold twoHeightA; linarith
  have hb41 : sleLambda κ - π * chiC κ - θ₁ * chiC κ ≤ twoHeightB κ θ₁ := by
    unfold twoHeightB; linarith
  have hbpc := isPiecewiseConstant_prop74Data (twoHeightA κ θ₂) (twoHeightB κ θ₁)
  obtain ⟨hL₁, hR₁⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 le_rfl hθ.le ha hb41
  obtain ⟨hL₂, hR₂⟩ := Sec7.Lemma71G.prop74Data_remark41 hκ hκ4 hθ.le le_rfl ha hb41
  filter_upwards [Sec5.Prop55Half.IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL₁ hR₁ h₁',
    Sec5.Prop55Half.IsFlowLine.ae_isSeedProper hκ hκ4.le hbpc hL₂ hR₂ h₂',
    h55 κ hκ hκ4 _ _ θ₁ θ₂ hθ hb ha Q F hF' γ₁ γ₂ U₁ U₂ h₁' h₂'] with s r₁ r₂ ho
  exact ⟨r₁.1, r₂.1, r₁.2, r₂.2, ho r₁.1 r₂.1⟩

/-! ### The Borel event of the restart space -/

/-- The closed lower half-plane. -/
def closedLowerHalf : Set ℂ := {z | z.im ≤ 0}

theorem isClosed_closedLowerHalf : IsClosed closedLowerHalf := isClosed_le Complex.continuous_im continuous_const

theorem closedLowerHalf_nonempty : closedLowerHalf.Nonempty := ⟨0, show (0 : ℂ).im ≤ 0 by simp⟩

theorem notMem_closedLowerHalf_iff {z : ℂ} : z ∉ closedLowerHalf ↔ z ∈ H := by
  show ¬ z.im ≤ 0 ↔ 0 < z.im
  exact not_le

/-- **The Borel event of Aux. lemma 94's conclusion on the canonical restart space**: both continuations have infinite
lifetime and start at `0`, the first is injective, both are in `ℍ` at every positive time (on every `[0, n]`), and the
codes of the two continuations are in the Borel order set (the first tends to `∞`, the second lies in its closed left
side). -/
def twoHeightGood (E : Type*) [MeasurableSpace E] : Set (RestartSpace × E) :=
  {s | s.1.life₁ = ⊤ ∧ s.1.life₂ = ⊤ ∧ s.1.path₁ 0 = 0 ∧ s.1.path₂ 0 = 0 ∧ Theorem15D5.InjC (encC s.1.path₁) ∧
    (∀ n : ℕ, AvoidC (encC s.1.path₁) n closedLowerHalf) ∧ (∀ n : ℕ, AvoidC (encC s.1.path₂) n closedLowerHalf) ∧
    (encC s.1.path₁, encC s.1.path₂) ∈ orderCodeSet}

theorem measurableSet_twoHeightGood (E : Type*) [MeasurableSpace E] : MeasurableSet (twoHeightGood E) := by
  have hco := isRestartCoordinates_restartSpace
  have hp₁ : ∀ t, Measurable fun s : RestartSpace × E => s.1.path₁ t := fun t =>
    (hco.2.2.2.1 t).comp measurable_fst
  have hp₂ : ∀ t, Measurable fun s : RestartSpace × E => s.1.path₂ t := fun t =>
    (hco.2.2.2.2.1 t).comp measurable_fst
  have hl₁ : Measurable fun s : RestartSpace × E => s.1.life₁ := hco.2.1.comp measurable_fst
  have hl₂ : Measurable fun s : RestartSpace × E => s.1.life₂ := hco.2.2.1.comp measurable_fst
  have he₁ : Measurable fun s : RestartSpace × E => encC s.1.path₁ := Sec5.Prop55Half.measurable_encC_comp hp₁
  have he₂ : Measurable fun s : RestartSpace × E => encC s.1.path₂ := Sec5.Prop55Half.measurable_encC_comp hp₂
  refine measurableSet_setOfPred.mpr ?_
  refine (measurableSet_setOfPred.mp (measurableSet_eq_fun hl₁ measurable_const)).and <|
    (measurableSet_setOfPred.mp (measurableSet_eq_fun hl₂ measurable_const)).and <|
    (measurableSet_setOfPred.mp (measurableSet_eq_fun (hp₁ 0) measurable_const)).and <|
    (measurableSet_setOfPred.mp (measurableSet_eq_fun (hp₂ 0) measurable_const)).and <|
    (Theorem15D5.measurable_injC.comp he₁).and <|
    (Measurable.forall fun n : ℕ => (measurable_avoidC (n : ℝ≥0) closedLowerHalf).comp he₁).and <|
    (Measurable.forall fun n : ℕ => (measurable_avoidC (n : ℝ≥0) closedLowerHalf).comp he₂).and ?_
  exact measurableSet_setOfPred.mp ((he₁.prodMk he₂) Sec5.Prop55Half.measurableSet_orderCodeSet)

/-- A continuation of infinite lifetime is continuous. -/
theorem continuous_decPath_of_top {p : (Sec2.Assembly.PCode × Sec2.Assembly.PCode) × ℝ≥0∞} (hp : p.2 = ⊤) :
    Continuous (decPath p) := by
  have h := continuousOn_decPath p
  rw [hp] at h
  simp only [le_top, ofPred_true] at h
  exact continuousOn_univ.1 h

/-- Being in `ℍ` at positive times through the codes on `[0, n]`. -/
theorem forall_avoidC_iff {g : ℝ≥0 → ℂ} (hg : Continuous g) :
    (∀ n : ℕ, AvoidC (encC g) n closedLowerHalf) ↔ ∀ t : ℝ≥0, 0 < t → g t ∈ H := by
  constructor
  · intro h t ht
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have := (avoidC_encC_iff hg.continuousOn isClosed_closedLowerHalf closedLowerHalf_nonempty).1 (h n) t ht hn
    exact notMem_closedLowerHalf_iff.1 this
  · intro h n
    exact (avoidC_encC_iff hg.continuousOn isClosed_closedLowerHalf closedLowerHalf_nonempty).2 fun t ht _ =>
      notMem_closedLowerHalf_iff.2 (h t ht)

/-- **Aux. lemma 94's conclusion puts a restart point in the Borel event.** -/
theorem mem_twoHeightGood {E : Type*} [MeasurableSpace E] {s : RestartSpace × E} (hl₁ : s.1.life₁ = ⊤)
    (hl₂ : s.1.life₂ = ⊤) (hp₁ : IsSeedProper s.1.path₁) (hp₂ : IsSeedProper s.1.path₂)
    (ho : range s.1.path₂ ⊆ closedLeftSide s.1.path₁) : s ∈ twoHeightGood E := by
  have hc₁ := hp₁.1
  have hc₂ := hp₂.1
  refine ⟨hl₁, hl₂, hp₁.2.2.1, hp₂.2.2.1, ?_, (forall_avoidC_iff hc₁).2 hp₁.2.2.2.1,
    (forall_avoidC_iff hc₂).2 hp₂.2.2.2.1, (Sec5.Prop55Half.mem_orderCodeSet_iff hc₁ hp₁.2.2.2.2 hc₂).2 ho⟩
  refine (Theorem15D5.injective_iff_injC (Theorem15D5.goodAll_encC hc₁)).1 ?_
  rw [Theorem15D5.decC_encC_of_continuous hc₁]
  exact hp₁.2.1

/-- **A restart point of the Borel event carries Aux. lemma 94's conclusion**: infinite lifetimes, a simple proper
first continuation from `0` in `ℍ` after `0`, a continuous second continuation from `0` in `ℍ` after `0`, in the
closed left side of the first. -/
theorem twoHeightGood_spec {E : Type*} [MeasurableSpace E] {s : RestartSpace × E} (hs : s ∈ twoHeightGood E) :
    s.1.life₁ = ⊤ ∧ s.1.life₂ = ⊤ ∧ IsSeedProper s.1.path₁ ∧ Continuous s.1.path₂ ∧ s.1.path₂ 0 = 0 ∧
      (∀ t : ℝ≥0, 0 < t → s.1.path₂ t ∈ H) ∧ range s.1.path₂ ⊆ closedLeftSide s.1.path₁ := by
  obtain ⟨hl₁, hl₂, h0₁, h0₂, hinj, hav₁, hav₂, hord⟩ := hs
  have hc₁ : Continuous s.1.path₁ := continuous_decPath_of_top hl₁
  have hc₂ : Continuous s.1.path₂ := continuous_decPath_of_top hl₂
  have hg₁ := Theorem15D5.goodAll_encC hc₁
  have hT : Tendsto (fun t => ‖s.1.path₁ t‖) atTop atTop := by
    have := (Theorem15D5.tendsto_norm_iff_propC hg₁).2 hord.2.1
    rwa [Theorem15D5.decC_encC_of_continuous hc₁] at this
  have hinj' : Function.Injective s.1.path₁ := by
    have := (Theorem15D5.injective_iff_injC hg₁).2 hinj
    rwa [Theorem15D5.decC_encC_of_continuous hc₁] at this
  exact ⟨hl₁, hl₂, ⟨hc₁, hinj', h0₁, (forall_avoidC_iff hc₁).1 hav₁, hT⟩, hc₂, h0₂, (forall_avoidC_iff hc₂).1 hav₂,
    (Sec5.Prop55Half.mem_orderCodeSet_iff hc₁ hT hc₂).1 hord⟩

end RLC

end InteractingSLE

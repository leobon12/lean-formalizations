/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VrVis
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Exist.FlowField
import InteractingSLE.Spec.Sec4.ZeroMarksAvoid

/-!
# A flow line stays off the closed bad set before its lifetime (D10 steps 1 and 3)

Packet PROVE-AUX61-NOJUMP (decision D10).

* **`cumWeightRight_rightLim_flowLine`**, **`cumWeightLeft_leftLim_flowLine`**: the outward cumulative weight of the
  flow-line word at a real point is the source's `cumWeight` of the one-sided boundary value there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal
namespace InteractingSLE.Theorem14.SB.Vr

open PiecewiseConstantBoundaryData (leftLim rightLim jumpSet)

/-- **Right weights of the flow-line word**: for `y > 0`, the right cumulative weight of the flow-line word from `x`
at angle `θ` up to `y` is `cumWeightRight` of the right boundary value at `y + x`. -/
theorem cumWeightRight_rightLim_flowLine {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (x θ : ℝ) {y : ℝ} (hy : 0 < y) :
    Sec4.cumWeightRight κ (rightLim b (y + x) + θ * QuantumZipper.chiC κ) =
      Vq.wR (flowLineXR b J x) (flowLineRhoR κ b J x θ) y := by
  set s := Vq.wR (flowLineXR b J x) (flowLineRhoR κ b J x θ) y with hs
  have hlim : rightLim b (y + x) = sleLambda κ * (1 + s) - θ * QuantumZipper.chiC κ := by
    have hall : ∀ᶠ t in 𝓝[>] (y + x), ∀ z ∈ J, y + x < z → t < z := by
      rw [Finset.eventually_all]
      intro z _
      by_cases hzy : y + x < z
      · filter_upwards [Ioo_mem_nhdsGT hzy] with t ht _ using ht.2
      · exact Eventually.of_forall fun t h => absurd h hzy
    unfold PiecewiseConstantBoundaryData.rightLim
    refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin, Sec4.eventually_notMem_nhdsGT J (y + x), hall] with t ht htJ hlt
    have ht' : y + x < t := ht
    have hfb := Exist.forceBoundaryData_flowLine_seed hκ hb x θ (y := t - x) (by linarith) (by simpa using htJ)
    rw [Sec4.forceBoundaryData_of_nonneg _ _ _ _ (by linarith : (0 : ℝ) ≤ t - x)] at hfb
    have hsum : ∑ i ∈ univ.filter (fun i => flowLineXR b J x i ≤ t - x), flowLineRhoR κ b J x θ i = s := by
      rw [hs]
      unfold Vq.wR
      congr 1
      apply Finset.filter_congr
      intro i _
      constructor
      · intro hi
        by_contra hiy
        rw [not_le] at hiy
        induction i using Fin.cases with
        | zero =>
          have h0 : y < 0 := hiy
          linarith
        | succ k =>
          have hk : flowLineXR b J x k.succ = ((jumpSet b J).filter (x < ·)).orderEmbOfFin rfl k - x := rfl
          rw [hk] at hi hiy
          have hzmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (x < ·)) rfl k
          have hzJ := (Finset.mem_filter.1 (Finset.mem_filter.1 hzmem).1).1
          have := hlt _ hzJ (by linarith)
          linarith
      · intro hi; linarith
    rw [hsum, sub_add_cancel] at hfb
    linarith
  rw [hlim, show sleLambda κ * (1 + s) - θ * QuantumZipper.chiC κ + θ * QuantumZipper.chiC κ =
    sleLambda κ * (1 + s) by ring, Sec4.cumWeightRight_spec hκ]

/-- **Left weights of the flow-line word**: for `y < 0`, the left cumulative weight of the flow-line word from `x` at
angle `θ` from `y` is `cumWeightLeft` of the left boundary value at `y + x`. -/
theorem cumWeightLeft_leftLim_flowLine {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (x θ : ℝ) {y : ℝ} (hy : y < 0) :
    Sec4.cumWeightLeft κ (leftLim b (y + x) + θ * QuantumZipper.chiC κ) =
      Vq.wL (flowLineXL b J x) (flowLineRhoL κ b J x θ) y := by
  set s := Vq.wL (flowLineXL b J x) (flowLineRhoL κ b J x θ) y with hs
  have hlim : leftLim b (y + x) = -sleLambda κ * (1 + s) - θ * QuantumZipper.chiC κ := by
    have hall : ∀ᶠ t in 𝓝[<] (y + x), ∀ z ∈ J, z < y + x → z < t := by
      rw [Finset.eventually_all]
      intro z _
      by_cases hzy : z < y + x
      · filter_upwards [Ioo_mem_nhdsLT hzy] with t ht _ using ht.1
      · exact Eventually.of_forall fun t h => absurd h hzy
    unfold PiecewiseConstantBoundaryData.leftLim
    refine Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin, Sec4.eventually_notMem_nhdsLT J (y + x), hall] with t ht htJ hlt
    have ht' : t < y + x := ht
    have hfb := Exist.forceBoundaryData_flowLine_seed hκ hb x θ (y := t - x) (by linarith) (by simpa using htJ)
    rw [Sec4.forceBoundaryData_of_neg _ _ _ _ (by linarith : t - x < 0)] at hfb
    have hsum : ∑ i ∈ univ.filter (fun i => t - x < flowLineXL b J x i), flowLineRhoL κ b J x θ i = s := by
      rw [hs]
      unfold Vq.wL
      congr 1
      apply Finset.filter_congr
      intro i _
      constructor
      · intro hi
        by_contra hiy
        rw [not_le] at hiy
        induction i using Fin.cases with
        | zero =>
          have h0 : (0 : ℝ) < y := hiy
          linarith
        | succ k =>
          have hk : flowLineXL b J x k.succ =
              ((jumpSet b J).filter (· < x)).orderEmbOfFin rfl (Fin.rev k) - x := rfl
          rw [hk] at hi hiy
          have hzmem := Finset.orderEmbOfFin_mem ((jumpSet b J).filter (· < x)) rfl (Fin.rev k)
          have hzJ := (Finset.mem_filter.1 (Finset.mem_filter.1 hzmem).1).1
          have := hlt _ hzJ (by linarith)
          linarith
      · intro hi; linarith
    rw [hsum, sub_add_cancel] at hfb
    linarith
  rw [hlim, show -sleLambda κ * (1 + s) - θ * QuantumZipper.chiC κ + θ * QuantumZipper.chiC κ =
    -sleLambda κ * (1 + s) by ring, Sec4.cumWeightLeft_spec hκ]

section Closure

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The set of bad points of a force word. -/
def badSet (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Set ℂ :=
  {z | Vq.IsBadPoint xL xR ρL ρR z}

theorem badSet_subset_real : badSet xL xR ρL ρR ⊆ {w : ℂ | w.im = 0} := fun _ hw => hw.1

/-- A point strictly closer to `y` than every mark other than `y` has no such mark between it and `y`. -/
theorem not_between_of_abs_lt {m b y : ℝ} (h : |b - y| < |m - y|) (h1 : min b y ≤ m) (h2 : m ≤ max b y) :
    False := by
  rcases le_total b y with hby | hby
  · rw [min_eq_left hby] at h1
    rw [max_eq_right hby] at h2
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
    linarith
  · rw [min_eq_right hby] at h1
    rw [max_eq_left hby] at h2
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
    linarith

/-- **The closure of the bad set adds only nonzero marks**: a limit of bad points is bad, or a nonzero mark. -/
theorem mem_badSet_or_mark_of_mem_closure (hxR : ∀ j, 0 ≤ xR j) (hxL : ∀ i, xL i ≤ 0) {z : ℂ}
    (hz : z ∈ closure (badSet xL xR ρL ρR)) :
    z ∈ badSet xL xR ρL ρR ∨ (∃ j, xR j ≠ 0 ∧ z = xR j) ∨ (∃ i, xL i ≠ 0 ∧ z = xL i) := by
  have hreal : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have hzim : z.im = 0 := closure_minimal badSet_subset_real hreal hz
  set y := z.re with hydef
  have hzy : z = (y : ℂ) := Complex.ext (by simp [hydef]) (by simp [hzim])
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨hzB, hR, hL⟩ := hcon
  have hRy : ∀ j, xR j = y → y = 0 := fun j hj => by
    by_contra hy0
    exact hR j (by rw [hj]; exact hy0) (by rw [hzy, hj])
  have hLy : ∀ i, xL i = y → y = 0 := fun i hi => by
    by_contra hy0
    exact hL i (by rw [hi]; exact hy0) (by rw [hzy, hi])
  -- marks other than `y` are bounded away from `y`
  set M : Finset ℝ := (Finset.univ.image xR ∪ Finset.univ.image xL).filter (fun m => m ≠ y) with hM
  have hev : ∀ᶠ b in 𝓝 y, ∀ m ∈ M, |b - y| < |m - y| := by
    rw [Finset.eventually_all]
    intro m hm
    have hmy : 0 < |m - y| := abs_pos.2 (sub_ne_zero.2 (Finset.mem_filter.1 hm).2)
    have hc : Tendsto (fun b => |b - y|) (𝓝 y) (𝓝 0) := by
      have h := ((continuous_id.sub (continuous_const (y := y))).abs.tendsto y)
      simpa using h
    exact hc.eventually (gt_mem_nhds hmy)
  have hev' : ∀ᶠ w in 𝓝 z, ∀ m ∈ M, |w.re - y| < |m - y| :=
    (Complex.continuous_re.tendsto z).eventually hev
  obtain ⟨w, hwev, hwB⟩ := mem_closure_iff_nhds.1 hz _ hev'
  set b := w.re with hbdef
  have hRM : ∀ j, xR j ≠ y → xR j ∈ M := fun j h =>
    Finset.mem_filter.2 ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem xR (Finset.mem_univ j)), h⟩
  have hLM : ∀ i, xL i ≠ y → xL i ∈ M := fun i h =>
    Finset.mem_filter.2 ⟨Finset.mem_union_right _ (Finset.mem_image_of_mem xL (Finset.mem_univ i)), h⟩
  have hbR : ∀ j, xR j ≠ y → min b y ≤ xR j → xR j ≤ max b y → False := fun j h h1 h2 =>
    not_between_of_abs_lt (hwev _ (hRM j h)) h1 h2
  have hbL : ∀ i, xL i ≠ y → min b y ≤ xL i → xL i ≤ max b y → False := fun i h h1 h2 =>
    not_between_of_abs_lt (hwev _ (hLM i h)) h1 h2
  apply hzB
  refine ⟨hzim, ?_⟩
  rcases hwB.2 with ⟨hb0, hbw⟩ | ⟨hb0, hbw⟩
  · -- a right bad point near `y`
    have hy0 : 0 ≤ y := by
      by_contra hy
      rw [not_le] at hy
      have hemp : univ.filter (fun j => xR j ≤ b) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun j _ hj => hbR j (by linarith [hxR j])
          ((min_le_right _ _).trans (by linarith [hxR j])) (hj.trans (le_max_left _ _))
      have : Vq.wR xR ρR b = 0 := by unfold Vq.wR; rw [hemp, sum_empty]
      linarith
    refine Or.inl ⟨hy0, ?_⟩
    have heq : Vq.wR xR ρR y = Vq.wR xR ρR b := by
      unfold Vq.wR
      congr 1
      apply Finset.filter_congr
      intro j _
      constructor
      · intro hj
        by_contra hjb
        rw [not_le] at hjb
        by_cases hjy : xR j = y
        · have := hRy j hjy; linarith
        · exact hbR j hjy ((min_le_left _ _).trans hjb.le) (hj.trans (le_max_right _ _))
      · intro hj
        by_contra hjy
        rw [not_le] at hjy
        exact hbR j hjy.ne' ((min_le_right _ _).trans hjy.le) (hj.trans (le_max_left _ _))
    rw [heq]; exact hbw
  · -- a left bad point near `y`
    have hy0 : y ≤ 0 := by
      by_contra hy
      rw [not_le] at hy
      have hemp : univ.filter (fun i => b ≤ xL i) = ∅ := by
        refine Finset.filter_eq_empty_iff.2 fun i _ hi => hbL i (by linarith [hxL i])
          ((min_le_left _ _).trans hi) ((hxL i).trans (by linarith [le_max_right b y]))
      have : Vq.wL xL ρL b = 0 := by unfold Vq.wL; rw [hemp, sum_empty]
      linarith
    refine Or.inr ⟨hy0, ?_⟩
    have heq : Vq.wL xL ρL y = Vq.wL xL ρL b := by
      unfold Vq.wL
      congr 1
      apply Finset.filter_congr
      intro i _
      constructor
      · intro hi
        by_contra hib
        rw [not_le] at hib
        by_cases hiy : xL i = y
        · have := hLy i hiy; linarith
        · exact hbL i hiy ((min_le_right _ _).trans hi) (hib.le.trans (le_max_left _ _))
      · intro hi
        by_contra hiy
        rw [not_le] at hiy
        exact hbL i hiy.ne ((min_le_left _ _).trans hi) (hiy.le.trans (le_max_right _ _))
    rw [heq]; exact hbw

end Closure

section Flow

universe u

/-- **A flow line stays off the closed bad set before its lifetime** (D10 step 3's core, almost surely). Before `ζ`,
the flow line (centred at its start) is never at a limit of bad points of its word: bad points other than the start
are never visited (`trace_ne_of_bad`); the start is bad only at a threshold at time `0`; and the other limits are the
finitely many nonzero marks of outward weight `> −2 > κ/2 − 4`, never visited by Lemma G12
(`Supp7.g12FlowStatement`). -/
theorem ae_notMem_closure_badSet {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x θ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, 0 < ζ ω → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      η ω t - x ∉ closure (badSet (flowLineXL b jumps x) (flowLineXR b jumps x) (flowLineRhoL κ b jumps x θ)
        (flowLineRhoR κ b jumps x θ)) := by
  set xL := flowLineXL b jumps x
  set xR := flowLineXR b jumps x
  set ρL := flowLineRhoL κ b jumps x θ
  set ρR := flowLineRhoR κ b jumps x θ
  have hG := Supp7.g12FlowStatement.{u} κ hκ hκ4 b jumps hb x θ
  have hd : κ / 2 - 4 < -2 := by linarith
  have hRj : ∀ j, ∀ᵐ ω ∂P, 0 < xR j → -2 < Vq.wR xR ρR (xR j) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ ((xR j + x : ℝ) : ℂ) := by
    intro j
    by_cases hc : 0 < xR j ∧ -2 < Vq.wR xR ρR (xR j)
    · have hS : κ / 2 - 4 < Sec4.cumWeightRight κ (rightLim b (xR j + x) + θ * QuantumZipper.chiC κ) := by
        rw [cumWeightRight_rightLim_flowLine hκ hb x θ hc.1]; linarith [hc.2]
      filter_upwards [((hG (xR j + x) P h hh η ζ hη).1 (by linarith [hc.1]) hS)] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hc
  have hLi : ∀ i, ∀ᵐ ω ∂P, xL i < 0 → -2 < Vq.wL xL ρL (xL i) →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ ((xL i + x : ℝ) : ℂ) := by
    intro i
    by_cases hc : xL i < 0 ∧ -2 < Vq.wL xL ρL (xL i)
    · have hS : κ / 2 - 4 < Sec4.cumWeightLeft κ (leftLim b (xL i + x) + θ * QuantumZipper.chiC κ) := by
        rw [cumWeightLeft_leftLim_flowLine hκ hb x θ hc.1]; linarith [hc.2]
      filter_upwards [((hG (xL i + x) P h hh η ζ hη).2 (by linarith [hc.1]) hS)] with ω hω _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ hc
  obtain ⟨h', 𝓕, W, VL, VR, B, -, hcoup, hgen⟩ := hη
  filter_upwards [hcoup.1.2.2.2.2, hgen, ae_all_iff.2 hRj, ae_all_iff.2 hLi] with ω hp hg hR hL hζ0 t ht hmem
  have hp' := hp
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, hvLw, hwvR, -, -, -, -, -, -, -, -, hnt, -⟩ := hp'
  have hz0' : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by simpa using hζ0
  have hxR : ∀ j, 0 ≤ xR j := fun j => by
    have := hwvR 0 hz0' j; rw [hw0, hvR0 j] at this; exact this
  have hxL : ∀ i, xL i ≤ 0 := fun i => by
    have := hvLw 0 hz0' i; rw [hw0, hvL0 i] at this; exact this
  set z := η ω t - x with hzdef
  by_cases hzB : z ∈ badSet xL xR ρL ρR
  · by_cases hz0 : z = 0
    · -- the start is bad only at a threshold at time `0`
      rw [hz0] at hzB
      apply hnt 0 hz0'
      simp only [hw0, hvL0, hvR0]
      rcases hzB.2 with ⟨-, hw⟩ | ⟨-, hw⟩
      · right
        have hf : univ.filter (fun j => xR j = 0) = univ.filter (fun j => xR j ≤ (0 : ℂ).re) := by
          refine Finset.filter_congr fun j _ => ?_
          simp only [Complex.zero_re]
          exact ⟨le_of_eq, fun h => le_antisymm h (hxR j)⟩
        rw [hf]; exact hw
      · left
        have hf : univ.filter (fun i => xL i = 0) = univ.filter (fun i => (0 : ℂ).re ≤ xL i) := by
          refine Finset.filter_congr fun i _ => ?_
          simp only [Complex.zero_re]
          exact ⟨ge_of_eq, fun h => le_antisymm (hxL i) h⟩
        rw [hf]; exact hw
    · exact trace_ne_of_bad hp hg ht hzB hz0 (by simp only [hzdef])
  · rcases mem_badSet_or_mark_of_mem_closure hxR hxL hmem with hB | ⟨j, hj0, hzj⟩ | ⟨i, hi0, hzi⟩
    · exact hzB hB
    · have hpos : 0 < xR j := lt_of_le_of_ne (hxR j) (Ne.symm hj0)
      have hw : -2 < Vq.wR xR ρR (xR j) := by
        by_contra hw
        exact hzB ⟨by rw [hzj]; simp, Or.inl ⟨by rw [hzj]; simpa using hpos.le, by rw [hzj]; simpa using hw⟩⟩
      exact hR j hpos hw t ht.le (by rw [Complex.ofReal_add, ← hzj, hzdef]; ring)
    · have hneg : xL i < 0 := lt_of_le_of_ne (hxL i) hi0
      have hw : -2 < Vq.wL xL ρL (xL i) := by
        by_contra hw
        exact hzB ⟨by rw [hzi]; simp, Or.inr ⟨by rw [hzi]; simpa using hneg.le, by rw [hzi]; simpa using hw⟩⟩
      exact hL i hneg hw t ht.le (by rw [Complex.ofReal_add, ← hzi, hzdef]; ring)

end Flow

end InteractingSLE.Theorem14.SB.Vr

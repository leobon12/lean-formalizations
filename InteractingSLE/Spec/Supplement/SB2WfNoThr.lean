/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WeStmt
import InteractingSLE.Spec.Supplement.SB2WeCol
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Exist.FlowField

/-!
# E7, first direction: no relative threshold before the lifetime (deterministic)

Packet PROVE-T14-SB2WORD (round 3, decision D18). If the relative driver `W` of SB2(1)'s remainder (in the launch
chart recentred at the entry `m`) reaches its continuation threshold at a relative time `t`, then the physical point
read back from the relative tip through the chart's inverse boundary map `g` is a bad point of the original data for
the upper flow (`badSet`). Hence, as long as `g(Γ s + m)` stays off the closure of the bad set, the relative driver
has no threshold: `V ≤ thr` (SB2DRV's producer obligation `V_le_thr` for D10's stops, which are defined by the
distance of `g(Γ s)` to that closed set).

* `badSet κ ψ u b`: the real points right of `u` with right weight `≤ −2` and left of `u` with left weight `≤ −2`;
* `wR_eq_of_isFlowType`, `wL_eq_of_isFlowType`: the cumulative weights of the cell word at a point are the weights of
  the word's height just beside it;
* `tip_bad_right_of_threshold`, `tip_bad_left_of_threshold`: a relative threshold puts the relative tip at a bad
  relative point (`Vq.right_bad_of_collision`, the left side by reflection);
* `phys_bad_right`, `phys_bad_left`: by the second clause the relative heights beside a bad relative point are
  original heights at free original-real points, so `g` of the tip is in the closure of the bad set;
* **`le_thr_of_good`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMapInv)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lv Sec7.PocketTraversal MartChar.RealFlow
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- **The bad real points of the original data** for the upper flow from `u` at angle `ψ`. -/
def badSet (κ ψ u : ℝ) (b : ℝ → ℝ) : Set ℝ :=
  {x | u < x ∧ Sec4.cumWeightRight κ (rightLim b x + ψ * chiC κ) ≤ -2} ∪
    {x | x < u ∧ Sec4.cumWeightLeft κ (leftLim b x + ψ * chiC κ) ≤ -2}

/-! ### Weights of the cell word from its heights -/

section Weights

variable {κ ψ : ℝ} {c : BoundaryWord} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ}

/-- A finite family of reals leaves a gap right of every point. -/
theorem exists_gap_right {n : ℕ} (x : Fin n → ℝ) (y : ℝ) : ∃ y₁, y < y₁ ∧ ∀ j, ¬ (y < x j ∧ x j < y₁) := by
  classical
  set M := (univ.filter (fun j => y < x j)).image x with hM
  by_cases hne : M.Nonempty
  · refine ⟨M.min' hne, ?_, fun j hj => ?_⟩
    · obtain ⟨j, hj, he⟩ := Finset.mem_image.1 (M.min'_mem hne)
      rw [← he]
      exact (Finset.mem_filter.1 hj).2
    · have := M.min'_le (x j) (Finset.mem_image.2 ⟨j, Finset.mem_filter.2 ⟨mem_univ _, hj.1⟩, rfl⟩)
      linarith [hj.2]
  · refine ⟨y + 1, by linarith, fun j hj => hne ⟨x j, Finset.mem_image.2 ⟨j, ?_, rfl⟩⟩⟩
    exact Finset.mem_filter.2 ⟨mem_univ _, hj.1⟩

/-- A finite family of reals leaves a gap left of every point. -/
theorem exists_gap_left {n : ℕ} (x : Fin n → ℝ) (y : ℝ) : ∃ y₁, y₁ < y ∧ ∀ j, ¬ (y₁ < x j ∧ x j < y) := by
  obtain ⟨y₁, hy₁, hgap⟩ := exists_gap_right (fun j => -x j) (-y)
  refine ⟨-y₁, by linarith, fun j hj => hgap j ⟨by linarith [hj.2], by linarith [hj.1]⟩⟩

/-- **The right cumulative weight of the cell word at `y ≥ 0`** is the right weight of the word's height just right of
`y`. -/
theorem wR_eq_of_isFlowType (hκ : 0 < κ) (hft : FCDet.IsFlowType κ ψ c xL xR ρL ρR) {y : ℝ} (hy : 0 ≤ y) :
    ∃ y₁, y < y₁ ∧ ∀ y'', y < y'' → y'' < y₁ → y'' ∉ c.jumps →
      Vq.wR xR ρR y = Sec4.cumWeightRight κ (c.fn y'' + ψ * chiC κ) := by
  obtain ⟨y₁, hy₁, hgap⟩ := exists_gap_right xR y
  refine ⟨y₁, hy₁, fun y'' hy'' hy''₁ hJ => ?_⟩
  have hfilt : univ.filter (fun j => xR j ≤ y) = univ.filter (fun j => xR j ≤ y'') :=
    Finset.filter_congr fun j _ => ⟨fun h => h.trans hy''.le, fun h => by
      by_contra hn
      push Not at hn
      exact hgap j ⟨hn, lt_of_le_of_lt h hy''₁⟩⟩
  have hy''0 : y'' ≠ 0 := (lt_of_le_of_lt hy hy'').ne'
  unfold Vq.wR
  rw [hfilt, ← Sec4.cumWeightRight_forceBoundaryData hκ ρL ρR xL xR (hy.trans hy''.le),
    RetAux79.forceBoundaryData_zero_of_isFlowType hft y'',
    forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 ψ hy''0 (by rwa [add_zero]), add_zero]

/-- **The left cumulative weight of the cell word at `y ≤ 0`** is the left weight of the word's height just left of
`y`. -/
theorem wL_eq_of_isFlowType (hκ : 0 < κ) (hft : FCDet.IsFlowType κ ψ c xL xR ρL ρR) {y : ℝ} (hy : y ≤ 0) :
    ∃ y₁, y₁ < y ∧ ∀ y'', y₁ < y'' → y'' < y → y'' ∉ c.jumps →
      Vq.wL xL ρL y = Sec4.cumWeightLeft κ (c.fn y'' + ψ * chiC κ) := by
  obtain ⟨y₁, hy₁, hgap⟩ := exists_gap_left xL y
  refine ⟨y₁, hy₁, fun y'' hy₁'' hy'' hJ => ?_⟩
  have hfilt : univ.filter (fun i => y ≤ xL i) = univ.filter (fun i => y'' < xL i) :=
    Finset.filter_congr fun i _ => ⟨fun h => lt_of_lt_of_le hy'' h, fun h => by
      by_contra hn
      push Not at hn
      exact hgap i ⟨lt_trans hy₁'' h, hn⟩⟩
  have hy''0 : y'' < 0 := lt_of_lt_of_le hy'' hy
  unfold Vq.wL
  rw [hfilt, ← Sec4.cumWeightLeft_forceBoundaryData hκ ρL ρR xL xR hy''0,
    RetAux79.forceBoundaryData_zero_of_isFlowType hft y'',
    forceBoundaryData_flowLine_seed hκ c.isPiecewiseConstantBoundaryData 0 ψ hy''0.ne (by rwa [add_zero]),
    add_zero]

end Weights

/-! ### A relative threshold puts the relative tip at a bad relative point -/

section Tip

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ω : Ω} {V : ℝ≥0∞} {Γ : ℝ≥0 → ℂ}

/-- The real driver of `W` at `ω` and the real trace, at a positive time `t ≤ V`: a Loewner trace continuous on
`[0, t]`, with boundary limits and tip `Γ t`. -/
theorem trace_facts (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0)
    (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ) {t : ℝ≥0} (ht0 : 0 < t) (ht : (t : ℝ≥0∞) ≤ V) :
    IsLoewnerTraceLT (Bessel.realPath W ω) t (fun s : ℝ => Γ s.toNNReal) ∧
      ContinuousOn (fun s : ℝ => Γ s.toNNReal) (Icc 0 t) ∧
      HasBdryLimits (fwdMapInv (Bessel.realPath W ω) t) ∧
      extendFrom H (fwdMapInv (Bessel.realPath W ω) t) 0 = Γ t := by
  have hU : Continuous (Bessel.realPath W ω) := hWc.comp continuous_real_toNNReal
  have hU0 : Bessel.realPath W ω 0 = 0 := by simp [Bessel.realPath, hW0]
  have hL := GB7a.isLoewnerTraceLT_of_agree hΓ ht (U := Bessel.realPath W ω) fun s _ _ => rfl
  have hc : ContinuousOn (fun s : ℝ => Γ s.toNNReal) (Icc 0 t) := by
    refine hΓ.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ V
    exact le_trans (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 hs.2)) ht
  have ht0' : (0 : ℝ) < t := ht0
  refine ⟨hL, hc, TraceClose.hasBdryLimits_of_isLoewnerTraceLT hL hU hU0 ht0' hc, ?_⟩
  rw [TraceClose.extendFrom_zero_eq hL hU hU0 ht0' hc]
  simp

/-- **A right threshold puts the relative tip at a bad right point.** -/
theorem tip_bad_right_of_threshold (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0)
    (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ) {nR : ℕ} {xR : Ω → Fin nR → ℝ} (hxR : ∀ j, 0 ≤ xR ω j)
    {ρR : Fin nR → ℝ} {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ V)
    (hthr : ∑ j ∈ univ.filter (fun j => geomRW W xR j t ω = W t ω), ρR j ≤ -2) :
    (Γ t).im = 0 ∧ 0 ≤ (Γ t).re ∧ Vq.wR (xR ω) ρR (Γ t).re ≤ -2 := by
  have hU : Continuous (Bessel.realPath W ω) := hWc.comp continuous_real_toNNReal
  have hU0 : Bessel.realPath W ω 0 = 0 := by simp [Bessel.realPath, hW0]
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0
    have hΓ0 : Γ 0 = 0 := hΓ.1
    rw [hΓ0]
    refine ⟨by simp, by simp, ?_⟩
    have hfilt : univ.filter (fun j => geomRW W xR j 0 ω = W 0 ω) =
        univ.filter (fun j => xR ω j ≤ (0 : ℂ).re) :=
      Finset.filter_congr fun j _ => by
        have h1 : geomRW W xR j 0 ω = xR ω j := by
          simp only [geomRW, NNReal.coe_zero]
          exact rightImg_zero hU hU0 (hxR j)
        rw [h1, hW0, Complex.zero_re]
        exact ⟨fun h => h.le, fun h => le_antisymm h (hxR j)⟩
    unfold Vq.wR
    rw [← hfilt]
    exact hthr
  · obtain ⟨-, -, hB, htip⟩ := trace_facts hWc hW0 hΓ (pos_iff_ne_zero.2 ht0) ht
    have hWt : Bessel.realPath W ω t = W t ω := by simp [Bessel.realPath]
    refine Vq.right_bad_of_collision hU hU0 t.coe_nonneg hB htip hxR ?_
    have hf : univ.filter (fun j => rightImg (Bessel.realPath W ω) (xR ω j) t = Bessel.realPath W ω t) =
        univ.filter (fun j => geomRW W xR j t ω = W t ω) :=
      Finset.filter_congr fun j _ => by rw [hWt]; rfl
    rw [hf]
    exact hthr

/-- **A left threshold puts the relative tip at a bad left point** (reflection of `tip_bad_right_of_threshold`). -/
theorem tip_bad_left_of_threshold (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0)
    (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ) {nL : ℕ} {xL : Ω → Fin nL → ℝ} (hxL : ∀ i, xL ω i ≤ 0)
    {ρL : Fin nL → ℝ} {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ V)
    (hthr : ∑ i ∈ univ.filter (fun i => geomLW W xL i t ω = W t ω), ρL i ≤ -2) :
    (Γ t).im = 0 ∧ (Γ t).re ≤ 0 ∧ Vq.wL (xL ω) ρL (Γ t).re ≤ -2 := by
  set U := Bessel.realPath W ω with hUdef
  have hU : Continuous U := hWc.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp [hUdef, Bessel.realPath, hW0]
  have hU' : Bessel.realPath (fun t ω => -W t ω) ω = -U := by
    funext r; simp [hUdef, Bessel.realPath]
  have hcond : ∀ i, geomLW W xL i t ω = W t ω ↔ rightImg (-U) (-xL ω i) t = (-U) t := fun i => by
    simp only [geomLW, hU', Pi.neg_apply, hUdef, Bessel.realPath, Real.toNNReal_coe]
    constructor <;> intro h <;> linarith
  have hwL : ∀ y : ℝ, Vq.wR (fun i => -xL ω i) ρL (-y) = Vq.wL (xL ω) ρL y := fun y => by
    unfold Vq.wR Vq.wL
    exact Finset.sum_congr (Finset.filter_congr fun i _ => by constructor <;> intro h <;> linarith) fun _ _ => rfl
  have hxL' : ∀ i, 0 ≤ -xL ω i := fun i => by linarith [hxL i]
  have hthr' : ∑ i ∈ univ.filter (fun i => rightImg (-U) (-xL ω i) t = (-U) t), ρL i ≤ -2 := by
    have hf : univ.filter (fun i => rightImg (-U) (-xL ω i) t = (-U) t) =
        univ.filter (fun i => geomLW W xL i t ω = W t ω) := Finset.filter_congr fun i _ => (hcond i).symm
    rw [hf]
    exact hthr
  have hnU : Continuous (-U) := hU.neg
  have hnU0 : (-U) 0 = 0 := by simp [hU0]
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0
    have hΓ0 : Γ 0 = 0 := hΓ.1
    rw [hΓ0]
    refine ⟨by simp, by simp, ?_⟩
    have hfilt : univ.filter (fun i => rightImg (-U) (-xL ω i) ((0 : ℝ≥0) : ℝ) = (-U) ((0 : ℝ≥0) : ℝ)) =
        univ.filter (fun i => -xL ω i ≤ -(0 : ℂ).re) :=
      Finset.filter_congr fun i _ => by
        rw [NNReal.coe_zero, rightImg_zero hnU hnU0 (hxL' i), hnU0, Complex.zero_re, neg_zero]
        exact ⟨fun h => h.le, fun h => le_antisymm h (hxL' i)⟩
    rw [← hwL]
    unfold Vq.wR
    rw [← hfilt]
    exact hthr'
  · obtain ⟨hL, hc, -, -⟩ := trace_facts hWc hW0 hΓ (pos_iff_ne_zero.2 ht0) ht
    have ht0' : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 ht0)
    have hLr := Vo.isLoewnerTraceLT_reflect hL
    have hcr : ContinuousOn (fun s : ℝ => LP.reflectC (Γ s.toNNReal)) (Icc 0 t) :=
      LP.continuous_reflectC.comp_continuousOn hc
    have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hLr hnU hnU0 ht0' hcr
    have htip := TraceClose.extendFrom_zero_eq hLr hnU hnU0 ht0' hcr
    simp only [Real.toNNReal_coe] at htip
    obtain ⟨him, hre, hbad⟩ := Vq.right_bad_of_collision hnU hnU0 t.coe_nonneg hB htip hxL' hthr'
    have hre' : (LP.reflectC (Γ t)).re = -(Γ t).re := by simp [LP.reflectC]
    have him' : (LP.reflectC (Γ t)).im = (Γ t).im := by simp [LP.reflectC]
    rw [hre', hwL] at hbad
    rw [him'] at him
    rw [hre'] at hre
    exact ⟨him, by linarith, hbad⟩

end Tip

/-! ### A bad relative point is read back in the closure of the bad set -/

section Corr

variable {κ ψ u m : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {c : Chart} {g : ℂ → ℂ} {β cw : BoundaryWord}
  {Fw : Finset ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- A complex limit of real points of a set is a real point of its closure. -/
theorem exists_real_mem_closure_of_tendsto {l : Filter ℝ} [l.NeBot] {f : ℝ → ℂ} {p : ℂ} (hf : Tendsto f l (𝓝 p))
    {B : Set ℝ} (hB : ∀ᶠ y in l, ∃ x ∈ B, f y = (x : ℂ)) : ∃ x₀ : ℝ, p = x₀ ∧ x₀ ∈ closure B := by
  have hcl : p ∈ closure (((↑) : ℝ → ℂ) '' B) :=
    mem_closure_of_tendsto hf (hB.mono fun y ⟨x, hx, he⟩ => ⟨x, hx, he.symm⟩)
  have him : p.im = 0 := by
    have hc : IsClosed {z : ℂ | z.im = 0} := isClosed_eq Complex.continuous_im continuous_const
    exact closure_minimal (by rintro _ ⟨x, -, rfl⟩; simp) hc hcl
  refine ⟨p.re, Complex.ext (by simp) (by simp [him]), Metric.mem_closure_iff.2 fun ε hε => ?_⟩
  obtain ⟨_, ⟨x, hx, rfl⟩, hd⟩ := Metric.mem_closure_iff.1 hcl ε hε
  refine ⟨x, hx, ?_⟩
  rw [Real.dist_eq]
  calc |p.re - x| = |(p - (x : ℂ)).re| := by simp
    _ ≤ ‖p - (x : ℂ)‖ := Complex.abs_re_le_norm _
    _ = dist p (x : ℂ) := (dist_eq_norm _ _).symm
    _ < ε := hd

theorem tendsto_g_real (hgc : ContinuousOn g {z | 0 ≤ z.im}) (l : Filter ℝ) {y : ℝ} (hly : l ≤ 𝓝 y) :
    Tendsto (fun y'' : ℝ => g ((y'' + m : ℝ) : ℂ)) l (𝓝 (g ((y + m : ℝ) : ℂ))) := by
  have hcont : Tendsto (fun y'' : ℝ => ((y'' + m : ℝ) : ℂ)) (𝓝 y) (𝓝[{z : ℂ | 0 ≤ z.im}] ((y + m : ℝ) : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨((Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).tendsto y),
      Eventually.of_forall fun y'' => by simp⟩
  exact ((hgc _ (by simp)).tendsto.comp hcont).mono_left hly

/-- **A bad right relative point is read back in the closure of the bad set** (second clause, right side). -/
theorem phys_bad_right (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal) (hgc : ContinuousOn g {z | 0 ≤ z.im})
    (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps) (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m))
    (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {y : ℝ} (hy : 0 ≤ y) (hbad : Vq.wR xR ρR y ≤ -2) :
    ∃ x₀ : ℝ, g ((y + m : ℝ) : ℂ) = x₀ ∧ x₀ ∈ closure (badSet κ ψ u b) := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, hSr, -⟩ := hSC
  obtain ⟨y₁, hy₁, hw⟩ := wR_eq_of_isFlowType hκ hft hy
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  set E : Finset ℝ := cw.jumps ∪ Fw ∪ β.jumps.image (· - m) ∪ Fy.image (· - m) ∪
    (jumps ∪ Fx ∪ {u}).image (fun x => rProf c x - m) with hE
  have hgood : ∀ y'', y < y'' → y'' < y₁ → y'' ∉ E → ∃ x ∈ badSet κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' h1 h2 hE''
    have hcwJ : y'' ∉ cw.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
    have hFw : y'' ∉ Fw := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
    have hβJ : y'' + m ∉ β.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩))))
    have hFy : y'' + m ∉ Fy := fun h => hE'' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩)))
    have hwr := hw y'' h1 h2 hcwJ
    rw [hwr, hcw y'' hFw] at hbad
    have hlow : β.fn (y'' + m) + ψ * chiC κ ≤ -sleLambda κ := by
      unfold Sec4.cumWeightRight at hbad
      have : (β.fn (y'' + m) + ψ * chiC κ) / sleLambda κ ≤ -1 := by linarith
      rw [div_le_iff₀ hl] at this
      linarith
    rcases hSy (y'' + m) hβJ hFy with ⟨hβ, -⟩ | ⟨x, hxS, hxy⟩
    · exfalso
      rw [hβ] at hlow
      have : 0 < (ψ + Real.pi / 2) * chiC κ := mul_pos (by linarith) hχ
      linarith
    · have hxJ : x ∉ jumps := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ (Finset.mem_union_left _ h), by rw [hxy]; ring⟩))
      have hxF : x ∉ Fx := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ (Finset.mem_union_right _ h), by rw [hxy]; ring⟩))
      have hxu : x ≠ u := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ (Finset.mem_singleton.2 h), by rw [hxy]; ring⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hβJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have hux : u ≤ x := hSr x hxS (by rw [hxy]; linarith)
      refine ⟨x, Or.inl ⟨lt_of_le_of_ne hux (Ne.symm hxu), ?_⟩, ?_⟩
      · rw [rightLim_eq_of_notMem hb hxJ, ← hbx, hxy]
        unfold Sec4.cumWeightRight
        have : (β.fn (y'' + m) + ψ * chiC κ) / sleLambda κ ≤ -1 := by
          rw [div_le_iff₀ hl]; linarith
        linarith
      · have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
        rw [hc.eq_ofReal x, hxy] at h1
        exact h1
  have hev : ∀ᶠ y'' in 𝓝[>] y, ∃ x ∈ badSet κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    have h1 : ∀ᶠ y'' in 𝓝[>] y, y'' < y₁ := (gt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y'' in 𝓝[>] y, y'' ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_gt hz)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hy''E
    exact hgood y'' hy'' hy''₁ hy''E
  obtain ⟨x₀, hx₀, hcl⟩ := exists_real_mem_closure_of_tendsto
    (tendsto_g_real (m := m) hgc (𝓝[>] y) nhdsWithin_le_nhds) hev
  exact ⟨x₀, hx₀, hcl⟩

/-- **A bad left relative point is read back in the closure of the bad set** (second clause, left side). -/
theorem phys_bad_left (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps) (hcc : c.IsConformal)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (hSC : SecondClause κ b jumps c u m β.fn β.jumps)
    (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m)) (hft : FCDet.IsFlowType κ ψ cw xL xR ρL ρR) {y : ℝ} (hy : y ≤ 0)
    (hbad : Vq.wL xL ρL y ≤ -2) :
    ∃ x₀ : ℝ, g ((y + m : ℝ) : ℂ) = x₀ ∧ x₀ ∈ closure (badSet κ ψ u b) := by
  classical
  obtain ⟨hc, S, Fx, Fy, hSm, hSc, hSo, hSy, -, hSl⟩ := hSC
  obtain ⟨y₁, hy₁, hw⟩ := wL_eq_of_isFlowType hκ hft hy
  set E : Finset ℝ := cw.jumps ∪ Fw ∪ β.jumps.image (· - m) ∪ Fy.image (· - m) ∪
    (jumps ∪ Fx).image (fun x => rProf c x - m) with hE
  have hgood : ∀ y'', y₁ < y'' → y'' < y → y'' ∉ E → ∃ x ∈ badSet κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    intro y'' h1 h2 hE''
    have hcwJ : y'' ∉ cw.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _ h))))
    have hFw : y'' ∉ Fw := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _ h))))
    have hβJ : y'' + m ∉ β.jumps := fun h => hE'' (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩))))
    have hFy : y'' + m ∉ Fy := fun h => hE'' (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y'' + m, h, by ring⟩)))
    have hwl := hw y'' h1 h2 hcwJ
    rw [hwl, hcw y'' hFw] at hbad
    rcases hSy (y'' + m) hβJ hFy with ⟨-, hmy⟩ | ⟨x, hxS, hxy⟩
    · exfalso
      linarith
    · have hxJ : x ∉ jumps := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_left _ h, by rw [hxy]; ring⟩))
      have hxF : x ∉ Fx := fun h => hE'' (Finset.mem_union_right _ (Finset.mem_image.2
        ⟨x, Finset.mem_union_right _ h, by rw [hxy]; ring⟩))
      have hzJ : rProf c x ∉ β.jumps := by rw [hxy]; exact hβJ
      have hbx : β.fn (rProf c x) = b x := hSo x hxS hxJ hxF hzJ
      have hxu : x < u := hSl x hxS (by rw [hxy]; linarith)
      refine ⟨x, Or.inr ⟨hxu, ?_⟩, ?_⟩
      · rw [leftLim_eq_of_notMem hb hxJ, ← hbx, hxy]
        exact hbad
      · have h1 := bdry_eq_of_chartFree hcc hgc hgi (hSc x hxS).1 (hSc x hxS).2 (hc x)
        rw [hc.eq_ofReal x, hxy] at h1
        exact h1
  have hev : ∀ᶠ y'' in 𝓝[<] y, ∃ x ∈ badSet κ ψ u b, g ((y'' + m : ℝ) : ℂ) = (x : ℂ) := by
    have h1 : ∀ᶠ y'' in 𝓝[<] y, y₁ < y'' := (lt_mem_nhds hy₁).filter_mono nhdsWithin_le_nhds
    have h2 : ∀ᶠ y'' in 𝓝[<] y, y'' ∉ (E : Set ℝ) :=
      (eventually_notMem_of_finite E.finite_toSet y).filter_mono (nhdsWithin_mono _ fun z hz => ne_of_lt hz)
    filter_upwards [self_mem_nhdsWithin, h1, h2] with y'' hy'' hy''₁ hy''E
    exact hgood y'' hy''₁ hy'' hy''E
  obtain ⟨x₀, hx₀, hcl⟩ := exists_real_mem_closure_of_tendsto
    (tendsto_g_real (m := m) hgc (𝓝[<] y) nhdsWithin_le_nhds) hev
  exact ⟨x₀, hx₀, hcl⟩

end Corr

/-! ### No relative threshold while the read-back stays good -/

/-- **E7, first direction** (deterministic): if, at every relative time before `V`, the read-back `g (Γ s + m)` of the
relative tip is not a real point of the closure of the bad set, then the relative driver has no continuation threshold
before `V`: `V ≤ thr`. -/
theorem le_thr_of_good {Ω : Type*} {κ ψ u m : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hψ : -(Real.pi / 2) < ψ)
    {b : ℝ → ℝ} {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {c : Chart}
    (hcc : c.IsConformal) {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    {β : BoundaryWord} (hSC : SecondClause κ b jumps c u m β.fn β.jumps) {cw : BoundaryWord} {Fw : Finset ℝ}
    (hcw : ∀ y ∉ Fw, cw.fn y = β.fn (y + m)) {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {W : ℝ≥0 → Ω → ℝ} {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {ω : Ω}
    (hft : FCDet.IsFlowType κ ψ cw (xL ω) (xR ω) ρL ρR) (hWc : Continuous fun t => W t ω) (hW0 : W 0 ω = 0)
    {V : ℝ≥0∞} {Γ : ℝ≥0 → ℂ} (hΓ : IsGeneratingTrace (fun t => W t ω) V Γ)
    (hgood : ∀ s : ℝ≥0, (s : ℝ≥0∞) < V → ∀ x : ℝ, g (Γ s + (m : ℂ)) = x → x ∉ closure (badSet κ ψ u b)) :
    V ≤ FCDet.thr ρL ρR W xL xR ω := by
  have hsigns := RetAux79.isFlowType_signs hft
  have hno : ∀ t : ℝ≥0, (t : ℝ≥0∞) < V → ¬ ForceWord.ThresholdCondition ρL ρR (W t ω)
      (fun i => geomLW W xL i t ω) (fun j => geomRW W xR j t ω) := by
    intro t ht hTC
    rcases hTC with hL | hR
    · obtain ⟨him, hre, hbad⟩ := tip_bad_left_of_threshold hWc hW0 hΓ hsigns.1 ht.le hL
      obtain ⟨x₀, hx₀, hcl⟩ := phys_bad_left hκ hb hcc hgc hgi hSC hcw hft hre hbad
      have hΓt : Γ t + (m : ℂ) = (((Γ t).re + m : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      exact hgood t ht x₀ (by rw [hΓt]; exact hx₀) hcl
    · obtain ⟨him, hre, hbad⟩ := tip_bad_right_of_threshold hWc hW0 hΓ hsigns.2 ht.le hR
      obtain ⟨x₀, hx₀, hcl⟩ := phys_bad_right hκ hκ4 hψ hb hcc hgc hgi hSC hcw hft hre hbad
      have hΓt : Γ t + (m : ℂ) = (((Γ t).re + m : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      exact hgood t ht x₀ (by rw [hΓt]; exact hx₀) hcl
  unfold FCDet.thr MartChar.thresholdTime
  split_ifs with hne
  · by_contra hlt
    push Not at hlt
    obtain ⟨r, hr1, hr2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hlt
    obtain ⟨t, htS, htr⟩ := (csInf_lt_iff (OrderBot.bddBelow _) hne).1 (ENNReal.coe_lt_coe.1 hr1)
    exact hno t ((ENNReal.coe_lt_coe.2 htr).trans hr2) htS
  · exact le_top

end InteractingSLE.Theorem14.SB.Wf

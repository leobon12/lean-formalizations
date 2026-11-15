/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowProbTransfer
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Foundations.Loewner.Capacity
import InteractingSLE.Foundations.Loewner.CapacityEstimates
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.RS.GenerationCor
import QuantumZipper.Proofs.Thm18.G1PkgTrace

/-!
# Aux. lemma 126: a countable characterization of a generating trace

Packet PROVE-T14-IN. Aux. lemma 126's proof (`source/spec/p385-432.md`, pp. 399–400) codes the stopped-trace event
by countably many conditions: "At each rational time the inverse Loewner map, and its vertical tip limit along `1/n`
when it exists, are measurable functions of that history … Existence of a continuous extension is a countable uniform
continuity condition, and equality of its filled hulls with the driving hulls can be checked at rational times by
their complements and a countable rational planar basis."

This file proves the deterministic half. For a continuous driver `w` with `w 0 = 0` and a finite horizon `S`,
`exists_isGeneratingTrace_iff_traceCond` shows that a continuous generating trace through `S` (the frozen
`IsGeneratingTrace`) exists iff the measurable tip values `τ p = LP.traceAt p w` at rational times `p < S` satisfy
`TraceCond`:

* **(C1)** `p ↦ τ p` is uniformly continuous on the rational times below `S`;
* **(C2a)** at each rational `q < S`, every rational tip value `τ p` (`p ≤ q`) that lies in `ℍ` lies in `K_q`;
* **(C2b)** at each rational `q < S`, every rational closed disc `B̄(c, ε) ⊂ ℍ` at distance more than `3ε` from the
  rational tip values up to `q` lies inside `K_q` or misses it. This says that the frontier of `K_q` in `ℍ` lies in
  the closed trace range, which is the comparison "by complements and a countable rational planar basis".

The hulls at irrational times follow from the rational ones by right-continuity of `K_t`, and by the corresponding
continuity of the filling of `η([0, t])`. The measurability half is in `CounterflowProb2Coding.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal NNRat

open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Sec7

namespace Coding

/-! ### Rational points and rational times -/

/-- The rational point `x + y i` of `ℂ`. -/
def ratPt (c : ℚ × ℚ) : ℂ := ⟨c.1, c.2⟩

@[simp] theorem ratPt_re (c : ℚ × ℚ) : (ratPt c).re = c.1 := rfl

@[simp] theorem ratPt_im (c : ℚ × ℚ) : (ratPt c).im = c.2 := rfl

/-- Rational points are dense in `ℂ`. -/
theorem exists_dist_ratPt_lt (z : ℂ) {r : ℝ} (hr : 0 < r) : ∃ c : ℚ × ℚ, dist z (ratPt c) < r := by
  obtain ⟨x, hx1, hx2⟩ := exists_rat_btwn (show z.re - r / 2 < z.re by linarith)
  obtain ⟨y, hy1, hy2⟩ := exists_rat_btwn (show z.im - r / 2 < z.im by linarith)
  refine ⟨(x, y), ?_⟩
  rw [Complex.dist_eq]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  simp only [Complex.sub_re, Complex.sub_im, ratPt_re, ratPt_im]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

/-- A nonnegative rational strictly between two nonnegative reals. -/
theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨q, hq0, h1, h2⟩ := (NNReal.lt_iff_exists_rat_btwn a b).1 h
  have e : ((q.toNNRat : ℚ≥0) : ℝ≥0) = Real.toNNReal q := by
    ext
    rw [Real.coe_toNNReal _ (Rat.cast_nonneg.2 hq0)]
    have h3 : (((q.toNNRat : ℚ≥0) : ℝ≥0) : ℝ) = ((q.toNNRat : ℚ) : ℝ) := by norm_cast
    rw [h3, Rat.coe_toNNRat q hq0]
  exact ⟨q.toNNRat, e ▸ h1, e ▸ h2⟩

/-- A rational time in `(t, t + δ)` below a horizon `S > t`. -/
theorem exists_nnrat_gt_lt {t : ℝ≥0} {S : ℝ≥0∞} (h : (t : ℝ≥0∞) < S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ ((q : ℝ≥0) : ℝ≥0∞) < S ∧ ((q : ℝ≥0) : ℝ) < t + δ := by
  obtain ⟨s, hts, hsS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  set u : ℝ≥0 := min s (t + (δ / 2).toNNReal) with hu
  have htu : t < u := lt_min (by exact_mod_cast hts)
    (lt_add_of_pos_right t (Real.toNNReal_pos.2 (half_pos hδ)))
  obtain ⟨q, hq1, hq2⟩ := exists_nnrat_btwn htu
  refine ⟨q, hq1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ((hq2.le).trans (min_le_left _ _))) hsS, ?_⟩
  have h3 : ((q : ℝ≥0) : ℝ) < (u : ℝ) := hq2
  have h4 : (u : ℝ) ≤ t + δ / 2 := by
    have := min_le_right s (t + (δ / 2).toNNReal)
    rw [← hu] at this
    have h5 : (u : ℝ) ≤ ((t + (δ / 2).toNNReal : ℝ≥0) : ℝ) := this
    rw [NNReal.coe_add, Real.coe_toNNReal _ (by linarith)] at h5
    exact h5
  linarith

/-! ### Connected sets, frontiers and fillings -/

/-- A preconnected set that misses the frontier of `K` lies in `K` or misses it. -/
theorem subset_or_disjoint_of_inter_frontier {X : Type*} [TopologicalSpace X] {U K : Set X}
    (hU : IsPreconnected U) (h : ∀ x ∈ U, x ∉ frontier K) : U ⊆ K ∨ Disjoint U K := by
  have hcover : U ⊆ interior K ∪ interior Kᶜ := by
    intro x hx
    by_cases hxc : x ∈ closure K
    · left
      by_contra hxi
      exact h x hx ⟨hxc, hxi⟩
    · right
      rw [interior_compl]
      exact hxc
  have hdisj : Disjoint (interior K) (interior Kᶜ) :=
    Disjoint.mono interior_subset interior_subset disjoint_compl_right
  rcases hU.subset_or_subset isOpen_interior isOpen_interior hdisj hcover with h1 | h1
  · exact Or.inl (h1.trans interior_subset)
  · exact Or.inr (Set.disjoint_left.2 fun x hx hxK => interior_subset (h1 hx) hxK)

/-- A nonempty preconnected subset of `ℍ \ closure A` lies in the filling of `A` or misses it. -/
theorem subset_fillH_or_disjoint {A B : Set ℂ} (hB : IsPreconnected B) (hBne : B.Nonempty)
    (hBA : B ⊆ H \ closure A) : B ⊆ fillH A ∨ Disjoint B (fillH A) := by
  obtain ⟨z, hz⟩ := hBne
  set C := connectedComponentIn (H \ closure A) z with hC
  have hBC : B ⊆ C := hB.subset_connectedComponentIn hz hBA
  have hcomp : ∀ y ∈ B, connectedComponentIn (H \ closure A) y = C := fun y hy =>
    (connectedComponentIn_eq (hBC hy)).symm
  by_cases hCb : Bornology.IsBounded C
  · left
    intro y hy
    exact ⟨(hBA hy).1, Or.inr (by rw [hcomp y hy]; exact hCb)⟩
  · right
    refine Set.disjoint_left.2 fun y hy hyF => ?_
    rcases hyF.2 with h1 | h1
    · exact (hBA hy).2 h1
    · rw [hcomp y hy] at h1
      exact hCb h1

/-- `ℍ` is unbounded. -/
theorem not_isBounded_H : ¬ Bornology.IsBounded H := by
  intro h
  obtain ⟨R, hR⟩ := h.subset_closedBall 0
  have hmem : ((max R 0 + 1 : ℝ) : ℂ) * Complex.I ∈ H := by
    show 0 < (((max R 0 + 1 : ℝ) : ℂ) * Complex.I).im
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero]
    positivity
  have h1 := hR hmem
  rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  linarith [le_max_left R 0]

/-- **A hull with frontier in a compact set `Γ` is the filling of `Γ`.** If `K ⊆ ℍ` is bounded, `ℍ \ K` is open and
preconnected, `Γ ∩ ℍ ⊆ K`, and the frontier of `K` in `ℍ` lies in `Γ`, then `K` is the filling of `Γ`. -/
theorem eq_fillH_of_frontier_subset {K Γ : Set ℂ} (hΓ : IsClosed Γ) (hKH : K ⊆ H)
    (hKb : Bornology.IsBounded K) (hKc : IsPreconnected (H \ K)) (ha : Γ ∩ H ⊆ K)
    (hb : frontier K ∩ H ⊆ Γ) : K = fillH Γ := by
  have hsub : H \ K ⊆ H \ Γ := fun y hy => ⟨hy.1, fun hyΓ => hy.2 (ha ⟨hyΓ, hy.1⟩)⟩
  ext z
  constructor
  · intro hzK
    refine ⟨hKH hzK, ?_⟩
    by_cases hzΓ : z ∈ closure Γ
    · exact Or.inl hzΓ
    right
    rw [hΓ.closure_eq] at hzΓ
    by_contra hCb
    set C := connectedComponentIn (H \ closure Γ) z with hC
    have hCo : IsOpen C := ((QuantumZipper.isOpen_H).sdiff isClosed_closure).connectedComponentIn
    have hCH : C ⊆ H \ Γ := by
      rw [hC, hΓ.closure_eq]; exact connectedComponentIn_subset _ _
    have hzC : z ∈ C := mem_connectedComponentIn (by rw [hΓ.closure_eq]; exact ⟨hKH hzK, hzΓ⟩)
    have hyout : ∃ y ∈ C, y ∉ K := by
      by_contra hall
      push Not at hall
      exact hCb (hKb.subset hall)
    have hfr := subset_or_disjoint_of_inter_frontier (K := K) (isPreconnected_connectedComponentIn)
      (U := C) (fun x hx hxf => (hCH hx).2 (hb ⟨hxf, (hCH hx).1⟩))
    rcases hfr with h1 | h1
    · obtain ⟨y, hyC, hyK⟩ := hyout
      exact hyK (h1 hyC)
    · exact Set.disjoint_left.1 h1 hzC hzK
  · rintro ⟨hzH, hz⟩
    rcases hz with hzΓ | hzb
    · rw [hΓ.closure_eq] at hzΓ
      exact ha ⟨hzΓ, hzH⟩
    · by_contra hzK
      rw [hΓ.closure_eq] at hzb
      have h1 : H \ K ⊆ connectedComponentIn (H \ Γ) z :=
        hKc.subset_connectedComponentIn ⟨hzH, hzK⟩ hsub
      have h2 : Bornology.IsBounded (H \ K) := hzb.subset h1
      exact not_isBounded_H ((h2.union hKb).subset fun y hy => by
        by_cases hyK : y ∈ K
        · exact Or.inr hyK
        · exact Or.inl ⟨hy, hyK⟩)

/-! ### The countable trace conditions -/

/-- **The countable trace conditions** (Aux. lemma 126's coding, pp. 399–400) for a driver `W` on `ℝ`, tip values
`τ`, and the predicate `L` of available rational times:
* (C1) `τ` is uniformly continuous on the available rational times;
* (C2a) at an available rational time `q`, the rational tip values up to `q` that lie in `ℍ` lie in `K_q`;
* (C2b) at an available rational time `q`, every rational closed disc `B̄(c, ε)` with `2ε < Im c` and at distance more
  than `3ε` from the rational tip values up to `q` lies in `K_q` or misses it. -/
def TraceCond (W : ℝ → ℝ) (τ : ℝ≥0 → ℂ) (L : ℚ≥0 → Prop) : Prop :=
  (∀ m : ℕ, ∃ k : ℕ, ∀ p p' : ℚ≥0, L p → L p' → dist (p : ℝ≥0) (p' : ℝ≥0) < 1 / ((k : ℝ) + 1) →
      dist (τ p) (τ p') ≤ 1 / ((m : ℝ) + 1)) ∧
  ∀ q : ℚ≥0, L q →
    (∀ p : ℚ≥0, p ≤ q → τ p ∈ H → τ p ∈ fwdHull W ((q : ℝ≥0) : ℝ)) ∧
    ∀ (ε : ℚ) (c : ℚ × ℚ), 0 < ε → 2 * (ε : ℝ) < c.2 →
      (∀ p : ℚ≥0, p ≤ q → 3 * (ε : ℝ) < dist (ratPt c) (τ p)) →
      closedBall (ratPt c) ε ⊆ fwdHull W ((q : ℝ≥0) : ℝ) ∨
        Disjoint (closedBall (ratPt c) ε) (fwdHull W ((q : ℝ≥0) : ℝ))

/-! ### Rational times are dense -/

/-- The rational times of `[0, q]`. -/
def ratTimesLE (q : ℝ≥0) : Set ℝ≥0 := {x | ∃ p : ℚ≥0, (p : ℝ≥0) ≤ q ∧ (p : ℝ≥0) = x}

theorem Icc_subset_closure_ratTimesLE {q : ℝ≥0} (hq : ∃ p : ℚ≥0, (p : ℝ≥0) = q) :
    Icc 0 q ⊆ closure (ratTimesLE q) := by
  intro x hx
  rcases eq_or_lt_of_le hx.2 with hxq | hxq
  · obtain ⟨p, rfl⟩ := hq
    exact subset_closure ⟨p, le_rfl, hxq.symm⟩
  · rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨p, h1, h2, h3⟩ := exists_nnrat_gt_lt (t := x) (S := (q : ℝ≥0∞))
      (ENNReal.coe_lt_coe.2 hxq) hε
    refine ⟨p, ⟨p, (ENNReal.coe_lt_coe.1 h2).le, rfl⟩, ?_⟩
    have h1' : (x : ℝ) < ((p : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 h1
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 h1')]
    linarith

/-- The image of `[0, q]` under a continuous `η` lies in the closure of its rational values. -/
theorem image_Icc_subset_closure {η : ℝ≥0 → ℂ} {q : ℝ≥0} (hη : ContinuousOn η (Icc 0 q))
    (hq : ∃ p : ℚ≥0, (p : ℝ≥0) = q) : η '' Icc 0 q ⊆ closure (η '' ratTimesLE q) := by
  rintro _ ⟨x, hx, rfl⟩
  have hsub : ratTimesLE q ⊆ Icc 0 q := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨bot_le, hp⟩
  exact ((hη x hx).mono hsub).mem_closure_image (Icc_subset_closure_ratTimesLE hq hx)

/-! ### The hull at a rational time -/

/-- **(C2) gives the hull at one time.** If the countable set `T` of tip values is dense in the closed set `Γ`, every
point of `T` in `ℍ` lies in `K_q`, and every rational disc far from `T` lies in `K_q` or misses it, then `K_q` is the
filling of `Γ`. -/
theorem fwdHull_eq_fillH_of_cond {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q : ℝ} (hq : 0 ≤ q)
    {Γ T : Set ℂ} (hΓ : IsClosed Γ) (hTΓ : Γ ⊆ closure T) (hTsub : T ⊆ Γ)
    (ha : ∀ z ∈ T, z ∈ H → z ∈ fwdHull W q)
    (hb : ∀ (ε : ℚ) (c : ℚ × ℚ), 0 < ε → 2 * (ε : ℝ) < c.2 → (∀ z ∈ T, 3 * (ε : ℝ) < dist (ratPt c) z) →
      closedBall (ratPt c) ε ⊆ fwdHull W q ∨ Disjoint (closedBall (ratPt c) ε) (fwdHull W q)) :
    fwdHull W q = fillH Γ := by
  set K := fwdHull W q with hK
  have hKH : K ⊆ H := QuantumZipper.fwdHull_mono.2 q
  have hF : IsClosed (K ∪ Hᶜ) := by
    have := (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hq).isClosed_compl
    rwa [Set.compl_sdiff] at this
  refine eq_fillH_of_frontier_subset hΓ hKH (isBounded_fwdHull hW q)
    (QuantumZipper.RS.isPreconnected_compl_fwdHull hW hW0 hq) ?_ ?_
  · rintro z ⟨hzΓ, hzH⟩
    have hTF : T ⊆ K ∪ Hᶜ := fun y hy => by
      by_cases hyH : y ∈ H
      · exact Or.inl (ha y hy hyH)
      · exact Or.inr hyH
    rcases hF.closure_subset_iff.2 hTF (hTΓ hzΓ) with h | h
    · exact h
    · exact absurd hzH h
  · rintro y ⟨hyf, hyH⟩
    by_contra hyΓ
    obtain ⟨δ, hδ, hδb⟩ := Metric.isOpen_iff.1 hΓ.isOpen_compl y hyΓ
    have hδΓ : ∀ z ∈ Γ, δ ≤ dist y z := fun z hz => by
      by_contra hlt
      exact hδb (by rw [mem_ball, dist_comm]; exact lt_of_not_ge hlt) hz
    have hyim : 0 < y.im := hyH
    obtain ⟨ε, hε0, hε⟩ := exists_rat_btwn (lt_min (div_pos hδ (by norm_num : (0 : ℝ) < 4))
      (div_pos hyim (by norm_num : (0 : ℝ) < 3)))
    have hε4 : 4 * (ε : ℝ) < δ := by linarith [min_le_left (δ / 4) (y.im / 3)]
    have hε3 : 3 * (ε : ℝ) < y.im := by linarith [min_le_right (δ / 4) (y.im / 3)]
    obtain ⟨c, hc⟩ := exists_dist_ratPt_lt y (half_pos hε0)
    have hcim : 2 * (ε : ℝ) < c.2 := by
      have h1 := Complex.abs_im_le_norm (y - ratPt c)
      rw [← Complex.dist_eq, Complex.sub_im, ratPt_im] at h1
      have h2 := (abs_le.1 h1).2
      linarith
    have hfar : ∀ z ∈ T, 3 * (ε : ℝ) < dist (ratPt c) z := fun z hz => by
      have h1 := hδΓ z (hTsub hz)
      have h2 := dist_triangle y (ratPt c) z
      linarith
    have hball : ball y (ε / 2) ⊆ closedBall (ratPt c) ε := fun x hx => by
      rw [mem_closedBall]
      have h1 := dist_triangle x y (ratPt c)
      rw [mem_ball] at hx
      linarith
    rcases hb ε c (by exact_mod_cast hε0) hcim hfar with h | h
    · exact hyf.2 (mem_interior_iff_mem_nhds.2
        (Filter.mem_of_superset (ball_mem_nhds y (half_pos (by exact_mod_cast hε0))) (hball.trans h)))
    · obtain ⟨x, hxK, hxy⟩ := Metric.mem_closure_iff.1 hyf.1 (ε / 2) (half_pos (by exact_mod_cast hε0))
      exact Set.disjoint_left.1 h (hball (by rw [mem_ball, dist_comm]; exact hxy)) hxK

/-! ### Right-continuity of the hulls and of the fillings -/

/-- **Right-continuity of the hulls**: a point swallowed at every rational time in `(t, S)` is swallowed at `t`. -/
theorem mem_fwdHull_of_forall_gt {W : ℝ → ℝ} {t : ℝ≥0} {S : ℝ≥0∞} (htS : (t : ℝ≥0∞) < S) {z : ℂ}
    (hz : z ∈ H)
    (h : ∀ q : ℚ≥0, t < (q : ℝ≥0) → ((q : ℝ≥0) : ℝ≥0∞) < S → z ∈ fwdHull W ((q : ℝ≥0) : ℝ)) :
    z ∈ fwdHull W t := by
  refine ⟨hz, ?_⟩
  by_contra hlt
  rw [not_le, ENNReal.ofReal_coe_nnreal] at hlt
  obtain ⟨q, hq1, hq2, -⟩ := exists_nnrat_gt_lt (lt_min htS hlt) one_pos
  have hqz := (h q hq1 (lt_of_lt_of_le hq2 (min_le_left _ _))).2
  rw [ENNReal.ofReal_coe_nnreal] at hqz
  exact absurd (lt_of_lt_of_le hq2 (min_le_right _ _)) (not_lt.2 hqz)

/-- **Right-continuity of the fillings of a continuous curve**: a point of `ℍ` outside the filling of `η([0, t])`
stays outside the filling of `η([0, s])` for all `s ∈ [t, t + δ')`. -/
theorem exists_forall_not_mem_fillH {η : ℝ≥0 → ℂ} {b t : ℝ≥0} (hη : ContinuousOn η (Icc 0 b)) (htb : t ≤ b)
    {z : ℂ} (hz : z ∈ H) (hzt : z ∉ fillH (η '' Icc 0 t)) :
    ∃ δ' > (0 : ℝ), ∀ s : ℝ≥0, t ≤ s → s ≤ b → (s : ℝ) < t + δ' → z ∉ fillH (η '' Icc 0 s) := by
  have hcpt : ∀ s ≤ b, IsCompact (η '' Icc 0 s) := fun s hs =>
    isCompact_Icc.image_of_continuousOn (hη.mono (Icc_subset_Icc_right hs))
  set Γt := η '' Icc 0 t with hΓt
  have hΓtc : IsClosed Γt := (hcpt t htb).isClosed
  obtain ⟨R₀, hR₀⟩ := (hcpt b le_rfl).isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0 + 1 with hR
  have hRpos : 0 < R := by positivity
  have hΓR : ∀ s ≤ b, closure (η '' Icc 0 s) ⊆ ball 0 R := fun s hs => by
    rw [(hcpt s hs).isClosed.closure_eq]
    intro x hx
    have h1 := hR₀ (image_mono (Icc_subset_Icc_right hs) hx)
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_ball, dist_zero_right]
    linarith [le_max_left R₀ 0]
  have hzΓ : z ∉ closure Γt := fun h => hzt ⟨hz, Or.inl h⟩
  set U := connectedComponentIn (H \ closure Γt) z with hU
  have hUb : ¬ Bornology.IsBounded U := fun h => hzt ⟨hz, Or.inr h⟩
  have hzU : z ∈ U := mem_connectedComponentIn ⟨hz, hzΓ⟩
  have hUo : IsOpen U := (QuantumZipper.isOpen_H.sdiff isClosed_closure).connectedComponentIn
  have hUsub : U ⊆ H \ closure Γt := connectedComponentIn_subset _ _
  obtain ⟨z', hz'U, hz'R⟩ : ∃ z' ∈ U, R ≤ ‖z'‖ := by
    by_contra hall
    push Not at hall
    exact hUb ((isBounded_ball (x := (0 : ℂ)) (r := R)).subset fun x hx => by
      rw [mem_ball, dist_zero_right]; exact hall x hx)
  have hUconn : IsConnected U := isConnected_connectedComponentIn_iff.2 ⟨hz, hzΓ⟩
  obtain ⟨γ, hγ⟩ := (hUo.isConnected_iff_isPathConnected.1 hUconn).joinedIn z hzU z' hz'U
  set P := Set.range γ with hP
  have hPU : P ⊆ U := by rintro _ ⟨u, rfl⟩; exact hγ u
  have hPc : IsCompact P := isCompact_range γ.continuous
  have hΓne : Γt.Nonempty := ⟨η 0, 0, ⟨le_rfl, bot_le⟩, rfl⟩
  obtain ⟨x₀, hx₀P, hx₀min⟩ := hPc.exists_isMinOn ⟨z, ⟨0, γ.source⟩⟩
    (continuous_infDist_pt Γt).continuousOn
  set δ := infDist x₀ Γt with hδdef
  have hδ : 0 < δ := by
    have hx₀ : x₀ ∉ Γt := fun h => (hUsub (hPU hx₀P)).2 (subset_closure h)
    exact (hΓtc.notMem_iff_infDist_pos hΓne).1 hx₀
  have hPΓ : ∀ x ∈ P, ∀ y ∈ Γt, δ ≤ dist x y := fun x hx y hy =>
    (isMinOn_iff.1 hx₀min x hx).trans (infDist_le_dist_of_mem hy)
  obtain ⟨δ', hδ', hcont⟩ := Metric.continuousOn_iff.1 hη t ⟨bot_le, htb⟩ (δ / 2) (half_pos hδ)
  refine ⟨δ', hδ', fun s hts hsb hsδ => ?_⟩
  set Γs := η '' Icc 0 s with hΓs
  have hPs : P ⊆ H \ closure Γs := by
    intro x hx
    refine ⟨(hUsub (hPU hx)).1, ?_⟩
    rw [(hcpt s hsb).isClosed.closure_eq]
    rintro ⟨s', hs', hxs'⟩
    by_cases hs't : s' ≤ t
    · have := hPΓ x hx (η s') ⟨s', ⟨bot_le, hs't⟩, rfl⟩
      rw [hxs', dist_self] at this
      linarith
    · push Not at hs't
      have hd : dist s' t < δ' := by
        have hs't' : (t : ℝ) < (s' : ℝ) := NNReal.coe_lt_coe.2 hs't
        rw [NNReal.dist_eq, abs_of_pos (sub_pos.2 hs't')]
        have : (s' : ℝ) ≤ s := hs'.2
        linarith
      have h1 := hcont s' ⟨bot_le, hs'.2.trans hsb⟩ hd
      have h2 := hPΓ x hx (η t) ⟨t, ⟨bot_le, le_rfl⟩, rfl⟩
      have h4 : dist x (η t) < δ / 2 := by rw [← hxs']; exact h1
      linarith
  have hz'cc : z' ∈ connectedComponentIn (H \ closure Γs) z :=
    (isPreconnected_range γ.continuous).subset_connectedComponentIn ⟨0, γ.source⟩ hPs ⟨1, γ.target⟩
  have hz'R' : z' ∈ connectedComponentIn (H \ closure Γs) (((R + 1 : ℝ) : ℂ) * Complex.I) :=
    mem_connectedComponentIn_of_le_norm hRpos (hΓR s hsb) (hUsub hz'U).1 hz'R
  have hzmem : z ∈ H \ fillH Γs := by
    rw [H_diff_fillH hRpos (hΓR s hsb), connectedComponentIn_eq hz'R', ← connectedComponentIn_eq hz'cc]
    exact mem_connectedComponentIn (hPs ⟨0, γ.source⟩)
  exact hzmem.2

/-! ### The continuous extension of the rational tip values -/

/-- The available rational times below `b`, as a subset of `ℝ≥0`. -/
def ratTimesLT (b : ℝ≥0) : Set ℝ≥0 := {x | ∃ p : ℚ≥0, (p : ℝ≥0) < b ∧ (p : ℝ≥0) = x}

theorem Icc_subset_closure_ratTimesLT {b : ℝ≥0} (hb : 0 < b) : Icc 0 b ⊆ closure (ratTimesLT b) := by
  have h1 : Iio b ⊆ closure (ratTimesLT b) := by
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨p, h1, h2, h3⟩ := exists_nnrat_gt_lt (t := x) (S := (b : ℝ≥0∞)) (ENNReal.coe_lt_coe.2 hx) hε
    refine ⟨p, ⟨p, ENNReal.coe_lt_coe.1 h2, rfl⟩, ?_⟩
    have h1' : (x : ℝ) < ((p : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 h1
    rw [NNReal.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.2 h1')]
    linarith
  have h2 : closure (Iio b) = Icc 0 b := by
    have := closure_Iio' (a := b) ⟨0, hb⟩
    rw [this]
    ext x; simp
  rw [← h2]
  exact closure_minimal h1 isClosed_closure

/-- **The continuous extension** (C1 ⇒ a continuous trace): if `τ` is uniformly continuous on the rational times
below `b > 0`, there is `η` continuous on `[0, b]` that agrees with `τ` at those times. -/
theorem exists_continuousOn_extension {τ : ℝ≥0 → ℂ} {b : ℝ≥0} (hb : 0 < b)
    (h1 : ∀ m : ℕ, ∃ k : ℕ, ∀ p p' : ℚ≥0, (p : ℝ≥0) < b → (p' : ℝ≥0) < b →
      dist (p : ℝ≥0) (p' : ℝ≥0) < 1 / ((k : ℝ) + 1) → dist (τ p) (τ p') ≤ 1 / ((m : ℝ) + 1)) :
    ∃ η : ℝ≥0 → ℂ, ContinuousOn η (Icc 0 b) ∧ ∀ p : ℚ≥0, (p : ℝ≥0) < b → η p = τ p := by
  set D := ratTimesLT b with hD
  have hcl := Icc_subset_closure_ratTimesLT hb
  have hclose : ∀ ε > (0 : ℝ), ∃ r > (0 : ℝ), ∀ x ∈ D, ∀ y ∈ D, dist x y < r → dist (τ x) (τ y) < ε := by
    intro ε hε
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk⟩ := h1 m
    refine ⟨1 / ((k : ℝ) + 1), by positivity, ?_⟩
    rintro _ ⟨p, hp, rfl⟩ _ ⟨p', hp', rfl⟩ hd
    exact (hk p p' hp hp' hd).trans_lt hm
  have hlim : ∀ x ∈ Icc 0 b, ∃ y, Tendsto τ (𝓝[D] x) (𝓝 y) := by
    intro x hx
    have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (hcl hx)
    refine cauchy_map_iff_exists_tendsto.1 (Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩)
    obtain ⟨r, hr, hrε⟩ := hclose ε hε
    refine ⟨τ '' (D ∩ ball x (r / 2)), image_mem_map (inter_mem_nhdsWithin D (ball_mem_nhds x
      (half_pos hr))), ?_⟩
    rintro _ ⟨y, ⟨hyD, hyx⟩, rfl⟩ _ ⟨y', ⟨hy'D, hy'x⟩, rfl⟩
    refine hrε y hyD y' hy'D ?_
    rw [mem_ball] at hyx hy'x
    linarith [dist_triangle_right y y' x]
  refine ⟨extendFrom D τ, continuousOn_extendFrom hcl hlim, fun p hp => ?_⟩
  refine extendFrom_eq (subset_closure ⟨p, hp, rfl⟩) (Metric.tendsto_nhdsWithin_nhds.2 fun ε hε => ?_)
  obtain ⟨r, hr, hrε⟩ := hclose ε hε
  exact ⟨r, hr, fun y hy hyp => hrε y hy p ⟨p, hp, rfl⟩ hyp⟩

/-- The tip value at time `0` is the seed. -/
theorem traceAt_zero {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) : LP.traceAt 0 w = 0 := by
  have hW : Continuous fun r : ℝ => w r.toNNReal := hw.comp continuous_real_toNNReal
  rw [LP.traceAt_eq_trace (s₂ := 1) (by norm_num) hw.continuousOn hw0, NNReal.coe_zero,
    QuantumZipper.Thm18Asm.G1Pkg.trace_zero_time hW]
  simp [hw0]

/-! ### The characterization -/

/-- **A continuous generating trace through a finite horizon `S` exists iff the countable trace conditions hold**
(Aux. lemma 126's proof, pp. 399–400), for a continuous driver `w` with `w 0 = 0`. -/
theorem exists_isGeneratingTrace_iff_traceCond {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {S : ℝ≥0∞} (hS : S ≠ ⊤) :
    (∃ η, IsGeneratingTrace w S η) ↔
      TraceCond (fun s : ℝ => w s.toNNReal) (fun p => LP.traceAt p w)
        (fun p => ((p : ℝ≥0) : ℝ≥0∞) < S) := by
  obtain ⟨b, rfl⟩ : ∃ b : ℝ≥0, S = b := ⟨S.toNNReal, (ENNReal.coe_toNNReal hS).symm⟩
  set W : ℝ → ℝ := fun s : ℝ => w s.toNNReal with hWdef
  have hW : Continuous W := hw.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  have hIcc : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (b : ℝ≥0∞)} = Icc 0 b := by
    ext t; simp
  have hrat : ∀ q : ℚ≥0, ∃ p : ℚ≥0, (p : ℝ≥0) = (q : ℝ≥0) := fun q => ⟨q, rfl⟩
  constructor
  · rintro ⟨η, hη⟩
    have hηc : ContinuousOn η (Icc 0 b) := hIcc ▸ hη.2.1
    have hτ : ∀ p : ℝ≥0, (p : ℝ≥0∞) < b → LP.traceAt p w = η p := fun p hp =>
      LP.traceAt_eq_of_isGeneratingTrace hη hw.continuousOn hw0 hp
    refine ⟨fun m => ?_, fun q hq => ?_⟩
    · obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuousOn_iff.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hηc) (1 / ((m : ℝ) + 1)) (by positivity)
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδ
      refine ⟨k, fun p p' hp hp' hd => ?_⟩
      show dist (LP.traceAt p w) (LP.traceAt p' w) ≤ _
      rw [hτ p hp, hτ p' hp']
      exact (hδε p ⟨bot_le, (ENNReal.coe_lt_coe.1 hp).le⟩ p' ⟨bot_le, (ENNReal.coe_lt_coe.1 hp').le⟩
        (hd.trans hk)).le
    · have hqb : (q : ℝ≥0) ≤ b := (ENNReal.coe_lt_coe.1 hq).le
      set Γ := η '' Icc 0 (q : ℝ≥0) with hΓ
      have hΓc : IsCompact Γ := isCompact_Icc.image_of_continuousOn (hηc.mono (Icc_subset_Icc_right hqb))
      have hKq : fwdHull W ((q : ℝ≥0) : ℝ) = fillH Γ :=
        (fillH_eq_iff_isFilling_of_isClosed hΓc.isBounded hΓc.isClosed
          (QuantumZipper.fwdHull_mono.2 _)).1 (hη.2.2 q hq)
      have hτq : ∀ p : ℚ≥0, p ≤ q → LP.traceAt p w = η p := fun p hp =>
        hτ p (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (by exact_mod_cast hp)) hq)
      have hΓsub := image_Icc_subset_closure (hηc.mono (Icc_subset_Icc_right hqb)) (hrat q)
      refine ⟨fun p hp hpH => ?_, fun ε c hε hc hfar => ?_⟩
      · beta_reduce at hpH ⊢
        rw [hKq]
        refine ⟨hpH, Or.inl (subset_closure ?_)⟩
        rw [hτq p hp]
        exact ⟨p, ⟨bot_le, by exact_mod_cast hp⟩, rfl⟩
      · beta_reduce at hfar
        rw [hKq]
        have hfarΓ : ∀ y ∈ Γ, 3 * (ε : ℝ) ≤ dist (ratPt c) y := by
          have hcl : IsClosed {y : ℂ | 3 * (ε : ℝ) ≤ dist (ratPt c) y} :=
            isClosed_le continuous_const (continuous_const.dist continuous_id)
          intro y hy
          refine hcl.closure_subset_iff.2 ?_ (hΓsub hy)
          rintro _ ⟨x, ⟨p, hp, rfl⟩, rfl⟩
          have hp' : p ≤ q := by exact_mod_cast hp
          have := hfar p hp'
          rw [hτq p hp'] at this
          exact this.le
        refine subset_fillH_or_disjoint (convex_closedBall _ _).isPreconnected
          ⟨ratPt c, mem_closedBall_self (by exact_mod_cast hε.le)⟩ fun x hx => ⟨?_, ?_⟩
        · rw [mem_closedBall] at hx
          have h1 := Complex.abs_im_le_norm (x - ratPt c)
          rw [← Complex.dist_eq, Complex.sub_im, ratPt_im] at h1
          have h2 := (abs_le.1 h1).1
          show 0 < x.im
          have : (0 : ℝ) < ε := by exact_mod_cast hε
          linarith
        · rw [hΓc.isClosed.closure_eq]
          intro hxΓ
          have h1 := hfarΓ x hxΓ
          rw [mem_closedBall, dist_comm] at hx
          have : (0 : ℝ) < ε := by exact_mod_cast hε
          linarith
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne b 0 with rfl | hb0
    · refine ⟨fun _ => 0, rfl, continuousOn_const, fun t ht => ?_⟩
      exact absurd ht (by simp)
    have hb : 0 < b := pos_iff_ne_zero.2 hb0
    obtain ⟨η, hηc, hητ⟩ := exists_continuousOn_extension (τ := fun p => LP.traceAt p w) hb
      fun m => by
        obtain ⟨k, hk⟩ := h1 m
        exact ⟨k, fun p p' hp hp' => hk p p' (ENNReal.coe_lt_coe.2 hp) (ENNReal.coe_lt_coe.2 hp')⟩
    have hη0 : η 0 = 0 := by
      have := hητ 0 (by exact_mod_cast hb)
      rw [NNRat.cast_zero] at this
      rw [this, traceAt_zero hw hw0]
    -- the hull at an available rational time
    have hKq : ∀ q : ℚ≥0, (q : ℝ≥0) < b → fwdHull W ((q : ℝ≥0) : ℝ) = fillH (η '' Icc 0 (q : ℝ≥0)) := by
      intro q hq
      have hqb : (q : ℝ≥0) ≤ b := hq.le
      have hτq : ∀ p : ℚ≥0, p ≤ q → LP.traceAt p w = η p := fun p hp =>
        (hητ p (lt_of_le_of_lt (by exact_mod_cast hp) hq)).symm
      obtain ⟨ha, hb'⟩ := h2 q (ENNReal.coe_lt_coe.2 hq)
      have hηq := hηc.mono (Icc_subset_Icc_right hqb)
      refine fwdHull_eq_fillH_of_cond hW hW0 (NNReal.coe_nonneg _)
        (T := η '' ratTimesLE (q : ℝ≥0))
        (isCompact_Icc.image_of_continuousOn hηq).isClosed (image_Icc_subset_closure hηq (hrat q))
        (image_mono fun x ⟨p, hp, hpx⟩ => ⟨bot_le, hpx ▸ hp⟩) ?_ ?_
      · rintro _ ⟨x, ⟨p, hp, rfl⟩, rfl⟩ hH
        have hp' : p ≤ q := by exact_mod_cast hp
        rw [← hτq p hp'] at hH ⊢
        exact ha p hp' hH
      · intro ε c hε hc hfar
        refine hb' ε c hε hc fun p hp => ?_
        show 3 * (ε : ℝ) < dist (ratPt c) (LP.traceAt p w)
        rw [hτq p hp]
        exact hfar _ ⟨p, ⟨p, by exact_mod_cast hp, rfl⟩, rfl⟩
    refine ⟨η, hη0, hIcc ▸ hηc, fun t ht => ?_⟩
    have htb : t < b := ENNReal.coe_lt_coe.1 ht
    have hΓc : IsCompact (η '' Icc 0 t) :=
      isCompact_Icc.image_of_continuousOn (hηc.mono (Icc_subset_Icc_right htb.le))
    refine (fillH_eq_iff_isFilling_of_isClosed hΓc.isBounded hΓc.isClosed
      (QuantumZipper.fwdHull_mono.2 _)).2 ?_
    ext z
    constructor
    · intro hzK
      have hzH : z ∈ H := (QuantumZipper.fwdHull_mono.2 _) hzK
      by_contra hzF
      obtain ⟨δ', hδ', hδ'F⟩ := exists_forall_not_mem_fillH hηc htb.le hzH hzF
      obtain ⟨q, hq1, hq2, hq3⟩ := exists_nnrat_gt_lt ht hδ'
      have hqb : (q : ℝ≥0) < b := ENNReal.coe_lt_coe.1 hq2
      refine hδ'F q hq1.le hqb.le hq3 ?_
      rw [← hKq q hqb]
      exact (QuantumZipper.fwdHull_mono.1 (show ((t : ℝ≥0) : ℝ) ≤ ((q : ℝ≥0) : ℝ) from hq1.le)) hzK
    · intro hzF
      refine mem_fwdHull_of_forall_gt ht hzF.1 fun q hq1 hq2 => ?_
      rw [hKq q (ENNReal.coe_lt_coe.1 hq2)]
      exact fillH_mono (image_mono (Icc_subset_Icc_right hq1.le)) hzF

end Coding

end Sec7

end InteractingSLE

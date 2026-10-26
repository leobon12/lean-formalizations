import SupercriticalLFPPAS.Local.Basic
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleTools
import SupercriticalLQGUniqueness.B2.Polylog.P4LFPPCompare
import SupercriticalLQGUniqueness.B2.Polylog.P2HeatBasic
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength
import SupercriticalLQGUniqueness.B2.PfeLocal.Length
import SupercriticalLQGUniqueness.B2.Median.Penalty
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.SampleV2

/-!
# Deterministic metric tools for Lemma 3.2 (packet P32)

Planning audit `planning/audits/SB1-sections-1-3.md` A12, steps 2 and 4–6.

* Curve lengths as partition suprema: monotonicity and scaling in the metric
  (`len_le_len_of_le`, `len_eq_mul_len`), curves of a larger metric are curves of a smaller one.
* LFPP: monotonicity in the field, constant shifts, the one-sided local length comparison
  `lfppMetric_len_ge_of_ge_on` (a field larger by `c` on an open set containing the curve
  multiplies its length by at least `e^{ξc}`), and the length-space property.
* Weyl scaling: lengths of the Weyl-scaled metric are the Weyl curve lengths of the toolkit.
* The collar confinement lemma `mem_tgtU_of_collars`: a Euclidean-continuous curve starting in
  `{1/3 ≤ |z| ≤ 6}` that leaves `U = {1/8 ≤ |z| ≤ 16}` crosses `{1/4 ≤ |z| ≤ 1/3}` or
  `{6 ≤ |z| ≤ 7}` inside the closed collar; so a curve whose length is below the cost of these
  crossings stays in `U`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LQGMetric (DistC)
open SupercriticalLQGUniqueness
open HigherDimLQGMetric (partitionSup curveLengthWith)

namespace SupercriticalLFPPAS.Local

/-! ### Curve lengths as partition suprema -/

/-- The length of a curve is the partition supremum of the metric along the curve. -/
theorem len_eq_partitionSup (D : LSCMetric) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b = partitionSup (fun u v => D (P u, P v)) a b := by
  change LQGMetric.MetricGeometry.curveLength (D.pt ∘ P) a b = _
  rw [← HigherDimLQGMetric.curveLengthWith_edist]
  rfl

/-- Lengths are monotone in the metric. -/
theorem len_le_len_of_le {D D' : LSCMetric} (h : ∀ p, D p ≤ D' p) (P : ℝ → ℂ) (a b : ℝ) :
    D.len P a b ≤ D'.len P a b := by
  rw [len_eq_partitionSup, len_eq_partitionSup]
  exact HigherDimLQGMetric.partitionSup_mono fun u v _ _ _ => h _

/-- Lengths scale with the metric. -/
theorem len_eq_mul_len {D D' : LSCMetric} (c : ℝ≥0∞) (h : ∀ p, D' p = c * D p)
    (P : ℝ → ℂ) (a b : ℝ) : D'.len P a b = c * D.len P a b := by
  rw [len_eq_partitionSup, len_eq_partitionSup, ← HigherDimLQGMetric.partitionSup_const_mul]
  congr 1
  funext u v
  exact h _

/-- A curve of a larger metric is a curve of a smaller one. -/
theorem isCurve_of_le {D D' : LSCMetric} (h : ∀ p, D p ≤ D' p) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D'.IsCurve P a b) : D.IsCurve P a b := by
  refine ⟨hP.1, ?_⟩
  let ι : D'.Space → D.Space := fun x => x
  have hL : LipschitzWith 1 ι := LipschitzWith.of_edist_le (f := ι) fun (x y : D'.Space) => h (x, y)
  exact hL.continuous.comp_continuousOn hP.2

/-- The trace of a curve in `Y` with length below `c` gives an internal distance below `c`. -/
theorem internal_lt_of_curve {D : LSCMetric} {Y : Set ℂ} {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hY : ∀ t ∈ Icc a b, P t ∈ Y) {x y : Y} (hx : P a = x)
    (hy : P b = y) {c : ℝ≥0∞} (hlen : D.len P a b < c) : D.internal Y (x, y) < c := by
  have h := B2.PfeLocal.internal_le_len D Y P a b hP hY
  have hxy : ((⟨P a, hY a ⟨le_rfl, hP.1⟩⟩ : Y), (⟨P b, hY b ⟨hP.1, le_rfl⟩⟩ : Y)) = (x, y) := by
    ext <;> simp [hx, hy]
  rw [hxy] at h
  exact lt_of_le_of_lt h hlen

/-! ### LFPP metrics -/

/-- The normalized LFPP metric is monotone in the field (`ξ ≥ 0`). -/
theorem lfppMetric_le_of_le {ξ : ℝ} (hξ : 0 ≤ ξ) (a : Set.Ioi (0 : ℝ)) {φ ψ : C(ℂ, ℝ)}
    (h : ∀ z, φ z ≤ ψ z) (p : ℂ × ℂ) :
    B2.Median.lfppMetric ξ a φ p ≤ B2.Median.lfppMetric ξ a ψ p := by
  rw [B2.Median.lfppMetric_apply, B2.Median.lfppMetric_apply]
  gcongr
  unfold lfppDistance
  refine iInf₂_mono fun P hP => ?_
  exact B2.Median.lfppLen_mono_field hξ _ _ h P

/-- Adding a constant `k` to the field multiplies the normalized LFPP metric by `e^{ξk}`. -/
theorem lfppMetric_add_const (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) {φ φ' : C(ℂ, ℝ)} (k : ℝ)
    (hφ : ∀ z, φ' z = φ z + k) (p : ℂ × ℂ) :
    B2.Median.lfppMetric ξ a φ' p =
      ENNReal.ofReal (Real.exp (ξ * k)) * B2.Median.lfppMetric ξ a φ p := by
  have h := B2.Polylog.lfppMetric_affine ξ a a (b := 0) (c := 1) one_ne_zero k
    (φ := φ) (φ' := φ') (by intro x; rw [hφ x, zero_add, one_mul]) p.1 p.2
  have ha : (0 : ℝ) < a := a.2
  simp only [zero_add, one_mul, norm_one, mul_one] at h
  rw [h]
  congr 2
  field_simp

/-- **One-sided local comparison of LFPP lengths**: if `φ' ≥ φ + c` on an open set containing a
Euclidean-continuous curve, its `φ'`-length is at least `e^{ξc}` times its `φ`-length. -/
theorem lfppMetric_len_ge_of_ge_on {ξ : ℝ} (hξ : 0 ≤ ξ) (a : Set.Ioi (0 : ℝ))
    {φ φ' : C(ℂ, ℝ)} {N : Set ℂ} (hN : IsOpen N) {c : ℝ} (hc : ∀ z ∈ N, φ z + c ≤ φ' z)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContinuousOn γ (Icc s t)) (hγN : ∀ u ∈ Icc s t, γ u ∈ N) :
    ENNReal.ofReal (Real.exp (ξ * c)) * (B2.Median.lfppMetric ξ a φ).len γ s t ≤
      (B2.Median.lfppMetric ξ a φ').len γ s t := by
  let φc : C(ℂ, ℝ) := φ + ContinuousMap.const ℂ c
  let ψ : C(ℂ, ℝ) := φ' ⊔ φc
  have hφc : ∀ z, φc z = φ z + c := fun z => rfl
  have hψ : ∀ z, φc z ≤ ψ z := fun z => le_sup_right
  have hψN : ∀ z ∈ N, |ψ z - φ' z| ≤ 0 := by
    intro z hz
    have : ψ z = φ' z := by
      change max (φ' z) (φc z) = φ' z
      exact max_eq_left (by rw [hφc]; exact hc z hz)
    rw [this, sub_self, abs_zero]
  have h1 : (B2.Median.lfppMetric ξ a φc).len γ s t =
      ENNReal.ofReal (Real.exp (ξ * c)) * (B2.Median.lfppMetric ξ a φ).len γ s t :=
    len_eq_mul_len _ (fun p => lfppMetric_add_const ξ a c hφc p) γ s t
  have h2 : (B2.Median.lfppMetric ξ a φc).len γ s t ≤ (B2.Median.lfppMetric ξ a ψ).len γ s t :=
    len_le_len_of_le (fun p => lfppMetric_le_of_le hξ a hψ p) γ s t
  have h3 := B2.Polylog.lfppMetric_len_le_of_abs_sub_le ξ a hN hψN hγ hγN
  rw [mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h3
  rw [← h1]
  exact h2.trans h3

/-- The normalized LFPP metric is a length space. -/
theorem lfppMetric_isLengthSpace (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) :
    (B2.Median.lfppMetric ξ a φ).IsLengthSpace := by
  rw [B2.Polylog.lfppMetric_eq_normalizedLFPPMetric]
  exact B2.PfeWeyl.isLengthSpace_normalizedLFPPMetric ξ a φ

/-! ### Weyl scaling -/

/-- If `Df = weylScale ξ f D` pointwise, then `Df`-lengths are the toolkit's Weyl curve lengths. -/
theorem len_eq_weylCurveLength {D Df : LSCMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hDf : ∀ p, Df p = weylScale ξ f D p) (P : ℝ → ℂ) (a b : ℝ) :
    Df.len P a b = curveLengthWith
      (fun x y : D.Space => weylScale ξ f D (Uniqueness.BiLipschitz.Barrier.forget D x,
        Uniqueness.BiLipschitz.Barrier.forget D y)) (D.pt ∘ P) a b := by
  rw [len_eq_partitionSup]
  unfold curveLengthWith
  congr 1
  funext u v
  exact hDf _

/-- For a nonnegative field, Weyl scaling does not decrease distances. -/
theorem le_weylScale_of_nonneg (D : LSCMetric) {ξ : ℝ} (hξ : 0 ≤ ξ) {f : C(ℂ, ℝ)}
    (hf : ∀ z, 0 ≤ f z) (p : ℂ × ℂ) : D p ≤ weylScale ξ f D p := by
  have h := Uniqueness.EndSaving.Choices.weylScale_ge_exp_mul D ξ hξ f 0
    (fun x => by rw [neg_zero]; exact hf x) p
  rwa [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] at h

/-- On a curve along which `f ≡ B`, Weyl-scaled lengths are `e^{ξB}` times the original
lengths (lower bound). -/
theorem le_len_weyl_of_eq_on {D Df : LSCMetric} {ξ : ℝ} (hξ : 0 ≤ ξ) {f : C(ℂ, ℝ)}
    (hDf : ∀ p, Df p = weylScale ξ f D p)
    (hforget : Continuous (Uniqueness.BiLipschitz.Barrier.forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) {B : ℝ} (hB : ∀ s ∈ Icc a b, B ≤ f (P s)) :
    ENNReal.ofReal (Real.exp (ξ * B)) * D.len P a b ≤ Df.len P a b := by
  rw [len_eq_weylCurveLength hDf]
  have hb := Uniqueness.Toolkit.WeylLength.weylCurveLength_factor_bounds D ξ hξ f hforget hP B
    (B ⊔ ⨆ s : Icc a b, f (P s)) hB (fun s hs => by
      have hbdd : BddAbove (Set.range fun s : Icc a b => f (P s)) := by
        have hc : ContinuousOn P (Icc a b) := hforget.comp_continuousOn hP.2
        have hcomp := (isCompact_Icc.image_of_continuousOn hc).image f.continuous
        obtain ⟨M, hM⟩ := hcomp.isBounded.bddAbove
        refine ⟨M, ?_⟩
        rintro _ ⟨s, rfl⟩
        exact hM ⟨P s, ⟨s, s.2, rfl⟩, rfl⟩
      exact le_sup_of_le_right (le_ciSup hbdd ⟨s, hs⟩))
  exact hb.1

/-- On a curve along which `f ≡ 0`, Weyl-scaled lengths equal the original lengths. -/
theorem len_weyl_eq_of_zero_on {D Df : LSCMetric} {ξ : ℝ} {f : C(ℂ, ℝ)}
    (hDf : ∀ p, Df p = weylScale ξ f D p)
    (hforget : Continuous (Uniqueness.BiLipschitz.Barrier.forget D)) {P : ℝ → ℂ} {a b : ℝ}
    (hP : D.IsCurve P a b) (hf : ∀ s ∈ Icc a b, f (P s) = 0) :
    Df.len P a b = D.len P a b := by
  rw [len_eq_weylCurveLength hDf]
  exact Uniqueness.Toolkit.WeylLength.weylCurveLength_eq_of_zero_on_trace D ξ f hforget hP hf

/-! ### The collar annuli and confinement -/

/-- The inner collar annulus `A(0; 1/4, 1/3)`. -/
def collarIn : EuclideanAnnulus := ⟨(0, (1 / 4, 1 / 3)), by norm_num, by norm_num⟩

/-- The outer collar annulus `A(0; 6, 7)`. -/
def collarOut : EuclideanAnnulus := ⟨(0, (6, 7)), by norm_num, by norm_num⟩

theorem collarIn_center : collarIn.center = 0 := rfl
theorem collarIn_innerRadius : collarIn.innerRadius = 1 / 4 := rfl
theorem collarIn_outerRadius : collarIn.outerRadius = 1 / 3 := rfl
theorem collarOut_center : collarOut.center = 0 := rfl
theorem collarOut_innerRadius : collarOut.innerRadius = 6 := rfl
theorem collarOut_outerRadius : collarOut.outerRadius = 7 := rfl

/-- **Collar confinement.** Let `P` be Euclidean continuous on `[a, b]` with
`1/3 ≤ |P a| ≤ 6`. Suppose every sub-crossing of `{1/4 ≤ |z| ≤ 1/3}` from `∂B_{1/3}` to `∂B_{1/4}`
and every sub-crossing of `{6 ≤ |z| ≤ 7}` from `∂B_6` to `∂B_7`, inside the respective closed
collar, has `E`-length at least `Λ`, while `E.len P a b < Λ`. Then `P` stays in `U`. -/
theorem mem_tgtU_of_collars (E : LSCMetric) {P : ℝ → ℂ} {a b : ℝ}
    (hPc : ContinuousOn P (Icc a b)) (ha : 1 / 3 ≤ ‖P a‖ ∧ ‖P a‖ ≤ 6) (Λ : ℝ≥0∞)
    (hin : ∀ s t, a ≤ s → s ≤ t → t ≤ b → (∀ u ∈ Icc s t, ‖P u‖ ∈ Icc (1 / 4 : ℝ) (1 / 3)) →
      ‖P s‖ = 1 / 3 → ‖P t‖ = 1 / 4 → Λ ≤ E.len P s t)
    (hout : ∀ s t, a ≤ s → s ≤ t → t ≤ b → (∀ u ∈ Icc s t, ‖P u‖ ∈ Icc (6 : ℝ) 7) →
      ‖P s‖ = 6 → ‖P t‖ = 7 → Λ ≤ E.len P s t)
    (hlen : E.len P a b < Λ) : ∀ t ∈ Icc a b, P t ∈ tgtU := by
  intro t ht
  by_contra hnot
  have hnorm : ContinuousOn (fun u => ‖P u‖) (Icc a t) :=
    continuous_norm.comp_continuousOn (hPc.mono (Icc_subset_Icc le_rfl ht.2))
  have hsub : ∀ s t', a ≤ s → s ≤ t' → t' ≤ t → E.len P s t' ≤ E.len P a b := fun s t' h1 _ h3 =>
    B2.PfeWeyl.len_mono_Icc E P h1 (h3.trans ht.2)
  simp only [tgtU, mem_ofPred_eq, not_and_or, not_le] at hnot
  rcases hnot with hlo | hhi
  · obtain ⟨s, s', has, hss', hs't, hs, hs', hmem⟩ :=
      LQGMetric.RectCross.exists_sub_crossing' ht.1 hnorm (by norm_num : (1 / 4 : ℝ) ≤ 1 / 3)
        (by linarith [ha.1]) (by linarith)
    have := hin s s' has hss' (hs't.trans ht.2) hmem hs hs'
    exact (not_le.2 hlen) (this.trans (hsub s s' has hss' hs't))
  · obtain ⟨s, s', has, hss', hs't, hs, hs', hmem⟩ :=
      LQGMetric.RectCross.exists_sub_crossing ht.1 hnorm (by norm_num : (6 : ℝ) ≤ 7)
        ha.2 (by linarith)
    have := hout s s' has hss' (hs't.trans ht.2) hmem hs hs'
    exact (not_le.2 hlen) (this.trans (hsub s s' has hss' hs't))

/-- A curve crossing the inner collar from `∂B_{1/3}` to `∂B_{1/4}` has length at least the
across distance of the collar. -/
theorem acrossDist_collarIn_le_len (E : LSCMetric) {P : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hPc : ContinuousOn P (Icc s t)) (hs : ‖P s‖ = 1 / 3) (ht : ‖P t‖ = 1 / 4) :
    acrossDist E collarIn ≤ E.len P s t :=
  B2.PfeWeyl.acrossDist_le_len_of_crossing_rev E collarIn hst hPc
    (by rw [collarIn_center, dist_zero_right, hs, collarIn_outerRadius])
    (by rw [collarIn_center, dist_zero_right, ht, collarIn_innerRadius])

/-- A curve crossing the outer collar from `∂B_6` to `∂B_7` has length at least the across
distance of the collar. -/
theorem acrossDist_collarOut_le_len (E : LSCMetric) {P : ℝ → ℂ} {s t : ℝ} (hst : s ≤ t)
    (hPc : ContinuousOn P (Icc s t)) (hs : ‖P s‖ = 6) (ht : ‖P t‖ = 7) :
    acrossDist E collarOut ≤ E.len P s t :=
  B2.PfeWeyl.acrossDist_le_len_of_crossing E collarOut hst hPc
    (by rw [collarOut_center, dist_zero_right, hs, collarOut_innerRadius])
    (by rw [collarOut_center, dist_zero_right, ht, collarOut_outerRadius])

end SupercriticalLFPPAS.Local

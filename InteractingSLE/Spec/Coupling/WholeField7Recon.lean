/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WholeField7Event
import InteractingSLE.Spec.Coupling.WholeField7Cover
import InteractingSLE.Spec.Sec7.TwoForcePocket

/-!
# C.5 at `κ = 4`: the random set off the labelled rational balls

Packet PROVE-WHOLEFIELD7 (follow-up note C.5, `source/external/AstraIG1/ig1_followup_proofs.txt` L1705–1760; ruling
R38; the additional note's countable-coordinate form, R39).

The reconstruction across the trace (Proposition R1, `WangWu.ae_condExp_exp_eq_gaussCF`) is applied with the random set
`A = ℍ \ ⋃ {open rational balls whose closure is a label at σ}` (`offLabels`):

* its avoidance events are countable unions of finite intersections of label events
  (`measurableSet_disjoint_offLabels`);
* it lies in the trace `η[0,σ]` (`offLabels_subset_image`): a point of `ℍ` off the trace is outside the hull (then a
  small ball is active) or in a pocket of `ℍ \ η[0,β]`, `β` its swallowing time, all of whose points are swallowed at
  `β` (`Sec7.swallowTime_eq_of_mem_pocket`);
* a test function avoiding `A` splits, at a fine dyadic scale, into pieces each supported in a label
  (`exists_scale_isLabel`, Lebesgue number lemma), to which C.4 applies.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open LQGMetric QuantumZipper LocalSets Ito Coupling

/-! ### Rational balls -/

section Balls

/-- The centre of the rational ball coded by `q`. -/
def qCentre (q : ℚ × ℚ × ℚ) : ℂ := ⟨q.1, q.2.1⟩

/-- The radius of the rational ball coded by `q`. -/
def qRad (q : ℚ × ℚ × ℚ) : ℝ := q.2.2

/-- A rational ball with positive radius whose closure lies in `ℍ`. -/
def IsGoodBall (q : ℚ × ℚ × ℚ) : Prop := 0 < qRad q ∧ closedBall (qCentre q) (qRad q) ⊆ H

/-- **Small rational balls**: a point of an open set `U ⊆ ℍ` lies in a good rational ball whose closure is in `U`. -/
theorem exists_goodBall {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ H) {z : ℂ} (hz : z ∈ U) :
    ∃ q : ℚ × ℚ × ℚ, IsGoodBall q ∧ z ∈ ball (qCentre q) (qRad q) ∧ closedBall (qCentre q) (qRad q) ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show z.re - ε / 8 < z.re + ε / 8 by linarith)
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show z.im - ε / 8 < z.im + ε / 8 by linarith)
  obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  have hdist : dist (⟨a, b⟩ : ℂ) z < ε / 4 := by
    rw [dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
    simp only [Complex.sub_re, Complex.sub_im]
    rw [show ((a : ℝ) - z.re) = (a : ℝ) - z.re from rfl]
    have h1 : |(a : ℝ) - z.re| < ε / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
    have h2 : |(b : ℝ) - z.im| < ε / 8 := abs_lt.2 ⟨by linarith, by linarith⟩
    linarith
  have hsub : closedBall (qCentre (a, b, r)) (qRad (a, b, r)) ⊆ U := fun x hx => by
    refine hball (mem_ball.2 ?_)
    have hx' : dist x (⟨a, b⟩ : ℂ) ≤ r := hx
    linarith [dist_triangle x (⟨a, b⟩ : ℂ) z]
  refine ⟨(a, b, r), ⟨show (0 : ℝ) < r by linarith, hsub.trans hUH⟩, ?_, hsub⟩
  show dist z (⟨a, b⟩ : ℂ) < r
  rw [dist_comm]; linarith

variable {Ω : Type*}

/-- **The random set off the labelled balls**: `ℍ` minus the open rational balls whose code `q` has `ω ∈ G q`. -/
def offLabels (G : ℚ × ℚ × ℚ → Set Ω) (ω : Ω) : Set ℂ :=
  H \ ⋃ q ∈ {q | ω ∈ G q}, ball (qCentre q) (qRad q)

/-- **Avoidance events of `offLabels` are events** of any σ-algebra containing every `G q`. -/
theorem measurableSet_disjoint_offLabels {𝒢 : MeasurableSpace Ω} {G : ℚ × ℚ × ℚ → Set Ω}
    (hG : ∀ q, MeasurableSet[𝒢] (G q)) {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    MeasurableSet[𝒢] {ω | Disjoint K (offLabels G ω)} := by
  have e : {ω | Disjoint K (offLabels G ω)} =
      ⋃ F : Finset (ℚ × ℚ × ℚ), ⋃ (_ : K ⊆ ⋃ q ∈ F, ball (qCentre q) (qRad q)), ⋂ q ∈ F, G q := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro hd
      have hcov : K ⊆ ⋃ q ∈ {q | ω ∈ G q}, ball (qCentre q) (qRad q) := fun z hz => by
        by_contra hz'
        exact Set.disjoint_left.1 hd hz ⟨hKH hz, hz'⟩
      obtain ⟨b, hb, hbfin, hbcov⟩ := hK.elim_finite_subcover_image (fun q _ => isOpen_ball) hcov
      refine ⟨hbfin.toFinset, fun z hz => ?_, fun q hq => hb (hbfin.mem_toFinset.1 hq)⟩
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 (hbcov hz)
      exact mem_iUnion₂.2 ⟨q, hbfin.mem_toFinset.2 hq, hzq⟩
    · rintro ⟨F, hF, hFG⟩
      refine Set.disjoint_left.2 fun z hz hzA => ?_
      obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 (hF hz)
      exact hzA.2 (mem_iUnion₂.2 ⟨q, hFG q hq, hzq⟩)
  rw [e]
  exact MeasurableSet.iUnion fun F => MeasurableSet.iUnion fun _ => Finset.measurableSet_biInter F fun q _ => hG q

/-- **The set off the labelled balls lies in the trace.** If, at a time `t` before the horizon of a generating trace
`η`, exactly the good rational balls whose closure is a label are marked, then `offLabels ⊆ η[0,t]`. -/
theorem offLabels_subset_image {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {G : ℚ × ℚ × ℚ → Set Ω}
    {ω : Ω} (hG : ∀ q, IsGoodBall q → IsLabel w (closedBall (qCentre q) (qRad q)) t → ω ∈ G q) :
    offLabels G ω ⊆ η '' Icc 0 t := by
  intro z ⟨hzH, hzA⟩
  by_contra hzη
  have hmark : ∀ q, IsGoodBall q → z ∈ ball (qCentre q) (qRad q) →
      ¬ IsLabel w (closedBall (qCentre q) (qRad q)) t := fun q hq hzq hl =>
    hzA (mem_iUnion₂.2 ⟨q, hG q hq hl, hzq⟩)
  by_cases hzK : z ∈ fwdHull (Ito.rpath w) (t : ℝ)
  · -- a pocket point: its component of `ℍ \ η[0,β]`
    have hsle : swallowTime (Ito.rpath w) z ≤ t := (mem_fwdHull_rpath_iff.1 hzK).2
    have hne : swallowTime (Ito.rpath w) z ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hsle
    set β : ℝ≥0 := (swallowTime (Ito.rpath w) z).toNNReal with hβdef
    have hzβ : swallowTime (fun s : ℝ => w s.toNNReal) z = β := (ENNReal.coe_toNNReal hne).symm
    have hβt : β ≤ t := by
      have : (β : ℝ≥0∞) ≤ t := by rw [hβdef, ENNReal.coe_toNNReal hne]; exact hsle
      exact_mod_cast this
    have hβζ : (β : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hβt) ht
    have hcpt : IsCompact (η '' Icc 0 β) :=
      isCompact_Icc.image_of_continuousOn (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans hβζ.le)
    have hzO : z ∈ H \ η '' Icc 0 β := ⟨hzH, fun h => hzη (image_mono (Icc_subset_Icc_right hβt) h)⟩
    have hPo : IsOpen (connectedComponentIn (H \ η '' Icc 0 β) z) :=
      (isOpen_H.sdiff hcpt.isClosed).connectedComponentIn
    obtain ⟨q, hq, hzq, hqP⟩ := exists_goodBall hPo
      ((connectedComponentIn_subset _ _).trans sdiff_subset) (mem_connectedComponentIn hzO)
    refine hmark q hq hzq (Or.inr ⟨β, hβt, fun x hx => ?_⟩)
    exact Sec7.swallowTime_eq_of_mem_pocket hη hβζ hzβ (hqP hx)
  · -- an active point
    have hU : IsOpen (H \ fwdHull (Ito.rpath w) (t : ℝ)) := MartMeans2.isOpen_H_diff_fwdHull_rpath hw ht
    obtain ⟨q, hq, hzq, hqU⟩ := exists_goodBall hU sdiff_subset ⟨hzH, hzK⟩
    exact hmark q hq hzq (Or.inl (Set.disjoint_left.2 fun x hx hxK => (hqU hx).2 hxK))

/-- A point of the cell `pouCell n k` is within `2 · 2^{-n}` of its centre. -/
theorem dist_pouCentre_le {n : ℕ} {k : ℤ × ℤ} {z : ℂ} (hz : z ∈ WangWu.pouCell n k) :
    dist z (WangWu.pouCentre n k) ≤ 2 / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  obtain ⟨hre, him⟩ := hz
  have e1 : |z.re - (k.1 : ℝ) / 2 ^ n| = |z.re * 2 ^ n - k.1| / 2 ^ n := by
    rw [show z.re - (k.1 : ℝ) / 2 ^ n = (z.re * 2 ^ n - k.1) / 2 ^ n by field_simp, abs_div, abs_of_pos h2]
  have e2 : |z.im - (k.2 : ℝ) / 2 ^ n| = |z.im * 2 ^ n - k.2| / 2 ^ n := by
    rw [show z.im - (k.2 : ℝ) / 2 ^ n = (z.im * 2 ^ n - k.2) / 2 ^ n by field_simp, abs_div, abs_of_pos h2]
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im, WangWu.pouCentre]
  rw [e1, e2]
  have h3 : |z.re * 2 ^ n - k.1| / 2 ^ n ≤ 1 / 2 ^ n := div_le_div_of_nonneg_right hre h2.le
  have h4 : |z.im * 2 ^ n - k.2| / 2 ^ n ≤ 1 / 2 ^ n := div_le_div_of_nonneg_right him h2.le
  linarith [show (2 : ℝ) / 2 ^ n = 1 / 2 ^ n + 1 / 2 ^ n by ring]

/-- **At a fine scale every piece of a test avoiding `offLabels` is a label** (Lebesgue number lemma). -/
theorem exists_scale_isLabel {w : ℝ≥0 → ℝ} {t : ℝ≥0} {G : ℚ × ℚ × ℚ → Set Ω} {ω : Ω}
    (hG : ∀ q, ω ∈ G q → IsLabel w (closedBall (qCentre q) (qRad q)) t) (ψ : TestOn upperHalfPlaneOpens)
    (hd : Disjoint (tsupport ψ) (offLabels G ω)) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : ℤ × ℤ, IsLabel w (tsupport (WangWu.pouTest ψ n k)) t := by
  have hK : IsCompact (tsupport ψ) := ψ.hasCompactSupport.isCompact
  have hcov : tsupport ψ ⊆ ⋃ q : {q : ℚ × ℚ × ℚ // ω ∈ G q}, ball (qCentre q.1) (qRad q.1) := fun z hz => by
    by_contra hz'
    refine Set.disjoint_left.1 hd hz ⟨ψ.tsupport_subset hz, fun hz'' => hz' ?_⟩
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.1 hz''
    exact mem_iUnion.2 ⟨⟨q, hq⟩, hzq⟩
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric hK (fun _ => isOpen_ball) hcov
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (4 : ℝ) / 2 ^ n₀ < δ := by
    obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < δ / 4 by positivity)
      (show (1 / 2 : ℝ) < 1 by norm_num)
    refine ⟨n₀, ?_⟩
    rw [one_div_pow] at hn₀
    rw [div_lt_iff₀ (pow_pos two_pos n₀)]
    rw [div_lt_iff₀ (pow_pos two_pos n₀)] at hn₀
    nlinarith
  refine ⟨n₀, fun n hn k => ?_⟩
  rcases (tsupport (WangWu.pouTest ψ n k)).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · left; rw [he]; exact Set.empty_disjoint _
  have hxs := WangWu.tsupport_pouTest_subset ψ n k hx
  obtain ⟨⟨q, hq⟩, hqb⟩ := hleb x hxs.1
  refine (hG q hq).mono fun y hy => ball_subset_closedBall (hqb (mem_ball.2 ?_))
  have hys := WangWu.tsupport_pouTest_subset ψ n k hy
  have h1 := dist_pouCentre_le hys.2
  have h2 := dist_pouCentre_le hxs.2
  have hpow : (2 : ℝ) ^ n₀ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have h4 : (4 : ℝ) / 2 ^ n ≤ 4 / 2 ^ n₀ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
  calc dist y x ≤ dist y (WangWu.pouCentre n k) + dist x (WangWu.pouCentre n k) := dist_triangle_right _ _ _
    _ ≤ 2 / 2 ^ n + 2 / 2 ^ n := add_le_add h1 h2
    _ = 4 / 2 ^ n := by ring
    _ < δ := h4.trans_lt hn₀

end Balls

end WholeField

end InteractingSLE

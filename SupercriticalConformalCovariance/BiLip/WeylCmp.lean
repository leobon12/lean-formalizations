import SupercriticalConformalCovariance.BiLip.Round
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.WeylLocalTopology
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.CountableBase.Annulus

/-!
# Lemma 2.1: the target quantities against whole-plane metrics

For one sample: `D₀ = D_{g₀}` with `(ℂ, D₀) → ℂ` continuous and `D₀` a length space, the domain correction
`k ∈ C(V)`, and a whole-plane metric `E = e^{ξ F} · D₀` (`F ∈ C(ℂ)`, Weyl scaling, in applications
`E = D_{g₀ + F}`). On a region `R ⊆ V` where `m ≤ k − F ≤ M`, the `e`-lengths (`dV`-lengths) of `D₀`-curves in
`R` are between `e^{ξ m}` and `e^{ξ M}` times their `E`-lengths (`curveLengthWith_dV_le`), and `D₀`-curves
and `E`-curves coincide (`isCurve_weyl_forward`, SLU `curve_back_all_continuous`). Hence
(`tAround_le`, `le_tAround`, `tAcr_le`, `le_tAcr`) for round annuli in `R`:

`e^{ξ m} E(around A) ≤ tAround(A) ≤ e^{ξ M} E(around A)`,  `e^{ξ m} acr(E) ≤ tAcr ≤ e^{ξ M} acr(E)`.

With `m = M = 0` (`F = k` on `R`, e.g. a cut-off extension of `k`) the target quantities are exactly the
whole-plane `aroundDist` and closed-annulus crossing cost `acr` of `E` (the step-4 locality input).
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.BiLip

open SupercriticalLQGUniqueness (LSCMetric weylScale Disconnects aroundDist EuclideanAnnulus)
open SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier (forget)
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent (acr cann)
open SupercriticalConformalCovariance.Domain (dV SV wV wt)
open HigherDimLQGMetric (curveLengthWith weightedLength infAlong)

/-- `weightedLength` is homogeneous in the weight. -/
theorem weightedLength_const_mul {X : Type*} [PseudoEMetricSpace X] (w : X → ℝ) (P : ℝ → X)
    (a b : ℝ) {c : ℝ} (hc : 0 < c) :
    weightedLength (fun x => c * w x) P a b = ENNReal.ofReal c * weightedLength w P a b := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hinf : ∀ u v, infAlong (fun x => c * w x) P u v = ENNReal.ofReal c * infAlong w P u v := by
    intro u v
    unfold infAlong
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine iInf_congr fun s => ?_
    rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
    refine iInf_congr fun _ => ?_
    rw [ENNReal.ofReal_mul hc.le]
  unfold weightedLength
  rw [← HigherDimLQGMetric.partitionSup_const_mul]
  refine HigherDimLQGMetric.partitionSup_congr fun u v _ _ _ => ?_
  rw [hinf, mul_assoc]

section Cmp

variable {D₀ : LSCMetric} {ξ : ℝ} {V : Set ℂ} (k : C(V, ℝ)) {F : C(ℂ, ℝ)} {E : LSCMetric}

/-- the `e`-length of a `D₀`-curve is the `e^{ξ k}`-weighted `D₀`-length -/
theorem curveLengthWith_dV_eq (hf : Continuous (forget D₀)) (hV : IsOpen V) {η : ℝ → ℂ}
    {a b : ℝ} (hη : D₀.IsCurve η a b) (hηV : ∀ t ∈ Icc a b, η t ∈ V) :
    curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) a b = weightedLength (wV D₀ ξ k) (D₀.pt ∘ η) a b :=
  SupercriticalConformalCovariance.Domain.curveLengthWith_dV hf hV k hη.2 (fun t ht => hηV t ht)

/-- **Weight comparison** of the `e`-length and the `E`-length on a region where `m ≤ k − F ≤ M`. -/
theorem curveLengthWith_dV_le (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hV : IsOpen V)
    (hE : ∀ q, E q = weylScale ξ F D₀ q) {R : Set ℂ} (hRV : R ⊆ V) {m M : ℝ}
    (hkF : ∀ y (hy : y ∈ R), m ≤ k ⟨y, hRV hy⟩ - F y ∧ k ⟨y, hRV hy⟩ - F y ≤ M)
    {η : ℝ → ℂ} {a b : ℝ} (hη : D₀.IsCurve η a b) (hηR : ∀ t ∈ Icc a b, η t ∈ R) :
    ENNReal.ofReal (Real.exp (ξ * m)) * E.len η a b ≤
        curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) a b ∧
      curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ η) a b ≤
        ENNReal.ofReal (Real.exp (ξ * M)) * E.len η a b := by
  rw [curveLengthWith_dV_eq k hf hV hη (fun t ht => hRV (hηR t ht)),
    SupercriticalConformalCovariance.Domain.len_eq_weightedLength hf hE hη,
    ← weightedLength_const_mul _ _ _ _ (Real.exp_pos _),
    ← weightedLength_const_mul _ _ _ _ (Real.exp_pos _)]
  have hw : ∀ t (ht : t ∈ Icc a b), wV D₀ ξ k ((D₀.pt ∘ η) t) =
      Real.exp (ξ * k ⟨η t, hRV (hηR t ht)⟩) := by
    intro t ht
    exact SupercriticalConformalCovariance.Domain.wV_of_mem k (show forget D₀ (D₀.pt (η t)) ∈ V from hRV (hηR t ht))
  constructor
  · refine HigherDimLQGMetric.weightedLength_mono_weight fun t ht => ?_
    rw [hw t ht]
    show Real.exp (ξ * m) * Real.exp (ξ * F (η t)) ≤ _
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [(hkF (η t) (hηR t ht)).1])
  · refine HigherDimLQGMetric.weightedLength_mono_weight fun t ht => ?_
    rw [hw t ht]
    show _ ≤ Real.exp (ξ * M) * Real.exp (ξ * F (η t))
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [(hkF (η t) (hηR t ht)).2])

end Cmp

section Annuli

variable {D₀ : LSCMetric} {ξ : ℝ} {V : Set ℂ} (k : C(V, ℝ)) {F : C(ℂ, ℝ)} {E : LSCMetric}

theorem ofReal_exp_ne_zero (x : ℝ) : ENNReal.ofReal (Real.exp x) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (Real.exp_pos x)).ne'

theorem annulus_toSet_mem {c y : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    y ∈ SupercriticalLQGUniqueness.EuclideanAnnulus.toSet (⟨(c, a, b), ha, hab⟩ : EuclideanAnnulus) ↔ y ∈ ball c b \ closedBall c a := by
  show y ∈ ball c b \ closure (ball c a) ↔ _
  rw [closure_ball c ha.ne']

/-- `tAround ≤ e^{ξ M} E(around A)` -/
theorem tAround_le (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hV : IsOpen V)
    (hE : ∀ q, E q = weylScale ξ F D₀ q) {R : Set ℂ} (hRV : R ⊆ V) {m M : ℝ}
    (hkF : ∀ y (hy : y ∈ R), m ≤ k ⟨y, hRV hy⟩ - F y ∧ k ⟨y, hRV hy⟩ - F y ≤ M)
    (c : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hAR : ball c b \ closedBall c a ⊆ R) :
    tAround D₀ ξ k c a b ≤
      ENNReal.ofReal (Real.exp (ξ * M)) * aroundDist E ⟨(c, a, b), ha, hab⟩ := by
  rw [← ENNReal.inv_mul_le_iff (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top]
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPA =>
    le_iInf fun hdisc => ?_
  rw [ENNReal.inv_mul_le_iff (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top]
  have hPD : D₀.IsCurve P s t :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.curve_back_all_continuous D₀ E ξ hξ F
      hf hE hP
  have hPA' : ∀ u ∈ Icc s t, P u ∈ ball c b \ closedBall c a := fun u hu =>
    (annulus_toSet_mem ha hab).1 (hPA u hu)
  have h1 : tAround D₀ ξ k c a b ≤ curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ P) s t := by
    unfold tAround
    exact iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hPD <|
      iInf_le_of_le hPA' <| iInf_le_of_le hdisc le_rfl
  exact h1.trans (curveLengthWith_dV_le k hξ hf hV hE hRV hkF hPD
    (fun u hu => hAR (hPA' u hu))).2

/-- `e^{ξ m} E(around A) ≤ tAround` -/
theorem le_tAround (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hL : D₀.IsLengthSpace)
    (hV : IsOpen V) (hE : ∀ q, E q = weylScale ξ F D₀ q) {R : Set ℂ} (hRV : R ⊆ V) {m M : ℝ}
    (hkF : ∀ y (hy : y ∈ R), m ≤ k ⟨y, hRV hy⟩ - F y ∧ k ⟨y, hRV hy⟩ - F y ≤ M)
    (c : ℂ) {a b : ℝ} (ha : 0 < a) (hab : a < b) (hAR : ball c b \ closedBall c a ⊆ R) :
    ENNReal.ofReal (Real.exp (ξ * m)) * aroundDist E ⟨(c, a, b), ha, hab⟩ ≤
      tAround D₀ ξ k c a b := by
  unfold tAround
  refine le_iInf fun η => le_iInf fun s => le_iInf fun t => le_iInf fun hη => le_iInf fun hηA =>
    le_iInf fun hdisc => ?_
  have hηE : E.IsCurve η s t := SupercriticalConformalCovariance.Domain.isCurve_weyl_forward hξ hf hL hE hη
  have h1 : aroundDist E ⟨(c, a, b), ha, hab⟩ ≤ E.len η s t := by
    unfold aroundDist
    exact iInf_le_of_le η <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hηE <|
      iInf_le_of_le (fun u hu => (annulus_toSet_mem ha hab).2 (hηA u hu)) <|
      iInf_le_of_le hdisc le_rfl
  exact (mul_le_mul_right h1 _).trans
    (curveLengthWith_dV_le k hξ hf hV hE hRV hkF hη (fun u hu => hAR (hηA u hu))).1

theorem mem_cann_iff {c y : ℂ} {a b : ℝ} :
    y ∈ SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.cann c a b ↔
      y ∈ closedBall c b \ ball c a := by
  show a ≤ dist y c ∧ dist y c ≤ b ↔ _
  rw [Set.mem_sdiff, Metric.mem_closedBall, Metric.mem_ball, not_lt]
  exact and_comm

/-- `tAcr ≤ e^{ξ M} acr(E)` -/
theorem tAcr_le (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hV : IsOpen V)
    (hE : ∀ q, E q = weylScale ξ F D₀ q) {R : Set ℂ} (hRV : R ⊆ V) {m M : ℝ}
    (hkF : ∀ y (hy : y ∈ R), m ≤ k ⟨y, hRV hy⟩ - F y ∧ k ⟨y, hRV hy⟩ - F y ≤ M)
    (c : ℂ) (a b : ℝ) (hAR : closedBall c b \ ball c a ⊆ R) :
    tAcr D₀ ξ k c a b ≤ ENNReal.ofReal (Real.exp (ξ * M)) * acr E c a b := by
  rw [← ENNReal.inv_mul_le_iff (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top]
  unfold acr
  refine le_iInf fun P => le_iInf fun s => le_iInf fun t => le_iInf fun hP => le_iInf fun hPA =>
    le_iInf fun hs => le_iInf fun ht => ?_
  rw [ENNReal.inv_mul_le_iff (ofReal_exp_ne_zero _) ENNReal.ofReal_ne_top]
  have hPD : D₀.IsCurve P s t :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylShift.curve_back_all_continuous D₀ E ξ hξ F
      hf hE hP
  have hPA' : ∀ u ∈ Icc s t, P u ∈ closedBall c b \ ball c a := fun u hu =>
    mem_cann_iff.1 (hPA ⟨u, hu, rfl⟩)
  have h1 : tAcr D₀ ξ k c a b ≤ curveLengthWith (dV D₀ ξ k) (D₀.pt ∘ P) s t := by
    unfold tAcr
    exact iInf_le_of_le P <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hPD <|
      iInf_le_of_le hPA' <| iInf_le_of_le hs <| iInf_le_of_le ht le_rfl
  exact h1.trans (curveLengthWith_dV_le k hξ hf hV hE hRV hkF hPD
    (fun u hu => hAR (hPA' u hu))).2

/-- `e^{ξ m} acr(E) ≤ tAcr` -/
theorem le_tAcr (hξ : 0 ≤ ξ) (hf : Continuous (forget D₀)) (hL : D₀.IsLengthSpace)
    (hV : IsOpen V) (hE : ∀ q, E q = weylScale ξ F D₀ q) {R : Set ℂ} (hRV : R ⊆ V) {m M : ℝ}
    (hkF : ∀ y (hy : y ∈ R), m ≤ k ⟨y, hRV hy⟩ - F y ∧ k ⟨y, hRV hy⟩ - F y ≤ M)
    (c : ℂ) (a b : ℝ) (hAR : closedBall c b \ ball c a ⊆ R) :
    ENNReal.ofReal (Real.exp (ξ * m)) * acr E c a b ≤ tAcr D₀ ξ k c a b := by
  unfold tAcr
  refine le_iInf fun η => le_iInf fun s => le_iInf fun t => le_iInf fun hη => le_iInf fun hηA =>
    le_iInf fun hs => le_iInf fun ht => ?_
  have hηE : E.IsCurve η s t := SupercriticalConformalCovariance.Domain.isCurve_weyl_forward hξ hf hL hE hη
  have h1 : acr E c a b ≤ E.len η s t := by
    unfold acr
    refine iInf_le_of_le η <| iInf_le_of_le s <| iInf_le_of_le t <| iInf_le_of_le hηE <|
      iInf_le_of_le ?_ <| iInf_le_of_le hs <| iInf_le_of_le ht le_rfl
    rintro _ ⟨u, hu, rfl⟩
    exact mem_cann_iff.2 (hηA u hu)
  exact (mul_le_mul_right h1 _).trans
    (curveLengthWith_dV_le k hξ hf hV hE hRV hkF hη (fun u hu => hAR (hηA u hu))).1

end Annuli

end SupercriticalConformalCovariance.BiLip

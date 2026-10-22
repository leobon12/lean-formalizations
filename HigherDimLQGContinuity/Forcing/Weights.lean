import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Metric.WeylBridge

/-!
# Weyl length facts for the deterministic site forcing lemma

The internal Weyl relation determines lengths even when the modified metric is not a length
metric.  We use the existing intrinsic-length and weighted-distance lemmas.
-/

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- An internal Weyl relation determines the length of every continuous curve. -/
theorem q6_weyl_len {G G' : ContMetric d} {ζ : ℝ} {F : C(Rd d, ℝ)}
    (hW : IsWeylInternal ζ F G G') {P : ℝ → Rd d} {a b : ℝ}
    (hP : ContinuousOn P (Icc a b)) :
    G'.len P a b = weightedLength (G.weylWeight ζ F) (G.pt ∘ P) a b := by
  have hG' := G'.curveLengthWith_internal hP (mapsTo_univ _ _)
  rw [G'.len_def] at hG'
  change curveLength (G'.pt ∘ P) a b = _
  rw [← hG']
  change curveLengthWith (fun x y => G'.internal univ x y) P a b = _
  rw [show (fun x y => G'.internal univ x y) =
      (fun x y => weylDistOn (G.weylWeight ζ F) univ (G.pt x) (G.pt y)) from by
        funext x y
        rw [hW univ isOpen_univ x y, weylScaleOn_eq_weylDistOn, G.image_pt_univ]]
  exact curveLengthWith_weylDistOn isOpen_univ
    (G.continuous_weylWeight ζ F).continuousOn
    (G.continuous_pt.comp_continuousOn hP) (mapsTo_univ _ _)

/-- Two-sided internal distance bounds under a nonpositive Weyl perturbation. -/
theorem q6_weyl_internal_bounds {G G' : ContMetric d} {ζ M : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G') (hζ : 0 ≤ ζ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) {W : Set (Rd d)} (hWo : IsOpen W)
    (x y : Rd d) :
    ENNReal.ofReal (Real.exp (-(ζ * M))) * G.internal W x y ≤ G'.internal W x y ∧
      G'.internal W x y ≤ G.internal W x y := by
  rw [hW W hWo x y]
  constructor
  · apply le_weylScaleOn_of_le
    intro z hz
    simp only [ContinuousMap.neg_apply]
    have := (hf z).2
    nlinarith
  · convert weylScaleOn_le_of_le (b := 0) (ξ := ζ) (f := -f) (D := G)
      (U := W) (z := x) (w := y) (fun z hz => ?_) using 1 <;> simp
    have := (hf z).1
    nlinarith

/-- On an open plateau where the Weyl factor is constant, internal distances scale exactly. -/
theorem q6_weyl_internal_const {G G' : ContMetric d} {ζ M : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G')
    {W : Set (Rd d)} (hWo : IsOpen W) (hf : ∀ x ∈ W, f x = M)
    (x y : Rd d) :
    G'.internal W x y = ENNReal.ofReal (Real.exp (-(ζ * M))) * G.internal W x y := by
  rw [hW W hWo x y]
  apply weylScaleOn_of_eq_const
  intro z hz
  simp [hf z hz]

/-- The zero-weight case of the previous fact. -/
theorem q6_weyl_internal_zero {G G' : ContMetric d} {ζ : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G')
    {W : Set (Rd d)} (hWo : IsOpen W) (hf : ∀ x ∈ W, f x = 0)
    (x y : Rd d) : G'.internal W x y = G.internal W x y := by
  simpa using q6_weyl_internal_const (M := 0) hW hWo hf x y

/-- The Weyl factor bounds path lengths without a length-space assumption. -/
theorem q6_weyl_len_bounds {G G' : ContMetric d} {ζ M : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G') (hζ : 0 ≤ ζ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) {P : ℝ → Rd d} {a b : ℝ}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) :
    ENNReal.ofReal (Real.exp (-(ζ * M))) * G.len P a b ≤ G'.len P a b ∧
      G'.len P a b ≤ G.len P a b := by
  rw [q6_weyl_len hW hP]
  constructor
  · have hw : ∀ t ∈ Icc a b, Real.exp (-(ζ * M)) ≤
        G.weylWeight ζ (-f) (G.pt (P t)) := by
      intro t ht
      dsimp [ContMetric.weylWeight]
      apply Real.exp_le_exp.mpr
      have h := (hf (P t)).2
      nlinarith
    simpa only [ContMetric.len_def, Function.comp_def] using
      ofReal_mul_curveLength_le_weightedLength hab hw
  · have hw : ∀ t ∈ Icc a b, G.weylWeight ζ (-f) (G.pt (P t)) ≤ 1 := by
      intro t ht
      dsimp [ContMetric.weylWeight]
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have h := (hf (P t)).1
      nlinarith
    simpa only [ContMetric.len_def, Function.comp_def, ENNReal.ofReal_one, one_mul] using
      weightedLength_le_ofReal_mul_curveLength (M := 1) hw

/-- A constant weight along a curve multiplies its length, including infinite lengths. -/
theorem q6_weyl_len_const {G G' : ContMetric d} {ζ M : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G')
    {P : ℝ → Rd d} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hf : ∀ t ∈ Icc a b, f (P t) = M) :
    G'.len P a b = ENNReal.ofReal (Real.exp (-(ζ * M))) * G.len P a b := by
  rw [q6_weyl_len hW hP]
  have hw : ∀ t ∈ Icc a b,
      G.weylWeight ζ (-f) (G.pt (P t)) = Real.exp (-(ζ * M)) := by
    intro t ht
    dsimp [ContMetric.weylWeight]
    rw [hf t ht]
    ring_nf
  apply le_antisymm
  · simpa only [ContMetric.len_def, Function.comp_def] using
      weightedLength_le_ofReal_mul_curveLength (M := Real.exp (-(ζ * M)))
        (fun t ht => (hw t ht).le)
  · simpa only [ContMetric.len_def, Function.comp_def] using
      ofReal_mul_curveLength_le_weightedLength hab (fun t ht => (hw t ht).ge)

/-- If the perturbation vanishes along a curve, its two metric lengths agree. -/
theorem q6_weyl_len_zero {G G' : ContMetric d} {ζ : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G')
    {P : ℝ → Rd d} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hf : ∀ t ∈ Icc a b, f (P t) = 0) :
    G'.len P a b = G.len P a b := by
  simpa only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul] using
    q6_weyl_len_const (M := 0) hW hab hP hf

/-- The weight can meet the two endpoint values: avoiding the topological support at interior
times already makes the curve lengths equal. -/
theorem q6_weyl_len_off_tsupport {G G' : ContMetric d} {ζ : ℝ}
    {f : C(Rd d, ℝ)} (hW : IsWeylInternal ζ (-f) G G')
    {P : ℝ → Rd d} {a b : ℝ} (hab : a < b)
    (hP : ContinuousOn P (Icc a b))
    (havoid : ∀ t ∈ Ioo a b, P t ∉ tsupport f) :
    G'.len P a b = G.len P a b := by
  have hzeroIoo : EqOn (fun t => f (P t)) (fun _ => (0 : ℝ)) (Ioo a b) :=
    fun t ht => image_eq_zero_of_notMem_tsupport (havoid t ht)
  have hzeroIcc : ∀ t ∈ Icc a b, f (P t) = 0 :=
    hzeroIoo.of_subset_closure (f.continuous.comp_continuousOn hP)
      continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne])
  exact q6_weyl_len_zero hW hab.le hP hzeroIcc

/-- The secondary plateau discount differs from the primary discount by at most `e^Ω`. -/
theorem q6_secondary_plateau_bounds {D E : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ η M θ h δsep ε₀ εnet εatt aout H b v d₀ Ω : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hmismatch : |η - ξ| * M ≤ Ω) :
    θ * Real.exp (-Ω) ≤ Real.exp (-(η * M)) ∧
      Real.exp (-(η * M)) ≤ θ * Real.exp Ω := by
  have hM : 0 ≤ M := ((cert.f_bd 0).1).trans (cert.f_bd 0).2
  have habs : |(η - ξ) * M| ≤ Ω := by
    simpa only [abs_mul, abs_of_nonneg hM] using hmismatch
  have hbounds := abs_le.mp habs
  constructor
  · rw [cert.θ_eq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hbounds.2]
  · rw [cert.θ_eq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hbounds.1]

end HigherDimLQGContinuity

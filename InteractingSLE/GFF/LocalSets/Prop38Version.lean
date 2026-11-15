import InteractingSLE.GFF.LocalSets.Prop38Geom
import LQGMetric.Field.Measurable

/-!
# Proposition 3.8: jointly measurable bump pairings

Infrastructure for the proof of Proposition 3.8 (specification p. 60), packet PROVE-LS-C.

For a radius `δ > 0` the radial bump `bump_{y,δ}` (`GFF.bumpTest`) depends continuously on its
centre `y` (`Im y > δ`) as a test function on `ℍ` (`continuousAt_bumpTestH`, by LQGMetric's
`continuous_testFamK` on a fixed compact), so for a measurable random distribution `T` the pairing
`(ω, y) ↦ T(ω)(bump_{y,δ})` is jointly measurable (Carathéodory, `measurable_bumpPair`). On the
event that `T(ω)` is harmonic on a neighbourhood of `B̄(y, δ)` it is `T(ω)`'s harmonic
representative at `y` times `δ² ∫ e(1 − |·|²)` (mean value property).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric
open LQGMetric.GM (radProf contDiff_radProf)

/-- `B̄(y, δ) ⊆ ℍ` iff `δ < Im y`. -/
lemma closedBall_subset_H_iff {y : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) :
    closedBall y δ ⊆ H ↔ δ < y.im := by
  constructor
  · intro h
    have hm : y - δ * Complex.I ∈ closedBall y δ := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
        Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ]
    have := h hm
    simp only [H, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at this
    linarith
  · intro h z hz
    have h1 : |z.im - y.im| ≤ δ := by
      rw [mem_closedBall, dist_eq_norm] at hz
      calc |z.im - y.im| = |(z - y).im| := by rw [Complex.sub_im]
        _ ≤ ‖z - y‖ := Complex.abs_im_le_norm _
        _ ≤ δ := hz
    show 0 < z.im
    have := (abs_le.1 h1).1
    linarith

lemma coe_upperHalfPlaneOpens : (upperHalfPlaneOpens : Set ℂ) = H := rfl

lemma closedBall_subset_upper_iff {y : ℂ} {δ : ℝ} (hδ : 0 ≤ δ) :
    closedBall y δ ⊆ (upperHalfPlaneOpens : Set ℂ) ↔ δ < y.im := by
  rw [coe_upperHalfPlaneOpens]; exact closedBall_subset_H_iff hδ

open Classical in
/-- The bump at `y` of radius `δ` as a test function on `ℍ` (`0` if `B̄(y, δ) ⊄ ℍ`). -/
def bumpTestH (δ : ℝ) (hδ : 0 < δ) (y : ℂ) : TestOn upperHalfPlaneOpens :=
  if h : closedBall y δ ⊆ (upperHalfPlaneOpens : Set ℂ) then GFF.bumpTest y hδ h else 0

lemma bumpTestH_of_lt {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (hy : δ < y.im) :
    bumpTestH δ hδ y = GFF.bumpTest (D := upperHalfPlaneOpens) y hδ
      ((closedBall_subset_upper_iff hδ.le).2 hy) := by
  have h : closedBall y δ ⊆ (upperHalfPlaneOpens : Set ℂ) := (closedBall_subset_upper_iff hδ.le).2 hy
  simp only [bumpTestH, h, dite_true]

lemma coe_bumpTestH_of_lt {δ : ℝ} (hδ : 0 < δ) {y : ℂ} (hy : δ < y.im) :
    ⇑(bumpTestH δ hδ y) = GFF.bumpFun y δ := by
  rw [bumpTestH_of_lt hδ hy, GFF.coe_bumpTest]

/-- The bump depends continuously on its centre. -/
theorem continuousAt_bumpTestH {δ : ℝ} (hδ : 0 < δ) {y₀ : ℂ} (hy₀ : δ < y₀.im) :
    ContinuousAt (bumpTestH δ hδ) y₀ := by
  set r := (y₀.im - δ) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  let S := closedBall y₀ r
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hSim : ∀ y ∈ S, δ < y.im := by
    intro y hy
    have h1 : |y.im - y₀.im| ≤ r := by
      rw [mem_closedBall, dist_eq_norm] at hy
      calc |y.im - y₀.im| = |(y - y₀).im| := by rw [Complex.sub_im]
        _ ≤ ‖y - y₀‖ := Complex.abs_im_le_norm _
        _ ≤ r := hy
    have := (abs_le.1 h1).1
    linarith
  let K : Compacts ℂ := ⟨closedBall y₀ (r + δ), isCompact_closedBall _ _⟩
  have hKH : (K : Set ℂ) ⊆ (upperHalfPlaneOpens : Set ℂ) := by
    refine (closedBall_subset_H_iff (by positivity)).2 ?_
    show r + δ < y₀.im
    rw [hr]; linarith
  set b₀ : ℂ → ℝ := fun w => radProf 1 (w / δ) with hb₀
  have hb₀s : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b₀ :=
    (contDiff_radProf 1).comp (contDiff_id.div_const _)
  have hΨ : ∀ (y : S) (z : ℂ), GFF.bumpFun (y : ℂ) δ z = b₀ (z + -(y : ℂ)) := fun y z => by
    simp [GFF.bumpFun, hb₀, sub_eq_add_neg]
  have hs : ∀ y : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z => b₀ (z + -(y : ℂ)) :=
    fun y => hb₀s.comp (contDiff_id.add contDiff_const)
  have hK : ∀ y : S, ∀ z ∉ (K : Set ℂ), b₀ (z + -(y : ℂ)) = 0 := by
    intro y z hz
    rw [← hΨ]
    refine GFF.bumpFun_eq_zero hδ ?_
    have hz' : r + δ < dist z y₀ := by
      simpa [K, mem_closedBall, not_le] using hz
    have hy : dist (y : ℂ) y₀ ≤ r := mem_closedBall.1 y.2
    have := dist_triangle z (y : ℂ) y₀
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun z => b₀ (z + -(p.1 : ℂ))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (hb₀s.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := continuous_testFamK K (fun (y : S) z => b₀ (z + -(y : ℂ))) hs hK hD
  have e : (S.domRestrict (bumpTestH δ hδ)) =
      (TestFunction.ofSupportedInCLM ℝ hKH) ∘ testFamK K _ hs hK := by
    funext y
    ext z
    show (bumpTestH δ hδ (y : ℂ)) z = _
    rw [coe_bumpTestH_of_lt hδ (hSim y y.2), hΨ]
    rfl
  have h2 : Continuous (S.domRestrict (bumpTestH δ hδ)) := by
    rw [e]; exact (TestFunction.ofSupportedInCLM ℝ hKH).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt (closedBall_mem_nhds _ hr0)

section Pair

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The jointly measurable bump pairing `(ω, y) ↦ T(ω)(bump_{y,δ})` (`0` where `Im y ≤ δ`). -/
def bumpPair (T : Ω → DistOn upperHalfPlaneOpens) (δ : ℝ) (hδ : 0 < δ) (p : Ω × ℂ) : ℝ :=
  if δ < p.2.im then T p.1 (bumpTestH δ hδ p.2) else 0

theorem measurable_bumpPair {T : Ω → DistOn upperHalfPlaneOpens} (hT : Measurable T) {δ : ℝ}
    (hδ : 0 < δ) : Measurable (bumpPair T δ hδ) := by
  classical
  set X : Set ℂ := {y | δ < y.im}
  have hXo : IsOpen X := isOpen_lt continuous_const Complex.continuous_im
  let Gsub : X → Ω → ℝ := fun y ω => T ω (bumpTestH δ hδ y)
  have hcont : ∀ ω, Continuous fun y : X => Gsub y ω := by
    intro ω
    rw [continuous_iff_continuousAt]
    intro y
    have h1 : ContinuousAt (bumpTestH δ hδ) (y : ℂ) := continuousAt_bumpTestH hδ y.2
    exact ((map_continuous (T ω)).continuousAt.comp h1).comp continuous_subtype_val.continuousAt
  have hmeas : ∀ y : X, Measurable (Gsub y) := fun y => (measurable_distOn_apply _).comp hT
  have hJ : Measurable (Function.uncurry Gsub) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  set s : Set (Ω × ℂ) := Prod.snd ⁻¹' X with hs
  have hsm : MeasurableSet s := measurable_snd hXo.measurableSet
  have e : bumpPair T δ hδ = fun p : Ω × ℂ => if hp : p ∈ s then Gsub ⟨p.2, hp⟩ p.1 else 0 := by
    funext p
    by_cases hp : p ∈ s
    · have hp' : δ < p.2.im := hp
      simp only [hp, dite_true, bumpPair, hp', ↓reduceIte]
      rfl
    · have hp' : ¬ δ < p.2.im := hp
      simp only [hp, dite_false, bumpPair, hp', ↓reduceIte]
  rw [e]
  refine Measurable.dite (f := fun q : s => Gsub ⟨q.1.2, q.2⟩ q.1.1) ?_ measurable_const hsm
  exact hJ.comp ((Measurable.subtype_mk (measurable_snd.comp measurable_subtype_coe)).prodMk
    (measurable_fst.comp measurable_subtype_coe))

omit [MeasurableSpace Ω] in
/-- On a harmonic patch, the normalized bump pairing is the harmonic representative. -/
lemma bumpPair_eq_of_harmonic {T : Ω → DistOn upperHalfPlaneOpens} {δ : ℝ} (hδ : 0 < δ)
    {ω : Ω} {y : ℂ} {V : Set ℂ} (hV : IsOpen V) {v : ℂ → ℝ}
    (hv : InnerProductSpace.HarmonicOnNhd v V)
    (hTv : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ V → T ω φ = ∫ z, v z * φ z)
    (hB : closedBall y δ ⊆ V) (hVH : V ⊆ H) :
    bumpPair T δ hδ (ω, y) / (δ ^ 2 * GFF.bumpMass) = v y := by
  have hy : δ < y.im := (closedBall_subset_H_iff hδ.le).1 (hB.trans hVH)
  have hm : 0 < δ ^ 2 * GFF.bumpMass := by have := GFF.bumpMass_pos; positivity
  have hts : tsupport (bumpTestH δ hδ y) ⊆ V := by
    rw [coe_bumpTestH_of_lt hδ hy]
    exact (GFF.tsupport_bumpFun_subset hδ).trans hB
  have e : bumpPair T δ hδ (ω, y) = T ω (bumpTestH δ hδ y) := by
    simp only [bumpPair, hy, ↓reduceIte]
  rw [e, hTv _ hts, coe_bumpTestH_of_lt hδ hy,
    GFF.integral_mul_bumpFun_of_harmonic hV hv hδ hB, mul_div_cancel_right₀ _ hm.ne']

end Pair

end LocalSets
end InteractingSLE

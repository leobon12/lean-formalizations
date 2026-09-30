import QuantumZipper.Proofs.GFF.K3.MixedLocal
import QuantumZipper.Proofs.GFF.CircleMeanValue
import QuantumZipper.Proofs.GFF.CircleFubini
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
# Annulus fields as Riesz vectors (GFF-K3 node M2, projection form)

Blueprint: `blueprint/GFF_K3_BLUEPRINT.md`, §3.M (M2).

* `annulusFeat D z s s'`: the element `(2π)^{-1/2} annulusField z s s'` of `GradSpace D`.
* `inner_annulusFeat_gradFeat`: for `f ∈ mixedSpace D S` and a local disc of radius `s'`,
  `⟪annulusFeat, gradFeat f⟫ = ∫ f d fold_{z,s} − ∫ f d fold_{z,s'}` (M1).
* `isAdmissibleDual_foldedCircle_of_local`: local folded circles are admissible (M4).
* `rieszVec_annulus_eq_starProjection`: `v_{fold s} − v_{fold s'}` is the orthogonal projection
  of `annulusFeat` onto `gradClosure D (mixedSpace D S)`.
* `rieszVec_annulus`: the blueprint form `v_{fold s} − v_{fold s'} = annulusFeat`, under the
  hypothesis `annulusFeat ∈ gradClosure` (the approximation by smooth radial profiles is not
  formalized here).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Real Topology ComplexConjugate ENNReal NNReal RealInnerProductSpace

namespace QuantumZipper.K3

/-! ## Local discs -/

theorem LocalBall.mono {D S : Set ℂ} {z w : ℂ} {R r : ℝ} (h : LocalBall D S z R) (hw : w ∈ Hbar)
    (hr : 0 < r) (hwr : r + dist w z ≤ R) : LocalBall D S w r := by
  have hsub : closedBall w r ⊆ closedBall z R := closedBall_subset_closedBall' hwr
  exact ⟨hw, hr, h.2.2.1, fun x hx => h.2.2.2.1 ⟨hsub hx.1, hx.2⟩,
    fun x hx => h.2.2.2.2 ⟨hsub hx.1, hx.2⟩⟩

theorem norm_conj_sub_le {y z : ℂ} (hy : y.im < 0) (hz : 0 ≤ z.im) :
    ‖conj y - z‖ ≤ ‖y - z‖ := by
  have hcH : 0 ≤ (conj y).im := by rw [Complex.conj_im]; linarith
  have h := norm_sub_le_norm_sub_conj hcH hz
  rwa [← map_sub, Complex.norm_conj] at h

/-- The folded circle is carried by `closedBall z r ∩ Hbar`. -/
theorem foldedCircle_compl_eq_zero {z : ℂ} (hz : z ∈ Hbar) {r : ℝ} (hr : 0 ≤ r) :
    foldedCircle z r (closedBall z r ∩ Hbar)ᶜ = 0 := by
  have hz' : 0 ≤ z.im := hz
  have hKm : MeasurableSet (closedBall z r ∩ Hbar) :=
    isClosed_closedBall.measurableSet.inter isClosed_Hbar.measurableSet
  rw [foldedCircle, Measure.map_apply measurable_foldH hKm.compl, measure_eq_zero_iff_ae_notMem]
  · filter_upwards [CircleMV.ae_circleUnif z r] with w hw
    intro hwK
    apply hwK
    have hwr : ‖w - z‖ = r := by rw [hw, abs_of_nonneg hr]
    refine ⟨?_, CircleFubini.foldH_mem_Hbar' w⟩
    rw [mem_closedBall, dist_eq_norm]
    by_cases him : 0 ≤ w.im
    · rw [CircleFubini.foldH_of_mem' him]; exact hwr.le
    · have hf : foldH w = conj w := by simp [foldH, him]
      rw [hf]
      exact (norm_conj_sub_le (not_le.mp him) hz').trans hwr.le

/-- **M4 for folded circles.** A folded circle well inside a local disc is admissible. -/
theorem isAdmissibleDual_foldedCircle_of_local {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {z : ℂ} {R0 r : ℝ}
    (hloc : LocalBall D S z R0) (hr : 0 < r) (hrR : r < R0) :
    IsAdmissibleDual D (mixedSpace D S) (foldedCircle z r) := by
  have hz := hloc.1
  set R : ℝ := (R0 - r) / 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  refine isAdmissibleDual_mixed_of_local hD hDH hb hS
    ((isCompact_closedBall z r).inter_right isClosed_Hbar) hR (fun w hw => ?_)
    (isAdmissibleH_foldedCircle hz hr) (foldedCircle_compl_eq_zero hz hr.le)
  refine hloc.mono hw.2 (by linarith) ?_
  have : dist w z ≤ r := hw.1
  rw [hRdef]; linarith

/-! ## The annulus feature -/

/-- `(z, i) ↦ (2π)^{-1/2} ⟪annulusField z s s', e_i⟫`. -/
def annulusVal (z : ℂ) (s s' : ℝ) (p : ℂ × Fin 2) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ *
    (if p.2 = 0 then (annulusField z s s' p.1).re else (annulusField z s s' p.1).im)

open Classical in
/-- The annulus feature `(2π)^{-1/2} annulusField ∈ GradSpace D` (`0` if not square integrable). -/
def annulusFeat (D : Set ℂ) (z : ℂ) (s s' : ℝ) : GradSpace D :=
  if h : MemLp (annulusVal z s s') 2 (gradMeasure D) then h.toLp _ else 0

theorem measurable_annulusTerm (c : ℂ) (s s' : ℝ) : Measurable (annulusTerm c s s') := by
  unfold annulusTerm
  refine Measurable.ite ?_ ?_ measurable_const
  · have hm : Measurable fun x : ℂ => ‖x - c‖ := (measurable_id.sub_const c).norm
    exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  · simp_rw [neg_div]
    exact (measurable_radial_vec c).neg

theorem measurable_annulusField (z : ℂ) (s s' : ℝ) : Measurable (annulusField z s s') := by
  have e : annulusField z s s' = fun x => annulusTerm z s s' x + annulusTerm (conj z) s s' x :=
    funext (annulusField_eq z s s')
  rw [e]
  exact (measurable_annulusTerm z s s').add (measurable_annulusTerm (conj z) s s')

theorem norm_annulusTerm_le (c : ℂ) {s s' : ℝ} (hs : 0 < s) (x : ℂ) :
    ‖annulusTerm c s s' x‖ ≤ s⁻¹ := by
  unfold annulusTerm
  split_ifs with h
  · rw [neg_div, norm_neg, norm_radial_vec]; exact inv_anti₀ hs h.1.le
  · rw [norm_zero]; exact (inv_pos.mpr hs).le

theorem measurable_annulusVal (z : ℂ) (s s' : ℝ) : Measurable (annulusVal z s s') := by
  unfold annulusVal
  have hA := measurable_annulusField z s s'
  refine measurable_const.mul (Measurable.ite (measurable_snd (measurableSet_singleton 0)) ?_ ?_)
  · exact Complex.measurable_re.comp (hA.comp measurable_fst)
  · exact Complex.measurable_im.comp (hA.comp measurable_fst)

theorem memLp_annulusVal {D : Set ℂ} (hb : Bornology.IsBounded D) (z : ℂ) {s s' : ℝ}
    (hs : 0 < s) : MemLp (annulusVal z s s') 2 (gradMeasure D) := by
  have : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  refine MemLp.of_bound (measurable_annulusVal z s s').aestronglyMeasurable
    ((Real.sqrt (2 * Real.pi))⁻¹ * (2 * s⁻¹)) (Eventually.of_forall fun p => ?_)
  have hA : ‖annulusField z s s' p.1‖ ≤ 2 * s⁻¹ := by
    rw [annulusField_eq, two_mul]
    exact (norm_add_le _ _).trans (add_le_add (norm_annulusTerm_le z hs _)
      (norm_annulusTerm_le _ hs _))
  unfold annulusVal
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  split_ifs
  · exact (Complex.abs_re_le_norm _).trans hA
  · exact (Complex.abs_im_le_norm _).trans hA

theorem sum_gradVal_mul_annulusVal (f : ℂ → ℝ) (z : ℂ) (s s' : ℝ) (x : ℂ) :
    ∑ i : Fin 2, gradVal f (x, i) * annulusVal z s s' (x, i) =
      (2 * Real.pi)⁻¹ * fderiv ℝ f x (annulusField z s s' x) := by
  have hc : (Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹ = (2 * Real.pi)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]
  rw [Fin.sum_univ_two, clm_complex_apply (fderiv ℝ f x) (annulusField z s s' x)]
  simp only [gradVal, annulusVal, gradVec]
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_ne_zero]
  rw [← hc]
  ring

/-- **M2, pairing.** `⟪annulusFeat, gradFeat f⟫ = ∫ f d fold_{z,s} − ∫ f d fold_{z,s'}`. -/
theorem inner_annulusFeat_gradFeat {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D)
    (hS : S ⊆ {z : ℂ | z.im = 0}) {z : ℂ} {s s' : ℝ} (hloc : LocalBall D S z s') (hs : 0 < s)
    (hss' : s < s') {f : ℂ → ℝ} (hf : f ∈ mixedSpace D S) :
    ⟪annulusFeat D z s s', gradFeat D f⟫ =
      ∫ x, f x ∂(foldedCircle z s) - ∫ x, f x ∂(foldedCircle z s') := by
  have hz := hloc.1
  have hz' : 0 ≤ z.im := hz
  have hf1 : ContDiff ℝ 1 f := hf.1.of_le one_le_smooth
  have hA := memLp_annulusVal hb z hs (s' := s') (D := D)
  have hG := memLp_gradVal hf1 hf.2.1 (D := D)
  have hfeat : annulusFeat D z s s' = hA.toLp _ := by simp [annulusFeat, hA]
  have hgrad : gradFeat D f = hG.toLp _ := by simp [gradFeat, hG]
  rw [hfeat, hgrad, L2.inner_def]
  have h1 : ∫ p, ⟪hA.toLp (annulusVal z s s') p, hG.toLp (gradVal f) p⟫ ∂(gradMeasure D) =
      ∫ p, gradVal f p * annulusVal z s s' p ∂(gradMeasure D) := by
    refine integral_congr_ae ?_
    filter_upwards [hA.coeFn_toLp, hG.coeFn_toLp] with p h1 h2
    rw [h1, h2, RCLike.inner_apply, conj_trivial]
  rw [h1]
  have hint : Integrable (fun p => gradVal f p * annulusVal z s s' p) (gradMeasure D) :=
    hG.integrable_mul hA
  rw [integral_prod _ hint]
  simp only [integral_count, sum_gradVal_mul_annulusVal]
  rw [integral_const_mul, ← annulus_identity hf1 hz hs hss']
  congr 1
  -- `∫_D = ∫_H`: the annulus field vanishes on `H \ D`.
  refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_H_mx hDH
    (fun x hx => ?_)).symm
  have hxH : x ∈ H := hx.1
  have hxD : x ∉ D := hx.2
  have hx' : 0 ≤ x.im := le_of_lt (show 0 < x.im from hxH)
  have h1 : ¬ ‖x - z‖ < s' := fun h => hxD (hloc.mem_of_mem_H hD hS hxH h.le)
  have h2 : ¬ ‖x - conj z‖ < s' := fun h =>
    h1 ((norm_sub_le_norm_sub_conj hx' hz').trans_lt h)
  simp [annulusField, h1, h2]

/-! ## Riesz uniqueness and M2 -/

/-- Two elements of `gradClosure D V` with the same pairings against `gradFeat '' V` agree. -/
theorem eq_of_mem_gradClosure_of_inner_eq {D : Set ℂ} {V : Set (ℂ → ℝ)} {v w : GradSpace D}
    (hv : v ∈ gradClosure D V) (hw : w ∈ gradClosure D V)
    (h : ∀ f ∈ V, ⟪v, gradFeat D f⟫ = ⟪w, gradFeat D f⟫) : v = w := by
  set K : Submodule ℝ (GradSpace D) := (ℝ ∙ (v - w))ᗮ with hK
  have hspan : Submodule.span ℝ (gradFeat D '' V) ≤ K := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    rw [SetLike.mem_coe, hK, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left,
      h f hf, sub_self]
  have hcl : gradClosure D V ≤ K :=
    Submodule.topologicalClosure_minimal _ hspan (Submodule.isClosed_orthogonal _)
  have hmem : v - w ∈ K := hcl (sub_mem hv hw)
  rw [hK, Submodule.mem_orthogonal_singleton_iff_inner_right, real_inner_self_eq_norm_sq] at hmem
  have : ‖v - w‖ = 0 := by nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **M2 (projection form).** In a local problem, the difference of the Riesz vectors of two
concentric folded circles is the orthogonal projection of the annulus feature onto
`gradClosure D (mixedSpace D S)`. -/
theorem rieszVec_annulus_eq_starProjection {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {z : ℂ} {s s' R0 : ℝ}
    (hloc : LocalBall D S z R0) (hs : 0 < s) (hss' : s < s') (hs'R : s' < R0) :
    rieszVec D (mixedSpace D S) (foldedCircle z s) -
        rieszVec D (mixedSpace D S) (foldedCircle z s') =
      (gradClosure D (mixedSpace D S)).starProjection (annulusFeat D z s s') := by
  set V := mixedSpace D S with hVdef
  set M := gradClosure D V with hMdef
  have hV : IsDNSpace D V := isDNSpace_mixedSpace D S
  have hloc' : LocalBall D S z s' := hloc.mono hloc.1 (hs.trans hss') (by simp; linarith)
  have hμs := isAdmissibleDual_foldedCircle_of_local hD hDH hb hS hloc hs (hss'.trans hs'R)
  have hμs' := isAdmissibleDual_foldedCircle_of_local hD hDH hb hS hloc (hs.trans hss') hs'R
  have hmemL : rieszVec D V (foldedCircle z s) - rieszVec D V (foldedCircle z s') ∈ M :=
    sub_mem rieszVec_mem rieszVec_mem
  have hmemR : M.starProjection (annulusFeat D z s s') ∈ M := M.starProjection_apply_mem _
  by_cases hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g
  · refine eq_of_mem_gradClosure_of_inner_eq hmemL hmemR fun f hf => ?_
    have hproj : ⟪M.starProjection (annulusFeat D z s s'), gradFeat D f⟫ =
        ⟪annulusFeat D z s s', gradFeat D f⟫ := by
      have h0 := M.starProjection_inner_eq_zero (annulusFeat D z s s') (gradFeat D f)
        (gradFeat_mem_gradClosure hf)
      rw [inner_sub_left] at h0
      linarith
    rw [hproj, inner_annulusFeat_gradFeat hD hDH hb hS hloc' hs hss' hf, inner_sub_left,
      pair_rieszVec hV hμs hpos f hf, pair_rieszVec hV hμs' hpos f hf]
  · rw [eq_zero_of_mem_gradClosure_of_nopos hV hpos hmemL,
      eq_zero_of_mem_gradClosure_of_nopos hV hpos hmemR]

/-- **M2.** If the annulus feature lies in `gradClosure D (mixedSpace D S)`, it is the difference
of the Riesz vectors of the two folded circles. -/
theorem rieszVec_annulus {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {z : ℂ} {s s' R0 : ℝ}
    (hloc : LocalBall D S z R0) (hs : 0 < s) (hss' : s < s') (hs'R : s' < R0)
    (hmem : annulusFeat D z s s' ∈ gradClosure D (mixedSpace D S)) :
    rieszVec D (mixedSpace D S) (foldedCircle z s) -
        rieszVec D (mixedSpace D S) (foldedCircle z s') = annulusFeat D z s s' := by
  rw [rieszVec_annulus_eq_starProjection hD hDH hb hS hloc hs hss' hs'R,
    Submodule.starProjection_eq_self_iff.mpr hmem]

/-! ## Unconditional M2: smooth radial approximations of the annulus field

The annulus field is the gradient of the Lipschitz radial function
`log (max(s', |x−z|) / max(s, |x−z|)) + (z̄ term)`. We approximate it by smooth radial functions
`Φ_n(|x−z|²) + Φ_n(|x−z̄|²)` with `Φ_n' (u) = −ψ_n(u)/(2u)`, where `ψ_n` are smooth bumps
increasing to the indicator of `(s², s'²)`; the gradients converge in `L²` by dominated
convergence. (Own elementary argument: the 1-D fundamental theorem of calculus plus
dominated convergence; no published formal proof was found for this specific density step.) -/

/-- Smooth bumps `ψ n` on `ℝ` with values in `[0,1]`, vanishing on `(-∞, a]` and near `b`, and
converging pointwise to the indicator of `(a, b)`. -/
theorem exists_bumps_Ioo {a b : ℝ} (hab : a < b) :
    ∃ ψ : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ n)) ∧
      (∀ n u, 0 ≤ ψ n u ∧ ψ n u ≤ 1) ∧ (∀ n u, u ≤ a → ψ n u = 0) ∧
      (∀ n, ∃ ρ < b, ∀ u, ρ ≤ u → ψ n u = 0) ∧
      (∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 ((Ioo a b).indicator 1 u))) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = (a + b) / 2 := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w : ℝ, w = (b - a) / 2 := ⟨_, rfl⟩
  have hw : 0 < w := by rw [hwd]; linarith
  let β : ℕ → ContDiffBump c := fun n =>
    { rIn := w * (n + 1) / (n + 3)
      rOut := w * (n + 2) / (n + 3)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        apply div_lt_div_of_pos_right _ (by positivity)
        nlinarith }
  have hrOut : ∀ n : ℕ, w * (n + 2) / (n + 3) < w := fun n => by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hrOut0 : ∀ n : ℕ, 0 ≤ w * (n + 2) / (n + 3) := fun n => by positivity
  refine ⟨fun n => β n, fun n => (β n).contDiff, fun n u => ⟨(β n).nonneg, (β n).le_one⟩,
    fun n u hu => ?_, fun n => ⟨c + w * (n + 2) / (n + 3), ?_, fun u hu => ?_⟩, fun u => ?_⟩
  · apply (β n).zero_of_le_dist
    rw [Real.dist_eq]
    show w * (n + 2) / (n + 3) ≤ |u - c|
    rw [abs_of_nonpos (by linarith)]
    linarith [hrOut n]
  · linarith [hrOut n]
  · apply (β n).zero_of_le_dist
    rw [Real.dist_eq]
    show w * (n + 2) / (n + 3) ≤ |u - c|
    rw [abs_of_nonneg (by linarith [hrOut0 n])]
    linarith
  · by_cases hu : u ∈ Ioo a b
    · rw [indicator_of_mem hu, Pi.one_apply]
      have hd : |u - c| < w := by
        rw [abs_lt]; constructor <;> linarith [hu.1, hu.2]
      have hpos : 0 < w - |u - c| := by linarith
      obtain ⟨N, hN⟩ := exists_nat_gt (3 * w / (w - |u - c|))
      rw [div_lt_iff₀ hpos] at hN
      refine tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N, fun n hn => ?_⟩)
      symm
      apply (β n).one_of_mem_closedBall
      rw [mem_closedBall, Real.dist_eq]
      show |u - c| ≤ w * (n + 1) / (n + 3)
      rw [le_div_iff₀ (by positivity)]
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [abs_nonneg (u - c), mul_le_mul_of_nonneg_right hn' hpos.le]
    · rw [indicator_of_notMem hu]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
      symm
      apply (β n).zero_of_le_dist
      rw [Real.dist_eq]
      show w * (n + 2) / (n + 3) ≤ |u - c|
      have : w ≤ |u - c| := by
        simp only [mem_Ioo, not_and_or, not_lt] at hu
        rcases hu with h | h
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      linarith [hrOut n]

theorem contDiff_neg_div_two_mul {ψ : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (h0 : ∀ u, u ≤ a → ψ u = 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => -ψ u / (2 * u)) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  rcases lt_or_ge u a with hu | hu
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hu] with t ht
    rw [h0 t (le_of_lt ht)]; simp
  · have hu0 : 0 < u := by linarith
    exact hψ.contDiffAt.neg.div (contDiffAt_const.mul contDiffAt_id) (by positivity)

/-- Smooth radial profiles `Φ n` with `Φ n' (u) = −ψ n (u)/(2u)`, vanishing near `[b, ∞)`. -/
theorem exists_radial_profiles {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ (Φ ψ : ℕ → ℝ → ℝ), (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φ n)) ∧
      (∀ n u, HasDerivAt (Φ n) (-ψ n u / (2 * u)) u) ∧
      (∀ n u, 0 ≤ ψ n u ∧ ψ n u ≤ 1) ∧ (∀ n u, u ≤ a → ψ n u = 0) ∧
      (∀ n, ∃ ρ < b, ∀ u, ρ ≤ u → Φ n u = 0) ∧
      (∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 ((Ioo a b).indicator 1 u))) ∧
      (∀ n u, Φ n u = ∫ t in b..u, -ψ n t / (2 * t)) ∧
      (∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => -ψ n u / (2 * u))) ∧
      (∀ n u, b ≤ u → ψ n u = 0) := by
  obtain ⟨ψ, hψs, hψ01, hψa, hψb, hψlim⟩ := exists_bumps_Ioo hab
  have hg : ∀ n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => -ψ n u / (2 * u)) :=
    fun n => contDiff_neg_div_two_mul ha (hψs n) (hψa n)
  have hderiv : ∀ n u, HasDerivAt (fun v => ∫ t in b..v, -ψ n t / (2 * t))
      (-ψ n u / (2 * u)) u :=
    fun n u => ((hg n).continuous.integral_hasStrictDerivAt b u).hasDerivAt
  refine ⟨fun n v => ∫ t in b..v, -ψ n t / (2 * t), ψ, fun n => ?_, hderiv, hψ01, hψa,
    fun n => ?_, hψlim, fun _ _ => rfl, hg, fun n u hu => ?_⟩
  · rw [contDiff_infty_iff_deriv]
    refine ⟨fun u => (hderiv n u).differentiableAt, ?_⟩
    have : deriv (fun v => ∫ t in b..v, -ψ n t / (2 * t)) = fun u => -ψ n u / (2 * u) :=
      funext fun u => (hderiv n u).deriv
    rw [this]; exact hg n
  · obtain ⟨ρ, hρb, hρ⟩ := hψb n
    refine ⟨ρ, hρb, fun u hu => ?_⟩
    simp only
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_, intervalIntegral.integral_zero]
    intro t ht
    have : ρ ≤ t := by
      rcases le_total b u with h | h
      · rw [uIcc_of_le h] at ht; linarith [ht.1]
      · rw [uIcc_of_ge h] at ht; linarith [ht.1]
    simp [hρ t this]
  · obtain ⟨ρ, hρb, hρ⟩ := hψb n
    exact hρ u (by linarith)

/-- The radial vector `−(ψ(‖x−c‖²)/‖x−c‖²)(x − c)`. -/
def radVec (ψ : ℝ → ℝ) (c x : ℂ) : ℂ := (-(ψ (‖x - c‖ ^ 2) / ‖x - c‖ ^ 2)) • (x - c)

theorem hasFDerivAt_radial {Φ ψ : ℝ → ℝ} (hΦ : ∀ u, HasDerivAt Φ (-ψ u / (2 * u)) u)
    (c x : ℂ) : HasFDerivAt (fun y => Φ (‖y - c‖ ^ 2)) (innerSL ℝ (radVec ψ c x)) x := by
  have h1 : HasFDerivAt (fun y : ℂ => y - c) (ContinuousLinearMap.id ℝ ℂ) x :=
    (hasFDerivAt_id x).sub_const c
  have h2 : HasFDerivAt (fun y : ℂ => ‖y - c‖ ^ 2)
      (2 • (innerSL ℝ (x - c)).comp (ContinuousLinearMap.id ℝ ℂ)) x := h1.norm_sq
  have h := (hΦ (‖x - c‖ ^ 2)).comp_hasFDerivAt x h2
  refine h.congr_fderiv (ContinuousLinearMap.ext (fun v : ℂ => ?_))
  simp only [radVec, innerSL_apply_apply, real_inner_smul_left, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, id_eq, ContinuousLinearMap.coe_id', smul_eq_mul,
    nsmul_eq_mul]
  push_cast
  ring

/-- The smooth radial approximation `Φ(‖x−z‖²) + Φ(‖x−z̄‖²)`. -/
def radialApprox (Φ : ℝ → ℝ) (z x : ℂ) : ℝ := Φ (‖x - z‖ ^ 2) + Φ (‖x - conj z‖ ^ 2)

theorem fderiv_radialApprox_apply {Φ ψ : ℝ → ℝ} (hΦ : ∀ u, HasDerivAt Φ (-ψ u / (2 * u)) u)
    (z x v : ℂ) :
    fderiv ℝ (radialApprox Φ z) x v = ⟪radVec ψ z x + radVec ψ (conj z) x, v⟫ := by
  have h := (hasFDerivAt_radial hΦ z x).add (hasFDerivAt_radial hΦ (conj z) x)
  have e : radialApprox Φ z = (fun y => Φ (‖y - z‖ ^ 2)) + (fun y => Φ (‖y - conj z‖ ^ 2)) := rfl
  rw [e, h.fderiv, ContinuousLinearMap.add_apply, innerSL_apply_apply, innerSL_apply_apply,
    inner_add_left]

theorem gradVal_radialApprox {Φ ψ : ℝ → ℝ} (hΦ : ∀ u, HasDerivAt Φ (-ψ u / (2 * u)) u)
    (z : ℂ) (p : ℂ × Fin 2) :
    gradVal (radialApprox Φ z) p = (Real.sqrt (2 * Real.pi))⁻¹ *
      (if p.2 = 0 then (radVec ψ z p.1 + radVec ψ (conj z) p.1).re
        else (radVec ψ z p.1 + radVec ψ (conj z) p.1).im) := by
  obtain ⟨x, i⟩ := p
  simp only [gradVal, gradVec, fderiv_radialApprox_apply hΦ]
  split_ifs <;> simp [Complex.inner] <;> left <;> ring

theorem norm_radVec_le {ψ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (h01 : ∀ u, 0 ≤ ψ u ∧ ψ u ≤ 1)
    (h0 : ∀ u, u ≤ s ^ 2 → ψ u = 0) (c x : ℂ) : ‖radVec ψ c x‖ ≤ s⁻¹ := by
  unfold radVec
  rw [norm_smul, Real.norm_eq_abs]
  by_cases h : ‖x - c‖ ^ 2 ≤ s ^ 2
  · rw [h0 _ h]; simp; positivity
  · push_neg at h
    have hr : s < ‖x - c‖ := by nlinarith [norm_nonneg (x - c)]
    have hr0 : 0 < ‖x - c‖ := hs.trans hr
    rw [abs_neg, abs_div, abs_of_nonneg (h01 _).1, abs_of_nonneg (sq_nonneg _),
      div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ s⁻¹ * ‖x - c‖ := by rw [inv_mul_eq_div, le_div_iff₀ hs]; linarith
    nlinarith [mul_le_mul_of_nonneg_right (h01 (‖x - c‖ ^ 2)).2 hr0.le,
      mul_le_mul_of_nonneg_right h1 hr0.le]

theorem tendsto_radVec {ψ : ℕ → ℝ → ℝ} {s s' : ℝ} (hs : 0 < s) (hss' : s < s')
    (hlim : ∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 ((Ioo (s ^ 2) (s' ^ 2)).indicator 1 u)))
    (c x : ℂ) : Tendsto (fun n => radVec (ψ n) c x) atTop (𝓝 (annulusTerm c s s' x)) := by
  have h := (((hlim (‖x - c‖ ^ 2)).div_const (‖x - c‖ ^ 2)).neg).smul_const (x - c)
  show Tendsto (fun n => (-(ψ n (‖x - c‖ ^ 2) / ‖x - c‖ ^ 2)) • (x - c)) _ _
  convert h using 2
  unfold annulusTerm
  by_cases hin : s < ‖x - c‖ ∧ ‖x - c‖ < s'
  · have hmem : ‖x - c‖ ^ 2 ∈ Ioo (s ^ 2) (s' ^ 2) :=
      ⟨by nlinarith [hin.1], by nlinarith [hin.2, norm_nonneg (x - c)]⟩
    rw [if_pos hin, indicator_of_mem hmem, Pi.one_apply, Complex.real_smul]
    push_cast
    ring
  · have hmem : ‖x - c‖ ^ 2 ∉ Ioo (s ^ 2) (s' ^ 2) := fun h => hin
      ⟨by nlinarith [h.1, norm_nonneg (x - c)], by nlinarith [h.2, norm_nonneg (x - c), hs, hss']⟩
    rw [if_neg hin, indicator_of_notMem hmem]
    simp

theorem radialApprox_mem_mixedSpace {D S : Set ℂ} (hb : Bornology.IsBounded D) {z : ℂ}
    {s' ρ : ℝ} (hloc : LocalBall D S z s') {Φ : ℝ → ℝ}
    (hΦs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) (hΦ0 : ∀ u, ρ ≤ u → Φ u = 0)
    (hρ : ρ < s' ^ 2) : radialApprox Φ z ∈ mixedSpace D S := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (radialApprox Φ z) :=
    (hΦs.comp ((contDiff_id.sub contDiff_const).norm_sq ℝ)).add
      (hΦs.comp ((contDiff_id.sub contDiff_const).norm_sq ℝ))
  refine ⟨hsm, ?_, ?_⟩
  · have hc : Continuous fun x => ‖fderiv ℝ (radialApprox Φ z) x‖ ^ 2 :=
      ((hsm.continuous_fderiv smooth_ne_zero).norm).pow 2
    exact (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  · refine ⟨{x | ρ < ‖x - z‖ ^ 2 ∧ ρ < ‖x - conj z‖ ^ 2}, ?_, ?_, ?_⟩
    · exact (isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm.pow 2)).inter
        (isOpen_lt continuous_const ((continuous_id.sub continuous_const).norm.pow 2))
    · rintro y ⟨hyF, hyS⟩
      have hyH : 0 ≤ y.im := by
        have hcl : closure D ⊆ Hbar :=
          (closure_mono hloc.2.2.1).trans (isClosed_Hbar.closure_subset_iff.mpr H_subset_Hbar)
        exact hcl (frontier_subset_closure hyF)
      have hs'0 := hloc.2.1
      have h1 : ρ < ‖y - z‖ ^ 2 := by
        by_contra hle
        push_neg at hle
        apply hyS
        refine hloc.2.2.2.2 ⟨?_, hyF⟩
        rw [mem_closedBall, dist_eq_norm]
        nlinarith [norm_nonneg (y - z)]
      refine ⟨h1, h1.trans_le ?_⟩
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_norm_sub_conj hyH hloc.1) 2
    · rintro x ⟨h1, h2⟩
      simp [radialApprox, hΦ0 _ h1.le, hΦ0 _ h2.le]

/-- Smooth radial approximations of the annulus field in the mixed space, with gradient features
converging to `annulusFeat` in `L²`. -/
theorem exists_radialApprox_tendsto {D S : Set ℂ} (hb : Bornology.IsBounded D) {z : ℂ}
    {s s' : ℝ} (hloc : LocalBall D S z s') (hs : 0 < s) (hss' : s < s') :
    ∃ (Φ ψ : ℕ → ℝ → ℝ), (∀ n u, 0 ≤ ψ n u ∧ ψ n u ≤ 1) ∧ (∀ n u, u ≤ s ^ 2 → ψ n u = 0) ∧
      (∀ u, Tendsto (fun n => ψ n u) atTop (𝓝 ((Ioo (s ^ 2) (s' ^ 2)).indicator 1 u))) ∧
      (∀ n u, Φ n u = ∫ t in (s' ^ 2)..u, -ψ n t / (2 * t)) ∧
      (∀ n, Continuous (fun u => -ψ n u / (2 * u))) ∧ (∀ n u, s' ^ 2 ≤ u → ψ n u = 0) ∧
      (∀ n, radialApprox (Φ n) z ∈ mixedSpace D S) ∧
      Tendsto (fun n => gradFeat D (radialApprox (Φ n) z)) atTop
        (𝓝 (annulusFeat D z s s')) := by
  obtain ⟨Φ, ψ, hΦs, hΦd, hψ01, hψa, hΦb, hψlim, hΦint, hgs, hψb'⟩ :=
    exists_radial_profiles (a := s ^ 2) (b := s' ^ 2) (by positivity) (by nlinarith)
  have hmem : ∀ n, radialApprox (Φ n) z ∈ mixedSpace D S := fun n => by
    obtain ⟨ρ, hρ, hρ0⟩ := hΦb n
    exact radialApprox_mem_mixedSpace hb hloc (hΦs n) hρ0 hρ
  have : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  have hfin : IsFiniteMeasure (gradMeasure D) := by unfold gradMeasure; infer_instance
  have hGL : ∀ n, MemLp (gradVal (radialApprox (Φ n) z)) 2 (gradMeasure D) := fun n =>
    memLp_gradVal ((hmem n).1.of_le one_le_smooth) (hmem n).2.1
  have hA := memLp_annulusVal hb z hs (s' := s') (D := D)
  have hfeat : ∀ n, gradFeat D (radialApprox (Φ n) z) = (hGL n).toLp _ := fun n => by
    simp [gradFeat, hGL n]
  have hann : annulusFeat D z s s' = hA.toLp _ := by simp [annulusFeat, hA]
  set B : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ * (2 * s⁻¹) with hB
  have hbound : ∀ n p, ‖gradVal (radialApprox (Φ n) z) p‖ ≤ B := fun n p => by
    rw [gradVal_radialApprox (hΦd n), norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Real.sqrt_nonneg _))
    have hA' : ‖radVec (ψ n) z p.1 + radVec (ψ n) (conj z) p.1‖ ≤ 2 * s⁻¹ := by
      rw [two_mul]
      exact (norm_add_le _ _).trans (add_le_add (norm_radVec_le hs (hψ01 n) (hψa n) _ _)
        (norm_radVec_le hs (hψ01 n) (hψa n) _ _))
    split_ifs
    · exact (Complex.abs_re_le_norm _).trans hA'
    · exact (Complex.abs_im_le_norm _).trans hA'
  have hT : Tendsto (fun n => gradFeat D (radialApprox (Φ n) z)) atTop
      (𝓝 (annulusFeat D z s s')) := by
    simp_rw [hfeat]
    rw [hann, Lp.tendsto_Lp_iff_tendsto_eLpNorm'']
    refine tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num) (fun n => (hGL n).1) hA
      ?_ (Eventually.of_forall fun p => ?_)
    · refine unifIntegrable_of (by norm_num) (by norm_num) (fun n => (hGL n).1) fun ε _ =>
        ⟨Real.toNNReal (B + 1), fun n => ?_⟩
      have h0 : {p | Real.toNNReal (B + 1) ≤ ‖gradVal (radialApprox (Φ n) z) p‖₊}.indicator
          (gradVal (radialApprox (Φ n) z)) = 0 := by
        funext p
        refine indicator_of_notMem (fun hp => ?_) _
        have hp' : ((Real.toNNReal (B + 1) : ℝ≥0) : ℝ) ≤ ‖gradVal (radialApprox (Φ n) z) p‖ :=
          NNReal.coe_le_coe.mpr hp
        have hB0 : 0 ≤ B := by rw [hB]; positivity
        rw [Real.coe_toNNReal _ (by linarith)] at hp'
        linarith [hbound n p]
      rw [h0, eLpNorm_zero]
      positivity
    · simp only [gradVal_radialApprox (hΦd _), annulusVal, annulusField_eq]
      have hlim := (tendsto_radVec (ψ := ψ) (s' := s') hs hss' hψlim z p.1).add
        (tendsto_radVec (ψ := ψ) (s' := s') hs hss' hψlim (conj z) p.1)
      refine Tendsto.const_mul _ ?_
      split_ifs
      · exact (Complex.continuous_re.tendsto _).comp hlim
      · exact (Complex.continuous_im.tendsto _).comp hlim
  exact ⟨Φ, ψ, hψ01, hψa, hψlim, hΦint, fun n => (hgs n).continuous, hψb', hmem, hT⟩

/-- **M2, membership.** In a local disc of radius `s'`, the annulus feature lies in the closure of
the gradients of the mixed test space. -/
theorem annulusFeat_mem_gradClosure {D S : Set ℂ} (hb : Bornology.IsBounded D) {z : ℂ}
    {s s' : ℝ} (hloc : LocalBall D S z s') (hs : 0 < s) (hss' : s < s') :
    annulusFeat D z s s' ∈ gradClosure D (mixedSpace D S) := by
  obtain ⟨Φ, ψ, -, -, -, -, -, -, hmem, hT⟩ := exists_radialApprox_tendsto hb hloc hs hss'
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto hT
    (Eventually.of_forall fun n => gradFeat_mem_gradClosure (hmem n))

/-- **M2 (unconditional).** In a local problem, the difference of the Riesz vectors of two
concentric folded circles is the annulus feature. -/
theorem rieszVec_annulus' {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) {z : ℂ} {s s' R0 : ℝ}
    (hloc : LocalBall D S z R0) (hs : 0 < s) (hss' : s < s') (hs'R : s' < R0) :
    rieszVec D (mixedSpace D S) (foldedCircle z s) -
        rieszVec D (mixedSpace D S) (foldedCircle z s') = annulusFeat D z s s' :=
  rieszVec_annulus hD hDH hb hS hloc hs hss' hs'R
    (annulusFeat_mem_gradClosure hb (hloc.mono hloc.1 (hs.trans hss') (by simp; linarith)) hs hss')

end QuantumZipper.K3

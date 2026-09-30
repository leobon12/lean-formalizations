import QuantumZipper.Proofs.Thm18.R18RTDefs
import QuantumZipper.Proofs.Thm18.R18RoundUpDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT2 (D82), deterministic part: unzipping reads the field only at circles off the remaining curve

Sheffield, arXiv:1012.4797, §4.1 p. 48 ("`h` may be defined arbitrarily on the measure-zero set
`η`"); Berestycki–Powell, arXiv:2404.16642, Thm 8.16 and Rem 8.10 (p. 283): the unzipped field is
determined by `h` restricted to `ℍ ∖ η`. In the regularized model:

* `regEqOff_coordChange_of_pull`: if two fields have the same regularized pairings with every folded
  dyadic circle, pulled back by `ψ`, that stays off `K`, then `coordChange · ψ Q` of them agree
  (regularized) off `K`;
* `qBoundaryMeasureOn_congr_off`: fields equal (regularized) off a closed `K` have the same local
  boundary measure on every `I ⊆ ℝ` whose points are off `K` (the vague limit only tests
  compactly supported functions, at positive distance from `K`);
* `coordsFull_rescale_congr_off`, `pairRaw_rescale_congr_off`: the raw values of the rescaled
  fields at circles / test functions off the rescaled curve agree.

Own elementary bookkeeping (the regularized encoding; no published proof is needed), in the style of
`R18OffCongr.lean` and `R18RoundUpDet.lean`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- Pulled-back pairings agree at every folded dyadic circle that stays off `K`
⇒ the coordinate changes agree off `K`. -/
theorem regEqOff_coordChange_of_pull {K : Set ℂ} {x y : FieldSample} {ψ : ℂ → ℂ} (Q : ℝ)
    (h : ∀ (d : ℂ) (k : ℕ), CircleOff K d (radius k) →
      evalReg x ((foldedCircle d (radius k)).map ψ) =
        evalReg y ((foldedCircle d (radius k)).map ψ)) :
    RegEqOff K (coordChange x ψ Q) (coordChange y ψ Q) := by
  intro k z hz
  obtain ⟨δ, hδ, hK⟩ := hz
  have hev : (fun n => coordChange x ψ Q (foldedCircle (dyadicRoundC n z) (radius k))) =ᶠ[atTop]
      fun n => coordChange y ψ Q (foldedCircle (dyadicRoundC n z) (radius k)) := by
    filter_upwards [(RegClosure.tendsto_dyadicRoundC z).eventually_mem
      (Metric.ball_mem_nhds z (half_pos hδ))] with n hn
    simp only [coordChange]
    rw [h _ _ ⟨δ / 2, half_pos hδ, circleOff_of_nearU hK hn⟩]
  unfold avgReg
  rw [limUnder, limUnder, Filter.map_congr hev]

/-- Fields equal off a closed `K` have the same local boundary measure on every `I ⊆ ℝ` off `K`. -/
theorem qBoundaryMeasureOn_congr_off {K : Set ℂ} (hK : IsClosed K) {x y : FieldSample}
    (h : RegEqOff K x y) (γ : ℝ) {I : Set ℝ} (hI : ∀ t ∈ I, (t : ℂ) ∉ K) :
    qBoundaryMeasureOn γ x I = qBoundaryMeasureOn γ y I := by
  have key : ∀ f : ℝ → ℝ, HasCompactSupport f → tsupport f ⊆ I →
      (fun k => ∫ t, f t ∂(bdryApprox γ x k)) =ᶠ[atTop]
        fun k => ∫ t, f t ∂(bdryApprox γ y k) := by
    intro f hfc hfI
    have hS : IsCompact ((fun t : ℝ => (t : ℂ)) '' tsupport f) :=
      hfc.isCompact.image Complex.continuous_ofReal
    have hdis : Disjoint ((fun t : ℝ => (t : ℂ)) '' tsupport f) K := by
      refine Set.disjoint_left.2 ?_
      rintro _ ⟨t, ht, rfl⟩
      exact hI t (hfI ht)
    obtain ⟨r, hr0, hr⟩ := Metric.exists_pos_forall_lt_edist hS hK hdis
    have hd : (0 : ℝ) < r := hr0
    obtain ⟨N, hN⟩ := ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (half_pos hd))).exists_forall_of_atTop
    filter_upwards [Filter.eventually_ge_atTop N] with k hk
    have hfar : ∀ t ∈ tsupport f, avgReg x k (t : ℂ) = avgReg y k (t : ℂ) := by
      intro t ht
      refine h k _ (circleOff_of_far (by simp) (fun p hp => ?_) (hN k hk) hd)
      have := hr _ ⟨t, ht, rfl⟩ p hp
      rw [edist_dist] at this
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 (by simpa using this))
    have hms : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
    have hz : ∀ t, t ∉ tsupport f → f t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
    have hμ : (bdryApprox γ x k).restrict (tsupport f) =
        (bdryApprox γ y k).restrict (tsupport f) := by
      simp only [bdryApprox]
      rw [restrict_withDensity hms, restrict_withDensity hms]
      refine withDensity_congr_ae ((ae_restrict_iff' hms).2 (ae_of_all _ fun t ht => ?_))
      simp only [hfar t ht]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := bdryApprox γ x k) hz,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := bdryApprox γ y k) hz, hμ]
  have hP : IsVagueLimitOnR I (bdryApprox γ x) = IsVagueLimitOnR I (bdryApprox γ y) := by
    funext ν
    apply propext
    unfold IsVagueLimitOnR
    refine and_congr_right fun _ => and_congr_right fun _ => forall_congr' fun f => ?_
    refine imp_congr_right fun _ => imp_congr_right fun hfc => imp_congr_right fun hfI => ?_
    exact tendsto_congr' (key f hfc hfI)
  unfold qBoundaryMeasureOn
  rw [hP]

/-- Scaling of `CircleOff`: a folded circle off `L` is, after scaling by `a > 0`, off
`{w | a⁻¹ w ∈ L}`. -/
theorem circleOff_scaleRT {L : Set ℂ} {d : ℂ} {r a : ℝ} (ha : 0 < a) (hc : CircleOff L d r) :
    CircleOff {w | ((a⁻¹ : ℝ) : ℂ) * w ∈ L} ((a : ℂ) * d) (a * r) := by
  obtain ⟨δ, hδ, hK⟩ := hc
  have hai : 0 < a⁻¹ := inv_pos.2 ha
  refine ⟨a * δ, by positivity, fun w hw hwK => ?_⟩
  set w' : ℂ := ((a⁻¹ : ℝ) : ℂ) * w with hw'
  have hww : (a : ℂ) * w' = w := by
    rw [hw', Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ha.ne'),
      one_mul]
  have hdist : dist w ((a : ℂ) * d) = a * dist w' d := by
    rw [← hww, dist_eq_norm, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ha]
  have h1 : |dist w' d - r| < δ := by
    rw [hdist, ← mul_sub, abs_mul, abs_of_pos ha] at hw
    exact lt_of_mul_lt_mul_left hw ha.le
  refine hK w' h1 ?_
  have : foldH w' = ((a⁻¹ : ℝ) : ℂ) * foldH w := by
    rw [hw', Thm18Asm.foldH_mul_ofReal hai]
  rw [this]
  exact hwK

/-- The raw values of the rescaled fields at a folded circle off `L` agree, when the fields agree
(regularized) off `{w | a⁻¹ w ∈ L}`. -/
theorem rescale_foldedCircle_congr_off {L : Set ℂ} {x y : FieldSample} {a : ℝ} (ha : 0 < a)
    (h : RegEqOff {w | ((a⁻¹ : ℝ) : ℂ) * w ∈ L} x y) (Q : ℝ) {d : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hc : CircleOff L d r) :
    rescale x Q a (foldedCircle d r) = rescale y Q a (foldedCircle d r) := by
  simp only [rescale, coordChange]
  rw [Thm18Asm.foldedCircle_map_mul ha]
  congr 1
  exact evalReg_foldedCircle_congr_of_regEqOff h (by positivity) (circleOff_scaleRT ha hc)

/-- The raw pairings of the rescaled fields with a test function whose support avoids the closed
set `L` agree, when the fields agree (regularized) off `{w | a⁻¹ w ∈ L}`. -/
theorem pairRaw_rescale_congr_off {L : Set ℂ} (hL : IsClosed L) {x y : FieldSample} {a : ℝ}
    (ha : 0 < a) (h : RegEqOff {w | ((a⁻¹ : ℝ) : ℂ) * w ∈ L} x y) (Q : ℝ) (ρ : TestFun H)
    (hρ : Disjoint (tsupport ρ.1) L) :
    pairRaw (rescale x Q a) ρ.1 = pairRaw (rescale y Q a) ρ.1 := by
  obtain ⟨r, hr0, hr⟩ := Metric.exists_pos_forall_lt_edist ρ.2.2.1 hL hρ
  have hd : (0 : ℝ) < r := hr0
  set K : Set ℂ := {w | ((a⁻¹ : ℝ) : ℂ) * w ∈ L} with hKdef
  set G : Set ℂ := {w | 0 ≤ w.im ∧ ∀ p ∈ K, a * r ≤ dist w p} with hGdef
  have hGc : IsClosed G := by
    have : G = {w : ℂ | 0 ≤ w.im} ∩ ⋂ p ∈ K, {w | a * r ≤ dist w p} := by
      ext w; simp [hGdef]
    rw [this]
    exact (isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_biInter fun p _ => isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hmul : Measurable fun w : ℂ => (a : ℂ) * w := measurable_const_mul _
  have hfar : ∀ w ∈ tsupport ρ.1, (a : ℂ) * w ∈ G := by
    intro w hw
    refine ⟨?_, fun p hp => ?_⟩
    · have : ((a : ℂ) * w).im = a * w.im := by simp
      rw [this]
      exact mul_nonneg ha.le (le_of_lt (ρ.2.2.2 hw))
    · set p' : ℂ := ((a⁻¹ : ℝ) : ℂ) * p with hp'
      have hpp : (a : ℂ) * p' = p := by
        rw [hp', Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast ha.ne'),
          one_mul]
      have h1 := hr w hw p' hp
      rw [edist_dist] at h1
      have h2 : (r : ℝ) ≤ dist w p' :=
        le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 (by simpa using h1))
      rw [← hpp, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha, ← dist_eq_norm]
      exact mul_le_mul_of_nonneg_left h2 ha.le
  have hae : ∀ f : ℂ → ℝ, (∀ z, z ∉ tsupport ρ.1 → f z = 0) →
      ∀ᵐ w ∂((volume.withDensity fun z => ENNReal.ofReal (f z)).map fun w => (a : ℂ) * w),
        0 ≤ w.im ∧ ∀ p ∈ K, a * r ≤ dist w p := by
    intro f hf
    rw [ae_map_iff hmul.aemeasurable hGc.measurableSet, ae_iff]
    have hm : MeasurableSet {z : ℂ | z ∉ tsupport ρ.1} :=
      (isClosed_tsupport ρ.1).isOpen_compl.measurableSet
    refine measure_mono_null (fun z hz => ?_) (show (volume.withDensity
      fun z => ENNReal.ofReal (f z)) {z : ℂ | z ∉ tsupport ρ.1} = 0 from ?_)
    · intro hzs
      exact hz (hfar z hzs)
    · rw [withDensity_apply _ hm, setLIntegral_congr_fun hm (g := fun _ => 0) (fun z hz => by
        show ENNReal.ofReal (f z) = 0
        rw [hf z hz, ENNReal.ofReal_zero]), lintegral_zero]
  have hpos := hae ρ.1 fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hneg := hae (fun z => -ρ.1 z) fun z hz => by
    simp [image_eq_zero_of_notMem_tsupport hz]
  have hdr : 0 < a * r := mul_pos ha hd
  simp only [pairRaw, rescale, coordChange]
  rw [evalReg_congr_of_regEqOff_far h hdr hpos, evalReg_congr_of_regEqOff_far h hdr hneg]

end R18
end QuantumZipper

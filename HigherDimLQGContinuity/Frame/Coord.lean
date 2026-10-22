import HigherDimLQGContinuity.Frame.Potential
import HigherDimLQGContinuity.Frame.Law
import HigherDimLQGMetric.LGF.Normalized
import HigherDimLQGMetric.Field.StandardBorel
import HigherDimLQGMetric.Frozen.SphereAvgSpec

/-!
# Pairing frame IV: the good set, frame shifts and the Lusin–Souslin inverse

Packet N3 (NA4 Details (a) A2, steps 4, 5, 7; blueprint Part C `c:prop-frame`, steps 1–3 and 5). NA4 §6.2 flags the
Lusin–Souslin plumbing as the risk of the packet; it is isolated here.

* `frameE d j = e_{ψ_j}` (the frame vectors) and `frameFunRd (frameE d) v = Σ_j v_j e_j`;
  `addFun g f_v` pairs with `ψ_i` as `g(ψ_i) + c_i v_i` and with `χ_k` as `g(χ_k) + Σ_{j ≤ k} b_{kj} v_j`.
* The good set `𝒢 = {g ∈ convSet : g_1(0) = 0, g(χ_k) = Σ_{j ≤ k} b_{kj} g(ψ_j) ∀ k}` (`frameGood`) is measurable,
  has full `normLGFLaw` measure (`ae_mem_frameGood`, from `sphereAvg_spec` and the relations of `Frame/Form.lean`) and
  is closed under the frame shifts `g ↦ g + f_v` (`addFun_frameE_mem_frameGood`).
* `Φ = frameCoord` is injective on `𝒢` (`frameCoord_injOn`: equal coordinates give equal `χ_k`-pairings, hence
  `g' = g + c` by `eq_addConst_of_forall_chi`, and `c = 0` by the normalization), so `Φ|_𝒢` is a measurable
  embedding of the standard Borel space `𝒢` (HDLM's `standardBorelSpace_distOn`, `MeasurableSet.standardBorel`,
  Mathlib's `Measurable.measurableEmbedding`), `Φ(𝒢)` is measurable, and there is a measurable `T₀` with
  `T₀ ∘ Φ = id` on `𝒢` (`exists_frameInv`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem frameFunRd_apply (e : ℕ → C(Rd d, ℝ)) (v : ℕ →₀ ℝ) (x : Rd d) :
    frameFunRd e v x = v.sum fun j c => c * e j x := by
  unfold frameFunRd Finsupp.sum
  rw [ContinuousMap.sum_apply]
  rfl

section Frame

variable [NeZero d]

/-- The frame vectors `e_j = e_{ψ_j}` (Part C `c:lem-frame-bessel`; `e_j = 0` for `c_j = 0`). -/
def frameE (d : ℕ) [NeZero d] (j : ℕ) : C(Rd d, ℝ) := framePot (frameGS d j)

theorem frameE_eq_zero_of_frameC_eq_zero {j : ℕ} (h : frameC d j = 0) : frameE d j = 0 := by
  rw [frameE, frameGS_eq_zero_of_frameC_eq_zero h, framePot_zero]

theorem integral_mul_frameFunRd (v : ℕ →₀ ℝ) {φ : TestRd d} (hφ0 : ∫ x, φ x = 0) :
    ∫ x, φ x * frameFunRd (frameE d) v x = v.sum fun j c => c * frameForm (frameGS d j) φ := by
  obtain ⟨M, D, hφ⟩ := exists_isBddSupp_testOn φ
  simp only [frameFunRd_apply, Finsupp.sum, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ =>
    ((integrable_mul_continuous_of_isBddSupp hφ (frameE d j).continuous).const_mul (v j)).congr
      (ae_of_all _ fun x => by simp only; ring)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have e : (fun x => φ x * (v j * frameE d j x)) = fun x => v j * (φ x * frameE d j x) := by
    funext x
    ring
  rw [e, integral_const_mul, frameE, integral_mul_framePot _ hφ0]

/-- `(g + f_v)(ψ_i) = g(ψ_i) + c_i v_i`. -/
theorem addFun_frameE_apply_frameGS (g : DistRd d) (v : ℕ →₀ ℝ) (i : ℕ) :
    addFun g (frameFunRd (frameE d) v) (frameGS d i) = g (frameGS d i) + frameC d i * v i := by
  classical
  rw [addFun_apply, integral_mul_frameFunRd v (integral_frameGS i)]
  congr 1
  simp only [frameGS_orthonormal, mul_ite, mul_zero]
  rw [Finsupp.sum_ite_eq' v i (fun j c => c * frameC d j)]
  split_ifs with hi
  · rw [mul_comm]
  · rw [Finsupp.notMem_support_iff.1 hi, mul_zero]

/-- `(g + f_v)(χ_k) = g(χ_k) + Σ_{j ≤ k} b_{kj} v_j`. -/
theorem addFun_frameE_apply_frameChi (g : DistRd d) (v : ℕ →₀ ℝ) (k : ℕ) :
    addFun g (frameFunRd (frameE d) v) (frameChi d k) =
      g (frameChi d k) + ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * v j := by
  classical
  rw [addFun_apply, integral_mul_frameFunRd v (integral_frameChi k)]
  congr 1
  unfold Finsupp.sum
  have hf : ∀ j, frameForm (frameGS d j) (frameChi d k) = frameGSCoef d k j := fun j =>
    frameForm_comm _ _
  simp only [hf]
  have h1 : ∑ j ∈ v.support, v j * frameGSCoef d k j =
      ∑ j ∈ v.support ∪ Finset.range (k + 1), v j * frameGSCoef d k j :=
    Finset.sum_subset Finset.subset_union_left fun j _ hj => by
      rw [Finsupp.notMem_support_iff.1 hj, zero_mul]
  have h2 : ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * v j =
      ∑ j ∈ v.support ∪ Finset.range (k + 1), frameGSCoef d k j * v j :=
    Finset.sum_subset Finset.subset_union_right fun j _ hj => by
      have hkj : k < j := by
        have := Finset.mem_range.not.1 hj
        omega
      rw [frameGSCoef_eq_zero_of_lt hkj, zero_mul]
  rw [h1, h2]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- `∫ f_v dσ₁ = 0`. -/
theorem integral_frameFunRd_sphere (v : ℕ →₀ ℝ) :
    ∫ u, frameFunRd (frameE d) v u ∂(unitSphereProb d) = 0 := by
  simp only [frameFunRd_apply, Finsupp.sum]
  rw [integral_finsetSum _ fun j _ =>
    (integrable_unitSphereProb_of_continuous (frameE d j).continuous).const_mul (v j)]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, frameE, integral_framePot_sphere, mul_zero]

/-- `Φ(g + f_v) = Φ(g) + π(v)`. -/
theorem frameCoord_addFun_frameE (g : DistRd d) (v : ℕ →₀ ℝ) :
    frameCoord d (addFun g (frameFunRd (frameE d) v)) = frameCoord d g + frameProj d ⇑v := by
  funext i
  exact addFun_frameE_apply_frameGS g v i

end Frame

/-! ## The good set -/

/-- The good set `𝒢` of fields (NA4 A2 step 4; Part C `c:prop-frame` step 1). -/
def frameGood (d : ℕ) : Set (DistRd d) :=
  {g | g ∈ convSet d ∧ sphereAvg g 1 0 = 0 ∧
    ∀ k, g (frameChi d k) = ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * g (frameGS d j)}

theorem measurableSet_frameGood : MeasurableSet (frameGood d) := by
  have e : {g : DistRd d | ∀ k, g (frameChi d k) =
      ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * g (frameGS d j)} =
      ⋂ k, {g : DistRd d | g (frameChi d k) =
        ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * g (frameGS d j)} := by
    ext g
    simp only [mem_ofPred_eq, mem_iInter]
  show MeasurableSet ({g : DistRd d | g ∈ convSet d} ∩ ({g : DistRd d | sphereAvg g 1 0 = 0} ∩
    {g : DistRd d | ∀ k, g (frameChi d k) =
      ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * g (frameGS d j)}))
  refine measurableSet_convSet.inter ((measurableSet_eq_fun (measurable_sphereAvg_left 1 0)
    measurable_const).inter ?_)
  rw [e]
  exact MeasurableSet.iInter fun k => measurableSet_eq_fun (measurable_distOn_apply _)
    (Finset.measurable_sum _ fun j _ => (measurable_distOn_apply _).const_mul _)

/-- `𝒢` has full measure under the normalized LGF (Part C `c:prop-frame` step 1). -/
theorem ae_mem_frameGood [NeZero d] (hd : 2 ≤ d) : ∀ᵐ g ∂(normLGFLaw d), g ∈ frameGood d := by
  have hspec := normLGFLaw_spec d hd
  have hh := hspec.2.1
  have hconv : ∀ᵐ g ∂(normLGFLaw d), g ∈ convSet d :=
    sphereConvAS_of_sphereAvg_spec (sphereAvg_spec d hd) (normLGFLaw d) id hh.1
  have hrel : ∀ᵐ g ∂(normLGFLaw d), ∀ k, g (frameChi d k) =
      ∑ j ∈ Finset.range (k + 1), frameGSCoef d k j * g (frameGS d j) :=
    ae_all_iff.2 fun k => ae_frameGS_relation hh.1 k
  filter_upwards [hconv, hh.2, hrel] with g h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem normLGFLaw_frameGood [NeZero d] (hd : 2 ≤ d) : normLGFLaw d (frameGood d) = 1 := by
  have := (normLGFLaw_spec d hd).1
  rw [← prob_compl_eq_zero_iff measurableSet_frameGood]
  exact ae_iff.1 (ae_mem_frameGood hd)

/-- **Closure under frame shifts** (Part C `c:prop-frame` step 2). -/
theorem addFun_frameE_mem_frameGood [NeZero d] {g : DistRd d} (hg : g ∈ frameGood d)
    (v : ℕ →₀ ℝ) : addFun g (frameFunRd (frameE d) v) ∈ frameGood d := by
  obtain ⟨⟨a, ha⟩, hs, hr⟩ := hg
  refine ⟨(exists_tendsto_sphereAvgSeq_addFun_iff g _ 1 0).2 ⟨a, ha⟩, ?_, fun k => ?_⟩
  · rw [sphereAvg_addFun_of_tendsto ha, hs, zero_add]
    simp only [zero_add, one_smul]
    exact integral_frameFunRd_sphere v
  · rw [addFun_frameE_apply_frameChi, hr k, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [addFun_frameE_apply_frameGS, mul_add, ← mul_assoc, frameGSCoef_mul_frameC]

/-! ## Injectivity and the Lusin–Souslin inverse -/

/-- `Φ` is injective on `𝒢` (Part C `c:prop-frame` step 3). -/
theorem frameCoord_injOn (hd : 1 ≤ d) : InjOn (frameCoord d) (frameGood d) := by
  intro g hg g' hg' heq
  have hψ : ∀ j, g (frameGS d j) = g' (frameGS d j) := fun j => congrFun heq j
  have hχ : ∀ k, g (frameChi d k) = g' (frameChi d k) := fun k => by
    rw [hg.2.2 k, hg'.2.2 k]
    simp only [hψ]
  have e := eq_addConst_of_forall_chi hχ
  set c := g' (theta d) - g (theta d) with hcdef
  have hc : c = 0 := by
    have h1 := sphereAvg_addConst_of_mem_convSet hd hg.1 c
    rw [← e, hg'.2.1, hg.2.1, zero_add] at h1
    exact h1.symm
  rw [e, hc, addConst_zero]

/-- **The Lusin–Souslin inverse** (Part C `c:prop-frame` step 5): `Φ(𝒢)` is measurable and there is a measurable
`T₀` with `T₀(Φ(g)) = g` on `𝒢`. -/
theorem exists_frameInv (hd : 1 ≤ d) :
    MeasurableSet (frameCoord d '' frameGood d) ∧
      ∃ T₀ : (ℕ → ℝ) → DistRd d, Measurable T₀ ∧ ∀ g ∈ frameGood d, T₀ (frameCoord d g) = g := by
  have hG := measurableSet_frameGood (d := d)
  have : StandardBorelSpace (frameGood d) := hG.standardBorel
  let f : frameGood d → (ℕ → ℝ) := fun g => frameCoord d g.1
  have hfm : Measurable f := measurable_frameCoord.comp measurable_subtype_coe
  have hfi : Function.Injective f := fun a b hab => Subtype.ext (frameCoord_injOn hd a.2 b.2 hab)
  have hemb : MeasurableEmbedding f := hfm.measurableEmbedding hfi
  refine ⟨?_, ?_⟩
  · rw [image_eq_range]
    exact hemb.measurableSet_range
  · obtain ⟨T₀, hT₀m, hT₀⟩ :=
      hemb.exists_measurable_extend (g := Subtype.val) measurable_subtype_coe (fun _ => ⟨0⟩)
    exact ⟨T₀, hT₀m, fun g hg => congrFun hT₀ ⟨g, hg⟩⟩

end HigherDimLQGContinuity

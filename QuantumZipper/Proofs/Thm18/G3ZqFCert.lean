import QuantumZipper.Proofs.Thm18.RTMeas2Area
import QuantumZipper.Proofs.Thm18.G3Zc2Law2
import QuantumZipper.Proofs.Thm18.G3Zc2Univ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH-FIX (1): a measurable certificate for the local area limit of dyadic data

The existence of the local area measure on `halfDisc r` is not known to be a measurable property
of the dyadic data, so it cannot be transferred directly along an equality of dyadic laws. The
countable window certificate of RT-MEAS2 (`R18.RTMeas.WinCertC`: eventual finiteness on the
windows and convergence against the countable dense family, windows weighted by `wt n`) is a
measurable property of the data (`measurableSet_dyadCert`), implies the local area limit
(`exists_lim_of_winCertC`), and holds for the dyadic data of any field agreeing near `0` with a
D3⁺ model field over a regular sample which has a local area limit (`dyadCert_of_model`: the
approximations there have a continuous density on the windows, `exists_cutoff`).

Own elementary bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv
namespace G3ZqF

open D3Plus R18.RTMeas

/-- The window certificate of the reconstructed dyadic field on `halfDisc r`. -/
def dyadCert (γ r : ℝ) (ξ : DyIdxIn r → ℝ) : Prop :=
  WinCertC (areaApprox γ (dyadField r ξ)) (halfDisc r)

theorem measurableSet_dyadCert (γ r : ℝ) : MeasurableSet {ξ | dyadCert γ r ξ} := by
  have hx : Measurable (dyadField r) := measurable_dyadField r
  refine measurableSet_setOfPred.2 (Measurable.forall fun n =>
    (measurable_const : Measurable fun _ : DyIdxIn r → ℝ => WinOKC (halfDisc r) n).imp ?_)
  refine Measurable.and (Measurable.exists fun K => Measurable.forall fun k =>
      measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_lt
        ((Measure.measurable_coe measurableSet_closedBall).comp
          ((measurable_areaApprox γ k).comp hx)) measurable_const))) ?_
  have hset : {ξ : DyIdxIn r → ℝ | ∀ f ∈ GoodMeas.denseFam, ∃ l, Tendsto (fun k => ∫ z,
      f z * wt n z ∂areaApprox γ (dyadField r ξ) k) atTop (𝓝 l)} =
      ⋂ f ∈ GoodMeas.denseFam, {ξ | ∃ l, Tendsto (fun k => ∫ z, f z * wt n z
        ∂areaApprox γ (dyadField r ξ) k) atTop (𝓝 l)} := by
    ext ξ; simp
  refine measurableSet_setOfPred.1 ?_
  rw [hset]
  refine MeasurableSet.biInter GoodMeas.denseFam_countable fun f hf => ?_
  have hfc : Continuous f := (GoodMeas.denseFam_dense.1 f hf).1
  exact StronglyMeasurable.measurableSet_exists_tendsto fun k =>
    (Prop16Area.Meas.measurable_integral_areaApprox_param γ k hx
      (g := fun _ z => f z * wt n z)
      ((hfc.mul (continuous_wt n)).measurable.comp measurable_snd)).stronglyMeasurable

/-- The certificate gives the local area limit of any field with these dyadic data. -/
theorem exists_vague_of_dyadCert {γ r : ℝ} {y : FieldSample} (h : dyadCert γ r (dyadData r y)) :
    ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ y) m :=
  (exists_isVagueLimitOn_halfDisc_iff (agreeNear_dyadField r y)).2
    (exists_lim_of_winCertC (isOpen_halfDisc r) (halfDisc_subset_H r) h)

/-- Finiteness of an approximation whose regularized averages on `K` are those of a regular
sample. -/
theorem areaApprox_lt_top_of_avgReg_eq {γ : ℝ} {y x : FieldSample} (hx : IsRegularSample x)
    {K : Set ℂ} (hK : IsCompact K) {k : ℕ} (h : ∀ z ∈ K, avgReg y k z = avgReg x k z) :
    areaApprox γ y k K < ⊤ := by
  obtain ⟨F, hF⟩ := hx
  have e : areaApprox γ y k K = areaApprox γ x k K := by
    rw [areaApprox, areaApprox, withDensity_apply _ hK.isClosed.measurableSet,
      withDensity_apply _ hK.isClosed.measurableSet]
    exact setLIntegral_congr_fun hK.isClosed.measurableSet (fun z hz => by rw [h z hz])
  rw [e, ← GoodSample.areaR_radius γ hF k]
  exact GoodSample.areaR_lt_top γ hF (by simpa using radius_pos k) hK

/-- **The certificate for a field agreeing near `0` with a D3⁺ model over a regular sample.** -/
theorem dyadCert_of_model {γ α r L r'' : ℝ} {ρ₀ : Measure ℂ} {x' : FieldSample} {g : ℂ → ℝ}
    (hX : IsRegularSample x') (hg : ContinuousOn g (ball (0 : ℂ) r ∩ Hbar)) {Z : FieldSample}
    (hag : AgreeNear Z (zoomModel γ α L ρ₀ x' g) r) (hr'' : r'' ≤ r)
    (hgood : ∃ m, IsVagueLimitOn (halfDisc r'') (areaApprox γ Z) m) :
    dyadCert γ r'' (dyadData r'' Z) := by
  intro n hok
  set K := closedBall (cC n) (2 * rC n) with hKdef
  have hKU : K ⊆ halfDisc r'' := hok.2
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨m, hm⟩ := (exists_isVagueLimitOn_halfDisc_iff (agreeNear_dyadField r'' Z)).1 hgood
  constructor
  · -- finiteness
    set φ : ℂ → ℝ := fun z => α * -Real.log ‖z‖ + g z + (L / γ - x' ρ₀) with hφdef
    have hφ : ContinuousOn φ ((ball (0 : ℂ) r \ {0}) ∩ Hbar) :=
      continuousOn_zoomPot (γ := γ) (α := α) (L := L) (ρ₀ := ρ₀) (x := x') hg
    have hKW : K ⊆ ball (0 : ℂ) r \ {0} := fun z hz => by
      have h1 := hKU hz
      refine ⟨ball_subset_ball hr'' h1.1, fun h0 => ?_⟩
      have h2 : 0 < z.im := h1.2
      rw [mem_singleton_iff.1 h0] at h2
      simp at h2
    obtain ⟨δ, hδ, φ', hφ'c, hEq⟩ :=
      LocalRule.exists_cutoff (isOpen_ball.sdiff isClosed_singleton) hφ hKc hKW
    have hx₁ : IsRegularSample (x' + ofFun φ') := GoodSample.gs_add_ofFun_sample hX hφ'c
    obtain ⟨ρ₁, hρ₁, hKρ₁⟩ := exists_lt_subset_ball hKc.isClosed (hKU.trans inter_subset_left)
    obtain ⟨K₀, hK₀⟩ := AtomlessUncond.exists_radius_lt
      (show 0 < min (δ / 2) (r'' - ρ₁) from lt_min (by positivity) (by linarith))
    refine ⟨K₀, fun k hk => areaApprox_lt_top_of_avgReg_eq hx₁ hKc fun z hz => ?_⟩
    have hrk := hK₀ k hk
    have hrk1 : radius k < δ / 2 := lt_of_lt_of_le hrk (min_le_left _ _)
    have hrk2 : radius k < r'' - ρ₁ := lt_of_lt_of_le hrk (min_le_right _ _)
    have hzρ : ‖z‖ < ρ₁ := by simpa using hKρ₁ hz
    have hzb : ‖z‖ + radius k < r'' := by linarith
    have hzH : z ∈ Hbar := H_subset_Hbar (hKU hz).2
    rw [avgReg_congr (agreeNear_dyadField r'' Z).symm' hzb,
      avgReg_congr (AgreeNear.mono_radius hag hr'') hzb]
    refine LocalRule.avgReg_congr_local k (ρ := δ / 2) (by positivity) (fun c hc hcz => ?_) hzH
    show x' (foldedCircle c (radius k)) + ofFun φ (foldedCircle c (radius k)) =
      x' (foldedCircle c (radius k)) + ofFun φ' (foldedCircle c (radius k))
    rw [LocalRule.ofFun_fc_congr hc (radius_pos k) (φ := φ) (ψ := φ') fun u hu => ?_]
    refine (hEq ?_).symm
    refine mem_cthickening_of_dist_le u z δ K hz ?_
    have h1 : dist u c ≤ radius k := hu
    have h2 := dist_triangle u c z
    linarith
  · intro f hf
    have hft := GoodMeas.denseFam_dense.1 f hf
    refine ⟨_, hm.2.2 (fun z => f z * wt n z) (hft.1.mul (continuous_wt n)) ?_ ?_⟩
    · exact hft.2.1.mul_right
    · refine (tsupport_mul_subset_right).trans ?_
      refine (closure_minimal (fun z hz => ?_) isClosed_closedBall).trans hKU
      by_contra h
      exact hz (wt_eq_zero hok.1 h)

end G3ZqF
end G3Cv
end QuantumZipper

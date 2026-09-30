import QuantumZipper.Proofs.Zipper.UnifAWDet
import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowWin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7c (3): the moving test functions `f ∘ F_s⁻¹` are a continuous family

For a family `F s` of maps, jointly continuous in `(s, y)` and strictly increasing in `y` on a
window `[u,v]`, and `f` continuous with `tsupport f ⊆ [u', v'] ⊂ (u, v)`, the transported test
functions `awTest (F s) u v f` (`= f ∘ (F s)⁻¹` on `F s (u,v)`, `0` elsewhere) are jointly
continuous in `(s, x)` (`continuousOn_awTest`), and vanish off `[F s u', F s v']`.
Own elementary proof (local inverse by the intermediate value theorem).
-/

noncomputable section

open Filter Set Topology Metric

namespace QuantumZipper
namespace SWCore

open RegUnif

theorem awTest_apply_of {F : ℝ → ℝ} {u v : ℝ} (hinj : InjOn F (Icc u v)) (f : ℝ → ℝ)
    {x y : ℝ} (hy : y ∈ Ioo u v) (hFy : F y = x) : awTest F u v f x = f y := by
  have h : ∃ y ∈ Ioo u v, F y = x := ⟨y, hy, hFy⟩
  simp only [awTest, dif_pos h]
  obtain ⟨h1, h2⟩ := h.choose_spec
  rw [hinj (Ioo_subset_Icc_self h1) (Ioo_subset_Icc_self hy) (h2.trans hFy.symm)]

theorem awTest_eq_zero_of {F : ℝ → ℝ} {u v : ℝ} {f : ℝ → ℝ} {x : ℝ}
    (h0 : ∀ y ∈ Ioo u v, F y = x → f y = 0) : awTest F u v f x = 0 := by
  unfold awTest
  split_ifs with h
  · exact h0 _ h.choose_spec.1 h.choose_spec.2
  · rfl

/-- Vanishing off the image of the support interval. -/
theorem awTest_eq_zero_of_not_mem {F : ℝ → ℝ} {u v u' v' : ℝ}
    (hmono : StrictMonoOn F (Icc u v)) {f : ℝ → ℝ} (hfs : tsupport f ⊆ Icc u' v')
    (hu' : u ≤ u') (hv' : v' ≤ v) {x : ℝ} (hx : x < F u' ∨ F v' < x) :
    awTest F u v f x = 0 := by
  refine awTest_eq_zero_of fun y hy hFy => ?_
  by_contra hne
  have hys := hfs (subset_tsupport f (Function.mem_support.2 hne))
  have hyI := Ioo_subset_Icc_self hy
  rcases hx with hx | hx
  · have := hmono.monotoneOn ⟨hu', by linarith [hys.1, hys.2]⟩ hyI hys.1
    linarith
  · have := hmono.monotoneOn hyI ⟨by linarith [hys.1, hys.2], hv'⟩ hys.2
    linarith

theorem b7c_dist_fst (p q : ℝ × ℝ) : dist p.1 q.1 ≤ dist p q := by
  rw [Prod.dist_eq]; exact le_max_left _ _

theorem b7c_dist_snd (p q : ℝ × ℝ) : dist p.2 q.2 ≤ dist p q := by
  rw [Prod.dist_eq]; exact le_max_right _ _

/-- **Joint continuity of the transported test functions.** -/
theorem continuousOn_awTest {S : Set ℝ} {F : ℝ → ℝ → ℝ} {u v u' v' : ℝ} (huu' : u < u')
    (hu'v' : u' ≤ v') (hv'v : v' < v)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2) (S ×ˢ Icc u v))
    (hmono : ∀ s ∈ S, StrictMonoOn (F s) (Icc u v)) {f : ℝ → ℝ} (hf : Continuous f)
    (hfs : tsupport f ⊆ Icc u' v') :
    ContinuousOn (fun p : ℝ × ℝ => awTest (F p.1) u v f p.2) (S ×ˢ univ) := by
  rintro ⟨s₀, x₀⟩ ⟨hs₀, -⟩
  have hcF : ∀ y ∈ Icc u v, ContinuousWithinAt (fun s => F s y) S s₀ := fun y hy =>
    (hF (s₀, y) ⟨hs₀, hy⟩).comp (f := fun s : ℝ => (s, y))
      (continuous_id.prodMk continuous_const).continuousWithinAt (fun s hs => ⟨hs, hy⟩)
  have hu'I : u' ∈ Icc u v := ⟨huu'.le, by linarith⟩
  have hv'I : v' ∈ Icc u v := ⟨by linarith, hv'v.le⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- the cases
  rcases lt_or_ge x₀ (F s₀ u') with hx | hx
  · -- left of the support image: the function vanishes nearby
    have hc := hcF u' hu'I
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc ((F s₀ u' - x₀) / 2) (by linarith)
    refine ⟨min δ ((F s₀ u' - x₀) / 2), lt_min hδ (by linarith), fun p hp hpd => ?_⟩
    have hd1 : dist p.1 s₀ < δ := lt_of_le_of_lt (b7c_dist_fst p (s₀, x₀))
      (lt_of_lt_of_le hpd (min_le_left _ _))
    have hd2 : dist p.2 x₀ < (F s₀ u' - x₀) / 2 := lt_of_le_of_lt (b7c_dist_snd p (s₀, x₀))
      (lt_of_lt_of_le hpd (min_le_right _ _))
    have k := hδc hp.1 hd1
    rw [Real.dist_eq, abs_lt] at k hd2
    have z1 : awTest (F p.1) u v f p.2 = 0 :=
      awTest_eq_zero_of_not_mem (hmono p.1 hp.1) hfs huu'.le hv'v.le (Or.inl (by linarith))
    have z0 : awTest (F s₀) u v f x₀ = 0 :=
      awTest_eq_zero_of_not_mem (hmono s₀ hs₀) hfs huu'.le hv'v.le (Or.inl hx)
    simp only [z1, z0, dist_self, hε]
  rcases lt_or_ge (F s₀ v') x₀ with hx' | hx'
  · have hc := hcF v' hv'I
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hc ((x₀ - F s₀ v') / 2) (by linarith)
    refine ⟨min δ ((x₀ - F s₀ v') / 2), lt_min hδ (by linarith), fun p hp hpd => ?_⟩
    have hd1 : dist p.1 s₀ < δ := lt_of_le_of_lt (b7c_dist_fst p (s₀, x₀))
      (lt_of_lt_of_le hpd (min_le_left _ _))
    have hd2 : dist p.2 x₀ < (x₀ - F s₀ v') / 2 := lt_of_le_of_lt (b7c_dist_snd p (s₀, x₀))
      (lt_of_lt_of_le hpd (min_le_right _ _))
    have k := hδc hp.1 hd1
    rw [Real.dist_eq, abs_lt] at k hd2
    have z1 : awTest (F p.1) u v f p.2 = 0 :=
      awTest_eq_zero_of_not_mem (hmono p.1 hp.1) hfs huu'.le hv'v.le (Or.inr (by linarith))
    have z0 : awTest (F s₀) u v f x₀ = 0 :=
      awTest_eq_zero_of_not_mem (hmono s₀ hs₀) hfs huu'.le hv'v.le (Or.inr hx')
    simp only [z1, z0, dist_self, hε]
  -- inside: a local inverse
  have hcont0 : ContinuousOn (F s₀) (Icc u v) := fun y hy =>
    (hF (s₀, y) ⟨hs₀, hy⟩).comp (f := fun y : ℝ => (s₀, y))
      (continuous_const.prodMk continuous_id).continuousWithinAt (fun y hy => ⟨hs₀, hy⟩)
  obtain ⟨y₀, hy₀, hFy₀⟩ := intermediate_value_Icc hu'v' (hcont0.mono (Icc_subset_Icc huu'.le
    hv'v.le)) ⟨hx, hx'⟩
  have hy₀I : y₀ ∈ Ioo u v := ⟨by linarith [hy₀.1], by linarith [hy₀.2]⟩
  obtain ⟨δf, hδf, hδfc⟩ := Metric.continuous_iff.1 hf y₀ ε hε
  set e : ℝ := min (δf / 2) (min ((y₀ - u) / 2) ((v - y₀) / 2)) with he
  have he0 : 0 < e := lt_min (by linarith) (lt_min (by linarith [hy₀I.1]) (by linarith [hy₀I.2]))
  have he1 : e ≤ δf / 2 := min_le_left _ _
  have he2 : e ≤ (y₀ - u) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have he3 : e ≤ (v - y₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hel : y₀ - e ∈ Icc u v := ⟨by linarith, by linarith [hy₀I.2]⟩
  have her : y₀ + e ∈ Icc u v := ⟨by linarith [hy₀I.1], by linarith⟩
  have hy₀I' : y₀ ∈ Icc u v := Ioo_subset_Icc_self hy₀I
  have g1 : F s₀ (y₀ - e) < x₀ := hFy₀ ▸ hmono s₀ hs₀ hel hy₀I' (by linarith)
  have g2 : x₀ < F s₀ (y₀ + e) := hFy₀ ▸ hmono s₀ hs₀ hy₀I' her (by linarith)
  set c : ℝ := min (x₀ - F s₀ (y₀ - e)) (F s₀ (y₀ + e) - x₀) / 2 with hc
  have hc0 : 0 < c := by
    have : 0 < min (x₀ - F s₀ (y₀ - e)) (F s₀ (y₀ + e) - x₀) := lt_min (by linarith) (by linarith)
    positivity
  have hc1 : c ≤ (x₀ - F s₀ (y₀ - e)) / 2 := by
    rw [hc]; linarith [min_le_left (x₀ - F s₀ (y₀ - e)) (F s₀ (y₀ + e) - x₀)]
  have hc2 : c ≤ (F s₀ (y₀ + e) - x₀) / 2 := by
    rw [hc]; linarith [min_le_right (x₀ - F s₀ (y₀ - e)) (F s₀ (y₀ + e) - x₀)]
  obtain ⟨δ1, hδ1, hδ1c⟩ := Metric.continuousWithinAt_iff.1 (hcF _ hel) c hc0
  obtain ⟨δ2, hδ2, hδ2c⟩ := Metric.continuousWithinAt_iff.1 (hcF _ her) c hc0
  refine ⟨min (min δ1 δ2) c, lt_min (lt_min hδ1 hδ2) hc0, fun p hp hpd => ?_⟩
  have hd1 : dist p.1 s₀ < min δ1 δ2 := lt_of_le_of_lt (b7c_dist_fst p (s₀, x₀))
    (lt_of_lt_of_le hpd (min_le_left _ _))
  have hd2 : dist p.2 x₀ < c := lt_of_le_of_lt (b7c_dist_snd p (s₀, x₀))
    (lt_of_lt_of_le hpd (min_le_right _ _))
  have k1 := hδ1c hp.1 (lt_of_lt_of_le hd1 (min_le_left _ _))
  have k2 := hδ2c hp.1 (lt_of_lt_of_le hd1 (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at k1 k2 hd2
  have hcontp : ContinuousOn (F p.1) (Icc (y₀ - e) (y₀ + e)) := fun y hy =>
    ((hF (p.1, y) ⟨hp.1, Icc_subset_Icc hel.1 her.2 hy⟩).comp (f := fun y : ℝ => (p.1, y))
      (continuous_const.prodMk continuous_id).continuousWithinAt
      (fun y hy => ⟨hp.1, Icc_subset_Icc hel.1 her.2 hy⟩))
  obtain ⟨y, hy, hFy⟩ := intermediate_value_Icc (by linarith) hcontp
    (show p.2 ∈ Icc (F p.1 (y₀ - e)) (F p.1 (y₀ + e)) from ⟨by linarith, by linarith⟩)
  have hyI : y ∈ Ioo u v := ⟨by linarith [hy.1, hel.1, he0], by linarith [hy.2, her.2]⟩
  rw [awTest_apply_of (hmono p.1 hp.1).injOn f hyI hFy,
    awTest_apply_of (hmono s₀ hs₀).injOn f hy₀I hFy₀]
  refine hδfc y ?_
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-! ## Joint continuity of the carrier on a live window -/

section Carrier

open RevMapExtension

/-- Uniform Lipschitz bound of the real carrier on a live window (clearance `c`). -/
theorem realRevMap_lipschitz_window {V : ℝ → ℝ} (hV : Continuous V) {τ u v : ℝ}
    (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal τ < realHitTime V x) {c : ℝ} (hc : 0 < c)
    (hcl : ∀ x ∈ Icc u v, ∀ σ ∈ Icc (0 : ℝ) τ, c ≤ ‖realRevMap V σ x‖) {σ : ℝ}
    (hσ : σ ∈ Icc (0 : ℝ) τ) {x y : ℝ} (hx : x ∈ Icc u v) (hy : y ∈ Icc u v) :
    |realRevMap V σ y - realRevMap V σ x| ≤ |y - x| * Real.exp (2 / c ^ 2 * σ) := by
  obtain ⟨wx, hwx⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hLive x hx)
  obtain ⟨wy, hwy⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hLive y hy)
  have hx' := RealLine.isRealRevSol_restrict hwx hσ.2
  have hy' := RealLine.isRealRevSol_restrict hwy hσ.2
  have hb : ∀ (z : ℝ) (w : ℝ → ℝ), z ∈ Icc u v → IsRealRevSol V z τ w →
      ∀ r ∈ Icc (0 : ℝ) σ, c ≤ ‖((w r : ℝ) : ℂ)‖ := by
    intro z w hz hw r hr
    rw [Complex.norm_real, ← RealLine.realRevMap_eq hV hw hr.1 (hr.2.trans hσ.2)]
    exact hcl z hz r ⟨hr.1, hr.2.trans hσ.2⟩
  have k := norm_revMapExt_sub_le hσ.1 hc (isCRevSol_ofReal hx') (isCRevSol_ofReal hy')
    (hb x wx hx hwx) (hb y wy hy hwy)
  rw [revMapExt_ofReal hV hσ.1 hx', revMapExt_ofReal hV hσ.1 hy', ← Complex.ofReal_sub,
    ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs] at k
  exact k

/-- **Joint continuity of the real carrier** on `[0,τ] × [u,v]` for a live window. -/
theorem continuousOn_realRevMap_joint {V : ℝ → ℝ} (hV : Continuous V) {τ u v : ℝ}
    (hτ : 0 ≤ τ) (hLive : ∀ x ∈ Icc u v, ENNReal.ofReal τ < realHitTime V x) :
    ContinuousOn (fun p : ℝ × ℝ => realRevMap V p.1 p.2) (Icc (0 : ℝ) τ ×ˢ Icc u v) := by
  obtain ⟨c, hc, hcl⟩ := RegUnif.exists_unif_clearance hV hτ hLive
  set C : ℝ := Real.exp (2 / c ^ 2 * τ) with hC
  have hC0 : 0 < C := Real.exp_pos _
  rintro ⟨σ₀, x₀⟩ ⟨hσ₀, hx₀⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have htime : ContinuousOn (fun σ => realRevMap V σ x₀) (Icc (0 : ℝ) τ) := by
    obtain ⟨w, hw⟩ := RealLine.exists_isRealRevSol_of_lt_realHitTime (hLive x₀ hx₀)
    exact hw.1.congr fun t ht => RealLine.realRevMap_eq hV hw ht.1 ht.2
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 (htime σ₀ hσ₀) (ε / 2) (by linarith)
  refine ⟨min δ (ε / (2 * C)), lt_min hδ (by positivity), fun p hp hpd => ?_⟩
  have hd1 : dist p.1 σ₀ < δ := lt_of_le_of_lt (b7c_dist_fst p (σ₀, x₀))
    (lt_of_lt_of_le hpd (min_le_left _ _))
  have hd2 : dist p.2 x₀ < ε / (2 * C) := lt_of_le_of_lt (b7c_dist_snd p (σ₀, x₀))
    (lt_of_lt_of_le hpd (min_le_right _ _))
  have k1 := hδc hp.1 hd1
  have k2 := realRevMap_lipschitz_window hV hLive hc (fun x hx σ hσ => by
    simpa using hcl x hx σ hσ) hp.1 hx₀ hp.2
  have hle : Real.exp (2 / c ^ 2 * p.1) ≤ C :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hp.1.2 (by positivity))
  rw [Real.dist_eq] at hd2 k1 ⊢
  have k3 : |p.2 - x₀| * Real.exp (2 / c ^ 2 * p.1) ≤ ε / (2 * C) * C :=
    mul_le_mul hd2.le hle (Real.exp_pos _).le (by positivity)
  have e : ε / (2 * C) * C = ε / 2 := by field_simp
  calc |realRevMap V p.1 p.2 - realRevMap V σ₀ x₀|
      ≤ |realRevMap V p.1 p.2 - realRevMap V p.1 x₀| +
        |realRevMap V p.1 x₀ - realRevMap V σ₀ x₀| := abs_sub_le _ _ _
    _ < ε := by linarith

end Carrier

end SWCore
end QuantumZipper

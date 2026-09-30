import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcDefs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-EXCLOWER: transport of crosscuts and harmonic measures by the similarity `flSim σ m`

For `σ = ±1`, `m > 0`, the map `flSim σ m : z ↦ (σ Re z + i Im z)/m` is a homeomorphism of `ℂ`
onto itself mapping `ℍ` onto `ℍ` and bounded sets to bounded sets; a harmonic function composed
with its inverse (`w ↦ m w` or `w ↦ −m conj w`) is harmonic. Hence it carries a crosscut `η` to
the crosscut `flSim σ m ∘ η`, the unbounded component `H_η` onto `H_{flSim ∘ η}`, and the harmonic
measure `h` of `η` in `H_η` to the harmonic measure `h ∘ flSim σ m⁻¹` (conformal invariance of
harmonic measure; `flSim` is conformal or anticonformal). Also: reversing the parameter of a
crosscut swaps its endpoints and keeps its point set. Own elementary proofs of these standard
facts (cost rule of AGENT_GUIDE).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

lemma flSim_re_im (σ m : ℝ) (z : ℂ) : (flSim σ m z).re = σ * z.re / m ∧ (flSim σ m z).im = z.im / m :=
  ⟨rfl, rfl⟩

lemma flSim_eq (σ m : ℝ) (z : ℂ) :
    flSim σ m z = ((σ * z.re / m : ℝ) : ℂ) + ((z.im / m : ℝ) : ℂ) * I :=
  Complex.ext (by simp [flSim]) (by simp [flSim])

lemma flSim_real (σ m a : ℝ) : flSim σ m (a : ℂ) = ((σ * a / m : ℝ) : ℂ) :=
  Complex.ext (by simp [flSim]) (by simp [flSim])

lemma flSim_inv {σ m : ℝ} (hσ : σ * σ = 1) (hm : m ≠ 0) (z : ℂ) :
    flSim σ m⁻¹ (flSim σ m z) = z := by
  apply Complex.ext
  · simp only [flSim]
    field_simp
    rw [sq, hσ, one_mul]
  · simp only [flSim]; field_simp

lemma flSim_continuous (σ m : ℝ) : Continuous (flSim σ m) := by
  have : flSim σ m = fun z : ℂ => ((σ * z.re / m : ℝ) : ℂ) + ((z.im / m : ℝ) : ℂ) * I :=
    funext (flSim_eq σ m)
  rw [this]; fun_prop

/-- `flSim σ m` as a homeomorphism. -/
def flSimHomeo (σ m : ℝ) (hσ : σ * σ = 1) (hm : m ≠ 0) : ℂ ≃ₜ ℂ where
  toFun := flSim σ m
  invFun := flSim σ m⁻¹
  left_inv := flSim_inv hσ hm
  right_inv := fun w => by
    have := flSim_inv hσ (inv_ne_zero hm) w
    rwa [inv_inv] at this
  continuous_toFun := flSim_continuous σ m
  continuous_invFun := flSim_continuous σ m⁻¹

lemma flSim_norm_le {σ m : ℝ} (hσ : σ * σ = 1) (hm : 0 < m) (z : ℂ) :
    ‖flSim σ m z‖ ≤ 2 * ‖z‖ / m := by
  have hs : |σ| = 1 := by
    have : |σ| * |σ| = 1 := by rw [← abs_mul, hσ, abs_one]
    nlinarith [abs_nonneg σ]
  have h1 := Complex.norm_le_abs_re_add_abs_im (flSim σ m z)
  rw [(flSim_re_im σ m z).1, (flSim_re_im σ m z).2, abs_div, abs_div, abs_mul, hs,
    abs_of_pos hm] at h1
  have h2 := Complex.abs_re_le_norm z
  have h3 := Complex.abs_im_le_norm z
  calc ‖flSim σ m z‖ ≤ 1 * |z.re| / m + |z.im| / m := h1
    _ ≤ 2 * ‖z‖ / m := by
      rw [one_mul, ← add_div]; gcongr; linarith

lemma flSim_isBounded_iff {σ m : ℝ} (hσ : σ * σ = 1) (hm : 0 < m) (K : Set ℂ) :
    Bornology.IsBounded (flSim σ m '' K) ↔ Bornology.IsBounded K := by
  have key : ∀ (m' : ℝ), 0 < m' → ∀ K' : Set ℂ, Bornology.IsBounded K' →
      Bornology.IsBounded (flSim σ m' '' K') := by
    intro m' hm' K' hK
    obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hK
    refine isBounded_iff_forall_norm_le.2 ⟨2 * C / m', ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (flSim_norm_le hσ hm' z).trans (by gcongr; exact hC z hz)
  refine ⟨fun hB => ?_, key m hm K⟩
  have := key m⁻¹ (inv_pos.2 hm) _ hB
  rwa [← image_comp, show flSim σ m⁻¹ ∘ flSim σ m = id from funext (flSim_inv hσ hm.ne'),
    image_id] at this

lemma flSim_mem_H {σ m : ℝ} (hm : 0 < m) (z : ℂ) : flSim σ m z ∈ H ↔ z ∈ H := by
  show 0 < z.im / m ↔ 0 < z.im
  exact div_pos_iff_of_pos_right hm

/-- A harmonic function composed with a complex-analytic map is harmonic. -/
lemma fl_harmonicAt_comp {h : ℂ → ℝ} {ψ : ℂ → ℂ} {u : ℂ} (hψ : AnalyticAt ℂ ψ u)
    (hh : InnerProductSpace.HarmonicAt h (ψ u)) : InnerProductSpace.HarmonicAt (h ∘ ψ) u := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (InnerProductSpace.isOpen_setOfPred_harmonicAt (f := h)) _ hh
  obtain ⟨F, hF, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := h)
      (z := ψ u) (R := r) (fun y hy => hball hy)
  have hFψ : AnalyticAt ℂ (F ∘ ψ) u := (hF _ (mem_ball_self hr)).comp hψ
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hFψ.harmonicAt_re
  have hev : ∀ᶠ v in 𝓝 u, ψ v ∈ ball (ψ u) r :=
    hψ.continuousAt.preimage_mem_nhds (isOpen_ball.mem_nhds (mem_ball_self hr))
  filter_upwards [hev] with v hv
  exact hFeq hv

/-- A harmonic function composed with complex conjugation is harmonic. -/
lemma fl_harmonicAt_conj {g : ℂ → ℝ} {w : ℂ} (hg : InnerProductSpace.HarmonicAt g (conj w)) :
    InnerProductSpace.HarmonicAt (fun u => g (conj u)) w := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp
    (InnerProductSpace.isOpen_setOfPred_harmonicAt (f := g)) _ hg
  obtain ⟨F, hF, hFeq⟩ :=
    InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq (f := g)
      (z := conj w) (R := r) (fun y hy => hball hy)
  have hmem : ∀ u ∈ ball w r, conj u ∈ ball (conj w) r := fun u hu => by
    rw [mem_ball, dist_eq_norm, ← map_sub, Complex.norm_conj, ← dist_eq_norm]; exact hu
  have hG : DifferentiableOn ℂ (conj ∘ F ∘ conj) (ball w r) := by
    intro u hu
    have hd := ((hF _ (hmem u hu)).differentiableAt.hasDerivAt).conj_conj
    rw [Complex.conj_conj] at hd
    exact hd.differentiableAt.differentiableWithinAt
  have hGa : AnalyticAt ℂ (conj ∘ F ∘ conj) w :=
    hG.analyticAt (isOpen_ball.mem_nhds (mem_ball_self hr))
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).mp hGa.harmonicAt_re
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with u hu
  simp only [Function.comp_apply, Complex.conj_re]
  exact hFeq (hmem u hu)

lemma flSim_harmonicAt {σ m : ℝ} (hσ : σ = 1 ∨ σ = -1) (hm : 0 < m) {h : ℂ → ℝ} {w : ℂ}
    (hh : InnerProductSpace.HarmonicAt h (flSim σ m⁻¹ w)) :
    InnerProductSpace.HarmonicAt (fun u => h (flSim σ m⁻¹ u)) w := by
  rcases hσ with rfl | rfl
  · have e : ∀ u, flSim 1 m⁻¹ u = (m : ℂ) * u := fun u =>
      Complex.ext (by simp [flSim, mul_comm]) (by simp [flSim, mul_comm])
    simp only [e] at hh ⊢
    exact fl_harmonicAt_comp (ψ := fun u => (m : ℂ) * u) (by fun_prop) hh
  · have e : ∀ u, flSim (-1) m⁻¹ u = -(m : ℂ) * conj u := fun u =>
      Complex.ext (by simp [flSim, mul_comm]) (by simp [flSim, mul_comm])
    simp only [e] at hh ⊢
    have h1 : InnerProductSpace.HarmonicAt (h ∘ fun v => -(m : ℂ) * v) (conj w) :=
      fl_harmonicAt_comp (ψ := fun v => -(m : ℂ) * v) (by fun_prop) hh
    exact fl_harmonicAt_conj (g := h ∘ fun v => -(m : ℂ) * v) h1

section Transport

variable {σ m : ℝ} (hσ : σ = 1 ∨ σ = -1) (hm : 0 < m)

include hσ in
lemma fl_sigma_sq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num

include hσ in
lemma flSim_unbddPart (S : Set ℂ) :
    unbddPart (flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' S) =
      flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' unbddPart S := by
  set e := flSimHomeo σ m (fl_sigma_sq hσ) hm.ne'
  have hb : ∀ K : Set ℂ, Bornology.IsBounded (e '' K) ↔ Bornology.IsBounded K :=
    flSim_isBounded_iff (fl_sigma_sq hσ) hm
  ext w; constructor
  · rintro ⟨⟨z, hz, rfl⟩, hub⟩
    refine ⟨z, ⟨hz, fun hB => hub ?_⟩, rfl⟩
    rw [← e.image_connectedComponentIn hz]; exact (hb _).2 hB
  · rintro ⟨z, ⟨hz, hub⟩, rfl⟩
    refine ⟨mem_image_of_mem e hz, fun hB => hub ?_⟩
    rw [← e.image_connectedComponentIn hz] at hB; exact (hb _).1 hB

include hσ in
lemma flSim_image_H : flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' H = H := by
  set e := flSimHomeo σ m (fl_sigma_sq hσ) hm.ne'
  ext w; constructor
  · rintro ⟨z, hz, rfl⟩; exact (flSim_mem_H hm z).2 hz
  · intro hw
    refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
    rw [← flSim_mem_H hm]
    exact (e.apply_symm_apply w).symm ▸ hw

include hσ in
lemma flSim_arcH (η : ℝ → ℂ) :
    arcH (fun t => flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' (η t)) =
      flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' arcH η := by
  unfold arcH; rw [← image_comp]; rfl

include hσ in
lemma flSim_hullComp (η : ℝ → ℂ) :
    hullComp (fun t => flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' (η t)) =
      flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' hullComp η := by
  unfold hullComp
  rw [flSim_arcH hσ hm, ← flSim_image_H hσ hm, ← image_sdiff (Homeomorph.injective _),
    flSim_image_H hσ hm, flSim_unbddPart hσ hm]

include hσ in
lemma flSim_crosscut {η : ℝ → ℂ} (hη : IsCrosscutH η) :
    IsCrosscutH (fun t => flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' (η t)) := by
  set e := flSimHomeo σ m (fl_sigma_sq hσ) hm.ne'
  obtain ⟨hc, hi, hH, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hη
  refine ⟨e.continuous.comp_continuousOn hc, e.injective.comp_injOn hi,
    fun t ht => (flSim_mem_H hm _).2 (hH ht), ⟨σ * a / m, ?_⟩, ⟨σ * b / m, ?_⟩⟩
  · have := (e.continuous.tendsto _).comp ha
    rwa [show e (a : ℂ) = ((σ * a / m : ℝ) : ℂ) from flSim_real σ m a] at this
  · have := (e.continuous.tendsto _).comp hb
    rwa [show e (b : ℂ) = ((σ * b / m : ℝ) : ℂ) from flSim_real σ m b] at this

lemma fl_tendsto_symm (e : ℂ ≃ₜ ℂ) {U : Set ℂ} {z : ℂ} {g : ℂ → ℝ} {l : Filter ℝ}
    (ht : Tendsto g (𝓝[U] z) l) : Tendsto (fun w => g (e.symm w)) (𝓝[e '' U] (e z)) l := by
  refine ht.comp ?_
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have := e.symm.continuous.tendsto (e z)
    rw [e.symm_apply_apply] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    rw [e.image_eq_preimage_symm] at hw
    exact hw

include hσ in
/-- **Transport of harmonic measure** by `flSim σ m`. -/
theorem flSim_isHarmMeas {U A : Set ℂ} {h : ℂ → ℝ} (hh : IsHarmMeas U A h) :
    IsHarmMeas (flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' U)
      (flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' '' A) (fun w => h (flSim σ m⁻¹ w)) := by
  set e := flSimHomeo σ m (fl_sigma_sq hσ) hm.ne' with he
  have hsymm : ∀ w, flSim σ m⁻¹ w = e.symm w := fun w => rfl
  have hb : ∀ K : Set ℂ, Bornology.IsBounded (e '' K) ↔ Bornology.IsBounded K :=
    flSim_isBounded_iff (fl_sigma_sq hσ) hm
  simp only [hsymm]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have h1 : InnerProductSpace.HarmonicAt h (flSim σ m⁻¹ (e z)) := by
      rw [hsymm, e.symm_apply_apply]; exact hh.harm z hz
    have := flSim_harmonicAt hσ hm h1
    simpa only [hsymm] using this
  · rintro _ ⟨z, hz, rfl⟩
    rw [e.symm_apply_apply]; exact hh.mem01 z hz
  · rintro _ ⟨z, hz, rfl⟩ hcl
    refine fl_tendsto_symm e (hh.one z hz fun hc => hcl ?_)
    rw [← e.image_frontier, ← image_sdiff e.injective, ← e.image_closure]
    exact mem_image_of_mem e hc
  · intro x₀ hx₀ hcl
    rw [← e.image_frontier] at hx₀
    obtain ⟨z, hz, rfl⟩ := hx₀
    refine fl_tendsto_symm e (hh.zero z hz fun hc => hcl ?_)
    rw [← e.image_closure]; exact mem_image_of_mem e hc
  · intro hA
    refine (hh.infty ((hb A).1 hA)).comp ?_
    refine tendsto_inf.2 ⟨?_, ?_⟩
    · refine (tendsto_inf_left ?_)
      have hcb : Bornology.cobounded ℂ = comap norm atTop := (comap_norm_atTop (E := ℂ)).symm
      rw [hcb, tendsto_comap_iff]
      have hle : ∀ w : ℂ, m / 2 * ‖w‖ ≤ ‖e.symm w‖ := fun w => by
        have := flSim_norm_le (fl_sigma_sq hσ) hm (e.symm w)
        have h2 : flSim σ m (e.symm w) = w := e.apply_symm_apply w
        rw [h2] at this
        rw [le_div_iff₀ hm] at this
        linarith
      refine tendsto_atTop_mono hle ?_
      exact (tendsto_comap.const_mul_atTop (by positivity : (0 : ℝ) < m / 2))
    · refine tendsto_inf_right (tendsto_principal_principal.2 fun w hw => ?_)
      rw [e.image_eq_preimage_symm] at hw; exact hw

end Transport

lemma fl_rev_tendsto0 : Tendsto (fun t : ℝ => 1 - t) (𝓝[>] 0) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 0) (𝓝 (1 - 0)) := (continuous_const.sub continuous_id).tendsto 0
    rw [sub_zero] at this; exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    show 1 - t < 1; linarith

lemma fl_rev_tendsto1 : Tendsto (fun t : ℝ => 1 - t) (𝓝[<] 1) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => 1 - t) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
    rw [sub_self] at this; exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t (ht : t < 1)
    show 0 < 1 - t; linarith

lemma fl_rev_mapsTo : MapsTo (fun t : ℝ => 1 - t) (Ioo 0 1) (Ioo 0 1) := fun t ht =>
  ⟨by linarith [ht.2], by linarith [ht.1]⟩

lemma fl_rev_arcH (η : ℝ → ℂ) : arcH (fun t => η (1 - t)) = arcH η := by
  unfold arcH
  ext w; constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, fl_rev_mapsTo ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨1 - t, fl_rev_mapsTo ht, by simp⟩

lemma fl_rev_crosscut {η : ℝ → ℂ} (hη : IsCrosscutH η) : IsCrosscutH (fun t => η (1 - t)) := by
  obtain ⟨hc, hi, hH, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hη
  refine ⟨hc.comp (by fun_prop) fl_rev_mapsTo, ?_, fun t ht => hH (fl_rev_mapsTo ht),
    ⟨b, hb.comp fl_rev_tendsto0⟩, ⟨a, ha.comp fl_rev_tendsto1⟩⟩
  intro s hs t ht hst
  have := hi (fl_rev_mapsTo hs) (fl_rev_mapsTo ht) hst
  linarith

end FieldLawler
end QuantumZipper

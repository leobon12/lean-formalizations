/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10FullFactor
import InteractingSLE.Spec.Supplement.GB6LawTrace

/-!
# Aux. lemma 10: the factor data of a protected conformal map

Packet PROVE-T14-BR9. Specification Aux. lemma 10, proof (pp. 69–71). Let `K = K_T` be a Loewner hull, `D ⊆ ℍ` open
and `φ : D → ℍ` conformal. Fix a real point `x ≠ 0` away from `K` and from `ℍ \ D`, and suppose `ℍ \ D` keeps a
positive distance from `K ∪ {0}`. With `m(z) = −1/(z − x)` (`mobAt x`) and `A = m(ℍ \ D)`,
`φ = M ∘ g_A ∘ m` on `D` (`exists_factorization`), and (`exists_factor_data`):

* `closure A` misses `m(0) = 1/x` and `closure m(K)` (a uniform lower bound for `|m(z) − m(w)|`);
* `M` moves `∞` (`c ≠ 0`), because `φ` stays bounded near `x` while `g_A(m(z)) → ∞` there;
* the boundary value `x₁` of `g_A` at `1/x` is the zero of `M`, because `φ → 0` at `0`;
* the pole of `M` keeps a distance `r₃ > 0` from `g_A(m(K))`, because `φ` is bounded on `K`.

This is GB6's `exists_relMap_factor` (`Spec/Supplement/GB6LawChain`) for an arbitrary protected conformal map.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Aux10

open ConformalImage ConformalImageFull Sec5.CrossRestart

/-- Uniformly separated sets have disjoint closures. -/
theorem disjoint_closure_of_le_norm_sub {S T : Set ℂ} {η : ℝ} (hη : 0 < η)
    (h : ∀ a ∈ S, ∀ b ∈ T, η ≤ ‖a - b‖) : Disjoint (closure S) (closure T) := by
  have h1 : ∀ b ∈ T, closure S ⊆ {v : ℂ | η ≤ ‖v - b‖} := fun b hb =>
    closure_minimal (fun a ha => h a ha b hb) (isClosed_le continuous_const (by fun_prop))
  have h2 : ∀ v ∈ closure S, closure T ⊆ {u : ℂ | η ≤ ‖v - u‖} := fun v hv =>
    closure_minimal (fun b hb => h1 b hb hv) (isClosed_le continuous_const (by fun_prop))
  rw [Set.disjoint_left]
  intro v hv hvT
  have := h2 v hv hvT
  simp only [sub_self, norm_zero, mem_ofPred_eq] at this
  linarith

theorem mobAt_sub_mobAt {x : ℝ} {z w : ℂ} (hz : z - x ≠ 0) (hw : w - x ≠ 0) :
    mobAt x z - mobAt x w = (z - w) / ((z - x) * (w - x)) := by
  rw [mobAt_apply, mobAt_apply]
  field_simp
  ring

theorem mobAt_zero (x : ℝ) : mobAt x 0 = ((1 / x : ℝ) : ℂ) := by
  rw [mobAt_apply]
  push_cast
  rw [zero_sub, inv_neg, neg_neg, one_div]

theorem sub_ne_zero_of_mem_H {z : ℂ} (hz : z ∈ H) (x : ℝ) : z - x ≠ 0 := fun h => by
  have : z = (x : ℂ) := sub_eq_zero.1 h
  rw [this] at hz
  simp [QuantumZipper.H] at hz

/-- `m(z) = −1/(z − x)` maps `ℍ` into `ℍ`. -/
theorem mobAt_mem_H (x : ℝ) {z : ℂ} (hz : z ∈ H) : mobAt x z ∈ H :=
  QuantumZipper.CA.realMobius_mem_H (mobAt_det x) hz

/-- `m` tends to `∞` at its pole, from `ℍ`. -/
theorem tendsto_mobAt_cobounded (x : ℝ) :
    Tendsto (mobAt x) (𝓝[H] (x : ℂ)) (Bornology.cobounded ℂ) := by
  have hsub : 𝓝[H] (x : ℂ) ≤ 𝓝[≠] (x : ℂ) := nhdsWithin_mono _ fun w hw h => by
    rw [Set.mem_singleton_iff] at h
    subst h
    simp [QuantumZipper.H] at hw
  have h1 : Tendsto (fun z : ℂ => z - x) (𝓝[≠] (x : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun z : ℂ => z - x) (𝓝 (x : ℂ)) (𝓝 0) := by
        simpa using (continuous_sub_right (x : ℂ)).tendsto (x : ℂ)
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact sub_ne_zero.2 hz
  have h2 := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp (h1.mono_left hsub)
  rw [← tendsto_norm_atTop_iff_cobounded] at h2 ⊢
  refine h2.congr fun z => ?_
  simp [Function.comp, mobAt_apply]

/-- The uncentred Loewner map `g_t = f_t + W_t` maps out `K_t`, for any starting point `W 0` (translate by `W 0`). -/
theorem gmap_isMapOut_gen {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t) :
    IsMapOut (QuantumZipper.fwdHull W t) (gmap W t) := by
  set c := W 0 with hc
  set V : ℝ → ℝ := fun s => W s - c with hV
  have hVc : Continuous V := hW.sub continuous_const
  have hV0 : V 0 = 0 := by simp [hV, hc]
  have hfun : (fun s => V s + c) = W := funext fun s => by simp [hV]
  have hm := (gmap_isMapOut hVc hV0 ht).comp_affHomeo (r := 1) (x := c) one_pos
  have hK : affHomeo 1 one_pos c '' QuantumZipper.fwdHull V t = QuantumZipper.fwdHull W t := by
    rw [← hfun, fwdHull_add_const V c t]
    exact image_congr fun z _ => affHomeo_one_apply c z
  have hg : (fun w => affHomeo 1 one_pos c (gmap V t ((affHomeo 1 one_pos c).symm w))) = gmap W t := by
    funext w
    rw [affHomeo_one_apply, affHomeo_one_symm_apply]
    simp only [gmap]
    rw [← hfun, fwdMap_add_const V c t w]
    simp only [hV]
    push_cast
    ring
  rwa [hK, hg] at hm

/-- `m` is continuous at the real point `0 ≠ x` and maps `ℍ` into `ℍ`. -/
theorem tendsto_mobAt_zero {x : ℝ} (hx0 : x ≠ 0) :
    Tendsto (mobAt x) (𝓝[H] (0 : ℂ)) (𝓝[H] ((1 / x : ℝ) : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have hc : ContinuousAt (mobAt x) 0 := continuousAt_realMobius (by simp [hx0])
    have := hc.tendsto
    rw [mobAt_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact mobAt_mem_H x hw

/-- **The factor data of a protected conformal map** (GB6's `exists_relMap_factor` for an arbitrary `φ`). -/
theorem exists_factor_data {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    {D : Set ℂ} {φ : ℂ → ℂ} (hDo : IsOpen D) (hDH : D ⊆ H) (hφd : DifferentiableOn ℂ φ D)
    (hφinj : InjOn φ D) (hφim : φ '' D = H) {x : ℝ} (hx0 : x ≠ 0) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) (hsep : ∀ z ∈ H \ D, δ ≤ ‖z - (x : ℂ)‖)
    (hsepK : ∀ z ∈ H \ D, ∀ w ∈ insert (0 : ℂ) (QuantumZipper.fwdHull W T), ε ≤ ‖z - w‖)
    (hφx : ∃ C : ℝ, ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ D ∧ ‖φ z‖ ≤ C)
    (hφ0 : ∀ᶠ z in 𝓝[H] (0 : ℂ), z ∈ D) (hφ0' : Tendsto φ (𝓝[H] (0 : ℂ)) (𝓝 0))
    (hφK : ∃ C : ℝ, ∀ w ∈ QuantumZipper.fwdHull W T, ‖φ w‖ ≤ C) :
    ∃ (g : ℂ → ℂ) (a' b' c' d' x₁ r₃ : ℝ),
      IsHPHull (mobAt x '' (H \ D)) ∧ IsMapOut (mobAt x '' (H \ D)) g ∧
      Disjoint (closure (mobAt x '' (H \ D)))
        (insert ((1 / x : ℝ) : ℂ) (closure (mobAt x '' QuantumZipper.fwdHull W T))) ∧
      Tendsto g (𝓝[H] ((1 / x : ℝ) : ℂ)) (𝓝 (x₁ : ℂ)) ∧
      0 < a' * d' - b' * c' ∧ c' ≠ 0 ∧ c' * x₁ + d' ≠ 0 ∧ a' * x₁ + b' = 0 ∧ 0 < r₃ ∧
      (∀ w ∈ QuantumZipper.fwdHull W T, r₃ ≤ ‖g (mobAt x w) - mobPole c' d'‖) ∧
      ∀ z ∈ D, mobAt x z ∈ H \ mobAt x '' (H \ D) ∧ φ z = realMobius a' b' c' d' (g (mobAt x z)) := by
  set K := QuantumZipper.fwdHull W T with hKdef
  set m := mobAt x with hm
  set A := m '' (H \ D) with hAdef
  obtain ⟨hA, hcompl, g, a', b', c', d', hg, hdet', hfac⟩ :=
    exists_factorization hDo hDH hφd hφinj hφim hδ hsep
  have hK : IsHPHull K := isHPHull_fwdHull hW hT
  have hKH : ∀ w ∈ K, w ∈ H := fun w hw => hK.1 hw
  have hmD : ∀ z ∈ D, m z ∈ H \ A := fun z hz => by rw [hcompl]; exact ⟨z, hz, rfl⟩
  have hKD : ∀ w ∈ K, w ∈ D := fun w hw => by
    by_contra hwD
    have := hsepK w ⟨hKH w hw, hwD⟩ w (mem_insert_of_mem _ hw)
    simp at this
    linarith
  -- a uniform separation of `A` from `m(K ∪ {0})`
  obtain ⟨M, hM⟩ := hK.2.1.exists_norm_le
  set CK : ℝ := |M| + |x| + 1 with hCK
  have hCKpos : 0 < CK := by positivity
  have hwx : ∀ w ∈ insert (0 : ℂ) K, w - x ≠ 0 ∧ ‖w - x‖ ≤ CK := by
    intro w hw
    rcases hw with rfl | hw
    · refine ⟨by simp [hx0], ?_⟩
      rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_eq_abs, hCK]
      linarith [abs_nonneg M]
    · refine ⟨sub_ne_zero_of_mem_H (hKH w hw) x, ?_⟩
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, hCK]
      linarith [hM w hw, le_abs_self M]
  set η : ℝ := ε / ((ε + CK) * CK) with hη
  have hηpos : 0 < η := by positivity
  have hsepA : ∀ a ∈ A, ∀ b ∈ m '' insert (0 : ℂ) K, η ≤ ‖a - b‖ := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
    obtain ⟨hw0, hwC⟩ := hwx w hw
    have hz0 : z - x ≠ 0 := sub_ne_zero_of_mem_H hz.1 x
    rw [hm, mobAt_sub_mobAt hz0 hw0, norm_div, norm_mul]
    have hzw := hsepK z hz w hw
    have hzx : ‖z - x‖ ≤ ‖z - w‖ + CK := by
      calc ‖z - x‖ = ‖(z - w) + (w - x)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - x‖ := norm_add_le _ _
        _ ≤ ‖z - w‖ + CK := by linarith
    have hzx0 : 0 < ‖z - x‖ := norm_pos_iff.2 hz0
    have hwx0 : 0 < ‖w - x‖ := norm_pos_iff.2 hw0
    have h1 : ‖z - x‖ * ‖w - x‖ ≤ (‖z - w‖ + CK) * CK :=
      mul_le_mul hzx hwC hwx0.le (by positivity)
    calc η = ε / ((ε + CK) * CK) := rfl
      _ ≤ ‖z - w‖ / ((‖z - w‖ + CK) * CK) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hzw (mul_pos hCKpos hCKpos).le]
      _ ≤ ‖z - w‖ / (‖z - x‖ * ‖w - x‖) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h1
  have hdA : Disjoint (closure A) (insert ((1 / x : ℝ) : ℂ) (closure (m '' K))) := by
    refine (disjoint_closure_of_le_norm_sub hηpos hsepA).mono_right ?_
    rintro v (rfl | hv)
    · exact subset_closure ⟨0, mem_insert _ _, by rw [hm, mobAt_zero]⟩
    · exact closure_mono (image_mono (subset_insert _ _)) hv
  -- the boundary value `x₁` of `g` at `1/x`
  have hball0 : Disjoint (ball ((1 / x : ℝ) : ℂ) η) A := by
    rw [Set.disjoint_left]
    intro v hv hvA
    have := hsepA v hvA (m 0) ⟨0, mem_insert _ _, rfl⟩
    rw [hm, mobAt_zero, ← dist_eq_norm] at this
    rw [mem_ball] at hv
    linarith
  obtain ⟨hLre, hg0'⟩ := hg.tendsto_limUnder_of_disjoint hA hηpos hball0
  set x₁ := (limUnder (𝓝[H] (((1 / x : ℝ)) : ℂ)) g).re with hx₁def
  have hx₁C : (x₁ : ℂ) = limUnder (𝓝[H] (((1 / x : ℝ)) : ℂ)) g :=
    Complex.ext (by simp [hx₁def]) (by rw [ofReal_im]; exact hLre.symm)
  have hg0 : Tendsto g (𝓝[H] ((1 / x : ℝ) : ℂ)) (𝓝 (x₁ : ℂ)) := by rw [hx₁C]; exact hg0'
  -- `M` moves `∞`
  set M₂ := realMobius a' b' c' d' with hM₂def
  have hc' : c' ≠ 0 := by
    intro hc0
    have hd0 : d' ≠ 0 := by rintro rfl; simp [hc0] at hdet'
    have ha0 : a' ≠ 0 := by rintro rfl; simp [hc0] at hdet'
    obtain ⟨C, hC⟩ := hφx
    set R : ℝ := (|C| * |d'| + |b'|) / |a'| + 2 with hR
    have hcob : Tendsto m (𝓝[H] (x : ℂ)) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ A)) := by
      refine tendsto_inf.2 ⟨tendsto_mobAt_cobounded x, tendsto_principal.2 ?_⟩
      filter_upwards [hC] with z hz
      exact hmD z hz.1
    have hev1 : ∀ᶠ z in 𝓝[H] (x : ℂ), ‖g (m z) - m z‖ < 1 :=
      hcob.eventually (hg.2.eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)) |>.mono fun z hz => by
        simpa [dist_eq_norm] using hz
    have hev2 : ∀ᶠ z in 𝓝[H] (x : ℂ), R ≤ ‖m z‖ :=
      (tendsto_norm_atTop_iff_cobounded.2 (tendsto_mobAt_cobounded x)).eventually (eventually_ge_atTop R)
    have := MobHyp.nhdsWithin_neBot x
    obtain ⟨z, ⟨hzD, hzC⟩, h1, h2⟩ := (hC.and (hev1.and hev2)).exists
    have hφz := hfac z hzD
    have hM : M₂ (g (m z)) = ((a' : ℂ) * g (m z) + b') / d' := by
      simp only [hM₂def, realMobius, hc0, ofReal_zero, zero_mul, zero_add]
    have hgz : R - 1 ≤ ‖g (m z)‖ := by
      have := norm_sub_norm_le (m z) (g (m z))
      rw [norm_sub_rev] at this
      linarith
    have hlow : |a'| * (R - 1) - |b'| ≤ ‖(a' : ℂ) * g (m z) + b'‖ := by
      have h3 := norm_sub_norm_le ((a' : ℂ) * g (m z)) (-(b' : ℂ))
      rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs] at h3
      nlinarith [abs_nonneg a', abs_pos.2 ha0]
    have hR1 : |C| * |d'| + |b'| < |a'| * (R - 1) - |b'| + |b'| := by
      have : (|C| * |d'| + |b'|) / |a'| < R - 1 := by rw [hR]; linarith
      rw [div_lt_iff₀ (abs_pos.2 ha0)] at this
      linarith
    rw [hφz, hM, norm_div, Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (abs_pos.2 hd0)] at hzC
    have : |C| * |d'| ≥ C * |d'| := mul_le_mul_of_nonneg_right (le_abs_self C) (abs_nonneg _)
    linarith
  -- `x₁` is the zero of `M`
  have hmt := tendsto_mobAt_zero hx0
  have hgM : Tendsto (fun w => g (m w)) (𝓝[H] (0 : ℂ)) (𝓝 (x₁ : ℂ)) := hg0.comp hmt
  have hevfac : ∀ᶠ w in 𝓝[H] (0 : ℂ), φ w = M₂ (g (m w)) := by
    filter_upwards [hφ0] with w hw
    exact hfac w hw
  have hM₂lim : Tendsto (fun w => M₂ (g (m w))) (𝓝[H] (0 : ℂ)) (𝓝 0) := hφ0'.congr' hevfac
  have hgMH : ∀ᶠ w in 𝓝[H] (0 : ℂ), g (m w) ∈ H := by
    filter_upwards [hφ0] with w hw
    exact hg.1.2.mapsTo (hmD w hw)
  set κ₂ := (a' * d' - b' * c') / c' ^ 2 with hκ₂
  have hκ₂pos : 0 < κ₂ := div_pos hdet' (by positivity)
  have hNe : (𝓝[H] (0 : ℂ)).NeBot := by simpa using MobHyp.nhdsWithin_neBot 0
  have hx₁ : (c' : ℂ) * x₁ + d' ≠ 0 := by
    intro hpole
    have hP : c' * x₁ + d' = 0 := by exact_mod_cast hpole
    have hev1 : ∀ᶠ w in 𝓝[H] (0 : ℂ), ‖M₂ (g (m w))‖ < 1 :=
      hM₂lim.norm.eventually (gt_mem_nhds (by simp))
    have hev2 : ∀ᶠ w in 𝓝[H] (0 : ℂ), ‖g (m w) - x₁‖ < κ₂ / (|a' / c'| + 2) := by
      have := (hgM.sub_const (x₁ : ℂ)).norm
      rw [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds (by positivity))
    obtain ⟨w, h1, h2, h3⟩ := (hev1.and (hev2.and hgMH)).exists
    have hv0 : g (m w) - x₁ ≠ 0 := sub_ne_zero_of_mem_H h3 x₁
    have hnf : M₂ (g (m w)) = nf (a' / c') κ₂ x₁ (g (m w)) := realMobius_eq_nf_of_pole hc' hP hv0
    have hn : κ₂ / ‖g (m w) - x₁‖ - |a' / c'| ≤ ‖M₂ (g (m w))‖ := by
      rw [hnf, nf]
      have := norm_sub_norm_le ((κ₂ : ℂ) / (g (m w) - x₁)) ((a' / c' : ℝ) : ℂ)
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ₂pos, Complex.norm_real,
        Real.norm_eq_abs] at this
      exact this.trans (norm_sub_rev _ _).le
    have hlt : |a' / c'| + 2 < κ₂ / ‖g (m w) - x₁‖ := by
      rw [lt_div_iff₀ (norm_pos_iff.2 hv0)]
      have := (lt_div_iff₀ (by positivity : (0 : ℝ) < |a' / c'| + 2)).1 h2
      linarith
    linarith
  have hM₂x₁ : M₂ (x₁ : ℂ) = 0 :=
    tendsto_nhds_unique ((continuousAt_realMobius (a' := a') (b' := b') hx₁).tendsto.comp hgM) hM₂lim
  have hnum : a' * x₁ + b' = 0 := by
    have h : ((a' : ℂ) * x₁ + b') / ((c' : ℂ) * x₁ + d') = 0 := hM₂x₁
    rw [div_eq_zero_iff] at h
    rcases h with h | h
    · exact_mod_cast h
    · exact absurd h hx₁
  -- the pole of `M` keeps a distance from `g(m(K))`
  obtain ⟨Cφ, hCφ⟩ := hφK
  set P₂ := mobPole c' d' with hP₂
  set r₃ := κ₂ / (|a' / c'| + |Cφ| + 1) with hr₃
  have hr₃pos : 0 < r₃ := by positivity
  have hclear : ∀ w ∈ K, r₃ ≤ ‖g (m w) - P₂‖ := by
    intro w hw
    have hvH : g (m w) ∈ H := hg.1.2.mapsTo (hmD w (hKD w hw))
    have hv0 : g (m w) - P₂ ≠ 0 := sub_ne_zero_of_mem_H hvH P₂
    have hnf : M₂ (g (m w)) = nf (a' / c') κ₂ P₂ (g (m w)) := realMobius_eq_nf hc' hv0
    have hΨ := hfac w (hKD w hw)
    have hb := hCφ w hw
    have hn : κ₂ / ‖g (m w) - P₂‖ ≤ |a' / c'| + |Cφ| + 1 := by
      have h1 : ‖((κ₂ : ℝ) : ℂ) / (g (m w) - P₂)‖ ≤ ‖((a' / c' : ℝ) : ℂ)‖ + ‖M₂ (g (m w))‖ := by
        rw [hnf, nf]
        calc ‖((κ₂ : ℝ) : ℂ) / (g (m w) - P₂)‖
            = ‖((a' / c' : ℝ) : ℂ) - (((a' / c' : ℝ) : ℂ) - ((κ₂ : ℝ) : ℂ) / (g (m w) - P₂))‖ := by
              ring_nf
          _ ≤ _ := norm_sub_le _ _
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ₂pos, Complex.norm_real,
        Real.norm_eq_abs, ← hΨ] at h1
      linarith [le_abs_self Cφ]
    rw [hr₃, div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (norm_pos_iff.2 hv0)] at hn
    linarith [mul_comm (|a' / c'| + |Cφ| + 1) ‖g (m w) - P₂‖]
  have hx₁' : c' * x₁ + d' ≠ 0 := by exact_mod_cast hx₁
  exact ⟨g, a', b', c', d', x₁, r₃, hA, hg, hdA, hg0, hdet', hc', hx₁', hnum, hr₃pos, hclear,
    fun z hz => ⟨hmD z hz, hfac z hz⟩⟩

end Aux10

end InteractingSLE

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImageBound

/-!
# Enclosure-uniform bounds for the seeded noise

Packet PROVE-ZHAN-GT4-A22. The source gap is protected by a real point
between the sources. All constants precede the paths and both times.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (fwdMap fwdHull)

/-- The actual other-source coordinate stays uniformly away from the whole
own seed interval. -/
theorem exists_original_source_gap_right {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hp : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) (Tm : ℝ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (W Vlo Vhi : ℝ → ℝ) (T : ℝ),
      Continuous W → W 0 = 0 → 0 < T → T ≤ Tm → fwdHull W T ⊆ H₁ →
      IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ uIcc (Vlo t) (Vhi t),
        c₀ ≤ |(fwdMap W t p).re + W t - x| := by
  have hpH₁ : Disjoint (ball (p : ℂ) δ) H₁ := by
    refine Set.disjoint_left.2 fun z hz hzH => ?_
    have hcl : closure H₂ ⊆ {w : ℂ | 2 * δ ≤ ‖w - z‖} :=
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).closure_subset_iff.2
        (fun w hw => hsep w hw z hzH)
    have hh : 2 * δ ≤ ‖(p : ℂ) - z‖ := hcl hp
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
    linarith
  obtain ⟨μ, c₀, -, hc₀, hpair⟩ := exists_protected_pair_gap hH₁
    (by positivity : 0 < 2 * d) hδ (hqH.mono_right subset_union_left) hpH₁ hq hqp Tm
  refine ⟨c₀, hc₀, ?_⟩
  intro W Vlo Vhi T hW hW0 hT hTm hK hlo hhi t ht x hx
  have hW0H := closure_mono hK (start_mem_closure_fwdHull hW hT)
  obtain ⟨uq, up, huq, hup, -, hgap⟩ := hpair W T hW hW0 hT.le hTm hW0H hK
  have hWq : W 0 < q := by rwa [hW0]
  have hxq := hx.2.trans_lt (max_lt (hlo.lt_gmap hW hWq huq ht) (hhi.lt_gmap hW hWq huq ht))
  have he := hgap t ht
  rw [fwdMap_eq_of_isForwardSol hW hup ht]
  exact (show c₀ ≤ (up t).re + W t - x by linarith only [he, hxq]).trans (le_abs_self _)

/-- The seeded logarithmic noise has a deterministic enclosure bound,
without a lower bound on an own seed gap. -/
theorem exists_seed_noise_bound_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hp : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (Tm κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) (Vhi t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) (Vhi t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂)
            κ rr (W₂ t₂) p V).ellX t (W t)| ≤ K := by
  obtain ⟨c₀, hc₀, hgap⟩ := exists_original_source_gap_right hH₁ hδ hsep hp hq hqp hd hqH Tm
  obtain ⟨r, L₀, hr, -, hint⟩ :=
    exists_seed_interval_own_bounds_right hH₁ hH₂ hδ hsep hd hqH Tm
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right hH₁ hH₂ hδ hsep hp hq hqp hd hqH Tm
  refine ⟨SeedData.noiseBound κ rr r L₀ Lrem c₀, ?_, ?_⟩
  · unfold SeedData.noiseBound
    exact add_nonneg (mul_nonneg (add_nonneg (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (div_nonneg (div_nonneg (by norm_num) hr.le) (Real.exp_pos _).le))
      (mul_nonneg (by norm_num) (add_nonneg
        (div_nonneg (Real.exp_pos _).le (mul_pos (Real.exp_pos _) hc₀).le)
        (div_nonneg zero_le_one hc₀.le)))
  intro W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI t ht
  let s := SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p V
  have hW0H := closure_mono hK₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rwa [hW₂0]
  have hb := hint W W₂ Vlo Vhi T t₂ a W' h hW₂ ht₂ hW0H hW₂H
    (by rwa [h.zero]) (by rwa [hW₂0]) ht₂m hK₁ hK₂ hlo hhi t ht
  have hs : ∀ x ∈ uIcc (Vlo t) (Vhi t), deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) :=
    fun x hx => (hb x hx).2
  have hremote := hrem κ rr W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂
    hlo hhi hWI hVI t ht
  have hg := hgap W Vlo Vhi T h.cont h.zero h.pos hTm hK₁ hlo hhi t ht (W t) (hWI t ht)
  have hg' : c₀ ≤ |s.W t - s.V₀ t| := by
    change c₀ ≤ |W t - ((fwdMap W t p).re + W t)|
    rwa [abs_sub_comm]
  exact s.abs_ellX_driver_le h ht hr hc₀ (convex_uIcc _ _) (hWI t ht) (hVI t ht)
    (fun x hx => (hb x hx).1) hs hremote hg'

end InteractingSLE.ZhanGT4

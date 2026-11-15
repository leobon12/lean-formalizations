/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcInterval
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteBounds
import InteractingSLE.Spec.ZhanGT4.DualSeedImageUniform

/-!
# Zhan's A.1, G3: the separated-source scales and the noise bound on the extended own interval

Packet PROVE-A1-G3CALC (R48). A22's `exists_seed_remoteScale_right`, `exists_original_source_gap_right` and
`exists_seed_noise_bound_right` with the seed interval replaced by the extended interval `[V_lo(t), g_t(q) + W_t]`
(`A1G3CalcInterval`). The protected point `q` is the right end of the interval, so the other source keeps A22's
uniform gap `g_t(p) − g_t(q) ≥ c` from every point of it; the interval is bounded by `|q| + 7R` instead of `7R`.

* `abs_le_of_mem_ext_interval`: the bound `|x| ≤ |q| + 7R` on the extended interval;
* **`exists_ext_remoteScale_right`**: `SeedData.RemoteScale` at one enclosure scale for every mark in the extended
  interval;
* `exists_ext_source_gap_right`, **`exists_ext_noise_bound_right`**: the uniform bound on `∂ₓℓ` at the driver.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

open InteractingSLE.ZhanGT4

/-- The extended interval is bounded: `|x| ≤ |q| + 7R` when the hull lies in the ball of radius `R` about `0`. -/
theorem abs_le_of_mem_ext_interval {W Vlo : ℝ → ℝ} {T R t x q : ℝ} {uq : ℝ → ℂ}
    (hlo : IsSeedCoordinate W Vlo T) (hW : Continuous W) (hT : 0 ≤ T) (hR : 0 < R)
    (hK : fwdHull W T ⊆ closedBall (0 : ℂ) R) (hW0 : |W 0| ≤ R)
    (huq : IsForwardSol W (q : ℂ) T uq) (ht : t ∈ Icc (0 : ℝ) T)
    (hx : x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) : |x| ≤ |q| + 7 * R := by
  have hl := abs_le.1 (hlo.abs_le_of_hull_subset_ball hW hT hR hK hW0 ht)
  rw [fwdMap_eq_of_isForwardSol hW huq ht] at hx
  have hb := norm_sol_add_sub_le hW ht.1 hR (((QuantumZipper.fwdHull_mono).1 ht.2).trans hK)
    (isForwardSol_restrict huq ht.2)
  have hre : |(uq t).re + W t| ≤ |q| + 5 * R := by
    have h1 := (Complex.abs_re_le_norm _).trans hb
    simpa only [Complex.ofReal_zero, sub_zero, Complex.add_re, Complex.ofReal_re, Complex.norm_real,
      Real.norm_eq_abs] using h1
  have hq := abs_le.1 hre
  have h1 : min (Vlo t) ((uq t).re + W t) ≤ x := hx.1
  have h2 : x ≤ max (Vlo t) ((uq t).re + W t) := hx.2
  have hqa := abs_nonneg q
  rw [abs_le]
  constructor
  · have hm : -(|q| + 7 * R) ≤ min (Vlo t) ((uq t).re + W t) :=
      le_min (by linarith [hl.1]) (by linarith [hq.1])
    linarith
  · have hm : max (Vlo t) ((uq t).re + W t) ≤ |q| + 7 * R :=
      max_le (by linarith [hl.2]) (by linarith [hq.2])
    linarith

/-- **The separated-source factors on the extended interval have one enclosure scale** (A22's
`exists_seed_remoteScale_right`, every mark in `[V_lo(t), g_t(q) + W_t]`). -/
theorem exists_ext_remoteScale_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hpH₂ : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖) (Tm : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ {n : ℕ} (κ : ℝ) (rr : Fin n → ℝ)
        (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          (SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂)
            κ rr (W₂ t₂) p V).RemoteScale t L := by
  have hpH₁ : Disjoint (ball (p : ℂ) δ) H₁ := by
    refine Set.disjoint_left.2 fun z hz hzH => ?_
    have hcl : closure H₂ ⊆ {w : ℂ | 2 * δ ≤ ‖w - z‖} :=
      (isClosed_le continuous_const (continuous_id.sub continuous_const).norm).closure_subset_iff.2
        (fun w hw => hsep w hw z hzH)
    have hh : 2 * δ ≤ ‖(p : ℂ) - z‖ := hcl hpH₂
    rw [mem_ball, dist_eq_norm, norm_sub_rev] at hz
    linarith
  obtain ⟨μ, co, hμ, hco, hpair⟩ := exists_protected_pair_gap hH₁
    (by positivity : 0 < 2 * d) hδ (hqH.mono_right subset_union_left) hpH₁ hq hqp Tm
  obtain ⟨r, L₀, hr, hL₀, hint⟩ :=
    exists_ext_interval_own_bounds_right hH₁ hH₂ hδ hsep hq hd hqH hseg Tm
  obtain ⟨r₀, a₀, γ, Γ, lam, hr₀, ha₀, hγ, hd9⟩ :=
    exists_twoCurveD9 hH₁ hH₂ hδ hsep hd hq hqH
      (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m) Tm
  obtain ⟨C₀, hC₀⟩ := (hH₁.2.1.union hH₂.2.1).exists_norm_le
  let R := max C₀ 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hball : H₁ ∪ H₂ ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    rw [mem_closedBall_zero_iff]
    exact (hC₀ z hz).trans (le_max_left _ _)
  let cn := r / 96 * Real.exp (-L₀)
  have hcn : 0 < cn := by dsimp only [cn]; positivity
  let C := |Γ| + |p| + |q| + 2 * (|q| + 7 * R) * Real.exp L₀ + 12 * R + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  obtain ⟨Lgap, hLgap, hscalegap⟩ := exists_inScale_of_abs_bounds
    (div_pos hcn hC) (div_pos hC hco)
  obtain ⟨L21, hL21, hscale21⟩ := exists_inScale_of_abs_bounds
    (div_pos (Real.exp_pos (-lam)) (Real.exp_pos lam)) (div_pos (Real.exp_pos lam) hμ)
  let Llog := |Tm| * rateBound r₀ a₀
  let L := max (max Lgap L21) Llog
  have hLgapL : Lgap ≤ L := (le_max_left _ _).trans (le_max_left _ _)
  have hL21L : L21 ≤ L := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨L, hLgap.trans hLgapL, ?_⟩
  intro n κ rr W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂ hlo hhi hWI hVI t ht
  let φ : ℂ → ℂ := fun z => fwdMap W₂ t₂ z + W₂ t₂
  let s := SeedData.fromSource W W' a φ κ rr (W₂ t₂) p V
  have hW0H : (W 0 : ℂ) ∈ closure H₁ :=
    closure_mono hK₁ (start_mem_closure_fwdHull h.cont h.pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rwa [hW₂0]
  have hWq : W 0 < q := by rwa [h.zero]
  have hqW : q < W₂ 0 := by rwa [hW₂0]
  have hbounds := hint W W₂ Vlo Vhi T t₂ a W' h hW₂ ht₂
    hW0H hW₂H hqW ht₂m hK₁ hK₂ hlo hhi t ht
  have hh := hd9 W W₂ t₂ T a W' 0 Fin.elim0 h hW₂ hW₂H hqW ht₂ ht₂m hTm hK₁ hK₂
  let fd : FrzData 0 := ⟨W, W', a, φ, 0, Fin.elim0, W₂ t₂,
    fun m => (fwdMap W₂ t₂ ((Fin.elim0 m : ℝ) : ℂ)).re + W₂ t₂⟩
  have hc : fd.D9Const (fwdHull W₂ t₂) T r₀ a₀ γ Γ lam := hh.d9
  obtain ⟨v₀, hv₀⟩ := hh.alive₀
  obtain ⟨uq, up, huq, hup, hderp, hpairgap⟩ :=
    hpair W T h.cont h.zero h.pos.le hTm hW0H hK₁
  have hKball := hK₁.trans (subset_union_left.trans hball)
  have hW0R : |W 0| ≤ R := by rw [h.zero, abs_zero]; exact hR.le
  have hxb : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t), |x| ≤ |q| + 7 * R := fun x hx =>
    abs_le_of_mem_ext_interval hlo h.cont h.pos.le hR hKball hW0R huq ht hx
  have hV₀ : s.V₀ t = (up t).re + W t := by
    dsimp only [s, SeedData.fromSource]
    rw [fwdMap_eq_of_isForwardSol h.cont hup ht]
  have hV₀b : |s.V₀ t| ≤ |p| + 5 * R := by
    have hb := norm_sol_add_sub_le h.cont ht.1 hR
      (((QuantumZipper.fwdHull_mono).1 ht.2).trans hKball) (isForwardSol_restrict hup ht.2)
    have hre := (Complex.abs_re_le_norm _).trans hb
    simpa only [Complex.ofReal_zero, sub_zero, Complex.add_re, Complex.ofReal_re,
      Complex.norm_real, Real.norm_eq_abs, hV₀] using hre
  have hownGap : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t),
      co ≤ |s.V₀ t - x| ∧ |s.V₀ t - x| ≤ C := by
    intro x hx
    have hxp : x ≤ (uq t).re + W t := by
      rw [fwdMap_eq_of_isForwardSol h.cont huq ht] at hx
      exact hx.2.trans (max_le (hlo.lt_gmap h.cont hWq huq ht).le le_rfl)
    have hl := hpairgap t ht
    have hg : co ≤ s.V₀ t - x := by rw [hV₀]; linarith
    refine ⟨hg.trans (le_abs_self _), ?_⟩
    have hb := (abs_sub _ _).trans (add_le_add hV₀b (hxb x hx))
    have hq0 : 0 ≤ (|q| + 7 * R) * Real.exp L₀ := by positivity
    dsimp only [C]
    linarith [abs_nonneg Γ]
  have hdiff : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t), DifferentiableAt ℝ (s.F 0 t) x := by
    intro x hx
    have hg := (h.ownExt_props ht (hbounds x hx).1).1
    have hxD := (hg.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).hasDerivAt
    exact hxD.real_of_complex.differentiableAt
  have hder : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t), ‖deriv (s.F 0 t) x‖ ≤ Real.exp L₀ := by
    intro x hx
    have hb := (hbounds x hx).2
    change deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) at hb
    rw [Real.norm_eq_abs, abs_of_pos ((Real.exp_pos _).trans_le hb.1)]
    exact hb.2
  obtain ⟨a₂, W₂', h₂⟩ := exists_imgData hW₂ ht₂
    (isHPHull_fwdHull h.cont ht.1) (isMapOut_fwdMap_gen h.cont ht.1)
    (h.disj.symm.mono (closure_mono ((QuantumZipper.fwdHull_mono).1 ht.2)) Subset.rfl)
  have himgGap : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t),
      cn ≤ |s.A20 t - s.F 0 t x| ∧ |s.A20 t - s.F 0 t x| ≤ C := by
    intro x hx
    refine ⟨h.le_abs_frzImg_sub_ownExt ht h₂ hv₀ hr (hbounds x hx).1 (hbounds x hx).2.1, ?_⟩
    have hmv := (convex_uIcc (Vlo t) ((fwdMap W t q).re + W t)).norm_image_sub_le_of_norm_deriv_le
      hdiff hder (hWI t ht) hx
    have hWb := hxb (W t) (hWI t ht)
    have hxb' := hxb x hx
    have he0 := (hc.E0 t ht).2
    change |s.A20 t - s.A 0 t| ≤ Γ at he0
    have hsW : s.F 0 t (W t) = s.A 0 t := rfl
    rw [hsW, Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have hsub : |x - W t| ≤ 2 * (|q| + 7 * R) := by
      exact (abs_sub _ _).trans (by linarith)
    have htri : |s.A20 t - s.F 0 t x| ≤ |s.A20 t - s.A 0 t| + |s.F 0 t x - s.A 0 t| := by
      have he : s.A20 t - s.F 0 t x = (s.A20 t - s.A 0 t) - (s.F 0 t x - s.A 0 t) := by ring
      rw [he]
      exact abs_sub _ _
    have hb : |s.A20 t - s.F 0 t x| ≤ Γ + Real.exp L₀ * (2 * (|q| + 7 * R)) :=
      htri.trans (add_le_add he0 (hmv.trans (mul_le_mul_of_nonneg_left hsub (Real.exp_pos _).le)))
    have he : Real.exp L₀ * (2 * (|q| + 7 * R)) = 2 * (|q| + 7 * R) * Real.exp L₀ := by ring
    dsimp only [C]
    linarith [le_abs_self Γ, abs_nonneg p, abs_nonneg q, hR]
  have hquot : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t),
      InScale L ((s.A20 t - s.F 0 t x) / (s.V₀ t - x)) := by
    intro x hx
    have hb := abs_div_bounds hcn hco hC (himgGap x hx) (hownGap x hx)
    exact FrzData.inScale_mono (hscalegap _ hb.1 hb.2) hLgapL
  change s.RemoteScale t L
  refine ⟨?_, ?_, fun m => hquot (V m t) (hVI t ht m), ?_⟩
  · have hnum := hc.A21 t ht
    change InScale lam (frzImgD W' a (W₂ t₂) t) at hnum
    have hd := hderp t ht
    have hd' : μ ≤ |s.G₀ t| ∧ |s.G₀ t| ≤ 1 := by
      change μ ≤ |(deriv (fwdMap W t) p).re| ∧ |(deriv (fwdMap W t) p).re| ≤ 1
      rw [abs_of_pos (hμ.trans_le hd.1)]
      exact hd
    have hb := abs_div_bounds (b := s.G₀ t) (Real.exp_pos (-lam)) hμ
      (Real.exp_pos lam) hnum ?_
    · exact FrzData.inScale_mono (hscale21 _ hb.1 hb.2) hL21L
    · exact ⟨hd'.1, hd'.2.trans (Real.one_le_exp (by
        have he := hnum.1.trans hnum.2
        have hn := Real.exp_le_exp.1 he
        linarith))⟩
  · have hrate : 0 ≤ rateBound r₀ a₀ := by unfold rateBound; positivity
    have hb : ∀ u ∈ uIoc (0 : ℝ) t, ‖frzRate W W' a φ u‖ ≤ rateBound r₀ a₀ := by
      intro u hu
      rw [uIoc_of_le ht.1] at hu
      exact fd.abs_frzRate_le h hc ⟨hu.1.le, hu.2.trans ht.2⟩
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at hi
    apply le_trans hi
    apply le_trans ?_ (le_max_right (max Lgap L21) Llog)
    change rateBound r₀ a₀ * t ≤ |Tm| * rateBound r₀ a₀
    nlinarith [(ht.2.trans hTm).trans (le_abs_self Tm)]
  · convert hquot (W t) (hWI t ht) using 1
    rw [show s.F 0 t (W t) = s.A 0 t from rfl]
    change (s.A 0 t - s.A20 t) / (W t - s.V₀ t) =
      (s.A20 t - s.A 0 t) / (s.V₀ t - W t)
    rw [show s.A 0 t - s.A20 t = -(s.A20 t - s.A 0 t) by ring,
      show W t - s.V₀ t = -(s.V₀ t - W t) by ring, neg_div_neg_eq]

/-- The other source stays uniformly away from the extended interval (A22's `exists_original_source_gap_right`). -/
theorem exists_ext_source_gap_right {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hp : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂)) (Tm : ℝ) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (W Vlo Vhi : ℝ → ℝ) (T : ℝ),
      Continuous W → W 0 = 0 → 0 < T → T ≤ Tm → fwdHull W T ⊆ H₁ →
      IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t),
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
  rw [fwdMap_eq_of_isForwardSol hW huq ht] at hx
  have hxq := hx.2.trans (max_le (hlo.lt_gmap hW hWq huq ht).le le_rfl)
  have he := hgap t ht
  rw [fwdMap_eq_of_isForwardSol hW hup ht]
  exact (show c₀ ≤ (up t).re + W t - x by linarith only [he, hxq]).trans (le_abs_self _)

/-- **The seeded noise on the extended interval has a deterministic enclosure bound** (A22's
`exists_seed_noise_bound_right`). -/
theorem exists_ext_noise_bound_right {H₁ H₂ : Set ℂ}
    (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hp : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖)
    (Tm κ : ℝ) {n : ℕ} (rr : Fin n → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (W W₂ a W' Vlo Vhi : ℝ → ℝ) (V : Fin n → ℝ → ℝ) (T t₂ : ℝ),
        OwnData W (fwdHull W₂ t₂) (fun z => fwdMap W₂ t₂ z + W₂ t₂) T a W' →
        Continuous W₂ → W₂ 0 = p → 0 < t₂ → t₂ ≤ Tm → T ≤ Tm →
        fwdHull W T ⊆ H₁ → fwdHull W₂ t₂ ⊆ H₂ →
        IsSeedCoordinate W Vlo T → IsSeedCoordinate W Vhi T →
        (∀ t ∈ Icc (0 : ℝ) T, W t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        (∀ t ∈ Icc (0 : ℝ) T, ∀ m, V m t ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t)) →
        ∀ t ∈ Icc (0 : ℝ) T,
          |(SeedData.fromSource W W' a (fun z => fwdMap W₂ t₂ z + W₂ t₂)
            κ rr (W₂ t₂) p V).ellX t (W t)| ≤ K := by
  obtain ⟨c₀, hc₀, hgap⟩ := exists_ext_source_gap_right hH₁ hδ hsep hp hq hqp hd hqH Tm
  obtain ⟨r, L₀, hr, -, hint⟩ :=
    exists_ext_interval_own_bounds_right hH₁ hH₂ hδ hsep hq hd hqH hseg Tm
  obtain ⟨Lrem, -, hrem⟩ := exists_ext_remoteScale_right hH₁ hH₂ hδ hsep hp hq hqp hd hqH hseg Tm
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
    (by rwa [hW₂0]) ht₂m hK₁ hK₂ hlo hhi t ht
  have hs : ∀ x ∈ uIcc (Vlo t) ((fwdMap W t q).re + W t),
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) :=
    fun x hx => (hb x hx).2
  have hremote := hrem κ rr W W₂ a W' Vlo Vhi V T t₂ h hW₂ hW₂0 ht₂ ht₂m hTm hK₁ hK₂
    hlo hhi hWI hVI t ht
  have hg := hgap W Vlo Vhi T h.cont h.zero h.pos hTm hK₁ hlo hhi t ht (W t) (hWI t ht)
  have hg' : c₀ ≤ |s.W t - s.V₀ t| := by
    change c₀ ≤ |W t - ((fwdMap W t p).re + W t)|
    rwa [abs_sub_comm]
  exact s.abs_ellX_driver_le h ht hr hc₀ (convex_uIcc _ _) (hWI t ht) (hVI t ht)
    (fun x hx => (hb x hx).1) hs hremote hg'

end InteractingSLE.ZhanGT4.A1G3Calc

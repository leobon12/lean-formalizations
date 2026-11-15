/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3CalcRemote
import InteractingSLE.Spec.ZhanGT4.DualSeedImagePrepare

/-!
# Zhan's A.1, G3: mixed seed/ordinary mark coordinates and the prepared seeded noise

Packet PROVE-A1-G3CALC (R48). Source: Astra, *Follow-up proofs*, §A.1.6 (`ig1_followup_proofs.txt` L426–L500): the
marks enter the seeded density through their own-chart force coordinates `V^m` with `V' = 2/(V − W)`, "seeds and
ordinary marks alike"; a seed is an integrated force coordinate (`IsSeedCoordinate`), an ordinary mark `p_m` is the
real flow `g_t(p_m)`. A22's analytic lemmas use of a seed only its continuity, its noncollision with the driver at
positive times and the force ODE there; `IsMarkCoordinate` records exactly these.

* **`IsMarkCoordinate`**, `isMarkCoordinate_of_seed`, **`isMarkCoordinate_of_forwardSol`** (an alive real point
  `g_t(p) + W_t` is a mark coordinate);
* `continuousOn_ellX_driver_mark`: A22's `SeedData.continuousOn_ellX_driver` for mark coordinates;
* **`exists_seedNoise_prepared_ext`**: A22's `exists_seedNoise_prepared_right` (predictable, Riemann-regular, bounded
  seeded noise) on the extended interval, for mark coordinates.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4.A1G3Calc

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

open InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A mark coordinate up to the horizon `T`**: continuous on `[0, T]`, off the driver at positive times, and
solving the force ODE `V' = 2/(V − W)` at positive times. Integrated seed coordinates and the real flow of an ordinary
mark both are. -/
structure IsMarkCoordinate (W V : ℝ → ℝ) (T : ℝ) : Prop where
  cont : ContinuousOn V (Icc 0 T)
  ne : ∀ s ∈ Ioc 0 T, V s ≠ W s
  deriv : ∀ s ∈ Ioc 0 T, HasDerivWithinAt V (2 / (V s - W s)) (Ioc 0 T) s

/-- An integrated seed coordinate of a continuous driver is a mark coordinate. -/
theorem isMarkCoordinate_of_seed {W V : ℝ → ℝ} {T : ℝ} (h : IsSeedCoordinate W V T) (hW : Continuous W) :
    IsMarkCoordinate W V T :=
  ⟨h.cont, h.ne, fun _ hs => h.hasDerivWithinAt_pos hW hs⟩

/-- **The real flow of an ordinary mark is a mark coordinate**: for an alive forward solution from the real point `p`,
`V t = Re g_t(p) + W_t` (`fwdMap` is centered) is continuous, never meets the driver, and solves `V' = 2/(V − W)`
(A22's `source_gmap_rates`). -/
theorem isMarkCoordinate_of_forwardSol {W : ℝ → ℝ} (hW : Continuous W) {p T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (p : ℂ) T u) :
    IsMarkCoordinate W (fun t => (fwdMap W t p).re + W t) T where
  cont := fun _ ht => (source_gmap_rates hW hu ht).1.continuousWithinAt
  ne := by
    intro s hs he
    have hs' := Ioc_subset_Icc_self hs
    have h0 : (fwdMap W s p).re = 0 := by linarith
    rw [fwdMap_eq_of_isForwardSol hW hu hs'] at h0
    exact (hu.2 s hs').1 (Complex.ext h0 (im_eq_zero_of_isForwardSol_real hW hu hs'))
  deriv := fun s hs => (source_gmap_rates hW hu (Ioc_subset_Icc_self hs)).1.mono Ioc_subset_Icc_self

/-- A22's `SeedData.continuousOn_ellX_driver` for mark coordinates (only their continuity and noncollision are
used). -/
theorem continuousOn_ellX_driver_mark {n : ℕ} (s : SeedData n) {A : Set ℂ}
    {T r L₀ Lrem : ℝ} {I : ℝ → Set ℝ}
    (h : OwnData s.W A s.φ T s.a s.W')
    {v₀ : ℝ → ℂ} (hv₀ : QuantumZipper.IsForwardSol s.W' s.ζ₀ (s.a T) v₀)
    (hr : 0 < r) (hI : ∀ t ∈ Icc (0 : ℝ) T, Convex ℝ (I t))
    (hWI : ∀ t ∈ Icc (0 : ℝ) T, s.W t ∈ I t)
    (hVI : ∀ t ∈ Icc (0 : ℝ) T, ∀ m, s.V m t ∈ I t)
    (hclear : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t, Disjoint (ball (x : ℂ) r)
      ((fun z => QuantumZipper.fwdMap s.W t z + s.W t) '' A))
    (hb : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ I t,
      deriv (s.F 0 t) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀))
    (hremote : ∀ t ∈ Icc (0 : ℝ) T, s.RemoteScale t Lrem)
    (hseed : ∀ m, IsMarkCoordinate s.W (s.V m) T)
    (hV₀c : ContinuousOn s.V₀ (Icc 0 T)) :
    ContinuousOn (fun t => s.ellX t (s.W t)) (Ioc 0 T) := by
  have nz : ∀ {u : ℝ}, InScale Lrem u → u ≠ 0 := by
    intro u hu he
    have hp := hu.1
    rw [he, abs_zero] at hp
    exact (not_le_of_gt (Real.exp_pos _)) hp
  have hrem : ∀ t ∈ Ioc (0 : ℝ) T,
      s.A 0 t - s.A20 t ≠ 0 ∧ s.W t - s.V₀ t ≠ 0 := by
    intro t ht
    exact div_ne_zero_iff.1 (nz (hremote t (Ioc_subset_Icc_self ht)).driver)
  have hB : ∀ m, ContinuousOn (fun t => s.B0 t m) (Ioc 0 T) := fun m =>
    (continuous_re.comp_continuousOn (h.continuousOn_iterDeriv_moving hr (hseed m).cont
      (fun t ht => hclear t ht _ (hVI t ht m)) 0)).mono Ioc_subset_Icc_self
  have hne : ∀ t ∈ Ioc (0 : ℝ) T, ∀ m, s.A 0 t - s.B0 t m ≠ 0 := by
    intro t ht m
    have ht' := Ioc_subset_Icc_self ht
    have hd : DifferentiableOn ℝ (s.F 0 t) (I t) := by
      intro x hx
      have hh := (h.ownExt_props ht' (hclear t ht' x hx)).1
      have hdx := hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
      exact hdx.hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt
    have hmono := strictMonoOn_of_deriv_pos (hI t ht') hd.continuousOn
      (fun x hx => (Real.exp_pos _).trans_le (hb t ht' x (interior_subset hx)).1)
    intro he
    have hi : s.F 0 t (s.W t) = s.F 0 t (s.V m t) := sub_eq_zero.1 he
    exact (hseed m).ne t ht (hmono.injOn (hVI t ht' m) (hWI t ht') hi.symm)
  have hy := continuousOn_dualLogSpaceX (κ := s.κ) (r := s.r)
    ((h.continuousOn_frzA 0).mono Ioc_subset_Icc_self)
    ((h.continuousOn_frzA 1).mono Ioc_subset_Icc_self)
    ((h.continuousOn_frzA 2).mono Ioc_subset_Icc_self)
    ((show ContinuousOn s.A20 (Icc 0 T) from fun t ht =>
      (h.hasDerivWithinAt_frzImg hv₀ ht).continuousWithinAt).mono Ioc_subset_Icc_self)
    hB (fun t ht => (h.frzA_one_pos (Ioc_subset_Icc_self ht)).ne')
    (fun t ht => (hrem t ht).1) hne
  have h0 := continuousOn_dualLogSpaceX (κ := s.κ) (r := s.r)
    (f1 := fun _ => 1) (f2 := fun _ => 0)
    (h.cont.continuousOn.mono Ioc_subset_Icc_self) continuousOn_const continuousOn_const
    (hV₀c.mono Ioc_subset_Icc_self) (fun m => (hseed m).cont.mono Ioc_subset_Icc_self)
    (fun _ _ => one_ne_zero) (fun t ht => (hrem t ht).2)
    (fun t ht m => sub_ne_zero.2 ((hseed m).ne t ht).symm)
  exact hy.sub h0

/-- **The prepared seeded noise on the extended interval** (A22's `exists_seedNoise_prepared_right` with marks in
`[V_lo(t), g_t(q) + W_t]` that are mark coordinates): the noise is the noise coordinate, strongly predictable,
Riemann-regular and bounded by an enclosure constant. -/
theorem exists_seedNoise_prepared_ext
    {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hp : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (hseg : ∀ a ∈ H₂, ∀ y : ℝ, 0 < y → y ≤ q → 2 * δ ≤ ‖a - y‖)
    (𝓕 : Filtration ℝ≥0 mΩ) (P : Measure Ω) {κ : ℝ} {n : ℕ} (rr : Fin n → ℝ)
    {W₂ : ℝ → ℝ} (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = p)
    {t₂ Tm : ℝ} (ht₂ : 0 < t₂) (ht₂m : t₂ ≤ Tm) (hK₂ : fwdHull W₂ t₂ ⊆ H₂)
    {X : ℝ≥0 → Ω → ℝ} (hXm : ∀ u, Measurable[𝓕 u] (X u)) (hXc : ∀ ω, Continuous (X · ω))
    {sdata : Ω → SeedData n} {Vlo Vhi : Ω → ℝ → ℝ} {T : Ω → ℝ≥0}
    (hdsource : ∀ ω, sdata ω = SeedData.fromSource (sdata ω).W (sdata ω).W' (sdata ω).a
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p (sdata ω).V)
    (hdW : ∀ ω, (sdata ω).W = Ito.rpath (X · ω))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    (h : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂) (sdata ω).φ (T ω)
      (sdata ω).a (sdata ω).W')
    (hK₁ : ∀ ω, fwdHull (sdata ω).W (T ω) ⊆ H₁)
    (hlo : ∀ ω, IsSeedCoordinate (sdata ω).W (Vlo ω) (T ω))
    (hhi : ∀ ω, IsSeedCoordinate (sdata ω).W (Vhi ω) (T ω))
    (hWI : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      (sdata ω).W t ∈ uIcc (Vlo ω t) ((fwdMap (sdata ω).W t q).re + (sdata ω).W t))
    (hVI : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      ∀ m, (sdata ω).V m t ∈ uIcc (Vlo ω t) ((fwdMap (sdata ω).W t q).re + (sdata ω).W t))
    (hseed : ∀ ω m, IsMarkCoordinate (sdata ω).W ((sdata ω).V m) (T ω))
    (hVm : ∀ (u : ℝ≥0) m,
      Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).V m u))
    (hV₀m : ∀ u : ℝ≥0,
      Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).V₀ u)) :
    ∃ C : ℝ, 0 ≤ C ∧ SeedNoiseCoordinate κ sdata T (seedNoise κ sdata T) ∧
      IsStronglyPredictable 𝓕 (seedNoise κ sdata T) ∧
      Girsanov.IsRiemannRegular P (seedNoise κ sdata T) ∧
      (∀ u ω, |seedNoise κ sdata T u ω| ≤ C) := by
  have hdκ : ∀ ω, (sdata ω).κ = κ := fun ω => congrArg SeedData.κ (hdsource ω)
  have hdr : ∀ ω, (sdata ω).r = rr := fun ω => congrArg SeedData.r (hdsource ω)
  have hdφ : ∀ ω, (sdata ω).φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) :=
    fun ω => congrArg SeedData.φ (hdsource ω)
  have hdζ : ∀ ω, (sdata ω).ζ₀ = W₂ t₂ := fun ω => congrArg SeedData.ζ₀ (hdsource ω)
  have hdV₀ : ∀ ω, (sdata ω).V₀ = fun u => (fwdMap (sdata ω).W u p).re + (sdata ω).W u :=
    fun ω => congrArg SeedData.V₀ (hdsource ω)
  have hown : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (sdata ω).a (sdata ω).W' := by
    intro ω
    rw [← hdφ ω]
    exact h ω
  have hW0H : ∀ ω, ((sdata ω).W 0 : ℂ) ∈ closure H₁ := fun ω =>
    closure_mono (hK₁ ω) (start_mem_closure_fwdHull (h ω).cont (h ω).pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rwa [hW₂0]
  obtain ⟨r, L₀, hr, -, hinterval⟩ :=
    exists_ext_interval_own_bounds_right hH₁ hH₂ hδ hsep hq hd hqH hseg Tm
  have hint : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) →
      ∀ x ∈ uIcc (Vlo ω u) ((fwdMap (sdata ω).W u q).re + (sdata ω).W u),
      Disjoint (ball (x : ℂ) r)
        ((fun z => fwdMap (sdata ω).W u z + (sdata ω).W u) '' fwdHull W₂ t₂) ∧
      deriv ((sdata ω).F 0 u) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) := by
    intro ω u hu x hx
    have hb := hinterval (sdata ω).W W₂ (Vlo ω) (Vhi ω) (T ω) t₂
      (sdata ω).a (sdata ω).W' (hown ω) hW₂ ht₂ (hW0H ω) hW₂H
      (by rwa [hW₂0]) ht₂m (hK₁ ω) hK₂ (hlo ω) (hhi ω) u hu x hx
    refine ⟨hb.1, ?_⟩
    change deriv (fun y : ℝ => (ownExt (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ u y).re) x ∈ _
    rw [hdφ ω]
    exact hb.2
  obtain ⟨Lrem, -, hrem⟩ := exists_ext_remoteScale_right hH₁ hH₂ hδ hsep hp hq hqp hd hqH hseg Tm
  have hremote : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → (sdata ω).RemoteScale u Lrem := by
    intro ω u hu
    have hb := hrem κ rr (sdata ω).W W₂ (sdata ω).a (sdata ω).W' (Vlo ω) (Vhi ω)
      (sdata ω).V (T ω) t₂ (hown ω) hW₂ hW₂0 ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
      (hlo ω) (hhi ω) (hWI ω) (hVI ω) u hu
    simpa only [← hdsource ω] using hb
  obtain ⟨r₀, a₀, γ, Γ, lam, -, -, -, hd9⟩ :=
    exists_twoCurveD9 hH₁ hH₂ hδ hsep hd hq hqH
      (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m) Tm
  have hv₀ : ∀ ω, ∃ v, QuantumZipper.IsForwardSol (sdata ω).W' (sdata ω).ζ₀ ((sdata ω).a (T ω)) v := by
    intro ω
    rw [hdζ ω]
    exact (hd9 (sdata ω).W W₂ t₂ (T ω) (sdata ω).a (sdata ω).W' 0 Fin.elim0 (hown ω)
      hW₂ hW₂H (by rwa [hW₂0]) ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂).alive₀
  have hV₀c : ∀ ω, ContinuousOn (sdata ω).V₀ (Icc 0 (T ω)) := by
    intro ω
    obtain ⟨a₂, W₂', h₂⟩ := exists_imgData hW₂ ht₂
      (isHPHull_fwdHull (h ω).cont (h ω).pos.le) (isMapOut_fwdMap_gen (h ω).cont (h ω).pos.le)
      (h ω).disj.symm
    obtain ⟨v, hv, -⟩ := h₂.exists_start_alive (h ω).cont (h ω).pos.le
      (by rw [hW₂0, (h ω).zero]; exact (hq.trans hqp).ne')
    rw [hW₂0] at hv
    rw [hdV₀ ω]
    exact fun u hu => (source_gmap_rates (h ω).cont hv hu).1.continuousWithinAt
  have hc : ∀ ω, ContinuousOn
      (fun u : ℝ≥0 => (sdata ω).ellX u ((sdata ω).W u)) (Ioc 0 (T ω)) := by
    intro ω
    have hc' := continuousOn_ellX_driver_mark (sdata ω) (h ω) (hv₀ ω).choose_spec hr
      (fun _ _ => convex_uIcc _ _) (hWI ω) (hVI ω)
      (fun u hu x hx => (hint ω u hu x hx).1) (fun u hu x hx => (hint ω u hu x hx).2)
      (hremote ω) (hseed ω) (hV₀c ω)
    exact hc'.comp NNReal.continuous_coe.continuousOn (fun u hu => hu)
  have hm : ∀ u : ℝ≥0, Measurable[𝓕 u]
      ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).ellX u ((sdata ω).W u)) := by
    intro u
    exact measurable_seed_ellX hXm hXc hdW hdφ hdζ u (measurableSet_ge_of_isStoppingTime hT u)
      (fun ω hω => hω) (fun ω _ => h ω) (fun ω _ => hv₀ ω)
      (fun ω hω m => ⟨r, hr, (hint ω u ⟨u.coe_nonneg, hω⟩ _ (hVI ω u ⟨u.coe_nonneg, hω⟩ m)).1⟩)
      (hVm u) hdκ hdr (hV₀m u)
  obtain ⟨K, hK, hbound⟩ := exists_ext_noise_bound_right hH₁ hH₂ hδ hsep hp hq hqp hd hqH hseg Tm κ rr
  have hb : ∀ ω u, u ∈ Ioc (0 : ℝ≥0) (T ω) → |(sdata ω).ellX u ((sdata ω).W u)| ≤ K := by
    intro ω u hu
    have hh := hbound (sdata ω).W W₂ (sdata ω).a (sdata ω).W' (Vlo ω) (Vhi ω)
      (sdata ω).V (T ω) t₂ (hown ω) hW₂ hW₂0 ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
      (hlo ω) (hhi ω) (hWI ω) (hVI ω) u ⟨u.coe_nonneg, hu.2⟩
    simpa only [← hdsource ω] using hh
  obtain ⟨hpredict, hregular⟩ := seedNoise_predictable_regular 𝓕 P hm hc
  exact ⟨Real.sqrt κ * K, mul_nonneg (Real.sqrt_nonneg _) hK,
    seedNoise_coordinate κ sdata T, hpredict, hregular, fun u ω => abs_seedNoise_le hK hb u ω⟩

end InteractingSLE.ZhanGT4.A1G3Calc

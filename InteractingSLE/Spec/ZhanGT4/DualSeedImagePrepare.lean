/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImagePredictable
import InteractingSLE.Spec.ZhanGT4.DualSeedMeas
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteSource

/-!
# Predictable seeded noise from the actual protected source data

Packet PROVE-ZHAN-GT4-A22. This assembles the geometric bound, positive-time
continuity and alive-event measurability. Predictability, Riemann regularity
and a deterministic bound are conclusions, not inputs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (fwdMap fwdHull)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The two analytic inputs of general-filtration Girsanov are obtained
from the regularized seeded evolution and protected enclosures. -/
theorem exists_seedNoise_prepared_right
    {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hp : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
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
    (hWI : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → (sdata ω).W t ∈ uIcc (Vlo ω t) (Vhi ω t))
    (hVI : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      ∀ m, (sdata ω).V m t ∈ uIcc (Vlo ω t) (Vhi ω t))
    (hseed : ∀ ω m, IsSeedCoordinate (sdata ω).W ((sdata ω).V m) (T ω))
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
    exists_seed_interval_own_bounds_right hH₁ hH₂ hδ hsep hd hqH Tm
  have hint : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → ∀ x ∈ uIcc (Vlo ω u) (Vhi ω u),
      Disjoint (ball (x : ℂ) r)
        ((fun z => fwdMap (sdata ω).W u z + (sdata ω).W u) '' fwdHull W₂ t₂) ∧
      deriv ((sdata ω).F 0 u) x ∈ Icc (Real.exp (-L₀)) (Real.exp L₀) := by
    intro ω u hu x hx
    have hb := hinterval (sdata ω).W W₂ (Vlo ω) (Vhi ω) (T ω) t₂
      (sdata ω).a (sdata ω).W' (hown ω) hW₂ ht₂ (hW0H ω) hW₂H
      (by rwa [(h ω).zero]) (by rwa [hW₂0]) ht₂m (hK₁ ω) hK₂ (hlo ω) (hhi ω) u hu x hx
    refine ⟨hb.1, ?_⟩
    change deriv (fun y : ℝ => (ownExt (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ u y).re) x ∈ _
    rw [hdφ ω]
    exact hb.2
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right hH₁ hH₂ hδ hsep hp hq hqp hd hqH Tm
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
    have hc' := (sdata ω).continuousOn_ellX_driver (h ω) (hv₀ ω).choose_spec hr
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
  obtain ⟨K, hK, hbound⟩ := exists_seed_noise_bound_right hH₁ hH₂ hδ hsep hp hq hqp hd hqH Tm κ rr
  have hb : ∀ ω u, u ∈ Ioc (0 : ℝ≥0) (T ω) → |(sdata ω).ellX u ((sdata ω).W u)| ≤ K := by
    intro ω u hu
    have hh := hbound (sdata ω).W W₂ (sdata ω).a (sdata ω).W' (Vlo ω) (Vhi ω)
      (sdata ω).V (T ω) t₂ (hown ω) hW₂ hW₂0 ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
      (hlo ω) (hhi ω) (hWI ω) (hVI ω) u ⟨u.coe_nonneg, hu.2⟩
    simpa only [← hdsource ω] using hh
  obtain ⟨hpredict, hregular⟩ := seedNoise_predictable_regular 𝓕 P hm hc
  exact ⟨Real.sqrt κ * K, mul_nonneg (Real.sqrt_nonneg _) hK,
    seedNoise_coordinate κ sdata T, hpredict, hregular, fun u ω => abs_seedNoise_le hK hb u ω⟩

end InteractingSLE.ZhanGT4

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedRemoteSource
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformMartingale

/-!
# A.1.6 for regularized seed paths on a protected rectangle

Packet PROVE-ZHAN-GT4-A22. Enclosures supply every deterministic bound;
integrated seed coordinates supply their positive-time ODE. Continuity and
noncollision of the band factors are proved internally, then the checked
A21 assembly removes both cutoffs. Only the regularized stochastic evolution
and its coordinate measurability are inputs.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap fwdHull)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A.1.6's seeded martingale on a protected rectangle.** There are no
scale, bounded-density, continuity-of-density, gap-version, or band-identity
hypotheses. The data identity specifies the actual original other-source
coordinate and derivative. -/
theorem integral_mul_seeded_source_stopped_sub_eq_zero
    {H₁ H₂ : Set ℂ} (hH₁ : IsHPHull H₁) (hH₂ : IsHPHull H₂)
    {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ a ∈ H₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖)
    {p q d : ℝ} (hpH₂ : (p : ℂ) ∈ closure H₂) (hq : 0 < q) (hqp : q < p)
    (hd : 0 < d) (hqH : Disjoint (ball (q : ℂ) (2 * d)) (H₁ ∪ H₂))
    (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (rr : Fin n → ℝ)
    {W₂ : ℝ → ℝ} (hW₂ : Continuous W₂) (hW₂0 : W₂ 0 = p)
    {t₂ Tm : ℝ} (ht₂ : 0 < t₂) (ht₂m : t₂ ≤ Tm) (hK₂ : fwdHull W₂ t₂ ⊆ H₂)
    {B D : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    {sdata : Ω → SeedData n} {Vlo Vhi : Ω → ℝ → ℝ} {T : Ω → ℝ≥0}
    (hdsource : ∀ ω, sdata ω = SeedData.fromSource (sdata ω).W (sdata ω).W' (sdata ω).a
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) κ rr (W₂ t₂) p (sdata ω).V)
    (hdW : ∀ ω, (sdata ω).W = driftDriver (Real.sqrt κ) B D ω)
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
    (hVV : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) → Function.Injective (fun m => (sdata ω).V m t))
    (hD : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (fun u : ℝ => D u.toNNReal ω) ((sdata ω).drift t) (Ioc 0 (T ω)) t)
    (hVm : ∀ (u : ℝ≥0) m,
      Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).V m u))
    (hV₀m : ∀ u : ℝ≥0,
      Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).V₀ u))
    (hG₀m : ∀ u : ℝ≥0,
      Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (sdata ω).G₀ u))
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Real.exp ((sdata ω).normEll (min t (T ω)))
      - Real.exp ((sdata ω).normEll (min s (T ω)))) ∂P = 0 := by
  have hdκ : ∀ ω, (sdata ω).κ = κ := fun ω => congrArg SeedData.κ (hdsource ω)
  have hdr : ∀ ω, (sdata ω).r = rr := fun ω => congrArg SeedData.r (hdsource ω)
  have hdφ : ∀ ω, (sdata ω).φ = (fun z => fwdMap W₂ t₂ z + W₂ t₂) :=
    fun ω => congrArg SeedData.φ (hdsource ω)
  have hdζ : ∀ ω, (sdata ω).ζ₀ = W₂ t₂ := fun ω => congrArg SeedData.ζ₀ (hdsource ω)
  have hdV₀ : ∀ ω, (sdata ω).V₀ = fun u => (fwdMap (sdata ω).W u p).re + (sdata ω).W u :=
    fun ω => congrArg SeedData.V₀ (hdsource ω)
  have hdG₀ : ∀ ω, (sdata ω).G₀ = fun u => (deriv (fwdMap (sdata ω).W u) p).re :=
    fun ω => congrArg SeedData.G₀ (hdsource ω)
  have hown : ∀ ω, OwnData (sdata ω).W (fwdHull W₂ t₂)
      (fun z => fwdMap W₂ t₂ z + W₂ t₂) (T ω) (sdata ω).a (sdata ω).W' := by
    intro ω
    rw [← hdφ ω]
    exact h ω
  have hW0H : ∀ ω, ((sdata ω).W 0 : ℂ) ∈ closure H₁ := fun ω =>
    closure_mono (hK₁ ω) (start_mem_closure_fwdHull (h ω).cont (h ω).pos)
  have hW₂H : (W₂ 0 : ℂ) ∈ closure H₂ := by rwa [hW₂0]
  obtain ⟨r, L₀, hr, hL₀, hinterval⟩ :=
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
  obtain ⟨Lrem, -, hrem⟩ := exists_seed_remoteScale_right hH₁ hH₂ hδ hsep hpH₂ hq hqp hd hqH Tm
  have hremote : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → (sdata ω).RemoteScale u Lrem := by
    intro ω u hu
    have hb := hrem κ rr (sdata ω).W W₂ (sdata ω).a (sdata ω).W' (Vlo ω) (Vhi ω)
      (sdata ω).V (T ω) t₂ (hown ω) hW₂ hW₂0 ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
      (hlo ω) (hhi ω) (hWI ω) (hVI ω) u hu
    simpa only [← hdsource ω] using hb
  obtain ⟨r₀, a₀, γ, Γ, lam, hr₀, ha₀, -, hd9⟩ :=
    exists_twoCurveD9 hH₁ hH₂ hδ hsep hd hq hqH
      (p := (Fin.elim0 : Fin 0 → ℝ)) (fun m => Fin.elim0 m) (fun m => Fin.elim0 m) Tm
  have hd9ω := fun ω => hd9 (sdata ω).W W₂ t₂ (T ω) (sdata ω).a (sdata ω).W'
    0 Fin.elim0 (hown ω) hW₂ hW₂H (by rwa [hW₂0]) ht₂ ht₂m (hTm ω) (hK₁ ω) hK₂
  have hv₀ : ∀ ω, ∃ v, IsForwardSol (sdata ω).W' (sdata ω).ζ₀ ((sdata ω).a (T ω)) v := by
    intro ω
    rw [hdζ ω]
    exact (hd9ω ω).alive₀
  have hsrc : ∀ ω, ∃ v, IsForwardSol (sdata ω).W (p : ℂ) (T ω) v := by
    intro ω
    obtain ⟨a₂, W₂', h₂⟩ := exists_imgData hW₂ ht₂
      (isHPHull_fwdHull (h ω).cont (h ω).pos.le) (isMapOut_fwdMap_gen (h ω).cont (h ω).pos.le)
      (h ω).disj.symm
    obtain ⟨v, hv, -⟩ := h₂.exists_start_alive (h ω).cont (h ω).pos.le
      (by rw [hW₂0, (h ω).zero]; exact (hq.trans hqp).ne')
    rw [hW₂0] at hv
    exact ⟨v, hv⟩
  have hrates : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) →
      HasDerivWithinAt (sdata ω).V₀ (2 / ((sdata ω).V₀ u - (sdata ω).W u)) (Icc 0 (T ω)) u ∧
      HasDerivWithinAt (sdata ω).G₀ (-2 * (sdata ω).G₀ u / ((sdata ω).V₀ u - (sdata ω).W u) ^ 2)
        (Icc 0 (T ω)) u := by
    intro ω u hu
    obtain ⟨v, hv⟩ := hsrc ω
    simpa only [hdV₀ ω, hdG₀ ω] using source_gmap_rates (h ω).cont hv hu
  have hreg := fun ω => (sdata ω).continuousOn_normEll_gapVal_of_remoteScale (h ω) (hv₀ ω).choose_spec
    hr (fun _ _ => convex_uIcc _ _) (hWI ω) (hVI ω)
    (fun u hu x hx => (hint ω u hu x hx).1) (fun u hu x hx => (hint ω u hu x hx).2)
    (hremote ω) (fun m => (hseed ω m).cont)
    (fun u hu => (hrates ω u hu).1.continuousWithinAt)
    (fun u hu => (hrates ω u hu).2.continuousWithinAt)
  have hgn : ∀ ω i u, u ∈ Ioc (0 : ℝ) (T ω) → (sdata ω).gapVal i u ≠ 0 := by
    intro ω i u hu
    have huc := Ioc_subset_Icc_self hu
    have hdiff : ∀ x ∈ uIcc (Vlo ω u) (Vhi ω u),
        DifferentiableAt ℂ (ownExt (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ u) x := by
      intro x hx
      have hd := ((h ω).ownExt_props huc (hint ω u huc x hx).1).1
      exact hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    apply (sdata ω).gapVal_ne_zero_of_remoteScale (hremote ω u huc) (convex_uIcc _ _)
      (fun x hx => (hdiff x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt)
      (fun x hx => (Real.exp_pos _).trans_le (hint ω u huc x hx).2.1)
      (fun x hx => ((sdata ω).deriv_F_zero (hdiff x hx)).symm) (hWI ω u huc) (hVI ω u huc)
      (fun m => (hseed ω m).ne u hu) (hVV ω u hu) i
  let L := max L₀ Lrem
  have hK : ∀ ω u, u ∈ Icc (0 : ℝ) (T ω) → |(sdata ω).normEll u| ≤ coefTot κ rr * L := by
    intro ω u hu
    have hdif : ∀ x ∈ uIcc (Vlo ω u) (Vhi ω u),
        DifferentiableAt ℂ (ownExt (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ u) x := by
      intro x hx
      have hh := ((h ω).ownExt_props hu (hint ω u hu x hx).1).1
      exact hh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    rw [← hdκ ω, ← hdr ω]
    exact (sdata ω).abs_normEll_le_of_interval_scale (hL₀.trans (le_max_left _ _)) (le_max_left _ _)
      (convex_uIcc _ _) (fun x hx => (hdif x hx).hasDerivAt.real_of_complex.differentiableAt.differentiableWithinAt)
      (fun x hx => (hint ω u hu x hx).2) (fun x hx => ((sdata ω).deriv_F_zero (hdif x hx)).symm)
      (hWI ω u hu) (hVI ω u hu) (FrzData.inScale_mono (hremote ω u hu).A21 (le_max_right _ _))
      ((hremote ω u hu).logF.trans (le_max_right _ _))
      (fun m => FrzData.inScale_mono ((hremote ω u hu).mark m) (le_max_right _ _))
      (FrzData.inScale_mono (hremote ω u hu).driver (le_max_right _ _))
  exact integral_mul_seed_norm_stopped_sub_eq_zero 𝓕 hκ rr hB hBc hDm hDc hdW hdκ hdr hdφ hdζ hT
    (fun ω => NNReal.coe_pos.1 (h ω).pos) hTm hr₀ ha₀ hr h hv₀
    (fun ω => (hd9ω ω).d9.clr) (fun ω u hu => by
      change a₀ ≤ frzA (sdata ω).W (sdata ω).W' (sdata ω).a (sdata ω).φ 1 u
      rw [hdφ ω]
      exact (hd9ω ω).d9.A1 u hu)
    (fun ω m u hu => (hint ω u hu _ (hVI ω u hu m)).1)
    (fun ω u hu => (hrates ω u (Ioc_subset_Icc_self hu)).1.mono Ioc_subset_Icc_self)
    (fun ω u hu => (hrates ω u (Ioc_subset_Icc_self hu)).2.mono Ioc_subset_Icc_self)
    (fun ω m u hu => (hseed ω m).hasDerivWithinAt_pos (h ω).cont hu)
    (fun ω m => (hseed ω m).cont) hD hVm hV₀m hG₀m
    (fun ω => (hreg ω).2) hgn (fun ω => (hreg ω).1) hK hst hξ hξb

end InteractingSLE.ZhanGT4

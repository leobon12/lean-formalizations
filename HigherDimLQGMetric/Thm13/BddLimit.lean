import HigherDimLQGMetric.Thm13.WeylPatch

/-! Turning Lemma 3.6's ballwise uniform limit into a continuous-map limit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

/-- Uniform convergence on all centered compact ball squares implies
convergence in the compact-open topology. -/
theorem l8_tendsto_contMap_of_balls
    (F : ℕ → C(Rd d × Rd d, ℝ)) (G : C(Rd d × Rd d, ℝ))
    (h : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(F n)) ⇑G atTop
      (Metric.closedBall (0 : Rd d) R ×ˢ Metric.closedBall (0 : Rd d) R)) :
    Tendsto F atTop (𝓝 G) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro K hK
  obtain ⟨R₁, hR₁⟩ := (hK.image continuous_fst).isBounded.subset_closedBall
    (0 : Rd d)
  obtain ⟨R₂, hR₂⟩ := (hK.image continuous_snd).isBounded.subset_closedBall
    (0 : Rd d)
  let R : ℝ := max (max R₁ R₂) 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right (max R₁ R₂) 0]
  have hsub : K ⊆ Metric.closedBall (0 : Rd d) R ×ˢ
      Metric.closedBall (0 : Rd d) R := by
    intro p hp
    have h1 := hR₁ ⟨p, hp, rfl⟩
    have h2 := hR₂ ⟨p, hp, rfl⟩
    constructor
    · rw [Metric.mem_closedBall] at h1 ⊢
      dsimp [R]
      linarith [le_max_left R₁ R₂, le_max_left (max R₁ R₂) 0]
    · rw [Metric.mem_closedBall] at h2 ⊢
      dsimp [R]
      linarith [le_max_right R₁ R₂, le_max_left (max R₁ R₂) 0]
  exact (h R hR).mono hsub

/-- The bundled truncated LFPP metric evaluates to the real expression in
the conclusion of Lemma 3.6. -/
theorem l8_truncScaledMetric_apply (hd : 2 ≤ d)
    (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    {ε : ℝ} (hε : 0 < ε) (g : DistRd d) (p : Rd d × Rd d) :
    (l8_truncScaledMetric hd hκ ξ hε g).1 p =
      (aEps κ ξ ε)⁻¹ * fieldLfpp ξ (truncMollify κ ε g) p := by
  rw [l8_truncScaledMetric, ContMetric.smul_apply, fieldLfppMetric_apply]
  rfl

/-- The pointwise conclusion of `l6c_lemma36_trunc` yields exactly the
bounded-perturbation limit required by `l8_patch_addFun_eq_weyl_of_bounded_limits`. -/
theorem l8_bounded_limits_of_lemma36_event
    (hd : 2 ≤ d) (hκ : HigherDimLFPP.IsLFPPKernel κ) (ξ : ℝ)
    (εs : ℕ → ℝ) (hεs : ∀ n, 0 < εs n)
    (g : DistRd d) (D : ContMetric d) (hD : D.IsLength)
    (h36 : ∀ (fn : ℕ → C(Rd d, ℝ)) (f : C(Rd d, ℝ)) (M : ℝ),
      (∀ n z, |fn n z| ≤ M) →
      (∀ R : ℝ, 0 < R →
        TendstoUniformlyOn (fun n => ⇑(fn n)) ⇑f atTop
          (Metric.closedBall (0 : Rd d) R)) →
      ∀ R : ℝ, 0 < R →
        TendstoUniformlyOn
          (fun n (p : Rd d × Rd d) =>
            (aEps κ ξ (εs n))⁻¹ *
              fieldLfpp ξ (truncMollify κ (εs n) (addFun g (fn n))) p)
          (fun p => (weylScale ξ f D p.1 p.2).toReal)
          atTop (Metric.closedBall (0 : Rd d) R ×ˢ
            Metric.closedBall (0 : Rd d) R)) :
    ∀ f' : C(Rd d, ℝ), (∃ M : ℝ, ∀ x, |f' x| ≤ M) →
      Tendsto (fun n =>
        (l8_truncScaledMetric hd hκ ξ (hεs n) (addFun g f')).1)
        atTop (𝓝 (weylMetric ξ f' D hD).1) := by
  intro f' ⟨M, hM⟩
  apply l8_tendsto_contMap_of_balls
  intro R hR
  convert h36 (fun _ => f') f' M (fun n z => hM z)
      (fun R hR => by
        rw [Metric.tendstoUniformlyOn_iff]
        intro η hη
        exact Eventually.of_forall fun _ x _ => by simpa using hη)
      R hR using 1
  · funext n p
    exact (l8_truncScaledMetric_apply hd hκ ξ (hεs n) (addFun g f') p).symm
  · funext p
    exact (weylMetric_apply hD p).symm

end HigherDimLQGMetric

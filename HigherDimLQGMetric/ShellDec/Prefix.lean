import HigherDimLQGMetric.ShellDec.Countable
import Mathlib.Probability.Martingale.Convergence

/-!
# Finite-prefix filtration of a countable coordinate map
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HigherDimLQGMetric

@[instance_reducible] private def shellPrefixSigma {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) :
    MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (k : Fin n) => X k ω) MeasurableSpace.pi

private theorem shellPrefixSigma_mono {Ω : Type*} (X : ℕ → Ω → ℝ) :
    Monotone (shellPrefixSigma X) := by
  intro n m hnm
  have hm : Measurable[shellPrefixSigma X m]
      (fun ω (k : Fin n) => X k ω) := by
    refine (@measurable_pi_iff _ _ _ (shellPrefixSigma X m) _ _).2 fun k => ?_
    have hsrc : Measurable[shellPrefixSigma X m]
        (fun ω (j : Fin m) => X j ω) := Measurable.of_comap_le le_rfl
    have hk : (k : ℕ) < m := lt_of_lt_of_le k.isLt hnm
    exact (measurable_pi_apply (⟨k, hk⟩ : Fin m)).comp hsrc
  exact hm.comap_le

private def shellPrefixFiltration {Ω : Type*} (X : ℕ → Ω → ℝ) :
    Filtration ℕ (MeasurableSpace.comap
      (fun ω (k : ℕ) => X k ω) MeasurableSpace.pi) where
  seq := shellPrefixSigma X
  mono' := shellPrefixSigma_mono X
  le' n := by
    have hm : Measurable[MeasurableSpace.comap
        (fun ω (k : ℕ) => X k ω) MeasurableSpace.pi]
        (fun ω (k : Fin n) => X k ω) := by
      refine (@measurable_pi_iff _ _ _
        (MeasurableSpace.comap (fun ω (k : ℕ) => X k ω) MeasurableSpace.pi)
        _ _).2 fun k => ?_
      have hsrc : Measurable[MeasurableSpace.comap
          (fun ω (k : ℕ) => X k ω) MeasurableSpace.pi]
          (fun ω (j : ℕ) => X j ω) := Measurable.of_comap_le le_rfl
      exact (measurable_pi_apply (k : ℕ)).comp hsrc
    exact hm.comap_le

private theorem shellPrefixFiltration_iSup {Ω : Type*} (X : ℕ → Ω → ℝ) :
    (⨆ n, shellPrefixFiltration X n) =
      MeasurableSpace.comap (fun ω (k : ℕ) => X k ω)
        MeasurableSpace.pi := by
  apply le_antisymm
  · exact iSup_le fun n => (shellPrefixFiltration X).le n
  · have hm : Measurable[⨆ n, shellPrefixFiltration X n]
        (fun ω (k : ℕ) => X k ω) := by
      refine (@measurable_pi_iff _ _ _ (⨆ n, shellPrefixFiltration X n)
        _ _).2 fun k => ?_
      have hsrc : Measurable[shellPrefixFiltration X (k + 1)]
          (fun ω (j : Fin (k + 1)) => X j ω) :=
        Measurable.of_comap_le le_rfl
      have hk : Measurable[shellPrefixFiltration X (k + 1)]
          (fun ω => X k ω) :=
        (measurable_pi_apply (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))).comp hsrc
      exact hk.mono (le_iSup (fun n => shellPrefixFiltration X n) (k + 1)) le_rfl
    exact hm.comap_le

private def shellClip (x : ℝ) : ℝ := max 0 (min 1 x)

private theorem shellClip_bounds (x : ℝ) :
    0 ≤ shellClip x ∧ shellClip x ≤ 1 := by
  simp only [shellClip]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem shellClip_eq (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    shellClip x = x := by
  simp [shellClip, min_eq_right hx1, max_eq_right hx0]

private theorem shellClip_continuous : Continuous shellClip :=
  continuous_const.max (continuous_const.min continuous_id)

/-- The bounded conditional expectations of a function of countably many
coordinates factor through finite prefixes and converge almost surely. -/
theorem shellBounded_martingale_factor {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ k, Measurable (X k))
    (F : Ω → ℝ)
    (hFm : Measurable[MeasurableSpace.comap
      (fun ω (k : ℕ) => X k ω) MeasurableSpace.pi] F)
    (hF0 : ∀ ω, 0 ≤ F ω) (hF1 : ∀ ω, F ω ≤ 1) :
    ∃ g : (m : ℕ) → (Fin m → ℝ) → ℝ,
      (∀ m, Measurable (g m)) ∧
      (∀ m v, 0 ≤ g m v ∧ g m v ≤ 1) ∧
      ∀ᵐ ω ∂P, Tendsto
        (fun m => g m (fun k : Fin m => X k ω)) atTop (𝓝 (F ω)) := by
  let m0 : MeasurableSpace Ω := MeasurableSpace.comap
    (fun ω (k : ℕ) => X k ω) MeasurableSpace.pi
  have hm0 : m0 ≤ mΩ := by
    have hXfull : @Measurable Ω (ℕ → ℝ) mΩ MeasurableSpace.pi
        (fun ω (k : ℕ) => X k ω) :=
      (@measurable_pi_iff _ _ _ mΩ _ _).2 hXm
    exact hXfull.comap_le
  let ℱ : Filtration ℕ mΩ :=
    { seq := shellPrefixSigma X
      mono' := shellPrefixSigma_mono X
      le' := fun n => ((shellPrefixFiltration X).le n).trans hm0 }
  have hFambient : @Measurable Ω ℝ mΩ _ F := hFm.mono hm0 le_rfl
  have hFi : Integrable F P := by
    apply Integrable.of_bound (μ := P) hFambient.aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 ω)]
    exact hF1 ω
  have hFstrong : StronglyMeasurable[⨆ m, ℱ m] F := by
    rw [show (⨆ m, ℱ m) = m0 from shellPrefixFiltration_iSup X]
    exact hFm.stronglyMeasurable
  have hCE_lim : ∀ᵐ ω ∂P, Tendsto (fun m => (P[F | ℱ m]) ω) atTop (𝓝 (F ω)) :=
    MeasureTheory.Integrable.tendsto_ae_condExp (m0 := mΩ) (μ := P)
      (ℱ := ℱ) (g := F) hFi hFstrong
  have hex (m : ℕ) : ∃ gm : (Fin m → ℝ) → ℝ,
      Measurable gm ∧ (∀ v, 0 ≤ gm v ∧ gm v ≤ 1) ∧
      (fun ω => gm (fun k : Fin m => X k ω)) =
        fun ω => shellClip (P[F | ℱ m] ω) := by
    have hCE : Measurable[ℱ m] (P[F | ℱ m]) :=
      stronglyMeasurable_condExp.measurable
    have hG : Measurable[ℱ m] (fun ω => shellClip (P[F | ℱ m] ω)) :=
      shellClip_continuous.measurable.comp hCE
    have hG' : Measurable[shellPrefixSigma X m]
        (fun ω => shellClip (P[F | ℱ m] ω)) := hG
    obtain ⟨g, hgm, hgeq⟩ := hG'.exists_eq_measurable_comp
    refine ⟨fun v => shellClip (g v), shellClip_continuous.measurable.comp hgm,
      fun v => shellClip_bounds _, ?_⟩
    funext ω
    have hgo : shellClip (P[F | ℱ m] ω) =
        g (fun k : Fin m => X k ω) := by
      simpa only [Function.comp_apply] using congrFun hgeq ω
    change shellClip (g (fun k : Fin m => X k ω)) =
      shellClip (P[F | ℱ m] ω)
    rw [← hgo]
    exact shellClip_eq _ (shellClip_bounds _).1 (shellClip_bounds _).2
  choose g hgm hgb hgeq using hex
  refine ⟨g, hgm, hgb, ?_⟩
  filter_upwards [hCE_lim] with ω hω
  have hc := shellClip_continuous.continuousAt.tendsto.comp hω
  have hlimit : Tendsto (fun m => shellClip (P[F | ℱ m] ω)) atTop
      (𝓝 (shellClip (F ω))) := hc
  rw [shellClip_eq (F ω) (hF0 ω) (hF1 ω)] at hlimit
  exact hlimit.congr' (Eventually.of_forall fun m =>
    (congrFun (hgeq m) ω).symm)

end HigherDimLQGMetric

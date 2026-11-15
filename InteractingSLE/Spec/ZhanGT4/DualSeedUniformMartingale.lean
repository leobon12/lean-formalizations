/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformBound
import InteractingSLE.Spec.ZhanGT4.DualSeedLimitVersions
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformLimit
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformMeas

/-!
# The normalized seeded martingale after removal of both cutoffs

Packet PROVE-ZHAN-GT4-A22. Continuous adapted stopped versions are constructed
from alive-event measurability. A21 gives the band identities, and A22's
bounded-convergence lemmas remove the band and positive-time restrictions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (IsForwardSol fwdMap)

namespace SeedData

/-- The band family's nonvanishing discharges all collision hypotheses of
the positive-time normalized-log identity. -/
theorem normEll_eq_ell_of_gapVal_ne {n : ℕ} (d : SeedData n) {t : ℝ}
    (hne : ∀ i, d.gapVal i t ≠ 0) : d.normEll t = d.ell t (d.W t) := by
  have h0 : d.A 0 t - d.A20 t ≠ 0 := by
    intro he
    apply hne (Sum.inl 0)
    simp only [gapVal, Matrix.cons_val_zero]
    linarith only [he]
  have hv0 : d.W t - d.V₀ t ≠ 0 := by
    intro he
    apply hne (Sum.inl 2)
    simp [gapVal]
    linarith only [he]
  apply d.normEll_eq_ell h0 hv0
  · intro m he
    exact hne (Sum.inr (Sum.inl (1, m))) (by simpa [gapVal] using he)
  · intro m he
    exact hne (Sum.inr (Sum.inl (4, m))) (by simpa [gapVal] using he)
  · intro m he
    exact hne (Sum.inr (Sum.inl (3, m))) (by simp [gapVal, he])
  · intro m he
    exact hne (Sum.inr (Sum.inl (0, m))) (by simp [gapVal, he])
  · intro m k hmk he
    exact hne (Sum.inr (Sum.inr (1, m, k))) (by simp [gapVal, hmk.ne, he])
  · intro m k hmk he
    exact hne (Sum.inr (Sum.inr (0, m, k))) (by simp [gapVal, hmk.ne, he])

end SeedData

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The seeded martingale with both cutoffs removed.** The analytic input
is a uniform bound for the normalized log, not a bound for the singular
individual seed gaps. All process regularity and ODE inputs are explicit.
No band versions, band exits, or band martingale hypotheses are inputs. -/
theorem integral_mul_seed_norm_stopped_sub_eq_zero
    (𝓕 : Filtration ℝ≥0 mΩ) {P : Measure Ω} [IsProbabilityMeasure P]
    {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (rr : Fin n → ℝ)
    {B D : ℝ≥0 → Ω → ℝ} (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω))
    (hDm : ∀ u, Measurable[𝓕 u] (D u)) (hDc : ∀ ω, Continuous (D · ω))
    {d : Ω → SeedData n}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hdκ : ∀ ω, (d ω).κ = κ) (hdr : ∀ ω, (d ω).r = rr)
    {A : Set ℂ} {φ : ℂ → ℂ} {ζ₀ : ℝ}
    (hdφ : ∀ ω, (d ω).φ = φ) (hdζ : ∀ ω, (d ω).ζ₀ = ζ₀)
    {T : Ω → ℝ≥0} (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hTpos : ∀ ω, 0 < T ω) {Tm : ℝ} (hTm : ∀ ω, (T ω : ℝ) ≤ Tm)
    {r a₀ ρm : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hρm : 0 < ρm)
    (h : ∀ ω, OwnData (d ω).W A (d ω).φ (T ω) (d ω).a (d ω).W')
    (hv₀ : ∀ ω, ∃ v₀ : ℝ → ℂ,
      IsForwardSol (d ω).W' (d ω).ζ₀ ((d ω).a (T ω)) v₀)
    (hclr : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).W t : ℂ) r)
        ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hA1 : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → a₀ ≤ (d ω).A 1 t)
    (hmclr : ∀ ω m t, t ∈ Icc (0 : ℝ) (T ω) →
      Disjoint (ball ((d ω).V m t : ℂ) ρm)
        ((fun z => fwdMap (d ω).W t z + (d ω).W t) '' A))
    (hV₀ : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (d ω).V₀ (2 / ((d ω).V₀ t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hG₀ : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (d ω).G₀
        (-2 * (d ω).G₀ t / ((d ω).V₀ t - (d ω).W t) ^ 2) (Ioc 0 (T ω)) t)
    (hV : ∀ ω m t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt ((d ω).V m) (2 / ((d ω).V m t - (d ω).W t)) (Ioc 0 (T ω)) t)
    (hVc : ∀ ω m, ContinuousOn ((d ω).V m) (Icc 0 (T ω)))
    (hD : ∀ ω t, t ∈ Ioc (0 : ℝ) (T ω) →
      HasDerivWithinAt (fun s : ℝ => D s.toNNReal ω)
        ((d ω).drift t) (Ioc 0 (T ω)) t)
    (hVm : ∀ (q : ℝ≥0) m,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V m q))
    (hV₀m : ∀ q : ℝ≥0,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).V₀ q))
    (hG₀m : ∀ q : ℝ≥0,
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).G₀ q))
    (hgc : ∀ ω i, ContinuousOn ((d ω).gapVal i) (Icc 0 (T ω)))
    (hgn : ∀ ω i t, t ∈ Ioc (0 : ℝ) (T ω) → (d ω).gapVal i t ≠ 0)
    (hnc : ∀ ω, ContinuousOn (d ω).normEll (Icc 0 (T ω)))
    {K : ℝ} (hK : ∀ ω t, t ∈ Icc (0 : ℝ) (T ω) → |(d ω).normEll t| ≤ K)
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ}
    (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (Real.exp ((d ω).normEll (min t (T ω)))
      - Real.exp ((d ω).normEll (min s (T ω)))) ∂P = 0 := by
  let X : ℝ≥0 → Ω → ℝ := fun u ω => Real.sqrt κ * B u ω + D u ω
  have hXm : ∀ u, Measurable[𝓕 u] (X u) := fun u =>
    ((hB.2.1 u).const_mul _).add (hDm u)
  have hXc : ∀ ω, Continuous (X · ω) := fun ω =>
    ((hBc ω).const_mul _).add (hDc ω)
  have hdX : ∀ ω, (d ω).W = Ito.rpath (X · ω) := by
    intro ω
    rw [hdW ω, driftDriver_eq_rpath]
  have hmeas : ∀ q : ℝ≥0,
      (∀ i, Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).gapVal i q)) ∧
      Measurable[𝓕 q] ({ω | q ≤ T ω}.indicator fun ω => (d ω).normEll q) := by
    intro q
    exact measurable_seed_norm_and_gaps hXm hXc hdX hdφ hdζ q
      (measurableSet_ge_of_isStoppingTime hT q)
      (fun ω hω => NNReal.coe_le_coe.2 hω)
      (fun ω _ => h ω) (fun ω _ => hv₀ ω)
      (fun ω hω m => ⟨ρm, hρm, hmclr ω m q ⟨q.coe_nonneg, NNReal.coe_le_coe.2 hω⟩⟩)
      (hVm q) hdκ hdr (hV₀m q) (hG₀m q)
  have hgm := fun q i => (hmeas q).1 i
  have hnm := fun q => (hmeas q).2
  let M : ℝ≥0 → Ω → ℝ := fun u ω => Real.exp ((d ω).normEll ((min u (T ω) : ℝ≥0) : ℝ))
  have hMm : ∀ u, Measurable[𝓕 u] (M u) := fun u =>
    (measurable_stopped_of_indicator hT hnm hnc u).exp
  have hMc : ∀ ω, Continuous (M · ω) := fun ω =>
    Real.continuous_exp.comp (continuous_stopped_of_continuousOn hnc ω)
  have hMb : ∀ u ω, |M u ω| ≤ Real.exp K := by
    intro u ω
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans
      (hK ω _ ⟨NNReal.coe_nonneg _, NNReal.coe_le_coe.2 (min_le_right _ _)⟩))
  have hMcap : ∀ u ω, M (min u (T ω)) ω = M u ω := by
    intro u ω
    simp only [M, min_assoc, min_self]
  have hTm0 : Measurable T := by
    have hm := (hT.measurable.mono hT.measurableSpace_le le_rfl).untopA
    simpa only [WithTop.untopA, WithTop.untopD_coe] using hm
  obtain ⟨Y, hYc, hYm, hYv⟩ := exists_continuous_adapted_stopped_versions hT
    (fun i q => hgm q i) (fun i ω => hgc ω i)
  have hpos : ∀ s t : ℝ≥0, 0 < s → s ≤ t → ∀ ξ : Ω → ℝ,
      Measurable[𝓕 s] ξ → (∀ ω, |ξ ω| ≤ 1) →
      ∫ ω, ξ ω * (M t ω - M s ω) ∂P = 0 := by
    intro s t hs hst ξ hξ hξb
    have hξm : Measurable ξ := hξ.mono (𝓕.le s) le_rfl
    apply integral_mul_sub_eq_zero_of_pos_horizon (Real.exp_pos K).le
      (fun u => ((hMm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable)
      hMb hTm0 hTpos hs hξm hξb
    intro ε hε hεs
    let R : ℝ≥0 := Tm.toNNReal
    have hTR : ∀ ω, T ω ≤ ε + R := by
      intro ω
      have hle : T ω ≤ R := by
        rw [← NNReal.coe_le_coe]
        exact (hTm ω).trans (Real.le_coe_toNNReal Tm)
      exact hle.trans (by exact le_add_of_nonneg_left (zero_le (a := ε)))
    have hne : ∀ ω, ε ≤ T ω → ∀ i u, ε ≤ u → u ≤ T ω → Y i u ω ≠ 0 := by
      intro ω hεT i u hεu hu
      rw [hYv i ω u hu]
      exact hgn ω i u ⟨NNReal.coe_pos.2 (hε.trans_le hεu), NNReal.coe_le_coe.2 hu⟩
    suffices hind : ∫ ω, {ω | ε ≤ T ω}.indicator ξ ω *
        (M (min t (T ω)) ω - M (min s (T ω)) ω) ∂P = 0 by
      simpa only [hMcap] using hind
    apply integral_indicator_mul_stopped_sub_eq_zero_of_nat_band
      (Y := Y) (M := M) (ε := ε) (R := R) (T := T) (s := s) (t := t)
      (Real.exp_pos K).le hYc hYm hT hTR hne hMm hMc
      (fun ω u _ => hMb u ω) hξm hξb
    intro k
    have subε : ∀ ω, Icc (ε : ℝ) (T ω) ⊆ Ioc (0 : ℝ) (T ω) :=
      fun ω u hu => ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2⟩
    have hk := integral_indicator_mul_seed_band_eq_zero 𝓕 hκ rr hB hBc hDm hDc
      hdW hdκ hdr hdφ hdζ hε hT hTm hr ha₀ hρm
      (fun ω _ => h ω) (fun ω _ => hv₀ ω)
      (fun ω _ => hclr ω) (fun ω _ => hA1 ω) (fun ω _ => hmclr ω)
      (fun ω _ u hu => (hV₀ ω u (subε ω hu)).mono (subε ω))
      (fun ω _ u hu => (hG₀ ω u (subε ω hu)).mono (subε ω))
      (fun ω _ m u hu => (hV ω m u (subε ω hu)).mono (subε ω))
      (fun ω _ => hVc ω)
      (fun ω _ u hu => (hD ω u (subε ω hu)).mono (subε ω))
      (fun q m _ => hVm q m) (fun q _ => hV₀m q) (fun q _ => hG₀m q)
      hYc hYm (fun ω i u _ hu => hYv i ω u hu) k R hεs hst hξ hξb
    convert hk using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
    swap
    · simp only [indicator_of_notMem hω, zero_mul]
    rw [indicator_of_mem hω]
    let S := bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω
    have hST : S ≤ T ω := bandExit_le hω.1
    have hεS : ε ≤ S := le_bandExit ω
    have heq : ∀ u : ℝ≥0, ε ≤ u →
        M (min u S) ω = Real.exp ((d ω).ell (min u S)
          (driftDriver (Real.sqrt κ) B D ω (min u S))) := by
      intro u hεu
      have huT := (min_le_right u S).trans hST
      have hu0 : 0 < min u S := hε.trans_le (le_min hεu hεS)
      have hn := (d ω).normEll_eq_ell_of_gapVal_ne
        (fun i => hgn ω i _ ⟨NNReal.coe_pos.2 hu0, NNReal.coe_le_coe.2 huT⟩)
      dsimp only [M]
      rw [min_eq_left huT, hn, hdW ω]
      simp only [NNReal.coe_min]
    rw [heq t (hεs.trans hst), heq s hεs]
  exact integral_mul_sub_eq_zero_of_pos
    (fun u => ((hMm u).mono (𝓕.le u) le_rfl).aestronglyMeasurable) hMb
    (fun ω => (hMc ω).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    hpos hst hξ hξb

end InteractingSLE.ZhanGT4

import SupercriticalLQGUniqueness.B2.DG20Conc.ScaledUnion
import LQGMetric.Topo.RectCross
import LQGMetric.Papers.DDDF.P18Geom

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

 

theorem exists_positive_infDist_gap
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hAB : Disjoint A B) :
    ∃ d : ℝ, 0 < d ∧ ∀ b ∈ B, d ≤ infDist b A := by
  have hpos : ∀ b ∈ B, 0 < infDist b A := by
    intro b hb
    have hbA : b ∉ A := fun hba => (disjoint_left.mp hAB) hba hb
    exact (hA.isClosed.notMem_iff_infDist_pos hAn).mp hbA
  exact hB.exists_forall_le' (continuous_infDist_pt A).continuousOn hpos

 
theorem infDist_shell_subpath_of_gap
    {A B : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hgap : ∀ b ∈ B, d ≤ infDist b A)
    {q : ℝ → ℂ} (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq0 : q 0 ∈ A) (hq1 : q 1 ∈ B) :
    ∃ s t : ℝ,
      0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧
      infDist (q s) A = d / 3 ∧
      infDist (q t) A = 2 * d / 3 ∧
      ∀ u ∈ Icc s t, infDist (q u) A ∈ Icc (d / 3) (2 * d / 3) := by
  let f : ℝ → ℝ := fun u => infDist (q u) A
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (continuous_infDist_pt A).comp_continuousOn hq
  have hf0 : f 0 ≤ d / 3 := by
    dsimp [f]
    rw [infDist_zero_of_mem hq0]
    positivity
  have hf1 : 2 * d / 3 ≤ f 1 := by
    exact (by linarith : 2 * d / 3 ≤ d).trans (hgap _ hq1)
  have hlevels : d / 3 ≤ 2 * d / 3 := by linarith
  obtain ⟨s, t, hs, hst, ht, hfs, hft, hmid⟩ :=
    LQGMetric.RectCross.exists_sub_crossing zero_le_one hf hlevels hf0 hf1
  exact ⟨s, t, hs, hst, ht, hfs, hft, hmid⟩

 


theorem exists_infDist_shell_subpath
    {A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hAB : Disjoint A B)
    {q : ℝ → ℂ} (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hq0 : q 0 ∈ A) (hq1 : q 1 ∈ B) :
    ∃ d : ℝ, 0 < d ∧ ∃ s t : ℝ,
      0 ≤ s ∧ s ≤ t ∧ t ≤ 1 ∧
      infDist (q s) A = d / 3 ∧
      infDist (q t) A = 2 * d / 3 ∧
      ∀ u ∈ Icc s t, infDist (q u) A ∈ Icc (d / 3) (2 * d / 3) := by
  obtain ⟨d, hd, hgap⟩ := exists_positive_infDist_gap hA hB hAn hAB
  exact ⟨d, hd, infDist_shell_subpath_of_gap hd hgap hq hq0 hq1⟩

 


theorem crossLenIn_subcross_le_pathLen
    {U A B V E F : Set ℂ} {q : ℝ → ℂ}
    (hq : LQGMetric.DDDF.AdmPath U A B q)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hV : ∀ u ∈ Icc s t, q u ∈ V)
    (hE : q s ∈ E) (hF : q t ∈ F)
    {ξ : ℝ} {f : ℂ → ℝ} :
    LQGMetric.DDDF.crossLenIn ξ f (U ∩ V) E F ≤
      LQGMetric.lfppLen ξ f q := by
  rcases hq with ⟨z, hz, w, hw, hqp, hqU⟩
  have hK : ∀ u ∈ Icc s t, q u ∈ U ∩ V := by
    intro u hu
    exact ⟨hqU u ⟨hs.trans hu.1, hu.2.trans ht⟩, hV u hu⟩
  calc
    LQGMetric.DDDF.crossLenIn ξ f (U ∩ V) E F
        ≤ ∫⁻ u in Ioo s t, LQGMetric.LFPP.lenDens ξ f q u :=
          LQGMetric.DDDF.crossLenIn_le_setLIntegral_Ioo hqp hs hst ht hK hE hF
    _ ≤ ∫⁻ u in Icc (0 : ℝ) 1, LQGMetric.LFPP.lenDens ξ f q u := by
      apply lintegral_mono_set
      intro u hu
      exact ⟨hs.trans hu.1.le, hu.2.le.trans ht⟩
    _ = LQGMetric.lfppLen ξ f q :=
      (LQGMetric.LFPP.lfppLen_eq _ _ _).symm

 


theorem crossLenIn_mono_domain
    {V U A B : Set ℂ} (hVU : V ⊆ U)
    {ξ : ℝ} {f : ℂ → ℝ} :
    LQGMetric.DDDF.crossLenIn ξ f U A B ≤
      LQGMetric.DDDF.crossLenIn ξ f V A B := by
  apply LQGMetric.DDDF.le_crossLenIn
  intro q hq
  obtain ⟨a, ha, b, hb, hqp, hqV⟩ := hq
  exact LQGMetric.DDDF.crossLenIn_le_lfppLen
    ⟨a, ha, b, hb, hqp, fun t ht => hVU (hqV t ht)⟩

 


theorem shell_crossLen_le_pathLen_of_gap
    {U A B : Set ℂ} {d : ℝ} (hd : 0 < d)
    (hgap : ∀ b ∈ B, d ≤ infDist b A)
    {q : ℝ → ℂ} (hq : LQGMetric.DDDF.AdmPath U A B q)
    {ξ : ℝ} {f : ℂ → ℝ} :
    LQGMetric.DDDF.crossLenIn ξ f
        (U ∩ {z | infDist z A ∈ Icc (d / 3) (2 * d / 3)})
        {z | infDist z A = d / 3}
        {z | infDist z A = 2 * d / 3} ≤
        LQGMetric.lfppLen ξ f q := by
  rcases hq with ⟨z, hz, w, hw, hqp, hqU⟩
  have hq0 : q 0 ∈ A := hqp.source.symm ▸ hz
  have hq1 : q 1 ∈ B := hqp.target.symm ▸ hw
  obtain ⟨s, t, hs, hst, ht, hfs, hft, hmid⟩ :=
    infDist_shell_subpath_of_gap hd hgap hqp.continuousOn hq0 hq1
  exact crossLenIn_subcross_le_pathLen
    ⟨z, hz, w, hw, hqp, hqU⟩ hs hst ht hmid hfs hft

 


theorem exists_shell_crossLen_le_crossLenIn
    {U A B : Set ℂ} (hA : IsCompact A) (hB : IsCompact B)
    (hAn : A.Nonempty) (hAB : Disjoint A B)
    {ξ : ℝ} {f : ℂ → ℝ} :
    ∃ d : ℝ, 0 < d ∧
      LQGMetric.DDDF.crossLenIn ξ f
        (U ∩ {z | infDist z A ∈ Icc (d / 3) (2 * d / 3)})
        {z | infDist z A = d / 3}
        {z | infDist z A = 2 * d / 3} ≤
        LQGMetric.DDDF.crossLenIn ξ f U A B := by
  obtain ⟨d, hd, hgap⟩ := exists_positive_infDist_gap hA hB hAn hAB
  refine ⟨d, hd, LQGMetric.DDDF.le_crossLenIn fun q hq => ?_⟩
  exact shell_crossLen_le_pathLen_of_gap hd hgap hq

end SupercriticalLQGUniqueness.B2.DG20Conc

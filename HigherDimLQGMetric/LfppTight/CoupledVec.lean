import HigherDimLQGMetric.LfppTight.CenteredWN

/-!
# Splitting the centered infinite band at unit scale

For `0 < ε < 1`, the white-noise vector of the centered field is the
finite-band point vector, minus the finite-band spherical mean vector,
plus a fixed centered high-band vector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd bandVecM)

/-- The scale-one boundary has zero Lebesgue measure, so the two versions of
the high-band vector agree in `L²`. -/
theorem l6a_high_band_vec_eq {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) (x : Rd d) :
    bandVecM κ (Ici 1) (Measure.dirac x) (unitSphereProb d) =
      bandVecM κ (Ioi 1) (Measure.dirac x) (unitSphereProb d) := by
  have hp : HigherDimLFPP.IsPairable κ (Ioi (1 / 2 : ℝ))
      (Measure.dirac x) (unitSphereProb d) :=
    l6a_isPairable_centeredIoi hd hκ (by norm_num) x
  have hp1 : HigherDimLFPP.IsPairable κ (Ici 1)
      (Measure.dirac x) (unitSphereProb d) :=
    hp.mono_set measurableSet_Ici (fun t ht => by change (1 : ℝ) ≤ t at ht; change (1 / 2 : ℝ) < t; linarith)
  have hp2 : HigherDimLFPP.IsPairable κ (Ioi 1)
      (Measure.dirac x) (unitSphereProb d) :=
    l6a_isPairable_centeredIoi hd hκ one_pos x
  apply HigherDimLFPP.bandVecM_congr hp1 hp2
  filter_upwards [HigherDimLFPP.ae_fst_ne (d := d) 1] with p hpne
  simp only [Pi.sub_apply, HigherDimLFPP.bandFun_apply]
  by_cases ht : 1 < p.1
  · have ht1 : p.1 ∈ Ici (1 : ℝ) := ht.le
    have ht2 : p.1 ∈ Ioi (1 : ℝ) := ht
    simp only [indicator_of_mem ht1, indicator_of_mem ht2]
  · have hlt : p.1 < 1 := lt_of_le_of_ne (le_of_not_gt ht) hpne
    have ht1 : p.1 ∉ Ici (1 : ℝ) := not_le_of_gt hlt
    have ht2 : p.1 ∉ Ioi (1 : ℝ) := not_lt_of_ge hlt.le
    simp only [indicator_of_notMem ht1, indicator_of_notMem ht2]

theorem l6a_centered_split_vec {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (x : Rd d) :
    bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d) =
      bandVecM κ (Ioo ε 1) (Measure.dirac x) 0 -
      bandVecM κ (Ioo ε 1) (unitSphereProb d) 0 +
      bandVecM κ (Ici 1) (Measure.dirac x) (unitSphereProb d) := by
  letI : IsProbabilityMeasure (unitSphereProb d) :=
    isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  have hp : HigherDimLFPP.IsPairable κ (Ioi ε)
      (Measure.dirac x) (unitSphereProb d) :=
    l6a_isPairable_centeredIoi hd hκ hε.1 x
  have hb1 : HigherDimLFPP.IsPairable κ (Ioo ε 1) (Measure.dirac x) 0 :=
    HigherDimLFPP.isPairable_of_subset_Icc hκ measurableSet_Ioo hε.1
      (fun t ht => ⟨ht.1.le, ht.2.le⟩) _ _
  have hb2 : HigherDimLFPP.IsPairable κ (Ioo ε 1) (unitSphereProb d) 0 :=
    HigherDimLFPP.isPairable_of_subset_Icc hκ measurableSet_Ioo hε.1
      (fun t ht => ⟨ht.1.le, ht.2.le⟩) _ _
  have hs : Disjoint (Ioo ε 1) (Ici (1 : ℝ)) := by
    exact disjoint_left.mpr (fun t ht1 ht2 => (not_le_of_gt ht1.2) ht2)
  have hset : Ioo ε 1 ∪ Ici 1 = Ioi ε :=
    Ioo_union_Ici_eq_Ioi hε.2
  have hsum := HigherDimLFPP.bandVecM_union
    (κ := κ) measurableSet_Ioo measurableSet_Ici hs (hset ▸ hp)
  rw [hset, HigherDimLFPP.bandVecM_sub hb1 hb2] at hsum
  exact hsum

/-- Couple every real finite-band cutoff with a single continuous high-band
field. The scalar subtracted from the finite band is its white-noise sphere
mean vector; the pointwise stochastic integral is not needed for this split. -/
theorem l6a_exists_coupled_centered_version {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : HigherDimLFPP.WN d → Ω → ℝ} (hW : HigherDimLFPP.IsWhiteNoise P W)
    (G : ℝ → Rd d → Ω → ℝ)
    (hG : ∀ ε ∈ Ioo (0 : ℝ) 1, HigherDimLFPP.IsBandVersion P W κ ε 1 (G ε)) :
    ∃ Ψ : Rd d → Ω → ℝ,
      (∀ ω, Continuous fun x => Ψ x ω) ∧
      (∀ x, Measurable (Ψ x)) ∧
      (∀ x, Ψ x =ᵐ[P] W (bandVecM κ (Ici 1) (Measure.dirac x) (unitSphereProb d))) ∧
      ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ x : Rd d,
        (fun ω => G ε x ω - W (bandVecM κ (Ioo ε 1) (unitSphereProb d) 0) ω + Ψ x ω)
          =ᵐ[P] W (bandVecM κ (Ioi ε) (Measure.dirac x) (unitSphereProb d)) := by
  obtain ⟨Ψ, hΨc, hΨm, hΨeq⟩ :=
    l6a_exists_centeredIoi_version hd hκ one_pos hW
  have hΨhigh (x : Rd d) :
      Ψ x =ᵐ[P] W (bandVecM κ (Ici 1) (Measure.dirac x) (unitSphereProb d)) := by
    rw [l6a_high_band_vec_eq hd hκ x]
    exact hΨeq x
  refine ⟨Ψ, hΨc, hΨm, hΨhigh, ?_⟩
  intro ε hε x
  let v : HigherDimLFPP.WN d := bandVecM κ (Ioo ε 1) (Measure.dirac x) 0
  let m : HigherDimLFPP.WN d := bandVecM κ (Ioo ε 1) (unitSphereProb d) 0
  let vhi : HigherDimLFPP.WN d :=
    bandVecM κ (Ici 1) (Measure.dirac x) (unitSphereProb d)
  have hv : G ε x =ᵐ[P] W v := by
    change G ε x =ᵐ[P] W (bandVecM κ (Ioo ε 1) (Measure.dirac x) 0)
    rw [HigherDimLFPP.bandVecM_dirac_zero]
    exact (hG ε hε).ae_eq x
  have hsum := hW.add_ae (v - m) vhi
  have hsub := hW.sub_ae v m
  filter_upwards [hv, hΨhigh x, hsum, hsub] with ω hve hhi hadd hminus
  rw [l6a_centered_split_vec hd hκ hε x]
  change G ε x ω - W m ω + Ψ x ω = W ((v - m) + vhi) ω
  rw [hadd, hminus, hve, hhi]

end HigherDimLQGMetric

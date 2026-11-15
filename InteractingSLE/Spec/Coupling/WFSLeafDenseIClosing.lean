/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafDenseIGeometry

/-!
# Identifying dense-time limits with the closed conditional mean

Right continuity identifies intersections of filtrations along decreasing
times. The landed backward martingale theorem then identifies the reconstructed
value at every fixed time, without assuming any nondyadic version identity.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- A sequence approaching from the right is cofinal for a right-continuous
filtration. Monotonicity of the sequence is unnecessary for this identity. -/
theorem iInf_filtration_eq_of_tendsto_right
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (𝓓 : Filtration ℝ≥0 mΩ)
    [𝓓.IsRightContinuous] {q : ℕ → ℝ≥0} {t : ℝ≥0}
    (hq : ∀ n, t ≤ q n) (hlim : Tendsto q atTop (𝓝 t)) :
    (⨅ n, 𝓓 (q n)) = 𝓓 t := by
  apply le_antisymm
  · have hrc : 𝓓 t = ⨅ s > t, 𝓓 s := by
      calc
        𝓓 t = 𝓓.rightCont t :=
          (congrArg (fun F : Filtration ℝ≥0 mΩ => F t)
            (Filtration.IsRightContinuous.eq (𝓕 := 𝓓))).symm
        _ = _ := Filtration.rightCont_eq 𝓓 t
    rw [hrc]
    refine le_iInf fun s => le_iInf fun hs => ?_
    obtain ⟨n, hn⟩ := (hlim.eventually (Iio_mem_nhds hs)).exists
    exact (iInf_le (fun n => 𝓓 (q n)) n).trans (𝓓.mono hn.le)
  · exact le_iInf fun n => 𝓓.mono (hq n)

/-- The continuous dyadic reconstruction of a closed conditional mean has
its required fixed-time identity, by backward martingale convergence. -/
theorem ae_dyadicTimeLimit_eq_condExp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓓 : Filtration ℝ≥0 mΩ) [𝓓.IsRightContinuous] {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hlim : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ∃ c : ℝ,
      Tendsto (fun d : dyadicTimes => P[Z | 𝓓 d] ω)
        (comap (fun d : dyadicTimes => (d : ℝ≥0)) (𝓝 t)) (𝓝 c)) (t : ℝ≥0) :
    (fun ω => dyadicTimeLimit (fun s => P[Z | 𝓓 s] ω) t) =ᵐ[P] P[Z | 𝓓 t] := by
  obtain ⟨q, hqa, hq, hqt⟩ := dense_dyadicTimes.exists_seq_strictAnti_tendsto t
  have hG : Antitone (fun n => 𝓓 (q n)) := fun a b hab => 𝓓.mono (hqa.antitone hab)
  have hi := iInf_filtration_eq_of_tendsto_right 𝓓 (fun n => (hq n).1.le) hqt
  obtain ⟨ns, hns, he⟩ := InteractingSLE.Martingale.exists_seq_ae_tendsto_condExp_iInf
    (fun n => 𝓓.le (q n)) hG hZ
  rw [hi] at he
  filter_upwards [hlim, he] with ω hω heω
  have hc := continuous_dyadicTimeLimit (f := fun s => P[Z | 𝓓 s] ω) hω
  have hv : ∀ n, dyadicTimeLimit (fun s => P[Z | 𝓓 s] ω) (q n) = P[Z | 𝓓 (q n)] ω :=
    fun n => dyadicTimeLimit_eq_at (f := fun s => P[Z | 𝓓 s] ω) hω (hq n).2
  have ht := (hc.tendsto t).comp (hqt.comp hns.tendsto_atTop)
  dsimp only [Function.comp_def] at ht
  simp only [hv] at ht
  exact tendsto_nhds_unique ht heω

end InteractingSLE.WFS

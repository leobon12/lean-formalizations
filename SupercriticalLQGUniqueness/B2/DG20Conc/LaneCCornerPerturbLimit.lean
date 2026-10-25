import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCornerPerturbedMeet

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric Filter
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 

theorem laneC_inwardPerturb_meet_limit
    {α β : ℝ → ℂ}
    (hα : ContinuousOn α (Icc (0 : ℝ) 1))
    (hβ : ContinuousOn β (Icc (0 : ℝ) 1))
    (hinter : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ s ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
        laneCInwardPerturb β ε s = α u) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ u ∈ Icc (0 : ℝ) 1,
      β s = α u := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n ∧ ε n ≤ 1 := by
    dsimp [ε]
    constructor
    · positivity
    · have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      exact (div_le_iff₀ (by positivity)).2 (by simpa using hn)
  choose s hs u hu heq using
    (fun n : ℕ => hinter (ε n) (hε n).1 (hε n).2)
  let p : ℕ → ℝ × ℝ := fun n => (s n, u n)
  have hpmem (n : ℕ) :
      p n ∈ (Icc (0 : ℝ) 1) ×ˢ (Icc (0 : ℝ) 1) :=
    ⟨hs n, hu n⟩
  obtain ⟨q, hq, f, hf, hlim⟩ :=
    (isCompact_Icc.prod isCompact_Icc).tendsto_subseq hpmem
  have hslim : Tendsto (fun n => s (f n)) atTop (nhds q.1) := by
    have h := (continuous_fst.tendsto q).comp hlim
    simpa [p, Function.comp_def] using h
  have hulim : Tendsto (fun n => u (f n)) atTop (nhds q.2) := by
    have h := (continuous_snd.tendsto q).comp hlim
    simpa [p, Function.comp_def] using h
  have hεlim : Tendsto (fun n => ε (f n)) atTop (nhds (0 : ℝ)) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hf.tendsto_atTop
  have hswithin : Tendsto (fun n => s (f n)) atTop
      (nhdsWithin q.1 (Icc (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hslim, Eventually.of_forall (fun n => hs (f n))⟩
  have huwithin : Tendsto (fun n => u (f n)) atTop
      (nhdsWithin q.2 (Icc (0 : ℝ) 1)) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hulim, Eventually.of_forall (fun n => hu (f n))⟩
  have hβlim : Tendsto (fun n => β (s (f n))) atTop (nhds (β q.1)) :=
    (hβ.continuousWithinAt hq.1).tendsto.comp hswithin
  have hαlim : Tendsto (fun n => α (u (f n))) atTop (nhds (α q.2)) :=
    (hα.continuousWithinAt hq.2).tendsto.comp huwithin
  have hwlim : Tendsto
      (fun n => ε (f n) * s (f n) * (1 - s (f n)))
      atTop (nhds (0 : ℝ)) := by
    convert (hεlim.mul hslim).mul (tendsto_const_nhds.sub hslim) using 1 <;> ring
  have hwc : Tendsto
      (fun n => ((ε (f n) * s (f n) * (1 - s (f n))) : ℂ))
      atTop (nhds (0 : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp hwlim
  have hpertLim : Tendsto
      (fun n => laneCInwardPerturb β (ε (f n)) (s (f n)))
      atTop (nhds (β q.1)) := by
    have hc1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hcmid : Tendsto (fun _ : ℕ => laneCmid) atTop (nhds laneCmid) :=
      tendsto_const_nhds
    have h1 := (hc1.sub hwc).mul hβlim
    have h2 := hwc.mul hcmid
    have h := h1.add h2
    simpa only [laneCInwardPerturb, Complex.ofReal_mul,
      Complex.ofReal_sub, Complex.ofReal_one, one_mul, zero_mul,
      add_zero, sub_zero] using h
  have hpertEq : (fun n => laneCInwardPerturb β (ε (f n)) (s (f n))) =
      (fun n => α (u (f n))) := funext (fun n => heq (f n))
  have hαlim' : Tendsto
      (fun n => laneCInwardPerturb β (ε (f n)) (s (f n)))
      atTop (nhds (α q.2)) := by
    rw [hpertEq]
    exact hαlim
  exact ⟨q.1, hq.1, q.2, hq.2,
    tendsto_nhds_unique hpertLim hαlim'⟩

end SupercriticalLQGUniqueness.B2.DG20Conc

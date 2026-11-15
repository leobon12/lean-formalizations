/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.ReverseContactImgLevy
import InteractingSLE.Spec.Sec5.StagedRepEntr

/-!
# The pathwise clause of a killed stage: killed words solve the integrated equations

Packet PROVE-STAGED-REP2. The first clause of the killed stage law (`IsStageLawFarK`, ruling R78) is pathwise: the
piece solves Definition 2.1's integrated equations before its killing time, driven by its noise. For PROVE-PROP59-
PIECES' candidate pieces the noise is a free parameter; with the **recovered noise** `(W + ½ Σ ρ (V − V₀))/√κ` the
clause is a deterministic property of a killed word (`WangWu.ImgDrv.IsKilledWord`: the deterministic properties of
force images before the kill, strictly separated from the driver at positive times):

* `forceDefect_eq_zero_of_ne`: a force path that never meets the driver at positive times has no singular motion
  (the defect is constant on every `[ε, t]` and continuous at `0`);
* **`IsKilledWord.isWordEntrance_recNoise`**: every sample of a killed word is a word entrance driven by its recovered
  noise up to the kill (the continued systems of PROVE-WW-B16 at an exhausting sequence of times, no probability);
* **`IsKilledWord.isSLEPathUpTo_recNoise`**: the local integrated path (`Sec2.IsSLEPathUpTo`) up to the kill, when the
  start is not a threshold configuration (positive times are separated).

R48: nothing here uses Theorem 1.2/1.3 or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedRepLater

open WangWu WangWu.ImgDrv MartChar Sec7.PhaseSelAdapt Sec7.PhaseSelFull Sec7.Aux117

/-! ### No singular motion without collisions -/

section Defect

variable {w v : ℝ≥0 → ℝ}

/-- **A force path that never meets the driver at positive times has zero force defect.** -/
theorem forceDefect_eq_zero_of_ne (hv : IsForcePath w v) (hne : ∀ u : ℝ≥0, 0 < u → v u ≠ w u) (t : ℝ≥0) :
    forceDefect w v t = 0 := by
  have h0 : forceDefect w v 0 = 0 := by simp [forceDefect]
  rcases eq_zero_or_pos t with rfl | ht
  · exact h0
  have hconst : ∀ ε ∈ Ioc (0 : ℝ≥0) t, forceDefect w v ε = forceDefect w v t := fun ε hε =>
    (hv.forceDefect_eq_of_forall_ne hε.2 fun u hu => hne u (lt_of_lt_of_le hε.1 hu.1)).symm
  have hlim : Tendsto (forceDefect w v) (𝓝[>] 0) (𝓝 (forceDefect w v 0)) :=
    hv.continuous_forceDefect.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hev : forceDefect w v =ᶠ[𝓝[>] 0] fun _ => forceDefect w v t := by
    filter_upwards [Ioc_mem_nhdsGT ht] with ε hε using hconst ε hε
  have he := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  rw [← he, h0]

end Defect

/-! ### An exhausting sequence below a positive time -/

theorem exists_seq_lt {T : WithTop ℝ≥0} (hT : 0 < T) :
    ∃ s : ℕ → ℝ≥0, (∀ n, (s n : WithTop ℝ≥0) < T) ∧ ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T → ∃ n, t < s n := by
  induction T using WithTop.recTopCoe with
  | top =>
    refine ⟨fun n => n, fun n => WithTop.coe_lt_top _, fun t _ => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact ⟨n, hn⟩
  | coe T₀ =>
    have hT₀ : 0 < T₀ := WithTop.coe_lt_coe.1 hT
    refine ⟨fun n => T₀ * ((n : ℝ≥0) / (n + 1)), fun n => WithTop.coe_lt_coe.2 ?_, fun t ht => ?_⟩
    · have h1 : (n : ℝ≥0) / (n + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one _)
      calc T₀ * ((n : ℝ≥0) / (n + 1)) < T₀ * 1 := mul_lt_mul_of_pos_left h1 hT₀
        _ = T₀ := mul_one _
    · have htl : t < T₀ := WithTop.coe_lt_coe.1 ht
      have hlim : Tendsto (fun n : ℕ => T₀ * ((n : ℝ≥0) / (n + 1))) atTop (𝓝 T₀) := by
        have h := (tendsto_natCast_div_add_atTop (1 : ℝ≥0)).const_mul T₀
        rwa [mul_one] at h
      obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds htl)).exists
      exact ⟨n, hn⟩

/-! ### Killed words solve the integrated equations with their recovered noise -/

section Word

variable {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {T : Ω → WithTop ℝ≥0}

/-- **The recovered noise** of a path started from the marks `(xL, xR)`: `(W + ½ (Σ ρ_L (V_L − x_L) + Σ ρ_R
(V_R − x_R)))/√κ`. -/
def recNoise (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  (w t + (1 / 2) * ((∑ i, ρL i * (vL i t - xL i)) + ∑ j, ρR j * (vR j t - xR j))) / Real.sqrt κ

/-- **Every sample of a killed word is a word entrance driven by its recovered noise up to the kill.** -/
theorem _root_.InteractingSLE.WangWu.ImgDrv.IsKilledWord.isWordEntrance_recNoise (hK : IsKilledWord W VL VR T)
    (hT0 : ∀ ω, 0 < T ω) {κ : ℝ}
    (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ω : Ω) :
    IsWordEntrance κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω)
      (recNoise κ ρL ρR (fun i => VL i 0 ω) (fun j => VR j 0 ω) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω))
      (T ω : ℝ≥0∞) := by
  choose s hsT hsex using fun ω' => exists_seq_lt (hT0 ω')
  set σ : ℕ → Ω → ℝ≥0 := fun n ω' => s ω' n with hσ
  have hσT : ∀ n ω', (σ n ω' : WithTop ℝ≥0) < T ω' := fun n ω' => hsT ω' n
  have hsk : Real.sqrt κ ≠ 0 := (Real.sqrt_pos.2 hκ).ne'
  set xL : Fin nL → ℝ := fun i => VL i 0 ω with hxL
  set xR : Fin nR → ℝ := fun j => VR j 0 ω with hxR
  set b : ℝ≥0 → ℝ := recNoise κ ρL ρR xL xR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) with hb
  have hn : ∀ n, IsWordEntrance κ xL xR ρL ρR (fun t => sysW W (σ n) t ω) (fun i t => sysVL W VL (σ n) i t ω)
      (fun j t => sysVR W VR (σ n) j t ω) b (σ n ω : ℝ≥0∞) := by
    intro n
    set b' : ℝ≥0 → ℝ := recNoise κ ρL ρR xL xR (fun t => sysW W (σ n) t ω) (fun i t => sysVL W VL (σ n) i t ω)
      (fun j t => sysVR W VR (σ n) j t ω) with hb'
    have hw' : ∀ t, sysW W (σ n) t ω = Real.sqrt κ * b' t - (1 / 2) * ((∑ i, ρL i *
        (sysVL W VL (σ n) i t ω - xL i)) + ∑ j, ρR j * (sysVR W VR (σ n) j t ω - xR j)) :=
      fun t => by simp only [hb', recNoise]; field_simp; ring
    have hE := isWordEntrance_of_forceDefect_eq_zero (a := κ) (b := b') (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
      (T := (σ n ω : ℝ≥0∞)) (sysW_zero hK.w_zero ω) (fun i => hK.sysVL_of_le (hσT n) zero_le i)
      (fun j => hK.sysVR_of_le (hσT n) zero_le j) (hK.continuous_sysW (hσT n) ω)
      (fun i => hK.isForcePath_sysVL (hσT n) ω i) (fun j => hK.isForcePath_sysVR (hσT n) ω j)
      (fun t _ => contV_left_le_contW t) (fun t _ => contW_le_contV_right t)
      (hK.antitone_idx_sysVL (hσT n) ω) (hK.monotone_idx_sysVR (hσT n) ω) hw'
      (fun t _ i => forceDefect_eq_zero_of_ne (hK.isForcePath_sysVL (hσT n) ω i)
        (fun u hu => (hK.sysVL_lt_sysW (hσT n) ω hu i).ne) t)
      (fun t _ j => forceDefect_eq_zero_of_ne (hK.isForcePath_sysVR (hσT n) ω j)
        (fun u hu => (hK.sysW_lt_sysVR (hσT n) ω hu j).ne') t)
    refine IsWordEntrance.congr_b hE fun t ht => ?_
    have htσ : t ≤ σ n ω := (ENNReal.coe_lt_coe.1 ht).le
    simp only [hb', hb, recNoise, sysW_of_le htσ, hK.sysVL_of_le (hσT n) htσ, hK.sysVR_of_le (hσT n) htσ]
  refine isWordEntrance_of_seq (wn := fun n t => sysW W (σ n) t ω)
    (vLn := fun n i t => sysVL W VL (σ n) i t ω) (vRn := fun n j t => sysVR W VR (σ n) j t ω)
    (s := fun n => σ n ω) hn (fun n t ht => ?_) (fun t ht => ?_)
  · exact ⟨sysW_of_le ht, fun i => hK.sysVL_of_le (hσT n) ht i, fun j => hK.sysVR_of_le (hσT n) ht j⟩
  · obtain ⟨r, htr, hrT⟩ := WithTop.lt_iff_exists_coe_btwn.1 (show (t : WithTop ℝ≥0) < T ω from ht)
    obtain ⟨n, hn'⟩ := hsex ω r hrT
    exact ⟨n, lt_trans (WithTop.coe_lt_coe.1 htr) hn'⟩

/-- **The local integrated path of a killed word with its recovered noise**: up to the kill, if the start is not a
threshold configuration (at positive times the marks are strictly separated from the driver). -/
theorem _root_.InteractingSLE.WangWu.ImgDrv.IsKilledWord.isSLEPathUpTo_recNoise (hK : IsKilledWord W VL VR T)
    (hT0 : ∀ ω, 0 < T ω) {κ : ℝ}
    (hκ : 0 < κ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (ω : Ω)
    (hthr0 : ¬ ForceWord.ThresholdCondition ρL ρR (W 0 ω) (fun i => VL i 0 ω) (fun j => VR j 0 ω)) :
    Sec2.IsSLEPathUpTo κ (fun i => VL i 0 ω) (fun j => VR j 0 ω) ρL ρR (W · ω) (fun i t => VL i t ω)
      (fun j t => VR j t ω)
      (recNoise κ ρL ρR (fun i => VL i 0 ω) (fun j => VR j 0 ω) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω))
      (T ω : ℝ≥0∞) := by
  refine StagedRep.isSLEPathUpTo_of_isWordEntrance (hK.isWordEntrance_recNoise hT0 hκ ρL ρR ω) fun t ht => ?_
  rcases eq_zero_or_pos t with rfl | htp
  · exact hthr0
  · have ht' : (t : WithTop ℝ≥0) < T ω := by exact_mod_cast ht
    exact StagedRep.not_threshold_of_sep (fun i => hK.sepL ω t htp ht' i) (fun j => hK.sepR ω t htp ht' j)

end Word

end InteractingSLE.Sec5.CrossCond.StagedRepLater

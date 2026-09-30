import QuantumZipper.Proofs.Zipper.FieldLawlerPath

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM: Field–Lawler Theorem 1.1 from the crosscut-sum covering

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*,
EJP 20 (2015), no. 10 (arXiv:1407.3314), **Theorem 1.1** (p. 3), proved as **Proposition 3.4**
(pp. 8–9): condition on `γ_ρ`, `ρ` the first time `|γ| = R`; the remaining curve is the image
under `Z_ρ⁻¹` of an `SLE_κ` in `ℍ` (strong Markov / domain Markov property); it enters
`B(0, ε)` only through the image crosscuts, and **Proposition 3.1** summed over them with
`Σ aⱼ^α ≤ (Σ aⱼ)^α` (`4a − 1 = 8/κ − 1 ≥ 1`) gives `c (ε/R)^{8/κ−1}`.

`fieldLawlerReturn_of_cover : FLCoverStmt → BaseFin2.FieldLawlerReturnStmt`. The strong Markov
step and Prop. 3.1 summed over the covering disks are `LWFar.lwf_restart_hit_le` (Lawler–Werness
Prop. 2.6 = `bdryHitStmt_holds`, with `StrongMarkov.isBrownianReal_smShift`); the first hitting
time is a stopping time by `LWFar.lwr_hit_stop`; the covering is `FLCoverStmt` (FL's crosscut sum).
The horizon `n` (monotone union) and the version `B''` of the Brownian motion are own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- The truncated stopping time `min τ n` as an `ℝ≥0`-valued function. -/
def truncT {Ω : Type} (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  WithTop.untopD (n : ℝ≥0) (min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0))

theorem truncT_coe {Ω : Type} (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    ((truncT τ n ω : ℝ≥0) : WithTop ℝ≥0) = min (τ ω) ((n : ℝ≥0) : WithTop ℝ≥0) := by
  unfold truncT
  cases h : τ ω with
  | top => simp; rfl
  | coe a =>
    rw [← WithTop.coe_min]
    rfl

theorem truncT_of_le {Ω : Type} {τ : Ω → WithTop ℝ≥0} {n : ℕ} {ω : Ω} {a : ℝ≥0}
    (ha : τ ω = (a : WithTop ℝ≥0)) (han : a ≤ (n : ℝ≥0)) : truncT τ n ω = a := by
  have h := truncT_coe τ n ω
  rw [ha, ← WithTop.coe_min, min_eq_left han] at h
  exact WithTop.coe_injective h

/-- **Field–Lawler Theorem 1.1 (scaled, unconditional form) from the crosscut-sum covering.** -/
theorem fieldLawlerReturn_of_cover (hcov : FLCoverStmt) : BaseFin2.FieldLawlerReturnStmt := by
  intro κ hκ hκ4
  obtain ⟨C, δ₀, hC0, hδ₀, hcv⟩ := hcov
  obtain ⟨C0, hC00, hRst⟩ := lwf_restart_hit_le hκ hκ4
  set α : ℝ := 8 / κ - 1 with hα
  have hα0 : 0 < α := by rw [hα, sub_pos, lt_div_iff₀ hκ]; linarith
  set δ₁ : ℝ := min δ₀ (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min hδ₀ (by norm_num)
  set c : ℝ := max (C0 * C ^ α) (δ₁⁻¹ ^ α) with hcdef
  refine ⟨c, le_max_of_le_right (by positivity), ?_⟩
  intro Ω _ P _ B hB R ε hR hε
  by_cases hsm : ε ≤ δ₁ * R
  swap
  · -- large `ε/R`: the bound is at least `1`
    refine prob_le_one.trans ?_
    rw [ENNReal.one_le_ofReal]
    have h1 : δ₁ ≤ ε / R := by rw [le_div_iff₀ hR]; push_neg at hsm; linarith
    calc (1 : ℝ) = δ₁⁻¹ ^ α * δ₁ ^ α := by
          rw [← Real.mul_rpow (by positivity) hδ₁0.le, inv_mul_cancel₀ hδ₁0.ne', Real.one_rpow]
      _ ≤ δ₁⁻¹ ^ α * (ε / R) ^ α := by gcongr
      _ ≤ c * (ε / R) ^ α := by gcongr; exact le_max_right _ _
  have hδ₁h : δ₁ ≤ 1 / 2 := min_le_right _ _
  have hεR : ε < R := by nlinarith
  have hεδ₀ : ε ≤ δ₀ * R := hsm.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hR.le)
  -- the target constant
  set K : ℝ≥0∞ := ENNReal.ofReal (C0 * (C * (ε / R)) ^ α) with hK
  have hKle : K ≤ ENNReal.ofReal (c * (ε / R) ^ α) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.mul_rpow hC0 (div_nonneg hε.le hR.le), ← mul_assoc]
    gcongr
    exact le_max_left _ _
  -- a version with continuous paths and its natural filtration
  obtain ⟨B'', hB''m, hB''c, hB''0, hB'', hBeq⟩ := RS.exists_good_version0 hB
  set 𝓕 := natFilt B'' hB''m with h𝓕
  have hS : SMSetup P B'' 𝓕 := smSetup_natFilt hB'' hB''m hB''c hB''0
  -- the first hitting time of `{|z| ≥ R}`
  set F : Set ℂ := {z : ℂ | R ≤ ‖z‖} with hF
  have hFc : IsClosed F := isClosed_le continuous_const continuous_norm
  obtain ⟨D, hDF, hDc, hFD⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace F).exists_countable_dense_subset
  have hRF : ((R : ℝ) : ℂ) ∈ F := by
    show R ≤ ‖((R : ℝ) : ℂ)‖
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have hDne : D.Nonempty := by
    by_contra hD
    rw [not_nonempty_iff_eq_empty] at hD
    have := hFD hRF
    rw [hD, closure_empty] at this
    exact this
  obtain ⟨cs, hcs⟩ := hDc.exists_eq_range hDne
  have hclo : ∀ ω : Ω, closure (cs '' {j | ω ∈ (univ : Set Ω)}) = F := by
    intro ω
    simp only [mem_univ, setOf_true, image_univ, ← hcs]
    exact subset_antisymm (hFc.closure_subset_iff.2 hDF) hFD
  obtain ⟨τ, hτ, hτeq⟩ := lwr_hit_stop hκ hκ4 hS (isStoppingTime_const 𝓕 (0 : ℝ≥0)) cs
    (fun _ => univ) (fun j t => by simp)
  -- the restarted processes
  have hind : ∀ t, Indep (𝓕 t) (MeasurableSpace.comap (StrongMarkov.smPath B'' (fun _ => t))
      MeasurableSpace.pi) P := fun t =>
    StrongMarkov.indep_shift_of_le_past hB''.toIsPreBrownianReal (fun t => le_of_eq (hS.natural t)) t
  have hσ : ∀ n : ℕ, IsStoppingTime 𝓕 (fun ω => (truncT τ n ω : WithTop ℝ≥0)) := by
    intro n
    have h := hτ.min_const ((n : ℝ≥0))
    convert h using 1
    funext ω
    exact truncT_coe τ n ω
  have hBt : ∀ n : ℕ, IsBrownianReal (StrongMarkov.smShift B'' (truncT τ n)) P := fun n =>
    StrongMarkov.isBrownianReal_smShift hB''.toIsPreBrownianReal hB''c hB''m hind (hσ n)
  -- almost sure path properties
  have hbase : ∀ᵐ ω ∂P, IsSimpleChord (sleTrace κ B'' ω) ∧
      (∀ t : ℝ, 0 ≤ t → fwdHull (drive κ B'' ω) t = sleTrace κ B'' ω '' Ioc 0 t) ∧
      ∀ u : ℝ, 0 ≤ u → Tendsto (fun y : ℝ => fwdMapInv (drive κ B'' ω) u (y * Complex.I))
        (𝓝[>] 0) (𝓝 (sleTrace κ B'' ω u)) := by
    obtain ⟨δ', hδ', hg'⟩ := RS.ae_sleTrace_good hB'' hκ (by linarith)
    filter_upwards [hg', RS.rohdeSchrammSimple κ hκ hκ4.le P B'' hB''] with ω hω hrs
    refine ⟨hrs.1, hrs.2, fun u hu => ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_ge u
    obtain ⟨C', hC'⟩ := hω.2.2 N
    exact fl_tendsto_of_radial hδ' (hC' u ⟨hu, hN⟩)
  have hshift : ∀ n : ℕ, ∀ᵐ ω ∂P,
      IsSimpleChord (sleTrace κ (StrongMarkov.smShift B'' (truncT τ n)) ω) ∧
      ∀ u : ℝ, 0 ≤ u → Tendsto (fun y : ℝ =>
        fwdMapInv (drive κ (StrongMarkov.smShift B'' (truncT τ n)) ω) u (y * Complex.I))
        (𝓝[>] 0) (𝓝 (sleTrace κ (StrongMarkov.smShift B'' (truncT τ n)) ω u)) := by
    intro n
    obtain ⟨δ', hδ', hg'⟩ := RS.ae_sleTrace_good (hBt n) hκ (by linarith)
    filter_upwards [hg', RS.rohdeSchrammSimple κ hκ hκ4.le P _ (hBt n)] with ω hω hrs
    refine ⟨hrs.1, fun u hu => ?_⟩
    obtain ⟨N, hN⟩ := exists_nat_ge u
    obtain ⟨C', hC'⟩ := hω.2.2 N
    exact fl_tendsto_of_radial hδ' (hC' u ⟨hu, hN⟩)
  -- the first hitting time, pathwise
  have key : ∀ ω, IsSimpleChord (sleTrace κ B'' ω) →
      τ ω = (sInf (ENNReal.ofReal '' {t : ℝ | 0 ≤ t ∧
        (((fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal t ∧
        sleTrace κ B'' ω t ∈ closure (cs '' {j | ω ∈ (fun _ => (univ : Set Ω)) j})}) :
          WithTop ℝ≥0) →
      ∀ s : ℝ, 0 ≤ s → R ≤ ‖sleTrace κ B'' ω s‖ →
      ∃ T : ℝ, 0 < T ∧ T ≤ s ∧ ‖sleTrace κ B'' ω T‖ = R ∧
        (∀ u ∈ Ico 0 T, ‖sleTrace κ B'' ω u‖ < R) ∧
        τ ω = ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) := by
    intro ω hsc hτω s hs0 hRs
    obtain ⟨T, hT0, hTs, -, hTR, hbel, hleast⟩ := fl_firstHit hsc.2.1 hsc.1 hR hs0 hRs
    refine ⟨T, hT0, hTs, hTR, hbel, ?_⟩
    rw [hτω, hclo ω]
    have hset : {t : ℝ | 0 ≤ t ∧
        (((fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω : WithTop ℝ≥0) : ℝ≥0∞) ≤ ENNReal.ofReal t ∧
        sleTrace κ B'' ω t ∈ F} = {t : ℝ | 0 ≤ t ∧ sleTrace κ B'' ω t ∈ F} := by
      ext t
      simp only [mem_setOf_eq]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, by first | exact zero_le _ | exact bot_le, h.2⟩⟩
    rw [hset]
    have hL : IsLeast (ENNReal.ofReal '' {t : ℝ | 0 ≤ t ∧ sleTrace κ B'' ω t ∈ F})
        (ENNReal.ofReal T) :=
      ⟨⟨T, hleast.1, rfl⟩, by
        rintro _ ⟨t, ht, rfl⟩
        exact ENNReal.ofReal_le_ofReal (hleast.2 ht)⟩
    have h1 : sInf (ENNReal.ofReal '' {t : ℝ | 0 ≤ t ∧ sleTrace κ B'' ω t ∈ F}) =
        ENNReal.ofReal T := hL.csInf_eq
    exact h1
  -- the events with horizon `n`
  set E : ℕ → Set Ω := fun n => {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ t ≤ n ∧
    R ≤ ‖sleTrace κ B'' ω s‖ ∧ ‖sleTrace κ B'' ω t‖ < ε} with hE
  have hEmono : Monotone E := by
    intro m n hmn ω hω
    obtain ⟨s, t, hs0, hst, htm, hRs, hεt⟩ := hω
    exact ⟨s, t, hs0, hst, htm.trans (Nat.cast_le.2 hmn), hRs, hεt⟩
  have hmain : ∀ n : ℕ, P (E n) ≤ K := by
    intro n
    set A : Set Ω := {ω | τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} with hAdef
    have hA : MeasurableSet[(hσ n).measurableSpace] A := by
      have h := hτ.measurableSet_stopping_time_le (hσ n)
      convert h using 1
      ext ω
      simp only [hAdef, mem_setOf_eq, truncT_coe, le_min_iff, le_refl, true_and]
    set V : Ω → Set ℂ := fun ω =>
      {p : ℂ | 0 < p.im ∧ ‖fwdMapInv (drive κ B'' ω) (truncT τ n ω) p‖ < ε} with hVdef
    have hVo : ∀ ω, IsOpen (V ω) := fun ω =>
      isOpen_invBall (continuousOn_fwdMapInv_H' (drive_continuous (hB''c ω))
        (drive_zero (hB''0 ω)) (truncT τ n ω).2) ε
    have hVm := measurableSet_invBall hS κ (hσ n) ε
    have hcovn : ∀ᵐ ω ∂P, ω ∈ A → ∃ c r : ℕ → ℝ, (∀ i, 0 < r i ∧ 2 * r i ≤ |c i|) ∧
        Summable (fun i => r i / |c i|) ∧ ∑' i, r i / |c i| ≤ C * (ε / R) ∧
        ∀ p ∈ V ω, ∃ i, ‖p - (c i : ℂ)‖ < r i := by
      filter_upwards [hbase, hτeq] with ω hb hτω
      intro hωA
      have hne : ∃ s : ℝ, 0 ≤ s ∧ R ≤ ‖sleTrace κ B'' ω s‖ := by
        by_contra hno
        push_neg at hno
        apply (show τ ω ≠ ⊤ from ne_top_of_le_ne_top WithTop.coe_ne_top hωA)
        rw [hτω, hclo ω]
        have h2 : ∀ S : Set ℝ, (∀ t ∈ S, False) → sInf (ENNReal.ofReal '' S) = ⊤ := by
          intro S hS
          rw [Set.subset_empty_iff.1 (fun t ht => (hS t ht).elim), image_empty, sInf_empty]
        exact h2 _ (fun t ht => absurd ht.2.2 (not_le.2 (hno t ht.1)))
      obtain ⟨s, hs0, hRs⟩ := hne
      obtain ⟨T, hT0, -, hTR, hbel, hτT⟩ := key ω hb.1 hτω s hs0 hRs
      have hTn : T.toNNReal ≤ (n : ℝ≥0) := by
        have hωA' : τ ω ≤ ((n : ℝ≥0) : WithTop ℝ≥0) := hωA
        rw [hτT] at hωA'; exact_mod_cast hωA'
      have htr : truncT τ n ω = T.toNNReal := truncT_of_le hτT hTn
      have hTr : ((truncT τ n ω : ℝ≥0) : ℝ) = T := by rw [htr, Real.coe_toNNReal _ hT0.le]
      have hsc := hb.1
      obtain ⟨c', r', h1, h2, h3, h4⟩ := hcv (drive κ B'' ω) (drive_continuous (hB''c ω))
        (drive_zero (hB''0 ω)) T R ε hT0.le hR hε hεδ₀ hsc.1 (hsc.2.1.mono Icc_subset_Ici_self)
        (hsc.2.2.1.mono Icc_subset_Ici_self) (fun u hu => hsc.2.2.2.1 u hu.1) (hb.2.1 T hT0.le)
        hbel hTR (hb.2.2 T hT0.le)
      refine ⟨c', r', h1, h2, h3, fun p hp => h4 p hp.1 ?_⟩
      have := hp.2
      rwa [hTr] at this
    have hb := hRst P B'' 𝓕 hS (truncT τ n) (hσ n) A V (C * (ε / R)) hA (by positivity) hVo
      hVm hcovn
    refine (measure_mono_ae ?_).trans (hb.trans (mul_le_of_le_one_right' prob_le_one))
    filter_upwards [hbase, ae_all_iff.2 hshift, hτeq] with ω hb hsh hτω
    rintro ⟨s, t, hs0, hst, htn, hRs, hεt⟩
    obtain ⟨T, hT0, hTs, hTR, hbel, hτT⟩ := key ω hb.1 hτω s hs0 hRs
    have hTn : T.toNNReal ≤ (n : ℝ≥0) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hT0.le]; push_cast; linarith
    have htr := truncT_of_le hτT hTn
    have hTr : ((truncT τ n ω : ℝ≥0) : ℝ) = T := by rw [htr, Real.coe_toNNReal _ hT0.le]
    have hωA : ω ∈ A := by
      show τ ω ≤ _
      rw [hτT]; exact_mod_cast hTn
    have hu : 0 < t - T := by
      rcases eq_or_lt_of_le (hTs.trans hst) with h | h
      · exfalso; rw [← h] at hεt; linarith
      · linarith
    refine ⟨hωA, t - T, hu.le, ?_⟩
    set W := drive κ B'' ω with hWdef
    have hW : Continuous W := drive_continuous (hB''c ω)
    have hW0 : W 0 = 0 := drive_zero (hB''0 ω)
    set Y := StrongMarkov.smShift B'' (truncT τ n) with hYdef
    have hYc : Continuous (drive κ Y ω) := drive_continuous
      (((hB''c ω).comp (continuous_const.add continuous_id)).sub continuous_const)
    have hY0 : drive κ Y ω 0 = 0 := drive_zero (by simp [hYdef, StrongMarkov.smShift])
    have hYtr : sleTrace κ Y ω (t - T) = trace (RS.shiftDrive W T) (t - T) := by
      have h := RS.sleTrace_shift_eq κ (truncT τ n ω) (hB''c ω) hu.le
      rw [hTr] at h
      exact h
    have hdr : EqOn (drive κ Y ω) (RS.shiftDrive W T) (Icc 0 (t - T)) := by
      intro r hr
      have h := RS.drive_shift κ B'' (truncT τ n ω) ω hr.1
      rw [hTr] at h
      exact h
    have hcg := RegCont.fwdMapInv_congr hYc hY0 (RS.continuous_shiftDrive hW T)
      (RS.shiftDrive_zero W T) hdr ⟨hu.le, le_rfl⟩
    have hpH : sleTrace κ Y ω (t - T) ∈ H := (hsh n).1.2.2.2.1 _ hu
    have hlim := (hsh n).2 (t - T) hu.le
    rw [hYtr] at hpH hlim
    have hlim' : Tendsto (fun y : ℝ => fwdMapInv (RS.shiftDrive W T) (t - T) (y * Complex.I))
        (𝓝[>] 0) (𝓝 (trace (RS.shiftDrive W T) (t - T))) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact hcg (RS.mul_I_mem_H hy)
    obtain ⟨-, -, htrace⟩ := RS.trace_add_of_tendsto_shift hW hW0 hT0.le hu.le hpH hlim'
    show 0 < (sleTrace κ Y ω (t - T)).im ∧
      ‖fwdMapInv W (truncT τ n ω) (sleTrace κ Y ω (t - T))‖ < ε
    rw [hYtr, hTr]
    refine ⟨hpH, ?_⟩
    rw [← htrace, show T + (t - T) = t by ring]
    exact hεt
  have hsub : {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ R ≤ ‖sleTrace κ B ω s‖ ∧
      ‖sleTrace κ B ω t‖ < ε} ≤ᵐ[P] ⋃ n, E n := by
    filter_upwards [hBeq] with ω hω
    rintro ⟨s, t, hs0, hst, hRs, hεt⟩
    have htr : sleTrace κ B ω = sleTrace κ B'' ω := by
      show trace (drive κ B ω) = trace (drive κ B'' ω)
      congr 1
      funext r
      simp only [drive, hω]
    obtain ⟨N, hN⟩ := exists_nat_ge t
    rw [htr] at hRs hεt
    exact mem_iUnion.2 ⟨N, s, t, hs0, hst, hN, hRs, hεt⟩
  calc P {ω | ∃ s t : ℝ, 0 ≤ s ∧ s ≤ t ∧ R ≤ ‖sleTrace κ B ω s‖ ∧ ‖sleTrace κ B ω t‖ < ε}
      ≤ P (⋃ n, E n) := measure_mono_ae hsub
    _ = ⨆ n, P (E n) := hEmono.measure_iUnion
    _ ≤ K := iSup_le hmain
    _ ≤ _ := hKle

end FieldLawler
end QuantumZipper

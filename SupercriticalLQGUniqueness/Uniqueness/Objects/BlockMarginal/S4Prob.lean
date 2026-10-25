import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.S4Sep
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge




 











set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Real
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

 
theorem not_S4_subset (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (hTr : T.r = C.r)
    (F : ℂ → Set DistC) {N : ℕ} (hN : N ≤ blockCount T.K C.A_sp) :
    {g | ¬ Objects.CorrectedEvent.S4 C T (fun z => g ∈ F z)} ⊆
      ⋃ i ∈ Finset.range (arcCount C.A_sp), (⋃ z ∈ blockSites T (arcCount C.A_sp) i N, F z)ᶜ := by
  intro g hg
  simp only [mem_ofPred_eq, Objects.CorrectedEvent.S4, not_forall, not_exists, not_and] at hg
  obtain ⟨θ0, θ1, _, _, hlen, hno⟩ := hg
  have hr : 0 < T.r := hTr ▸ C.rPos
  obtain ⟨i, hi, hcov⟩ := arc_contains_block T C.A_sp C.spPos hr hN θ0 θ1 (by rw [hTr]; exact hlen)
  simp only [mem_iUnion, Finset.mem_range, mem_compl_iff, not_exists]
  refine ⟨i, hi, fun z hz hgz => ?_⟩
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hz
  have hon := hcov k hk
  rw [hTr] at hon
  exact hno k hon hgz

 
theorem exists_s4_bound (pbar : Ioo (0 : ℝ) 1) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (Asp : ℝ) (hA : 0 < Asp) :
    ∃ n₀ : ℕ, ∀ (μ : Measure DistC) [IsProbabilityMeasure μ],
      LQGMetric.IsWholePlaneGFF (id : DistC → DistC) μ →
      ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), C.A_sp = Asp → T.r = C.r → Asp ≤ 1 →
      ∀ R : ℝ, 0 < R → 2 * (1 + 22 / 3) * R ≤ 8 * T.r / T.K → n₀ ≤ blockCount T.K Asp →
      ∀ F : ℂ → Set DistC,
        (∀ k : Fin T.K, AEEventIn μ (fieldSigma0On (id : DistC → DistC)
          (ball (Objects.CorrectedEvent.site T k) R)) (F (Objects.CorrectedEvent.site T k))) →
        (∀ k : Fin T.K, ENNReal.ofReal p ≤ μ (F (Objects.CorrectedEvent.site T k))) →
        (∀ k : Fin T.K, NullMeasurableSet (F (Objects.CorrectedEvent.site T k)) μ) →
        μ {g | ¬ Objects.CorrectedEvent.S4 C T (fun z => g ∈ F z)} ≤ ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  set m := arcCount Asp with hm
  have hm0 : 0 < m := arcCount_pos hA
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hb1 := pbar.2.1
  have hb2 := pbar.2.2
  set ε : ℝ := (1 - (pbar : ℝ)) / (10 * m) with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    rw [hε, div_lt_one (by positivity)]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    nlinarith
  set q : ℝ := 1 - ε with hq
  obtain ⟨n₀, hn₀⟩ := Toolkit.AnnulusIteration.gm_spatial_scaled_modConst (22 / 3) p q (by norm_num) hp hp1
    (by linarith) (by linarith)
  refine ⟨n₀, ?_⟩
  intro μ _ hμ C T hCA hTr hA1 R hR hsepR hcount F hloc hmarg hnull
  have hr : 0 < T.r := hTr ▸ C.rPos
  set N := blockCount T.K Asp with hNdef
  have hblock : ∀ i : ℕ, ENNReal.ofReal q ≤ μ (⋃ z ∈ blockSites T m i N, F z) := by
    intro i
    have hcard : n₀ ≤ (blockSites T m i N).card := by
      rw [card_blockSites T hr Asp hA hA1 le_rfl m i]
      exact hcount
    refine hn₀ μ id hμ R hR (blockSites T m i N) hcard ?_ F ?_ ?_
    · intro z hz w hw hzw
      exact hsepR.trans (blockSites_sep T hr Asp hA hA1 le_rfl m i z hz w hw hzw)
    · intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hz
      exact hloc k
    · intro z hz
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hz
      exact hmarg k
  have hfail : ∀ i : ℕ, μ (⋃ z ∈ blockSites T m i N, F z)ᶜ ≤ ENNReal.ofReal ε := by
    intro i
    have hmeas : NullMeasurableSet (⋃ z ∈ blockSites T m i N, F z) μ := by
      refine NullMeasurableSet.biUnion (blockSites T m i N).countable_toSet fun z hz => ?_
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.1 hz
      exact hnull k
    rw [prob_compl_eq_one_sub₀ hmeas]
    have h := hblock i
    calc 1 - μ (⋃ z ∈ blockSites T m i N, F z) ≤ 1 - ENNReal.ofReal q := tsub_le_tsub_left h 1
      _ = ENNReal.ofReal ε := by
        rw [hq, ENNReal.ofReal_sub 1 hε0.le, ENNReal.ofReal_one]
        rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top]
        exact ENNReal.ofReal_le_one.2 hε1.le
  calc μ {g | ¬ Objects.CorrectedEvent.S4 C T (fun z => g ∈ F z)}
      ≤ μ (⋃ i ∈ Finset.range m, (⋃ z ∈ blockSites T m i N, F z)ᶜ) := by
        apply measure_mono
        have h := not_S4_subset C T hTr F (N := N) (by rw [hCA])
        rw [hCA] at h
        exact h
    _ ≤ ∑ i ∈ Finset.range m, μ (⋃ z ∈ blockSites T m i N, F z)ᶜ := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ Finset.range m, ENNReal.ofReal ε := Finset.sum_le_sum fun i _ => hfail i
    _ = ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hε]
        field_simp

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

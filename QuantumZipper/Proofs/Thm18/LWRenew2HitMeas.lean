import QuantumZipper.Proofs.Thm18.LWRenew2HitGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWS-0′-HIT, part 4: the guard is an `𝓕_v`-event

`RadGuard W δ C v` only needs to be checked at rational radii and at the times
`ℚ ∩ [0,v] ∪ {v}` (continuity of `f̂_t(iy)` in `y` and in `t`), so for the natural filtration
`{ω | RadGuard (drive κ B ω) δ C v}` is `𝓕_v`-measurable for every `v` (own elementary
bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

variable {W : ℝ → ℝ} {δ C : ℝ}

/-- The guard inequality at time `t` for rational radii. -/
def RatBound (W : ℝ → ℝ) (δ C t : ℝ) : Prop :=
  ∀ y y' : ℚ, (y : ℝ) ∈ Ioc (0 : ℝ) 1 → (y' : ℝ) ∈ Ioc 0 (y : ℝ) →
    dist (fwdMapInv W t ((y : ℝ) * Complex.I)) (fwdMapInv W t ((y' : ℝ) * Complex.I)) ≤
      C * (y : ℝ) ^ δ

lemma continuousOn_radial (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    ContinuousOn (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (Ioi 0) :=
  (RS.differentiableOn_fwdMapInv hW hW0 ht).continuousOn.comp (by fun_prop)
    fun y hy => by simpa using hy

/-- Rational radii suffice. -/
theorem ratBound_real (hW : Continuous W) (hW0 : W 0 = 0) (hδ : 0 < δ) {t : ℝ} (ht : 0 ≤ t)
    (h : RatBound W δ C t) {y y' : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) (hy' : y' ∈ Ioc 0 y) :
    dist (fwdMapInv W t (y * Complex.I)) (fwdMapInv W t (y' * Complex.I)) ≤ C * y ^ δ := by
  have hex : ∀ k : ℕ, ∃ p : ℚ × ℚ, max (y' / 2) (y' - 1 / ((k : ℝ) + 1)) < (p.2 : ℝ) ∧
      (p.2 : ℝ) < y' ∧ max (p.2 : ℝ) (y - 1 / ((k : ℝ) + 1)) < (p.1 : ℝ) ∧ (p.1 : ℝ) < y := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (max_lt (by linarith [hy'.1]) (by linarith) :
      max (y' / 2) (y' - 1 / ((k : ℝ) + 1)) < y')
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (max_lt (hb2.trans_le hy'.2) (by linarith) :
      max (b : ℝ) (y - 1 / ((k : ℝ) + 1)) < y)
    exact ⟨(a, b), hb1, hb2, ha1, ha2⟩
  choose p hp1 hp2 hp3 hp4 using hex
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim2 : Tendsto (fun k => ((p k).2 : ℝ)) atTop (𝓝 y') := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k : ℕ => y' - 1 / ((k : ℝ) + 1))
      (h := fun _ : ℕ => y') ?_ tendsto_const_nhds (fun k => ((le_max_right _ _).trans_lt (hp1 k)).le)
      (fun k => (hp2 k).le)
    simpa using tendsto_const_nhds.sub hinv
  have hlim1 : Tendsto (fun k => ((p k).1 : ℝ)) atTop (𝓝 y) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun k : ℕ => y - 1 / ((k : ℝ) + 1))
      (h := fun _ : ℕ => y) ?_ tendsto_const_nhds (fun k => ((le_max_right _ _).trans_lt (hp3 k)).le)
      (fun k => (hp4 k).le)
    simpa using tendsto_const_nhds.sub hinv
  have hpos2 : ∀ k, (0 : ℝ) < ((p k).2 : ℝ) := fun k =>
    lt_of_lt_of_le (by linarith [hy'.1]) ((le_max_left _ _).trans (hp1 k).le)
  have hpos1 : ∀ k, (0 : ℝ) < ((p k).1 : ℝ) := fun k =>
    (hpos2 k).trans ((le_max_left _ _).trans_lt (hp3 k))
  have hc := continuousOn_radial hW hW0 ht
  have hF1 := ((hc y hy.1).tendsto).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim1, Eventually.of_forall fun k => hpos1 k⟩)
  have hF2 := ((hc y' hy'.1).tendsto).comp
    (tendsto_nhdsWithin_iff.2 ⟨hlim2, Eventually.of_forall fun k => hpos2 k⟩)
  have hR : Tendsto (fun k => C * ((p k).1 : ℝ) ^ δ) atTop (𝓝 (C * y ^ δ)) :=
    tendsto_const_nhds.mul
      ((Real.continuousAt_rpow_const y δ (Or.inr hδ.le)).tendsto.comp hlim1)
  refine le_of_tendsto_of_tendsto (hF1.dist hF2) hR (Eventually.of_forall fun k => ?_)
  exact h (p k).1 (p k).2 ⟨hpos1 k, (hp4 k).le.trans hy.2⟩
    ⟨hpos2 k, ((le_max_left _ _).trans_lt (hp3 k)).le⟩

/-- **Countable form of the guard.** -/
theorem radGuard_iff_rat (hW : Continuous W) (hW0 : W 0 = 0) (hδ : 0 < δ) {v : ℝ}
    (hv : 0 ≤ v) :
    RadGuard W δ C v ↔ RatBound W δ C v ∧ ∀ q : ℚ, (q : ℝ) ∈ Icc 0 v → RatBound W δ C q := by
  constructor
  · intro h
    exact ⟨fun y y' hy hy' => h v ⟨hv, le_rfl⟩ y hy y' hy',
      fun q hq y y' hy hy' => h q hq y hy y' hy'⟩
  · rintro ⟨hv', hq⟩ t ht y hy y' hy'
    rcases ht.2.lt_or_eq with htv | rfl
    · -- rational times `t_k ↓ t` inside `[0,v]`
      have hex : ∀ k : ℕ, ∃ q : ℚ, t < q ∧ (q : ℝ) < min v (t + 1 / ((k : ℝ) + 1)) := fun k =>
        exists_rat_btwn (lt_min htv (by linarith [(by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1))]))
      choose q hq1 hq2 using hex
      have hlim : Tendsto (fun k => (q k : ℝ)) atTop (𝓝 t) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => t)
          (h := fun k : ℕ => t + 1 / ((k : ℝ) + 1)) tendsto_const_nhds ?_ (fun k => (hq1 k).le)
          (fun k => ((hq2 k).trans_le (min_le_right _ _)).le)
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat :
            Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0))
      have hqI : ∀ k, (q k : ℝ) ∈ Icc 0 v := fun k =>
        ⟨ht.1.trans (hq1 k).le, ((hq2 k).trans_le (min_le_left _ _)).le⟩
      have hc1 := RS.continuousOn_fwdMapInv_mul_I hW hW0 hy.1 hv
      have hc2 := RS.continuousOn_fwdMapInv_mul_I hW hW0 hy'.1 hv
      have hT : Tendsto (fun k => (q k : ℝ)) atTop (𝓝[Icc 0 v] t) :=
        tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hqI⟩
      refine le_of_tendsto ((((hc1 t ht).tendsto.comp hT)).dist ((hc2 t ht).tendsto.comp hT))
        (Eventually.of_forall fun k => ?_)
      exact ratBound_real hW hW0 hδ (hqI k).1 (hq (q k) (hqI k)) hy hy'
    · exact ratBound_real hW hW0 hδ ht.1 hv' hy hy'

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {𝓕 : Filtration ℝ≥0 mΩ}

lemma measurableSet_ratBound (hS : SMSetup P B 𝓕) (κ δ C : ℝ) (s : ℝ≥0) :
    MeasurableSet[𝓕 s] {ω | RatBound (drive κ B ω) δ C s} := by
  simp only [RatBound, setOf_forall]
  refine MeasurableSet.iInter fun y => MeasurableSet.iInter fun y' =>
    MeasurableSet.iInter fun hy => MeasurableSet.iInter fun hy' => ?_
  have h1 := measurable_fwdMapInv_adapt hS κ s (w := ((y : ℝ) : ℂ) * Complex.I)
    (by simpa using hy.1)
  have h2 := measurable_fwdMapInv_adapt hS κ s (w := ((y' : ℝ) : ℂ) * Complex.I)
    (by simpa using hy'.1)
  exact (@Measurable.dist ℂ Ω _ _ _ (𝓕 s) _ _ _ h1 h2) measurableSet_Iic

/-- **The guard event is `𝓕_v`-measurable.** -/
theorem measurableSet_radGuard (hS : SMSetup P B 𝓕) (κ : ℝ) (hδ : 0 < δ) (C : ℝ) (v : ℝ≥0) :
    MeasurableSet[𝓕 v] {ω | RadGuard (drive κ B ω) δ C v} := by
  have heq : {ω | RadGuard (drive κ B ω) δ C v} = {ω | RatBound (drive κ B ω) δ C v} ∩
      ⋂ q : ℚ, ⋂ (_ : (q : ℝ) ∈ Icc 0 (v : ℝ)), {ω | RatBound (drive κ B ω) δ C q} := by
    ext ω
    simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
    exact radGuard_iff_rat (drive_continuous (hS.cont ω)) (drive_zero (hS.zero ω)) hδ v.2
  rw [heq]
  refine (measurableSet_ratBound hS κ δ C v).inter
    (MeasurableSet.iInter fun q => MeasurableSet.iInter fun hq => ?_)
  have hq0 : (0 : ℝ) ≤ q := hq.1
  have h := measurableSet_ratBound hS κ δ C (Real.toNNReal q)
  rw [Real.coe_toNNReal _ hq0] at h
  exact 𝓕.mono (Real.toNNReal_le_iff_le_coe.2 hq.2) _ h

end LWFar
end Thm18Asm
end QuantumZipper

import QuantumZipper.Proofs.Thm18.LWRenew2HitDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LWS-0′-HIT, part 3: a pathwise continuity guard for the trace

The natural filtration is not completed, so the hitting-time argument must run for **every**
sample point, while the trace is only a.s. continuous. We use a deterministic sufficient condition
for continuity of the trace on `[0,v]` (a uniform radial Cauchy bound with rate `C y^δ`,
`RadGuard`), which holds a.s. for all `v` by Rohde–Schramm (`RS.ae_sleTrace_good`), is downward
closed and closed from the left in `v`, and implies continuity of the trace on `[0,v]` (uniform
limit of the continuous maps `t ↦ f̂_t(iy)`, as in the proof of RS Thm 3.6 / `RS.trace_of_radialBound`).
Then the guarded rational hitting criterion `hitE_iff` holds for every driver.

Own elementary bookkeeping (the guard device replaces the completion of the filtration).
-/

noncomputable section

open Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- Radial Cauchy guard on `[0,v]` with rate `C y^δ`. -/
def RadGuard (W : ℝ → ℝ) (δ C v : ℝ) : Prop :=
  ∀ t ∈ Icc 0 v, ∀ y ∈ Ioc (0 : ℝ) 1, ∀ y' ∈ Ioc 0 y,
    dist (fwdMapInv W t (y * Complex.I)) (fwdMapInv W t (y' * Complex.I)) ≤ C * y ^ δ

variable {W : ℝ → ℝ} {δ C : ℝ}

lemma RadGuard.mono {v v' : ℝ} (h : RadGuard W δ C v) (hv : v' ≤ v) : RadGuard W δ C v' :=
  fun t ht => h t ⟨ht.1, ht.2.trans hv⟩

lemma eventually_rpow_small (hδ : 0 < δ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝[>] (0 : ℝ), C * y ^ δ < ε := by
  have h : Tendsto (fun y : ℝ => C * y ^ δ) (𝓝 0) (𝓝 (C * (0 : ℝ) ^ δ)) :=
    tendsto_const_nhds.mul (Real.continuousAt_rpow_const 0 δ (Or.inr hδ.le)).tendsto
  rw [Real.zero_rpow hδ.ne', mul_zero] at h
  exact nhdsWithin_le_nhds (h (Iio_mem_nhds hε))

/-- Under the guard, the radial limit exists with rate `C y^δ`. -/
theorem RadGuard.dist_trace_le {v : ℝ} (hδ : 0 < δ) (h : RadGuard W δ C v) {t : ℝ}
    (ht : t ∈ Icc 0 v) {y : ℝ} (hy : y ∈ Ioc (0 : ℝ) 1) :
    dist (fwdMapInv W t (y * Complex.I)) (trace W t) ≤ C * y ^ δ := by
  set F : ℝ → ℂ := fun y => fwdMapInv W t (y * Complex.I) with hF
  have hcau : Cauchy (map F (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨y0, hy0C, hy0⟩ :=
      ((eventually_rpow_small (C := C) hδ (half_pos hε)).and (Ioc_mem_nhdsGT one_pos)).exists
    refine ⟨F '' Ioo 0 y0, image_mem_map (Ioo_mem_nhdsGT hy0.1), ?_⟩
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := h t ht y0 hy0 a ⟨ha.1, ha.2.le⟩
    have h2 := h t ht y0 hy0 b ⟨hb.1, hb.2.le⟩
    calc dist (F a) (F b) ≤ dist (F a) (F y0) + dist (F y0) (F b) := dist_triangle _ _ _
      _ ≤ C * y0 ^ δ + C * y0 ^ δ := add_le_add (by rw [dist_comm]; exact h1) h2
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.1 hcau
  have htr : trace W t = L := hL.limUnder_eq
  rw [htr]
  have hlim : Tendsto (fun y' => dist (F y) (F y')) (𝓝[>] 0) (𝓝 (dist (F y) L)) :=
    tendsto_const_nhds.dist hL
  refine le_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT hy.1] with y' hy'
  exact h t ht y hy y' ⟨hy'.1, hy'.2.le⟩

/-- **The guard gives continuity of the trace on `[0,v]`.** -/
theorem RadGuard.continuousOn (hW : Continuous W) (hW0 : W 0 = 0) (hδ : 0 < δ) {v : ℝ}
    (h : RadGuard W δ C v) : ContinuousOn (trace W) (Icc 0 v) := by
  by_cases hv : 0 ≤ v
  swap
  · rw [Icc_eq_empty (by linarith)]; exact continuousOn_empty _
  have hyn : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  refine TendstoUniformlyOn.continuousOn
    (F := fun (n : ℕ) (t : ℝ) => fwdMapInv W t (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
    (p := atTop) ?_ (Frequently.of_forall fun n =>
      RS.continuousOn_fwdMapInv_mul_I hW hW0 (y := 1 / ((n : ℝ) + 1)) (by positivity) hv)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hyn.eventually (eventually_rpow_small (C := C) hδ hε)] with n hn t ht
  have hy : 1 / ((n : ℝ) + 1) ∈ Ioc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [dist_comm]
  exact (h.dist_trace_le hδ ht hy).trans_lt hn

/-- **The guard is closed from the left.** -/
theorem radGuard_of_lt (hW : Continuous W) (hW0 : W 0 = 0) {v : ℝ} (hv : 0 < v)
    (h : ∀ v' < v, RadGuard W δ C v') : RadGuard W δ C v := by
  intro t ht y hy y' hy'
  rcases ht.2.lt_or_eq with htv | rfl
  · exact h ((t + v) / 2) (by linarith) t ⟨ht.1, by linarith⟩ y hy y' hy'
  · have hc1 := RS.continuousOn_fwdMapInv_mul_I hW hW0 hy.1 ht.1
    have hc2 := RS.continuousOn_fwdMapInv_mul_I hW hW0 hy'.1 ht.1
    have hcl : t ∈ closure (Ioo 0 t) := by
      rw [closure_Ioo hv.ne]; exact ⟨hv.le, le_rfl⟩
    refine ContinuousWithinAt.closure_le hcl
      ((show ContinuousWithinAt (fun s => dist (fwdMapInv W s (↑y * Complex.I))
        (fwdMapInv W s (↑y' * Complex.I))) (Icc 0 t) t from
        (hc1 t ⟨ht.1, le_rfl⟩).dist (hc2 t ⟨ht.1, le_rfl⟩)).mono Ioo_subset_Icc_self) continuousWithinAt_const
      fun s hs => h ((s + t) / 2) (by linarith [hs.2]) s ⟨hs.1.le, by linarith [hs.2]⟩ y hy y' hy'

/-- Guarded rational hitting predicate (deterministic form of the `𝓕_u`-event). -/
def HitE (W : ℝ → ℝ) (δ C σ : ℝ) (K : Set ℂ) (u : ℝ) : Prop :=
  σ ≤ u ∧ ∀ n : ℕ, ∃ q : ℚ, (q : ℝ) ∈ Icc 0 u ∧ RadGuard W δ C q ∧
    σ < q + 1 / ((n : ℝ) + 1) ∧ ∃ z ∈ K, dist (trace W q) z < 1 / ((n : ℝ) + 1)

/-- **Guarded rational hitting criterion**, for every continuous driver. -/
theorem hitE_iff (hW : Continuous W) (hW0 : W 0 = 0) (hδ : 0 < δ) {σ : ℝ} (hσ : 0 ≤ σ)
    (K : Set ℂ) (u : ℝ) :
    HitE W δ C σ K u ↔ ∃ s ∈ Icc σ u, RadGuard W δ C s ∧ trace W s ∈ closure K := by
  constructor
  · rintro ⟨hσu, h⟩
    choose q hqI hqG hσq z hzK hz using h
    set S : Set ℝ := {v | v ∈ Icc 0 u ∧ RadGuard W δ C v} with hSdef
    have hSb : BddAbove S := ⟨u, fun v hv => hv.1.2⟩
    have hqS : ∀ n, (q n : ℝ) ∈ S := fun n => ⟨hqI n, hqG n⟩
    set m := sSup S with hm
    have hqm : ∀ n, (q n : ℝ) ≤ m := fun n => le_csSup hSb (hqS n)
    have hmG : RadGuard W δ C m := by
      by_cases hex : ∃ n, m ≤ q n
      · obtain ⟨n, hn⟩ := hex; exact (hqG n).mono hn
      · push Not at hex
        have hm0 : 0 < m := lt_of_le_of_lt (hqI 0).1 (hex 0)
        refine radGuard_of_lt hW hW0 hm0 fun v' hv' => ?_
        obtain ⟨w, hwS, hw⟩ := exists_lt_of_lt_csSup ⟨_, hqS 0⟩ hv'
        exact hwS.2.mono hw.le
    have hmu : m ≤ u := csSup_le ⟨_, hqS 0⟩ fun v hv => hv.1.2
    obtain ⟨s, hs, hs0, hsK⟩ := (hit_iff_rat (hmG.continuousOn hW hW0 hδ) K).2
      fun n => ⟨q n, ⟨(hqI n).1, hqm n⟩, hσq n, z n, hzK n, hz n⟩
    exact ⟨s, ⟨hs.1, hs.2.trans hmu⟩, hmG.mono hs.2, hsK⟩
  · rintro ⟨s, hs, hsG, hsK⟩
    refine ⟨hs.1.trans hs.2, fun n => ?_⟩
    obtain ⟨q, hqI, hσq, z, hzK, hz⟩ :=
      (hit_iff_rat (hsG.continuousOn hW hW0 hδ) K).1 ⟨s, ⟨hs.1, le_rfl⟩, hσ.trans hs.1, hsK⟩ n
    exact ⟨q, ⟨hqI.1, hqI.2.trans hs.2⟩, hsG.mono hqI.2, hσq, z, hzK, hz⟩

/-- **The guarded hit set contains its infimum** (for every continuous driver). -/
theorem exists_first_guardedHit (hW : Continuous W) (hW0 : W 0 = 0) (hδ : 0 < δ) {σ : ℝ}
    (hσ : 0 ≤ σ) (K : Set ℂ)
    (hne : ∃ s, σ ≤ s ∧ RadGuard W δ C s ∧ trace W s ∈ closure K) :
    ∃ m, σ ≤ m ∧ RadGuard W δ C m ∧ trace W m ∈ closure K ∧
      ∀ s, σ ≤ s → RadGuard W δ C s → trace W s ∈ closure K → m ≤ s := by
  set A : Set ℝ := {s | σ ≤ s ∧ RadGuard W δ C s ∧ trace W s ∈ closure K} with hA
  have hAne : A.Nonempty := hne
  have hAb : BddBelow A := ⟨σ, fun s hs => hs.1⟩
  set m := sInf A with hm
  obtain ⟨s0, hs0⟩ := hAne
  have hmσ : σ ≤ m := le_csInf ⟨s0, hs0⟩ fun s hs => hs.1
  have hms0 : m ≤ s0 := csInf_le hAb hs0
  have hmin : ∀ s, σ ≤ s → RadGuard W δ C s → trace W s ∈ closure K → m ≤ s :=
    fun s h1 h2 h3 => csInf_le hAb ⟨h1, h2, h3⟩
  refine ⟨m, hmσ, hs0.2.1.mono hms0, ?_, hmin⟩
  rcases hms0.lt_or_eq with hlt | heq
  · obtain ⟨x, -, hxlim, hxA⟩ := exists_seq_tendsto_sInf ⟨s0, hs0⟩ hAb
    have hcont := hs0.2.1.continuousOn hW hW0 hδ
    have hev : ∀ᶠ k in atTop, x k ∈ Icc 0 s0 := by
      filter_upwards [hxlim.eventually (Iio_mem_nhds hlt)] with k hk
      exact ⟨hσ.trans (hxA k).1, hk.le⟩
    have hlim : Tendsto (fun k => trace W (x k)) atTop (𝓝 (trace W m)) :=
      (hcont m ⟨hσ.trans hmσ, hms0⟩).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hxlim, hev⟩)
    exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun k => (hxA k).2.2)
  · rw [heq]; exact hs0.2.2

end LWFar
end Thm18Asm
end QuantumZipper

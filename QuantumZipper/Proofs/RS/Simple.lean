import QuantumZipper.Proofs.RS.TipA
import QuantumZipper.Proofs.RS.GenerationCor
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# EXT-RS nodes SIM and HULL: the SLE trace is simple and generates the hulls (κ ≤ 4)

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, nodes **SIM** and **HULL** (task RS-TIP-SIM).

* `trace_mem_H_of_good`, `injOn_trace_of_good` (deterministic SIM): for `0 < t₁ < t₂` take
  `u ∈ (t₁,t₂)` in a dense set of good times; `η t₁ ∈ K_u`, while `η t₂ = f̂_u(ηᵘ(t₂ − u))`
  lies in `ℍ \ K_u` (P3(b)), since `ηᵘ(t₂ − u) ∈ ℍ` (NR and TIP for the shifted driver).
* **SIM** `ae_sleTrace_simple` (κ ≤ 4, TIP for all Brownian motions on `Ω` as hypothesis) and
  `ae_sleTrace_simple_of_lt_four` (κ < 4, TIP-a).
* **HULL** `ae_fwdHull_eq_sleTrace_image` (κ ≤ 4, TIP as hypothesis) and
  `ae_fwdHull_eq_sleTrace_image_of_lt_four` (κ < 4, unconditional):
  `K_t = η '' (0,t]` for all `t ≥ 0`. `⊆` by GEN-c, with `interior K_t = ∅` from DF-2
  (`ae_measure_fwdHull_eq_zero`: `K_n` is Lebesgue-null); `⊇` by TR5 and SIM.

GEN-c is RS-GEN's `fwdHull_subset_trace_image_of_interior_eq_empty` (`GenerationCor.lean`).

Sources: Rohde–Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 6.1 and its
proof (p. 23), Exercise 6.7 (p. 30); Kemppainen (2017), Prop 5.3 (p. 81) and Prop 5.8 (p. 86);
Lawler (2005), Prop 6.9 (p. 128).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Complex Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

variable {W : ℝ → ℝ}

/-! ## Deterministic SIM -/

theorem trace_mem_H_of_good (hW : RadialGood W) (hnr : NoRealHitDet W)
    (htip : ∀ t > (0 : ℝ), trace W t ≠ 0) {t : ℝ} (ht : 0 < t) : trace W t ∈ H := by
  rcases trace_mem_fwdHull_or_real hW.1 hW.2.1 ht.le (hW.tendsto ht.le) with h | h
  · exact (fwdHull_mono.2 t) h
  · exact absurd (hnr t ht h) (htip t ht)

theorem trace_mem_fwdHull_of_good (hW : RadialGood W) (hnr : NoRealHitDet W)
    (htip : ∀ t > (0 : ℝ), trace W t ≠ 0) {t : ℝ} (ht : 0 < t) : trace W t ∈ fwdHull W t := by
  rcases trace_mem_fwdHull_or_real hW.1 hW.2.1 ht.le (hW.tendsto ht.le) with h | h
  · exact h
  · exact absurd (hnr t ht h) (htip t ht)

theorem trace_ne_of_lt_of_good (hW : RadialGood W) (hnr : NoRealHitDet W)
    (htip : ∀ t > (0 : ℝ), trace W t ≠ 0) {D : Set ℝ} (hD : Dense D)
    (hgood : ∀ u ∈ D, 0 < u → RadialGood (shiftDrive W u) ∧ NoRealHitDet (shiftDrive W u) ∧
      ∀ t > (0 : ℝ), trace (shiftDrive W u) t ≠ 0)
    {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ < t₂) : trace W t₁ ≠ trace W t₂ := by
  rcases h1.lt_or_eq with h1 | h1
  · obtain ⟨u, huD, hu1, hu2⟩ := hD.exists_between h12
    have hu0 : 0 < u := h1.trans hu1
    obtain ⟨hV, hVnr, hVtip⟩ := hgood u huD hu0
    have hsu : 0 < t₂ - u := sub_pos.2 hu2
    have hK : trace W t₁ ∈ fwdHull W u :=
      fwdHull_mono.1 hu1.le (trace_mem_fwdHull_of_good hW hnr htip h1)
    have hpH := trace_mem_H_of_good hV hVnr hVtip hsu
    have h3 := (trace_add_of_tendsto_shift hW.1 hW.2.1 hu0.le hsu.le hpH (hV.tendsto hsu.le)).2.2
    rw [show u + (t₂ - u) = t₂ by ring] at h3
    have hc := fwdMapInv_mem_compl_fwdHull hW.1 hW.2.1 hu0.le hpH
    rw [← h3] at hc
    intro heq
    exact hc.2 (heq ▸ hK)
  · subst h1
    rw [hW.2.2.1]
    exact (htip t₂ (by linarith)).symm

theorem injOn_trace_of_good (hW : RadialGood W) (hnr : NoRealHitDet W)
    (htip : ∀ t > (0 : ℝ), trace W t ≠ 0) {D : Set ℝ} (hD : Dense D)
    (hgood : ∀ u ∈ D, 0 < u → RadialGood (shiftDrive W u) ∧ NoRealHitDet (shiftDrive W u) ∧
      ∀ t > (0 : ℝ), trace (shiftDrive W u) t ≠ 0) :
    InjOn (trace W) (Ici 0) := by
  intro a ha b hb hab
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact trace_ne_of_lt_of_good hW hnr htip hD hgood ha h hab
  · exact trace_ne_of_lt_of_good hW hnr htip hD hgood hb h hab.symm

/-! ## Deterministic HULL -/

theorem fwdHull_eq_trace_image_of_good (hW : RadialGood W)
    (hH : ∀ t > (0 : ℝ), trace W t ∈ fwdHull W t)
    {t : ℝ} (ht : 0 ≤ t) (hint : interior (fwdHull W t) = ∅) :
    fwdHull W t = trace W '' Ioc 0 t := by
  refine subset_antisymm (fun z hz => ?_) ?_
  · obtain ⟨s, hs, rfl⟩ := fwdHull_subset_trace_image_of_interior_eq_empty hW.1 hW.2.1 ht
      (tendstoUniformlyOn_trace hW t) (hW.2.2.2.1.mono Icc_subset_Ici_self) hint hz
    rcases hs.1.lt_or_eq with hs0 | hs0
    · exact ⟨s, ⟨hs0, hs.2⟩, rfl⟩
    · exfalso
      have hzH := (fwdHull_mono.2 t) hz
      rw [← hs0, hW.2.2.1] at hzH
      exact lt_irrefl _ (show (0 : ℂ).im > 0 from hzH)
  · rintro _ ⟨s, hs, rfl⟩
    exact fwdHull_mono.1 hs.2 (hH s hs.1)

/-! ## Almost sure statements -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- TR4, NR and TIP for the driver and for all shifted drivers at rational times. -/
theorem ae_good_all_shifts [IsProbabilityMeasure P] (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (htip : ∀ B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B' P →
      ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), sleTrace κ B' ω t ≠ 0) :
    ∀ᵐ ω ∂P, RadialGood (drive κ B ω) ∧ NoRealHitDet (drive κ B ω) ∧
      (∀ t > (0 : ℝ), trace (drive κ B ω) t ≠ 0) ∧
      ∀ u ∈ range ((↑) : ℚ → ℝ), 0 < u →
        RadialGood (shiftDrive (drive κ B ω) u) ∧ NoRealHitDet (shiftDrive (drive κ B ω) u) ∧
        ∀ t > (0 : ℝ), trace (shiftDrive (drive κ B ω) u) t ≠ 0 := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, 0 < (q : ℝ) →
      RadialGood (shiftDrive (drive κ B ω) q) ∧ NoRealHitDet (shiftDrive (drive κ B ω) q) ∧
      ∀ t > (0 : ℝ), trace (shiftDrive (drive κ B ω) q) t ≠ 0 := by
    intro q
    set s : ℝ≥0 := (q : ℝ).toNNReal
    have hB' := (isBrownianReal_shift_indep hB κ s).1
    filter_upwards [ae_shift_good hB hκ hκ4 s, htip _ hB', hB.cont] with ω hs htω hBc hq0
    have hsq : ((s : ℝ)) = q := Real.coe_toNNReal _ hq0.le
    rw [hsq] at hs
    refine ⟨hs.1, hs.2, fun t ht => ?_⟩
    rw [← hsq, ← sleTrace_shift_eq κ s hBc ht.le]
    exact htω t ht
  filter_upwards [ae_radialGood_drive hB hκ (by linarith), ae_sleTrace_real_eq_zero hB hκ hκ4,
    htip B hB, ae_all_iff.2 hq] with ω hg hnr htω hqω
  refine ⟨hg, hnr, htω, ?_⟩
  rintro _ ⟨q, rfl⟩ hq0
  exact hqω q hq0

/-- **SIM (EXT-RS).** For `0 < κ ≤ 4`, given TIP for every Brownian motion on `Ω`, almost surely
the SLE trace is injective on `[0,∞)` and lies in `ℍ` at positive times. RS Thm 6.1 (p. 23);
Kemppainen Prop 5.3 (p. 81); Lawler Prop 6.9 (p. 128). -/
theorem ae_sleTrace_simple [IsProbabilityMeasure P] (hB : IsBrownianReal B P) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (htip : ∀ B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B' P →
      ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), sleTrace κ B' ω t ≠ 0) :
    ∀ᵐ ω ∂P, InjOn (sleTrace κ B ω) (Ici 0) ∧ ∀ t > (0 : ℝ), sleTrace κ B ω t ∈ H := by
  filter_upwards [ae_good_all_shifts hB hκ hκ4 htip] with ω ⟨hg, hnr, htω, hsh⟩
  exact ⟨injOn_trace_of_good hg hnr htω Rat.denseRange_cast hsh,
    fun t ht => trace_mem_H_of_good hg hnr htω ht⟩

/-- DF-2 for all times at once: a.s. every hull has empty interior (`κ ≤ 4`). -/
theorem ae_interior_fwdHull_eq_empty [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, interior (fwdHull (drive κ B ω) t) = ∅ := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hB'pre : IsPreBrownianReal B' P :=
    hB.toIsPreBrownianReal.congr fun t => hB'eq.mono fun ω h => (h t).symm
  have hn : ∀ n : ℕ, ∀ᵐ ω ∂P, (volume : Measure ℂ) (fwdHull (drive κ B' ω) n) = 0 := fun n =>
    NonSwallow.ae_measure_fwdHull_eq_zero hB'pre hB'm hB'c hκ hκ4 volume n
  filter_upwards [ae_all_iff.2 hn, hB'eq] with ω hω heq t
  have hdr : drive κ B ω = drive κ B' ω := by funext r; simp [drive, heq]
  rw [hdr]
  have hsub : interior (fwdHull (drive κ B' ω) t) ⊆ fwdHull (drive κ B' ω) ⌈t⌉₊ :=
    interior_subset.trans (fwdHull_mono.1 (Nat.le_ceil t))
  exact (isOpen_interior.measure_eq_zero_iff volume).1 (measure_mono_null hsub (hω _))

/-- **HULL (EXT-RS).** For `0 < κ ≤ 4`, given TIP for every Brownian motion on `Ω`,
almost surely `K_t = η '' (0,t]` for all `t ≥ 0`. RS Thm 6.1 (p. 23) and Exercise 6.7 (p. 30);
Kemppainen Prop 5.8 (p. 86) supplies one ingredient only (AUDIT11 P11-9). -/
theorem ae_fwdHull_eq_sleTrace_image [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (htip : ∀ B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B' P →
      ∀ᵐ ω ∂P, ∀ t > (0 : ℝ), sleTrace κ B' ω t ≠ 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → fwdHull (drive κ B ω) t = sleTrace κ B ω '' Ioc 0 t := by
  filter_upwards [ae_good_all_shifts hB hκ hκ4 htip, ae_interior_fwdHull_eq_empty hB hκ hκ4]
    with ω hgood hint t ht
  obtain ⟨hg, hnr, htω, -⟩ := hgood
  exact fwdHull_eq_trace_image_of_good hg
    (fun s hs => trace_mem_fwdHull_of_good hg hnr htω hs) ht (hint t)

end RS
end QuantumZipper

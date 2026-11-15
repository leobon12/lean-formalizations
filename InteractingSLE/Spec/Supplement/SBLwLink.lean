/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLvStage
import InteractingSLE.Spec.Supplement.SBLvStageGeom
import InteractingSLE.Spec.Restart.ClockInv
import InteractingSLE.Spec.Restart.ClockTrace

/-!
# S5's relative step from SB2(1)'s link

Packet PROVE-T14-SBLEAVES2, item (1) of `planning/handoffs/PROVE-T14-SBLEAVES.md` §8.4. SB2(1) in launch form
(`Lv.SB2UpperLaunchStatement`, ruling R87) links the relative upper curve `ηr` to the actual upper flow `η` by
`Lv.IsRemainderLink`: a continuous increasing clock `σL` from relative to physical time, with
`c⁻¹ (ηr s) = η (t_L + σL s)` whenever `ηr s ∈ ℍ`. Lemma S5's relative step (`Erase.erasureStep_of_relative_clocks`)
needs the identity the other way round and at every time: `g (ηr (σ s)) = η (t_L + s)` for every physical
`s ≤ a − t_L`, with `g` the boundary extension of `c⁻¹` and `σ` a continuous increasing clock.

* `firstVisit_spec`: the first visit is attained (`η t_L = L`, S5's `hL`);
* `add_clock_le`: the clock stays in the physical range on the whole relative range;
* `exists_relClock_of_link`: the inverse clock `σ` (`Restart.invClock`) and the pointwise identity, extended from
  interior relative times by continuity (`Lv.eqOn_Icc_of_dense_H`). The relative range reaches `a − t_L`: either the
  relative lifetime is finite (then the link's lifetime clause gives it), or the relative curve is transient and
  the boundary map is proper (`SB.exists_norm_le_norm_g`), which forbids a bounded physical clock.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Lw

open Lv

/-- **The first visit is attained** for a curve continuous on its available range. -/
theorem firstVisit_spec {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {z : ℂ} (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hv : firstVisit η ζ z < ⊤) :
    ((firstVisit η ζ z).toNNReal : ℝ≥0∞) = firstVisit η ζ z ∧
      ((firstVisit η ζ z).toNNReal : ℝ≥0∞) ≤ ζ ∧ η (firstVisit η ζ z).toNNReal = z := by
  set S : Set ℝ≥0 := {s | (s : ℝ≥0∞) ≤ ζ ∧ η s = z} with hS
  have hne : S.Nonempty := by
    by_contra hS0
    rw [not_nonempty_iff_eq_empty] at hS0
    apply hv.ne
    refine iInf_eq_top.2 fun s => iInf_eq_top.2 fun hs => ?_
    exact absurd (show s ∈ S from hs) (by rw [hS0]; exact notMem_empty s)
  have hcl : IsClosed S := by
    have h1 : IsClosed {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} := isClosed_le ENNReal.continuous_coe continuous_const
    exact hη.preimage_isClosed_of_isClosed h1 isClosed_singleton
  have hmem := hcl.csInf_mem hne (OrderBot.bddBelow S)
  have heq : firstVisit η ζ z = ((sInf S : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_sInf hne]; rfl
  rw [heq, ENNReal.toNNReal_coe]
  exact ⟨rfl, hmem.1, hmem.2⟩

/-- **The clock stays in the physical range** on the whole relative range `[0, ζr]` (`0 < ζr`), by continuity at a
finite relative lifetime. -/
theorem add_clock_le {σL : ℝ≥0 → ℝ≥0} {tL : ℝ≥0} {ζ ζr : ℝ≥0∞} (hσc : Continuous σL)
    (hiff : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζr ↔ ((tL + σL s : ℝ≥0) : ℝ≥0∞) < ζ) (hζr : 0 < ζr) {s : ℝ≥0}
    (hs : (s : ℝ≥0∞) ≤ ζr) : ((tL + σL s : ℝ≥0) : ℝ≥0∞) ≤ ζ := by
  rcases hs.lt_or_eq with hlt | heq
  · exact ((hiff s).1 hlt).le
  · have hs0 : 0 < s := by
      rw [← ENNReal.coe_lt_coe, heq]; simpa using hζr
    have : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨0, hs0⟩
    have hcont : Tendsto (fun r => ((tL + σL r : ℝ≥0) : ℝ≥0∞)) (𝓝[<] s)
        (𝓝 ((tL + σL s : ℝ≥0) : ℝ≥0∞)) :=
      ((ENNReal.continuous_coe.comp (continuous_const.add hσc)).tendsto s).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hcont ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact ((hiff r).1 (heq ▸ ENNReal.coe_lt_coe.2 hr)).le

/-- **S5's `hrel` from SB2(1)'s link.** Let `ηr` be a relative curve, continuous on its range `[0, ζr]` in `ℍ̄`, with
dense interior times, transient if `ζr = ∞`; let `g` be a continuous boundary extension of `c⁻¹` that is proper
(`‖w‖ ≤ C₁‖g w‖ + C₂`). If `ηr` is linked to `η` after its first visit `t_L` to `L`, then for every physical stop
`a ≤ ζ` there is a continuous increasing clock `σ` on `[0, a − t_L]`, `σ 0 = 0`, staying in the relative range, with
`g (ηr (σ s)) = η (t_L + s)` at every `s ≤ a − t_L`. -/
theorem exists_relClock_of_link {c : Chart} {g : ℂ → ℂ} {η ηr : ℝ≥0 → ℂ} {ζ ζr : ℝ≥0∞} {L : ℝ}
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ}) (hηr : ContinuousOn ηr {t | (t : ℝ≥0∞) ≤ ζr})
    (hηrH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζr → 0 ≤ (ηr s).im)
    (hdense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζr → ∃ s ∈ Ioo a b, ηr s ∈ H)
    (hprop : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂)
    (htr : ζr = ⊤ → Tendsto (fun s => ‖ηr s‖) atTop atTop)
    (hlink : IsRemainderLink c η ζ L ηr ζr) (hv : firstVisit η ζ L < ζ) {a : ℝ≥0} (ha : (a : ℝ≥0∞) ≤ ζ) :
    ∃ σ : ℝ≥0 → ℝ≥0, ContinuousOn σ (Iic (a - (firstVisit η ζ L).toNNReal)) ∧
      StrictMonoOn σ (Iic (a - (firstVisit η ζ L).toNNReal)) ∧ σ 0 = 0 ∧
      (σ (a - (firstVisit η ζ L).toNNReal) : ℝ≥0∞) ≤ ζr ∧
      ∀ s : ℝ≥0, s ≤ a - (firstVisit η ζ L).toNNReal →
        g (ηr (σ s)) = η ((firstVisit η ζ L).toNNReal + s) := by
  set tL := (firstVisit η ζ L).toNNReal with htL
  set d := a - tL with hd
  obtain ⟨σL, hσ0, hσm, hσc, hσ⟩ := hlink hv
  have hiff : ∀ s : ℝ≥0, (s : ℝ≥0∞) < ζr ↔ ((tL + σL s : ℝ≥0) : ℝ≥0∞) < ζ := fun s => (hσ s).1
  have htLζ : (tL : ℝ≥0∞) < ζ := by
    rw [htL, ENNReal.coe_toNNReal (hv.trans_le le_top).ne]; exact hv
  have hζr0 : 0 < ζr := by
    have h0 := (hiff 0).2 (by rw [hσ0, add_zero]; exact htLζ)
    simpa using h0
  have hle : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζr → ((tL + σL s : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun s hs =>
    add_clock_le hσc hiff hζr0 hs
  -- the relative range reaches `d`
  have hreach : ∃ s₁ : ℝ≥0, (s₁ : ℝ≥0∞) ≤ ζr ∧ d ≤ σL s₁ := by
    by_cases hd0 : d = 0
    · exact ⟨0, by simp, by rw [hd0]; exact zero_le⟩
    by_cases hζr : ζr = ⊤
    · by_contra hno
      push Not at hno
      have hlt : ∀ s, σL s < d := fun s => hno s (by rw [hζr]; exact le_top)
      have htla : tL < a := tsub_pos_iff_lt.1 (pos_iff_ne_zero.2 hd0)
      have hcpt : IsCompact (η '' Icc 0 a) :=
        isCompact_Icc.image_of_continuousOn (hη.mono fun t ht => (ENNReal.coe_le_coe.2 ht.2).trans ha)
      obtain ⟨M, hM⟩ := hcpt.isBounded.exists_norm_le
      obtain ⟨C₁, C₂, hC₁, hC⟩ := hprop
      obtain ⟨S, hS⟩ := eventually_atTop.1 ((htr hζr).eventually (eventually_gt_atTop (C₁ * M + C₂)))
      obtain ⟨s, hs, hsH⟩ := hdense S (S + 1) (lt_add_one S) (by rw [hζr]; exact le_top)
      have hsζ : (s : ℝ≥0∞) < ζr := by rw [hζr]; exact ENNReal.coe_lt_top
      have hgs : g (ηr s) = η (tL + σL s) := (hgi hsH).trans ((hσ s).2 hsζ hsH)
      have hmemI : tL + σL s ∈ Icc 0 a := by
        refine ⟨zero_le, ?_⟩
        have h1 : tL + σL s < tL + d := add_lt_add_right (hlt s) tL
        rw [hd, add_tsub_cancel_of_le htla.le] at h1
        exact h1.le
      have hbd := hM _ ⟨_, hmemI, rfl⟩
      have h1 := hC (ηr s) (le_of_lt (show (0 : ℝ) < (ηr s).im from hsH))
      have h2 := hS s hs.1.le
      rw [hgs] at h1
      have h3 := mul_le_mul_of_nonneg_left hbd hC₁
      linarith
    · refine ⟨ζr.toNNReal, (ENNReal.coe_toNNReal hζr).le, ?_⟩
      have hnot : ¬ ((tL + σL ζr.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun h =>
        lt_irrefl ζr (by simpa [ENNReal.coe_toNNReal hζr] using (hiff ζr.toNNReal).2 h)
      have h1 : (a : ℝ≥0∞) ≤ ((tL + σL ζr.toNNReal : ℝ≥0) : ℝ≥0∞) := ha.trans (not_lt.1 hnot)
      exact tsub_le_iff_left.2 (ENNReal.coe_le_coe.1 h1)
  obtain ⟨s₁, hs₁ζ, hds₁⟩ := hreach
  obtain ⟨s₀, hs₀I, hs₀⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ s₁) hσc.continuousOn
    ⟨by rw [hσ0]; exact zero_le, hds₁⟩
  have hs₀ζ : (s₀ : ℝ≥0∞) ≤ ζr := (ENNReal.coe_le_coe.2 hs₀I.2).trans hs₁ζ
  -- the inverse clock
  have hclk : Restart.IsClockOn (fun s => (σL s : ℝ)) (s₀ : ℝ≥0∞) :=
    ⟨by simp [hσ0], fun x _ y _ hxy => NNReal.coe_lt_coe.2 (hσm hxy),
      (NNReal.continuous_coe.comp hσc).continuousOn, fun h => absurd h ENNReal.coe_ne_top⟩
  have hdom : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ Restart.capLife (fun s => (σL s : ℝ)) (s₀ : ℝ≥0∞)} = Iic d := by
    ext u
    simp [Restart.capLife, hs₀]
  set σ := Restart.invClock (fun s => (σL s : ℝ)) (s₀ : ℝ≥0∞) with hσdef
  have hspec : ∀ u ∈ Iic d, σ u ≤ s₀ ∧ σL (σ u) = u := by
    intro u hu
    rw [← hdom] at hu
    obtain ⟨h1, h2⟩ := hclk.invClock_spec hu
    exact ⟨ENNReal.coe_le_coe.1 h1, NNReal.coe_injective h2⟩
  -- the identity on `[0, T]`, `s₀ ≤ T ≤ ζr`, `0 < T`
  obtain ⟨ε, hε0, hεζ⟩ : ∃ ε : ℝ≥0, 0 < ε ∧ (ε : ℝ≥0∞) ≤ ζr := by
    by_cases hζr : ζr = ⊤
    · exact ⟨1, one_pos, by rw [hζr]; exact le_top⟩
    · refine ⟨ζr.toNNReal, ?_, (ENNReal.coe_toNNReal hζr).le⟩
      exact ENNReal.toNNReal_pos hζr0.ne' hζr
  set T := max s₀ ε with hT
  have hTζ : (T : ℝ≥0∞) ≤ ζr := by
    rw [hT, ENNReal.coe_max]; exact max_le hs₀ζ hεζ
  have hT0 : 0 < T := lt_of_lt_of_le hε0 (le_max_right _ _)
  have hEq : EqOn (fun s => g (ηr s)) (fun s => η (tL + σL s)) (Icc 0 T) := by
    refine eqOn_Icc_of_dense_H (γ := fun s => if (s : ℝ≥0∞) < ζr then ηr s else 0) hT0 ?_ ?_ ?_ ?_
    · exact hgc.comp (hηr.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2).trans hTζ)
        fun s hs => hηrH s ((ENNReal.coe_le_coe.2 hs.2).trans hTζ)
    · exact hη.comp (continuous_const.add hσc).continuousOn
        fun s hs => hle s ((ENNReal.coe_le_coe.2 hs.2).trans hTζ)
    · intro a' b' hab hbT
      obtain ⟨s, hs, hsH⟩ := hdense a' b' hab ((ENNReal.coe_le_coe.2 hbT).trans hTζ)
      have hsζ : (s : ℝ≥0∞) < ζr :=
        (ENNReal.coe_lt_coe.2 hs.2).trans_le ((ENNReal.coe_le_coe.2 hbT).trans hTζ)
      exact ⟨s, hs, by simp only [hsζ, ↓reduceIte]; exact hsH⟩
    · intro s _ hsH
      by_cases hsζ : (s : ℝ≥0∞) < ζr
      · simp only [hsζ, ↓reduceIte] at hsH
        exact (hgi hsH).trans ((hσ s).2 hsζ hsH)
      · simp only [hsζ, ↓reduceIte] at hsH
        exact absurd (show (0 : ℝ) < (0 : ℂ).im from hsH) (by simp)
  refine ⟨σ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hdom]; exact hclk.continuousOn_invClock
  · rw [← hdom]; exact hclk.strictMonoOn_invClock
  · have h0 := hclk.invClock_apply (r := 0) (by simp)
    simpa [hσ0] using h0
  · exact (ENNReal.coe_le_coe.2 (hspec d (Set.mem_Iic.2 le_rfl)).1).trans hs₀ζ
  · intro s hs
    obtain ⟨h1, h2⟩ := hspec s hs
    have h3 := hEq ⟨zero_le, h1.trans (le_max_left _ _)⟩
    simp only at h3
    rw [h3, h2]

/-- **Lemma S5's relative step from SB2(1)'s link** (pathwise, in S5's coordinates: the retained set `A = p([0, 1])`
from `0`, the upper curve `η` from `0`, the relative curves `αR` from `w ≥ 0` and `ηr` from `0` in the left entry
chart `c` of `A`). The relative stage ordering at all stops (`Lv.HasRelStageOrdering`'s last clause), the link and
the regularity of `ηr` give the erasure step adding the relative lower piece `g(αR([0, d]))`. -/
theorem erasureStep_of_link {p : ℝ → ℂ} {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} {a : ℝ≥0} {c : Chart} {g : ℂ → ℂ}
    {ηr αR : ℝ≥0 → ℂ} {ζr ζα : ℝ≥0∞} {d : ℝ≥0} {w : ℝ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0) (hpf : ∀ z, (p ⁻¹' {z} ∩ Icc 0 1).Finite)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) (hη0 : η 0 = 0) (hη : ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (ha : (a : ℝ≥0∞) ≤ ζ) (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hηr : ContinuousOn ηr {t | (t : ℝ≥0∞) ≤ ζr}) (hηr0 : ηr 0 = 0)
    (hηrH : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζr → 0 ≤ (ηr s).im)
    (hdense : ∀ a b : ℝ≥0, a < b → (b : ℝ≥0∞) ≤ ζr → ∃ s ∈ Ioo a b, ηr s ∈ H)
    (htr : ζr = ⊤ → Tendsto (fun s => ‖ηr s‖) atTop atTop)
    (hlink : IsRemainderLink c η ζ (realMin (p '' Icc 0 1)) ηr ζr)
    (hv : firstVisit η ζ (realMin (p '' Icc 0 1)) < ζ)
    (hta : (firstVisit η ζ (realMin (p '' Icc 0 1))).toNNReal ≤ a)
    (hw : 0 ≤ w) (hα0 : αR 0 = w) (hdα : (d : ℝ≥0∞) ≤ ζα)
    (hord : ∀ d' a' : ℝ≥0, (d' : ℝ≥0∞) ≤ ζα → (a' : ℝ≥0∞) ≤ ζr → HasOrderedProperCompletions αR d' ηr a') :
    Erase.ErasureStep η a (p '' Icc 0 1) (p '' Icc 0 1 ∪ g '' (αR '' Icc 0 d)) := by
  set L := realMin (p '' Icc 0 1)
  have hAb : Bornology.IsBounded (p '' Icc 0 1) := (isCompact_Icc.image_of_continuousOn hp).isBounded
  have hAc : IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) := by
    refine (isPreconnected_Icc.image p hp).union (0 : ℂ) ⟨0, ⟨le_rfl, zero_le_one⟩, hp0⟩ (by simp) ?_
    exact (convex_halfSpace_im_le 0).isPreconnected
  have hprop := exists_norm_le_norm_g hc hAb hAc hgc hgi
  obtain ⟨σ, hσc, hσm, hσ0, hσζ, hrel⟩ :=
    exists_relClock_of_link hgc hgi hη hηr hηrH hdense hprop htr hlink hv ha
  have hL : η (firstVisit η ζ L).toNNReal = (L : ℂ) :=
    (firstVisit_spec hη (hv.trans_le le_top)).2.2
  have hstep := erasureStep_of_relative_clocks_of_finite (τ := id) (a₁ := d) hp hp0 hpf hpH hη0 hc hgc hgi
    hta hL hηr0 hrel hw hα0 continuousOn_id (strictMono_id.strictMonoOn _) rfl hσc hσm hσ0
    (hord _ _ hdα hσζ)
  simpa only [Function.comp_id] using hstep

end InteractingSLE.Theorem14.SB.Lw

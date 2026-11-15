/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NcClock
import InteractingSLE.Spec.Supplement.SB2VcCongr

/-!
# Locality of the canonical stage values and of the relative clock

Packet PROVE-AUX61-NOJUMP (round 21, D34, component B), deterministic. Before B's time `S` (`S ≤` both lifetimes),
the canonical stage values `Dv.canonVal X x₀ p L` only see the fill of `X`, the offset and the piece on `[0, S]`
(`canonVal_congr_lt`; at a bad time the limit is along the good times, which agree near it). The relative clock at
`t` only sees them before `min t L` (`clockOf_canonVal_congr`: before `L` through continuity at `t`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Nc

open Sec7.PocketTraversal Sec7.Lemma71C Dv

/-- **The canonical stage values before `S` only see the fill, the offset and the piece up to `S`.** -/
theorem canonVal_congr_lt {X X' : Set ℂ} (hX : fillH X = fillH X') (x₀ : ℝ) {p p' : ℝ≥0 → ℂ} {L L' S : ℝ≥0∞}
    (hSL : S ≤ L) (hSL' : S ≤ L') (hp : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ S → p s = p' s) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < S) :
    canonVal X x₀ p L s = canonVal X' x₀ p' L' s := by
  classical
  set U : Set ℝ≥0 := {r | (r : ℝ≥0∞) < S} with hU
  have hUo : IsOpen U := isOpen_lt ENNReal.continuous_coe continuous_const
  have hsU : s ∈ U := hs
  have hGU : canonGood X p L ∩ U = canonGood X' p' L' ∩ U := by
    ext r
    simp only [canonGood, mem_inter_iff, mem_ofPred_eq, hU]
    constructor
    · rintro ⟨⟨-, hr⟩, hrS⟩
      refine ⟨⟨hrS.le.trans hSL', ?_⟩, hrS⟩
      rw [← hp r hrS.le, ← hX]; exact hr
    · rintro ⟨⟨-, hr⟩, hrS⟩
      refine ⟨⟨hrS.le.trans hSL, ?_⟩, hrS⟩
      rw [hp r hrS.le, hX]; exact hr
  have hmem : s ∈ canonGood X p L ↔ s ∈ canonGood X' p' L' := by
    constructor
    · intro h
      have h1 : s ∈ canonGood X p L ∩ U := ⟨h, hsU⟩
      rw [hGU] at h1; exact h1.1
    · intro h
      have h1 : s ∈ canonGood X' p' L' ∩ U := ⟨h, hsU⟩
      rw [← hGU] at h1; exact h1.1
  have hUn : U ∈ 𝓝 s := hUo.mem_nhds hsU
  have hnhds : 𝓝[canonGood X p L] s = 𝓝[canonGood X' p' L'] s := by
    have e1 : 𝓝[canonGood X p L ∩ U] s = 𝓝[canonGood X p L] s :=
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hUn)
    have e2 : 𝓝[canonGood X' p' L' ∩ U] s = 𝓝[canonGood X' p' L'] s :=
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds hUn)
    rw [← e1, ← e2, hGU]
  unfold canonVal
  by_cases hg : s ∈ canonGood X p L
  · simp only [hg, (hmem.1 hg), ↓reduceIte, hp s hs.le, hX]
  · have hg' : s ∉ canonGood X' p' L' := fun h => hg (hmem.2 h)
    simp only [hg, hg', ↓reduceIte, hnhds, hX]
    unfold limUnder
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [mem_nhdsWithin_of_mem_nhds hUn] with r hr
    show (Mo.hullChart (fillH X') x₀).1 (p r) = (Mo.hullChart (fillH X') x₀).1 (p' r)
    rw [hp r (le_of_lt hr)]

/-- The clock of two lifts agreeing before `T`, at times before `T` (with the same lifetime conditions). -/
theorem clockOf_congr_lt {γ γ' : ℝ≥0 → ℂ} {L L' T : ℝ≥0∞} (hγ : ∀ r : ℝ≥0, (r : ℝ≥0∞) < T → γ r = γ' r)
    {s : ℝ≥0} (hs : (s : ℝ≥0∞) < T) (hLL : ∀ s' : ℝ≥0, s' ≤ s → ((s' : ℝ≥0∞) < L ↔ (s' : ℝ≥0∞) < L')) :
    Vc.clockOf γ 0 L s = Vc.clockOf γ' 0 L' s := by
  unfold Vc.clockOf
  refine iSup_congr fun s' => ?_
  rw [zero_add]
  by_cases hs' : s' ≤ s
  · have hc : Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) s' =
        Sec7.Lemma71C.capClock (fun r : ℝ => γ' r.toNNReal) s' := Vc.capClock_congr fun r hr => by
      refine hγ r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hs)
      exact hr.trans (by rw [Real.toNNReal_coe]; exact hs')
    simp only [hs', iSup_pos, hLL s' hs', hc]
  · simp only [hs', iSup_neg, not_false_eq_true]

/-- **The relative clock at `t` only sees the canonical values before `min t L`.** -/
theorem clockOf_canonVal_congr {X X' : Set ℂ} (hX : fillH X = fillH X') {x₀ : ℝ} {p p' : ℝ≥0 → ℂ}
    {L L' : ℝ≥0∞} (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hd' : IsDrivenCurve (canonCurve X' x₀ p' L'))
    (hL : L ≠ 0) (hL' : L' ≠ 0) (t : ℝ≥0) (htL : (t : ℝ≥0∞) < L ↔ (t : ℝ≥0∞) < L')
    (hmin : min (t : ℝ≥0∞) L = min (t : ℝ≥0∞) L')
    (hp : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min (t : ℝ≥0∞) L → p s = p' s) :
    Vc.clockOf (canonVal X x₀ p L) 0 L t = Vc.clockOf (canonVal X' x₀ p' L') 0 L' t := by
  have hloc : ∀ r : ℝ≥0, (r : ℝ≥0∞) < min (t : ℝ≥0∞) L → canonVal X x₀ p L r = canonVal X' x₀ p' L' r :=
    fun r hr => canonVal_congr_lt hX x₀ (min_le_right _ _) (hmin ▸ min_le_right _ _) hp hr
  by_cases ht : (t : ℝ≥0∞) < L
  · have ht' : (t : ℝ≥0∞) < L' := htL.1 ht
    have hmt : min (t : ℝ≥0∞) L = t := min_eq_left ht.le
    rcases eq_zero_or_pos t with h0 | htpos
    · subst h0
      have hc1 := clockOf_canonVal hd hL 0
      have hc2 := clockOf_canonVal hd' hL' 0
      simp only [ht, ↓reduceIte] at hc1
      simp only [ht', ↓reduceIte] at hc2
      rw [hc1, hc2]
      simp only [NNReal.coe_zero, uOf_zero, hd.capClock_zero, hd'.capClock_zero]
    · -- continuity at `t` from the left
      have hc := continuous_clockOf_canonVal hd hL
      have hc' := continuous_clockOf_canonVal hd' hL'
      have hm := Vc.monotone_clockOf (canonVal X x₀ p L) 0 L
      have hm' := Vc.monotone_clockOf (canonVal X' x₀ p' L') 0 L'
      have hsup : ∀ (c : ℝ≥0 → ℝ≥0∞), Continuous c → Monotone c → c t = ⨆ (s : ℝ≥0) (_ : s < t), c s := by
        intro c hcc hcm
        refine le_antisymm ?_ (iSup₂_le fun s hs => hcm hs.le)
        have : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
        refine le_of_tendsto (hcc.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio t))) ?_
        filter_upwards [self_mem_nhdsWithin] with s (hs : s < t)
        exact le_iSup₂_of_le s hs le_rfl
      rw [hsup _ hc hm, hsup _ hc' hm']
      refine iSup_congr fun s => iSup_congr fun hs => ?_
      refine clockOf_congr_lt (T := t) (fun r hr => hloc r (by rw [hmt]; exact hr)) (ENNReal.coe_lt_coe.2 hs)
        fun s' hs' => ?_
      have h1 : (s' : ℝ≥0∞) < L := lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hs'.trans hs.le)) ht
      have h2 : (s' : ℝ≥0∞) < L' := lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hs'.trans hs.le)) ht'
      exact iff_of_true h1 h2
  · have ht' : ¬ (t : ℝ≥0∞) < L' := fun h => ht (htL.2 h)
    rw [not_lt] at ht ht'
    have hLL : L = L' := by rw [min_eq_right ht, min_eq_right ht'] at hmin; exact hmin
    subst hLL
    rw [Vd.clockOf_eq_sup_of_le ht, Vd.clockOf_eq_sup_of_le ht']
    refine iSup_congr fun s => iSup_congr fun hs => ?_
    rw [zero_add] at hs
    have hsm : (s : ℝ≥0∞) < min (t : ℝ≥0∞) L := by rw [min_eq_right ht]; exact hs
    congr 1
    refine Vc.capClock_congr fun r hr => hloc r (lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hsm)
    rwa [Real.toNNReal_coe] at hr

end InteractingSLE.Theorem14.SB.Nc

/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BhEval
import InteractingSLE.Spec.Supplement.GW2BhSep

/-!
# The uncapped gauge rule along a locally regular readout (S3)

Packet PROVE-GW2-BUF (S3; independent of the cap decision recorded in the handoff). `GW2Bh.afterRule_eq` evaluates the
uncapped rule along a readout that is continuous and antitone FOREVER. Along GB6's relative coordinates the readout is
regular only before the first contact. This file localizes the evaluation to a prefix `[0, c₁]`:

* `antitone_compactSeparation`: a compact separation is antitone in the explored time;
* `lt_hitRule_of_forall`: the attained first hit is after every time up to which the readout stays above the level;
* **`afterRule_eq_of_on`**: the uncapped rule is the first hit after `A`, when the readout is continuous and antitone
  on a prefix containing the hit;
* **`lt_afterRule_of_on`**: the uncapped rule is after every time up to which the readout stays above the level.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.GaugeE Supp8.GB6.ReadD Supp8.GB6.HullId Supp8.GB6.RelDrv
  Supp8.GB6.RelDrv.Version

/-- **A compact separation is antitone in the explored time.** -/
theorem antitone_compactSeparation (X A : ℝ≥0 → ℂ) (s : ℝ≥0) :
    Antitone fun t => compactSeparation X A t s := by
  intro t t' htt
  unfold compactSeparation squareMin
  have hsub : range (prefixIntegrand X A t s) ⊆ range (prefixIntegrand X A t' s) := by
    rintro _ ⟨p, rfl⟩
    obtain ⟨y, hy⟩ := exists_unit_mul ((fraction_mul_le t p.1).trans htt)
    exact ⟨(y, p.2), by simp only [prefixIntegrand, hy]⟩
  refine csInf_le_csInf ⟨0, ?_⟩ (range_nonempty _) hsub
  rintro _ ⟨p, rfl⟩
  exact separationValue_nonneg _ _

/-- **The attained first hit is after every time up to which the readout stays above the level** (before the cap). -/
theorem lt_hitRule_of_forall {G : GaugeReadout} {ε : RecData → ℝ} {c : ℝ≥0} {r : RecData} {w : ℝ≥0 → ℝ}
    {t₁ : ℝ≥0} (ht₁c : t₁ < c) (hcont : ContinuousOn (fun u => G u (r, w)) (Icc 0 t₁))
    (hlt : ∀ u ≤ t₁, ε r < G u (r, w)) : (t₁ : ℝ≥0∞) < hitRule G ε c (r, w) := by
  have hnot : (r, w) ∉ prefixHitSet G ε c t₁ := by
    rintro (h | h)
    · exact (not_le.2 ht₁c) h
    · obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
        (show (Icc (0 : ℝ≥0) t₁).Nonempty from ⟨0, zero_le, zero_le⟩) hcont
      have haε : ε r < G a (r, w) := hlt a ha.2
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 haε)
      obtain ⟨q, hqt, hq⟩ := h n
      have hm : G a (r, w) ≤ G q (r, w) := hmin ⟨zero_le, hqt⟩
      change G q (r, w) < ε r + 1 / ((n : ℝ) + 1) at hq
      linarith only [hn, hq, hm]
  have hnot' : ∀ t ≤ t₁, (r, w) ∉ prefixHitSet G ε c t := fun t ht hm =>
    hnot (mem_prefixHitSet_mono ht hm)
  have hinf : t₁ ≤ hitInf G ε c (r, w) := by
    refine le_csInf ⟨c, mem_prefixHitSet_cap (r, w)⟩ fun t ht => ?_
    by_contra hlt'
    exact hnot' t (not_le.1 hlt').le ht
  unfold hitRule
  split_ifs with hm
  · rcases eq_or_lt_of_le hinf with he | he
    · exact absurd (he ▸ hm) hnot
    · exact ENNReal.coe_lt_coe.2 he
  · exact ENNReal.coe_lt_top

section Local

variable {G : GaugeReadout} {A : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} {lev : ℝ → ℝ} {r : RecData} {w : ℝ≥0 → ℝ}
  {a₀ c₁ : ℝ≥0}

/-- The readout frozen after `c₁`. -/
def frozenGauge (G : GaugeReadout) (r : RecData) (w : ℝ≥0 → ℝ) (c₁ : ℝ≥0) (t : ℝ≥0) : ℝ := G (min t c₁) (r, w)

theorem continuous_frozenGauge (hc : ContinuousOn (fun u => G u (r, w)) (Iic c₁)) :
    Continuous (frozenGauge G r w c₁) :=
  hc.comp_continuous (continuous_id.min continuous_const) fun t => min_le_right t c₁

theorem antitone_frozenGauge (hanti : AntitoneOn (fun u => G u (r, w)) (Iic c₁)) :
    Antitone (frozenGauge G r w c₁) := fun t t' htt =>
  hanti (min_le_right t c₁) (min_le_right t' c₁) (min_le_min_right c₁ htt)

theorem frozenGauge_of_le {t : ℝ≥0} (ht : t ≤ c₁) : frozenGauge G r w c₁ t = G t (r, w) := by
  simp only [frozenGauge, min_eq_left ht]

/-- **The uncapped rule is the first hit after `A`** along a readout regular on a prefix containing the hit. -/
theorem afterRule_eq_of_on (hc : ContinuousOn (fun u => G u (r, w)) (Iic c₁))
    (hanti : AntitoneOn (fun u => G u (r, w)) (Iic c₁)) (hA : A (r, w) = a₀)
    (hℓ : 0 < lev (min 1 (G a₀ (r, w)))) (hℓ2 : 2 * lev (min 1 (G a₀ (r, w))) ≤ G a₀ (r, w))
    {h : ℝ≥0} (hah : a₀ ≤ h) (hhc : h < c₁) (hh : G h (r, w) ≤ lev (min 1 (G a₀ (r, w))))
    (hlt : ∀ t, a₀ ≤ t → t < h → lev (min 1 (G a₀ (r, w))) < G t (r, w)) :
    afterRule G A lev (r, w) = h := by
  have ha₀ : frozenGauge G r w c₁ a₀ = G a₀ (r, w) := frozenGauge_of_le (hah.trans hhc.le)
  refine afterRule_eq (g := frozenGauge G r w c₁) (L := c₁) (continuous_frozenGauge hc) (antitone_frozenGauge hanti)
    hA (fun t ht => (frozenGauge_of_le (ENNReal.coe_le_coe.1 ht.le)).symm) (by rwa [ha₀]) (by rwa [ha₀]) hah
    (ENNReal.coe_lt_coe.2 hhc) (by rwa [ha₀, frozenGauge_of_le hhc.le]) fun t ht1 ht2 => ?_
  rw [ha₀, frozenGauge_of_le (ht2.le.trans hhc.le)]
  exact hlt t ht1 ht2

/-- **The uncapped rule is after every time up to which the readout stays above the level**, along a readout
regular on a prefix strictly containing that time. -/
theorem lt_afterRule_of_on (hc : ContinuousOn (fun u => G u (r, w)) (Iic c₁))
    (hanti : AntitoneOn (fun u => G u (r, w)) (Iic c₁)) (hA : A (r, w) = a₀) (ha₀c : a₀ < c₁)
    (hℓ : 0 < lev (min 1 (G a₀ (r, w)))) (hℓ2 : 2 * lev (min 1 (G a₀ (r, w))) ≤ G a₀ (r, w))
    {t₁ : ℝ≥0} (ht₁c : t₁ < c₁) (hlt : ∀ t, a₀ ≤ t → t ≤ t₁ → lev (min 1 (G a₀ (r, w))) < G t (r, w)) :
    (t₁ : ℝ≥0∞) < afterRule G A lev (r, w) := by
  set g := frozenGauge G r w c₁ with hgdef
  have hg := continuous_frozenGauge hc
  have hga : AntitoneOn (fun u => G u (r, w)) (Iic c₁) := hanti
  have ha₀ : g a₀ = G a₀ (r, w) := frozenGauge_of_le ha₀c.le
  set ℓ := lev (min 1 (g a₀)) with hℓdef
  have hℓ' : 0 < ℓ := by rw [hℓdef, ha₀]; exact hℓ
  have hℓ2' : 2 * ℓ ≤ g a₀ := by rw [hℓdef, ha₀]; exact hℓ2
  have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (c₁ : ℝ≥0∞) → G t (r, w) = g t :=
    fun t ht => (frozenGauge_of_le (ENNReal.coe_le_coe.1 ht.le)).symm
  have hn := continuous_normGauge (a₀ := a₀) hg hℓ' hℓ2'
  have hgt : ∀ u ≤ t₁, (1 : ℝ) < normGauge g a₀ ℓ u := fun u hu => not_le.1 fun hle => by
    obtain ⟨h1, h2⟩ := (normGauge_le_one_iff hℓ' u).1 hle
    have := hlt u h1 hu
    rw [← ha₀, ← hℓdef, ← frozenGauge_of_le (G := G) (r := r) (w := w) (hu.trans ht₁c.le)] at this
    exact (not_le.2 this) h2
  obtain ⟨N, hN⟩ := exists_nat_gt (t₁ : ℝ)
  have hNc : t₁ < (N : ℝ≥0) := by exact_mod_cast hN
  have hcontN : ContinuousOn (fun u => afterRead G A lev u (r, w)) (Icc 0 t₁) := by
    refine hn.continuousOn.congr fun u hu => ?_
    exact afterRead_eq hg (antitone_frozenGauge hga) hA (ENNReal.coe_lt_coe.2 ha₀c) hread
      (ENNReal.coe_lt_coe.2 (hu.2.trans_lt ht₁c))
  have hltN : ∀ u ≤ t₁, (fun _ : RecData => (1 : ℝ)) r < afterRead G A lev u (r, w) := by
    intro u hu
    rw [afterRead_eq hg (antitone_frozenGauge hga) hA (ENNReal.coe_lt_coe.2 ha₀c) hread
      (ENNReal.coe_lt_coe.2 (hu.trans_lt ht₁c))]
    exact hgt u hu
  have h1 := lt_hitRule_of_forall (G := afterRead G A lev) (ε := fun _ => 1) (w := w) hNc hcontN hltN
  exact h1.trans_le (le_iSup (fun n : ℕ => hitRule (afterRead G A lev) (fun _ => 1) (n : ℝ≥0) (r, w)) N)

end Local

end InteractingSLE.Theorem14.GW2Bh

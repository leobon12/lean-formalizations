/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2aForceGap
import InteractingSLE.Spec.Sec2.Assembly2Pathwise

/-!
# A collision at a fixed time: pathwise reduction to Bessel zeros and absorbed merges

Packet PROVE-GW2A-FORCE (input of `FlowFixedTimeInteriorStatement`). Deterministic, one integrated path at a time.

Let `t > 0` be before the lifetime and suppose a right force coordinate meets the driver at `t`. Let `{0, …, m−1}`
be the right marks on the driver at `t` (an initial segment, `exists_eq_iff_lt`); their total weight exceeds `−2`
(no continuation threshold at `t`). Call the configuration an **absorbed merge** (`AbsorbedMergeR`) if some
consecutive pair `k, k+1` of these marks has partial sum `2 + S_k ≤ 0` and is still unmerged at every time before
`t` — the trace swallows, exactly at `t`, a boundary gap that it can never touch.

Otherwise every such pair merged before `t`, so on a final interval `[a, t]` (`a` rational) the Abel conditions hold
at the breaks with some rational `c₀ > 0`, the separated marks stay away, and the nearest gap is small; the
comparison (`bessel_mul_sqrt_le_gap`) forces the Bessel path with coefficient `c₀/(2κ)` driven by the Brownian
increments after `a` to vanish at `t − a` (`absorbedMergeR_of_collision`). The probabilistic part
(`GW2aForceFixed`) shows that these countably many Bessel zeros are null events.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Theorem14

namespace GW2aForce

open Sec2

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- The partial sum `S_k = ∑_{i ≤ k} ρ_i` of the right weights. -/
def partialR (ρR : Fin nR → ℝ) (k : Fin nR) : ℝ := ∑ i ∈ univ.filter (fun i : Fin nR => i ≤ k), ρR i

/-- **An absorbed merge on the right at time `t`**: two consecutive right marks `k, k+1` on the driver at `t` with
`2 + S_k ≤ 0` that are unmerged at every earlier time (the gap between them, which the trace can never touch, is
swallowed exactly at `t`). -/
def AbsorbedMergeR (ρR : Fin nR → ℝ) (w : ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  ∃ k k' : Fin nR, k'.val = k.val + 1 ∧ 2 + partialR ρR k ≤ 0 ∧ vR k' t = w t ∧ ∀ s < t, vR k s < vR k' s

/-- The coordinates of a monotone family equal to a lower bound form an initial segment. -/
theorem exists_eq_iff_lt {n : ℕ} (v : Fin n → ℝ) (w : ℝ) (hmono : Monotone v) (hle : ∀ i, w ≤ v i) :
    ∃ m ≤ n, ∀ i : Fin n, v i = w ↔ i.val < m := by
  classical
  have hex : ∃ k, k = n ∨ ∃ h : k < n, v ⟨k, h⟩ ≠ w := ⟨n, Or.inl rfl⟩
  refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · by_contra hlt
    rw [not_lt] at hlt
    rcases Nat.find_spec hex with h | ⟨h, hne⟩
    · omega
    · have h1 : v ⟨Nat.find hex, h⟩ ≤ v i := hmono (by rw [Fin.le_def]; exact hlt)
      exact hne (le_antisymm (h1.trans hi.le) (hle _))
  · have hmin := Nat.find_min hex hi
    push Not at hmin
    exact hmin.2 i.isLt

/-- Finitely many positive numbers have a common positive lower bound. -/
theorem exists_pos_lt_all {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ δ > 0, ∀ i, δ < f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => isEmptyElim i⟩
  · set m := univ.inf' univ_nonempty f
    have hm : 0 < m := (lt_inf'_iff _).2 fun i _ => hf i
    exact ⟨m / 2, by positivity, fun i => by have : m ≤ f i := inf'_le _ (Finset.mem_univ i); linarith⟩

/-- **A right collision at a fixed time is an absorbed merge, unless a Bessel path vanishes** (pathwise). If for all
rationals `q, c` with `c > 0` and `q⁺ < t` the Bessel path `X q c` with coefficient `c/(2κ)` from `0` driven by
`s ↦ −(b(q⁺+s) − b(q⁺))` is nonzero at `t − q⁺`, then every right collision at `t` is an absorbed merge. -/
theorem absorbedMergeR_of_collision (hκ : 0 < κ) (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hF : IsOrderedForceWord xL xR) {t : ℝ≥0} (ht : 0 < t) (htζ : (t : ℝ≥0∞) < ζ) (X : ℚ → ℚ → ℝ≥0 → ℝ)
    (hX : ∀ q c : ℚ, 0 < c → (q : ℝ).toNNReal < t →
      Bessel.IsBesselPath ((c : ℝ) / (2 * κ)) 0 (fun s => -(b ((q : ℝ).toNNReal + s) - b (q : ℝ).toNNReal))
        (X q c) ∧ X q c (t - (q : ℝ).toNNReal) ≠ 0)
    {j : Fin nR} (hj : vR j t = w t) : AbsorbedMergeR ρR w vR t := by
  classical
  by_contra hnot
  have hf := hp.isForcePath
  have hnR : 0 < nR := Fin.pos j
  set j₀ : Fin nR := ⟨0, hnR⟩ with hj₀
  -- the marks on the driver at `t`
  obtain ⟨m, hmn, hmiff⟩ := exists_eq_iff_lt (fun i => vR i t) (w t) (fun _ _ h => hf.monotone_vR htζ h)
    (hf.w_le_vR htζ)
  have hj₀t : vR j₀ t = w t := le_antisymm
    ((hf.monotone_vR htζ (show j₀ ≤ j by rw [Fin.le_def]; exact Nat.zero_le _)).trans hj.le) (hf.w_le_vR htζ j₀)
  have hm : 0 < m := (hmiff j₀).1 hj₀t
  set kM : Fin nR := ⟨m - 1, by omega⟩ with hkM
  -- no threshold at `t`: the colliding group has weight `> −2`
  have hthr : 0 < 2 + partialR ρR kM := by
    have hnt := hf.not_threshold htζ
    simp only [ForceWord.ThresholdCondition, not_or, not_le] at hnt
    have hfil : univ.filter (fun i : Fin nR => vR i t = w t) = univ.filter (fun i : Fin nR => i ≤ kM) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmiff i, Fin.le_def, hkM]
      omega
    have := hnt.2
    rw [hfil] at this
    simp only [partialR]
    linarith
  -- the admissible breaks and the constant `c₀`
  set A := univ.filter (fun k : Fin nR => k.val < m ∧ 0 < 2 + partialR ρR k) with hA
  have hkMA : kM ∈ A := by
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and, hkM]
    exact ⟨by omega, hthr⟩
  set c₀s := A.inf' ⟨kM, hkMA⟩ (fun k => 2 + partialR ρR k) with hc₀s
  have hc₀s : 0 < c₀s := (lt_inf'_iff _).2 fun k hk => (Finset.mem_filter.1 hk).2.2
  obtain ⟨c, hc0, hcs⟩ := exists_rat_btwn hc₀s
  have hc0' : (0 : ℚ) < c := by exact_mod_cast hc0
  have hcA : ∀ k ∈ A, (c : ℝ) ≤ 2 + partialR ρR k := fun k hk => hcs.le.trans (inf'_le _ hk)
  -- the absorbed pairs merged before `t`
  have hmerge : ∀ k : Fin nR, ∃ s : ℝ≥0, s < t ∧ ∀ k' : Fin nR, k'.val = k.val + 1 → k'.val < m →
      2 + partialR ρR k ≤ 0 → vR k s = vR k' s := by
    intro k
    by_cases hex : ∃ k' : Fin nR, k'.val = k.val + 1 ∧ k'.val < m ∧ 2 + partialR ρR k ≤ 0
    · obtain ⟨k', hk', hk'm, hS⟩ := hex
      have hnot' : ¬ ∀ s < t, vR k s < vR k' s := fun hall =>
        hnot ⟨k, k', hk', hS, (hmiff k').2 hk'm, hall⟩
      push Not at hnot'
      obtain ⟨s, hst, hle⟩ := hnot'
      have hsζ : (s : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hst.le) htζ
      have hkk' : k ≤ k' := by rw [Fin.le_def]; omega
      refine ⟨s, hst, fun k'' hk'' _ _ => ?_⟩
      have : k'' = k' := Fin.ext (by omega)
      subst this
      exact le_antisymm (hf.monotone_vR hsζ hkk') hle
    · push Not at hex
      exact ⟨0, ht, fun k' hk' hk'm hS => absurd hS (not_le.2 (hex k' hk' hk'm))⟩
  choose sk hskt hsk using hmerge
  set sStar : ℝ≥0 := univ.sup sk with hsStar
  have hsStar_lt : sStar < t := (Finset.sup_lt_iff ht).2 fun k _ => hskt k
  -- the separation constant at `t`
  have hgap : ∀ i : Fin nR ⊕ Fin nL, 0 < (Sum.elim (fun j' : Fin nR => if m ≤ j'.val then vR j' t - w t else 1)
      (fun i : Fin nL => w t - vL i t) i) := by
    rintro (j' | i)
    · simp only [Sum.elim_inl]
      split_ifs with h
      · have hne : vR j' t ≠ w t := fun he => by have := (hmiff j').1 he; omega
        exact sub_pos.2 (lt_of_le_of_ne (hf.w_le_vR htζ j') (Ne.symm hne))
      · exact one_pos
    · simp only [Sum.elim_inr]
      have := hp.vL_lt_vR_of_pos hF ht htζ i j₀
      rw [hj₀t] at this
      exact sub_pos.2 this
  obtain ⟨δ, hδ, hδlt⟩ := exists_pos_lt_all _ hgap
  set M := sepConst ρL ρR δ with hMdef
  have hM0 : 0 ≤ M := div_nonneg (add_nonneg (sum_nonneg fun j _ => abs_nonneg _)
    (sum_nonneg fun i _ => abs_nonneg _)) hδ.le
  set ε : ℝ := (c : ℝ) / (2 * (M + 1)) with hε
  have hεpos : 0 < ε := div_pos hc0 (by linarith)
  have hεM : ε * M ≤ (c : ℝ) / 2 := by
    rw [hε, div_mul_eq_mul_div, div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  -- the good conditions hold on a left neighbourhood of `t`
  have hopen : {τ : ℝ≥0 | (τ : ℝ≥0∞) < ζ} ∈ 𝓝 t :=
    (isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds htζ
  have hcontR : ∀ j' : Fin nR, ContinuousAt (fun τ => vR j' τ - w τ) t := fun j' =>
    ((hf.continuousOn_vR j').continuousAt hopen).sub (hf.continuousOn_w.continuousAt hopen)
  have hcontL : ∀ i : Fin nL, ContinuousAt (fun τ => w τ - vL i τ) t := fun i =>
    (hf.continuousOn_w.continuousAt hopen).sub ((hf.continuousOn_vL i).continuousAt hopen)
  have hev : ∀ᶠ τ in 𝓝 t, (∀ j' : Fin nR, m ≤ j'.val → δ < vR j' τ - w τ) ∧ (∀ i, δ < w τ - vL i τ) ∧
      vR j₀ τ - w τ < ε := by
    refine (eventually_all.2 fun j' => ?_).and ((eventually_all.2 fun i => ?_).and ?_)
    · by_cases hj' : m ≤ j'.val
      · have h1 := hδlt (Sum.inl j')
        simp only [Sum.elim_inl, hj', ↓reduceIte] at h1
        exact ((hcontR j').eventually (lt_mem_nhds h1)).mono fun τ hτ _ => hτ
      · exact Eventually.of_forall fun τ h => absurd h hj'
    · have h1 := hδlt (Sum.inr i)
      simp only [Sum.elim_inr] at h1
      exact (hcontL i).eventually (lt_mem_nhds h1)
    · have h0 : vR j₀ t - w t < ε := by rw [hj₀t, sub_self]; exact hεpos
      exact (hcontR j₀).eventually (gt_mem_nhds h0)
  obtain ⟨a₀, ha₀t, ha₀⟩ := (mem_nhdsLE_iff_exists_Ioc_subset' ht).1 (nhdsWithin_le_nhds hev)
  -- a rational restart time
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show ((max a₀ sStar : ℝ≥0) : ℝ) < t by
    exact_mod_cast max_lt ha₀t hsStar_lt)
  have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hq1.le
  set a : ℝ≥0 := (q : ℝ).toNNReal with ha
  have hac : (a : ℝ) = q := Real.coe_toNNReal _ hq0
  have hat : a < t := by rw [← NNReal.coe_lt_coe, hac]; exact hq2
  have ha₀a : a₀ < a := by
    rw [← NNReal.coe_lt_coe, hac]; exact lt_of_le_of_lt (by exact_mod_cast le_max_left _ _) hq1
  have hsa : sStar < a := by
    rw [← NNReal.coe_lt_coe, hac]; exact lt_of_le_of_lt (by exact_mod_cast le_max_right _ _) hq1
  have hgood : ∀ τ : ℝ≥0, a ≤ τ → τ ≤ t → (∀ j' : Fin nR, m ≤ j'.val → δ < vR j' τ - w τ) ∧
      (∀ i, δ < w τ - vL i τ) ∧ vR j₀ τ - w τ < ε := fun τ haτ hτt => ha₀ ⟨ha₀a.trans_le haτ, hτt⟩
  -- the Abel conditions at `a`
  have habel : ∀ k : Fin nR, k.val < m →
      (k.val + 1 = m ∨ ∀ k' : Fin nR, k'.val = k.val + 1 → vR k a < vR k' a) →
        (c : ℝ) - 2 ≤ ∑ i ∈ univ.filter (fun i : Fin nR => i ≤ k), ρR i := by
    intro k hk hbr
    by_cases hpos : 0 < 2 + partialR ρR k
    · have := hcA k (by simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hk, hpos⟩)
      simp only [partialR] at this
      linarith
    · exfalso
      rw [not_lt] at hpos
      rcases hbr with h | h
      · have hk' : k = kM := Fin.ext (by simp only [hkM]; omega)
        rw [hk'] at hpos
        linarith
      · have hk1 : k.val + 1 < m := by
          rcases Nat.lt_or_ge (k.val + 1) m with h' | h'
          · exact h'
          · exfalso
            have hkm1 : k.val + 1 = m := by omega
            have hk' : k = kM := Fin.ext (by simp only [hkM]; omega)
            rw [hk'] at hpos; linarith
        set k' : Fin nR := ⟨k.val + 1, by omega⟩ with hk'
        have hmerged := hsk k k' rfl hk1 hpos
        have hsk_a : sk k ≤ a := (le_sup (f := sk) (Finset.mem_univ k)).trans hsa.le
        have haζ : (a : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hat.le) htζ
        have hkk' : k ≤ k' := by rw [Fin.le_def]; simp only [hk']; omega
        have := hf.vR_eq_vR_of_eq hsk_a haζ hkk' hmerged
        exact absurd (h k' rfl) (by rw [this]; exact lt_irrefl _)
  -- the comparison
  obtain ⟨hXB, hXne⟩ := hX q c hc0' hat
  have hcmp := bessel_mul_sqrt_le_gap hκ hp hat.le htζ hnR hm hmn (by exact_mod_cast hc0) hδ hεM
    (fun τ h1 h2 j' hj' => (hgood τ h1 h2).1 j' hj' |>.le) (fun τ h1 h2 i => (hgood τ h1 h2).2.1 i |>.le)
    (fun τ h1 h2 => (hgood τ h1 h2).2.2) habel hXB
  rw [hj₀t, sub_self] at hcmp
  have hXnn := hXB.2.1 (t - a)
  have hsκ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have : X q c (t - a) = 0 := le_antisymm (by nlinarith) hXnn
  exact hXne this

end GW2aForce

end Theorem14

end InteractingSLE

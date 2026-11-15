/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCCMain
import InteractingSLE.Spec.Supplement.GW0
import InteractingSLE.Spec.Supplement.G12Low
import InteractingSLE.Spec.Supplement.G12Statement
import InteractingSLE.Spec.Supplement.S7Weights
import InteractingSLE.Spec.Supplement.RLCIOrder

/-!
# The proved weight and avoidance parts of Lemma G2a

This file proves the G2a reference flow's group-end admissibility, infinite lifetimes, simplicity,
and avoidance of the opposite seed. It supplies the exact parts statement imported from RLCIOrder
when the remaining transience input is available.
-/

set_option autoImplicit false

noncomputable section

universe u

open MeasureTheory Set Filter Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE

namespace RLC

open PiecewiseConstantBoundaryData (leftLim rightLim)

private theorem leftLim_g2aData_w2 {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ} :
    leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₂ = -sleLambda κ - θ₂ * chiC κ := by
  apply Sec4.leftLim_eq_of_forall (a := w₂ - 1)
  · linarith
  · intro t ht
    simp [g2aData, ht.2]

private theorem rightLim_g2aData_w2 {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    (hw : w₂ < w₁)
    (hnear : ∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε →
      m x = sleLambda κ - θ₂ * chiC κ) :
    rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₂ = sleLambda κ - θ₂ * chiC κ := by
  obtain ⟨ε, hε, hnear⟩ := hnear
  let δ := min (ε / 2) ((w₁ - w₂) / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  apply Sec4.rightLim_eq_of_forall (a := w₂ + δ)
  · linarith
  · intro t ht
    have hδε : δ ≤ ε / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδw : δ ≤ (w₁ - w₂) / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    have htε : t < w₂ + ε := by
      calc
        t < w₂ + δ := ht.2
        _ ≤ w₂ + ε / 2 := add_le_add_right hδε w₂
        _ < w₂ + ε := by linarith
    have htw₁ : t < w₁ := by
      calc
        t < w₂ + δ := ht.2
        _ ≤ w₂ + (w₁ - w₂) / 2 := add_le_add_right hδw w₂
        _ < w₁ := by linarith
    rw [show g2aData κ θ₁ θ₂ w₂ w₁ m t = m t by
      simp [g2aData, not_lt.mpr ht.1.le, htw₁]]
    exact hnear t ht.1 htε

private theorem leftLim_g2aData_w1 {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    (hw : w₂ < w₁)
    (hnear : ∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ →
      m x = -sleLambda κ - θ₁ * chiC κ) :
    leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₁ = -sleLambda κ - θ₁ * chiC κ := by
  obtain ⟨ε, hε, hnear⟩ := hnear
  let δ := min (ε / 2) ((w₁ - w₂) / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  apply Sec4.leftLim_eq_of_forall (a := w₁ - δ)
  · linarith
  · intro t ht
    have hδε : δ ≤ ε / 2 := by
      dsimp [δ]
      exact min_le_left _ _
    have hδw : δ ≤ (w₁ - w₂) / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    have htw₂ : w₂ < t := by
      calc
        w₂ < w₂ + (w₁ - w₂) / 2 := by linarith
        _ = w₁ - (w₁ - w₂) / 2 := by ring
        _ ≤ w₁ - δ := by linarith
        _ < t := ht.1
    have htε : w₁ - ε < t := by
      calc
        w₁ - ε < w₁ - ε / 2 := by linarith
        _ ≤ w₁ - δ := by linarith
        _ < t := ht.1
    rw [show g2aData κ θ₁ θ₂ w₂ w₁ m t = m t by
      simp [g2aData, not_lt.mpr htw₂.le, ht.2]]
    exact hnear t htε ht.2

private theorem rightLim_g2aData_w1 {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    (hw : w₂ < w₁) :
    rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₁ = sleLambda κ - θ₁ * chiC κ := by
  apply Sec4.rightLim_eq_of_forall (a := w₁ + 1)
  · linarith
  · intro t ht
    have htw₂ : ¬ t < w₂ := not_lt.mpr (hw.le.trans ht.1.le)
    have htw₁ : ¬ t < w₁ := not_lt.mpr ht.1.le
    simp [g2aData, htw₂, htw₁]

private theorem leftLim_g2aData_middle {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {J : Finset ℝ} (hpc : IsPiecewiseConstantBoundaryData
      (g2aData κ θ₁ θ₂ w₂ w₁ m) J)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ)
    {y : ℝ} (hy₂ : w₂ < y) (hy₁ : y < w₁) :
    -sleLambda κ - θ₂ * chiC κ < leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) y ∧
      leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) y < sleLambda κ - θ₁ * chiC κ := by
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_eq_lims hpc y
  let ε := min (δ / 2) ((y - w₂) / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεδ : ε < δ := by
    dsimp [ε] at *
    have h := min_le_left (δ / 2) ((y - w₂) / 2)
    linarith
  have hyε₂ : w₂ < y - ε := by
    dsimp [ε] at *
    have h := min_le_right (δ / 2) ((y - w₂) / 2)
    linarith
  have hyε₁ : y - ε < w₁ := by linarith
  have hlim := (hδJ ε hε hεδ).2.2.2
  have hdata : g2aData κ θ₁ θ₂ w₂ w₁ m (y - ε) = m (y - ε) := by
    simp [g2aData, not_lt.mpr hyε₂.le, hyε₁]
  rw [hdata] at hlim
  rw [← hlim]
  exact hmid (y - ε) hyε₂ hyε₁

private theorem rightLim_g2aData_middle {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {J : Finset ℝ} (hpc : IsPiecewiseConstantBoundaryData
      (g2aData κ θ₁ θ₂ w₂ w₁ m) J)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ)
    {y : ℝ} (hy₂ : w₂ < y) (hy₁ : y < w₁) :
    -sleLambda κ - θ₂ * chiC κ < rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) y ∧
      rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) y < sleLambda κ - θ₁ * chiC κ := by
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_eq_lims hpc y
  let ε := min (δ / 2) ((w₁ - y) / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεδ : ε < δ := by
    dsimp [ε] at *
    have h := min_le_left (δ / 2) ((w₁ - y) / 2)
    linarith
  have hyε₂ : w₂ < y + ε := by
    dsimp [ε] at *
    have h := min_le_right (δ / 2) ((w₁ - y) / 2)
    linarith
  have hyε₁ : y + ε < w₁ := by
    change y + min (δ / 2) ((w₁ - y) / 2) < w₁
    have h := min_le_right (δ / 2) ((w₁ - y) / 2)
    linarith
  have hlim := (hδJ ε hε hεδ).2.2.1
  have hdata : g2aData κ θ₁ θ₂ w₂ w₁ m (y + ε) = m (y + ε) := by
    simp [g2aData, not_lt.mpr hyε₂.le, hyε₁]
  rw [hdata] at hlim
  rw [← hlim]
  exact hmid (y + ε) hyε₂ hyε₁

private theorem g2a_leftCum_gt {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    (hpc : IsPiecewiseConstantBoundaryData
      (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)))
    (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ)
    {y : ℝ} (hy : y < w₁)
    (hjy : y ∈ PiecewiseConstantBoundaryData.jumpSet
      (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm))) :
    -2 < Sec4.cumWeightLeft κ
      (leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) y + θ₁ * chiC κ) := by
  have hyc : y ∈ insert w₂ (insert w₁ Jm) := (Finset.mem_filter.mp hjy).1
  rcases Finset.mem_insert.1 hyc with hyw₂ | hyc
  · subst y
    have heq : Sec4.cumWeightLeft κ
        (leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₂ + θ₁ * chiC κ) =
        Supp7.angleGap κ θ₁ θ₂ := by
      rw [leftLim_g2aData_w2]
      unfold Sec4.cumWeightLeft Supp7.angleGap
      field_simp [Sec4.sleLambda_ne_zero hκ]
      ring
    rw [heq]
    have hd := Supp7.angleGap_pos hκ hκ4 hθ
    linarith
  · rcases Finset.mem_insert.1 hyc with hyw₁ | hyJ
    · subst y
      exfalso
      exact (lt_irrefl w₁) hy
    · obtain ⟨hy₂, hy₁⟩ := hJm y hyJ
      have hlim := leftLim_g2aData_middle hpc hmid hy₂ hy₁
      exact ((Supp7.g2a_weights_gt_iff hκ θ₁ θ₂ _).2 hlim).1

private theorem g2a_rightCum_gt {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    (hw : w₂ < w₁) (hpc : IsPiecewiseConstantBoundaryData
      (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)))
    (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ)
    {y : ℝ} (hy : w₂ < y)
    (hjy : y ∈ PiecewiseConstantBoundaryData.jumpSet
      (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm))) :
    -2 < Sec4.cumWeightRight κ
      (rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) y + θ₂ * chiC κ) := by
  have hyc : y ∈ insert w₂ (insert w₁ Jm) := (Finset.mem_filter.mp hjy).1
  rcases Finset.mem_insert.1 hyc with hyw₂ | hyc
  · subst y
    exfalso
    exact (lt_irrefl w₂) hy
  · rcases Finset.mem_insert.1 hyc with hyw₁ | hyJ
    · subst y
      have heq : Sec4.cumWeightRight κ
          (rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₁ + θ₂ * chiC κ) =
          Supp7.angleGap κ θ₁ θ₂ := by
        rw [rightLim_g2aData_w1 hw]
        unfold Sec4.cumWeightRight Supp7.angleGap
        field_simp [Sec4.sleLambda_ne_zero hκ]
        ring
      rw [heq]
      have hd := Supp7.angleGap_pos hκ hκ4 hθ
      linarith
    · obtain ⟨hy₂, hy₁⟩ := hJm y hyJ
      have hlim := rightLim_g2aData_middle hpc hmid hy₂ hy₁
      exact ((Supp7.g2a_weights_gt_iff hκ θ₁ θ₂ _).2 hlim).2

private theorem sum_filter_le_fin_zero {n : ℕ} (hn : 0 < n) (ρ : Fin n → ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ (⟨0, hn⟩ : Fin n)), ρ i = ρ ⟨0, hn⟩ := by
  have hfilter : Finset.univ.filter (fun i : Fin n => i ≤ (⟨0, hn⟩ : Fin n)) =
      {⟨0, hn⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hi
      have hi' : i.val ≤ 0 := by
        simpa only [Fin.le_def, Fin.val_mk] using hi
      apply Fin.ext
      exact Nat.eq_zero_of_le_zero hi'
    · rintro rfl
      exact le_rfl
  rw [hfilter, Finset.sum_singleton]

private theorem g2a_leftGroupEndsAdmissible {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    (hw : w₂ < w₁) (hpc : IsPiecewiseConstantBoundaryData
      (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)))
    (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hnear₁ : ∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ →
      m x = -sleLambda κ - θ₁ * chiC κ)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ) :
    Theorem14.GW0.LeftGroupEndsAdmissible
      (flowLineXL (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁)
      (flowLineRhoL κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ) w₁ θ₁) := by
  classical
  let b := g2aData κ θ₁ θ₂ w₂ w₁ m
  let J := insert w₂ (insert w₁ Jm)
  change ∀ j, (∀ i, j < i → flowLineXL b J w₁ i < flowLineXL b J w₁ j) →
    -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), flowLineRhoL κ b J w₁ θ₁ i
  have hlimSeed := leftLim_g2aData_w1 (κ := κ) (θ₁ := θ₁) (θ₂ := θ₂)
    (w₂ := w₂) (w₁ := w₁) (m := m) hw hnear₁
  have hseed_raw : flowLineRhoL κ (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm)) w₁ θ₁ ⟨0, Nat.succ_pos _⟩ = 0 := by
    change -(leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₁ + θ₁ * chiC κ) /
      sleLambda κ - 1 = 0
    rw [leftLim_g2aData_w1 hw hnear₁]
    field_simp [Sec4.sleLambda_ne_zero hκ]
    ring_nf
  have hseed : flowLineRhoL κ b J w₁ θ₁ ⟨0, Nat.succ_pos _⟩ = 0 := by
    simpa [b, J] using hseed_raw
  intro j _
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, hj⟩
  · let z : Fin (flowLineNL b J w₁) := ⟨0, by unfold flowLineNL; omega⟩
    have hsum : (∑ k ∈ univ.filter (fun k : Fin (flowLineNL b J w₁) => k ≤ z),
        flowLineRhoL κ b J w₁ θ₁ k) = flowLineRhoL κ b J w₁ θ₁ z := by
      exact sum_filter_le_fin_zero (n := flowLineNL b J w₁) (by unfold flowLineNL; omega)
        (flowLineRhoL κ b J w₁ θ₁)
    have hzi : z = (⟨0, Nat.succ_pos _⟩ : Fin (flowLineNL b J w₁)) := Fin.ext rfl
    have hsz : flowLineRhoL κ b J w₁ θ₁ z = 0 := by rw [hzi]; exact hseed
    change -2 < ∑ k ∈ univ.filter (fun k : Fin (flowLineNL b J w₁) => k ≤ z),
      flowLineRhoL κ b J w₁ θ₁ k
    rw [hsum, hsz]
    norm_num
  · let S := (PiecewiseConstantBoundaryData.jumpSet b J).filter (· < w₁)
    let y := S.orderEmbOfFin rfl (Fin.rev i)
    have hyS : y ∈ S := Finset.orderEmbOfFin_mem S rfl (Fin.rev i)
    have hy : y < w₁ := (Finset.mem_filter.mp hyS).2
    have hjy : y ∈ PiecewiseConstantBoundaryData.jumpSet b J :=
      (Finset.mem_filter.mp hyS).1
    have hpos : flowLineXL b J w₁ j = y - w₁ := by
      rw [hj]
      rfl
    have hord := Theorem15.isOrderedForceWord_flowLine b J w₁
    have hfilter : univ.filter (fun l => l ≤ j) =
        univ.filter (fun l => flowLineXL b J w₁ j ≤ flowLineXL b J w₁ l) := by
      apply Finset.filter_congr
      intro l _
      constructor
      · intro hli
        exact hord.1 hli
      · intro hcoord
        by_contra hnot
        have hlt : j < l := lt_of_not_ge hnot
        exact (not_lt_of_ge hcoord) (Theorem14.GW0.flowLineXL_lt b J w₁ hlt)
    rw [hfilter, hpos, Supp7.sum_filter_flowLineXL_ge hκ hpc θ₁ hy]
    exact g2a_leftCum_gt hκ hκ4 hθ hpc hJm hmid hy hjy

private theorem g2a_rightGroupEndsAdmissible {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂)
    (hw : w₂ < w₁) (hpc : IsPiecewiseConstantBoundaryData
      (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)))
    (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hnear₂ : ∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε →
      m x = sleLambda κ - θ₂ * chiC κ)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ) :
    Theorem14.GW0.RightGroupEndsAdmissible
      (flowLineXR (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂)
      (flowLineRhoR κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ) w₂ θ₂) := by
  classical
  let b := g2aData κ θ₁ θ₂ w₂ w₁ m
  let J := insert w₂ (insert w₁ Jm)
  change ∀ j, (∀ i, j < i → flowLineXR b J w₂ j < flowLineXR b J w₂ i) →
    -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), flowLineRhoR κ b J w₂ θ₂ i
  have hlimSeed := rightLim_g2aData_w2 (κ := κ) (θ₁ := θ₁) (θ₂ := θ₂)
    (w₂ := w₂) (w₁ := w₁) (m := m) hw hnear₂
  have hseed_raw : flowLineRhoR κ (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm)) w₂ θ₂ ⟨0, Nat.succ_pos _⟩ = 0 := by
    change (rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₂ + θ₂ * chiC κ) /
      sleLambda κ - 1 = 0
    rw [rightLim_g2aData_w2 hw hnear₂]
    field_simp [Sec4.sleLambda_ne_zero hκ]
    ring_nf
  have hseed : flowLineRhoR κ b J w₂ θ₂ ⟨0, Nat.succ_pos _⟩ = 0 := by
    simpa [b, J] using hseed_raw
  intro j _
  rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨i, hj⟩
  · let z : Fin (flowLineNR b J w₂) := ⟨0, by unfold flowLineNR; omega⟩
    have hsum : (∑ k ∈ univ.filter (fun k : Fin (flowLineNR b J w₂) => k ≤ z),
        flowLineRhoR κ b J w₂ θ₂ k) = flowLineRhoR κ b J w₂ θ₂ z := by
      exact sum_filter_le_fin_zero (n := flowLineNR b J w₂) (by unfold flowLineNR; omega)
        (flowLineRhoR κ b J w₂ θ₂)
    have hzi : z = (⟨0, Nat.succ_pos _⟩ : Fin (flowLineNR b J w₂)) := Fin.ext rfl
    have hsz : flowLineRhoR κ b J w₂ θ₂ z = 0 := by rw [hzi]; exact hseed
    change -2 < ∑ k ∈ univ.filter (fun k : Fin (flowLineNR b J w₂) => k ≤ z),
      flowLineRhoR κ b J w₂ θ₂ k
    rw [hsum, hsz]
    norm_num
  · let S := (PiecewiseConstantBoundaryData.jumpSet b J).filter (w₂ < ·)
    let y := S.orderEmbOfFin rfl i
    have hyS : y ∈ S := Finset.orderEmbOfFin_mem S rfl i
    have hy : w₂ < y := (Finset.mem_filter.mp hyS).2
    have hjy : y ∈ PiecewiseConstantBoundaryData.jumpSet b J :=
      (Finset.mem_filter.mp hyS).1
    have hpos : flowLineXR b J w₂ j = y - w₂ := by
      rw [hj]
      rfl
    have hord := Theorem15.isOrderedForceWord_flowLine b J w₂
    have hfilter : univ.filter (fun l => l ≤ j) =
        univ.filter (fun l => flowLineXR b J w₂ l ≤ flowLineXR b J w₂ j) := by
      apply Finset.filter_congr
      intro l _
      constructor
      · intro hli
        exact hord.2.2.1 hli
      · intro hcoord
        by_contra hnot
        have hlt : j < l := lt_of_not_ge hnot
        exact (not_lt_of_ge hcoord) (Theorem14.GW0.flowLineXR_lt b J w₂ hlt)
    rw [hfilter, hpos, Supp7.sum_filter_flowLineXR_le hκ hpc θ₂ hy]
    exact g2a_rightCum_gt hκ hκ4 hθ hw hpc hJm hmid hy hjy

private theorem g2a_singleMark_leftGroupEndsAdmissible {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ}
    (hN : flowLineNL b J x = 1)
    (hseed : flowLineRhoL κ b J x θ ⟨0, Nat.succ_pos _⟩ = 0) :
    Theorem14.GW0.LeftGroupEndsAdmissible (flowLineXL b J x) (flowLineRhoL κ b J x θ) := by
  change ∀ j, (∀ i, j < i → flowLineXL b J x i < flowLineXL b J x j) →
    -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), flowLineRhoL κ b J x θ i
  intro j _
  have hjlt := j.isLt
  have hj0 : j.val = 0 := by omega
  have hjeq : j = (⟨0, by unfold flowLineNL; omega⟩ : Fin (flowLineNL b J x)) := Fin.ext hj0
  rw [hjeq]
  let z : Fin (flowLineNL b J x) := ⟨0, by unfold flowLineNL; omega⟩
  have hsum : (∑ k ∈ univ.filter (fun k : Fin (flowLineNL b J x) => k ≤ z),
      flowLineRhoL κ b J x θ k) = flowLineRhoL κ b J x θ z := by
    exact sum_filter_le_fin_zero (n := flowLineNL b J x) (by unfold flowLineNL; omega)
      (flowLineRhoL κ b J x θ)
  have hzi : z = (⟨0, Nat.succ_pos _⟩ : Fin (flowLineNL b J x)) := Fin.ext rfl
  have hsz : flowLineRhoL κ b J x θ z = 0 := by rw [hzi]; exact hseed
  change -2 < ∑ k ∈ univ.filter (fun k : Fin (flowLineNL b J x) => k ≤ z),
    flowLineRhoL κ b J x θ k
  rw [hsum, hsz]
  norm_num

private theorem g2a_singleMark_rightGroupEndsAdmissible {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ}
    (hN : flowLineNR b J x = 1)
    (hseed : flowLineRhoR κ b J x θ ⟨0, Nat.succ_pos _⟩ = 0) :
    Theorem14.GW0.RightGroupEndsAdmissible (flowLineXR b J x) (flowLineRhoR κ b J x θ) := by
  change ∀ j, (∀ i, j < i → flowLineXR b J x j < flowLineXR b J x i) →
    -2 < ∑ i ∈ univ.filter (fun i => i ≤ j), flowLineRhoR κ b J x θ i
  intro j _
  have hjlt := j.isLt
  have hj0 : j.val = 0 := by omega
  have hjeq : j = (⟨0, by unfold flowLineNR; omega⟩ : Fin (flowLineNR b J x)) := Fin.ext hj0
  rw [hjeq]
  let z : Fin (flowLineNR b J x) := ⟨0, by unfold flowLineNR; omega⟩
  have hsum : (∑ k ∈ univ.filter (fun k : Fin (flowLineNR b J x) => k ≤ z),
      flowLineRhoR κ b J x θ k) = flowLineRhoR κ b J x θ z := by
    exact sum_filter_le_fin_zero (n := flowLineNR b J x) (by unfold flowLineNR; omega)
      (flowLineRhoR κ b J x θ)
  have hzi : z = (⟨0, Nat.succ_pos _⟩ : Fin (flowLineNR b J x)) := Fin.ext rfl
  have hsz : flowLineRhoR κ b J x θ z = 0 := by rw [hzi]; exact hseed
  change -2 < ∑ k ∈ univ.filter (fun k : Fin (flowLineNR b J x) => k ≤ z),
    flowLineRhoR κ b J x θ k
  rw [hsum, hsz]
  norm_num

private theorem g2a_rightFlowLineNL_eq_one {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hw : w₂ < w₁) (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁) :
    flowLineNL (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ = 1 := by
  have hfilter : (PiecewiseConstantBoundaryData.jumpSet (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm))).filter (· < w₂) = ∅ := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨hyj, hy⟩
      have hyJ := (Finset.mem_filter.mp hyj).1
      rcases Finset.mem_insert.mp hyJ with hyw₂ | hyJ
      · rw [hyw₂] at hy
        exact False.elim (lt_irrefl w₂ hy)
      · rcases Finset.mem_insert.mp hyJ with hyw₁ | hyJm
        · rw [hyw₁] at hy
          exact False.elim (not_lt_of_ge hw.le hy)
        · exact False.elim (not_lt_of_ge (hJm y hyJm).1.le hy)
    · intro hy
      cases hy
  unfold flowLineNL
  rw [hfilter]
  simp

private theorem g2a_leftFlowLineNR_eq_one {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hw : w₂ < w₁) (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁) :
    flowLineNR (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ = 1 := by
  have hfilter : (PiecewiseConstantBoundaryData.jumpSet (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm))).filter (w₁ < ·) = ∅ := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_filter.mp hy with ⟨hyj, hy⟩
      have hyJ := (Finset.mem_filter.mp hyj).1
      rcases Finset.mem_insert.mp hyJ with hyw₂ | hyJ
      · rw [hyw₂] at hy
        exact False.elim (not_lt_of_ge hw.le hy)
      · rcases Finset.mem_insert.mp hyJ with hyw₁ | hyJm
        · rw [hyw₁] at hy
          exact False.elim (lt_irrefl w₁ hy)
        · exact False.elim (not_lt_of_ge (hJm y hyJm).2.le hy)
    · intro hy
      cases hy
  unfold flowLineNR
  rw [hfilter]
  simp

private theorem g2a_outwardGroupEndsAdmissible {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ}
    {Jm : Finset ℝ} (hκ : 0 < κ) (hw : w₂ < w₁) (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁) :
    Theorem14.GW0.LeftGroupEndsAdmissible
      (flowLineXL (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂)
      (flowLineRhoL κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ θ₂) ∧
    Theorem14.GW0.RightGroupEndsAdmissible
      (flowLineXR (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁)
      (flowLineRhoR κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ θ₁) := by
  have hleftSeed : flowLineRhoL κ (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm)) w₂ θ₂ ⟨0, Nat.succ_pos _⟩ = 0 := by
    change -(leftLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₂ + θ₂ * chiC κ) /
      sleLambda κ - 1 = 0
    rw [leftLim_g2aData_w2]
    field_simp [Sec4.sleLambda_ne_zero hκ]
    ring_nf
  have hrightSeed : flowLineRhoR κ (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm)) w₁ θ₁ ⟨0, Nat.succ_pos _⟩ = 0 := by
    change (rightLim (g2aData κ θ₁ θ₂ w₂ w₁ m) w₁ + θ₁ * chiC κ) /
      sleLambda κ - 1 = 0
    rw [rightLim_g2aData_w1 hw]
    field_simp [Sec4.sleLambda_ne_zero hκ]
    ring_nf
  exact ⟨g2a_singleMark_leftGroupEndsAdmissible (g2a_rightFlowLineNL_eq_one hw hJm) hleftSeed,
    g2a_singleMark_rightGroupEndsAdmissible (g2a_leftFlowLineNR_eq_one hw hJm) hrightSeed⟩

/-- All four side words of the two G2a reference flows have every group-end sum strictly above `−2`.
The two inward sides use the middle-height bounds; the outward sides consist only of their zero seed mark. -/
theorem g2a_groupEndSums_gt_negTwo {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ} {Jm : Finset ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (hw : w₂ < w₁)
    (hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm))) (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hnear₂ : ∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * chiC κ)
    (hnear₁ : ∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * chiC κ)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ) :
    Theorem14.GW0.LeftGroupEndsAdmissible
        (flowLineXL (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁)
        (flowLineRhoL κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ θ₁) ∧
      Theorem14.GW0.RightGroupEndsAdmissible
        (flowLineXR (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁)
        (flowLineRhoR κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁ θ₁) ∧
      Theorem14.GW0.LeftGroupEndsAdmissible
        (flowLineXL (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂)
        (flowLineRhoL κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ θ₂) ∧
      Theorem14.GW0.RightGroupEndsAdmissible
        (flowLineXR (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂)
        (flowLineRhoR κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂ θ₂) := by
  have hout := g2a_outwardGroupEndsAdmissible (κ := κ) (θ₁ := θ₁) (θ₂ := θ₂)
    (w₂ := w₂) (w₁ := w₁) (m := m) (Jm := Jm) hκ hw hJm
  exact ⟨g2a_leftGroupEndsAdmissible hκ hκ4 hθ hw hpc hJm hnear₁ hmid, hout.2,
    hout.1, g2a_rightGroupEndsAdmissible hκ hκ4 hθ hw hpc hJm hnear₂ hmid⟩

/-- The G2a flow-line words have infinite lifetimes almost surely, by the four explicit group-end bounds and GW0. -/
theorem ae_g2a_infiniteLifetimes {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ} {Jm : Finset ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (hw : w₂ < w₁)
    (hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm))) (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hnear₂ : ∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * chiC κ)
    (hnear₁ : ∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * chiC κ)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ)
    {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (h : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞)
    (hη₁ : IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ)
      w₁ θ₁ Q h α₁ ζ₁)
    (hη₂ : IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ)
      w₂ θ₂ Q h α₂ ζ₂) : ∀ᵐ x ∂Q, ζ₁ x = ⊤ ∧ ζ₂ x = ⊤ := by
  have hadm := g2a_groupEndSums_gt_negTwo hκ hκ4 hθ hw hpc hJm hnear₂ hnear₁ hmid
  obtain ⟨_, 𝓕₁, W₁, VL₁, VR₁, B₁, -, hcpl₁, _⟩ := hη₁
  obtain ⟨_, 𝓕₂, W₂, VL₂, VR₂, B₂, -, hcpl₂, _⟩ := hη₂
  have hlife₁ := Theorem14.GW0.ae_lifetime_eq_top_of_neg_two_lt
    (Theorem15.isOrderedForceWord_flowLine (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₁)
    hadm.1 hadm.2.1 hcpl₁.1
  have hlife₂ := Theorem14.GW0.ae_lifetime_eq_top_of_neg_two_lt
    (Theorem15.isOrderedForceWord_flowLine (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) w₂)
    hadm.2.2.1 hadm.2.2.2 hcpl₂.1
  filter_upwards [hlife₁, hlife₂] with x hx₁ hx₂
  exact ⟨hx₁, hx₂⟩

/-- Aux. 25 gives almost-sure simplicity of both G2a flow lines on their available lifetimes. -/
theorem ae_g2a_simple {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {w₁ w₂ θ₁ θ₂ : ℝ}
    {S : Type u} [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q]
    {h : S → LQGMetric.DistOn upperHalfPlaneOpens} {α₁ α₂ : S → ℝ≥0 → ℂ}
    {ζ₁ ζ₂ : S → ℝ≥0∞} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hη₁ : IsFlowLine κ b J w₁ θ₁ Q h α₁ ζ₁)
    (hη₂ : IsFlowLine κ b J w₂ θ₂ Q h α₂ ζ₂) :
    (∀ᵐ x ∂Q, InjOn (α₁ x) {t | (t : ℝ≥0∞) ≤ ζ₁ x}) ∧
      (∀ᵐ x ∂Q, InjOn (α₂ x) {t | (t : ℝ≥0∞) ≤ ζ₂ x}) :=
  ⟨Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁,
    Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂⟩

/-- G12 excludes the opposite seed for each G2a flow line. The jump at the other seed has outward cumulative weight
strictly above `−2`, hence strictly above the G12 threshold `κ/2 − 4`. -/
theorem ae_g2a_oppositeSeedNotInRange {κ θ₁ θ₂ w₂ w₁ : ℝ} {m : ℝ → ℝ} {Jm : Finset ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ₁ < θ₂) (hw : w₂ < w₁)
    (hpc : IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m)
      (insert w₂ (insert w₁ Jm))) (hJm : ∀ y ∈ Jm, w₂ < y ∧ y < w₁)
    (hnear₂ : ∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * chiC κ)
    (hnear₁ : ∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * chiC κ)
    (hmid : ∀ x, w₂ < x → x < w₁ →
      -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ)
    {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
    (h : S → LQGMetric.DistOn upperHalfPlaneOpens)
    (hĤ : IsGFFWithBoundaryData Q h (g2aData κ θ₁ θ₂ w₂ w₁ m)
      ((insert w₂ (insert w₁ Jm) : Finset ℝ) : Set ℝ))
    (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞)
    (hη₁ : IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ)
      w₁ θ₁ Q h α₁ ζ₁)
    (hη₂ : IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ)
      w₂ θ₂ Q h α₂ ζ₂) :
    ∀ᵐ x ∂Q, (w₂ : ℂ) ∉ range (α₁ x) ∧ (w₁ : ℂ) ∉ range (α₂ x) := by
  let b := g2aData κ θ₁ θ₂ w₂ w₁ m
  let J := insert w₂ (insert w₁ Jm)
  have hjw₂ : w₂ ∈ PiecewiseConstantBoundaryData.jumpSet b J := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_insert_self w₂ (insert w₁ Jm), ?_⟩
    rw [leftLim_g2aData_w2, rightLim_g2aData_w2 hw hnear₂]
    exact ne_of_lt (by nlinarith [Sec4.sleLambda_pos hκ])
  have hjw₁ : w₁ ∈ PiecewiseConstantBoundaryData.jumpSet b J := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self w₁ Jm), ?_⟩
    rw [leftLim_g2aData_w1 hw hnear₁, rightLim_g2aData_w1 hw]
    exact ne_of_lt (by nlinarith [Sec4.sleLambda_pos hκ])
  have hleft := g2a_leftCum_gt hκ hκ4 hθ hpc hJm hmid (by linarith : w₂ < w₁) hjw₂
  have hright := g2a_rightCum_gt hκ hκ4 hθ hw hpc hJm hmid (by linarith : w₂ < w₁) hjw₁
  have hthreshold : κ / 2 - 4 < -2 := by linarith
  have havoid₁ := (Supp7.g12FlowStatement κ hκ hκ4 b J hpc w₁ θ₁ w₂ Q h hĤ α₁ ζ₁ hη₁).2
    (by linarith) (hthreshold.trans hleft)
  have havoid₂ := (Supp7.g12FlowStatement κ hκ hκ4 b J hpc w₂ θ₂ w₁ Q h hĤ α₂ ζ₂ hη₂).1
    (by linarith) (hthreshold.trans hright)
  have hlife := ae_g2a_infiniteLifetimes hκ hκ4 hθ hw hpc hJm hnear₂ hnear₁ hmid
    Q h α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [hlife, havoid₁, havoid₂] with x hζ hno₁ hno₂
  constructor
  · rintro ⟨t, ht⟩
    exact hno₁ t (by rw [hζ.1]; exact le_top) ht
  · rintro ⟨t, ht⟩
    exact hno₂ t (by rw [hζ.2]; exact le_top) ht

/-- Named input for the remaining transience clause of the G2a reference: both reference traces tend to infinity.
Continuity, injectivity, the closed-half-plane condition, and the prefix property are supplied by landed flow-line lemmas,
Aux. 25, and infinite lifetime. -/
def G2aTransienceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ θ₁ θ₂ w₂ w₁ : ℝ, θ₁ < θ₂ → w₂ < w₁ →
    ∀ (m : ℝ → ℝ) (Jm : Finset ℝ), (∀ j ∈ Jm, w₂ < j ∧ j < w₁) →
      IsPiecewiseConstantBoundaryData (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm)) →
      (∃ ε > 0, ∀ x, w₂ < x → x < w₂ + ε → m x = sleLambda κ - θ₂ * chiC κ) →
      (∃ ε > 0, ∀ x, w₁ - ε < x → x < w₁ → m x = -sleLambda κ - θ₁ * chiC κ) →
      (∀ x, w₂ < x → x < w₁ →
        -sleLambda κ - θ₂ * chiC κ < m x ∧ m x < sleLambda κ - θ₁ * chiC κ) →
      ∀ {S : Type u} [MeasurableSpace S] (Q : Measure S) [IsProbabilityMeasure Q]
        (h : S → LQGMetric.DistOn upperHalfPlaneOpens),
        IsGFFWithBoundaryData Q h (g2aData κ θ₁ θ₂ w₂ w₁ m)
          ((insert w₂ (insert w₁ Jm) : Finset ℝ) : Set ℝ) →
        ∀ (α₁ α₂ : S → ℝ≥0 → ℂ) (ζ₁ ζ₂ : S → ℝ≥0∞),
          IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ)
            w₁ θ₁ Q h α₁ ζ₁ →
          IsFlowLine κ (g2aData κ θ₁ θ₂ w₂ w₁ m) (insert w₂ (insert w₁ Jm) : Finset ℝ)
            w₂ θ₂ Q h α₂ ζ₂ →
          ∀ᵐ x ∂Q, Tendsto (fun t => ‖α₁ x t‖) atTop atTop ∧
            Tendsto (fun t => ‖α₂ x t‖) atTop atTop

/-- Combine transience with the landed continuity, half-plane, and Aux. 25 results to obtain proper completions. -/
theorem ae_g2a_properCompletions_of_transience {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {w₁ w₂ θ₁ θ₂ : ℝ} {S : Type u} [MeasurableSpace S] {Q : Measure S}
    [IsProbabilityMeasure Q] {h : S → LQGMetric.DistOn upperHalfPlaneOpens}
    {α₁ α₂ : S → ℝ≥0 → ℂ} {ζ₁ ζ₂ : S → ℝ≥0∞}
    (hκ : 0 < κ) (hκ4 : κ < 4)
    (hη₁ : IsFlowLine κ b J w₁ θ₁ Q h α₁ ζ₁)
    (hη₂ : IsFlowLine κ b J w₂ θ₂ Q h α₂ ζ₂)
    (hlife : ∀ᵐ x ∂Q, ζ₁ x = ⊤ ∧ ζ₂ x = ⊤)
    (htrans : ∀ᵐ x ∂Q, Tendsto (fun t => ‖α₁ x t‖) atTop atTop ∧
      Tendsto (fun t => ‖α₂ x t‖) atTop atTop) :
    ∀ᵐ x ∂Q, IsProperCompletion (α₁ x) 0 (α₁ x) ∧ IsProperCompletion (α₂ x) 0 (α₂ x) := by
  have hinj := ae_g2a_simple hκ hκ4 hη₁ hη₂
  filter_upwards [hlife, hinj.1, hinj.2, htrans,
    Sec7.ae_continuousOn_of_isFlowLine hη₁, Sec7.ae_continuousOn_of_isFlowLine hη₂,
    Supp7.ae_im_nonneg_of_isFlowLine hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₂]
    with x hl hI₁ hI₂ ht hc₁ hc₂ him₁ him₂
  have hdomain₁ : ∀ t, (t : ℝ≥0∞) ≤ ζ₁ x := fun t => by rw [hl.1]; exact le_top
  have hdomain₂ : ∀ t, (t : ℝ≥0∞) ≤ ζ₂ x := fun t => by rw [hl.2]; exact le_top
  have hcont₁ : Continuous (α₁ x) := continuousOn_univ.1 (hc₁.mono fun t _ => hdomain₁ t)
  have hcont₂ : Continuous (α₂ x) := continuousOn_univ.1 (hc₂.mono fun t _ => hdomain₂ t)
  have hinj₁ : Function.Injective (α₁ x) := by
    intro s t hst
    exact hI₁ (hdomain₁ s) (hdomain₁ t) hst
  have hinj₂ : Function.Injective (α₂ x) := by
    intro s t hst
    exact hI₂ (hdomain₂ s) (hdomain₂ t) hst
  have himage₁ : ∀ t, 0 ≤ (α₁ x t).im := fun t => him₁ t (hdomain₁ t)
  have himage₂ : ∀ t, 0 ≤ (α₂ x t).im := fun t => him₂ t (hdomain₂ t)
  exact ⟨⟨hcont₁, hinj₁, himage₁, ht.1, fun _ _ => rfl⟩,
    ⟨hcont₂, hinj₂, himage₂, ht.2, fun _ _ => rfl⟩⟩

/-- Bridge the proved G2a parts to the exact statement owned by RLCIOrder, from the remaining
transience input. -/
theorem g2aPartsStatement_of_transience (hTrans : G2aTransienceStatement.{u}) :
    G2aPartsStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hnear₂ hnear₁ hmid
    S _ Q _ h hĤ α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  have hlife := ae_g2a_infiniteLifetimes hκ hκ4 hθ hw hpc hJm hnear₂ hnear₁ hmid
    Q h α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  have htrans := hTrans κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hnear₂ hnear₁ hmid
    Q h hĤ α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  have hproper := ae_g2a_properCompletions_of_transience hκ hκ4 hη₁ hη₂ hlife htrans
  have havoid := ae_g2a_oppositeSeedNotInRange hκ hκ4 hθ hw hpc hJm hnear₂ hnear₁ hmid
    Q h hĤ α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  filter_upwards [hlife, hproper, havoid] with x hl hp ha
  exact ⟨hl.1, hl.2, hp.1, hp.2, ha.1, ha.2⟩

end RLC

end InteractingSLE

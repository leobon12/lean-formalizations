/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NvMeas

/-!
# SB2(2)'s v6 measurability: `StageOK` from drivenness

Packet PROVE-GW2-GEOM2, round 10 (D28, item (A)). `Lk.StageOK ρ G Z` asks:
* the curve is measurable at every time;
* the driven event `G` and the zero event `Z` are measurable;
* the curve is driven on `G`.

For the v6 rule the first three are proved here; the fourth is the input:

* **`stageOK_dh`**: for the regular family `Dh Ê` and a measurable `Gd` on which the walk launches at `relOff` off a
  zero root, every relative family measurable and regular before `j` and every stage `j`, drivenness of the v4 curve
  on the v6 mask gives `StageOK` of the v6 rule;
* **`stageOK_of_agree`**: the same for an actual family that agrees with `Dh Ê` on `Gd` (`AgreeAt`): the mask, the
  masked zero events and the v6 curves coincide.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Nv

open Lk Exist Exist.Staged Exist.StagedLaw Sec7.PocketTraversal LuM GW1W GW1Bookkeep

section Stage

variable {Ω : Type*} {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}
  {R : ℝ} {c : Chart} {m : ℝ}

/-- The launch at `relOff` at stage `0`, from a mask point (`Gd` gives it off a zero root). -/
theorem launch_relOff_of_not_cZ4 {Ê : ℕ → Ω → Drv} {Gd : Set Ω}
    (hGd : ∀ ω ∈ Gd, ¬ ZeroRoot κ θ b₁ J₁ R (fun i => Ê i ω) →
      (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none)
    {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω} (hω : ω ∈ Gd) (hZ : ω ∉ cZ4 κ θ b₁ J₁ R (Dh Ê) j F) :
    j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none := by
  intro hj
  refine hGd ω hω fun hz => hZ ?_
  subst hj
  exact Or.inr (Or.inl ⟨rfl, hz⟩)

/-- **`StageOK` of the v6 rule for the regular family, from drivenness on the mask.** -/
theorem stageOK_dh [MeasurableSpace Ω] [StandardBorelSpace Ω] (hb₁ : IsPiecewiseConstantBoundaryData b₁ J₁)
    (hb₂ : IsPiecewiseConstantBoundaryData b₂ J₂) (hcc : c.IsConformal) {Ê : ℕ → Ω → Drv}
    (hÊm : ∀ j, Measurable (Ê j)) (hÊreg : ∀ j ω, IsRegularDriver (Ê j ω))
    (hÊP : ∀ ω, RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) fun j => Ê j ω) {Gd : Set Ω}
    (hGdm : MeasurableSet Gd)
    (hGd : ∀ ω ∈ Gd, ¬ ZeroRoot κ θ b₁ J₁ R (fun i => Ê i ω) →
      (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1 (rO κ θ b₁ J₁ R Ê ω) ≠ none)
    {j : ℕ} {F : ℕ → Ω → Drv} (hFm : ∀ i < j, Measurable (F i)) (hFr : ∀ i < j, ∀ ω, IsRegularDriver (F i ω))
    (hdrv : ∀ ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) Gd j F,
      IsDrivenCurve (cρ3 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) j F ω)) :
    StageOK (mρ6 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) Gd j F) (maskEv κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) Gd j F)
      (mZ Gd (cZ4 κ θ b₁ J₁ R (Dh Ê)) j F) := by
  classical
  set M := maskEv κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) Gd j F with hMdef
  -- the zero events on `Gd`
  have hZG : MeasurableSet (Gd ∩ cZ4 κ θ b₁ J₁ R (Dh Ê) j F) := by
    have e : Gd ∩ cZ4 κ θ b₁ J₁ R (Dh Ê) j F = Gd ∩ ({_ω | j % 2 = 1} ∪
        ({_ω | j = 0} ∩ {ω | ZeroRoot κ θ b₁ J₁ R (fun i => Ê i ω)}) ∪
          {ω | Lhm κ θ b₁ J₁ R Ê j ω = 0}) := by
      ext ω
      simp only [mem_inter_iff, mem_union, mem_ofPred_eq, and_congr_right_iff]
      intro hω
      have hz : ω ∈ cZ4 κ θ b₁ J₁ R (Dh Ê) j F ↔ j % 2 = 1 ∨ (j = 0 ∧ ZeroRoot κ θ b₁ J₁ R (fun i => Ê i ω)) ∨
          stL κ θ b₁ J₁ R (Dh Ê) j ω = 0 := Iff.rfl
      rw [hz]
      by_cases h0 : j = 0 ∧ ZeroRoot κ θ b₁ J₁ R (fun i => Ê i ω)
      · simp only [h0, and_self, true_or, or_true]
      · have hl : j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1
            (rO κ θ b₁ J₁ R Ê ω) ≠ none := fun hj => hGd ω hω fun hz => h0 ⟨hj, hz⟩
        rw [stL_eq_Lhm hl]
        tauto
    rw [e]
    exact hGdm.inter (((MeasurableSet.const _).union ((MeasurableSet.const _).inter
      (measurableSet_zeroRoot hb₁ hÊm hÊreg hÊP R))).union
      (measurableSet_eq_fun (measurable_Lhm hb₁ hÊm hÊreg hÊP j) measurable_const))
  -- the launch and the record events
  have hLm : MeasurableSet (launchEv κ θ b₁ J₁ R (Dh Ê) j) := by
    have h := measurableSet_launch_relOff hb₁ hÊm hÊreg hÊP R j
    have e : launchEv κ θ b₁ J₁ R (Dh Ê) j = {ω | (wRun κ θ b₁ J₁ (fun i => Ê i ω)
        (j + relOff κ θ b₁ J₁ R (fun i => Ê i ω) + 1)).2.2.2.1 (j + relOff κ θ b₁ J₁ R (fun i => Ê i ω)) ≠ none} :=
      rfl
    rw [e]; exact h
  have hRm := measurableSet_recGoodEv (κ := κ) (θ := θ) hb₂ hFm hFr
  -- the surrogate density event
  set DG : Set Ω := {ω | ∀ k n : ℕ, ∃ i, Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω ∧
    dist (ratPt i) (ratPt k) < 1 / ((n : ℝ) + 1)} with hDG
  have hDGm : MeasurableSet DG := by
    have e : DG = ⋂ k : ℕ, ⋂ n : ℕ, ⋃ i : ℕ, {ω | Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω} ∩
        {_ω | dist (ratPt i) (ratPt k) < 1 / ((n : ℝ) + 1)} := by
      ext ω; simp [hDG]
    rw [e]
    exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun n => MeasurableSet.iUnion fun i =>
      (measurableSet_Gv hb₁ hÊm hÊreg hÊP hb₂ hcc m i hFm hFr).inter (MeasurableSet.const _)
  set B : Set Ω := (Gd ∩ (Gd ∩ cZ4 κ θ b₁ J₁ R (Dh Ê) j F)ᶜ) ∩ (launchEv κ θ b₁ J₁ R (Dh Ê) j ∩
    recGoodEv κ θ b₂ J₂ j F) with hB
  have hBm : MeasurableSet B := (hGdm.inter hZG.compl).inter (hLm.inter hRm)
  -- the readings of a mask point
  have hpt : ∀ ω ∈ M, (j = 0 → (wRun κ θ b₁ J₁ (fun i => Ê i ω) (rO κ θ b₁ J₁ R Ê ω + 1)).2.2.2.1
      (rO κ θ b₁ J₁ R Ê ω) ≠ none) := fun ω hω => launch_relOff_of_not_cZ4 hGd hω.1 hω.2.1
  have hMeq : M = B ∩ DG := by
    ext ω
    constructor
    · intro hω
      obtain ⟨hG, hZ, hL, hR, hD⟩ := hω
      refine ⟨⟨⟨hG, fun h => hZ h.2⟩, hL, hR⟩, fun k n => ?_⟩
      obtain ⟨i, hi, hd⟩ := hD k n
      exact ⟨i, (goodRead_iff_Gv i hFr (launch_relOff_of_not_cZ4 hGd hG hZ) hL hR).1 hi, hd⟩
    · rintro ⟨⟨⟨hG, hZ⟩, hL, hR⟩, hD⟩
      have hZ' : ω ∉ cZ4 κ θ b₁ J₁ R (Dh Ê) j F := fun h => hZ ⟨hG, h⟩
      refine ⟨hG, hZ', hL, hR, fun k n => ?_⟩
      obtain ⟨i, hi, hd⟩ := hD k n
      exact ⟨i, (goodRead_iff_Gv i hFr (launch_relOff_of_not_cZ4 hGd hG hZ') hL hR).2 hi, hd⟩
  have hMm : MeasurableSet M := by rw [hMeq]; exact hBm.inter hDGm
  refine ⟨fun t ht => ?_, hMm, ?_, fun ω hω => ?_⟩
  · -- the curve at a time
    set t' : ℝ≥0 := t.toNNReal with ht'
    have htt : ((t' : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht
    have hmeas : Measurable fun ω => if ω ∈ M then cρ3 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) j F ω (t' : ℝ) else 0 := by
      refine measurable_at_of_dense_good (ρ := fun ω (u : ℝ≥0) => cρ3 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) j F ω u)
        (good := fun i ω => ω ∈ B ∧ Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω)
        (V := fun i => Vm κ θ b₁ J₁ R Ê c m b₂ J₂ j i F)
        (fun i => hBm.inter (measurableSet_Gv hb₁ hÊm hÊreg hÊP hb₂ hcc m i hFm hFr))
        (fun i => measurable_Vm hb₁ hÊm hÊreg hÊP hb₂ hcc m i hFm hFr) hMm (σ := fun _ => t') measurable_const
        ?_ ?_ ?_
      · intro ω hω i hi
        exact cρ3_ratPt_eq_Vm i hFr (hpt ω hω) hω.2.2.1 hω.2.2.2.1 hi.2
      · intro ω hω ε hε
        have hωBD : ω ∈ B ∩ DG := hMeq ▸ hω
        obtain ⟨k, hk⟩ := exists_ratPt_near t' (half_pos hε)
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hε)
        obtain ⟨i, hi, hd⟩ := hωBD.2 k n
        refine ⟨i, ⟨hωBD.1, hi⟩, ?_⟩
        calc dist (ratPt i) t' ≤ dist (ratPt i) (ratPt k) + dist (ratPt k) t' := dist_triangle _ _ _
          _ < ε / 2 + ε / 2 := add_lt_add (hd.trans hn) hk
          _ = ε := add_halves ε
      · intro ω hω v hv hconv
        have hc := (hdrv ω hω).continuousOn
        have hcont : Continuous fun u : ℝ≥0 => cρ3 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) j F ω (u : ℝ) :=
          hc.comp_continuous NNReal.continuous_coe fun u => u.2
        exact tendsto_of_continuousWithinAt (S := univ) hcont.continuousWithinAt
          (good := fun i => ω ∈ B ∧ Gv κ θ b₁ J₁ R Ê c m b₂ J₂ j i F ω) (fun _ _ => mem_univ _) v hv hconv
    have h2 := measurable_ite_of_masked hMm hmeas (vertCurve t)
    have e : (fun ω => mρ6 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) Gd j F ω t) =
        fun ω => if ω ∈ M then cρ3 κ θ b₁ J₁ b₂ J₂ R c m (Dh Ê) j F ω (t' : ℝ) else vertCurve t := by
      funext ω
      rw [htt]
      by_cases hω : ω ∈ M
      · rw [mρ6_of_mem hω]; simp only [hω, ↓reduceIte]
      · rw [mρ6_of_not_mem hω]; simp only [hω, ↓reduceIte]
    rw [e]
    exact h2
  · -- the masked zero events
    have e : mZ Gd (cZ4 κ θ b₁ J₁ R (Dh Ê)) j F = (Gd ∩ cZ4 κ θ b₁ J₁ R (Dh Ê) j F) ∪ Gdᶜ := by
      unfold mZ; rw [inter_comm]
    rw [e]
    exact hZG.union hGdm.compl
  · -- drivenness on the mask
    rw [mρ6_of_mem hω]
    exact hdrv ω hω

end Stage

/-! ### Transfer to an agreeing actual family -/

section Transfer

variable {Ω : Type*} {κ θ : ℝ} {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}
  {R : ℝ} {c : Chart} {m : ℝ} {D₁ Dh' : Ω → ℕ → Drv} {Gd : Set Ω}

/-- On `Gd`, agreeing families have the same mask. -/
theorem maskEv_eq_of_agree (hAg : ∀ ω ∈ Gd, AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh' ω))
    (hGd : ∀ ω ∈ Gd, ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) →
      (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none)
    (j : ℕ) (F : ℕ → Ω → Drv) :
    maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F = maskEv κ θ b₁ J₁ b₂ J₂ R c m Dh' Gd j F := by
  ext ω
  by_cases hω : ω ∈ Gd
  · exact mem_maskEv_iff_of_agree (hAg ω hω) (hGd ω hω) Gd j F
  · exact ⟨fun h => absurd h.1 hω, fun h => absurd h.1 hω⟩

/-- On `Gd`, agreeing families have the same masked zero events. -/
theorem mZ_eq_of_agree (hAg : ∀ ω ∈ Gd, AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh' ω))
    (hGd : ∀ ω ∈ Gd, ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) →
      (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none)
    (j : ℕ) (F : ℕ → Ω → Drv) :
    mZ Gd (cZ4 κ θ b₁ J₁ R D₁) j F = mZ Gd (cZ4 κ θ b₁ J₁ R Dh') j F := by
  ext ω
  unfold mZ
  by_cases hω : ω ∈ Gd
  · simp only [mem_union, mem_inter_iff, hω, and_true, mem_compl_iff, not_true_eq_false, or_false]
    exact mem_cZ4_iff_of_agree (hAg ω hω) (hGd ω hω) j F F
  · simp only [mem_union, mem_inter_iff, hω, and_false, mem_compl_iff, not_false_eq_true, or_true]

/-- On the mask, agreeing families have the same v4 curves. -/
theorem cρ3_eq_of_mask (hAg : ∀ ω ∈ Gd, AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh' ω))
    (hGd : ∀ ω ∈ Gd, ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) →
      (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none)
    {j : ℕ} {F : ℕ → Ω → Drv} {ω : Ω} (hω : ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) :
    cρ3 κ θ b₁ J₁ b₂ J₂ R c m D₁ j F ω = cρ3 κ θ b₁ J₁ b₂ J₂ R c m Dh' j F ω := by
  refine cρ3_eq_of_agree (hAg ω hω.1) hω.2.2.1 (fun hj => hGd ω hω.1 fun hz => hω.2.1 ?_) F
  subst hj
  exact Or.inr (Or.inl ⟨rfl, hz⟩)

/-- **`StageOK` transfers to an agreeing actual family.** -/
theorem stageOK_of_agree [MeasurableSpace Ω] (hAg : ∀ ω ∈ Gd, AgreeAt κ θ b₁ J₁ (D₁ ω) (Dh' ω))
    (hGd : ∀ ω ∈ Gd, ¬ ZeroRoot κ θ b₁ J₁ R (D₁ ω) →
      (wRun κ θ b₁ J₁ (D₁ ω) (relOff κ θ b₁ J₁ R (D₁ ω) + 1)).2.2.2.1 (relOff κ θ b₁ J₁ R (D₁ ω)) ≠ none)
    {j : ℕ} {F : ℕ → Ω → Drv}
    (h : StageOK (mρ6 κ θ b₁ J₁ b₂ J₂ R c m Dh' Gd j F) (maskEv κ θ b₁ J₁ b₂ J₂ R c m Dh' Gd j F)
      (mZ Gd (cZ4 κ θ b₁ J₁ R Dh') j F)) :
    StageOK (mρ6 κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F) (maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F)
      (mZ Gd (cZ4 κ θ b₁ J₁ R D₁) j F) := by
  have hM := maskEv_eq_of_agree (b₂ := b₂) (J₂ := J₂) (c := c) (m := m) hAg hGd j F
  have hρ : mρ6 κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F = mρ6 κ θ b₁ J₁ b₂ J₂ R c m Dh' Gd j F := by
    funext ω
    by_cases hω : ω ∈ maskEv κ θ b₁ J₁ b₂ J₂ R c m D₁ Gd j F
    · rw [mρ6_of_mem hω, mρ6_of_mem (hM ▸ hω), cρ3_eq_of_mask hAg hGd hω]
    · rw [mρ6_of_not_mem hω, mρ6_of_not_mem (hM ▸ hω)]
  rw [hρ, hM, mZ_eq_of_agree hAg hGd j F]
  exact h

end Transfer

end InteractingSLE.Theorem14.SB.Nv

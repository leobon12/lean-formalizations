/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdyWord

/-!
# The near selection with its shape and positions pinned (decision D16)

Packet PROVE-GW2-SDE (round 14; DECISIONS-FABLE-4 §D16). BUF's near stop reads the near family only through its
SHAPE `(nL, nR, mL, mR, goLeft)` (`nearBuffer`) and its POSITIONS `xL`, `xR` (the image state). `GW2Sdy.nearSel` takes
the family by choice, so these fields must be pinned by the statement. This file restates the construction with:

* `cutL β`, `cutR β`: the far-block indices as COUNTS (the number of left labels right of `−3`, of right labels left
  of `3`); `card_filter_val_lt`, **`cut_eq_card_antitone`**, **`cut_eq_card_monotone`**: ROOT2's cut is unique, and it
  is this count (the least admissible index);
* **`exists_nearFamily_top_shape`**, **`exists_nearFamily_bottom_shape`**: ROOT2's families with `mL`/`mR` the counts;
* **`exists_nearFamily_top_presentsO_shape`**, **`exists_nearFamily_bottom_presentsO_shape`**: the same in the
  `PresentsO` form of `GW2Sdy.exists_nearFamily_top/bottom_presentsO`, with the positions pinned (`PositionsOf`);
* `nearShape κ s flip c`: the explicit shape (the upper shape when the upper structure holds, else the lower one);
* **`exists_nearSelection_shape`**: the near selection with shape `nearShape …` and positions the flow-line positions
  of the dilated base word `nearDilWord s flip c`;
* `nearSelS`, `nearSelS_shape`, `nearSelS_positions`, `nearSelS_spec`; the package `VPkgXFamily.withNearS`, its near
  words **`frameNNearWord_withNearS`**, `vwordsX_withNearS`, `vpkgXSafe_withNearS`, and the identities BUF needs,
  **`withNearS_shape`** and **`withNearS_positions`** (on every sample where the structure holds).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdo

open Restart GW2JDetR11 GW2Sdf GW2Sdh GW2Sdi GW2Sdx GW2Sdy GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootN4
  GW2TipSystem.RootH10 GW2TipSystem.RootW8 Supp12.DSReach CS3Cross

/-! ### The far-block cut as a count -/

theorem card_filter_val_lt (n m : ℕ) (hm : m ≤ n) : (univ.filter fun i : Fin n => (i : ℕ) < m).card = m := by
  have : (univ.filter fun i : Fin n => (i : ℕ) < m) =
      (Finset.range m).attachFin (fun k hk => (mem_range.1 hk).trans_le hm) := by
    ext i
    simp
  rw [this, card_attachFin, card_range]

/-- **ROOT2's antitone cut is the count of labels beyond the level.** -/
theorem cut_eq_card_antitone {n : ℕ} {x : Fin n → ℝ} {a : ℝ} {m : ℕ} (hm : m ≤ n)
    (hnear : ∀ i : Fin n, (i : ℕ) < m → a < x i) (hfar : ∀ i : Fin n, m ≤ (i : ℕ) → x i ≤ a) :
    (univ.filter fun i => a < x i).card = m := by
  have : (univ.filter fun i => a < x i) = univ.filter fun i : Fin n => (i : ℕ) < m :=
    Finset.filter_congr fun i _ => ⟨fun h => by by_contra h'; exact absurd (hfar i (not_lt.1 h')) (not_le.2 h),
      hnear i⟩
  rw [this, card_filter_val_lt n m hm]

/-- **ROOT2's monotone cut is the count of labels below the level.** -/
theorem cut_eq_card_monotone {n : ℕ} {x : Fin n → ℝ} {a : ℝ} {m : ℕ} (hm : m ≤ n)
    (hnear : ∀ i : Fin n, (i : ℕ) < m → x i < a) (hfar : ∀ i : Fin n, m ≤ (i : ℕ) → a ≤ x i) :
    (univ.filter fun i => x i < a).card = m := by
  have : (univ.filter fun i => x i < a) = univ.filter fun i : Fin n => (i : ℕ) < m :=
    Finset.filter_congr fun i _ => ⟨fun h => by by_contra h'; exact absurd (hfar i (not_lt.1 h')) (not_le.2 h),
      hnear i⟩
  rw [this, card_filter_val_lt n m hm]

/-- The far-block index of the upper family: the number of left labels strictly right of `−3`. -/
def cutL (β : BoundaryWord) : ℕ :=
  (univ.filter fun i : Fin (flowLineNL β.fn β.jumps 0) => -3 < flowLineXL β.fn β.jumps 0 i).card

/-- The far-block index of the lower family: the number of right labels strictly left of `3`. -/
def cutR (β : BoundaryWord) : ℕ :=
  (univ.filter fun j : Fin (flowLineNR β.fn β.jumps 0) => flowLineXR β.fn β.jumps 0 j < 3).card

/-! ### ROOT2's families with the cut pinned -/

section Families

variable {κ : ℝ}

/-- **The upper-extreme near family with its shape pinned** (`GW2Sdy.exists_nearFamily_top` with `mL = cutL β`). -/
theorem exists_nearFamily_top_shape (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord}
    (hOldL : ∀ y ∈ Set.Ioo (-3) 0, y ∉ β.jumps → β.fn y ∈ oldLeftHeights κ)
    (hR : ∀ y, 0 < y → y ∉ β.jumps → β.fn y ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ β.fn y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hxm : flowLineXL β.fn β.jumps 0 (GW2TipStage.lastL β.fn β.jumps) ≤ -3)
    (hxp : 0 < flowLineXR β.fn β.jumps 0 (GW2TipStage.lastR β.fn β.jumps))
    (hfarL : ∀ y, y < flowLineXL β.fn β.jumps 0 (GW2TipStage.lastL β.fn β.jumps) → y ∉ β.jumps →
      β.fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR β.fn β.jumps 0 (GW2TipStage.lastR β.fn β.jumps) < y → y ∉ β.jumps →
      β.fn y = sleLambda (16 / κ) - Real.pi * chiC κ)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (Real.pi / 2))) :
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = true ∧ f.mL = cutL β ∧
      f.mR = flowLineNR β.fn β.jumps 0 - 1 ∧
      ∀ m, FCDet.IsFlowType κ (θs (m + N)) β f.xL f.xR (f.ρLs m) (f.ρRs m) := by
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData β
  have hF := Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0
  obtain ⟨cut, hcut, hnear, hfar⟩ := exists_antitone_cut (flowLineXL β.fn β.jumps 0) hF.1 (-3)
  have hcL : cutL β = cut := cut_eq_card_antitone hcut hnear hfar
  obtain ⟨η, hη, hsepL, hsepR⟩ := exists_positive_separation hF
  obtain ⟨hpL, hpR⟩ := strict_prefixes_top hκ hκ4 hb hOldL hR
  have hsL := (GW2TipStage.sum_flowLineRhoL_eq_of_far hκ hb
    (Real.pi / 2) hfarL).trans (GW2TipStage.totals_far_half_pi hκ).1
  have hsR := (GW2TipStage.sum_flowLineRhoR_eq_of_far hκ hb
    (Real.pi / 2) hfarR).trans (GW2TipStage.totals_far_half_pi hκ).2
  have hρL := (continuous_flowLineRhoL κ β.fn β.jumps).continuousAt.tendsto.comp hθ
  have hρR := (continuous_flowLineRhoR κ β.fn β.jumps).continuousAt.tendsto.comp hθ
  have hpsL : ∀ i : Fin (flowLineNL β.fn β.jumps 0), (i : ℕ) < cut →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoL κ β.fn β.jumps 0 (Real.pi / 2) j :=
    fun i hi => hpL i (hnear i hi)
  have hpsR : ∀ i : Fin (flowLineNR β.fn β.jumps 0), (i : ℕ) < flowLineNR β.fn β.jumps 0 - 1 →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoR κ β.fn β.jumps 0 (Real.pi / 2) j :=
    fun i _ => hpR i
  obtain ⟨Rw, ε, hε, hw₀, N, hN⟩ := exists_ds1_tail hF hpsL hpsR hρL hρR
  let f : NearCrossingFamily.{u} κ :=
    { nL := flowLineNL β.fn β.jumps 0
      nR := flowLineNR β.fn β.jumps 0
      hnL := by unfold flowLineNL; omega
      hnR := by unfold flowLineNR; omega
      xL := flowLineXL β.fn β.jumps 0
      xR := flowLineXR β.fn β.jumps 0
      ρLs := fun m => flowLineRhoL κ β.fn β.jumps 0 (θs (m + N))
      ρRs := fun m => flowLineRhoR κ β.fn β.jumps 0 (θs (m + N))
      ρL₀ := flowLineRhoL κ β.fn β.jumps 0 (Real.pi / 2)
      ρR₀ := flowLineRhoR κ β.fn β.jumps 0 (Real.pi / 2)
      sequence := fun m => GW2JDetR10.referenceEvolution.{u} hκ (flowLineRhoL κ β.fn β.jumps 0 (θs (m + N)))
        (flowLineRhoR κ β.fn β.jumps 0 (θs (m + N))) hF
      limit := GW2JDetR10.referenceEvolution.{u} hκ (flowLineRhoL κ β.fn β.jumps 0 (Real.pi / 2))
        (flowLineRhoR κ β.fn β.jumps 0 (Real.pi / 2)) hF
      mL := cut
      mR := flowLineNR β.fn β.jumps 0 - 1
      Rw := Rw
      ε := ε
      η := η
      goLeft := true
      hε := hε
      hη := hη
      hxL0 := rfl
      hxR0 := rfl
      hxL := hsepL
      hxR := hsepR
      hw := fun m => hN _ (Nat.le_add_left _ _)
      hw₀ := hw₀
      hρL := hρL.comp (tendsto_add_atTop_nat N)
      hρR := hρR.comp (tendsto_add_atTop_nat N)
      hE := fun m => GW2JDetR10.referenceEvolution_isEvolution hκ _ _ hF
      hE₀ := GW2JDetR10.referenceEvolution_isEvolution hκ _ _ hF
      horientation := Or.inl ⟨rfl, rfl, hxp, hxm, hfar, hsL, hsR⟩ }
  exact ⟨f, N, rfl, hcL.symm, rfl, fun m => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The lower-extreme near family with its shape pinned** (`GW2Sdy.exists_nearFamily_bottom` with
`mR = cutR β`). -/
theorem exists_nearFamily_bottom_shape (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord}
    (hL : ∀ y, y < 0 → y ∉ β.jumps → β.fn y ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ β.fn y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hOldR : ∀ y ∈ Set.Ioo 0 3, y ∉ β.jumps → β.fn y ∈ oldRightHeights κ)
    (hxm : flowLineXL β.fn β.jumps 0 (GW2TipStage.lastL β.fn β.jumps) < 0)
    (hxp : 3 ≤ flowLineXR β.fn β.jumps 0 (GW2TipStage.lastR β.fn β.jumps))
    (hfarL : ∀ y, y < flowLineXL β.fn β.jumps 0 (GW2TipStage.lastL β.fn β.jumps) → y ∉ β.jumps →
      β.fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR β.fn β.jumps 0 (GW2TipStage.lastR β.fn β.jumps) < y → y ∉ β.jumps →
      β.fn y = sleLambda (16 / κ) - Real.pi * chiC κ)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (-(Real.pi / 2)))) :
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = false ∧ f.mL = flowLineNL β.fn β.jumps 0 - 1 ∧
      f.mR = cutR β ∧ ∀ m, FCDet.IsFlowType κ (θs (m + N)) β f.xL f.xR (f.ρLs m) (f.ρRs m) := by
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData β
  have hF := Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0
  obtain ⟨cut, hcut, hnear, hfar⟩ := exists_monotone_cut (flowLineXR β.fn β.jumps 0) hF.2.2.1 3
  have hcR : cutR β = cut := cut_eq_card_monotone hcut hnear hfar
  obtain ⟨η, hη, hsepL, hsepR⟩ := exists_positive_separation hF
  obtain ⟨hpL, hpR⟩ := strict_prefixes_bottom hκ hκ4 hb hL hOldR
  have hsL := (GW2TipStage.sum_flowLineRhoL_eq_of_far hκ hb
    (-(Real.pi / 2)) hfarL).trans (GW2TipStage.totals_far_neg_half_pi hκ).1
  have hsR := (GW2TipStage.sum_flowLineRhoR_eq_of_far hκ hb
    (-(Real.pi / 2)) hfarR).trans (GW2TipStage.totals_far_neg_half_pi hκ).2
  have hρL := (continuous_flowLineRhoL κ β.fn β.jumps).continuousAt.tendsto.comp hθ
  have hρR := (continuous_flowLineRhoR κ β.fn β.jumps).continuousAt.tendsto.comp hθ
  have hpsL : ∀ i : Fin (flowLineNL β.fn β.jumps 0), (i : ℕ) < flowLineNL β.fn β.jumps 0 - 1 →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoL κ β.fn β.jumps 0 (-(Real.pi / 2)) j :=
    fun i _ => hpL i
  have hpsR : ∀ i : Fin (flowLineNR β.fn β.jumps 0), (i : ℕ) < cut →
      -2 < ∑ j ∈ univ.filter (fun j => j ≤ i), flowLineRhoR κ β.fn β.jumps 0 (-(Real.pi / 2)) j :=
    fun i hi => hpR i (hnear i hi)
  obtain ⟨Rw, ε, hε, hw₀, N, hN⟩ := exists_ds1_tail hF hpsL hpsR hρL hρR
  let f : NearCrossingFamily.{u} κ :=
    { nL := flowLineNL β.fn β.jumps 0
      nR := flowLineNR β.fn β.jumps 0
      hnL := by unfold flowLineNL; omega
      hnR := by unfold flowLineNR; omega
      xL := flowLineXL β.fn β.jumps 0
      xR := flowLineXR β.fn β.jumps 0
      ρLs := fun m => flowLineRhoL κ β.fn β.jumps 0 (θs (m + N))
      ρRs := fun m => flowLineRhoR κ β.fn β.jumps 0 (θs (m + N))
      ρL₀ := flowLineRhoL κ β.fn β.jumps 0 (-(Real.pi / 2))
      ρR₀ := flowLineRhoR κ β.fn β.jumps 0 (-(Real.pi / 2))
      sequence := fun m => GW2JDetR10.referenceEvolution.{u} hκ (flowLineRhoL κ β.fn β.jumps 0 (θs (m + N)))
        (flowLineRhoR κ β.fn β.jumps 0 (θs (m + N))) hF
      limit := GW2JDetR10.referenceEvolution.{u} hκ (flowLineRhoL κ β.fn β.jumps 0 (-(Real.pi / 2)))
        (flowLineRhoR κ β.fn β.jumps 0 (-(Real.pi / 2))) hF
      mL := flowLineNL β.fn β.jumps 0 - 1
      mR := cut
      Rw := Rw
      ε := ε
      η := η
      goLeft := false
      hε := hε
      hη := hη
      hxL0 := rfl
      hxR0 := rfl
      hxL := hsepL
      hxR := hsepR
      hw := fun m => hN _ (Nat.le_add_left _ _)
      hw₀ := hw₀
      hρL := hρL.comp (tendsto_add_atTop_nat N)
      hρR := hρR.comp (tendsto_add_atTop_nat N)
      hE := fun m => GW2JDetR10.referenceEvolution_isEvolution hκ _ _ hF
      hE₀ := GW2JDetR10.referenceEvolution_isEvolution hκ _ _ hF
      horientation := Or.inr ⟨rfl, rfl, hxm, hxp, hfar, hsR, hsL⟩ }
  exact ⟨f, N, rfl, rfl, hcR.symm, fun m => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Families

/-! ### The explicit shape and the pinned selection -/

/-- The shape of a near family: `(nL, nR, mL, mR, goLeft)` (what `nearBuffer` reads). -/
def famShape {κ : ℝ} (f : NearCrossingFamily.{u} κ) : ℕ × ℕ × ℕ × ℕ × Bool := (f.nL, f.nR, f.mL, f.mR, f.goLeft)

open Classical in
/-- **The explicit shape of the near family of a base word**: the upper shape when the dilated base word has the upper
structure, the lower shape otherwise. -/
def nearShape (κ : ℝ) (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) : ℕ × ℕ × ℕ × ℕ × Bool :=
  if NearStructTop κ s flip c then
    (flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0, cutL (nearDilWord s flip c),
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1, true)
  else
    (flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
      flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0,
      flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1, cutR (nearDilWord s flip c), false)

/-- **The positions of a near family are the flow-line positions of a word** (with the casts of
`FCDet.IsFlowType`). -/
def PositionsOf {κ : ℝ} (f : NearCrossingFamily.{u} κ) (β : BoundaryWord) : Prop :=
  ∃ (eL : flowLineNL β.fn β.jumps 0 = f.nL) (eR : flowLineNR β.fn β.jumps 0 = f.nR),
    (fun i => f.xL (Fin.cast eL i)) = flowLineXL β.fn β.jumps 0 ∧
      (fun j => f.xR (Fin.cast eR j)) = flowLineXR β.fn β.jumps 0

theorem positionsOf_of_isFlowType {κ θ : ℝ} {f : NearCrossingFamily.{u} κ} {β : BoundaryWord} {ρL : Fin f.nL → ℝ}
    {ρR : Fin f.nR → ℝ} (h : FCDet.IsFlowType κ θ β f.xL f.xR ρL ρR) : PositionsOf f β := by
  obtain ⟨eL, eR, hxL, hxR, -, -⟩ := h
  exact ⟨eL, eR, hxL, hxR⟩

/-- **`exists_nearFamily_top_presentsO` with the shape and positions pinned** (decision D16, ruling R121): the upper
family's far-block index is the count `cutL` of the dilated base word, its last right index is `nR − 1`, and its
positions are the dilated base word's flow-line positions. -/
theorem exists_nearFamily_top_presentsO_shape {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {s : ℝ≥0} (hs : s ≠ 0)
    (flip : Bool) {c : BoundaryWord} (h : NearStructTop κ s flip c) {θs : ℕ → ℝ}
    (hθ : Tendsto θs atTop (𝓝 (Real.pi / 2))) :
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = true ∧ f.mL = cutL (nearDilWord s flip c) ∧
      f.mR = flowLineNR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1 ∧
      PositionsOf f (nearDilWord s flip c) ∧ ∀ m,
        GW2Sdf.PresentsO κ (GW2Rd.upW (nearSign flip * θs (m + N) * chiC κ) c) s flip f.xL (f.ρLs m) f.xR
          (f.ρRs m) := by
  obtain ⟨f, N, hgo, hmL, hmR, hf⟩ :=
    exists_nearFamily_top_shape.{u} hκ hκ4 h.oldL h.right h.xm h.xp h.farL h.farR hθ
  exact ⟨f, N, hgo, hmL, hmR, positionsOf_of_isFlowType (hf 0),
    fun m => presentsO_of_isFlowType_nearDilWord hs flip (hf m)⟩

/-- **`exists_nearFamily_bottom_presentsO` with the shape and positions pinned** (decision D16, ruling R121). -/
theorem exists_nearFamily_bottom_presentsO_shape {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {s : ℝ≥0} (hs : s ≠ 0)
    (flip : Bool) {c : BoundaryWord} (h : NearStructBot κ s flip c) {θs : ℕ → ℝ}
    (hθ : Tendsto θs atTop (𝓝 (-(Real.pi / 2)))) :
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = false ∧
      f.mL = flowLineNL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0 - 1 ∧
      f.mR = cutR (nearDilWord s flip c) ∧ PositionsOf f (nearDilWord s flip c) ∧ ∀ m,
        GW2Sdf.PresentsO κ (GW2Rd.upW (nearSign flip * θs (m + N) * chiC κ) c) s flip f.xL (f.ρLs m) f.xR
          (f.ρRs m) := by
  obtain ⟨f, N, hgo, hmL, hmR, hf⟩ :=
    exists_nearFamily_bottom_shape.{u} hκ hκ4 h.left h.oldR h.xm h.xp h.farL h.farR hθ
  exact ⟨f, N, hgo, hmL, hmR, positionsOf_of_isFlowType (hf 0),
    fun m => presentsO_of_isFlowType_nearDilWord hs flip (hf m)⟩

/-- **The near selection with its shape and positions pinned** (decision D16): under the structure, a near family whose
shape is `nearShape κ s flip c` and whose positions are the flow-line positions of the dilated base word, and angle
indices `ι` such that its word at `m` presents the raised base word at the angle of `ι m`. -/
theorem exists_nearSelection_shape {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω)
    (r : ScaledRootIdx cs.Θ cs.Q) {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord}
    (h : NearStruct cs.κ s flip c) :
    ∃ (f : NearCrossingFamily.{u} cs.κ) (ι : ℕ → ℕ), famShape f = nearShape cs.κ s flip c ∧
      PositionsOf f (nearDilWord s flip c) ∧ ∀ m,
        PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r (ι m) : ℝ) * chiC cs.κ) c) s flip f.xL (f.ρLs m)
          f.xR (f.ρRs m) := by
  classical
  -- angle indices with `nearSign flip · angle → θ₀`
  have hidx : ∀ θ₀ : ℝ, (θ₀ = Real.pi / 2 ∨ θ₀ = -(Real.pi / 2)) → ∃ ι₀ : ℕ → ℕ,
      Tendsto (fun m => nearSign flip * (RootJ31.angleEnumeration cs r (ι₀ m) : ℝ)) atTop (𝓝 θ₀) := by
    intro θ₀ hθ₀
    have hθ₀' : nearSign flip * θ₀ = Real.pi / 2 ∨ nearSign flip * θ₀ = -(Real.pi / 2) := by
      cases flip <;> rcases hθ₀ with rfl | rfl <;> simp [nearSign]
    obtain ⟨ι₀, hι₀⟩ := exists_angleIdx_tendsto cs r hθ₀'
    refine ⟨ι₀, ?_⟩
    have := hι₀.const_mul (nearSign flip)
    rwa [← mul_assoc, nearSign_mul_self, one_mul] at this
  -- the presentation at the angle of `ι₀ (m + N)`
  have hpres : ∀ (f : NearCrossingFamily.{u} cs.κ) (ι₀ : ℕ → ℕ) (N : ℕ),
      (∀ m, FCDet.IsFlowType cs.κ (nearSign flip * (RootJ31.angleEnumeration cs r (ι₀ (m + N)) : ℝ))
        (nearDilWord s flip c) f.xL f.xR (f.ρLs m) (f.ρRs m)) →
      ∀ m, PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r (ι₀ (m + N)) : ℝ) * chiC cs.κ) c) s flip f.xL
        (f.ρLs m) f.xR (f.ρRs m) := by
    intro f ι₀ N hf m
    have := presentsO_of_isFlowType_nearDilWord hs flip (hf m)
    rwa [← mul_assoc, nearSign_mul_self, one_mul] at this
  by_cases ht : NearStructTop cs.κ s flip c
  · obtain ⟨ι₀, hι₀⟩ := hidx _ (Or.inl rfl)
    obtain ⟨f, N, hgo, hmL, hmR, hf⟩ := exists_nearFamily_top_shape.{u} cs.hκ cs.hκ4 ht.oldL ht.right ht.xm ht.xp
      ht.farL ht.farR hι₀
    obtain ⟨eL, eR, -, -, -, -⟩ := hf 0
    refine ⟨f, fun m => ι₀ (m + N), ?_, positionsOf_of_isFlowType (hf 0), hpres f ι₀ N hf⟩
    simp only [famShape, nearShape, ht, ↓reduceIte, hgo, hmL, hmR, eL, eR]
  · have hb : NearStructBot cs.κ s flip c := h.resolve_left ht
    obtain ⟨ι₀, hι₀⟩ := hidx _ (Or.inr rfl)
    obtain ⟨f, N, hgo, hmL, hmR, hf⟩ := exists_nearFamily_bottom_shape.{u} cs.hκ cs.hκ4 hb.left hb.oldR hb.xm hb.xp
      hb.farL hb.farR hι₀
    obtain ⟨eL, eR, -, -, -, -⟩ := hf 0
    refine ⟨f, fun m => ι₀ (m + N), ?_, positionsOf_of_isFlowType (hf 0), hpres f ι₀ N hf⟩
    simp only [famShape, nearShape, ht, ↓reduceIte, hgo, hmL, hmR, eL, eR]

open Classical in
/-- **The pinned near selection** at a history and sample: under the structure, `exists_nearSelection_shape`'s family
and angle indices; otherwise the default family and the identity. -/
def nearSelS {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q) (s : ℝ≥0)
    (flip : Bool) (c : BoundaryWord) (f₀ : NearCrossingFamily.{u} cs.κ) :
    NearCrossingFamily.{u} cs.κ × (ℕ → ℕ) :=
  if h : s ≠ 0 ∧ NearStruct cs.κ s flip c then
    ((exists_nearSelection_shape cs r h.1 flip h.2).choose,
      (exists_nearSelection_shape cs r h.1 flip h.2).choose_spec.choose)
  else (f₀, id)

section Sel

variable {Ω : Type u} [MeasurableSpace Ω] (cs : SourceData Ω) (r : ScaledRootIdx cs.Θ cs.Q) {s : ℝ≥0}
  (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord} (h : NearStruct cs.κ s flip c) (f₀ : NearCrossingFamily.{u} cs.κ)

include hs h in
theorem nearSelS_eq :
    nearSelS cs r s flip c f₀ = ((exists_nearSelection_shape cs r hs flip h).choose,
      (exists_nearSelection_shape cs r hs flip h).choose_spec.choose) := by
  unfold nearSelS
  split_ifs with h'
  · rfl
  · exact absurd ⟨hs, h⟩ h'

include hs h in
/-- **The pinned selection's shape** is `nearShape`. -/
theorem nearSelS_shape : famShape (nearSelS cs r s flip c f₀).1 = nearShape cs.κ s flip c := by
  rw [nearSelS_eq cs r hs flip h f₀]
  exact (exists_nearSelection_shape cs r hs flip h).choose_spec.choose_spec.1

include hs h in
/-- **The pinned selection's positions** are the flow-line positions of the dilated base word. -/
theorem nearSelS_positions : PositionsOf (nearSelS cs r s flip c f₀).1 (nearDilWord s flip c) := by
  rw [nearSelS_eq cs r hs flip h f₀]
  exact (exists_nearSelection_shape cs r hs flip h).choose_spec.choose_spec.2.1

include hs h in
theorem nearSelS_spec (m : ℕ) :
    PresentsO cs.κ (GW2Rd.upW ((RootJ31.angleEnumeration cs r ((nearSelS cs r s flip c f₀).2 m) : ℝ) *
      chiC cs.κ) c) s flip (nearSelS cs r s flip c f₀).1.xL ((nearSelS cs r s flip c f₀).1.ρLs m)
      (nearSelS cs r s flip c f₀).1.xR ((nearSelS cs r s flip c f₀).1.ρRs m) := by
  rw [nearSelS_eq cs r hs flip h f₀]
  exact (exists_nearSelection_shape cs r hs flip h).choose_spec.choose_spec.2.2 m

end Sel

/-! ### The package with the pinned selection -/

/-- **The package with the pinned near selection** (`GW2Sdy.VPkgXFamily.withNear` with `nearSelS`). -/
def _root_.InteractingSLE.Theorem14.GW2Sdx.VPkgXFamily.withNearS (V : VPkgXFamily.{u}) (lam : NearDil.{u})
    (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
    (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ) : VPkgXFamily.{u} :=
  fun Ω _ _ c r =>
    { V Ω c r with
      nearFamily := fun l ω => (nearSelS c r (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length)
        (base Ω c r l ω) ((V Ω c r).nearFamily l ω)).1
      nearCandidate := fun l ω n m => Nat.pair ((nearSelS c r (nearRootScale r.2 (lam Ω c r l ω))
        (flipOf l.length) (base Ω c r l ω) ((V Ω c r).nearFamily l ω)).2 m) (kSel Ω c r l ω n m) }

section Pkg

variable (V : VPkgXFamily.{u}) (lam : NearDil.{u})
  (base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord)
  (kSel : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → ℕ → ℕ → ℕ)

/-- **The shape identity BUF reads** (decision D16): where the structure holds, the package's near family has the
explicit shape `nearShape` of the base word. -/
theorem withNearS_shape (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (hlam : lam Ω c r l ω ≠ 0)
    (h : NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    famShape (((V.withNearS lam base kSel) Ω c r).nearFamily l ω) =
      nearShape c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω) :=
  nearSelS_shape c r (nearRootScale_ne_zero r.2 hlam) (flipOf l.length) h _

/-- **The position identity BUF reads** (decision D16): where the structure holds, the package's near family has the
flow-line positions of the dilated base word. -/
theorem withNearS_positions (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) (hlam : lam Ω c r l ω ≠ 0)
    (h : NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    PositionsOf (((V.withNearS lam base kSel) Ω c r).nearFamily l ω)
      (nearDilWord (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :=
  nearSelS_positions c r (nearRootScale_ne_zero r.2 hlam) (flipOf l.length) h _

/-- **The near words of the package with the pinned selection** (as `GW2Sdy.frameNNearWord_withNear`). -/
theorem frameNNearWord_withNearS {D : ConstructionFamily.{u}}
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i k : ℕ,
        ((V Ω c r).nearVar l n m (Nat.pair i k)).record ω ∈ ((V Ω c r).nearVar l n m (Nat.pair i k)).E ∧
        ((V Ω c r).nearVar l n m (Nat.pair i k)).β (((V Ω c r).nearVar l n m (Nat.pair i k)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (base Ω c r l ω))
    (hstruct : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω)) :
    FrameNNearWord D (((V.withNearS lam base kSel).at 0).frameN lam) := by
  intro Ω _ _ c r l
  filter_upwards [hword Ω c r l, hstruct Ω c r l] with ω hw hs halive n
  filter_upwards [hw halive n] with m hm
  set s := nearRootScale r.2 (lam Ω c r l ω)
  have hs0 : s ≠ 0 := nearRootScale_ne_zero r.2 (hlam Ω c r l ω)
  set sel := nearSelS c r s (flipOf l.length) (base Ω c r l ω) ((V Ω c r).nearFamily l ω)
  obtain ⟨hE, hβ⟩ := hm (sel.2 m) (kSel Ω c r l ω n m)
  refine ⟨hE, ?_⟩
  show PresentsO c.κ (((V Ω c r).nearVar l n m (Nat.pair (sel.2 m) (kSel Ω c r l ω n m))).β
    (((V Ω c r).nearVar l n m (Nat.pair (sel.2 m) (kSel Ω c r l ω n m))).record ω)) s (flipOf l.length)
    sel.1.xL (sel.1.ρLs m) sel.1.xR (sel.1.ρRs m)
  rw [hβ]
  exact nearSelS_spec c r hs0 (flipOf l.length) (hs halive) ((V Ω c r).nearFamily l ω) m

/-- The pinned selection changes neither the stage variables nor the shells. -/
theorem vpkgXSafe_withNearS {V : VPkgXFamily.{u}} (hV : VPkgXSafe V) : VPkgXSafe (V.withNearS lam base kSel) :=
  ⟨hV.nearSafe, hV.slowSafe⟩

/-- **The words of the package with the pinned selection**: its near words, and the package's slow words. -/
theorem vwordsX_withNearS {D : ConstructionFamily.{u}}
    (hlam : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (ω : Ω), lam Ω c r l ω ≠ 0)
    (hword : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l → ∀ n : ℕ, ∀ᶠ m in atTop, ∀ i k : ℕ,
        ((V Ω c r).nearVar l n m (Nat.pair i k)).record ω ∈ ((V Ω c r).nearVar l n m (Nat.pair i k)).E ∧
        ((V Ω c r).nearVar l n m (Nat.pair i k)).β (((V Ω c r).nearVar l n m (Nat.pair i k)).record ω) =
          GW2Rd.upW ((RootJ31.angleEnumeration c r i : ℝ) * chiC c.κ) (base Ω c r l ω))
    (hstruct : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)),
      ∀ᵐ ω ∂c.P, ω ∈ ((D Ω c).experiment r).data.alive ((D Ω c).G r) l →
        NearStruct c.κ (nearRootScale r.2 (lam Ω c r l ω)) (flipOf l.length) (base Ω c r l ω))
    (hslow : FrameNSlowWordN D fun n => (V.at n).frameN lam) :
    VWordsX D (V.withNearS lam base kSel) lam :=
  ⟨frameNNearWord_withNearS V lam base kSel hlam hword hstruct, hslow⟩

end Pkg

end InteractingSLE.Theorem14.GW2Sdo

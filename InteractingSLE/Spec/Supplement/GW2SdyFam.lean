/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdyDil
import InteractingSLE.Spec.Supplement.GW2RootH10Cross
import InteractingSLE.Spec.Supplement.GW2JDetR10Evolution
import InteractingSLE.Spec.Supplement.GW2RootJ31Program

/-!
# Near families presenting a joint-chart word, and candidate angles tending to `±π/2`

Packet PROVE-GW2-SDE (round 11). The parts of the near-model identification (spec pp. 621–623) that do not depend on
how the stage word is produced:

* **`exists_nearFamily_top`** / **`exists_nearFamily_bottom`**: for a word `β` with the structure ROOT2's
  `RootH10.exists_crossing_top/bottom` assume (old heights inside `(∓3, 0)`, the far heights `∓λ′ ± πχ` beyond the
  last labels, a far label beyond `∓3`) and angles `θs → ±π/2`, an N4 near-crossing family `f` and a shift `N` such
  that `f`'s word at index `m` IS the flow-line word of `β` at angle `θs (m + N)`. The evolutions are ROOT2/JOINTDET's
  reference evolutions (`GW2JDetR10.referenceEvolution`, Theorem 2.2), not inputs; the DS1 constants come from
  `RootW8.exists_ds1_tail`.
* **`presentsO_nearFamily_top`** / **`presentsO_nearFamily_bottom`**: with `β = dilW (√s)⁻¹ c` (or its mirror), the
  family presents the raised stage word `upW (±θs (m + N) χ) c` at the near scale `s` (`GW2SdyDil`).
* **`exists_angleIdx_tendsto`**: indices `ι m` with `angleEnumeration c r (ι m) → ±π/2` (the source's angle set
  `Θ ⊆ (−π/2, π/2)` is dense); `candidateAngle_pair`: every candidate `Nat.pair (ι m) k` has angle
  `angleEnumeration (ι m)`, whatever its cap and buffer components `k` are.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Sdy

open Restart GW2TipSystem GW2TipSystem.RootN4 GW2TipSystem.RootH10 GW2TipSystem.RootW8 Supp12.DSReach CS3Cross

section Families

variable {κ : ℝ}

/-- **The upper-extreme near family of a word** (ROOT2's `exists_crossing_top` construction, with reference
evolutions and the DS1 tail made explicit): its word at index `m` is the flow-line word of `β` at angle `θs (m + N)`,
and it goes left. -/
theorem exists_nearFamily_top (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord}
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
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = true ∧
      ∀ m, FCDet.IsFlowType κ (θs (m + N)) β f.xL f.xR (f.ρLs m) (f.ρRs m) := by
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData β
  have hF := Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0
  obtain ⟨cut, -, hnear, hfar⟩ := exists_antitone_cut (flowLineXL β.fn β.jumps 0) hF.1 (-3)
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
  exact ⟨f, N, rfl, fun m => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- **The lower-extreme near family of a word** (ROOT2's `exists_crossing_bottom` construction): its word at index
`m` is the flow-line word of `β` at angle `θs (m + N)`, and it goes right. -/
theorem exists_nearFamily_bottom (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord}
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
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = false ∧
      ∀ m, FCDet.IsFlowType κ (θs (m + N)) β f.xL f.xR (f.ρLs m) (f.ρRs m) := by
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData β
  have hF := Theorem15.isOrderedForceWord_flowLine β.fn β.jumps 0
  obtain ⟨cut, -, hnear, hfar⟩ := exists_monotone_cut (flowLineXR β.fn β.jumps 0) hF.2.2.1 3
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
  exact ⟨f, N, rfl, fun m => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

end Families

/-! ### The families present the raised stage word -/

/-- The dilated word of a history: `dilW (√s)⁻¹ c` (even histories) or of the sorted mirror word (odd histories). -/
def nearDilWord (s : ℝ≥0) (flip : Bool) (c : BoundaryWord) : BoundaryWord :=
  match flip with
  | false => dilW (Real.sqrt s)⁻¹ c
  | true => dilW (Real.sqrt s)⁻¹ (FCPlumb.FCKerD.sreflWord c)

/-- The sign of the raising angle: `1` on even histories, `−1` on odd ones. -/
def nearSign (flip : Bool) : ℝ := if flip then -1 else 1

/-- **A typing of the history's dilated word presents the raised stage word.** -/
theorem presentsO_of_isFlowType_nearDilWord {κ θ : ℝ} {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool) {c : BoundaryWord}
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ}
    (h : FCDet.IsFlowType κ θ (nearDilWord s flip c) xL xR ρL ρR) :
    GW2Sdf.PresentsO κ (GW2Rd.upW (nearSign flip * θ * chiC κ) c) s flip xL ρL xR ρR := by
  cases flip with
  | false =>
    simp only [nearSign, Bool.false_eq_true, ↓reduceIte, one_mul]
    exact presentsO_of_isFlowType_dilW hs h
  | true =>
    simp only [nearSign, ↓reduceIte, neg_one_mul]
    exact presentsO_true_of_isFlowType_dilW hs h

/-- **The upper-extreme family of a history presents the raised stage words**: if the history's dilated word has
ROOT2's upper structure and `θs → π/2`, then a near family's word at `m` presents
`upW (nearSign flip · θs (m + N) · χ) c` at the near scale `s`. -/
theorem exists_nearFamily_top_presentsO {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {s : ℝ≥0} (hs : s ≠ 0) (flip : Bool)
    {c : BoundaryWord}
    (hOldL : ∀ y ∈ Set.Ioo (-3) 0, y ∉ (nearDilWord s flip c).jumps →
      (nearDilWord s flip c).fn y ∈ oldLeftHeights κ)
    (hR : ∀ y, 0 < y → y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ (nearDilWord s flip c).fn y = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ)
    (hxm : flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) ≤ -3)
    (hxp : 0 < flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps))
    (hfarL : ∀ y, y < flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) → y ∉ (nearDilWord s flip c).jumps →
        (nearDilWord s flip c).fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < y →
        y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y = sleLambda (16 / κ) - Real.pi * chiC κ)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (Real.pi / 2))) :
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = true ∧ ∀ m,
      GW2Sdf.PresentsO κ (GW2Rd.upW (nearSign flip * θs (m + N) * chiC κ) c) s flip f.xL (f.ρLs m) f.xR (f.ρRs m) := by
  obtain ⟨f, N, hgo, hf⟩ := exists_nearFamily_top.{u} hκ hκ4 hOldL hR hxm hxp hfarL hfarR hθ
  exact ⟨f, N, hgo, fun m => presentsO_of_isFlowType_nearDilWord hs flip (hf m)⟩

/-- **The lower-extreme family of a history presents the raised stage words** (`θs → −π/2`). -/
theorem exists_nearFamily_bottom_presentsO {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {s : ℝ≥0} (hs : s ≠ 0)
    (flip : Bool) {c : BoundaryWord}
    (hL : ∀ y, y < 0 → y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ (nearDilWord s flip c).fn y = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ)
    (hOldR : ∀ y ∈ Set.Ioo 0 3, y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y ∈ oldRightHeights κ)
    (hxm : flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < 0)
    (hxp : 3 ≤ flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps))
    (hfarL : ∀ y, y < flowLineXL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastL (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) → y ∉ (nearDilWord s flip c).jumps →
        (nearDilWord s flip c).fn y = -sleLambda (16 / κ) + Real.pi * chiC κ)
    (hfarR : ∀ y, flowLineXR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps 0
      (GW2TipStage.lastR (nearDilWord s flip c).fn (nearDilWord s flip c).jumps) < y →
        y ∉ (nearDilWord s flip c).jumps → (nearDilWord s flip c).fn y = sleLambda (16 / κ) - Real.pi * chiC κ)
    {θs : ℕ → ℝ} (hθ : Tendsto θs atTop (𝓝 (-(Real.pi / 2)))) :
    ∃ (f : NearCrossingFamily.{u} κ) (N : ℕ), f.goLeft = false ∧ ∀ m,
      GW2Sdf.PresentsO κ (GW2Rd.upW (nearSign flip * θs (m + N) * chiC κ) c) s flip f.xL (f.ρLs m) f.xR (f.ρRs m) := by
  obtain ⟨f, N, hgo, hf⟩ := exists_nearFamily_bottom.{u} hκ hκ4 hL hOldR hxm hxp hfarL hfarR hθ
  exact ⟨f, N, hgo, fun m => presentsO_of_isFlowType_nearDilWord hs flip (hf m)⟩

/-! ### Candidate angles tending to `±π/2` -/

section Angles

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The two extreme angles are limits of the source's angle set. -/
theorem half_pi_mem_closure (c : RootC24.SourceData Ω) :
    Real.pi / 2 ∈ closure c.Θ ∧ -(Real.pi / 2) ∈ closure c.Θ := by
  have hlt : -(Real.pi / 2) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hsub : Icc (-(Real.pi / 2)) (Real.pi / 2) ⊆ closure c.Θ := by
    rw [← closure_Ioo hlt.ne]
    exact closure_minimal c.hΘd isClosed_closure
  exact ⟨hsub ⟨hlt.le, le_rfl⟩, hsub ⟨le_rfl, hlt.le⟩⟩

/-- **Angle indices tending to an extreme angle**: for `±π/2`, indices `ι m` of the source's angle enumeration with
`angleEnumeration c r (ι m) → ±π/2`. -/
theorem exists_angleIdx_tendsto (c : RootC24.SourceData Ω) (r : GW2TipSystem.ScaledRootIdx c.Θ c.Q) {θ₀ : ℝ}
    (hθ₀ : θ₀ = Real.pi / 2 ∨ θ₀ = -(Real.pi / 2)) :
    ∃ ι : ℕ → ℕ, Tendsto (fun m => (RootJ31.angleEnumeration c r (ι m) : ℝ)) atTop (𝓝 θ₀) := by
  have hmem : θ₀ ∈ closure c.Θ := by
    rcases hθ₀ with rfl | rfl
    · exact (half_pi_mem_closure c).1
    · exact (half_pi_mem_closure c).2
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hmem
  have hsurj := RootJ31.angleEnumeration_surjective c r
  refine ⟨fun m => Function.surjInv hsurj ⟨x m, hx m⟩, ?_⟩
  have he : ∀ m, (RootJ31.angleEnumeration c r (Function.surjInv hsurj ⟨x m, hx m⟩) : ℝ) = x m := fun m => by
    rw [Function.surjInv_eq hsurj]
  simpa only [he] using hlim

/-- **Every candidate with angle index `i` has angle `angleEnumeration i`**, whatever its cap and buffer
components. -/
theorem candidateAngle_pair (c : RootC24.SourceData Ω) (r : GW2TipSystem.ScaledRootIdx c.Θ c.Q) (i k : ℕ) :
    RootJ31.candidateAngle c r (Nat.pair i k) = RootJ31.angleEnumeration c r i := by
  simp only [RootJ31.candidateAngle, Nat.unpair_pair]

end Angles

end InteractingSLE.Theorem14.GW2Sdy

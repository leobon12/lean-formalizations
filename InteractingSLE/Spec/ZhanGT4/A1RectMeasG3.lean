/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1RectMeasHeight
import InteractingSLE.Spec.ZhanGT4.A1AsmG3
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Times
import InteractingSLE.Spec.ZhanGT4.DualSeedJoint2Inputs

/-!
# Zhan's A.1 (G3): the measurability input `G3RectMeas` PROVED

Packet PROVE-A1-RECTMEAS. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`ig1_followup_proofs.txt` L300–L407).

A1-ASSEMBLE reduced A.1 (G3) to named inputs; `A1Asm.G3RectMeas κ` is the measurability of the seeded height field of
every cofinal rectangle at measurable random times (`A1Patch.IsFieldMeas`). The records go through the chosen image
chain `imgChain` (a `Classical.choose`). No measurable selection is needed:

* **the frozen height is treated as a random variable** (`A1RectMeasHeight`): at a fixed own time the seeded logarithm
  at any measurable random height is measurable, through the unique mapping-out function of the random frozen hull;
* **the own time is rounded** (`isFieldMeas_of_height`): dyadic rounding (`measurable_comp_of_sepCont`) needs only the
  continuity of the columns, which is the column calculus of A1-G3CALC (`IsSourceColumnG.calculus`).

In particular no continuity of the rows in the frozen height is used (for G3 the row identity is open, A1-G3ROW).

## Main results

* **`isFieldMeas_of_height`**: `IsFieldMeas` from random-height measurability and column continuity;
* **`measurable_g3Rec_height`**, **`continuousOn_g3Rec_column`**, **`isFieldMeas_g3Rec`**: the G3 records;
* **`g3RectMeas`**: `A1Asm.G3RectMeas κ` for every `κ`;
* **`a1DualCouplingG3SeedGStatement_of_rowLaw`**: `G3RectRow κ → G3RectLaw κ → A1DualCouplingG3SeedGStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1RectMeas

open QuantumZipper (H IsForwardSol fwdMap fwdHull)
open A2X A1EightSeed A1SeedField A1G3Calc A1Common A1Asm A1Marg A1Patch

/-! ### Rounding the own time -/

section Round

/-- **Measurability on the rectangle from random heights and continuous columns.** If at every fixed own time `s` the
field is measurable at every measurable random height inside the rectangle, and every column `s ↦ N ω s t` is
continuous on `[0, S₁]`, then the field is measurable at measurable random times in the rectangle. -/
theorem isFieldMeas_of_height {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {N : X × Y → ℝ → ℝ → ℝ}
    {S₁ : X → ℝ≥0} {S₂ : Y → ℝ≥0}
    (hm : ∀ τ : X × Y → ℝ, Measurable τ → (∀ ω, 0 ≤ τ ω) → (∀ ω, τ ω ≤ S₂ ω.2) → ∀ s : ℝ, 0 ≤ s →
      Measurable ({ω : X × Y | s ≤ S₁ ω.1}.indicator fun ω => N ω s (τ ω)))
    (hc : ∀ ω, ∀ t ∈ Icc (0 : ℝ) (S₂ ω.2), ContinuousOn (fun s => N ω s t) (Icc (0 : ℝ) (S₁ ω.1))) :
    IsFieldMeas N (fun _ : Unit => S₁) (fun _ : Unit => S₂) := by
  intro U V hU hV hU0 hV0 hUV
  have hle : ∀ ω, U ω ≤ S₁ ω.1 ∧ V ω ≤ S₂ ω.2 := fun ω => (hUV ω).choose_spec
  refine measurable_comp_of_sepCont (f := fun ω a _ => N ω a (V ω)) (Y := fun _ => (0 : ℝ)) hU measurable_const
    hU0 (fun _ => le_rfl) (fun a b ha _ => ?_)
    (fun ω _ _ => (hc ω (V ω) ⟨hV0 ω, (hle ω).2⟩).mono (Icc_subset_Icc_right (hle ω).1))
    (fun _ => continuousOn_const)
  have hmeas := hm V hV hV0 (fun ω => (hle ω).2) a ha
  by_cases hb : b ≤ 0
  · have e : {ω : X × Y | a ≤ U ω ∧ b ≤ (fun _ => (0 : ℝ)) ω}.indicator (fun ω => N ω a (V ω)) =
        {ω : X × Y | a ≤ U ω}.indicator ({ω : X × Y | a ≤ S₁ ω.1}.indicator fun ω => N ω a (V ω)) := by
      funext ω
      by_cases hω : a ≤ U ω
      · have h1 : ω ∈ {ω : X × Y | a ≤ U ω ∧ b ≤ (fun _ => (0 : ℝ)) ω} := ⟨hω, hb⟩
        have h2 : ω ∈ {ω : X × Y | a ≤ S₁ ω.1} := hω.trans (hle ω).1
        rw [indicator_of_mem h1, indicator_of_mem (show ω ∈ {ω : X × Y | a ≤ U ω} from hω),
          indicator_of_mem h2]
      · have h1 : ω ∉ {ω : X × Y | a ≤ U ω ∧ b ≤ (fun _ => (0 : ℝ)) ω} := fun h => hω h.1
        rw [indicator_of_notMem h1, indicator_of_notMem (show ω ∉ {ω : X × Y | a ≤ U ω} from hω)]
    rw [e]
    exact hmeas.indicator (measurableSet_le measurable_const hU)
  · have e : {ω : X × Y | a ≤ U ω ∧ b ≤ (fun _ => (0 : ℝ)) ω} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun _ => hb
    rw [e, indicator_empty]
    exact measurable_const

end Round

/-! ### Stopped drivers -/

section Stop

/-- `stopDrv w T` reads only nonnegative times: its value at `r` is its value at `r⁺`. -/
theorem stopDrv_toNNReal (w : ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) (r : ℝ) :
    A1Ref.stopDrv w T (r.toNNReal : ℝ) = A1Ref.stopDrv w T r := by
  rcases le_or_gt 0 r with hr | hr
  · rw [Real.coe_toNNReal r hr]
  · rw [Real.toNNReal_of_nonpos hr.le]
    simp only [A1Ref.stopDrv, NNReal.coe_zero, min_eq_left hT, max_self]
    rw [max_eq_left ((min_le_left _ _).trans hr.le)]

/-- Stopping at `S` and then at `τ ∈ [0, S]` is stopping at `τ`. -/
theorem stopDrv_stopDrv (w : ℝ → ℝ) {S τ : ℝ} (hτ : 0 ≤ τ) (hτS : τ ≤ S) :
    A1Ref.stopDrv (A1Ref.stopDrv w S) τ = A1Ref.stopDrv w τ := by
  funext u
  have h0 : 0 ≤ max 0 (min u τ) := le_max_left _ _
  have hS : max 0 (min u τ) ≤ S := max_le (hτ.trans hτS) ((min_le_right _ _).trans hτS)
  simp only [A1Ref.stopDrv]
  rw [min_eq_left hS, max_eq_right h0]

variable {X Y : Type*}

/-- The large driver stopped at the large exit of rectangle `m`, as a family over the product space. -/
def stopW₂ (W₂ : ℝ≥0 → Y → ℝ) (S₂ : ℕ → Y → ℝ≥0) (m : ℕ) (ω : X × Y) : ℝ → ℝ :=
  A1Ref.stopDrv (Strip.extPath (W₂ · ω.2)) (S₂ m ω.2)

/-- The frozen path of the record at a height below the large exit is the frozen driver of `stopW₂`. -/
theorem frzPath_eq_frzDrv {W₂ : ℝ≥0 → Y → ℝ} {S₂ : ℕ → Y → ℝ≥0} {m : ℕ} {p : ℝ} {τ : X × Y → ℝ} {ω : X × Y}
    (hτ0 : 0 ≤ τ ω) (hτS : τ ω ≤ S₂ m ω.2) :
    frzPath W₂ p (τ ω) ω.2 = frzDrv (stopW₂ W₂ S₂ m) p τ ω := by
  funext u
  simp only [frzPath, frzDrv, stopW₂, stopDrv_stopDrv _ hτ0 hτS]

end Stop

/-! ### The G3 records -/

section G3

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {𝓕₁ : Filtration ℝ≥0 mX}
  {𝓕₂ : Filtration ℝ≥0 mY} {P₁ : Measure X} {κ x y : ℝ} {W₁ : ℝ≥0 → X → ℝ} {VL₁ : Fin 1 → ℝ≥0 → X → ℝ}
  {VR₁ : Fin 3 → ℝ≥0 → X → ℝ} {B₁ : ℝ≥0 → X → ℝ} {ζ₁ : X → ℝ≥0∞} {W₂ : ℝ≥0 → Y → ℝ}
  {S₁ : ℕ → X → ℝ≥0} {S₂ : ℕ → Y → ℝ≥0} {H₁ H₂ : ℕ → Set ℂ} {δ q dd Tm : ℕ → ℝ}

/-- **The G3 seeded height field at a fixed own time and a measurable random height is measurable** on the event
`{s ≤ S₁ m}`. The hypotheses are those of A1-G3CALC's `seedFieldInputG_of_g3` (supplied by A1-COMMON's `g3_rect`) for
a regular small marginal, with the large driver progressive and the exits stopping times. -/
theorem measurable_g3Rec_height [Nonempty Y] (hyx : y < x) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hs₁ : ∀ m, IsStoppingTime 𝓕₁ fun ω => (S₁ m ω : WithTop ℝ≥0))
    (hW₂ : IsStronglyProgressive 𝓕₂ W₂) (hs₂ : ∀ m, IsStoppingTime 𝓕₂ fun ω => (S₂ m ω : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPairG (H₁ m) (H₂ m) (δ m) (-y) (q m) (dd m)) (hxOq : ∀ m, x - y ≤ q m)
    (hgood₁ : ∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (S₁ m ω : ℝ) ∧ (S₁ m ω : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m ω) (S₁ m ω) ⊆ H₁ m)
    (hsep₁ : ∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω)
    (hsepO : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 1 s ω ≠ W₁ s ω)
    (hneP : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 2 s ω ≠ W₁ s ω)
    (hc₂ : ∀ m ω, ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω))) (h0₂ : ∀ ω, W₂ 0 ω = 0)
    (hgood₂ : ∀ m ω, (S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-y) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m)
    (hS₂pos : ∀ m ω, 0 < (S₂ m ω : ℝ))
    (m : ℕ) {τ : X × Y → ℝ} (hτ : Measurable τ) (hτ0 : ∀ ω, 0 ≤ τ ω) (hτS : ∀ ω, τ ω ≤ S₂ m ω.2)
    {s : ℝ} (hs : 0 ≤ s) :
    Measurable ({ω : X × Y | s ≤ S₁ m ω.1}.indicator fun ω =>
      seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m) ω s (τ ω)) := by
  obtain ⟨y₀⟩ := ‹Nonempty Y›
  have hp0 : 0 < -y := by linarith
  have hlt : ∀ ω (u : ℝ≥0), u ≤ S₁ m ω → (u : ℝ≥0∞) < ζ₁ ω := fun ω u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) (hgood₁ m ω).1
  -- the drivers
  have hDc : ∀ ω : X × Y, Continuous (eightDrv W₁ S₁ m ω.1) := fun ω =>
    continuous_eightDrv (h₁.path ω.1).2.2.2.1 (hgood₁ m ω.1).1
  have hD0 : ∀ ω : X × Y, eightDrv W₁ S₁ m ω.1 0 = 0 := fun ω => eightDrv_zero (h₁.path ω.1).1
  have hDm : ∀ r, Measurable fun ω : X × Y => eightDrv W₁ S₁ m ω.1 r := by
    intro r
    have h : Measurable fun x' : X => A1Ref.stopDrv (Strip.extPath (W₁ · x')) (S₁ m x') (r.toNNReal : ℝ) :=
      (measurable_stopDrv_of_progressive h₁.progW (hs₁ m) r.toNNReal).mono (𝓕₁.le _) le_rfl
    have e : (fun ω : X × Y => eightDrv W₁ S₁ m ω.1 r) =
        (fun x' => A1Ref.stopDrv (Strip.extPath (W₁ · x')) (S₁ m x') (r.toNNReal : ℝ)) ∘ Prod.fst := by
      funext ω
      exact (eightDrv_toNNReal W₁ S₁ m ω.1 r).symm
    rw [e]
    exact h.comp measurable_fst
  have hFc : ∀ ω : X × Y, Continuous (stopW₂ W₂ S₂ m ω) := fun ω =>
    A1Ref.continuous_stopDrv (hc₂ m ω.2) (S₂ m ω.2).coe_nonneg
  have hFm : ∀ r, Measurable fun ω : X × Y => stopW₂ W₂ S₂ m ω r := by
    intro r
    have h : Measurable fun y' : Y => A1Ref.stopDrv (Strip.extPath (W₂ · y')) (S₂ m y') (r.toNNReal : ℝ) :=
      (measurable_stopDrv_of_progressive hW₂ (hs₂ m) r.toNNReal).mono (𝓕₂.le _) le_rfl
    have e : (fun ω : X × Y => stopW₂ W₂ S₂ m ω r) =
        (fun y' => A1Ref.stopDrv (Strip.extPath (W₂ · y')) (S₂ m y') (r.toNNReal : ℝ)) ∘ Prod.snd := by
      funext ω
      exact (stopDrv_toNNReal _ (S₂ m ω.2).coe_nonneg r).symm
    rw [e]
    exact h.comp measurable_snd
  have hF0 : ∀ ω : X × Y, stopW₂ W₂ S₂ m ω 0 = 0 := fun ω => by
    simp only [stopW₂, A1Ref.stopDrv_eqOn _ _ ⟨le_rfl, (S₂ m ω.2).coe_nonneg⟩, Strip.extPath,
      Real.toNNReal_zero, h0₂ ω.2]
  have hGm : MeasurableSet {ω : X × Y | s ≤ S₁ m ω.1} :=
    measurableSet_le measurable_const ((measurable_coe_of_isStoppingTime (hs₁ m)).comp measurable_fst)
  -- the frozen hull at the random height
  have hfz : ∀ ω, frzPath W₂ (-y) (τ ω) ω.2 = frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω := fun ω =>
    frzPath_eq_frzDrv (hτ0 ω) (hτS ω)
  have hK₂ : ∀ ω, fwdHull (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω) ⊆ H₂ m := fun ω => by
    rw [← hfz ω]
    exact fwdHull_frzPath_subset (hc₂ m ω.2) (hτ0 ω) (hτS ω) (hgood₂ m ω.2).2
  have hpair := (hpp m).pair
  have hex : ∀ ω ∈ {ω : X × Y | s ≤ S₁ m ω.1}, ∃ a W', OwnData (eightDrv W₁ S₁ m ω.1)
      (fwdHull (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω)) (frzChart (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω))
      (S₁ m ω.1) a W' := fun ω _ =>
    exists_ownData_of_encl (hDc ω) (hD0 ω) (hgood₁ m ω.1).2.1 (continuous_frzDrv hFc hτ0 ω) (hτ0 ω)
      hpair.sep_pos hpair.sep (hgood₁ m ω.1).2.2.2 (hK₂ ω)
  have hv : ∀ ω ∈ {ω : X × Y | s ≤ S₁ m ω.1}, ∀ a W', OwnData (eightDrv W₁ S₁ m ω.1)
      (fwdHull (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω)) (frzChart (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω))
      (S₁ m ω.1) a W' → ∃ v, IsForwardSol W' (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω (τ ω) : ℂ) (a (S₁ m ω.1)) v := by
    intro ω _ a W' h
    refine h.tip_alive_of_enclosures hpair.hull₁ hpair.hull₂ hpair.sep_pos hpair.sep
      (continuous_frzDrv hFc hτ0 ω) (hτ0 ω) ?_ ?_ (hgood₁ m ω.1).2.2.2 (hK₂ ω)
    · rw [hD0 ω, frzDrv_zero hτ0 hF0]
      exact hp0.ne
    · rw [frzDrv_zero hτ0 hF0]
      exact hpair.src
  -- the clearance of the marks
  obtain ⟨r, hr, hclear⟩ := exists_le_norm_fwdMap_sub_ext_interval_uniform hpair.hull₁ hpair.hull₂.2.1
    hpair.hull₂.1 hpair.sep_pos hpair.sep hpair.prot_pos (hpp m).seg
  have h2d : 0 < 2 * dd m := by have := hpair.rad_pos; positivity
  have hqH₁ : Disjoint (ball (q m : ℂ) (2 * dd m)) (H₁ m) := hpair.prot.mono_right subset_union_left
  have hcl : ∀ u ∈ Icc (0 : ℝ) s, ∀ ω ∈ {ω : X × Y | s ≤ S₁ m ω.1}, ∀ k, ∃ ρ > 0,
      Disjoint (ball (g3Marks VL₁ VR₁ ω.1 k u : ℂ) ρ)
        (imgHull (eightDrv W₁ S₁ m ω.1) (fwdHull (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω)) u) := by
    intro u hu ω hω k
    have huS : u ≤ S₁ m ω.1 := hu.2.trans hω
    have hrec := isSourceRecordG_g3Rec (κ := κ) (p := -y) (y := ω.2) (h₁.path ω.1) rfl rfl
      (show 0 < (![0, x - y, -y] : Fin 3 → ℝ) 1 by simp; linarith)
      (show (![0, x - y, -y] : Fin 3 → ℝ) 1 ≤ q m by simpa using hxOq m) (hgood₁ m ω.1).1 (hgood₁ m ω.1).2.1
      (fun u hu hus => (hsep₁ ω.1 u hu (hlt ω.1 u hus)).1) (fun u hu hus => (hsep₁ ω.1 u hu (hlt ω.1 u hus)).2)
      (fun u hus => hsepO ω.1 u (hlt ω.1 u hus)) h2d hqH₁ (hc₂ m ω.2) (h0₂ ω.2) (hS₂pos m ω.2)
      (hgood₂ m ω.2).1 (hgood₁ m ω.1).2.2.1 hpair.sep_pos hpair.sep (hgood₁ m ω.1).2.2.2 (hgood₂ m ω.2).2
    have hq0 : eightDrv W₁ S₁ m ω.1 0 < q m := by rw [hD0 ω]; exact hpair.prot_pos
    obtain ⟨uq, huq⟩ := exists_isForwardSol_of_disjoint_ball_gen (hDc ω) hq0.ne' (S₁ m ω.1).coe_nonneg h2d
      (hqH₁.mono_right (hgood₁ m ω.1).2.2.2)
    have huI : u ∈ Icc (0 : ℝ) (S₁ m ω.1) := ⟨hu.1, huS⟩
    have hmk := hrec.marks u huI k
    change g3Marks VL₁ VR₁ ω.1 k u ∈ uIcc (Strip.extPath (VL₁ 0 · ω.1) u)
      ((fwdMap (eightDrv W₁ S₁ m ω.1) u (q m)).re + eightDrv W₁ S₁ m ω.1 u) at hmk
    rw [InteractingSLE.fwdMap_eq_of_isForwardSol (hDc ω) huq huI] at hmk
    have hW0H : ((eightDrv W₁ S₁ m ω.1 0 : ℝ) : ℂ) ∈ closure (H₁ m) :=
      closure_mono (hgood₁ m ω.1).2.2.2 (start_mem_closure_fwdHull (hDc ω) (hgood₁ m ω.1).2.1)
    refine ⟨r, hr, Set.disjoint_left.2 ?_⟩
    rintro z hz ⟨w, hw, rfl⟩
    have hb := hclear (eightDrv W₁ S₁ m ω.1) _ _ (S₁ m ω.1) (hDc ω) (hD0 ω) hW0H (hgood₁ m ω.1).2.2.2 hrec.lo
      hrec.hi uq huq u huI w (hK₂ ω hw) _ hmk
    rw [mem_ball, dist_eq_norm] at hz
    exact not_lt_of_ge hb hz
  -- the measurable own-side inputs
  have hsub : ∀ u ∈ Icc (0 : ℝ) s, ∀ ω ∈ {ω : X × Y | s ≤ S₁ m ω.1}, ω.1 ∈ {x' : X | u.toNNReal ≤ S₁ m x'} :=
    fun u hu ω hω => Real.toNNReal_le_iff_le_coe.2 (hu.2.trans hω)
  have hneP' : ∀ ω (u : ℝ≥0), u ≤ S₁ m ω → VR₁ 2 u ω ≠ W₁ u ω := fun ω u hu => hneP ω u (hlt ω u hu)
  have hZ : ∀ u ∈ Icc (0 : ℝ) s, ∀ k,
      Measurable ({ω : X × Y | s ≤ S₁ m ω.1}.indicator fun ω => g3Marks VL₁ VR₁ ω.1 k u) := by
    intro u hu k
    have h := measurable_mask_prod_fst (((measurable_mask_g3Rec_V (κ := κ) (y := y) (W₁ := W₁) (W₂ := W₂) (t₂ := 0)
      (y₀ := y₀) h₁.progVL h₁.progVR (hs₁ m) u.toNNReal k).mono (𝓕₁.le _) le_rfl)) hGm (hsub u hu)
    rw [Real.coe_toNNReal _ hu.1] at h
    exact h
  have hV₀ : ∀ u ∈ Icc (0 : ℝ) s, Measurable ({ω : X × Y | s ≤ S₁ m ω.1}.indicator fun ω =>
      (fwdMap (eightDrv W₁ S₁ m ω.1) u (-y : ℝ)).re + eightDrv W₁ S₁ m ω.1 u) := by
    intro u hu
    have h := measurable_mask_prod_fst (((measurable_mask_g3Rec_V₀ (W₂ := W₂) (t₂ := 0) (y₀ := y₀) h₁.path
      h₁.progVR (hs₁ m) (fun ω => (hgood₁ m ω).1) hneP' u.toNNReal).mono (𝓕₁.le _) le_rfl)) hGm (hsub u hu)
    rw [Real.coe_toNNReal _ hu.1] at h
    exact h
  have hG₀ : ∀ u ∈ Icc (0 : ℝ) s, Measurable ({ω : X × Y | s ≤ S₁ m ω.1}.indicator fun ω =>
      (deriv (fwdMap (eightDrv W₁ S₁ m ω.1) u) (-y : ℝ)).re) := by
    intro u hu
    have h := measurable_mask_prod_fst (((measurable_mask_g3Rec_G₀ (W₂ := W₂) (t₂ := 0) (y₀ := y₀) h₁.path
      h₁.progW h₁.progVR (hs₁ m) (fun ω => (hgood₁ m ω).1) hneP' u.toNNReal).mono (𝓕₁.le _) le_rfl)) hGm
      (hsub u hu)
    rw [Real.coe_toNNReal _ hu.1] at h
    exact h
  have hm : ∀ u ∈ Icc (0 : ℝ) s, Measurable ({ω : X × Y | s ≤ S₁ m ω.1}.indicator fun ω =>
      (srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω) (kh κ) (g3RR κ) (-y)
        (g3Marks VL₁ VR₁ ω.1)).normEll u) := fun u hu =>
    measurable_srcRec_normEll_rand (D := fun ω : X × Y => eightDrv W₁ S₁ m ω.1) hDc hDm hFc hFm hF0 hτ hτ0
      (kh κ) (g3RR κ) (T := fun ω : X × Y => (S₁ m ω.1 : ℝ)) (Z := fun ω : X × Y => g3Marks VL₁ VR₁ ω.1) hGm hu.1
      hex (fun ω hω => hu.2.trans hω) hv (hcl u hu) (hZ u hu) (hV₀ u hu) (hG₀ u hu)
  have e : ∀ ω, seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m) ω s (τ ω) =
      Real.exp ((srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω) (kh κ)
        (g3RR κ) (-y) (g3Marks VL₁ VR₁ ω.1)).normEll s -
        (srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1) (frzDrv (stopW₂ W₂ S₂ m) (-y) τ ω) (τ ω) (kh κ) (g3RR κ) (-y)
          (g3Marks VL₁ VR₁ ω.1)).normEll 0) := by
    intro ω
    simp only [seedHeightField]
    rw [show g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m (τ ω) ω = srcRec (eightDrv W₁ S₁ m ω.1) (S₁ m ω.1)
      (frzPath W₂ (-y) (τ ω) ω.2) (τ ω) (kh κ) (g3RR κ) (-y) (g3Marks VL₁ VR₁ ω.1) from rfl, hfz ω]
  simp_rw [e]
  convert (Real.measurable_exp.comp ((hm s ⟨hs, le_rfl⟩).sub (hm 0 ⟨le_rfl, hs⟩))).indicator hGm using 1
  funext ω
  by_cases hω : ω ∈ {ω : X × Y | s ≤ S₁ m ω.1}
  · simp only [indicator_of_mem hω, Function.comp_apply, Pi.sub_apply]
  · simp only [indicator_of_notMem hω]

omit mY in
/-- **The G3 columns are continuous** on `[0, S₁ m]` at every frozen height `t ∈ [0, S₂ m]`: A1-G3CALC's column calculus
(`IsSourceColumnG.calculus`) at positive heights, the identity chart (`normEll_g3Rec_zero`) at height zero. -/
theorem continuousOn_g3Rec_column [IsProbabilityMeasure P₁] (hk : 0 < kh κ) (hyx : y < x)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω)) (hs₁ : ∀ m, IsStoppingTime 𝓕₁ fun ω => (S₁ m ω : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPairG (H₁ m) (H₂ m) (δ m) (-y) (q m) (dd m)) (hxOq : ∀ m, x - y ≤ q m)
    (hgood₁ : ∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (S₁ m ω : ℝ) ∧ (S₁ m ω : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m ω) (S₁ m ω) ⊆ H₁ m)
    (hsep₁ : ∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω)
    (hsepO : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 1 s ω ≠ W₁ s ω)
    (hneP : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 2 s ω ≠ W₁ s ω)
    (hc₂ : ∀ m ω, ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω))) (h0₂ : ∀ ω, W₂ 0 ω = 0)
    (hgood₂ : ∀ m ω, (S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-y) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m)
    (m : ℕ) (ω : X × Y) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (S₂ m ω.2)) :
    ContinuousOn (fun s => seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m) ω s t) (Icc (0 : ℝ) (S₁ m ω.1)) := by
  obtain ⟨ω₁, ω₂⟩ := ω
  have hlt : ∀ ω (u : ℝ≥0), u ≤ S₁ m ω → (u : ℝ≥0∞) < ζ₁ ω := fun ω u hu =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) (hgood₁ m ω).1
  have hpair := (hpp m).pair
  have hc₂t : ContinuousOn (Strip.extPath (W₂ · ω₂)) (Icc 0 t) := (hc₂ m ω₂).mono (Icc_subset_Icc_right ht.2)
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    have hK₂ : fwdHull (frzPath W₂ (-y) 0 ω₂) 0 ⊆ H₂ m :=
      fwdHull_frzPath_subset (hc₂ m ω₂) le_rfl (S₂ m ω₂).coe_nonneg (hgood₂ m ω₂).2
    have hex := exists_ownData_of_encl (continuous_eightDrv (h₁.path ω₁).2.2.2.1 (hgood₁ m ω₁).1)
      (eightDrv_zero (h₁.path ω₁).1) (hgood₁ m ω₁).2.1 (continuous_frzPath hc₂t le_rfl) le_rfl hpair.sep_pos
      hpair.sep (hgood₁ m ω₁).2.2.2 hK₂
    refine (continuousOn_const : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc (0 : ℝ) (S₁ m ω₁))).congr fun s hs => ?_
    have he := normEll_g3Rec_zero (κ := κ) (VL₁ := VL₁) (VR₁ := VR₁) hc₂t (h0₂ ω₂) hex hs.1 hs.2
    simp only [seedHeightField, he, sub_self, Real.exp_zero]
  have h2d : 0 < 2 * dd m := by have := hpair.rad_pos; positivity
  have hqH₁ : Disjoint (ball (q m : ℂ) (2 * dd m)) (H₁ m) := hpair.prot.mono_right subset_union_left
  have hrec : ∀ x', IsSourceRecordG (H₁ m) (H₂ m) (-y) (q m) (Tm m) (kh κ) (g3RR κ) (frzPath W₂ (-y) t ω₂) t
      (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m t (x', ω₂)) (Strip.extPath (VL₁ 0 · x')) (Strip.extPath (VR₁ 0 · x'))
      (S₁ m x') := fun x' =>
    isSourceRecordG_g3Rec (h₁.path x') rfl rfl (show 0 < (![0, x - y, -y] : Fin 3 → ℝ) 1 by simp; linarith)
      (show (![0, x - y, -y] : Fin 3 → ℝ) 1 ≤ q m by simpa using hxOq m) (hgood₁ m x').1 (hgood₁ m x').2.1
      (fun u hu hus => (hsep₁ x' u hu (hlt x' u hus)).1) (fun u hu hus => (hsep₁ x' u hu (hlt x' u hus)).2)
      (fun u hus => hsepO x' u (hlt x' u hus)) h2d hqH₁ hc₂t (h0₂ ω₂) hpos (ht.2.trans (hgood₂ m ω₂).1)
      (hgood₁ m x').2.2.1 hpair.sep_pos hpair.sep (hgood₁ m x').2.2.2
      (fwdHull_frzPath_subset (hc₂ m ω₂) hpos.le ht.2 (hgood₂ m ω₂).2)
  have hst := isColumnStoch_g3Rec_of_reg (W₂ := W₂) (t₂ := t) (y₀ := ω₂) hk h₁ hB₁ (hs₁ m)
    (fun ω => (hgood₁ m ω).1) (fun ω s hs hsS => (hsep₁ ω s hs (hlt ω s hsS)).1) (fun ω j s hs hsS => by
      fin_cases j
      · exact (hsep₁ ω s hs (hlt ω s hsS)).2
      · exact hsepO ω s (hlt ω s hsS)
      · exact hneP ω s (hlt ω s hsS))
    (fun ω s hsS => hneP ω s (hlt ω s hsS))
  have hcol := isSourceColumnG_of_stoch hrec (hs₁ m) hst
  have hc := (IsSourceColumnG.calculus (hpp m) hk hcol).2 ω₁
  apply continuousOn_of_continuous_stopped
  exact hc

/-- **The G3 seeded height field of every rectangle is measurable on the rectangle** (`A1Patch.IsFieldMeas`), from the
pathwise rectangle data of A1-COMMON's `g3_rect`, a regular small marginal, a progressive large driver and stopping-time
exits. -/
theorem isFieldMeas_g3Rec [IsProbabilityMeasure P₁] [Nonempty Y] (hk : 0 < kh κ) (hyx : y < x) (hx : x < 0)
    (h₁ : IsRegMarginal (kh κ) ![0] ![0, x - y, -y] (smallG3RhoL κ) (smallG3RhoR κ) P₁ 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁)
    (hB₁ : ∀ ω, Continuous (B₁ · ω)) (hs₁ : ∀ m, IsStoppingTime 𝓕₁ fun ω => (S₁ m ω : WithTop ℝ≥0))
    (hW₂ : IsStronglyProgressive 𝓕₂ W₂) (hs₂ : ∀ m, IsStoppingTime 𝓕₂ fun ω => (S₂ m ω : WithTop ℝ≥0))
    (hpp : ∀ m, IsProtectedPairG (H₁ m) (H₂ m) (δ m) (-y) (q m) (dd m)) (hxOq : ∀ m, x - y ≤ q m)
    (hgood₁ : ∀ m ω, (S₁ m ω : ℝ≥0∞) < ζ₁ ω ∧ 0 < (S₁ m ω : ℝ) ∧ (S₁ m ω : ℝ) ≤ Tm m ∧
      fwdHull (eightDrv W₁ S₁ m ω) (S₁ m ω) ⊆ H₁ m)
    (hsep₁ : ∀ ω (s : ℝ≥0), 0 < s → (s : ℝ≥0∞) < ζ₁ ω → VL₁ 0 s ω ≠ W₁ s ω ∧ VR₁ 0 s ω ≠ W₁ s ω)
    (hsepO : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 1 s ω ≠ W₁ s ω)
    (hneP : ∀ ω (s : ℝ≥0), (s : ℝ≥0∞) < ζ₁ ω → VR₁ 2 s ω ≠ W₁ s ω)
    (hc₂ : ∀ m ω, ContinuousOn (Strip.extPath (W₂ · ω)) (Icc 0 (S₂ m ω))) (h0₂ : ∀ ω, W₂ 0 ω = 0)
    (hgood₂ : ∀ m ω, (S₂ m ω : ℝ) ≤ Tm m ∧ fwdHull (frzPath W₂ (-y) (S₂ m ω) ω) (S₂ m ω) ⊆ H₂ m)
    (hS₂pos : ∀ m ω, 0 < (S₂ m ω : ℝ)) (m : ℕ) :
    IsFieldMeas (seedHeightField (g3Rec κ (-y) W₁ VL₁ VR₁ W₂ S₁ m)) (fun _ : Unit => S₁ m)
      (fun _ : Unit => S₂ m) :=
  isFieldMeas_of_height
    (fun _ hτ hτ0 hτS _ hs => measurable_g3Rec_height hyx hx h₁ hs₁ hW₂ hs₂ hpp hxOq hgood₁ hsep₁ hsepO hneP hc₂
      h0₂ hgood₂ hS₂pos m hτ hτ0 hτS hs)
    (fun ω _ ht => continuousOn_g3Rec_column hk hyx h₁ hB₁ hs₁ hpp hxOq hgood₁ hsep₁ hsepO hneP hc₂ h0₂ hgood₂
      m ω ht)

end G3

/-! ### The named input -/

/-- **`A1Asm.G3RectMeas κ` holds for every `κ`**: for regular G3 marginals in right-continuous filtrations with
continuous Brownian paths at every sample and a `GoodSmallG3` small curve at every sample, the seeded height field of
every cofinal rectangle `g3S₁ m`, `g3S₂ m` is measurable on the rectangle. -/
theorem g3RectMeas (κ : ℝ) : G3RectMeas κ := by
  intro hκ4 hκ8 y x hyx hx X Y mX mY _ _ P₁ hP₁ P₂ hP₂ 𝓖₁ 𝓖₂ hrc₁ hrc₂ W₂ VL₂ VR₂ B₂ ζ₂ W₁ VL₁ VR₁ B₁ ζ₁ h₂ hB₂
    h₁ hB₁ hg₁ m
  have := hrc₁
  have := hrc₂
  have : Nonempty Y := nonempty_of_isProbabilityMeasure P₂
  have hqlo : 0 < x - y := by linarith
  have hqlox : x - y < -y := by linarith
  have hne : (goodIdxG (-y) (x - y) ![x - y]).Nonempty :=
    goodIdxG_nonempty hqlo hqlox (fun m => by fin_cases m; simp; linarith) (fun m => by fin_cases m; simp; linarith)
  have hF := isEnclFamily_cofG hne
  obtain ⟨-, hgood₁, hsep₁, hsepO, hneP, hc₂, h0₂, hgood₂, hS₂pos, -⟩ :=
    g3_rect hκ4 hκ8 hyx hx h₁.path hg₁ hB₁ h₂.path hB₂ hF
  have hs₁ : ∀ m, IsStoppingTime 𝓖₁ fun ω => (g3S₁ x y W₁ ζ₁ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₁ (fun ω => (h₁.path ω).2.2.2.1) h₁.evol.2.1 (fun m => (hF.pp m).hull₁)
      (cofGN (-y) (x - y) ![x - y]) m
  have hs₂ : ∀ m, IsStoppingTime 𝓖₂ fun ω => (g3S₂ x y W₂ ζ₂ m ω : WithTop ℝ≥0) := fun m =>
    isStoppingTime_rect₂ (fun ω => (h₂.path ω).2.2.2.1) h₂.evol.2.1 (fun m => (hF.pp m).hull₂)
      (cofGN (-y) (x - y) ![x - y]) (-y) m
  have hk : 0 < kh κ := by unfold kh; exact div_pos (by norm_num) (by linarith)
  exact isFieldMeas_g3Rec (H₁ := cofGH₁ (-y) (x - y) ![x - y]) (H₂ := cofGH₂ (-y) (x - y) ![x - y])
    (δ := cofGδ (-y) (x - y) ![x - y]) (q := cofGq (-y) (x - y) ![x - y]) (dd := cofGd (-y) (x - y) ![x - y])
    (Tm := cofGTm (-y) (x - y) ![x - y]) hk hyx hx h₁ hB₁ hs₁ h₂.progW hs₂ (isProtectedPairG_cofG hne)
    (fun m => by simpa using qlo_le_cofGq hne m) hgood₁ hsep₁ hsepO hneP hc₂ h0₂ hgood₂ hS₂pos m

/-- **A.1 (G3), rectangle-wise seeded form, from the rows and the law input alone**: A1-ASSEMBLE's
`a1DualCouplingG3SeedGStatement_of_rect` with its measurability input discharged by `g3RectMeas`. -/
theorem a1DualCouplingG3SeedGStatement_of_rowLaw {κ : ℝ} (hR : G3RectRow κ) (hL : G3RectLaw κ) :
    A1G3Calc.A1DualCouplingG3SeedGStatement κ :=
  a1DualCouplingG3SeedGStatement_of_rect hR (g3RectMeas κ) hL

end InteractingSLE.ZhanGT4.A1RectMeas

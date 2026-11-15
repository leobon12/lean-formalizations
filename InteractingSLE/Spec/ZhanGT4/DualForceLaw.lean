/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualForceLawD9
import InteractingSLE.Spec.ZhanGT4.DualFubiniOuter
import InteractingSLE.Spec.ZhanGT4.DualLaw

/-!
# The marginals of the stopped dual coupling are the force-point laws

Packet PROVE-ZHAN-GT4-A17. Source: Astra, *Follow-up proofs*, §A.1.3–A.1.4 (`source/external/AstraIG1/
ig1_followup_proofs.txt` L341–L343, L401–L406, R38): "The positive density `M(S₁, S₂)`, with respect to the product of
the two marginal laws, has expectation one … Its marginals are unchanged."

A16's `DualHyp.map_fst_dualCoupling` identifies the curve-`1` marginal of `dualCoupling` with `m₁ · P₁`,
`m₁ = Ñ_s(max S₁, 0)/Ñ_s(0, 0)` (`margDens₁`). Here `m₁ · P₁` is identified with **the force-point law stopped at the
last exit time** `max_i S₁ i`: under `m₁ · P₁`, the curve `√κ B₁` stopped at `max_i S₁ i` and continued by the
maximal solution is an integrated `SLE_κ(ρ)` evolution of the word "the other source `x₂` with weight `−κ/2`, the
marks `p_m` with weights `κ r_m`", and its killed laws are those of every such evolution (Theorem 2.2's uniqueness).

Route: at frozen height `0` the frozen hull is empty, the chart is the identity (`frzChart_zero_eq_id`) and the image
chain is the curve itself (`OwnData.clock_eq_of_empty`, `OwnData.W'_eq_of_empty`); the (D9) constants hold at height
`0` (`exists_twoCurveD9_family`), so A12's frozen-hull identification `FrzD10Hyp.exists_isIntegratedSLEEvolution_img_law`
applies with `Q = girsMeasure … = m₁ · P₁` (`girsMeasure_marg₁_eq`).

## Main results

* `lastExit`, `isStoppingTime_lastExit`, `coe_lastExit`;
* `DualHyp.frzD10Hyp_marg₁`: the frozen-hull hypotheses of A12 at height `0`;
* `DualHyp.girsMeasure_marg₁_eq`: A12's tilted measure is `m₁ · P₁`;
* **`DualHyp.exists_forceLaw₁`**: the curve-`1` marginal `m₁ · P₁` is the force-point law up to `max S₁`.
-/

set_option autoImplicit false

noncomputable section

open Finset Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull drive)

/-! ### The last exit time -/

section LastExit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]

/-- **The last exit time** `max_i S i` (`0` for an empty family). -/
def lastExit (S : ι → Ω → ℝ≥0) (ω : Ω) : ℝ≥0 := (maxIn (stairCols fun i => (S i ω : ℝ))).toNNReal

theorem coe_lastExit (S : ι → Ω → ℝ≥0) (ω : Ω) :
    (lastExit S ω : ℝ) = maxIn (stairCols fun i => (S i ω : ℝ)) :=
  Real.coe_toNNReal _ (maxIn_nonneg _)

theorem le_lastExit (S : ι → Ω → ℝ≥0) (ω : Ω) (i : ι) : S i ω ≤ lastExit S ω := by
  rw [← NNReal.coe_le_coe, coe_lastExit]
  exact le_maxIn (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem lastExit_le_iff (S : ι → Ω → ℝ≥0) (ω : Ω) (t : ℝ≥0) : lastExit S ω ≤ t ↔ ∀ i, S i ω ≤ t := by
  refine ⟨fun h i => (le_lastExit S ω i).trans h, fun h => ?_⟩
  rw [← NNReal.coe_le_coe, coe_lastExit]
  refine max'_le _ _ _ fun x hx => ?_
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact t.coe_nonneg
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact NNReal.coe_le_coe.2 (h i)

/-- The last exit time is attained (nonempty family). -/
theorem exists_lastExit_eq [Nonempty ι] (S : ι → Ω → ℝ≥0) (ω : Ω) : ∃ j, lastExit S ω = S j ω := by
  have hmem := Finset.max'_mem (insert 0 (stairCols fun i => (S i ω : ℝ))) (Finset.insert_nonempty _ _)
  rcases Finset.mem_insert.1 hmem with h0 | hC
  · obtain ⟨j⟩ := ‹Nonempty ι›
    refine ⟨j, le_antisymm ?_ (le_lastExit S ω j)⟩
    rw [← NNReal.coe_le_coe, coe_lastExit]
    exact h0.le.trans (S j ω).coe_nonneg
  · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hC
    refine ⟨j, ?_⟩
    rw [← NNReal.coe_inj, coe_lastExit]
    exact hj.symm

/-- **The last exit time of stopping times is a stopping time.** -/
theorem isStoppingTime_lastExit {𝓕 : Filtration ℝ≥0 mΩ} {S : ι → Ω → ℝ≥0}
    (hS : ∀ i, IsStoppingTime 𝓕 fun ω => (S i ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => (lastExit S ω : WithTop ℝ≥0) := by
  intro t
  have e : {ω | (lastExit S ω : WithTop ℝ≥0) ≤ t} = ⋂ i, {ω | (S i ω : WithTop ℝ≥0) ≤ t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, WithTop.coe_le_coe, lastExit_le_iff]
  rw [e]
  exact MeasurableSet.iInter fun i => hS i t

end LastExit

/-! ### The height-`0` selection of curve `1` -/

section Marg0

variable {Ω₁ : Type*} {ι : Type*} [Fintype ι]

/-- The canonical height-`0` capacity clock of curve `1` (the `s`-view selection of `margDens₁`). -/
def marg0A (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (ω : Ω₁) : ℝ → ℝ :=
  sSelA (drive κ B₁ ω) (fun _ => x₂) (fun i => (S₁ i ω : ℝ)) (fun _ => 0) 0

/-- The canonical height-`0` image driver of curve `1`. -/
def marg0W (κ : ℝ) (B₁ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (S₁ : ι → Ω₁ → ℝ≥0) (ω : Ω₁) : ℝ → ℝ :=
  sSelW (drive κ B₁ ω) (fun _ => x₂) (fun i => (S₁ i ω : ℝ)) (fun _ => 0) 0

/-- The width of the height-`0` selection, `stairH 0 S₁ 0`. -/
def marg0T (S₁ : ι → Ω₁ → ℝ≥0) (ω : Ω₁) : ℝ := stairH (fun _ : ι => (0 : ℝ)) (fun i => (S₁ i ω : ℝ)) 0

theorem marg0T_eq (S₁ : ι → Ω₁ → ℝ≥0) (ω : Ω₁) : marg0T S₁ ω = lastExit S₁ ω := by
  rw [marg0T, stairH_zero_eq_maxIn (fun _ => le_rfl), coe_lastExit]

/-- The canonical height-`0` capacity clock of curve `2` (translated by `−x₂`; the `t`-view selection of `margDens₂`,
`DualHyp.girsMeasure_marg0₂_eq`). -/
def marg0A₂ (κ : ℝ) (B₂ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (S₂ : ι → Ω₁ → ℝ≥0) (ω : Ω₁) : ℝ → ℝ :=
  (imgSelD (drive (16 / κ) B₂ ω) (fun _ => -x₂) (marg0T S₂ ω) 0).1

/-- The canonical height-`0` image driver of curve `2` (translated by `−x₂`). -/
def marg0W₂ (κ : ℝ) (B₂ : ℝ≥0 → Ω₁ → ℝ) (x₂ : ℝ) (S₂ : ι → Ω₁ → ℝ≥0) (ω : Ω₁) : ℝ → ℝ :=
  (imgSelD (drive (16 / κ) B₂ ω) (fun _ => -x₂) (marg0T S₂ ω) 0).2

end Marg0

section ForceLaw

variable {Ω₁ Ω₂ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {mΩ₂ : MeasurableSpace Ω₂} {ι : Type*} [Fintype ι] {n : ℕ}
  {κ : ℝ} {P₁ : Measure Ω₁} {𝓕₁ : Filtration ℝ≥0 mΩ₁} {B₁ : ℝ≥0 → Ω₁ → ℝ} {P₂ : Measure Ω₂}
  {𝓕₂ : Filtration ℝ≥0 mΩ₂} {B₂ : ℝ≥0 → Ω₂ → ℝ} {x₂ : ℝ} {H₁ H₂ : ι → Set ℂ} {δ q d : ι → ℝ} {p : Fin n → ℝ}
  {Tm : ℝ} {S₁ : ι → Ω₁ → ℝ≥0} {S₂ : ι → Ω₂ → ℝ≥0}

namespace DualHyp

variable (h : DualHyp κ P₁ 𝓕₁ B₁ P₂ 𝓕₂ B₂ x₂ H₁ H₂ δ q d p Tm S₁ S₂)
include h

theorem lastExit_pos [Nonempty ι] (ω : Ω₁) : 0 < lastExit S₁ ω := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  exact (h.pos₁ j ω).trans_le (le_lastExit S₁ ω j)

theorem coe_lastExit_le (ω : Ω₁) : (lastExit S₁ ω : ℝ) ≤ Tm := by
  rw [coe_lastExit]; exact maxIn_stairCols_le h.Tmpos.le fun i => h.le₁ i ω

/-- **The height-`0` image data of curve `1`** (empty frozen hull, identity chart) up to the last exit time. -/
theorem ownData_marg0 [Nonempty ι] (ω : Ω₁) :
    OwnData (drive κ B₁ ω) (fwdHull (fun _ => x₂) 0) (frzChart (fun _ => x₂) 0) (marg0T S₁ ω)
      (marg0A κ B₁ x₂ S₁ ω) (marg0W κ B₁ x₂ S₁ ω) := by
  have hW : Continuous (drive κ B₁ ω) := QuantumZipper.drive_continuous (h.cont₁ ω)
  have hW0 : drive κ B₁ ω 0 = 0 := QuantumZipper.drive_zero (h.zero₁ ω)
  have hV : Continuous (fun _ : ℝ => x₂) := continuous_const
  have hT : 0 < marg0T S₁ ω := by rw [marg0T_eq]; exact NNReal.coe_pos.2 (h.lastExit_pos ω)
  refine imgSelD_spec (exists_ownData hW hW0 hT (isHPHull_fwdHull hV le_rfl) (isMapOut_fwdMap_gen hV le_rfl) ?_)
  rw [QuantumZipper.RS.fwdHull_zero_eq_empty hV, closure_empty]
  exact Set.empty_disjoint _

/-- **The frozen-hull hypotheses of A12 at height `0`** for curve `1` stopped at its last exit time. -/
theorem exists_frzD10Hyp_marg0 [Nonempty ι] (rr : Fin n → ℝ) : ∃ r a₀ γ Γ lam L : ℝ,
    FrzD10Hyp κ B₁ (marg0W κ B₁ x₂ S₁) (marg0A κ B₁ x₂ S₁) (fwdHull (fun _ => x₂) 0) (frzChart (fun _ => x₂) 0) rr
      x₂ (frzMarks (fun _ => x₂) p 0) (lastExit S₁) (marg0T S₁) r a₀ γ Γ lam L Tm := by
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha, hg, hmain⟩ := exists_twoCurveD9_family h.hull₁ h.hull₂ h.δpos h.sep h.dpos
    h.qpos h.qH h.pH h.pinj Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha hg Γ lam Tm
  have hTj : ∀ ω, ∃ j, marg0T S₁ ω = S₁ j ω := fun ω => by
    obtain ⟨j, hj⟩ := exists_lastExit_eq S₁ ω
    exact ⟨j, by rw [marg0T_eq, hj]⟩
  have hD : ∀ ω, TwoCurveD9 (frzDataOf κ B₁ (marg0W κ B₁ x₂ S₁) (marg0A κ B₁ x₂ S₁) (frzChart (fun _ => x₂) 0) rr
      x₂ (frzMarks (fun _ => x₂) p 0) ω) (fwdHull (fun _ => x₂) 0) (marg0T S₁ ω) r a₀ γ Γ lam := fun ω => by
    obtain ⟨j, hj⟩ := hTj ω
    refine hmain j (drive κ B₁ ω) (fun _ => x₂) 0 (marg0T S₁ ω) (marg0A κ B₁ x₂ S₁ ω) (marg0W κ B₁ x₂ S₁ ω) κ rr
      (h.ownData_marg0 ω) continuous_const (h.x₂H j) (h.qx j) le_rfl h.Tmpos.le (by rw [hj]; exact h.le₁ j ω)
      (by rw [hj]; exact h.K₁ j ω) ?_
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const]
    exact Set.empty_subset _
  obtain ⟨ω₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  refine ⟨r, a₀, γ, Γ, lam, L, ⟨⟨fun ω => h.ownData_marg0 ω, fun ω => (marg0T_eq S₁ ω).ge, fun ω => ?_,
    fun ω => (hD ω).alive₀, fun ω m => (hD ω).alive m, (hD ω₀).ne, (hD ω₀).inj, fun ω => (hD ω).d9, hL⟩,
    fun ω t ht => (hD ω).drv t ht⟩⟩
  rw [marg0T_eq]; exact h.coe_lastExit_le ω

/-- **A12's tilted measure at height `0` is `m₁ · P₁`.** -/
theorem girsMeasure_marg0_eq (rr : Fin n → ℝ) :
    girsMeasure P₁ (Real.sqrt κ) B₁ (lastExit S₁) (fun ω => (frzDataOf κ B₁ (marg0W κ B₁ x₂ S₁) (marg0A κ B₁ x₂ S₁)
      (frzChart (fun _ => x₂) 0) rr x₂ (frzMarks (fun _ => x₂) p 0) ω).ell) =
      P₁.withDensity fun ω => ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω) := by
  unfold girsMeasure
  congr 1
  funext ω
  have hx : min (maxIn (stairCols fun i => (S₁ i ω : ℝ))) Tm = (lastExit S₁ ω : ℝ) := by
    rw [coe_lastExit]; exact min_eq_left (maxIn_stairCols_le h.Tmpos.le fun i => h.le₁ i ω)
  have hd : ∀ s : ℝ≥0, drive κ B₁ ω (s : ℝ) = Real.sqrt κ * B₁ s ω := fun s => by
    simp only [drive, Real.toNNReal_coe]
  unfold girsDensity margDens₁ sEll
  rw [hx, hd, ← NNReal.coe_zero, hd]
  rfl

/-- At height `0` the image data of curve `1` have the empty frozen hull and the identity chart. -/
theorem ownData_marg0_empty [Nonempty ι] (ω : Ω₁) :
    OwnData (drive κ B₁ ω) ∅ id (marg0T S₁ ω) (marg0A κ B₁ x₂ S₁ ω) (marg0W κ B₁ x₂ S₁ ω) := by
  have h1 := h.ownData_marg0 ω
  rwa [QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const, frzChart_zero_eq_id] at h1

/-- **The curve-`1` marginal of the stopped dual coupling is the force-point law up to the last exit time**
(§A.1.3, "its marginals are unchanged"). Under `m₁ · P₁` (`margDens₁`, A16's `map_fst_dualCoupling`) there is an
integrated `SLE_κ(ρ)` evolution `(gW, gL, gR, B̂, ζG)` of the word "`x₂` with weight `−κ/2`, `p_m` with weight
`κ r_m`" (sorted by `e` around the start `0`), on the same space, living at least until `max_i S₁ i` and equal before
`max_i S₁ i` to the curve `√κ B₁` and the Loewner flow of the marks; its killed finite-dimensional laws are those of
**every** integrated evolution of that word (Theorem 2.2's uniqueness). -/
theorem exists_forceLaw₁ [Nonempty ι] (rr : Fin n → ℝ) :
    ∃ (nL nR : ℕ) (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)),
      (∀ i, markPos x₂ p (e (Sum.inl i)) < 0) ∧ (∀ i, 0 < markPos x₂ p (e (Sum.inr i))) ∧
      Antitone (fun i => markPos x₂ p (e (Sum.inl i))) ∧ Monotone (fun i => markPos x₂ p (e (Sum.inr i))) ∧
      ∃ (𝓗 : Filtration ℝ≥0 mΩ₁) (Bh gW : ℝ≥0 → Ω₁ → ℝ) (gL : Fin nL → ℝ≥0 → Ω₁ → ℝ)
        (gR : Fin nR → ℝ≥0 → Ω₁ → ℝ) (ζG : Ω₁ → ℝ≥0∞),
        IsIntegratedSLEEvolution κ (fun i => markPos x₂ p (e (Sum.inl i))) (fun i => markPos x₂ p (e (Sum.inr i)))
          (fun i => markWt κ rr (e (Sum.inl i))) (fun i => markWt κ rr (e (Sum.inr i)))
          (P₁.withDensity fun ω => ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω)) 𝓗 gW gL gR Bh ζG ∧
        (∀ ω, ENNReal.ofReal (lastExit S₁ ω) ≤ ζG ω ∧ ∀ t : ℝ≥0, t < lastExit S₁ ω →
          gW t ω = drive κ B₁ ω t ∧ (∀ i, gL i t ω = imgV (drive κ B₁ ω) (markPos x₂ p (e (Sum.inl i))) t) ∧
          ∀ j, gR j t ω = imgV (drive κ B₁ ω) (markPos x₂ p (e (Sum.inr j))) t) ∧
        ∀ {Ω₃ : Type*} {m₃ : MeasurableSpace Ω₃} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₃]
          {𝓕₃ : Filtration ℝ≥0 m₃} {W₃ : ℝ≥0 → Ω₃ → ℝ} {VL₃ : Fin nL → ℝ≥0 → Ω₃ → ℝ}
          {VR₃ : Fin nR → ℝ≥0 → Ω₃ → ℝ} {B₃ : ℝ≥0 → Ω₃ → ℝ} {ζ₃ : Ω₃ → ℝ≥0∞},
          IsIntegratedSLEEvolution κ (fun i => markPos x₂ p (e (Sum.inl i)))
            (fun i => markPos x₂ p (e (Sum.inr i))) (fun i => markWt κ rr (e (Sum.inl i)))
            (fun i => markWt κ rr (e (Sum.inr i))) P₃ 𝓕₃ W₃ VL₃ VR₃ B₃ ζ₃ →
          ∀ (m : ℕ) (ts : Fin m → ℝ≥0) (Asets : Fin m → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (Asets j)) →
            (P₁.withDensity fun ω => ENNReal.ofReal (margDens₁ κ rr p B₁ x₂ S₁ Tm ω))
                {ω | ∀ j, (ts j : ℝ≥0∞) < ζG ω ∧ (gW (ts j) ω, (fun i => gL i (ts j) ω),
                  (fun i => gR i (ts j) ω), Bh (ts j) ω) ∈ Asets j} =
              P₃ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₃ ω ∧
                (W₃ (ts j) ω, (fun i => VL₃ i (ts j) ω), (fun i => VR₃ i (ts j) ω), B₃ (ts j) ω) ∈ Asets j} := by
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ := h.exists_frzD10Hyp_marg0 rr
  have hS := isStoppingTime_lastExit h.stop₁
  obtain ⟨C, hC⟩ := (Bornology.isBounded_iUnion.2 fun j => (h.hull₁ j).2.1).exists_norm_le
  have hK : ∀ ω, fwdHull (drive κ B₁ ω) (marg0T S₁ ω) ⊆ Metric.closedBall (0 : ℂ) (max C 1) := fun ω z hz => by
    obtain ⟨j, hj⟩ := exists_lastExit_eq S₁ ω
    rw [marg0T_eq, hj] at hz
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hC z (Set.mem_iUnion.2 ⟨j, h.K₁ j ω hz⟩)).trans (le_max_left _ _)
  have hBb := hH.abs_B_le h.κpos h.cont₁ (lt_of_lt_of_le one_pos (le_max_right C 1)) hK
  have hown0 := h.ownData_marg0_empty (p := p)
  have hT0 : ∀ ω, (0 : ℝ) ∈ Icc (0 : ℝ) (marg0T S₁ ω) := fun ω => ⟨le_rfl, (hown0 ω).pos.le⟩
  have hw₀ : ∀ ω, marg0W κ B₁ x₂ S₁ ω 0 = 0 := fun ω => by
    rw [(hown0 ω).W'_eq_of_empty (hT0 ω)]; exact QuantumZipper.drive_zero (h.zero₁ ω)
  obtain ⟨ω₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  have hF := hH.toFrzMartHyp
  obtain ⟨nL, nR, e, hL, hR, hLa, hRm⟩ := exists_sort_marks (markPos_injective hF.ne hF.inj) (w₀ := 0)
    fun o => by have h1 := hF.markPos_ne ω₀ o; rwa [hw₀ ω₀] at h1
  obtain ⟨gW, gL, gR, ζG, hE, hagree, huniq⟩ := hH.exists_isIntegratedSLEEvolution_img_law h.κpos h.bm₁ h.cont₁
    hS h.lastExit_pos hBb e hw₀ hL hR hLa hRm
  rw [h.girsMeasure_marg0_eq rr] at hE huniq
  simp only [frzMarks_zero_eq_self, sub_zero] at hE huniq hagree hL hR hLa hRm
  refine ⟨nL, nR, e, hL, hR, hLa, hRm, _, _, gW, gL, gR, ζG, hE, fun ω => ?_, huniq⟩
  have hST : (lastExit S₁ ω : ℝ) ∈ Icc (0 : ℝ) (marg0T S₁ ω) := ⟨(lastExit S₁ ω).coe_nonneg, (marg0T_eq S₁ ω).ge⟩
  have ha := (hown0 ω).clock_eq_of_empty hST
  have hEq : EqOn (marg0W κ B₁ x₂ S₁ ω) (drive κ B₁ ω) (Icc 0 (marg0T S₁ ω)) := fun s hs =>
    (hown0 ω).W'_eq_of_empty hs
  obtain ⟨h1, h2⟩ := hagree ω
  rw [ha] at h1 h2
  refine ⟨h1, fun t ht => ?_⟩
  have htT : (t : ℝ) ≤ marg0T S₁ ω := (marg0T_eq S₁ ω).ge.trans' (NNReal.coe_le_coe.2 ht.le)
  have himg : ∀ x : ℝ, imgV (marg0W κ B₁ x₂ S₁ ω) x t = imgV (drive κ B₁ ω) x t := fun x => by
    unfold imgV
    rw [hEq ⟨t.coe_nonneg, htT⟩, Ito.fwdMap_congr_of_eqOn_of_le hEq htT]
  obtain ⟨g1, g2, g3⟩ := h2 t (NNReal.coe_lt_coe.2 ht)
  exact ⟨g1.trans (hEq ⟨t.coe_nonneg, htT⟩), fun i => (g2 i).trans (himg _), fun j => (g3 j).trans (himg _)⟩

/-! ### Curve `2` -/

theorem lastExit₂_pos [Nonempty ι] (ω : Ω₂) : 0 < lastExit S₂ ω := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  exact (h.pos₂ j ω).trans_le (le_lastExit S₂ ω j)

theorem coe_lastExit₂_le (ω : Ω₂) : (lastExit S₂ ω : ℝ) ≤ Tm := by
  rw [coe_lastExit]; exact maxIn_stairCols_le h.Tmpos.le fun i => h.le₂ i ω

omit [Fintype ι] h in
/-- Curve `2` translated to start at `0` is `√(16/κ) B₂`. -/
theorem drive₂_sub (ω : Ω₂) : (fun u => drive (16 / κ) B₂ ω u + x₂ - x₂) = drive (16 / κ) B₂ ω := by
  funext u; ring

/-- **The height-`0` image data of curve `2`** (translated by `−x₂`; the frozen curve `1` is its start `−x₂`). -/
theorem ownData_marg0₂ [Nonempty ι] (ω : Ω₂) :
    OwnData (drive (16 / κ) B₂ ω) (fwdHull (fun _ => -x₂) 0) (frzChart (fun _ => -x₂) 0) (marg0T S₂ ω)
      (marg0A₂ κ B₂ x₂ S₂ ω) (marg0W₂ κ B₂ x₂ S₂ ω) := by
  have hW : Continuous (drive (16 / κ) B₂ ω) := QuantumZipper.drive_continuous (h.cont₂ ω)
  have hW0 : drive (16 / κ) B₂ ω 0 = 0 := QuantumZipper.drive_zero (h.zero₂ ω)
  have hV : Continuous (fun _ : ℝ => -x₂) := continuous_const
  have hT : 0 < marg0T S₂ ω := by rw [marg0T_eq]; exact NNReal.coe_pos.2 (h.lastExit₂_pos ω)
  refine imgSelD_spec (exists_ownData hW hW0 hT (isHPHull_fwdHull hV le_rfl) (isMapOut_fwdMap_gen hV le_rfl) ?_)
  rw [QuantumZipper.RS.fwdHull_zero_eq_empty hV, closure_empty]
  exact Set.empty_disjoint _

theorem ownData_marg0₂_empty [Nonempty ι] (ω : Ω₂) :
    OwnData (drive (16 / κ) B₂ ω) ∅ id (marg0T S₂ ω) (marg0A₂ κ B₂ x₂ S₂ ω) (marg0W₂ κ B₂ x₂ S₂ ω) := by
  have h1 := h.ownData_marg0₂ ω
  rwa [QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const, frzChart_zero_eq_id] at h1

/-- **The frozen-hull hypotheses of A12 at height `0` for curve `2`** (translated by `−x₂`, frozen curve `1` on the
left: `exists_twoCurveD9_left_family` on the translated enclosures). -/
theorem exists_frzD10Hyp_marg0₂ [Nonempty ι] (rr : Fin n → ℝ) : ∃ r a₀ γ Γ lam L : ℝ,
    FrzD10Hyp (16 / κ) B₂ (marg0W₂ κ B₂ x₂ S₂) (marg0A₂ κ B₂ x₂ S₂) (fwdHull (fun _ => -x₂) 0)
      (frzChart (fun _ => -x₂) 0) (fun m => -(κ / 4) * rr m) (-x₂) (frzMarks (fun _ => -x₂) (fun m => p m - x₂) 0)
      (lastExit S₂) (marg0T S₂) r a₀ γ Γ lam L Tm := by
  set G : ι → Set ℂ := fun j => transl (-x₂) (H₂ j) with hG
  set F : ι → Set ℂ := fun j => transl (-x₂) (H₁ j) with hF
  have hsep' : ∀ j, ∀ a ∈ F j, ∀ z ∈ G j, 2 * δ j ≤ ‖a - z‖ := fun j =>
    sep_transl (fun a ha z hz => by rw [norm_sub_rev]; exact h.sep j z hz a ha) (-x₂)
  have hunion : ∀ j, transl (-x₂) (H₁ j ∪ H₂ j) = G j ∪ F j := fun j => by
    simp only [hG, hF, transl, Set.image_union, Set.union_comm]
  have hpH' : ∀ j m, Disjoint (Metric.ball (((fun m => p m - x₂) m : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j m => by
    have := disjoint_ball_transl (h.pH j m) (-x₂)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hqH' : ∀ j, Disjoint (Metric.ball ((q j - x₂ : ℝ) : ℂ) (2 * d j)) (G j ∪ F j) := fun j => by
    have := disjoint_ball_transl (h.qH j) (-x₂)
    rw [hunion j] at this
    simpa [sub_eq_add_neg] using this
  have hpinj' : Function.Injective (fun m => p m - x₂) := fun m k hmk => h.pinj (by simpa using hmk)
  obtain ⟨ω₁⟩ := nonempty_of_isFilteredBrownianReal h.bm₁
  obtain ⟨ω₂⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  have hV0F : ∀ j, (((fun _ : ℝ => -x₂) 0 : ℝ) : ℂ) ∈ closure (F j) := fun j => by
    have := mem_closure_transl ((h.twoEncl ω₁ ω₂).zero_mem_closure j) (-x₂)
    simpa using this
  obtain ⟨r, a₀, γ, Γ, lam, hr, ha, hg, hmain⟩ := exists_twoCurveD9_left_family
    (fun j => isHPHull_transl (h.hull₂ j) (-x₂)) (fun j => isHPHull_transl (h.hull₁ j) (-x₂)) h.δpos hsep' h.dpos
    (fun j => by linarith [h.qx j] : ∀ j, q j - x₂ < 0) hqH' hpH' hpinj' Tm
  obtain ⟨L, hL⟩ := exists_scaleOK hr ha hg Γ lam Tm
  have hTj : ∀ ω, ∃ j, marg0T S₂ ω = S₂ j ω := fun ω => by
    obtain ⟨j, hj⟩ := exists_lastExit_eq S₂ ω
    exact ⟨j, by rw [marg0T_eq, hj]⟩
  have hD : ∀ ω, TwoCurveD9 (frzDataOf (16 / κ) B₂ (marg0W₂ κ B₂ x₂ S₂) (marg0A₂ κ B₂ x₂ S₂)
      (frzChart (fun _ => -x₂) 0) (fun m => -(κ / 4) * rr m) (-x₂) (frzMarks (fun _ => -x₂) (fun m => p m - x₂) 0) ω)
      (fwdHull (fun _ => -x₂) 0) (marg0T S₂ ω) r a₀ γ Γ lam := fun ω => by
    obtain ⟨j, hj⟩ := hTj ω
    have hK : fwdHull (drive (16 / κ) B₂ ω) (marg0T S₂ ω) ⊆ G j := by
      have := fwdHull_sub_const_subset (c := x₂) (h.K₂ j ω)
      rwa [drive₂_sub ω, ← hj] at this
    refine hmain j (drive (16 / κ) B₂ ω) (fun _ => -x₂) 0 (marg0T S₂ ω) (marg0A₂ κ B₂ x₂ S₂ ω)
      (marg0W₂ κ B₂ x₂ S₂ ω) (16 / κ) (fun m => -(κ / 4) * rr m) (h.ownData_marg0₂ ω) continuous_const (hV0F j)
      (by linarith [h.qpos j]) le_rfl h.Tmpos.le (by rw [hj]; exact h.le₂ j ω) hK ?_
    rw [QuantumZipper.RS.fwdHull_zero_eq_empty continuous_const]
    exact Set.empty_subset _
  refine ⟨r, a₀, γ, Γ, lam, L, ⟨⟨fun ω => h.ownData_marg0₂ ω, fun ω => (marg0T_eq S₂ ω).ge, fun ω => ?_,
    fun ω => (hD ω).alive₀, fun ω m => (hD ω).alive m, (hD ω₂).ne, (hD ω₂).inj, fun ω => (hD ω).d9, hL⟩,
    fun ω t ht => (hD ω).drv t ht⟩⟩
  rw [marg0T_eq]; exact h.coe_lastExit₂_le ω

/-- **A12's tilted measure at height `0` for curve `2` is `m₂ · P₂`.** -/
theorem girsMeasure_marg0₂_eq (rr : Fin n → ℝ) :
    girsMeasure P₂ (Real.sqrt (16 / κ)) B₂ (lastExit S₂) (fun ω => (frzDataOf (16 / κ) B₂ (marg0W₂ κ B₂ x₂ S₂)
      (marg0A₂ κ B₂ x₂ S₂) (frzChart (fun _ => -x₂) 0) (fun m => -(κ / 4) * rr m) (-x₂)
      (frzMarks (fun _ => -x₂) (fun m => p m - x₂) 0) ω).ell) =
      P₂.withDensity fun ω => ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω) := by
  unfold girsMeasure
  congr 1
  funext ω
  have hx : min (maxIn (stairCols fun i => (S₂ i ω : ℝ))) Tm = (lastExit S₂ ω : ℝ) := by
    rw [coe_lastExit]; exact min_eq_left (maxIn_stairCols_le h.Tmpos.le fun i => h.le₂ i ω)
  have hd : ∀ s : ℝ≥0, drive (16 / κ) B₂ ω (s : ℝ) = Real.sqrt (16 / κ) * B₂ s ω := fun s => by
    simp only [drive, Real.toNNReal_coe]
  have hc : drive (16 / κ) B₂ ω 0 + x₂ = x₂ := by rw [QuantumZipper.drive_zero (h.zero₂ ω), zero_add]
  unfold girsDensity margDens₂ tEll tView tSelA tSelW
  simp only [hc, drive₂_sub, zero_sub]
  rw [hx, hd, add_sub_cancel_right, sub_self, h.zero₂ ω, mul_zero]
  rfl

/-- **The curve-`2` marginal of the stopped dual coupling is the force-point law up to the last exit time**
(§A.1.3, "its marginals are unchanged"), in coordinates translated by `−x₂`. Under `m₂ · P₂` (`margDens₂`, A16's
`map_snd_dualCoupling`) there is an integrated `SLE_{16/κ}(ρ)` evolution of the word "`−x₂` with weight `−8/κ`,
`p_m − x₂` with weight `(16/κ)(−κ/4) r_m`", living at least until `max_i S₂ i` and equal before it to `√(16/κ) B₂`
(curve `2` minus `x₂`) and the Loewner flow of the translated marks; its killed laws are those of every integrated
evolution of that word. -/
theorem exists_forceLaw₂ [Nonempty ι] (rr : Fin n → ℝ) :
    ∃ (nL nR : ℕ) (e : Fin nL ⊕ Fin nR ≃ Option (Fin n)),
      (∀ i, markPos (-x₂) (fun m => p m - x₂) (e (Sum.inl i)) < 0) ∧ (∀ i, 0 < markPos (-x₂) (fun m => p m - x₂) (e (Sum.inr i))) ∧
      Antitone (fun i => markPos (-x₂) (fun m => p m - x₂) (e (Sum.inl i))) ∧ Monotone (fun i => markPos (-x₂) (fun m => p m - x₂) (e (Sum.inr i))) ∧
      ∃ (𝓗 : Filtration ℝ≥0 mΩ₂) (Bh gW : ℝ≥0 → Ω₂ → ℝ) (gL : Fin nL → ℝ≥0 → Ω₂ → ℝ)
        (gR : Fin nR → ℝ≥0 → Ω₂ → ℝ) (ζG : Ω₂ → ℝ≥0∞),
        IsIntegratedSLEEvolution (16 / κ) (fun i => markPos (-x₂) (fun m => p m - x₂) (e (Sum.inl i))) (fun i => markPos (-x₂) (fun m => p m - x₂) (e (Sum.inr i)))
          (fun i => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inl i))) (fun i => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inr i)))
          (P₂.withDensity fun ω => ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω)) 𝓗 gW gL gR Bh ζG ∧
        (∀ ω, ENNReal.ofReal (lastExit S₂ ω) ≤ ζG ω ∧ ∀ t : ℝ≥0, t < lastExit S₂ ω →
          gW t ω = drive (16 / κ) B₂ ω t ∧ (∀ i, gL i t ω = imgV (drive (16 / κ) B₂ ω) (markPos (-x₂) (fun m => p m - x₂) (e (Sum.inl i))) t) ∧
          ∀ j, gR j t ω = imgV (drive (16 / κ) B₂ ω) (markPos (-x₂) (fun m => p m - x₂) (e (Sum.inr j))) t) ∧
        ∀ {Ω₃ : Type*} {m₃ : MeasurableSpace Ω₃} {P₃ : Measure Ω₃} [IsProbabilityMeasure P₃]
          {𝓕₃ : Filtration ℝ≥0 m₃} {W₃ : ℝ≥0 → Ω₃ → ℝ} {VL₃ : Fin nL → ℝ≥0 → Ω₃ → ℝ}
          {VR₃ : Fin nR → ℝ≥0 → Ω₃ → ℝ} {B₃ : ℝ≥0 → Ω₃ → ℝ} {ζ₃ : Ω₃ → ℝ≥0∞},
          IsIntegratedSLEEvolution (16 / κ) (fun i => markPos (-x₂) (fun m => p m - x₂) (e (Sum.inl i)))
            (fun i => markPos (-x₂) (fun m => p m - x₂) (e (Sum.inr i))) (fun i => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inl i)))
            (fun i => markWt (16 / κ) (fun m => -(κ / 4) * rr m) (e (Sum.inr i))) P₃ 𝓕₃ W₃ VL₃ VR₃ B₃ ζ₃ →
          ∀ (m : ℕ) (ts : Fin m → ℝ≥0) (Asets : Fin m → Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) × ℝ)),
            (∀ j, MeasurableSet (Asets j)) →
            (P₂.withDensity fun ω => ENNReal.ofReal (margDens₂ κ rr p B₂ x₂ S₂ Tm ω))
                {ω | ∀ j, (ts j : ℝ≥0∞) < ζG ω ∧ (gW (ts j) ω, (fun i => gL i (ts j) ω),
                  (fun i => gR i (ts j) ω), Bh (ts j) ω) ∈ Asets j} =
              P₃ {ω | ∀ j, (ts j : ℝ≥0∞) < ζ₃ ω ∧
                (W₃ (ts j) ω, (fun i => VL₃ i (ts j) ω), (fun i => VR₃ i (ts j) ω), B₃ (ts j) ω) ∈ Asets j} := by
  obtain ⟨r, a₀, γ, Γ, lam, L, hH⟩ := h.exists_frzD10Hyp_marg0₂ rr
  have hS := isStoppingTime_lastExit h.stop₂
  obtain ⟨C, hC⟩ := (Bornology.isBounded_iUnion.2 fun j => (h.hull₂ j).2.1).exists_norm_le
  have hK : ∀ ω, fwdHull (drive (16 / κ) B₂ ω) (marg0T S₂ ω) ⊆ Metric.closedBall (0 : ℂ) (max (C + |x₂|) 1) :=
      fun ω z hz => by
    obtain ⟨j, hj⟩ := exists_lastExit_eq S₂ ω
    rw [marg0T_eq, hj] at hz
    have hz' := fwdHull_sub_const_subset (c := x₂) (h.K₂ j ω) (by rwa [drive₂_sub ω])
    rw [mem_transl_iff] at hz'
    have h1 := hC _ (Set.mem_iUnion.2 ⟨j, hz'⟩)
    rw [Metric.mem_closedBall, dist_zero_right]
    have e : z = (z - ((-x₂ : ℝ) : ℂ)) + ((-x₂ : ℝ) : ℂ) := by ring
    calc ‖z‖ ≤ ‖z - ((-x₂ : ℝ) : ℂ)‖ + ‖((-x₂ : ℝ) : ℂ)‖ := by
          conv_lhs => rw [e]
          exact norm_add_le _ _
      _ ≤ C + |x₂| := by rw [Complex.norm_real, Real.norm_eq_abs, abs_neg]; linarith
      _ ≤ _ := le_max_left _ _
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) h.κpos
  have hBb := hH.abs_B_le hκ' h.cont₂ (lt_of_lt_of_le one_pos (le_max_right (C + |x₂|) 1)) hK
  have hown0 := h.ownData_marg0₂_empty (p := p)
  have hT0 : ∀ ω, (0 : ℝ) ∈ Icc (0 : ℝ) (marg0T S₂ ω) := fun ω => ⟨le_rfl, (hown0 ω).pos.le⟩
  have hw₀ : ∀ ω, marg0W₂ κ B₂ x₂ S₂ ω 0 = 0 := fun ω => by
    rw [(hown0 ω).W'_eq_of_empty (hT0 ω)]; exact QuantumZipper.drive_zero (h.zero₂ ω)
  obtain ⟨ω₀⟩ := nonempty_of_isFilteredBrownianReal h.bm₂
  have hF := hH.toFrzMartHyp
  obtain ⟨nL, nR, e, hL, hR, hLa, hRm⟩ := exists_sort_marks (markPos_injective hF.ne hF.inj) (w₀ := 0)
    fun o => by have h1 := hF.markPos_ne ω₀ o; rwa [hw₀ ω₀] at h1
  obtain ⟨gW, gL, gR, ζG, hE, hagree, huniq⟩ := hH.exists_isIntegratedSLEEvolution_img_law hκ' h.bm₂ h.cont₂
    hS h.lastExit₂_pos hBb e hw₀ hL hR hLa hRm
  rw [h.girsMeasure_marg0₂_eq rr] at hE huniq
  simp only [frzMarks_zero_eq_self, sub_zero] at hE huniq hagree hL hR hLa hRm
  refine ⟨nL, nR, e, hL, hR, hLa, hRm, _, _, gW, gL, gR, ζG, hE, fun ω => ?_, huniq⟩
  have hST : (lastExit S₂ ω : ℝ) ∈ Icc (0 : ℝ) (marg0T S₂ ω) := ⟨(lastExit S₂ ω).coe_nonneg, (marg0T_eq S₂ ω).ge⟩
  have ha := (hown0 ω).clock_eq_of_empty hST
  have hEq : EqOn (marg0W₂ κ B₂ x₂ S₂ ω) (drive (16 / κ) B₂ ω) (Icc 0 (marg0T S₂ ω)) := fun s hs =>
    (hown0 ω).W'_eq_of_empty hs
  obtain ⟨h1, h2⟩ := hagree ω
  rw [ha] at h1 h2
  refine ⟨h1, fun t ht => ?_⟩
  have htT : (t : ℝ) ≤ marg0T S₂ ω := (marg0T_eq S₂ ω).ge.trans' (NNReal.coe_le_coe.2 ht.le)
  have himg : ∀ x : ℝ, imgV (marg0W₂ κ B₂ x₂ S₂ ω) x t = imgV (drive (16 / κ) B₂ ω) x t := fun x => by
    unfold imgV
    rw [hEq ⟨t.coe_nonneg, htT⟩, Ito.fwdMap_congr_of_eqOn_of_le hEq htT]
  obtain ⟨g1, g2, g3⟩ := h2 t (NNReal.coe_lt_coe.2 ht)
  exact ⟨g1.trans (hEq ⟨t.coe_nonneg, htT⟩), fun i => (g2 i).trans (himg _), fun j => (g3 j).trans (himg _)⟩

end DualHyp

end ForceLaw

end InteractingSLE.ZhanGT4

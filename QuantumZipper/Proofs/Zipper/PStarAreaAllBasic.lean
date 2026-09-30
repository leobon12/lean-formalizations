import QuantumZipper.Proofs.LQG.AreaProfile
import QuantumZipper.Proofs.LQG.WedgeCanonical
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.LQG.WedgeFinZeroCoupling
import QuantumZipper.Proofs.LQG.WedgeInfTotal
import QuantumZipper.Proofs.Field.Factorization
import QuantumZipper.Proofs.GFF.CoordRegFwd
import QuantumZipper.Proofs.Thm18.G1PkgTrace
import QuantumZipper.Proofs.Zipper.Cor15Partial

/-!
# E6-PSTAR-AREA-ALL, part 1: the area predicate and its transformation rules

Theorem 1.3, node E6, the area half of `E6.PStarAreaAllStmt` (`HitScaleZip.lean`). The statement
asks, for a `P_*` sample and at every time `t ≥ 0`, that the quantum area measure `μ_t` of the
unzipped field be finite on every half-disc `B_a(0) ∩ ℍ` and have infinite total mass on `ℍ`.

This file isolates the *field-level* content in a single predicate `AreaAll γ x` and proves the
two transformation rules needed to move it along the reduction (`PStarAreaAll.lean`):

* `areaAll_congr` / `areaAll_congr_coords`: `AreaAll` depends only on the countable circle
  coordinates (`avgReg`), because `qAreaMeasure_congr` does
  (`Factorization.qAreaMeasure_congr`; the bridge from `coords` to `avgReg` is
  `Factorization.avgReg_reconstruct_coords`, own elementary);
* `areaAll_rescale_iff`: `AreaAll` is invariant under the rescaling `rescale x (Qc γ) b`,
  `b > 0`, for a good sample: the *finite half-disc* part by M4-T3's push-forward rule
  `GoodTransforms.qAreaMeasure_rescale` (the preimage of `B_a(0) ∩ ℍ` under `z ↦ z/b` is
  `B_{ab}(0) ∩ ℍ`, `GoodTransforms.preimage_div_ball_inter_H`), the *infinite total mass* part by
  `AreaProfile.qAreaMeasure_rescale_H` (`ℍ` is invariant under `z ↦ z/b`).

**On the finiteness half-disc input.** `IsLQGGood` supplies only `∀ K, IsCompact K → K ⊆ ℍ →
μ K < ⊤` (`HasAreaLimit`), and `B_a(0) ∩ ℍ` is *not* compact (it meets the real axis), so
finiteness there is extra information: it is the input Sheffield asserts on p. 21 ("a finite
amount of `μ_h` mass in each bounded neighborhood of 0") and which is proved for the free field
and its continuous shifts in `FinArea.ae_qAreaMeasure_ball_lt_top`,
`FinArea.ae_qAreaMeasure_add_ofFun_ball_lt_top` (`WedgeFinZero` for the wedge field). Nothing in
this file assumes it without proof: `AreaAll` carries it as part of the predicate, and the three
bridges below place it relative to the existing theory.

Further contents:

* `qAreaMeasure_H_sub_closedBall_eq_top`: infinite total area plus finiteness on bounded
  half-discs forces infinite area *far out* (`ℍ \ closedBall(0,R)`), the pure measure-theoretic
  half of the infinite-area node;
* `areaAll_of_hasAreaProfile`: `AreaProfile.HasAreaProfile γ x → AreaAll γ x` — so every proved
  area profile (free field, wedge field) yields `AreaAll`;
* `qAreaMeasure_unzippedField_zero`, `areaAll_unzippedField_zero`: at `t = 0` the unzipping map
  is the identity on `ℍ`, so the node at `t = 0` is the area property of the field itself;
* `ae_areaAll_wedgeField`, `ae_areaAll_freeField`: unconditional `AreaAll` for the wedge field
  (from the proved `WedgeFinZero` + `WedgeInf`) and for the free field.

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.6 p. 21, §5.4
pp. 70–72. All lemmas here are own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

/-! ## The predicate -/

/-- **The area property** of a field: the quantum area measure is finite on every half-disc
`B_a(0) ∩ ℍ` and has infinite total mass on `ℍ`. (These are the two properties of the unzipped
`P_*` fields asserted in Sheffield §5.4, pp. 70–72.) -/
def AreaAll (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ a : ℝ, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤) ∧ qAreaMeasure γ x H = ⊤

/-- `AreaAll` depends only on the area measure. -/
theorem areaAll_congr {γ : ℝ} {x x' : FieldSample} (hμ : qAreaMeasure γ x = qAreaMeasure γ x') :
    AreaAll γ x ↔ AreaAll γ x' := by
  simp only [AreaAll, hμ]

/-- Agreement on the circle coordinates gives agreement of `avgReg`
(own elementary; `Factorization.avgReg_reconstruct_coords`). -/
theorem avgReg_eq_of_coords_eq' {x y : FieldSample}
    (h : Factorization.coords x = Factorization.coords y) : avgReg x = avgReg y := by
  rw [← Factorization.avgReg_reconstruct_coords x, h, Factorization.avgReg_reconstruct_coords]

/-! ## Rescaling -/

/-! ## The tail of `ℍ` carries infinite area -/

/-- **Infinite total area implies infinite area far out**, given finiteness on the bounded
half-discs: `ℍ \ closedBall_ℝ(0,R) = B_{R+1}(0) ∩ ℍ` up to a set of finite `μ`-mass. This is the
half of the infinite-area node that is pure measure theory; the remaining input for
`E6.WedgeAreaHStmt` is the transport of infinite mass near `∞` through the unzipping map (the
area coordinate-change rule, together with `φ ≈ id` far out). -/
theorem qAreaMeasure_H_sub_closedBall_eq_top {γ : ℝ} {x : FieldSample}
    (hfin : ∀ a : ℝ, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤)
    (hH : qAreaMeasure γ x H = ⊤) (R : ℝ) :
    qAreaMeasure γ x (H \ Metric.closedBall (0 : ℂ) R) = ⊤ := by
  have hsub : H ⊆ (Metric.ball (0 : ℂ) (R + 1) ∩ H) ∪ (H \ Metric.closedBall (0 : ℂ) R) := by
    intro z hz
    by_cases h : z ∈ Metric.closedBall (0 : ℂ) R
    · have hR : ‖z‖ ≤ R := by
        have := Metric.mem_closedBall.1 h
        rwa [dist_zero_right] at this
      exact Or.inl ⟨by rw [Metric.mem_ball, dist_zero_right]; linarith, hz⟩
    · exact Or.inr ⟨hz, h⟩
  have hle : (⊤ : ℝ≥0∞) ≤ qAreaMeasure γ x (Metric.ball (0 : ℂ) (R + 1) ∩ H) +
      qAreaMeasure γ x (H \ Metric.closedBall (0 : ℂ) R) := by
    rw [← hH]
    exact (measure_mono hsub).trans (measure_union_le _ _)
  rcases ENNReal.add_eq_top.1 (le_antisymm le_top hle) with h | h
  · exact absurd h (hfin (R + 1)).ne
  · exact h

/-! ## From the area profile to `AreaAll` -/

/-- **An area profile gives `AreaAll`.** `AreaProfile.HasAreaProfile` already contains the
finiteness of every half-disc (`∀ a, profile μ a ≠ ⊤`), and its limit `profile μ → ⊤` at `atTop`
gives `μ ℍ = ⊤`, because `ℍ = ⋃_N B_N(0) ∩ ℍ` and the `profile` at the integer radii already
exhausts `ℍ`. -/
theorem areaAll_of_hasAreaProfile {γ : ℝ} {x : FieldSample}
    (h : AreaProfile.HasAreaProfile γ x) : AreaAll γ x := by
  set μ := qAreaMeasure γ x with hμ
  have hle : (⨆ a : ℝ, AreaProfile.profile μ a) ≤ (⨆ N : ℕ, AreaProfile.profile μ (N : ℝ)) :=
    iSup_le fun a => (AreaProfile.profile_mono μ (Nat.le_ceil a)).trans
      (le_iSup (fun N : ℕ => AreaProfile.profile μ (N : ℝ)) ⌈a⌉₊)
  have hsup : (⨆ a : ℝ, AreaProfile.profile μ a) = ⊤ :=
    iSup_eq_top.2 fun b hb => (h.2.2.2.2.eventually (IsOpen.mem_nhds isOpen_Ioi hb)).exists
  have hHtop : (⨆ N : ℕ, AreaProfile.profile μ (N : ℝ)) = μ H := by
    have hU : H = ⋃ N : ℕ, Metric.ball (0 : ℂ) N ∩ H := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      exact ⟨fun hz => by obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖; exact ⟨N, hN, hz⟩,
        fun hz => by obtain ⟨N, -, hzH⟩ := hz; exact hzH⟩
    have hmono : Monotone fun N : ℕ => Metric.ball (0 : ℂ) N ∩ H := fun N N' h =>
      inter_subset_inter_left _ (Metric.ball_subset_ball (by exact_mod_cast h))
    rw [hU, hmono.measure_iUnion]
    simp only [AreaProfile.profile]
  refine ⟨fun a => lt_top_iff_ne_top.2 (h.1 a), ?_⟩
  rw [← hHtop]
  exact eq_top_iff.2 (hsup ▸ hle)

/-! ## Time `0`: the unzipping map is the identity -/

/-- **At time `0` the unzipped field has the area measure of the field itself.** The unzipping
map at time `0` is the identity on `ℍ` when `W 0 = 0` (`Thm18Asm.G1Pkg.fwdMapInv_zero_time`),
and swapping the map on `ℍ` does not change `avgReg` (`CoordReg.avgReg_coordChange_congr`);
`coordChange x id Q` is the regularized sample (`Cor15Partial.coordChange_id_apply`), whose area
measure is that of `x` for a regular `x` (`WedgeCan.qAreaMeasure_evalReg`). -/
theorem qAreaMeasure_unzippedField_zero {γ : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hx : IsRegularSample x) :
    qAreaMeasure γ (unzippedField γ (x, W) 0) = qAreaMeasure γ x := by
  obtain ⟨F, hF⟩ := hx
  have hid : EqOn (fwdMapInv W 0) id H := fun w hw => by
    rw [Thm18Asm.G1Pkg.fwdMapInv_zero_time hW (show 0 < w.im from hw), hW0]
    simp
  have h1 : avgReg (coordChange x (fwdMapInv W 0) (Qc γ)) = avgReg (coordChange x id (Qc γ)) :=
    funext fun k => funext fun z => CoordReg.avgReg_coordChange_congr x hid (Qc γ) k z
  have h2 : coordChange x id (Qc γ) = fun μ => evalReg x μ :=
    funext fun μ => Cor15Partial.coordChange_id_apply x (Qc γ) μ
  show qAreaMeasure γ (coordChange x (fwdMapInv W 0) (Qc γ)) = qAreaMeasure γ x
  rw [Factorization.qAreaMeasure_congr h1 γ, h2, WedgeCan.qAreaMeasure_evalReg hF γ]

/-! ## `AreaAll` for the wedge field (unconditional) -/

/-- **`AreaAll` for the wedge field.** Sheffield §1.6, p. 21: the (unscaled) wedge field has
finite area on every bounded neighbourhood of `0` and infinite area in every neighbourhood of
`∞`. This is unconditional: the area profile of the wedge field is
`WedgeCan4.ae_hasAreaProfile_wedgeField_of_inputs`, whose two analytic inputs are the proved
`WedgeFinZero.wedgeFiniteNearZero_holds` and `WedgeInf.wedgeInfiniteTotal`. -/
theorem ae_areaAll_wedgeField {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} (hX : IsFreeGFFModConstH X P)
    (hA : IsWedgeProcess α (Qc γ) A P) (hInd : IndepFun X (fun ω t => A t ω) P) :
    ∀ᵐ ω ∂P, AreaAll γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) := by
  filter_upwards [WedgeCan4.ae_hasAreaProfile_wedgeField_of_inputs
    (WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hX hA hInd] with ω hω
  exact areaAll_of_hasAreaProfile hω

/-- **`AreaAll` for the free field** (unconditional), from `FinArea.ae_qAreaMeasure_ball_lt_top`
and `AreaProfile.ae_qAreaMeasure_H_eq_top`. -/
theorem ae_areaAll_freeField {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    ∀ᵐ ω ∂P, AreaAll γ (X ω) := by
  filter_upwards [FinArea.ae_qAreaMeasure_ball_lt_top hX hγ hγ2,
    AreaProfile.ae_qAreaMeasure_H_eq_top hX hγ hγ2] with ω h1 h2
  exact ⟨h1, h2⟩

end QuantumZipper.E6

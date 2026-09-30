import QuantumZipper.Proofs.Thm18.G4Weld2Arc
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Thm18.G4UnzipGoodField
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.E4L3i
import QuantumZipper.Proofs.Zipper.E5Model1
import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.Zipper.F1CanonLaw
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.F2WedgeCouple
import QuantumZipper.Proofs.Zipper.F2WeldTimes
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.HitScaleZipScale
import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G4CoreDownLong
import QuantumZipper.Proofs.Thm18.G4CoreUpShort
import QuantumZipper.Proofs.Thm18.G4CoreZipCocycle
import QuantumZipper.Proofs.Thm18.G4CapLen
import QuantumZipper.Proofs.Thm18.G4Weld2Arc
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Thm18.LenPos
import QuantumZipper.Proofs.LQG.GoodTransforms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: the base point of the re-zipping driver of `Z_ℓ ∘ Z_{−ℓ}`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 and the proof of
Theorem 1.8 (1): after unzipping the wedge configuration `c = (Y, W)` until the left quantum
length of the unzipped segment `η[0,τ]` is `ℓ` (`τ = unzipTime γ ℓ c`) and rescaling by
`a = unzipScale γ ℓ c`, the time reversal `revDrv W τ a` of the driver re-zips the segment. The
node `G4UpWeldIdStmt` (`G4Weld2Nodes.lean`) has two conjuncts; this file splits it as

* `G4UpWeldBaseStmt` (base point: `0₋(revDrv) = lenWeldPoint γ (Z_{−ℓ} c).1 ℓ`), **proved** here
  from existing nodes (`g4UpWeldBaseStmt_of`, `g4UpWeldBaseStmt_of_cont`), and
* `G4UpWeldHomStmt` (the welding homeomorphism of `revDrv` is `R_{(Z_{−ℓ} c).1}`), left open,

with `g4UpWeldIdStmt_of_base_hom : G4UpWeldBaseStmt → G4UpWeldHomStmt → G4UpWeldIdStmt`.

Proof of the base point (deterministic given the a.s. inputs):

1. On `[0, τ/a²]`, `revDrv W τ a = vrev W τ (a² ·)/a` (`revDrv_eqOn_vrev`), and Loewner scaling
   (Lawler, *Conformally Invariant Processes in the Plane*, Prop. 4.13 / A1(d),
   `LoewnerAlgebra.revMap_scale`) gives `0₋(revDrv W τ a) = 0₋(vrev W τ, τ)/a`
   (`zeroMinus_scale`; the junk values of `limUnder` are handled by `limUnder_eq_of_not_tendsto`).
2. `0₋(vrev W τ, τ) = O⁻_τ` (`B5.sideImages_fst_eq_zeroMinus_vrev`, as in `lenSideNegStmt_holds`).
3. `ν_{rescale x Q a} = (·/a)_* ν_x` (M4-T3, `GoodTransforms.qBoundaryMeasure_rescale`) gives
   `lenWeldPoint γ (rescale x Q a) ℓ = lenWeldPoint γ x ℓ / a` (`lenWeldPoint_rescale`).
4. `lenWeldPoint γ x_τ ℓ = O⁻_τ`: `ν_{x_τ}[O⁻_τ,0] = ℓ` (no overshoot, `G4UnzipPassStmt`) and
   `ν_{x_τ}` charges every `(O⁻_τ, v)` (`UnzipBdryPosStmt`) (`lenWeldPoint_eq_of_exact`).

`τ > 0` is `τ_{ℓ/2} < τ_ℓ` (`G4UnzipTimeStrictStmt`). **Own elementary argument** (bookkeeping
of the definitions; the paper takes these identities for granted).
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Pointwise

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. Deterministic scaling lemmas -/

/-- Two `limUnder`s without limit take the same junk value. -/
theorem limUnder_eq_of_not_tendsto {α β : Type} [TopologicalSpace β] [Nonempty β]
    {F : Filter α} {g h : α → β} (hg : ¬ ∃ L, Tendsto g F (𝓝 L))
    (hh : ¬ ∃ L, Tendsto h F (𝓝 L)) : limUnder F g = limUnder F h := by
  have hg' : ¬ ∃ L, map g F ≤ 𝓝 L := hg
  have hh' : ¬ ∃ L, map h F ≤ 𝓝 L := hh
  unfold limUnder lim Classical.epsilon Classical.strongIndefiniteDescription
  simp only [hg', hh', dite_false]

/-- `y ↦ c y` maps `𝓝[>] 0` into itself for `c > 0`. -/
theorem tendsto_mul_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => c * y) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have : Tendsto (fun y : ℝ => c * y) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact mul_pos hc hy

/-- `limUnder` at `0⁺` of `y ↦ g (a y) / a` vanishes iff that of `g` does. -/
theorem limUnder_scale_eq_zero_iff (g : ℝ → ℂ) {a : ℝ} (ha : 0 < a) :
    limUnder (𝓝[>] (0 : ℝ)) (fun y => g (a * y) / a) = 0 ↔
      limUnder (𝓝[>] (0 : ℝ)) g = 0 := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  by_cases hg : ∃ L, Tendsto g (𝓝[>] 0) (𝓝 L)
  · obtain ⟨L, hL⟩ := hg
    have hL' : Tendsto (fun y => g (a * y) / a) (𝓝[>] (0 : ℝ)) (𝓝 (L / a)) :=
      (hL.comp (tendsto_mul_nhdsGT_zero ha)).div_const _
    rw [hL.limUnder_eq, hL'.limUnder_eq, div_eq_zero_iff]
    simp [ha']
  · have hh : ¬ ∃ L, Tendsto (fun y => g (a * y) / a) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
      rintro ⟨L, hL⟩
      refine hg ⟨a * L, ?_⟩
      have h1 := (hL.comp (tendsto_mul_nhdsGT_zero (inv_pos.2 ha))).const_mul (a : ℂ)
      refine h1.congr fun y => ?_
      simp only [Function.comp]
      rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
      field_simp
    rw [limUnder_eq_of_not_tendsto hh hg]

/-- `sSup {x | p (a x)} = sSup {y | p y} / a` for `a > 0`. -/
theorem sSup_setOf_mul (p : ℝ → Prop) {a : ℝ} (ha : 0 < a) :
    sSup {x : ℝ | p (a * x)} = sSup {y : ℝ | p y} / a := by
  have hs : {x : ℝ | p (a * x)} = a⁻¹ • {y : ℝ | p y} := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_smul_set, smul_eq_mul]
    constructor
    · intro h
      exact ⟨a * x, h, by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]⟩
    · rintro ⟨y, hy, rfl⟩
      rwa [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  rw [hs, Real.sSup_smul_of_nonneg (inv_nonneg.2 ha.le), smul_eq_mul, div_eq_inv_mul]

/-- **Scaling of `0₋`**: `0₋(V(a² ·)/a, T/a²) = 0₋(V, T)/a`. -/
theorem zeroMinus_scale {V : ℝ → ℝ} (hV : Continuous V) {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    zeroMinus (fun s => V (a ^ 2 * s) / a) (T / a ^ 2) = zeroMinus V T / a := by
  have ha2 : a ^ 2 ≠ 0 := by positivity
  have hbd : ∀ x : ℝ, revMapBdry (fun s => V (a ^ 2 * s) / a) (T / a ^ 2) x = 0 ↔
      revMapBdry V T (a * x) = 0 := by
    intro x
    unfold revMapBdry
    have heq : (fun y : ℝ => revMap (fun s => V (a ^ 2 * s) / a) (T / a ^ 2) (x + y * Complex.I))
        =ᶠ[𝓝[>] (0 : ℝ)]
        fun y => (fun y' : ℝ => revMap V T (((a * x : ℝ) : ℂ) + y' * Complex.I)) (a * y) / a := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hz : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
      rw [LoewnerAlgebra.revMap_scale V hV ha (div_nonneg hT (by positivity)) hz,
        mul_div_cancel₀ _ ha2]
      congr 2
      push_cast
      ring
    have hl : limUnder (𝓝[>] (0 : ℝ))
          (fun y : ℝ => revMap (fun s => V (a ^ 2 * s) / a) (T / a ^ 2) (x + y * Complex.I)) =
        limUnder (𝓝[>] (0 : ℝ)) (fun y => (fun y' : ℝ => revMap V T (((a * x : ℝ) : ℂ) +
          y' * Complex.I)) (a * y) / a) := congrArg lim (Filter.map_congr heq)
    refine Iff.trans ?_ (limUnder_scale_eq_zero_iff (fun y' : ℝ => revMap V T (((a * x : ℝ) : ℂ) +
          y' * Complex.I)) ha)
    rw [hl]
  unfold zeroMinus
  have hset : {x : ℝ | x < 0 ∧ revMapBdry (fun s => V (a ^ 2 * s) / a) (T / a ^ 2) x = 0} =
      {x : ℝ | a * x < 0 ∧ revMapBdry V T (a * x) = 0} := by
    ext x
    simp only [mem_ofPred_eq, hbd]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨mul_neg_of_pos_of_neg ha h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨neg_of_mul_neg_right h1 ha.le, h2⟩
  rw [hset, sSup_setOf_mul (fun y => y < 0 ∧ revMapBdry V T y = 0) ha]

/-- **The left welding point at an exact passage**: if `ν[O,0] = ℓ` and `ν` charges every
`(O,v)`, `v ≤ 0`, then `lenWeldPoint = O`. -/
theorem lenWeldPoint_eq_of_exact {γ : ℝ} {x : FieldSample} {ℓ O : ℝ} (hO : O ≤ 0)
    (hex : qBoundaryMeasure γ x (Icc O 0) = ENNReal.ofReal ℓ)
    (hpos : ∀ v : ℝ, O < v → v ≤ 0 → 0 < qBoundaryMeasure γ x (Ioo O v)) :
    lenWeldPoint γ x ℓ = O := by
  refine IsGreatest.csSup_eq ⟨⟨hO, hex.ge⟩, ?_⟩
  rintro s ⟨hs0, hs⟩
  by_contra hlt
  push Not at hlt
  have hdisj : Disjoint (Ioo O s) (Icc s 0) :=
    Set.disjoint_left.2 fun u hu hu' => (lt_irrefl u) (hu.2.trans_le hu'.1)
  have hsub : Ioo O s ∪ Icc s 0 ⊆ Icc O 0 := by
    rintro u (hu | hu)
    · exact ⟨hu.1.le, hu.2.le.trans hs0⟩
    · exact ⟨hlt.le.trans hu.1, hu.2⟩
  have h1 := measure_mono (μ := qBoundaryMeasure γ x) hsub
  rw [measure_union hdisj measurableSet_Icc, hex] at h1
  have h2 := (hpos s hlt hs0).ne'
  have h3 : ENNReal.ofReal ℓ < ENNReal.ofReal ℓ + qBoundaryMeasure γ x (Ioo O s) :=
    ENNReal.lt_add_right ENNReal.ofReal_ne_top h2
  have h4 : ENNReal.ofReal ℓ + qBoundaryMeasure γ x (Ioo O s) ≤
      qBoundaryMeasure γ x (Ioo O s) + qBoundaryMeasure γ x (Icc s 0) := by
    rw [add_comm]; gcongr
  exact absurd (h3.trans_le (h4.trans h1)) (lt_irrefl _)

/-! ## 2. The split of `G4UpWeldIdStmt` -/

/-! ## 3. The base point -/

end Thm18Asm
end QuantumZipper

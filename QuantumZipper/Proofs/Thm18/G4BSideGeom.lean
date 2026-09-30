import QuantumZipper.Proofs.Zipper.LogShiftW2Pos
import QuantumZipper.Proofs.Zipper.F1Reflect
import QuantumZipper.Proofs.Thm18.G4CoreDefs2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, G4 Core B (task G4C-2): the side images of a restarted unzipping

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 (lengths read in the
unzipped picture) and §5.4 (proof of Theorem 1.8, pp. 69–72). Deterministic bookkeeping.

Let `W` be the SLE driver, `τ ≥ r > 0`, `u = τ − r` and `V = vrev W τ`. The configuration
unzipped by capacity time `u` has driver `W_u = W(u + ·) − W(u)`; unzipping it by `r` more
produces the segment `[O⁻_r(W_u), O⁺_r(W_u)]`, the image of the two sides of `η[u, τ]` in the
picture at time `τ`. This file proves

* `revMapBdry_neg_eq_zero_iff`, `zeroPlus_eq_neg_zeroMinus_neg`: reflection `z ↦ −z̄` exchanges
  `0₊^V` and `−0₋^{−V}` (A1(e) `revMap_reflect`; the junk value of `limUnder` is the same on both
  sides when no boundary limit exists);
* `lswPos_snd_eq_zeroPlus`: `O⁺_r(W_u) = 0₊^V(r)` (right counterpart of
  `F1.lswPos_fst_eq_zeroMinus`, by reflection);
* `ae_sideImages_zipCapDown`: a.s. at the Theorem 1.8 driver, for all `τ ≥ r > 0`,
  `O^∓_r(W_{τ−r}) = (0₋^V(r), 0₊^V(r))`.

Own elementary argument (reflection of the reverse Loewner flow; Lawler, *Conformally invariant
processes in the plane*, §4.1, uses these facts without proof).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-! ## 1. Reflection of the base preimages -/

/-- `revMapBdry (−V) T (−x) = 0 ↔ revMapBdry V T x = 0`. -/
theorem revMapBdry_neg_eq_zero_iff {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T)
    (x : ℝ) : revMapBdry (-V) T (-x) = 0 ↔ revMapBdry V T x = 0 := by
  set g : ℝ → ℂ := fun y => revMap V T ((x : ℂ) + (y : ℂ) * Complex.I) with hg
  set φ : ℂ → ℂ := fun z => -conj z with hφ
  have hφc : Continuous φ := Complex.continuous_conj.neg
  have hφφ : ∀ z, φ (φ z) = z := fun z => by simp [hφ]
  have heq : (fun y : ℝ => revMap (-V) T (((-x : ℝ) : ℂ) + (y : ℂ) * Complex.I)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun y => φ (g y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hz : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
    have h := LoewnerAlgebra.revMap_reflect V hV hT hz
    have e : -conj ((x : ℂ) + (y : ℂ) * Complex.I) = ((-x : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [e] at h
    simp only [hφ, hg]
    exact h
  have hL1 : revMapBdry (-V) T (-x) = limUnder (𝓝[>] (0 : ℝ)) (fun y => φ (g y)) := by
    unfold revMapBdry limUnder
    rw [Filter.map_congr heq]
  have hL2 : revMapBdry V T x = limUnder (𝓝[>] (0 : ℝ)) g := rfl
  rw [hL1, hL2]
  by_cases hex : ∃ L, Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 L)
  · obtain ⟨L, hL⟩ := hex
    have hL' : Tendsto (fun y => φ (g y)) (𝓝[>] (0 : ℝ)) (𝓝 (φ L)) := (hφc.tendsto L).comp hL
    rw [hL.limUnder_eq, hL'.limUnder_eq]
    simp [hφ]
  · have hex' : ¬ ∃ L, Tendsto (fun y => φ (g y)) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
      rintro ⟨L, hL⟩
      refine hex ⟨φ L, ?_⟩
      have := (hφc.tendsto L).comp hL
      simpa [Function.comp_def, hφφ] using this
    have hp : (fun a => map (fun y => φ (g y)) (𝓝[>] (0 : ℝ)) ≤ 𝓝 a) =
        fun a => map g (𝓝[>] (0 : ℝ)) ≤ 𝓝 a :=
      funext fun a => propext ⟨fun h => absurd ⟨a, h⟩ hex', fun h => absurd ⟨a, h⟩ hex⟩
    have : limUnder (𝓝[>] (0 : ℝ)) (fun y => φ (g y)) = limUnder (𝓝[>] (0 : ℝ)) g := by
      unfold limUnder lim
      rw [hp]
    rw [this]

/-- **`0₊^V(T) = −0₋^{−V}(T)`** (reflection). -/
theorem zeroPlus_eq_neg_zeroMinus_neg {V : ℝ → ℝ} (hV : Continuous V) {T : ℝ} (hT : 0 ≤ T) :
    zeroPlus V T = -zeroMinus (-V) T := by
  unfold zeroPlus zeroMinus
  have hs : {x : ℝ | 0 < x ∧ revMapBdry V T x = 0} =
      -{x : ℝ | x < 0 ∧ revMapBdry (-V) T x = 0} := by
    ext x
    simp only [Set.mem_neg, Set.mem_ofPred_eq, Left.neg_neg_iff,
      revMapBdry_neg_eq_zero_iff hV hT]
  rw [hs, Real.sInf_neg]

theorem vrev_neg (W : ℝ → ℝ) (T : ℝ) : B2.vrev (-W) T = -B2.vrev W T := by
  funext s
  simp only [B2.vrev, Pi.neg_apply]
  ring

/-! ## 2. The right side image of the restarted unzipping -/

/-- **`b_T(r) = 0₊^{vrev W T}(T − r)`** (right counterpart of `F1.lswPos_fst_eq_zeroMinus`,
by reflection `F1.lswPos_neg`). -/
theorem lswPos_snd_eq_zeroPlus {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hneg : ∀ v ≤ 0, W v = 0)
    (hK' : ∀ s : ℝ, 0 < s → IsSimpleCurveHull (revHull (B2.vrev (-W) s) s))
    (halive' : ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T → ∃ v, IsForwardSol (-W) (x : ℂ) T v)
    {T r : ℝ} (hT : 0 < T) (hr : r ∈ Icc 0 T) :
    (F1.lswPos W T r).2 = zeroPlus (B2.vrev W T) (T - r) := by
  have h1 := F1.lswPos_fst_eq_zeroMinus hW.neg (by simp [hW0])
    (fun v hv => by simp [hneg v hv]) hK' halive' hT hr
  rw [F1.lswPos_neg hW hr.2, vrev_neg] at h1
  rw [zeroPlus_eq_neg_zeroMinus_neg (B2.continuous_vrev hW T) (by linarith [hr.2]), ← h1,
    neg_neg]

/-- **The side images of the restarted unzipping at the Theorem 1.8 driver.** A.s., for all
`0 < r ≤ τ`, unzipping the configuration unzipped by `τ − r` by `r` more gives the segment
`[0₋^V(r), 0₊^V(r)]`, `V = vrev W τ`. -/
theorem ae_sideImages_zipCapDown {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, ∀ τ r : ℝ, r ∈ Ioc (0 : ℝ) τ →
      (sideImages (zipCapDown γ (τ - r) (wedgeConfig γ B Y ω)).2 r).1 =
          zeroMinus (B2.vrev (wedgeConfig γ B Y ω).2 τ) r ∧
        (sideImages (zipCapDown γ (τ - r) (wedgeConfig γ B Y ω)).2 r).2 =
          zeroPlus (B2.vrev (wedgeConfig γ B Y ω).2 τ) r := by
  obtain ⟨hγ, hγ2, hB, -, -⟩ := hS
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 ≤ 4 := by nlinarith
  have hB' : IsBrownianReal (RegUnif.negB B) P := hB.neg
  filter_upwards [RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4 P B
      hB, RegUnif.ae_forall_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4 P _ hB',
    RS.ae_real_alive hB hκ hκ4, RS.ae_real_alive hB' hκ hκ4, hB.cont, hB.eval_zero_ae_eq_zero]
    with ω hK hK' hal hal' hc h0 τ r hr
  have hW : Continuous (drive (γ ^ 2) B ω) := by
    unfold drive
    exact continuous_const.mul (hc.comp continuous_real_toNNReal)
  have hW0 : drive (γ ^ 2) B ω 0 = 0 := by simp [drive, h0]
  have hneg : ∀ v ≤ 0, drive (γ ^ 2) B ω v = 0 := fun v hv => by
    simp [drive, Real.toNNReal_of_nonpos hv, h0]
  simp only [B2.Vr, RegUnif.drive_negB] at hK hK' hal'
  have hτ : 0 < τ := hr.1.trans_le hr.2
  have hmem : τ - r ∈ Icc 0 τ := ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have e1 := F1.lswPos_fst_eq_zeroMinus hW hW0 hneg hK (fun x hx T hT => hal x hx T hT) hτ hmem
  have e2 := lswPos_snd_eq_zeroPlus hW hW0 hneg hK' (fun x hx T hT => hal' x hx T hT) hτ hmem
  unfold F1.lswPos at e1 e2
  rw [sub_sub_cancel] at e1 e2
  exact ⟨e1, e2⟩

end G4Core
end Thm18Asm
end QuantumZipper

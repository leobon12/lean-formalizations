import QuantumZipper.Proofs.Thm18.R18G3TXSide3
import QuantumZipper.Proofs.Thm18.G3RCond

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-c): the point `R(x)` of schemes `B` and `C` in region 2

Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71. Mirror image of `R18G3TXSide` for the
right point `R(x) = lenRight (ν₀ + ν₂) ℓ`: region-2 measures of `B` and `C` coincide
(`g3pν₂_cut_eq`), the gap measures give no mass to the closed region-2 interval, and region 2
gives no mass to `[0, t₂ − r₂]`; so reading `ℓ` in `B` and `ℓ − d_B + d_C` in `C`
(`d = ν₀[0, t₂ − r₂]`, outside-measurable) gives the same point in region 2 (`g3pR_transfer`).
Reflection `x ↦ −x` reduces `lenRight` to `lenLeft` (`lenRight_eq_neg_lenLeft`), so the
`x`-side lemma `lenLeft_congr` applies. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω

theorem map_neg_Icc (μ : Measure ℝ) (a b : ℝ) :
    (μ.map Neg.neg) (Icc a b) = μ (Icc (-b) (-a)) := by
  rw [Measure.map_apply measurable_neg measurableSet_Icc]
  congr 1
  ext x
  simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem lenRight_eq_neg_lenLeft (m : Measure ℝ) (ℓ : ℝ) :
    lenRight m ℓ = -lenLeft (m.map Neg.neg) ℓ := by
  unfold lenRight lenLeft
  rw [neg_neg]
  congr 1
  ext y
  simp only [mem_setOf_eq, map_neg_Icc, neg_neg, neg_zero]

/-- The open region-2 interval. -/
abbrev reg2 (i : G3Idx) : Set ℝ := Ioo (i.t₂ - i.r₂) (i.t₂ + i.r₂)

/-- The gap mass of `[0, t₂ − r₂]`. -/
def g3pd (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀) : ℝ :=
  (g3pν₀ γ g i ω (Icc 0 (i.t₂ - i.r₂))).toReal

theorem measurable_g3pd_out (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx) :
    Measurable[outsideSigma2 gffBase.X i.t₁ i.r₁ i.t₂ i.r₂] (g3pd γ g i) :=
  ENNReal.measurable_toReal.comp ((Measure.measurable_coe measurableSet_Icc).comp
    ((measurable_bdryM γ).comp (measurable_g3pGap γ g i)))

theorem g3_t₂_sub_r₂_pos (i : G3Idx) : 0 < i.t₂ - i.r₂ := by
  have := i.hη; unfold G3Idx.t₂ G3Idx.r₂; linarith

/-- The region-2 measure gives no mass to `[0, t₂ − r₂]`. -/
theorem g3pν₂_null_of {γ : ℝ} (hγ : 0 < γ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀)
    (hv : IsVagueLimitR (bdryApprox γ (g3pField γ g ω)) (qBoundaryMeasure γ (g3pField γ g ω)))
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ g ω) k))
    (hat : ∀ s, qBoundaryMeasure γ (g3pField γ g ω) {s} = 0) :
    g3pν₂ γ g i ω (Icc 0 (i.t₂ - i.r₂)) = 0 := by
  obtain ⟨hB2, e2⟩ := G3Fid.regionCut hγ hv hfin hat (t := i.t₂) i.r₂_pos
  rw [g3pν₂, bdryM, if_pos hB2, e2, Measure.restrict_apply measurableSet_Icc]
  exact measure_mono_null (fun x hx => absurd hx.2.1 (not_lt.2 hx.1.2)) measure_empty

/-- The gap measure gives no mass to the closed region-2 interval. -/
theorem g3pν₀_region2_null_of {γ : ℝ} (hγ : 0 < γ) (g : ℂ → ℝ) (i : G3Idx) (ω : Ω₀)
    (hv : IsVagueLimitR (bdryApprox γ (g3pField γ g ω)) (qBoundaryMeasure γ (g3pField γ g ω)))
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (bdryApprox γ (g3pField γ g ω) k))
    (hat : ∀ s, qBoundaryMeasure γ (g3pField γ g ω) {s} = 0) :
    g3pν₀ γ g i ω (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0 := by
  obtain ⟨hB0, e0⟩ := G3Fid.gapCut hγ hv hfin hat (t₁ := i.t₁) (t₂ := i.t₂) i.r₁_pos i.r₂_pos
  rw [g3pν₀, bdryM, if_pos hB0, e0, Measure.restrict_apply measurableSet_Icc]
  exact measure_mono_null (fun x hx => (hx.2 (Or.inr hx.1)).elim) measure_empty

/-- Splitting `[0, y]` at `t₂ − r₂`. -/
theorem g3pm2_split {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {ω : Ω₀}
    (h0 : g3pν₀ γ g i ω (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0)
    (h2z : g3pν₂ γ g i ω (Icc 0 (i.t₂ - i.r₂)) = 0) {y : ℝ} (hy : y ∈ reg2 i) :
    (g3pν₀ γ g i ω + g3pν₂ γ g i ω) (Icc 0 y) =
      g3pν₂ γ g i ω (Ioc (i.t₂ - i.r₂) y) + ENNReal.ofReal (g3pd γ g i ω) := by
  have hpos := g3_t₂_sub_r₂_pos i
  have hu : Icc 0 y = Icc 0 (i.t₂ - i.r₂) ∪ Ioc (i.t₂ - i.r₂) y :=
    (Icc_union_Ioc_eq_Icc hpos.le hy.1.le).symm
  have hdis : Disjoint (Icc 0 (i.t₂ - i.r₂)) (Ioc (i.t₂ - i.r₂) y) :=
    disjoint_left.2 fun x h1 h2 => absurd h1.2 (not_le.2 h2.1)
  have hz : g3pν₀ γ g i ω (Ioc (i.t₂ - i.r₂) y) = 0 :=
    measure_mono_null (fun x (hx : x ∈ Ioc (i.t₂ - i.r₂) y) =>
      (⟨hx.1.le, hx.2.trans hy.2.le⟩ : x ∈ Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂))) h0
  rw [hu, measure_union hdis measurableSet_Ioc, Measure.add_apply, Measure.add_apply, hz, h2z,
    add_zero, zero_add, g3pd, ENNReal.ofReal_toReal (g3pν₀_le_m γ g i ω _ _), add_comm]

/-- **The point `R(x)` of `g` in region 2 is that of `g'` at the shifted length.** -/
theorem g3pR_transfer {γ : ℝ} {g g' : ℂ → ℝ} {i : G3Idx} {ω : Ω₀} {ℓ : ℝ}
    (h2 : g3pν₂ γ g i ω = g3pν₂ γ g' i ω)
    (h2z : g3pν₂ γ g i ω (Icc 0 (i.t₂ - i.r₂)) = 0)
    (h0 : g3pν₀ γ g i ω (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0)
    (h0' : g3pν₀ γ g' i ω (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0)
    (hx : g3pR γ g i (ω, ℓ) ∈ reg2 i) :
    g3pR γ g' i (ω, ℓ - g3pd γ g i ω + g3pd γ g' i ω) = g3pR γ g i (ω, ℓ) := by
  have hpos := g3_t₂_sub_r₂_pos i
  have h2z' : g3pν₂ γ g' i ω (Icc 0 (i.t₂ - i.r₂)) = 0 := by rw [← h2]; exact h2z
  set m := (g3pν₀ γ g i ω + g3pν₂ γ g i ω).map Neg.neg
  set m' := (g3pν₀ γ g' i ω + g3pν₂ γ g' i ω).map Neg.neg
  have hc : m (Icc (-(i.t₂ - i.r₂)) 0) = ENNReal.ofReal (g3pd γ g i ω) := by
    rw [map_neg_Icc, neg_zero, neg_neg, Measure.add_apply, h2z, add_zero, g3pd,
      ENNReal.ofReal_toReal (g3pν₀_le_m γ g i ω _ _)]
  have hc' : m' (Icc (-(i.t₂ - i.r₂)) 0) = ENNReal.ofReal (g3pd γ g' i ω) := by
    rw [map_neg_Icc, neg_zero, neg_neg, Measure.add_apply, h2z', add_zero, g3pd,
      ENNReal.ofReal_toReal (g3pν₀_le_m γ g' i ω _ _)]
  have hR : g3pR γ g i (ω, ℓ) = -lenLeft m ℓ := lenRight_eq_neg_lenLeft _ _
  have hR' : g3pR γ g' i (ω, ℓ - g3pd γ g i ω + g3pd γ g' i ω) =
      -lenLeft m' (ℓ - g3pd γ g i ω + g3pd γ g' i ω) := lenRight_eq_neg_lenLeft _ _
  have hx' : lenLeft m ℓ ∈ Ioo (-(i.t₂ + i.r₂)) (-(i.t₂ - i.r₂)) := by
    rw [hR] at hx; exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have key := lenLeft_congr (c := g3pd γ g i ω) (c' := g3pd γ g' i ω) (neg_lt_zero.2 hpos)
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg hc hc'
    (fun y => g3pν₂ γ g i ω (Ioc (i.t₂ - i.r₂) y)) (fun y hy => by
      have hy' : y ∈ reg2 i := ⟨by linarith [hy.1], by linarith [hy.2]⟩
      refine ⟨?_, ?_⟩
      · rw [map_neg_Icc, neg_zero, neg_neg, g3pm2_split h0 h2z hy']
      · rw [map_neg_Icc, neg_zero, neg_neg, g3pm2_split h0' h2z' hy', h2]) hx'
  rw [hR', hR, key]

/-- The Palm length exceeds `d` when `R(x)` lies in region 2. -/
theorem lt_of_g3pR_mem {γ : ℝ} {g : ℂ → ℝ} {i : G3Idx} {ω : Ω₀} {ℓ : ℝ}
    (h2z : g3pν₂ γ g i ω (Icc 0 (i.t₂ - i.r₂)) = 0) (hx : g3pR γ g i (ω, ℓ) ∈ reg2 i) :
    g3pd γ g i ω < ℓ := by
  have hpos := g3_t₂_sub_r₂_pos i
  set m := (g3pν₀ γ g i ω + g3pν₂ γ g i ω).map Neg.neg
  have hc : m (Icc (-(i.t₂ - i.r₂)) 0) = ENNReal.ofReal (g3pd γ g i ω) := by
    rw [map_neg_Icc, neg_zero, neg_neg, Measure.add_apply, h2z, add_zero, g3pd,
      ENNReal.ofReal_toReal (g3pν₀_le_m γ g i ω _ _)]
  have hR : g3pR γ g i (ω, ℓ) = -lenLeft m ℓ := lenRight_eq_neg_lenLeft _ _
  rw [hR] at hx
  exact lt_of_lenLeft_mem (neg_lt_zero.2 hpos) hc
    (A := -(i.t₂ + i.r₂)) ⟨by linarith [hx.2], by linarith [hx.1]⟩

/-- Almost surely the region-2 null facts hold for both schemes and every index. -/
theorem ae_gap2_null {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂gffBase.P, ∀ i : G3Idx,
      g3pν₀ γ (g3wCut γ i.η) i ω (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0 ∧
      g3pν₀ γ (g3wProf γ) i ω (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0 ∧
      g3pν₂ γ (g3wProf γ) i ω (Icc 0 (i.t₂ - i.r₂)) = 0 := by
  filter_upwards [ae_g3pField_good hγ hγ2, ae_g3pBField_good hγ hγ2] with ω hC hB i
  exact ⟨g3pν₀_region2_null_of hγ _ i ω (hB i.η i.hη).1 (hB i.η i.hη).2.1 (hB i.η i.hη).2.2.1,
    g3pν₀_region2_null_of hγ _ i ω hC.1 hC.2.1 hC.2.2.1,
    g3pν₂_null_of hγ _ i ω hC.1 hC.2.1 hC.2.2.1⟩

/-- The shift `Ψ(ω, ℓ) = (ω, ℓ + d_C(ω) − d_B(ω))` from scheme `B` to scheme `C`. -/
def g3Ψ (γ : ℝ) (i : G3Idx) (p : Ω₀ × ℝ) : Ω₀ × ℝ :=
  (p.1, p.2 + (g3pd γ (g3wProf γ) i p.1 - g3pd γ (g3wCut γ i.η) i p.1))

/-- On good samples, `R(x)` of `B` in region 2 is `R(x)` of `C` after the shift, and
conversely. -/
theorem g3pR_Ψ {γ : ℝ} {i : G3Idx} {p : Ω₀ × ℝ}
    (h0B : g3pν₀ γ (g3wCut γ i.η) i p.1 (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0)
    (h0C : g3pν₀ γ (g3wProf γ) i p.1 (Icc (i.t₂ - i.r₂) (i.t₂ + i.r₂)) = 0)
    (h2z : g3pν₂ γ (g3wProf γ) i p.1 (Icc 0 (i.t₂ - i.r₂)) = 0) :
    (g3pR γ (g3wCut γ i.η) i p ∈ reg2 i → g3pR γ (g3wProf γ) i (g3Ψ γ i p) =
      g3pR γ (g3wCut γ i.η) i p) ∧
    (g3pR γ (g3wProf γ) i (g3Ψ γ i p) ∈ reg2 i → g3pR γ (g3wCut γ i.η) i p =
      g3pR γ (g3wProf γ) i (g3Ψ γ i p)) := by
  have h2 := g3pν₂_cut_eq γ i p.1
  have h2zB : g3pν₂ γ (g3wCut γ i.η) i p.1 (Icc 0 (i.t₂ - i.r₂)) = 0 := by rw [h2]; exact h2z
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have e := g3pR_transfer (ℓ := p.2) h2 h2zB h0B h0C hx
    rw [show p.2 - g3pd γ (g3wCut γ i.η) i p.1 + g3pd γ (g3wProf γ) i p.1 =
      p.2 + (g3pd γ (g3wProf γ) i p.1 - g3pd γ (g3wCut γ i.η) i p.1) by ring] at e
    exact e
  · have e := g3pR_transfer (g := g3wProf γ) (g' := g3wCut γ i.η)
      (ℓ := p.2 + (g3pd γ (g3wProf γ) i p.1 - g3pd γ (g3wCut γ i.η) i p.1)) h2.symm h2z h0C h0B hx
    rw [show p.2 + (g3pd γ (g3wProf γ) i p.1 - g3pd γ (g3wCut γ i.η) i p.1) -
      g3pd γ (g3wProf γ) i p.1 + g3pd γ (g3wCut γ i.η) i p.1 = p.2 by ring] at e
    exact e

end R18
end QuantumZipper

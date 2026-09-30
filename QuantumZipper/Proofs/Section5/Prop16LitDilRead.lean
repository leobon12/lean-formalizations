import QuantumZipper.Proofs.Section5.Prop16LitDilLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: the dilation event on the local readings (D98)

`dilSet`: readings `q = (y, x)` for which, with the rational scale `S = scaleQ` of the rebuilt
chart zoom, either `S ≤ 0` or `DilGood` holds at `S`. A Borel set (`measurableSet_dilSet`);
membership is a property of the rebuilt chart zoom (`mem_dilSet_iff`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA Prop16Asm

variable {D : Set ℂ} {a b : ℝ} {ψ : ℝ → ℂ → ℂ} {r₀ : ℝ → ℝ}

theorem measurable_hbCut₂ (n : ℕ) : Measurable fun p : ℝ × ℂ => hbCut p.1 n p.2 := by
  unfold hbCut
  exact measurable_const.min (measurable_const.max ((measurable_const.mul
    ((measurable_fst.sub (measurable_snd.norm)).min (Complex.measurable_im.comp measurable_snd))).sub
    measurable_const))

theorem avgReg_litZr (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) {q : (ℕ → ℝ) × ℝ}
    (hq : q.2 ∈ Ioo a b) :
    avgReg (litZr hfam γ C q) = avgReg (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2)) := by
  have h := (exists_measurable_coords_litRep hfam γ C).choose_spec.2 q hq
  simp only [litZr, litPhi]
  rw [← h]
  exact Factorization.avgReg_reconstruct_coords _

/-- The rational scale of the rebuilt chart zoom. -/
def litS (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) (q : (ℕ → ℝ) × ℝ) : ℝ :=
  scaleQ γ (litZr hfam γ C q) (r₀ q.2)

/-- Its positive version. -/
def litSp (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) (q : (ℕ → ℝ) × ℝ) : ℝ :=
  if 0 < litS hfam γ C q then litS hfam γ C q else 1

theorem litSp_pos (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) (q : (ℕ → ℝ) × ℝ) :
    0 < litSp hfam γ C q := by
  unfold litSp; split_ifs with h
  · exact h
  · exact one_pos

theorem measurable_litS (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) : Measurable (litS hfam γ C) :=
  measurable_scaleQ (measurable_litZr hfam γ C) (hfam.2.1.comp measurable_snd) γ

theorem measurable_litSp (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) : Measurable (litSp hfam γ C) :=
  Measurable.ite (measurableSet_lt measurable_const (measurable_litS hfam γ C))
    (measurable_litS hfam γ C) measurable_const

/-- **The dilation event on readings.** -/
def dilSet (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) : Set ((ℕ → ℝ) × ℝ) :=
  {q | q.2 ∈ Ioo a b} ∩ ({q | litS hfam γ C q ≤ 0} ∪ ({q | 0 < litS hfam γ C q} ∩
    {q | DilGood γ (litZr hfam γ C q) (r₀ q.2) (litSp hfam γ C q)}))

theorem dilGood_set_eq {α : Type*} {γ : ℝ} (Z : α → FieldSample) (S r : α → ℝ) :
    {q | DilGood γ (Z q) (r q) (S q)} =
      goodExA γ (fun q => rescale (Z q) (Qc γ) (S q)) (fun q => r q / S q) ∩
      ⋂ n : ℕ, ⋂ g ∈ famF, {q | ∃ l,
        Tendsto (fun k => ∫ z, hbCut (r q / S q) n z * g z
          ∂areaApprox γ (rescale (Z q) (Qc γ) (S q)) k) atTop (𝓝 l) ∧
        Tendsto (fun k => ∫ z, hbCut (r q / S q) n (z / S q) * g (z / S q)
          ∂areaApprox γ (Z q) k) atTop (𝓝 l)} := by
  ext q
  simp only [mem_setOf_eq, mem_inter_iff, mem_iInter]
  exact Iff.rfl

theorem measurableSet_dilCommon {α : Type*} [MeasurableSpace α] {γ : ℝ} {Z : α → FieldSample}
    (hZ : Measurable Z) {S : α → ℝ} (hS : Measurable S) (hS0 : ∀ q, 0 < S q) {r : α → ℝ}
    (hr : Measurable r) (n : ℕ) {g : ℂ → ℝ} (hgm : Measurable g) :
    MeasurableSet {q | ∃ l,
        Tendsto (fun k => ∫ z, hbCut (r q / S q) n z * g z
          ∂areaApprox γ (rescale (Z q) (Qc γ) (S q)) k) atTop (𝓝 l) ∧
        Tendsto (fun k => ∫ z, hbCut (r q / S q) n (z / S q) * g (z / S q)
          ∂areaApprox γ (Z q) k) atTop (𝓝 l)} := by
  have hA := measurable_avgReg_rescale_fam hZ hS hS0 (Qc γ)
  have hrs : Measurable fun q => r q / S q := hr.div hS
  have hc1 : Measurable fun p : α × ℂ => hbCut (r p.1 / S p.1) n p.2 * g p.2 :=
    ((measurable_hbCut₂ n).comp ((hrs.comp measurable_fst).prodMk measurable_snd)).mul
      (hgm.comp measurable_snd)
  have hdiv : Measurable fun p : α × ℂ => p.2 / (S p.1 : ℂ) :=
    measurable_snd.div (Complex.measurable_ofReal.comp (hS.comp measurable_fst))
  have hc2 : Measurable fun p : α × ℂ =>
      hbCut (r p.1 / S p.1) n (p.2 / S p.1) * g (p.2 / S p.1) :=
    ((measurable_hbCut₂ n).comp ((hrs.comp measurable_fst).prodMk hdiv)).mul (hgm.comp hdiv)
  have h1 := fun k => measurable_integral_areaApprox_fam' (Z := fun q => rescale (Z q) (Qc γ) (S q))
    γ k (hA k) (T := fun q z => hbCut (r q / S q) n z * g z) hc1
  have h2 := fun k => measurable_integral_areaApprox_fam hZ γ k
    (T := fun q z => hbCut (r q / S q) n (z / S q) * g (z / S q)) hc2
  exact measurableSet_common_limit h1 h2

theorem measurableSet_dilGood_fam {α : Type*} [MeasurableSpace α] {γ : ℝ} {Z : α → FieldSample}
    (hZ : Measurable Z) {S : α → ℝ} (hS : Measurable S) (hS0 : ∀ q, 0 < S q) {r : α → ℝ}
    (hr : Measurable r) : MeasurableSet {q | DilGood γ (Z q) (r q) (S q)} := by
  rw [dilGood_set_eq]
  have hA : ∀ k, Measurable fun p : α × ℂ => avgReg (rescale (Z p.1) (Qc γ) (S p.1)) k p.2 :=
    measurable_avgReg_rescale_fam hZ hS hS0 (Qc γ)
  have hG := measurableSet_goodExA' (γ := γ) (Z := fun q => rescale (Z q) (Qc γ) (S q))
    (r := fun q => r q / S q) hA (hr.div hS)
  exact hG.inter
    (MeasurableSet.iInter fun n => MeasurableSet.biInter famF_countable fun g hg =>
      measurableSet_dilCommon hZ hS hS0 hr n (famF_dense.1 g hg).1.measurable)

theorem measurableSet_dilSet (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) :
    MeasurableSet (dilSet hfam γ C) := by
  have hS := measurable_litS hfam γ C
  refine (measurableSet_Ioo.preimage measurable_snd).inter
    ((measurableSet_le hS measurable_const).union ((measurableSet_lt measurable_const hS).inter ?_))
  exact measurableSet_dilGood_fam (measurable_litZr hfam γ C) (measurable_litSp hfam γ C)
    (litSp_pos hfam γ C) (hfam.2.1.comp measurable_snd)

/-- **Membership is a property of the rebuilt chart zoom.** -/
theorem mem_dilSet_iff (hfam : LitFamily D a b ψ r₀) (γ C : ℝ) {q : (ℕ → ℝ) × ℝ}
    (hq : q.2 ∈ Ioo a b) : q ∈ dilSet hfam γ C ↔
      (0 < scaleQ γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2)) (r₀ q.2) →
        DilGood γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2)) (r₀ q.2)
          (scaleQ γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2)) (r₀ q.2))) := by
  have he := avgReg_litZr hfam γ C hq
  have hS : litS hfam γ C q = scaleQ γ (zoomFieldLit γ C (repFam D a b 0 q.1) q.2 (ψ q.2))
      (r₀ q.2) := scaleQ_congr_avgReg he _
  simp only [dilSet, mem_inter_iff, mem_union, mem_setOf_eq, hq, true_and]
  rw [← hS]
  constructor
  · rintro (h | ⟨h0, hD⟩) hpos
    · exact absurd hpos (not_lt.2 h)
    · have hSp : litSp hfam γ C q = litS hfam γ C q := by simp [litSp, h0]
      rw [hSp] at hD
      exact (dilGood_congr_avgReg he _ _).1 hD
  · intro h
    by_cases h0 : 0 < litS hfam γ C q
    · refine Or.inr ⟨h0, ?_⟩
      have hSp : litSp hfam γ C q = litS hfam γ C q := by simp [litSp, h0]
      rw [hSp]
      exact (dilGood_congr_avgReg he _ _).2 (h h0)
    · exact Or.inl (not_lt.1 h0)

end Prop16Lit
end QuantumZipper

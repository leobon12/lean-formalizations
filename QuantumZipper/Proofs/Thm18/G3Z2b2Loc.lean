import QuantumZipper.Proofs.Thm18.G0MapLoc
import QuantumZipper.Proofs.Thm18.G1PkgLeft
import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Complex.UniformizerUnique
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3Z2B-2 (1): the local maps of the curve, measurably in the path

`g1zLocMap left W x = ψ(· + ψ⁻¹(x)) − x` is built from the chosen normalized uniformizer
`uniformizer (sideDom η left)`. Normalized uniformizers are unique only up to a positive
dilation (`CA.Uniformizer.normalizedUniformizer_unique_*`), and the choice of the dilation is not
measurable in the path, so `g1zLocMap` itself is not a measurable function of the path. Instead:

* `g3locM Ψ left (a, x, w) = Ψ_a(w + b(a, x)) − x` is built from the **measurable selection**
  `Ψ` of inverse normalized uniformizers (`G1PsiSel`, proved: `g1PsiSelStmt`). The boundary
  preimage `b(a, x)` of `x` is read from the boundary values of `Ψ_a` at rational points, as an
  `iSup` (right side) or an `iInf` (left side) over `ℚ` (`g3bpre`).
* `measurable_g3locM`: `(a, x, w) ↦ g3locM Ψ left (a, x, w)` is measurable.
* `g1zLocMap_eq_g3locM`: for every good path (continuous, simple chord, normalized chosen
  uniformizer) there is `c > 0` with `g1zLocMap left W x w = g3locM Ψ left (a, x, c w)` for all
  `x` on the side half-line and all `w`: the two local maps differ by the dilation `w ↦ c w`,
  which the canonical description absorbs.

`G3LocMeasStmt` packages this (`g3LocMeasStmt_holds`). Sheffield, arXiv:1012.4797, p. 70 uses
the side maps without discussing measurability; own bookkeeping (AGENT_GUIDE cost rule), with the
Schwarz-reflection boundary values `G1Z2.sideReflChordStmt_holds` and the uniqueness of normalized
uniformizers (Riemann mapping; Ahlfors, *Complex Analysis*, Ch. 6 §1).
-/

noncomputable section

open MeasureTheory Filter Set Function Complex
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Z2b2

open G1ZZ1

variable (Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ)

/-- The approximation points `q + i/(n+1)` of a real point `q`. -/
def apx (q : ℝ) (n : ℕ) : ℂ := (q : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I

/-- The boundary value of `Ψ_a` at the real point `q`. -/
def g3bl (left : Bool) (a : ℝ≥0 → ℝ) (q : ℝ) : ℂ := limUnder atTop fun n => Ψ left a (apx q n)

/-- The boundary preimage of `x` read at rational points. -/
def g3bpre (left : Bool) (a : ℝ≥0 → ℝ) (x : ℝ) : ℝ :=
  if left then ⨅ q : ℚ, (if (q : ℝ) < 0 ∧ x ≤ (g3bl Ψ left a q).re then (q : ℝ) else 0)
  else ⨆ q : ℚ, (if 0 < (q : ℝ) ∧ (g3bl Ψ left a q).re ≤ x then (q : ℝ) else 0)

/-- The measurable local maps. -/
def g3locM (left : Bool) (p : (ℝ≥0 → ℝ) × ℝ × ℂ) : ℂ :=
  Ψ left p.1 (p.2.2 + (g3bpre Ψ left p.1 p.2.1 : ℂ)) - (p.2.1 : ℂ)

variable {Ψ}

theorem measurable_g3bl (hΨ : ∀ left, Measurable fun p : (ℝ≥0 → ℝ) × ℂ => Ψ left p.1 p.2)
    (left : Bool) (q : ℝ) : Measurable fun a => g3bl Ψ left a q := by
  have h : ∀ n : ℕ, Measurable fun a => Ψ left a (apx q n) := fun n =>
    (hΨ left).comp (measurable_id.prodMk measurable_const)
  exact (StronglyMeasurable.limUnder (l := atTop) (f := fun n a => Ψ left a (apx q n))
    fun n => (h n).stronglyMeasurable).measurable

theorem measurable_g3bpre (hΨ : ∀ left, Measurable fun p : (ℝ≥0 → ℝ) × ℂ => Ψ left p.1 p.2)
    (left : Bool) : Measurable fun p : (ℝ≥0 → ℝ) × ℝ => g3bpre Ψ left p.1 p.2 := by
  have hre : ∀ q : ℚ, Measurable fun p : (ℝ≥0 → ℝ) × ℝ => (g3bl Ψ left p.1 q).re := fun q =>
    Complex.measurable_re.comp ((measurable_g3bl hΨ left q).comp measurable_fst)
  cases left
  · simp only [g3bpre, Bool.false_eq_true, ite_false]
    refine Measurable.iSup fun q => Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.const _).inter (measurableSet_le (hre q) measurable_snd)
  · simp only [g3bpre, ite_true]
    refine Measurable.iInf fun q => Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.const _).inter (measurableSet_le measurable_snd (hre q))

/-- **The local maps are measurable in (path, point, variable).** -/
theorem measurable_g3locM (hΨ : ∀ left, Measurable fun p : (ℝ≥0 → ℝ) × ℂ => Ψ left p.1 p.2)
    (left : Bool) : Measurable (g3locM Ψ left) := by
  have hb : Measurable fun p : (ℝ≥0 → ℝ) × ℝ × ℂ => g3bpre Ψ left p.1 p.2.1 :=
    (measurable_g3bpre hΨ left).comp (f := fun p : (ℝ≥0 → ℝ) × ℝ × ℂ => (p.1, p.2.1))
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have harg : Measurable fun p : (ℝ≥0 → ℝ) × ℝ × ℂ =>
      (p.1, p.2.2 + (g3bpre Ψ left p.1 p.2.1 : ℂ)) :=
    have h2 : Measurable fun p : (ℝ≥0 → ℝ) × ℝ × ℂ => p.2.2 := measurable_snd.comp measurable_snd
    have h3 : Measurable fun p : (ℝ≥0 → ℝ) × ℝ × ℂ => (g3bpre Ψ left p.1 p.2.1 : ℂ) :=
      Complex.measurable_ofReal.comp hb
    measurable_fst.prodMk (h2.add h3)
  exact ((hΨ left).comp harg).sub
    (Complex.measurable_ofReal.comp (measurable_fst.comp measurable_snd))

/-! ## Identification on good paths -/

theorem tendsto_apx (q : ℝ) : Tendsto (apx q) atTop (𝓝[H] (q : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
  · have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => (q : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I) atTop
        (𝓝 ((q : ℂ) + ((0 : ℝ) : ℂ) * I)) :=
      tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto 0).comp h1 |>.mul_const I)
    have e : apx q = fun n : ℕ => (q : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I := rfl
    rw [e]; simpa using h2
  · show 0 < (apx q n).im
    simp only [apx, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero,
      add_zero, zero_add]
    positivity

theorem g3bl_eq {left : Bool} {a : ℝ≥0 → ℝ} {Φ : ℝ ≃o ℝ} (h : SideReflGood left (Ψ left a) Φ)
    {q : ℝ} (hq : q ∈ g1SideHalf left) : g3bl Ψ left a q = ((Φ q : ℝ) : ℂ) :=
  ((tendsto_of_reflGood h hq).comp (tendsto_apx q)).limUnder_eq

theorem g3bpre_eq {left : Bool} {a : ℝ≥0 → ℝ} {Φ : ℝ ≃o ℝ} (h : SideReflGood left (Ψ left a) Φ)
    {x : ℝ} (hx : x ∈ g1SideHalf left) : g3bpre Ψ left a x = Φ.symm x := by
  have hb : Φ.symm x ∈ g1SideHalf left := (mem_half_symm_iff h.1 left x).2 hx
  set b := Φ.symm x with hbdef
  have hΦb : Φ b = x := Φ.apply_symm_apply x
  cases left
  · -- right side: `g1SideHalf false = Ioi 0`
    have hb0 : 0 < b := by simpa [g1SideHalf] using hb
    have hcond : ∀ q : ℚ, (0 < (q : ℝ) ∧ (g3bl Ψ false a q).re ≤ x) ↔
        (0 < (q : ℝ) ∧ (q : ℝ) ≤ b) := fun q => by
      constructor
      · rintro ⟨h0, hle⟩
        rw [g3bl_eq h (by simpa [g1SideHalf] using h0), ofReal_re, ← hΦb] at hle
        exact ⟨h0, Φ.le_iff_le.1 hle⟩
      · rintro ⟨h0, hle⟩
        rw [g3bl_eq h (by simpa [g1SideHalf] using h0), ofReal_re, ← hΦb]
        exact ⟨h0, Φ.le_iff_le.2 hle⟩
    simp only [g3bpre, Bool.false_eq_true, ite_false]
    simp_rw [hcond]
    have hle : ∀ q : ℚ, (if 0 < (q : ℝ) ∧ (q : ℝ) ≤ b then (q : ℝ) else 0) ≤ b := fun q => by
      split_ifs with hc
      · exact hc.2
      · exact hb0.le
    have hbdd : BddAbove (range fun q : ℚ => if 0 < (q : ℝ) ∧ (q : ℝ) ≤ b then (q : ℝ) else 0) :=
      ⟨b, by rintro _ ⟨q, rfl⟩; exact hle q⟩
    refine le_antisymm (ciSup_le hle) (le_of_forall_lt fun r hr => ?_)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (max_lt hr hb0)
    have hc : 0 < (q : ℝ) ∧ (q : ℝ) ≤ b := ⟨(le_max_right _ _).trans_lt hq1, hq2.le⟩
    calc r < q := (le_max_left _ _).trans_lt hq1
      _ = (if 0 < (q : ℝ) ∧ (q : ℝ) ≤ b then (q : ℝ) else 0) := by rw [if_pos hc]
      _ ≤ _ := le_ciSup hbdd q
  · -- left side: `g1SideHalf true = Iio 0`
    have hb0 : b < 0 := by simpa [g1SideHalf] using hb
    have hcond : ∀ q : ℚ, ((q : ℝ) < 0 ∧ x ≤ (g3bl Ψ true a q).re) ↔
        ((q : ℝ) < 0 ∧ b ≤ (q : ℝ)) := fun q => by
      constructor
      · rintro ⟨h0, hle⟩
        rw [g3bl_eq h (by simpa [g1SideHalf] using h0), ofReal_re, ← hΦb] at hle
        exact ⟨h0, Φ.le_iff_le.1 hle⟩
      · rintro ⟨h0, hle⟩
        rw [g3bl_eq h (by simpa [g1SideHalf] using h0), ofReal_re, ← hΦb]
        exact ⟨h0, Φ.le_iff_le.2 hle⟩
    simp only [g3bpre, ite_true]
    simp_rw [hcond]
    have hle : ∀ q : ℚ, b ≤ (if (q : ℝ) < 0 ∧ b ≤ (q : ℝ) then (q : ℝ) else 0) := fun q => by
      split_ifs with hc
      · exact hc.2
      · exact hb0.le
    have hbdd : BddBelow (range fun q : ℚ => if (q : ℝ) < 0 ∧ b ≤ (q : ℝ) then (q : ℝ) else 0) :=
      ⟨b, by rintro _ ⟨q, rfl⟩; exact hle q⟩
    refine le_antisymm (le_of_forall_gt fun r hr => ?_) (le_ciInf hle)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min hr hb0)
    have hc : (q : ℝ) < 0 ∧ b ≤ (q : ℝ) := ⟨hq2.trans_le (min_le_right _ _), hq1.le⟩
    calc _ ≤ (if (q : ℝ) < 0 ∧ b ≤ (q : ℝ) then (q : ℝ) else 0) := ciInf_le hbdd q
      _ = q := by rw [if_pos hc]
      _ < r := hq2.trans_le (min_le_left _ _)

/-- Uniqueness of normalized uniformizers of a side domain up to a positive dilation. -/
theorem side_unique {η : ℝ → ℂ} (hη : IsSimpleChord η) {left : Bool} {φ₁ φ₂ : ℂ → ℂ}
    (h₁ : IsNormalizedUniformizer (sideDom η left) φ₁)
    (h₂ : IsNormalizedUniformizer (sideDom η left) φ₂) :
    ∃ c : ℝ, 0 < c ∧ EqOn φ₂ (fun z => (c : ℂ) * φ₁ z) (sideDom η left) := by
  cases left
  · exact CA.Uniformizer.normalizedUniformizer_unique_rightComponent hη h₁ h₂
  · exact CA.Uniformizer.normalizedUniformizer_unique_leftComponent hη h₁ h₂

/-- Inverse uniformizers of dilated uniformizers are precomposed with the inverse dilation. -/
theorem invFunOn_dilate {D : Set ℂ} {φ₁ φ₂ : ℂ → ℂ} (h₁ : IsNormalizedUniformizer D φ₁)
    (h₂ : IsNormalizedUniformizer D φ₂) {c : ℝ} (hc : 0 < c)
    (hEq : EqOn φ₂ (fun z => (c : ℂ) * φ₁ z) D) (z : ℂ) :
    invFunOn φ₂ D z = invFunOn φ₁ D (z / c) := by
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  by_cases hz : z ∈ H
  · have hzc : z / c ∈ H := by
      show 0 < (z / (c : ℂ)).im
      rw [div_ofReal_im]; exact div_pos hz hc
    obtain ⟨u, hu, hφu⟩ := h₁.1.surjOn hzc
    have hl := h₁.1.injOn.leftInvOn_invFunOn hu
    have h2u : φ₂ u = z := by rw [hEq hu]; simp only; rw [hφu]; field_simp
    rw [← h2u, h₂.1.injOn.leftInvOn_invFunOn hu, h2u, ← hφu, hl]
  · have hzc : z / c ∉ H := by
      intro h; apply hz
      have : 0 < (z / (c : ℂ)).im := h
      rw [div_ofReal_im] at this
      exact (div_pos_iff_of_pos_right hc).1 this
    rw [invFunOn_neg (fun ⟨u, hu, e⟩ => hz (e ▸ h₂.1.mapsTo hu)),
      invFunOn_neg (fun ⟨u, hu, e⟩ => hzc (e ▸ h₁.1.mapsTo hu))]

/-- **Identification on good paths**: the chosen local maps are the measurable ones precomposed
with a dilation `w ↦ c w`, `c > 0` depending on the path only. -/
theorem g1zLocMap_eq_g3locM {γ : ℝ} (hsel : G1PsiSel γ Ψ) {a : ℝ≥0 → ℝ} (hac : Continuous a)
    (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool)
    (hN : IsNormalizedUniformizer (sideDom (pathTrace (γ ^ 2) a) left)
      (uniformizer (sideDom (pathTrace (γ ^ 2) a) left))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ g1SideHalf left, ∀ w : ℂ,
      g1zLocMap left (pathDrive (γ ^ 2) a) x w = g3locM Ψ left (a, x, (c : ℂ) * w) := by
  obtain ⟨φ, hφ, hΨa⟩ := hsel.2.2 a hac hs left
  obtain ⟨c, hc, hEq⟩ := side_unique hs hN hφ
  have hdil : ∀ z, Ψ left a z = g1zSideMap left (pathDrive (γ ^ 2) a) (z / c) := fun z => by
    rw [hΨa]; exact invFunOn_dilate hN hφ hc hEq z
  obtain ⟨Φ₀, h₀⟩ := G1Z2.sideReflChordStmt_holds _ hs left _ hN
  obtain ⟨Φ₁, h₁⟩ := G1Z2.sideReflChordStmt_holds _ hs left _ hφ
  have h₀' : SideReflGood left (g1zSideMap left (pathDrive (γ ^ 2) a)) Φ₀ := h₀
  have h₁' : SideReflGood left (Ψ left a) Φ₁ := by rw [hΨa]; exact h₁
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  refine ⟨c, hc, fun x hx w => ?_⟩
  have hb₀ : Φ₀.symm x ∈ g1SideHalf left := (mem_half_symm_iff h₀'.1 left x).2 hx
  have hcb : c * Φ₀.symm x ∈ g1SideHalf left := by
    cases left
    · have h' : 0 < Φ₀.symm x := by simpa [g1SideHalf] using hb₀
      simpa [g1SideHalf] using mul_pos hc h'
    · have h' : Φ₀.symm x < 0 := by simpa [g1SideHalf] using hb₀
      simpa [g1SideHalf] using mul_neg_of_pos_of_neg hc h'
  have hT1 := tendsto_of_reflGood h₁' hcb
  have hmap : Tendsto (fun z : ℂ => z / c) (𝓝[H] ((c * Φ₀.symm x : ℝ) : ℂ))
      (𝓝[H] ((Φ₀.symm x : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun z hz => ?_⟩
    · have e : ((Φ₀.symm x : ℝ) : ℂ) = ((c * Φ₀.symm x : ℝ) : ℂ) / c := by
        push_cast; field_simp
      rw [e]
      exact ((continuous_id.div_const _).tendsto _).mono_left nhdsWithin_le_nhds
    · show 0 < (z / (c : ℂ)).im
      rw [div_ofReal_im]; exact div_pos hz hc
  have hT2 : Tendsto (Ψ left a) (𝓝[H] ((c * Φ₀.symm x : ℝ) : ℂ)) (𝓝 ((x : ℝ) : ℂ)) := by
    have h := (tendsto_of_reflGood h₀' hb₀).comp hmap
    rw [OrderIso.apply_symm_apply] at h
    exact h.congr fun z => (hdil z).symm
  have := neBot_nhdsWithin_H (c * Φ₀.symm x)
  have hx1 : Φ₁ (c * Φ₀.symm x) = x := ofReal_injective (tendsto_nhds_unique hT1 hT2)
  have hpre : g3bpre Ψ left a x = c * Φ₀.symm x := by
    rw [g3bpre_eq h₁' hx]; exact Φ₁.symm_apply_eq.2 hx1.symm
  simp only [g1zLocMap, g3locM, hpre, g1zBdryPre_eq h₀' hx, hdil]
  congr 2
  push_cast
  field_simp

end G3Z2b2

end Thm18Asm
end QuantumZipper

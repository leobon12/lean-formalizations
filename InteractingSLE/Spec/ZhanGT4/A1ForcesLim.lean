/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkCanon
import InteractingSLE.Spec.ZhanGT4.A1MultiMarkRecord

/-!
# Zhan's A.1 (R80): measurable canonical image forces of frozen-chart marks

Packet PROVE-A1-FORCES. A1-FROZEN's families ask for image force points jointly measurable in the frozen time and the
sample (`FrozenFamily(Fst).measurable_VL`), and A1-FAMILY's `FamilyRect(Fst).ofRect` for force points that agree before
the cap with record-measurable functions (`hgVL`, `hgVR`). PROVE-A1-MULTIMARK's canonical force `rFrzFst` reads the
forward map `g̃_u(p)` of the canonical image driver at a real mark `p`; that value is a junk `0` once `p` is swallowed
and the canonical driver is only continuous before the image lifetime, so no measurability of `rFrzFst` itself is
available. Here:

* `fwdRe W t p`: the real-point forward map **through approximation from `ℍ`**, the limit of `Re g_t(p + i/(n+1))`;
  **`fwdRe_eq`**: it is `Re g_t(p)` when `p` is alive at `t` (`RS.tendsto_fwdMap_of_sol`, uniqueness of the real
  solution `F1.fwdMap_eq_of_isForwardSol`); **`measurable_fwdRe`**: it is measurable for any family of continuous
  drivers with measurable evaluations (A1-MARG's `measurable_fwd_prod` at the points `p + i/(n+1) ∈ ℍ`, Mathlib's
  `StronglyMeasurable.limUnder`), with no condition on the swallowed samples;
* `canonForce`: the canonical image force at a mark `p`, read through `fwdRe` of the canonical driver stopped at the
  image time, masked by the live event and by the image time being before the canonical image lifetime;
  **`CanonHyp.measurable_canonForce`**: it is measurable under A1-MARG's standing hypotheses `CanonHyp`;
  **`canonForce_eq_imgForce`**: it is PROVE-A1-MULTIMARK's `imgForce` whenever the mark is alive.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Forces

open QuantumZipper (H IsForwardSol fwdMap)
open A2X A1Ref A1Marg A1MultiMark

/-! ### The real-point forward map through approximation from `ℍ` -/

/-- The approximating points `p + i/(n+1) ∈ ℍ` of a real point `p`. -/
def approxPt (p : ℝ) (n : ℕ) : ℂ := (p : ℂ) + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * I

/-- **The real-point forward map through approximation from `ℍ`**: the limit of `Re g_t(p + i/(n+1))` (a junk value
if the limit does not exist). -/
def fwdRe (W : ℝ → ℝ) (t p : ℝ) : ℝ := limUnder atTop fun n : ℕ => (fwdMap W t (approxPt p n)).re

theorem approxPt_mem_H (p : ℝ) (n : ℕ) : approxPt p n ∈ H := by
  show 0 < (approxPt p n).im
  simp only [approxPt, add_im, ofReal_im, mul_im, I_re, mul_zero, ofReal_re, I_im, mul_one, zero_add]
  positivity

theorem tendsto_approxPt (p : ℝ) : Tendsto (approxPt p) atTop (𝓝[H] (p : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (approxPt_mem_H p)⟩
  have h1 : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ)) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 := (tendsto_const_nhds (x := (p : ℂ))).add (h1.mul_const I)
  rw [ofReal_zero, zero_mul, add_zero] at h2
  exact h2

/-- **The approximation recovers the real-point forward map at an alive mark.** -/
theorem fwdRe_eq {W : ℝ → ℝ} (hW : Continuous W) {t p : ℝ} (ht : 0 ≤ t) {v : ℝ → ℂ}
    (hv : IsForwardSol W (p : ℂ) t v) : fwdRe W t p = (fwdMap W t p).re := by
  have h := (QuantumZipper.RS.tendsto_fwdMap_of_sol hW ht hv).comp (tendsto_approxPt p)
  rw [← QuantumZipper.F1.fwdMap_eq_of_isForwardSol hv ⟨ht, le_rfl⟩] at h
  exact ((Complex.continuous_re.tendsto _).comp h).limUnder_eq

/-- At a stop `t` of a driver continuous on `[0, t]`, the approximation of the stopped driver recovers the forward map
of the driver at an alive mark. -/
theorem fwdRe_stopDrv_eq {w : ℝ → ℝ} {t p : ℝ} (hc : ContinuousOn w (Icc 0 t)) (ht : 0 ≤ t) {v : ℝ → ℂ}
    (hv : IsForwardSol w (p : ℂ) t v) : fwdRe (stopDrv w t) t p = (fwdMap w t p).re := by
  have e : ∀ r ∈ Icc (0 : ℝ) t, w r = stopDrv w t r := fun r hr => (stopDrv_eqOn w t hr).symm
  rw [fwdRe_eq (continuous_stopDrv hc ht) ht (QuantumZipper.isForwardSol_congr_drive e hv),
    Ito.fwdMap_congr_of_eqOn_of_le (stopDrv_eqOn w t) le_rfl]

section Family

variable {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℝ → ℝ}

/-- **The forward map of a family of continuous drivers at measurable points of `ℍ` is measurable** (the junk value of
a swallowed point is `0`, so A1-MARG's masked joint map is the map itself). -/
theorem measurable_fwdMap_of_mem_H (hDc : ∀ ω, Continuous (D ω)) {t : ℝ} (ht : 0 ≤ t)
    (hDm : ∀ r ∈ Icc (0 : ℝ) t, Measurable fun ω => D ω r) {q : Ω → ℂ} (hq : Measurable q)
    (hqH : ∀ ω, q ω ∈ H) : Measurable fun ω => fwdMap (D ω) t (q ω) := by
  have e : (fun ω => fwdMap (D ω) t (q ω)) = ({p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 t u}.indicator
      fun p => fwdMap (D p.2) t p.1) ∘ fun ω => (q ω, ω) := by
    funext ω
    simp only [Function.comp_apply]
    by_cases ha : ∃ u, IsForwardSol (D ω) (q ω) t u
    · rw [indicator_of_mem (show (q ω, ω) ∈ {p : ℂ × Ω | p.1 ∈ H ∧ ∃ u, IsForwardSol (D p.2) p.1 t u} from
        ⟨hqH ω, ha⟩)]
    · rw [indicator_of_notMem (fun h => ha h.2), QuantumZipper.fwdMap, dite_eq_right ha]
  rw [e]
  exact (measurable_fwd_prod hDc ht hDm).comp (hq.prodMk measurable_id)

/-- **The real-point forward map through approximation is measurable** for a family of continuous drivers with
measurable evaluations and a measurable mark, at every sample (no aliveness needed). -/
theorem measurable_fwdRe (hDc : ∀ ω, Continuous (D ω)) {t : ℝ} (ht : 0 ≤ t)
    (hDm : ∀ r ∈ Icc (0 : ℝ) t, Measurable fun ω => D ω r) {p : Ω → ℝ} (hp : Measurable p) :
    Measurable fun ω => fwdRe (D ω) t (p ω) := by
  have hq : ∀ n : ℕ, Measurable fun ω => approxPt (p ω) n := fun n =>
    (Complex.measurable_ofReal.comp hp).add measurable_const
  exact (StronglyMeasurable.limUnder fun n => (Complex.measurable_re.comp (measurable_fwdMap_of_mem_H hDc ht hDm
    (hq n) fun ω => approxPt_mem_H (p ω) n)).stronglyMeasurable).measurable

end Family

/-! ### The canonical image force of a mark, masked -/

section Canon

variable {Ω : Type*} [MeasurableSpace Ω]

open scoped Classical in
/-- **The canonical image force of the mark `p ω`** at image time `t` (frozen time `τ ω`): `g̃_t(p) + W̃_t − W̃_0` for
the canonical image driver `W̃` stopped at `t`, the forward map read through `fwdRe`; `0` off the live event and once
`t` reaches the canonical image lifetime. -/
def canonForce (L : Set Ω) (xj xk : ℝ) (wj : Ω → ℝ≥0 → ℝ) (ζj : Ω → ℝ≥0∞) (wk : Ω → ℝ≥0 → ℝ) (τ : Ω → ℝ≥0)
    (p : Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ L ∧ ENNReal.ofReal t < imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) then
    fwdRe (stopDrv (imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω)) t) t (p ω) +
      imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) t -
      imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0
  else 0

/-- The canonical driver is continuous on `[0, t]` before the canonical image lifetime. -/
theorem continuousOn_imgDrv_Icc {xj xk : ℝ} {wj wk : ℝ → ℝ} {ζj : ℝ≥0∞} {τ : ℝ}
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj → ContinuousOn wj (Icc 0 T)) (hj0 : wj 0 = 0)
    (hk : ∃ τ', τ < τ' ∧ ContinuousOn wk (Icc 0 τ')) (hk0 : wk 0 = 0) (hτ : 0 ≤ τ) {t : ℝ}
    (ht : ENNReal.ofReal t < imgLife xj wj ζj xk wk τ) : ContinuousOn (imgDrv xj wj ζj xk wk τ) (Icc 0 t) :=
  (continuousOn_imgDrv hj hj0 hk hk0 hτ).mono fun _ hs =>
    ⟨hs.1, (ENNReal.ofReal_le_ofReal hs.2).trans_lt ht⟩

omit [MeasurableSpace Ω] in
/-- **The masked canonical force is A1-MULTIMARK's `imgForce`** at a live sample, before the image lifetime, when the
mark is alive at `t` under the canonical driver. -/
theorem canonForce_eq_imgForce {L : Set Ω} {xj xk : ℝ} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ}
    {τ : Ω → ℝ≥0} {p : Ω → ℝ} {t : ℝ≥0} {ω : Ω} (hω : ω ∈ L)
    (hj : ∀ T : ℝ, ENNReal.ofReal T < ζj ω → ContinuousOn (Strip.extPath (wj ω)) (Icc 0 T))
    (hj0 : Strip.extPath (wj ω) 0 = 0)
    (hk : ∃ τ' : ℝ, (τ ω : ℝ) < τ' ∧ ContinuousOn (Strip.extPath (wk ω)) (Icc 0 τ'))
    (hk0 : Strip.extPath (wk ω) 0 = 0)
    (ht : ENNReal.ofReal t < imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
    {v : ℝ → ℂ} (hv : IsForwardSol (imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω))
      (p ω : ℂ) t v) :
    canonForce L xj xk wj ζj wk τ p t ω =
      imgForce xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) (p ω) t := by
  rw [canonForce, ite_eq_left ⟨hω, ht⟩, imgForce,
    fwdRe_stopDrv_eq (continuousOn_imgDrv_Icc hj hj0 hk hk0 (τ ω).coe_nonneg ht) t.coe_nonneg hv]

section CanonHyp

variable {L : Set Ω} {wj : Ω → ℝ≥0 → ℝ} {ζj : Ω → ℝ≥0∞} {wk : Ω → ℝ≥0 → ℝ} {ζk : Ω → ℝ≥0∞} {τ : Ω → ℝ≥0}

/-- **The masked canonical force of a measurable mark is measurable** under A1-MARG's standing hypotheses. -/
theorem _root_.InteractingSLE.ZhanGT4.A1Marg.CanonHyp.measurable_canonForce (hC : CanonHyp L wj ζj wk ζk τ)
    (xj xk : ℝ) {p : Ω → ℝ} (hp : Measurable p)
    (t : ℝ≥0) : Measurable (canonForce L xj xk wj ζj wk τ p t) := by
  classical
  set E : Set Ω := L ∩ {ω | ENNReal.ofReal t < L.indicator (fun ω => imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk
    (Strip.extPath (wk ω)) (τ ω)) ω} with hE
  have hEm : MeasurableSet E :=
    hC.meas.inter (measurableSet_lt measurable_const (hC.measurable_canonImgLife xj xk))
  have hEiff : ∀ ω, ω ∈ E ↔ ω ∈ L ∧ ENNReal.ofReal t < imgLife xj (Strip.extPath (wj ω)) (ζj ω) xk
      (Strip.extPath (wk ω)) (τ ω) := fun ω => by
    constructor
    · rintro ⟨hL, h⟩
      rw [mem_ofPred_eq, indicator_of_mem hL] at h
      exact ⟨hL, h⟩
    · rintro ⟨hL, h⟩
      refine ⟨hL, ?_⟩
      rw [mem_ofPred_eq, indicator_of_mem hL]
      exact h
  set D : Ω → ℝ → ℝ := fun ω => if ω ∈ E then stopDrv (imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk
    (Strip.extPath (wk ω)) (τ ω)) t else fun _ => 0 with hD
  have hDc : ∀ ω, Continuous (D ω) := fun ω => by
    by_cases h : ω ∈ E
    · simp only [hD, h, ↓reduceIte]
      obtain ⟨hL, hlt⟩ := (hEiff ω).1 h
      exact continuous_stopDrv (continuousOn_imgDrv_Icc (hC.regj ω) (hC.regj0 ω) (hC.regk hL) (hC.regk0 ω)
        (τ ω).coe_nonneg hlt) t.coe_nonneg
    · simp only [hD, h, ↓reduceIte]; exact continuous_const
  have hDm : ∀ r ∈ Icc (0 : ℝ) t, Measurable fun ω => D ω r := fun r _ => by
    have e : (fun ω => D ω r) = E.indicator (L.indicator fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk
        (Strip.extPath (wk ω)) (τ ω) (max 0 (min r t))) := by
      funext ω
      by_cases h : ω ∈ E
      · simp only [hD, h, ↓reduceIte, indicator_of_mem h, indicator_of_mem h.1, stopDrv]
      · simp only [hD, h, ↓reduceIte, indicator_of_notMem h]
    rw [e]
    exact (hC.measurable_imgDrv_at xj xk (le_max_left _ _)).indicator hEm
  have e : canonForce L xj xk wj ζj wk τ p t = E.indicator fun ω => fwdRe (D ω) t (p ω) +
      L.indicator (fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) t) ω -
      L.indicator (fun ω => imgDrv xj (Strip.extPath (wj ω)) (ζj ω) xk (Strip.extPath (wk ω)) (τ ω) 0) ω := by
    funext ω
    by_cases h : ω ∈ E
    · rw [indicator_of_mem h, indicator_of_mem h.1, indicator_of_mem h.1, canonForce, ite_eq_left ((hEiff ω).1 h)]
      simp only [hD, h, ↓reduceIte]
    · rw [indicator_of_notMem h, canonForce, ite_eq_right fun h' => h ((hEiff ω).2 h')]
  rw [e]
  exact (((measurable_fwdRe hDc t.coe_nonneg hDm hp).add (hC.measurable_imgDrv_at xj xk t.coe_nonneg)).sub
    (hC.measurable_imgDrv_at xj xk le_rfl)).indicator hEm

end CanonHyp

end Canon

end InteractingSLE.ZhanGT4.A1Forces

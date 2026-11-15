/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SvVer

/-!
# GW2's stage identity: capping an announced GB6 version at a second path rule

Packet PROVE-GW2-RELDET, ruling R106. A stage version stops at the end of the current piece. If the stop of the
explored curve's relative exploration is a path rule `ρ'` of the record and of the relative driver, the version can be
capped there. Typical caps are the relative clock of a physical time (JOINTDET's `physicalCapacityStop`, `GW2SxTime`)
or a death time.

* `isPathRule_min`: the minimum of two path rules is a path rule.
* `ruleCapStop`: the capped stop `min(V, ρ'(record, R))`.
* `ruleCapDrv`: `R` frozen at the capped stop.
* `isGB6RelVersionA_ruleCap`: for an announced R-form version `(R, V)`, the capped pair is again an announced
  R-form version. The cap must be positive on the interior-tip event. On the record event it must be announced
  (by any measurable monotone path rules) where it lies below `V`, and the announcing supremum must agree with it
  below `V`. Above `V` the frozen driver carries no information, so nothing is asked there. Finiteness comes from
  the version's own announcement.
  Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8 Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId

/-! ### Path rules -/

/-- A path rule evaluated at a path agreeing with `w` up to a level below its value stays above that level. -/
theorem le_pathRule_of_agree {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) {r : RecData}
    {w w' : ℝ≥0 → ℝ} {m : ℝ≥0∞} (hm : m ≤ ρ (r, w)) (hag : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ m → w u = w' u) :
    m ≤ ρ (r, w') := by
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have e : ρ (r, w) = ρ (r, w') := hρ r w' w fun u hu => (hag u (hu.trans hlt.le)).symm
  rw [← e] at hlt
  exact absurd hm (not_le.2 hlt)

/-- **The minimum of two path rules is a path rule.** -/
theorem isPathRule_min {ρ ρ' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (hρ' : IsPathRule ρ') :
    IsPathRule fun x => min (ρ x) (ρ' x) := by
  intro r w w' hag
  simp only at hag ⊢
  have h1 := le_pathRule_of_agree hρ (min_le_left _ _) hag
  have h2 := le_pathRule_of_agree hρ' (min_le_right _ _) hag
  rcases le_total (ρ (r, w)) (ρ' (r, w)) with h | h
  · have e : ρ (r, w') = ρ (r, w) := hρ r w w' fun u hu => hag u (by rw [min_eq_left h]; exact hu)
    rw [min_eq_left h] at h2
    rw [e, min_eq_left h, min_eq_left h2]
  · have e : ρ' (r, w') = ρ' (r, w) := hρ' r w w' fun u hu => hag u (by rw [min_eq_right h]; exact hu)
    rw [min_eq_right h] at h1
    rw [e, min_eq_right h, min_eq_right h1]

/-- The stopping set of a path rule is determined up to `t`. -/
theorem isDetUpTo_pathRule_le {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ : IsPathRule ρ) (t : ℝ≥0) :
    IsDetUpTo t {x : RecData × (ℝ≥0 → ℝ) | ρ x ≤ (t : ℝ≥0∞)} := by
  intro r w w' hww'
  simp only [mem_ofPred_eq]
  constructor
  · intro h
    rw [hρ r w w' fun u hu => hww' u (ENNReal.coe_le_coe.1 (hu.trans h))]
    exact h
  · intro h
    rw [hρ r w' w fun u hu => (hww' u (ENNReal.coe_le_coe.1 (hu.trans h))).symm]
    exact h

/-! ### The capped stop and the capped driver -/

section Cap

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The stop `V` capped at the path rule `ρ'` of the record and of the relative driver. -/
def ruleCapStop (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ρ' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  min (V ω) (ρ' (gb6Rec s Wα ζα ω, fun u => R u ω))

/-- The driver `R` frozen at the time `v` (unchanged where `v = ⊤`). -/
def ruleCapDrv (R : ℝ≥0 → Ω → ℝ) (v : Ω → ℝ≥0∞) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if v ω = ⊤ then R t ω else R (min t (v ω).toNNReal) ω

theorem ruleCapDrv_of_le {R : ℝ≥0 → Ω → ℝ} {v : Ω → ℝ≥0∞} {t : ℝ≥0} {ω : Ω} (ht : (t : ℝ≥0∞) ≤ v ω) :
    ruleCapDrv R v t ω = R t ω := by
  by_cases hv : v ω = ⊤
  · simp only [ruleCapDrv, hv, ↓reduceIte]
  · simp only [ruleCapDrv, hv, ↓reduceIte, min_eq_left (ENNReal.le_toNNReal_of_coe_le ht hv)]

theorem ruleCapDrv_after {R : ℝ≥0 → Ω → ℝ} {v : Ω → ℝ≥0∞} {t : ℝ≥0} {ω : Ω} (ht : v ω ≤ t) :
    ruleCapDrv R v t ω = ruleCapDrv R v (v ω).toNNReal ω := by
  have hv : v ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top ht
  have hle : (v ω).toNNReal ≤ t := by
    simpa only [ENNReal.toNNReal_coe] using ENNReal.toNNReal_mono ENNReal.coe_ne_top ht
  simp only [ruleCapDrv, hv, ↓reduceIte, min_self, min_eq_right hle]

theorem ruleCapDrv_zero {R : ℝ≥0 → Ω → ℝ} (hR0 : ∀ ω, R 0 ω = 0) (v : Ω → ℝ≥0∞) (ω : Ω) :
    ruleCapDrv R v 0 ω = 0 := by
  by_cases hv : v ω = ⊤
  · simp only [ruleCapDrv, hv, ↓reduceIte, hR0]
  · simp only [ruleCapDrv, hv, ↓reduceIte, zero_min, hR0]

theorem continuous_ruleCapDrv {R : ℝ≥0 → Ω → ℝ} (hRc : ∀ ω, Continuous fun t => R t ω) (v : Ω → ℝ≥0∞)
    (ω : Ω) : Continuous fun t => ruleCapDrv R v t ω := by
  by_cases hv : v ω = ⊤
  · simp only [ruleCapDrv, hv, ↓reduceIte]
    exact hRc ω
  · simp only [ruleCapDrv, hv, ↓reduceIte]
    exact (hRc ω).comp (continuous_id.min continuous_const)

theorem measurable_ruleCapDrv {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t))
    (hRc : ∀ ω, Continuous fun t => R t ω) {v : Ω → ℝ≥0∞} (hv : Measurable v) (t : ℝ≥0) :
    Measurable (ruleCapDrv R v t) := by
  have hA : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) (fun _ => (⊤ : ℝ≥0∞)) R := by
    intro t A hA
    have e : {ω | (t : ℝ≥0∞) < (fun _ => (⊤ : ℝ≥0∞)) ω ∧ R t ω ∈ A} = R t ⁻¹' A := by
      ext ω
      simp only [mem_ofPred_eq, ENNReal.coe_lt_top, true_and, mem_preimage]
    rw [e]
    exact (hRm t) hA
  have hf : Measurable (Version.freeze R (fun ω => (v ω).toNNReal) t) :=
    Version.measurable_freeze hA (fun ω => (hRc ω).continuousOn) hv.ennreal_toNNReal
      (fun _ => ENNReal.coe_lt_top) t
  exact Measurable.ite (hv (measurableSet_singleton ⊤)) (hRm t) hf

/-- Agreement of the capped driver with the original one up to the cap. -/
theorem ruleCapDrv_agree {R : ℝ≥0 → Ω → ℝ} {v : Ω → ℝ≥0∞} (ω : Ω) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ v ω → R u ω = ruleCapDrv R v u ω :=
  fun _ hu => (ruleCapDrv_of_le hu).symm

/-- Hulls of continuous drivers agreeing on `[0, max a 0]` agree at `a`. -/
theorem fwdHull_eq_of_agree {w w' : ℝ≥0 → ℝ} (hw : Continuous w) (hw' : Continuous w') {a : ℝ}
    (h : ∀ u : ℝ≥0, (u : ℝ) ≤ max a 0 → w u = w' u) :
    QuantumZipper.fwdHull (fun r : ℝ => w r.toNNReal) a = QuantumZipper.fwdHull (fun r : ℝ => w' r.toNNReal) a := by
  have hmax : ∀ f : ℝ → ℝ, QuantumZipper.fwdHull f a = QuantumZipper.fwdHull f (max a 0) := by
    intro f
    rcases le_total a 0 with ha | ha
    · simp only [QuantumZipper.fwdHull, max_eq_right ha, ENNReal.ofReal_of_nonpos ha, ENNReal.ofReal_zero]
    · rw [max_eq_left ha]
  rw [hmax, hmax]
  apply YuanCorollary13.fwdHull_eq_of_eqOn_Icc (hw.comp continuous_real_toNNReal)
    (hw'.comp continuous_real_toNNReal) (le_max_right a 0)
  intro r hr
  exact h r.toNNReal (by rw [Real.coe_toNNReal r hr.1]; exact hr.2)

/-- **Capping an announced GB6 version at an announced positive path rule.** -/
theorem isGB6RelVersionA_ruleCap {P : Measure Ω} {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞}
    {γ α : Ω → ℝ≥0 → ℂ} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hver : Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α R V) (hrecm : Measurable (gb6Rec s Wα ζα))
    {ρ' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρ'm : Measurable ρ') (hρ' : IsPathRule ρ')
    (hpos : ∀ᵐ ω ∂P, (s : ℝ≥0∞) < ζα ω → α ω s ∈ H → 0 < ρ' (gb6Rec s Wα ζα ω, fun u => R u ω))
    {ρa : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρam : ∀ n, Measurable (ρa n)) (hρa : ∀ n, IsPathRule (ρa n))
    (hρamono : ∀ x, Monotone fun n => ρa n x)
    (hann : ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s →
      (ρ' (gb6Rec s Wα ζα ω, fun u => R u ω) < V ω →
        ∀ n, ρa n (gb6Rec s Wα ζα ω, fun u => R u ω) < ρ' (gb6Rec s Wα ζα ω, fun u => R u ω)) ∧
        min (V ω) (⨆ n, ρa n (gb6Rec s Wα ζα ω, fun u => R u ω)) =
          min (V ω) (ρ' (gb6Rec s Wα ζα ω, fun u => R u ω))) :
    Q3Stop.IsGB6RelVersionA s P W Wα ζα γ α (ruleCapDrv R (ruleCapStop s Wα ζα ρ' R V))
      (ruleCapStop s Wα ζα ρ' R V) := by
  obtain ⟨⟨⟨hRm, hRc, hR0, -, hVm, -, hae⟩, ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hannV⟩ := hver
  set V' := ruleCapStop s Wα ζα ρ' R V with hV'def
  set R' := ruleCapDrv R V' with hR'def
  have hRpm : Measurable fun ω => (gb6Rec s Wα ζα ω, fun u => R u ω) :=
    hrecm.prodMk (measurable_pi_iff.mpr hRm)
  have hV'm : Measurable V' := hVm.min (hρ'm.comp hRpm)
  have hR'm : ∀ t, Measurable (R' t) := measurable_ruleCapDrv hRm hRc hV'm
  have hR'pm : Measurable fun ω => (gb6Rec s Wα ζα ω, fun u => R' u ω) :=
    hrecm.prodMk (measurable_pi_iff.mpr hR'm)
  -- the capped rule
  set ρ'' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ := fun x => min (ρ x) (ρ' x) with hρ''def
  have hρ''m : Measurable ρ'' := hρm.min hρ'm
  have hρ'' : IsPathRule ρ'' := isPathRule_min hρ hρ'
  have hV'ρ : ∀ᵐ ω ∂P, V' ω = ρ'' (gb6Rec s Wα ζα ω, fun u => R' u ω) := by
    filter_upwards [hVρ] with ω hω
    have e1 : V' ω = ρ'' (gb6Rec s Wα ζα ω, fun u => R u ω) := by
      simp only [hV'def, ruleCapStop, hρ''def, hω]
    rw [e1]
    exact (hρ'' _ _ _ fun u hu => ruleCapDrv_agree ω u (e1 ▸ hu)).symm
  refine ⟨⟨⟨hR'm, continuous_ruleCapDrv hRc V', ruleCapDrv_zero hR0 V', fun ω t ht => ruleCapDrv_after ht,
    hV'm, fun t => ⟨_, measurableSet_le hρ''m measurable_const, isDetUpTo_pathRule_le hρ'' t, ?_⟩, ?_⟩,
    ρ'', hρ''m, hρ'', hV'ρ⟩, fun n x => min (ρs n x) (ρa n x), fun n => (hρsm n).min (hρam n),
    fun n => isPathRule_min (hρs n) (hρa n), fun n x => ne_top_of_le_ne_top (hρsfin n x) (min_le_left _ _),
    fun x => fun n m hnm => min_le_min (hρsmono x hnm) (hρamono x hnm), ?_⟩
  · -- the stopping sets
    filter_upwards [hV'ρ] with ω hω
    rw [hω]
  · -- positivity, coverage and the hull identity
    filter_upwards [hae, hpos] with ω hω hposω hs hsH
    obtain ⟨hV0, hcov, hhull⟩ := hω hs hsH
    refine ⟨lt_min hV0 (hposω hs hsH), fun u hu => hcov u (hu.trans_le (min_le_left _ _)), fun t ht hle => ?_⟩
    rw [← hhull t ht (hle.trans (min_le_left _ _))]
    refine (fwdHull_eq_of_agree (continuous_ruleCapDrv hRc V' ω) (hRc ω) fun u hu => ?_)
    refine (ruleCapDrv_agree ω u ?_).symm
    calc (u : ℝ≥0∞) = ENNReal.ofReal (u : ℝ) := (ENNReal.ofReal_coe_nnreal).symm
      _ ≤ ENNReal.ofReal (max (gb6Clock s W Wα ω t) 0) := ENNReal.ofReal_le_ofReal hu
      _ = ENNReal.ofReal (gb6Clock s W Wα ω t) := by
          rcases le_total (gb6Clock s W Wα ω t) 0 with h0 | h0
          · rw [max_eq_right h0, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h0]
          · rw [max_eq_left h0]
      _ ≤ V' ω := hle
  · -- the announcement
    filter_upwards [hannV, hann] with ω hVω hρ'ω hm
    obtain ⟨hlt, hsup⟩ := hVω hm
    obtain ⟨hlt', hsup'⟩ := hρ'ω hm
    have hV'e : V' ω = min (V ω) (ρ' (gb6Rec s Wα ζα ω, fun u => R u ω)) := rfl
    -- the announcing rules read the same at `R` and at `R'`
    have hlt'' : ∀ n, min (ρs n (gb6Rec s Wα ζα ω, fun u => R u ω)) (ρa n (gb6Rec s Wα ζα ω, fun u => R u ω)) <
        V' ω := fun n => by
      rw [hV'e]
      by_cases hρV : ρ' (gb6Rec s Wα ζα ω, fun u => R u ω) < V ω
      · rw [min_eq_right hρV.le]
        exact (min_le_right _ _).trans_lt (hlt' hρV n)
      · rw [min_eq_left (not_lt.1 hρV)]
        exact (min_le_left _ _).trans_lt (hlt n)
    have he : ∀ n, min (ρs n (gb6Rec s Wα ζα ω, fun u => R' u ω)) (ρa n (gb6Rec s Wα ζα ω, fun u => R' u ω)) =
        min (ρs n (gb6Rec s Wα ζα ω, fun u => R u ω)) (ρa n (gb6Rec s Wα ζα ω, fun u => R u ω)) := fun n =>
      isPathRule_min (hρs n) (hρa n) _ _ _ fun u hu => ruleCapDrv_agree ω u (hu.trans (hlt'' n).le)
    simp only [he]
    refine ⟨hlt'', ?_⟩
    have hsup'' := iSup_inf_of_monotone (f := fun n => ρs n (gb6Rec s Wα ζα ω, fun u => R u ω))
      (g := fun n => ρa n (gb6Rec s Wα ζα ω, fun u => R u ω)) (hρsmono _) (hρamono _)
    rw [hsup'', hsup, hsup', hV'e]

end Cap

end InteractingSLE.Theorem14.GW2Rd

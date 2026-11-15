/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseSel
import InteractingSLE.Spec.Sec7.CounterflowPhase

/-!
# §7.4, Aux. lemma 122: the phase-shifted boundary word and the constancy of the phase

Packet PROVE-STRIPSYS4. Specification §7.4.1, Aux. lemma 122 and its proof (`source/spec/p385-432.md` L103–L139,
pp. 389–391). At time `t` the exact boundary description of Aux. lemma 122 is the finite word of the force coordinates
with the newly exposed trace raised by one common `d_t`: in the centred coordinate the heights are those of
`forceBoundaryData k ρL ρR` (`−Λ`, `+Λ` on the two exposed sides) plus `d_t` on the exposed interval `(V⁻, V⁺)`
(`phaseData`).

* (PS9.2): subtracting a constant `c` from the field subtracts it from every height; with `c = 2πnχ = 2AnΛ` the result
  is the canonical word of the shifted seed weights `r_L + c/Λ`, `r_R − c/Λ` (`phaseData_sub_eq`,
  `isBoundedHarmonicExtension_shift`, `couplingMean_sub_const`).
* (PS9.1) and the constancy: the actual mean minus the canonical one is `d_t` times the harmonic measure of the exposed
  interval (`CounterflowPhase.eqOn_sub_eq_mul_phaseWindow`, landed); at a far point `iY` all three are continuous in
  `t`, so `d_t` is continuous on `(0, ∞)` with values in `2πχℤ`, hence constant (`phase_eq_of_pos`).

## Main definitions

* `phaseData k ρL ρR vL vR d`: the boundary heights of Aux. lemma 122 at one time;
* `shiftL k ρL c`, `shiftR k ρR c`: the seed weights shifted by a field constant `c` ((PS9.2) with `c = 2πnχ`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace PhaseSel

open Aux117 MartChar

/-! ### The phase-shifted word -/

section Data

variable {nL nR : ℕ}

/-- **The boundary heights of Aux. lemma 122 at one time** (centred coordinate): the word `ρ` of the force
coordinates `vL, vR` (seeds at index `0`), with the exposed interval `(vL 0, vR 0)` raised by the phase `d`. -/
def phaseData (k : ℝ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ) (vL : Fin (nL + 1) → ℝ)
    (vR : Fin (nR + 1) → ℝ) (d : ℝ) (x : ℝ) : ℝ :=
  forceBoundaryData k ρL ρR vL vR x + d * (Ioo (vL 0) (vR 0)).indicator 1 x

/-- The left seed weight shifted by the field constant `c`: `ρ^L_0 + c/Λ`, `Λ = π/√k` ((PS9.2): `r_L + 2An`). -/
def shiftL (k : ℝ) (ρL : Fin (nL + 1) → ℝ) (c : ℝ) : Fin (nL + 1) → ℝ :=
  Function.update ρL 0 (ρL 0 + c / (Real.pi / Real.sqrt k))

/-- The right seed weight shifted by the field constant `c`: `ρ^R_0 − c/Λ` ((PS9.2): `r_R − 2An`). -/
def shiftR (k : ℝ) (ρR : Fin (nR + 1) → ℝ) (c : ℝ) : Fin (nR + 1) → ℝ :=
  Function.update ρR 0 (ρR 0 - c / (Real.pi / Real.sqrt k))

theorem update_zero_add_eq {n : ℕ} (ρ : Fin (n + 1) → ℝ) (a : ℝ) :
    Function.update ρ 0 (ρ 0 + a) = fun i => ρ i + if i = 0 then a else 0 := by
  funext i
  by_cases hi : i = 0
  · subst hi; simp
  · simp [hi]

theorem sum_update_zero_add {n : ℕ} (ρ : Fin (n + 1) → ℝ) (a : ℝ) (s : Finset (Fin (n + 1))) :
    ∑ i ∈ s, Function.update ρ 0 (ρ 0 + a) i = (∑ i ∈ s, ρ i) + if (0 : Fin (n + 1)) ∈ s then a else 0 := by
  rw [update_zero_add_eq, Finset.sum_add_distrib, Finset.sum_ite_eq']

@[simp] theorem shiftL_zero (k : ℝ) (ρL : Fin (nL + 1) → ℝ) (c : ℝ) :
    shiftL k ρL c 0 = ρL 0 + c / (Real.pi / Real.sqrt k) := by simp [shiftL]

@[simp] theorem shiftR_zero (k : ℝ) (ρR : Fin (nR + 1) → ℝ) (c : ℝ) :
    shiftR k ρR c 0 = ρR 0 - c / (Real.pi / Real.sqrt k) := by simp [shiftR]

@[simp] theorem shiftL_zero_eq (k : ℝ) (ρL : Fin (nL + 1) → ℝ) : shiftL k ρL 0 = ρL := by
  simp [shiftL]

@[simp] theorem shiftR_zero_eq (k : ℝ) (ρR : Fin (nR + 1) → ℝ) : shiftR k ρR 0 = ρR := by
  simp [shiftR]

/-- **(PS9.2): subtracting `c` from the phase-shifted data gives the canonical word of the shifted seed weights**, off
the jump set, for seeds on their sides of the driver. -/
theorem phaseData_sub_eq {k : ℝ} (hk : 0 < k) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hvL : vL 0 ≤ 0) (hvR : 0 ≤ vR 0) (c : ℝ) {x : ℝ}
    (hx : x ∉ forceJumpSet vL vR) :
    phaseData k ρL ρR vL vR c x - c = forceBoundaryData k (shiftL k ρL c) (shiftR k ρR c) vL vR x := by
  have hΛ : Real.pi / Real.sqrt k ≠ 0 := div_ne_zero Real.pi_ne_zero (Real.sqrt_pos.2 hk).ne'
  have hx0 : x ≠ 0 := fun h => hx (Or.inl h)
  have hxL : x ≠ vL 0 := fun h => hx (Or.inr (Or.inl ⟨0, h.symm⟩))
  have hxR : x ≠ vR 0 := fun h => hx (Or.inr (Or.inr ⟨0, h.symm⟩))
  have hR' : shiftR k ρR c = Function.update ρR 0 (ρR 0 + -(c / (Real.pi / Real.sqrt k))) := by
    simp only [shiftR, sub_eq_add_neg]
  unfold phaseData forceBoundaryData
  rw [shiftL, hR', sum_update_zero_add, sum_update_zero_add]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hneg : x < 0
  · simp only [hneg, ↓reduceIte]
    rcases lt_or_gt_of_ne hxL with h | h
    · have hI : x ∉ Ioo (vL 0) (vR 0) := fun hI => absurd hI.1 (not_lt.2 h.le)
      simp only [h, ↓reduceIte, indicator_of_notMem hI, mul_zero, add_zero]
      field_simp
      ring
    · have hI : x ∈ Ioo (vL 0) (vR 0) := ⟨h, lt_of_lt_of_le hneg hvR⟩
      simp only [not_lt.2 h.le, ↓reduceIte, indicator_of_mem hI, Pi.one_apply, mul_one, add_zero]
      ring
  · have hpos : 0 < x := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm hx0)
    simp only [hneg, ↓reduceIte]
    rcases lt_or_gt_of_ne hxR with h | h
    · have hI : x ∈ Ioo (vL 0) (vR 0) := ⟨lt_of_le_of_lt hvL hpos, h⟩
      simp only [not_le.2 h, ↓reduceIte, indicator_of_mem hI, Pi.one_apply, mul_one, add_zero]
      ring
    · have hI : x ∉ Ioo (vL 0) (vR 0) := fun hI => absurd hI.2 (not_lt.2 h.le)
      simp only [h.le, ↓reduceIte, indicator_of_notMem hI, mul_zero, add_zero]
      field_simp
      ring

/-- A bounded harmonic extension minus a constant extends the data minus that constant. -/
theorem isBoundedHarmonicExtension_sub_const {g : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (c : ℝ) :
    IsBoundedHarmonicExtension (fun x => g x - c) S (fun z => u z - c) := by
  obtain ⟨hh, ⟨C, hC⟩, hl⟩ := hu
  refine ⟨hh.sub (InnerProductSpace.harmonicOnNhd_const c), ⟨C + |c|, fun z hz => ?_⟩,
    fun x hx => (hl x hx).sub tendsto_const_nhds⟩
  exact (abs_sub _ _).trans (add_le_add (hC z hz) le_rfl)

/-- Bounded harmonic extensions only see the data off the exceptional set. -/
theorem isBoundedHarmonicExtension_congr_data {g g' : ℝ → ℝ} {S : Set ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (h : ∀ x ∉ S, g x = g' x) : IsBoundedHarmonicExtension g' S u := by
  obtain ⟨hh, hb, hl⟩ := hu
  exact ⟨hh, hb, fun x hx => h x hx ▸ hl x hx⟩

/-- **(PS9.2) for the extensions**: an extension of the phase-shifted data minus `c` extends the canonical word of the
shifted seed weights. -/
theorem isBoundedHarmonicExtension_shift {k : ℝ} (hk : 0 < k) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hvL : vL 0 ≤ 0) (hvR : 0 ≤ vR 0) {c : ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (phaseData k ρL ρR vL vR c) (forceJumpSet vL vR) u) :
    IsBoundedHarmonicExtension (forceBoundaryData k (shiftL k ρL c) (shiftR k ρR c) vL vR) (forceJumpSet vL vR)
      (fun z => u z - c) :=
  isBoundedHarmonicExtension_congr_data (isBoundedHarmonicExtension_sub_const hu c) fun _ hx =>
    phaseData_sub_eq hk ρL ρR hvL hvR c hx

/-- Conversely, an extension of the shifted canonical word plus `c` extends the phase-shifted data. -/
theorem isBoundedHarmonicExtension_unshift {k : ℝ} (hk : 0 < k) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hvL : vL 0 ≤ 0) (hvR : 0 ≤ vR 0) {c : ℝ} {u : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension (forceBoundaryData k (shiftL k ρL c) (shiftR k ρR c) vL vR)
      (forceJumpSet vL vR) u) :
    IsBoundedHarmonicExtension (phaseData k ρL ρR vL vR c) (forceJumpSet vL vR) (fun z => u z + c) := by
  have h := isBoundedHarmonicExtension_sub_const hu (-c)
  simp only [sub_neg_eq_add] at h
  refine isBoundedHarmonicExtension_congr_data h fun x hx => ?_
  have := phaseData_sub_eq hk ρL ρR hvL hvR c hx
  linarith

/-- The coupling mean of an extension minus a constant. -/
theorem couplingMean_sub_const (k : ℝ) (w : ℝ → ℝ) (t : ℝ) (u : ℂ → ℝ) (c : ℝ) (z : ℂ) :
    couplingMean k w t (fun ξ => u ξ - c) z = couplingMean k w t u z - c := by
  simp only [couplingMean]
  ring

end Data

/-! ### The phase is constant -/

section Const

variable {nL nR : ℕ}

/-- **The two seed coordinates separate at once** (proof of Aux. lemma 122, p. 390: "Equality at a positive time would
force both and the intervening driver to coincide throughout an initial nontrivial interval, contrary to the
capacity-null collision sets"). -/
theorem seed_lt_seed {w vL vR : ℝ≥0 → ℝ} (hantiL : Antitone vL) (hmonoR : Monotone vR)
    (hordL : ∀ t, vL t ≤ w t) (hordR : ∀ t, w t ≤ vR t)
    (hnull : volume {u : ℝ | 0 ≤ u ∧ vL u.toNNReal = w u.toNNReal} = 0) {t : ℝ≥0} (ht : 0 < t) :
    vL t < vR t := by
  by_contra h
  rw [not_lt] at h
  have hsub : Icc (0 : ℝ) t ⊆ {u : ℝ | 0 ≤ u ∧ vL u.toNNReal = w u.toNNReal} := by
    intro u hu
    refine ⟨hu.1, le_antisymm (hordL _) ?_⟩
    have hut : u.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hu.2
    calc w u.toNNReal ≤ vR u.toNNReal := hordR _
      _ ≤ vR t := hmonoR hut
      _ ≤ vL t := h
      _ ≤ vL u.toNNReal := hantiL hut
  have hpos : 0 < volume (Icc (0 : ℝ) t) := by
    rw [Real.volume_Icc, sub_zero]
    exact ENNReal.ofReal_pos.2 (by exact_mod_cast ht)
  exact absurd (measure_mono_null hsub hnull) hpos.ne'

/-- **(PS9.1) at one point**: the actual coupling mean minus the canonical one is `d` times the harmonic measure of the
exposed interval, at the image point `f_t(z) ∈ ℍ`. -/
theorem couplingMean_sub_couplingMean_eq {k : ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} {w : ℝ → ℝ}
    {t : ℝ} {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} {d : ℝ} (hsep : vL 0 < vR 0) {U : ℂ → ℝ}
    (hU : IsBoundedHarmonicExtension (phaseData k ρL ρR (fun i => vL i - w t) (fun j => vR j - w t) d)
      (forceJumpSet (fun i => vL i - w t) (fun j => vR j - w t)) U) {z : ℂ}
    (hf : QuantumZipper.fwdMap w t z ∈ H) :
    couplingMean k w t U z - couplingMean k w t (meanExt k ρL ρR (w t) vL vR) z =
      d * phaseWindow (vL 0 - w t) (vR 0 - w t) (QuantumZipper.fwdMap w t z) := by
  have hS : (forceJumpSet (fun i => vL i - w t) (fun j => vR j - w t)).Finite :=
    ((finite_range _).union (finite_range _)).insert 0
  have h := eqOn_sub_eq_mul_phaseWindow (d := d) hS (by linarith : vL 0 - w t < vR 0 - w t)
    (Or.inr (Or.inl ⟨0, rfl⟩)) (Or.inr (Or.inr ⟨0, rfl⟩)) hU
    (isBoundedHarmonicExtension_meanExt k ρL ρR (w t) vL vR) (fun x _ => rfl) hf
  simp only at h
  simp only [couplingMean]
  linarith

/-- Continuity of the harmonic measure of the exposed interval along the flow, before swallowing. -/
theorem continuousOn_phaseWindow {w : ℝ → ℝ} (hw : Continuous w) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H \ QuantumZipper.fwdHull w T) {a b : ℝ → ℝ} (ha : ContinuousOn a (Icc 0 T))
    (hb : ContinuousOn b (Icc 0 T)) :
    ContinuousOn (fun t => phaseWindow (a t) (b t) (QuantumZipper.fwdMap w t z)) (Icc 0 T) := by
  have hf := Ito.continuousOn_fwdMap_time' hw hT hz
  have him : ∀ t ∈ Icc 0 T, 0 < (QuantumZipper.fwdMap w t z).im := fun t ht =>
    Ito.im_fwdMap_pos hw hT hz ht
  have harg : ∀ c : ℝ → ℝ, ContinuousOn c (Icc 0 T) →
      ContinuousOn (fun t => Complex.arg (QuantumZipper.fwdMap w t z - (c t : ℂ))) (Icc 0 T) :=
      fun c hc t ht => by
    have hcw : ContinuousWithinAt (fun t => QuantumZipper.fwdMap w t z - (c t : ℂ)) (Icc 0 T) t :=
      (hf t ht).sub (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hc t ht))
    have hpos : 0 < (QuantumZipper.fwdMap w t z - (c t : ℂ)).im := by simpa using him t ht
    exact ContinuousAt.comp_continuousWithinAt (g := Complex.arg)
      (f := fun t => QuantumZipper.fwdMap w t z - (c t : ℂ)) (Complex.continuousAt_arg (Or.inr hpos.ne')) hcw
  simp only [phaseWindow]
  exact ((harg b hb).sub (harg a ha)).div_const _

/-- **The phase is constant on `(0, ∞)`** (proof of Aux. lemma 122, p. 390: "Equation (PS9.1) therefore makes `d_t` an
adapted continuous function of `t > 0`. Its values lie in the discrete set `2πχℤ`, so it is constant on the entire
available positive interval"), along one path with continuous driver and force coordinates (the seeds separate at
once, `seed_lt_seed`), an actual mean `couplingMean k w t (U t) z` continuous in `t` before swallowing and the exact
boundary description `phaseData` with `d_t ∈ cℤ`, `c ≠ 0`. -/
theorem phase_eq_of_pos {k c : ℝ} (hc : c ≠ 0) {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ} (hwc : Continuous w)
    (hvLc : ∀ i, Continuous (vL i)) (hvRc : ∀ j, Continuous (vR j)) (hordL : ∀ t i, vL i t ≤ w t)
    (hordR : ∀ t j, w t ≤ vR j t) (hantiL : Antitone (vL 0))
    (hmonoR : Monotone (vR 0)) (hnull : volume {u : ℝ | 0 ≤ u ∧ vL 0 u.toNNReal = w u.toNNReal} = 0)
    {d : ℝ≥0 → ℝ} (hd : ∀ t, 0 < t → ∃ n : ℤ, d t = n * c) {U : ℝ≥0 → ℂ → ℝ}
    (hU : ∀ t, IsBoundedHarmonicExtension
      (phaseData k ρL ρR (fun i => vL i t - w t) (fun j => vR j t - w t) (d t))
      (forceJumpSet (fun i => vL i t - w t) (fun j => vR j t - w t)) (U t))
    (hcont : ∀ (z : ℂ) (T : ℝ), 0 ≤ T → z ∈ H \ QuantumZipper.fwdHull (fun s : ℝ => w s.toNNReal) T →
      ContinuousOn (fun t : ℝ => couplingMean k (fun s : ℝ => w s.toNNReal) t (U t.toNNReal) z) (Icc 0 T))
    {s t : ℝ≥0} (hs : 0 < s) (ht : 0 < t) : d s = d t := by
  set wr : ℝ → ℝ := fun r => w r.toNNReal with hwr
  have hwrc : Continuous wr := hwc.comp continuous_real_toNNReal
  set T : ℝ := s + t + 1 with hT
  have hT0 : 0 ≤ T := by positivity
  -- a far point, not swallowed before `T`
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn hwrc.continuousOn
  set z : ℂ := Complex.I * ((|K| + 3 * Real.sqrt T + 1 : ℝ) : ℂ) with hzdef
  have hzim : z.im = |K| + 3 * Real.sqrt T + 1 := by simp [hzdef]
  have hzH : z ∈ H := by
    show (0 : ℝ) < z.im
    rw [hzim]
    positivity
  have hznorm : |K| + 3 * Real.sqrt T < ‖z‖ := by
    have h1 := Complex.abs_im_le_norm z
    have h2 := le_abs_self z.im
    linarith
  have hz : z ∈ H \ QuantumZipper.fwdHull wr T :=
    mem_diff_fwdHull_of_norm hwrc hT0 (fun r hr => (Real.norm_eq_abs _ ▸ hK r hr).trans (le_abs_self K)) hzH
      hznorm
  -- the three continuous functions
  set X : ℝ → ℝ := fun r => couplingMean k wr r (U r.toNNReal) z with hX
  set X₀ : ℝ → ℝ := fun r => couplingMean k wr r
    (meanExt k ρL ρR (wr r) (fun i => vL i r.toNNReal) (fun j => vR j r.toNNReal)) z with hX₀
  set pw : ℝ → ℝ := fun r => phaseWindow (vL 0 r.toNNReal - wr r) (vR 0 r.toNNReal - wr r)
    (QuantumZipper.fwdMap wr r z) with hpw
  have hXc : ContinuousOn X (Icc 0 T) := hcont z T hT0 hz
  have hX₀c : ContinuousOn X₀ (Icc 0 T) := by
    have hv : ∀ j, ContinuousOn (fun r : ℝ => jointV (fun i => vL i r.toNNReal) (fun i => vR i r.toNNReal) j)
        (Icc 0 T) := fun j => by
      cases j with
      | inl i => exact ((hvLc i).comp continuous_real_toNNReal).continuousOn
      | inr i => exact ((hvRc i).comp continuous_real_toNNReal).continuousOn
    have h := (continuousOn_const (c := Real.pi / Real.sqrt k * (1 + ∑ i, ρR i))).add
      (continuousOn_harmPart k (jointρ ρL ρR) hwrc hT0 hz hv)
    refine h.congr fun r hr => ?_
    have hf : QuantumZipper.fwdMap wr r z ∈ H := Ito.im_fwdMap_pos hwrc hT0 hz hr
    simp only [hX₀]
    rw [couplingMean_meanExt_eq k ρL ρR (fun i => hordL _ i) (fun j => hordR _ j) hf]
    rfl
  have hpwc : ContinuousOn pw (Icc 0 T) :=
    continuousOn_phaseWindow hwrc hT0 hz
      ((((hvLc 0).comp continuous_real_toNNReal).sub hwrc).continuousOn)
      ((((hvRc 0).comp continuous_real_toNNReal).sub hwrc).continuousOn)
  -- `d` is their combination on `(0, T)`
  have hpos : ∀ r ∈ Ioo (0 : ℝ) T, 0 < pw r := fun r hr => by
    have hsep : vL 0 r.toNNReal < vR 0 r.toNNReal :=
      seed_lt_seed hantiL hmonoR (fun t => hordL t 0) (fun t => hordR t 0) hnull
        (Real.toNNReal_pos.2 hr.1)
    exact (phaseWindow_mem_Ioo (by linarith) (Ito.im_fwdMap_pos hwrc hT0 hz (Ioo_subset_Icc_self hr))).1
  have hrep : EqOn (fun r : ℝ => d r.toNNReal) (fun r => (X r - X₀ r) / pw r) (Ioo 0 T) := fun r hr => by
    have hsep : vL 0 r.toNNReal < vR 0 r.toNNReal :=
      seed_lt_seed hantiL hmonoR (fun t => hordL t 0) (fun t => hordR t 0) hnull
        (Real.toNNReal_pos.2 hr.1)
    have hf : QuantumZipper.fwdMap wr r z ∈ H := Ito.im_fwdMap_pos hwrc hT0 hz (Ioo_subset_Icc_self hr)
    have h := couplingMean_sub_couplingMean_eq (k := k) (ρL := ρL) (ρR := ρR) (w := wr) (t := r)
      (vL := fun i => vL i r.toNNReal) (vR := fun j => vR j r.toNNReal) (d := d r.toNNReal) hsep (hU r.toNNReal) hf
    simp only [hX, hX₀, hpw]
    rw [h, mul_div_assoc, div_self (hpos r hr).ne', mul_one]
  have hdc : ContinuousOn (fun r : ℝ => d r.toNNReal) (Ioo 0 T) :=
    (((hXc.mono Ioo_subset_Icc_self).sub (hX₀c.mono Ioo_subset_Icc_self)).div (hpwc.mono Ioo_subset_Icc_self)
      fun r hr => (hpos r hr).ne').congr hrep
  have hmem : ∀ r ∈ Ioo (0 : ℝ) T, ∃ n : ℤ, d r.toNNReal = n * c := fun r hr =>
    hd _ (Real.toNNReal_pos.2 hr.1)
  have hsT : (s : ℝ) ∈ Ioo (0 : ℝ) T := ⟨by exact_mod_cast hs, by linarith [t.coe_nonneg]⟩
  have htT : (t : ℝ) ∈ Ioo (0 : ℝ) T := ⟨by exact_mod_cast ht, by linarith [s.coe_nonneg]⟩
  have := eqOn_const_of_continuousOn_of_mem_zmultiples hdc hc hmem htT hsT
  simpa only [Real.toNNReal_coe] using this

end Const

end PhaseSel

end Sec7

end InteractingSLE

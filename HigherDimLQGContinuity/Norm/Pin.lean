import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Param.Defs
import HigherDimLQGMetric.Sphere.Scaling
import HigherDimLQGMetric.Sec4.Lemma41Uniform

/-!
# Pins and recentred fields (packet P2; blueprint Part A `a:def-pin`, `a:lem-pinlaw`, `a:lem-ratio`)

Source: [C] (2.5)–(2.7), p. 3–4, l. 145–167; NA1 items 11–13, R2(h); NA3 R7.

* `recentre s r z g = g(z + r ·) - g_{sr}(z)` and `scaleS d ξ s r z g = r^{ϕ(ξ)} e^{ξ g_{sr}(z)}`
  (the two definitions owned by P2; `ϕ = phiXi`, so `S_0 = r` and `S_ξ = r^{ξ Q(ξ)} e^{ξ g_{sr}(z)}` for `ξ > 0`,
  ruling N21);
* `a:lem-pinlaw` (a): `measurable_pin`, `measurable_recentre`, `isProbabilityMeasure_pinLaw`, `pinLaw_one`,
  `isWholeSpaceLGF_pinLaw`;
* `a:lem-pinlaw` (b): `pin_addConst`, `recentre_addConst` (a.s. for an LGF, simultaneously for every constant);
* `a:lem-pinlaw` (c), (d): `recentre_law`, `pinLaw_preimage_recentre_le`; joint laws `map_comp_recentre`; a.s.
  transfers `ae_recentre_of_ae`, `ae_pin_of_ae`;
* `a:lem-ratio`: `scaleS_ratio`, and `scaleS_pos`, `scaleS_of_pos`, `scaleS_zero`.

Everything holds for `d ≥ 2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- `h(z + r ·) - h_{sr}(z)` (Part A `a:def-pin`). -/
def recentre (s r : ℝ) (z : Rd d) (g : DistRd d) : DistRd d :=
  addConst (affineComp r z g) (-sphereAvg g (s * r) z)

/-- `S^{(s)}_ξ(r, z) = r^{ϕ(ξ)} e^{ξ g_{sr}(z)}` (Part A `a:def-pin`), with `ϕ = phiXi`: `ϕ(ξ) = ξ Q(ξ)` for `ξ > 0`
and `ϕ(0) = 1`, so that `S_0 = r` is the scale factor of the Euclidean endpoint (ruling N21). -/
def scaleS (d : ℕ) (ξ s r : ℝ) (z : Rd d) (g : DistRd d) : ℝ :=
  r ^ phiXi d ξ * Real.exp (ξ * sphereAvg g (s * r) z)

/-! ## Measurability and the pinned laws (`a:lem-pinlaw` (a)) -/

theorem measurable_pin (s : ℝ) : Measurable (pin (d := d) s) :=
  measurable_id.addConst (measurable_sphereAvg_left s 0).neg

theorem measurable_recentre (s r : ℝ) (z : Rd d) : Measurable (recentre (d := d) s r z) :=
  (measurable_id.affineComp r z).addConst (measurable_sphereAvg_left (s * r) z).neg

theorem isProbabilityMeasure_pinLaw (hd : 2 ≤ d) (s : ℝ) : IsProbabilityMeasure (pinLaw d s) := by
  have := (normLGFLaw_spec_holds d hd).1
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pin s).aemeasurable).2 this

/-- Deterministic form of `a:lem-pinlaw` (b) for the pin: if the radius-`s` sphere averages of `g` at `0` converge,
`pin s (g + c) = pin s g`. -/
theorem pin_addConst_of_tendsto (hd : 1 ≤ d) {s : ℝ} {g : DistRd d} {a : ℝ}
    (ha : Tendsto (sphereAvgSeq g s 0) atTop (𝓝 a)) (c : ℝ) :
    pin s (addConst g c) = pin s g := by
  unfold pin
  rw [sphereAvg_addConst_of_tendsto hd ha c, addConst_addConst]
  congr 1
  ring

/-- Deterministic form of `a:lem-pinlaw` (b) for the recentred field. -/
theorem recentre_addConst_of_tendsto (hd : 1 ≤ d) {s r : ℝ} (hr : 0 < r) {z : Rd d} {g : DistRd d}
    {a : ℝ} (ha : Tendsto (sphereAvgSeq g (s * r) z) atTop (𝓝 a)) (c : ℝ) :
    recentre s r z (addConst g c) = recentre s r z g := by
  unfold recentre
  rw [sphereAvg_addConst_of_tendsto hd ha c, affineComp_addConst hr, addConst_addConst]
  congr 1
  ring

section LGF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- `a:lem-pinlaw` (b) for the pin: for an LGF `h`, almost surely `pin s (h + c) = pin s h` simultaneously for every
constant `c` (so in particular for a random constant `c ω`). -/
theorem pin_addConst (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {s : ℝ} (hs : 0 < s) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, pin s (addConst (h ω) c) = pin s (h ω) := by
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd hs 0] with ω hω c
  obtain ⟨a, ha⟩ := hω
  exact pin_addConst_of_tendsto (by omega) ha c

/-- `a:lem-pinlaw` (b) for the recentred field: for an LGF `h`, almost surely
`recentre s r z (h + c) = recentre s r z h` simultaneously for every constant `c`. -/
theorem recentre_addConst (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (z : Rd d) : ∀ᵐ ω ∂P, ∀ c : ℝ, recentre s r z (addConst (h ω) c) = recentre s r z (h ω) := by
  filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq hd (mul_pos hs hr) z] with ω hω c
  obtain ⟨a, ha⟩ := hω
  exact recentre_addConst_of_tendsto (by omega) hr ha c

/-- For an LGF `h`, almost surely `recentre s r z h = pin s (h(z + r ·) - h_r(z))`. -/
theorem ae_recentre_eq_pin (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (z : Rd d) :
    ∀ᵐ ω ∂P, recentre s r z (h ω) =
      pin s (addConst (affineComp r z (h ω)) (-sphereAvg (h ω) r z)) := by
  have hk := hh.affineComp hr z
  filter_upwards [hk.ae_exists_tendsto_sphereAvgSeq hd hs 0,
    hh.ae_sphereAvg_affineComp hd hr z hs 0] with ω hω hsc
  obtain ⟨a, ha⟩ := hω
  unfold pin recentre
  rw [sphereAvg_addConst_of_tendsto (by omega) ha, hsc, addConst_addConst, smul_zero, zero_add,
    mul_comm r s]
  congr 1
  ring

end LGF

/-- `a:lem-pinlaw` (a): `id` is a whole-space LGF under `pinLaw d s`, with `g_s(0) = 0` almost surely. -/
theorem isWholeSpaceLGF_pinLaw (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) :
    IsWholeSpaceLGF (id : DistRd d → DistRd d) (pinLaw d s) ∧
      ∀ᵐ g ∂(pinLaw d s), sphereAvg g s 0 = 0 := by
  have hN := (normLGFLaw_spec_holds d hd).2.1
  have hP : IsWholeSpaceLGF (fun g : DistRd d => pin s g) (normLGFLaw d) :=
    hN.1.addConst ((measurable_sphereAvg_left s 0).comp hN.1.measurable).neg
  refine ⟨hP.map_id, ?_⟩
  have hS : MeasurableSet {k : DistRd d | sphereAvg k s 0 = 0} :=
    measurableSet_eq_fun (measurable_sphereAvg_left s 0) measurable_const
  rw [pinLaw, ae_map_iff (measurable_pin s).aemeasurable hS]
  filter_upwards [hN.1.ae_exists_tendsto_sphereAvgSeq hd hs 0] with g hg
  obtain ⟨a, ha⟩ := hg
  show sphereAvg (addConst g (-sphereAvg g s 0)) s 0 = 0
  rw [sphereAvg_addConst_of_tendsto (h := g) (by omega) ha, add_neg_cancel]

/-- `a:lem-pinlaw` (a): the unit pin is the normalized law. -/
theorem pinLaw_one (hd : 2 ≤ d) : pinLaw d 1 = normLGFLaw d := by
  have hN := (normLGFLaw_spec_holds d hd).2.1
  have e : pin (d := d) 1 =ᵐ[normLGFLaw d] id := by
    filter_upwards [hN.2] with g hg
    show addConst g (-sphereAvg g 1 0) = g
    rw [show sphereAvg g 1 0 = 0 from hg, neg_zero, addConst_zero]
  rw [pinLaw, Measure.map_congr e, Measure.map_id]

/-! ## The law of the recentred field (`a:lem-pinlaw` (c), (d)) -/

/-- `a:lem-pinlaw` (c): under every pin `s₀`, the recentred field `g(z + r ·) - g_{sr}(z)` has the law of the
radius-`s` pin. -/
theorem recentre_law (hd : 2 ≤ d) {s s₀ r : ℝ} (hs : 0 < s) (_hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) :
    (pinLaw d s₀).map (recentre s r z) = pinLaw d s := by
  have hN := (normLGFLaw_spec_holds d hd).2.1
  have hid : IsWholeSpaceLGF (id : DistRd d → DistRd d) (normLGFLaw d) := hN.1
  -- the recentred affine image, of law `normLGFLaw d`
  let k : DistRd d → DistRd d := fun g => addConst (affineComp r z g) (-sphereAvg g r z)
  have hkm : Measurable k := (measurable_id.affineComp r z).addConst (measurable_sphereAvg_left r z).neg
  have hklaw : (normLGFLaw d).map k = normLGFLaw d := by
    have := hN.map_affineComp_sub_sphereAvg hd hr z
    rw [Measure.map_id] at this
    exact this
  have e : (recentre s r z ∘ pin s₀) =ᵐ[normLGFLaw d] (pin s ∘ k) := by
    filter_upwards [recentre_addConst hd hid hs hr z, ae_recentre_eq_pin hd hid hs hr z] with g h1 h2
    simp only [Function.comp_apply]
    exact (h1 _).trans h2
  rw [pinLaw, Measure.map_map (measurable_recentre s r z) (measurable_pin s₀), Measure.map_congr e,
    ← Measure.map_map (measurable_pin s) hkm, hklaw, pinLaw]

/-- `a:lem-pinlaw` (d): for every set `B` (outer measures), `P_{s₀}{recentre ∈ B} ≤ P_s(B)`. -/
theorem pinLaw_preimage_recentre_le (hd : 2 ≤ d) {s s₀ r : ℝ} (hs : 0 < s) (hs₀ : 0 < s₀) (hr : 0 < r)
    (z : Rd d) (B : Set (DistRd d)) :
    pinLaw d s₀ {g | recentre s r z g ∈ B} ≤ pinLaw d s B := by
  rw [← recentre_law hd hs hs₀ hr z]
  exact Measure.le_map_apply (measurable_recentre s r z).aemeasurable B

/-- `a:lem-pinlaw` (c), joint laws: for a measurable functional `F` of the field (e.g. a pair `(Ψ, Ψ')`, or `rho D` for
a measurable `D`), `F(recentre s r z g)` has under `pinLaw d s₀` the law of `F` under `pinLaw d s`. -/
theorem map_comp_recentre (hd : 2 ≤ d) {β : Type*} [MeasurableSpace β] {F : DistRd d → β} (hF : Measurable F)
    {s s₀ r : ℝ} (hs : 0 < s) (hs₀ : 0 < s₀) (hr : 0 < r) (z : Rd d) :
    (pinLaw d s₀).map (fun g => F (recentre s r z g)) = (pinLaw d s).map F := by
  rw [← recentre_law hd hs hs₀ hr z, Measure.map_map hF (measurable_recentre s r z)]
  rfl

/-- Almost-sure properties transfer from `pinLaw d s` to the recentred field under `pinLaw d s₀` (no measurability of
the property is needed). -/
theorem ae_recentre_of_ae (hd : 2 ≤ d) {p : DistRd d → Prop} {s s₀ r : ℝ} (hs : 0 < s) (hs₀ : 0 < s₀)
    (hr : 0 < r) (z : Rd d) (h : ∀ᵐ g ∂(pinLaw d s), p g) :
    ∀ᵐ g ∂(pinLaw d s₀), p (recentre s r z g) := by
  rw [← recentre_law hd hs hs₀ hr z] at h
  exact ae_of_ae_map (measurable_recentre s r z).aemeasurable h

/-- Almost-sure properties under `pinLaw d s` hold for `pin s h`, `h ∼ normLGFLaw d`. -/
theorem ae_pin_of_ae {p : DistRd d → Prop} {s : ℝ} (h : ∀ᵐ g ∂(pinLaw d s), p g) :
    ∀ᵐ g ∂(normLGFLaw d), p (pin s g) :=
  ae_of_ae_map (measurable_pin s).aemeasurable h

/-! ## The scale factor (`a:lem-ratio`) -/

theorem scaleS_pos (d : ℕ) (ξ s : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) (g : DistRd d) :
    0 < scaleS d ξ s r z g :=
  mul_pos (Real.rpow_pos_of_pos hr _) (Real.exp_pos _)

/-- For `ξ > 0`, `S = r^{ξ Q(ξ)} e^{ξ g_{sr}(z)}`. -/
theorem scaleS_of_pos (d : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (s r : ℝ) (z : Rd d) (g : DistRd d) :
    scaleS d ξ s r z g = r ^ (ξ * distExp d ξ) * Real.exp (ξ * sphereAvg g (s * r) z) := by
  rw [scaleS, phiXi_of_pos hξ]

/-- At the Euclidean endpoint, `S_0 = r`. -/
@[simp] theorem scaleS_zero (d : ℕ) (s r : ℝ) (z : Rd d) (g : DistRd d) : scaleS d 0 s r z g = r := by
  rw [scaleS, phiXi_zero, Real.rpow_one, zero_mul, Real.exp_zero, mul_one]

/-- `scaleS` as one exponential: `S = exp(ϕ(ξ) log r + ξ g_{sr}(z))` (`r > 0`). -/
theorem scaleS_eq_exp (d : ℕ) (ξ s : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) (g : DistRd d) :
    scaleS d ξ s r z g = Real.exp (phiXi d ξ * Real.log r + ξ * sphereAvg g (s * r) z) := by
  rw [scaleS, Real.rpow_def_of_pos hr, Real.exp_add, mul_comm (Real.log r)]

/-- For `ξ > 0`, `S = exp(ξ Q(ξ) log r + ξ g_{sr}(z))` (`r > 0`). -/
theorem scaleS_eq_exp_of_pos (d : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (s : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d)
    (g : DistRd d) :
    scaleS d ξ s r z g = Real.exp (ξ * distExp d ξ * Real.log r + ξ * sphereAvg g (s * r) z) := by
  rw [scaleS_eq_exp d ξ s hr, phiXi_of_pos hξ]

/-- `a:lem-ratio` ((2.7)): `S_η / S_ξ = exp((ϕ(η) - ϕ(ξ)) log r + (η - ξ) g_{sr}(z))`. -/
theorem scaleS_ratio (d : ℕ) (ξ η s : ℝ) {r : ℝ} (hr : 0 < r) (z : Rd d) (g : DistRd d) :
    scaleS d η s r z g / scaleS d ξ s r z g =
      Real.exp ((phiXi d η - phiXi d ξ) * Real.log r + (η - ξ) * sphereAvg g (s * r) z) := by
  rw [scaleS_eq_exp d η s hr, scaleS_eq_exp d ξ s hr, ← Real.exp_sub]
  congr 1
  ring

end HigherDimLQGContinuity

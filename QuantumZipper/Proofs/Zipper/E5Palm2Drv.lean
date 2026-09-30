import QuantumZipper.Proofs.Zipper.E5Palm2Read

/-!
# E5-PALM2, part 3: driver readability `DrvReadable` (proved)

Task E5-PALM2. The collided driver `(collided …).2 u = W(T−τ+u) − W(T−τ)` (`u ≥ 0`, `W = √κ B`)
is read from the E4 driver data `(x, V^τ, W⁰)`:

* the collision time is recovered from the stopped reversed driver alone,
  `τ = tauHat T V^τ = sup {r ∈ ℚ : V^τ(r) ≠ V^τ(T)}` (clamped by `T`), because a Brownian path is
  a.s. not constant on any interval (increments `B r − B s`, `r ≠ s`, are non-degenerate
  Gaussians, mathlib `IsPreBrownianReal.hasLaw_sub`, `nullSingletonClass_gaussianReal`);
* paths are evaluated at real times through the jointly measurable dyadic evaluation
  `evq f t = lim_n f(⌊2ⁿ t⌋ / 2ⁿ)`, exact for continuous paths (a.s., `IsBrownianReal.cont`);
* `drvRd T q u = V^τ(τ−u) − V^τ(τ)` for `u ≤ τ`, `W⁰(u−τ) − V^τ(τ)` for `u > τ`.

Main result: `drvReadable_drvRd : IsBrownianReal B P → 0 < κ → DrvReadable κ T P B X ϖ δ (drvRd T)`.
Own elementary argument (no source needed: path bookkeeping and the non-atomic Gaussian law of
Brownian increments).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2 E1 CoordsFull E4Grid

/-! ## Dyadic evaluation of paths -/

/-- The dyadic grid time `⌊2ⁿ t⌋ / 2ⁿ` (as an element of `ℝ≥0`). -/
def dyT (n : ℕ) (t : ℝ) : ℝ≥0 := ((⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n).toNNReal

/-- Evaluation of a path at a real time along the dyadic grid (junk `0` without a limit). -/
def evq (f : ℝ≥0 → ℝ) (t : ℝ) : ℝ := limUnder atTop fun n => f (dyT n t)

theorem measurable_dyEval (n : ℕ) : Measurable fun p : (ℝ≥0 → ℝ) × ℝ => p.1 (dyT n p.2) := by
  have hg : Measurable fun q : (ℝ≥0 → ℝ) × ℤ => q.1 (((q.2 : ℝ)) / 2 ^ n).toNNReal :=
    measurable_from_prod_countable_left fun k =>
      measurable_pi_apply (((k : ℝ)) / 2 ^ n).toNNReal
  exact hg.comp (measurable_fst.prodMk
    (Int.measurable_floor.comp (measurable_snd.mul measurable_const)))

theorem measurable_evq : Measurable fun p : (ℝ≥0 → ℝ) × ℝ => evq p.1 p.2 := by
  unfold evq
  exact (StronglyMeasurable.limUnder fun n => (measurable_dyEval n).stronglyMeasurable).measurable

theorem tendsto_dyT (t : ℝ) : Tendsto (fun n => dyT n t) atTop (𝓝 t.toNNReal) := by
  refine (continuous_real_toNNReal.tendsto t).comp ?_
  have hp : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have hlo : ∀ n : ℕ, t - (1 / 2) ^ n ≤ (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n := fun n => by
    rw [le_div_iff₀ (hp n), sub_mul, one_div, inv_pow, inv_mul_cancel₀ (hp n).ne']
    linarith [Int.lt_floor_add_one (t * 2 ^ n)]
  have hhi : ∀ n : ℕ, (⌊t * 2 ^ n⌋ : ℝ) / 2 ^ n ≤ t := fun n => by
    rw [div_le_iff₀ (hp n)]; exact Int.floor_le _
  have h0 : Tendsto (fun n : ℕ => t - (1 / 2 : ℝ) ^ n) atTop (𝓝 t) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_sub t
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h0 tendsto_const_nhds hlo hhi

theorem evq_of_continuous {f : ℝ≥0 → ℝ} (hf : Continuous f) (t : ℝ) :
    evq f t = f t.toNNReal :=
  ((hf.tendsto _).comp (tendsto_dyT t)).limUnder_eq

/-! ## Recovering the collision time -/

open Classical in
/-- The collision time read from the stopped reversed driver. -/
def tauHat (T : ℝ) (V : ℝ≥0 → ℝ) : ℝ :=
  ⨆ r : ℚ, if V (r : ℝ).toNNReal ≠ V T.toNNReal then min (r : ℝ) T else 0

theorem measurable_tauHat (T : ℝ) : Measurable (tauHat T) := by
  classical
  refine Measurable.iSup fun r => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_eq_fun (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) _)
    (measurable_pi_apply (X := fun _ : ℝ≥0 => ℝ) _)).compl

open Classical in
/-- **The driver reader.** -/
def drvRd (T : ℝ) (q : CfgE) (u : ℝ) : ℝ :=
  if u ≤ tauHat T q.2.1 then evq q.2.1 (tauHat T q.2.1 - u) - evq q.2.1 (tauHat T q.2.1)
  else evq q.2.2 (u - tauHat T q.2.1) - evq q.2.1 (tauHat T q.2.1)

theorem measurable_drvRd (T : ℝ) : Measurable fun p : CfgE × ℝ => drvRd T p.1 p.2 := by
  classical
  have hV : Measurable fun p : CfgE × ℝ => p.1.2.1 := measurable_fst.snd.fst
  have hW : Measurable fun p : CfgE × ℝ => p.1.2.2 := measurable_fst.snd.snd
  have hτ : Measurable fun p : CfgE × ℝ => tauHat T p.1.2.1 := (measurable_tauHat T).comp hV
  have hE : Measurable fun p : CfgE × ℝ => evq p.1.2.1 (tauHat T p.1.2.1) :=
    measurable_evq.comp (hV.prodMk hτ)
  refine Measurable.ite (measurableSet_le measurable_snd hτ) ?_ ?_
  · exact (measurable_evq.comp (hV.prodMk (hτ.sub measurable_snd))).sub hE
  · exact (measurable_evq.comp (hW.prodMk (measurable_snd.sub hτ))).sub hE

/-! ## Brownian paths are a.s. nowhere locally constant -/

theorem ae_brownian_ne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ r s : ℚ, 0 < r → r < s → B (r : ℝ).toNNReal ω ≠ B (s : ℝ).toNNReal ω := by
  refine ae_all_iff.2 fun r => ae_all_iff.2 fun s => ?_
  by_cases h : 0 < r ∧ r < s
  swap
  · exact Eventually.of_forall fun ω h1 h2 => absurd ⟨h1, h2⟩ h
  have hr : (0 : ℝ) < r := by exact_mod_cast h.1
  have hrs : (r : ℝ) < s := by exact_mod_cast h.2
  set a : ℝ≥0 := (r : ℝ).toNNReal
  set b : ℝ≥0 := (s : ℝ).toNNReal
  have hab : (a : ℝ) ≠ b := by
    simp only [a, b, Real.coe_toNNReal _ hr.le, Real.coe_toNNReal _ (hr.trans hrs).le]
    exact hrs.ne
  have hL := hB.toIsPreBrownianReal.hasLaw_sub a b
  have hv : nndist (a : ℝ) b ≠ 0 := by rwa [Ne, nndist_eq_zero]
  have h0 : P ((B a - B b) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply₀ hL.aemeasurable (measurableSet_singleton 0).nullMeasurableSet,
      hL.map_eq]
    exact (nullSingletonClass_gaussianReal (μ := 0) hv).measure_singleton 0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω _ _ heq
  exact hω (by simp [heq])

/-! ## The deterministic identity on good paths -/

section Det

variable {Ω : Type*} {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω}

theorem continuous_drive_e5 (hc : Continuous fun t => B t ω) : Continuous (drive κ B ω) :=
  continuous_const.mul (hc.comp continuous_real_toNNReal)

theorem continuous_Vr_e5 (hc : Continuous fun t => B t ω) : Continuous (Vr κ T B ω) := by
  have hd := continuous_drive_e5 (κ := κ) hc
  show Continuous fun s => drive κ B ω (T - min (max s 0) T) - drive κ B ω T
  exact (hd.comp (continuous_const.sub ((continuous_id.max continuous_const).min
    continuous_const))).sub continuous_const

theorem continuous_Vstop_e5 (hc : Continuous fun t => B t ω) (τ : ℝ) :
    Continuous (Vstop κ T τ B ω) :=
  (continuous_Vr_e5 hc).comp (NNReal.continuous_coe.min continuous_const)

theorem continuous_W0p_e5 (hc : Continuous fun t => B t ω) : Continuous (W0p κ T B ω) := by
  have hd := continuous_drive_e5 (κ := κ) hc
  show Continuous fun u : ℝ≥0 => drive κ B ω (T + max (u : ℝ) 0) - drive κ B ω T
  exact (hd.comp (continuous_const.add (NNReal.continuous_coe.max continuous_const))).sub
    continuous_const

theorem Vr_apply_e5 {s : ℝ} (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    Vr κ T B ω s = drive κ B ω (T - s) - drive κ B ω T := by
  show drive κ B ω (T - min (max s 0) T) - drive κ B ω T = _
  rw [max_eq_left hs0, min_eq_left hsT]

theorem tauHat_Vstop (hc : Continuous fun t => B t ω)
    (hne : ∀ r s : ℚ, 0 < r → r < s → B (r : ℝ).toNNReal ω ≠ B (s : ℝ).toNNReal ω)
    (hκ : 0 < κ) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ < T) :
    tauHat T (Vstop κ T τ B ω) = τ := by
  classical
  set V := Vstop κ T τ B ω with hVdef
  have hT0 : 0 ≤ T := hτ0.trans hτT.le
  have hVT : V T.toNNReal = Vr κ T B ω τ := by
    simp only [V, Vstop, Real.coe_toNNReal _ hT0, min_eq_right hτT.le]
  have hVr : ∀ r : ℚ, V (r : ℝ).toNNReal = Vr κ T B ω (min (max (r : ℝ) 0) τ) := fun r => by
    simp only [V, Vstop, Real.coe_toNNReal']
  set g : ℚ → ℝ := fun r => if V (r : ℝ).toNNReal ≠ V T.toNNReal then min (r : ℝ) T else 0
    with hg
  have hle : ∀ r, g r ≤ τ := by
    intro r
    simp only [g]
    split_ifs with h
    · by_contra hlt
      push Not at hlt
      have hτr : τ < r := lt_of_lt_of_le hlt (min_le_left _ _)
      apply h
      rw [hVr, hVT, max_eq_left (hτ0.trans hτr.le), min_eq_right hτr.le]
    · exact hτ0
  have hbdd : BddAbove (range g) := ⟨τ, by rintro _ ⟨r, rfl⟩; exact hle r⟩
  have hg0 : g 0 = 0 := by simp only [g]; split_ifs <;> simp [hT0]
  show (⨆ r, g r) = τ
  refine le_antisymm (ciSup_le hle) ?_
  by_contra hlt
  push Not at hlt
  set a := ⨆ r, g r
  have ha0 : 0 ≤ a := hg0 ▸ le_ciSup hbdd 0
  -- `V` is constant on the rationals of `(a, τ)`
  have hconstQ : ∀ r : ℚ, (r : ℝ) ∈ Ioo a τ → Vr κ T B ω r = Vr κ T B ω τ := by
    intro r hr
    have hr0 : (0 : ℝ) ≤ r := ha0.trans hr.1.le
    by_contra hne'
    have hgr : g r = r := by
      simp only [g]
      rw [if_pos (by rw [hVr, hVT, max_eq_left hr0, min_eq_left hr.2.le]; exact hne'),
        min_eq_left (hr.2.le.trans hτT.le)]
    have := le_ciSup hbdd r
    rw [hgr] at this
    exact absurd hr.1 (not_lt.2 this)
  have hconst : EqOn (Vr κ T B ω) (fun _ => Vr κ T B ω τ) (Ioo a τ) := by
    refine EqOn.of_subset_closure (s := Ioo a τ ∩ range ((↑) : ℚ → ℝ)) ?_
      (continuous_Vr_e5 hc).continuousOn continuousOn_const inter_subset_left
      (Rat.denseRange_cast.open_subset_closure_inter isOpen_Ioo)
    rintro _ ⟨hr, r, rfl⟩
    exact hconstQ r hr
  obtain ⟨r₁, h₁, h₁'⟩ := exists_rat_btwn (show T - τ < T - a by linarith)
  obtain ⟨r₂, h₂, h₂'⟩ := exists_rat_btwn h₁'
  have hpos : (0 : ℝ) < r₁ := by linarith
  have key : ∀ r : ℚ, T - τ < r → (r : ℝ) < T - a →
      drive κ B ω r = drive κ B ω (T - τ) := by
    intro r hr hr'
    have hm : T - (r : ℝ) ∈ Ioo a τ := ⟨by linarith, by linarith⟩
    have e := hconst hm
    simp only at e
    rw [Vr_apply_e5 (by linarith) (by linarith), Vr_apply_e5 hτ0 hτT.le, sub_sub_cancel] at e
    linarith
  have e1 := key r₁ h₁ h₁'
  have e2 := key r₂ (h₁.trans h₂) h₂'
  have hB12 : B (r₁ : ℝ).toNNReal ω = B (r₂ : ℝ).toNNReal ω := by
    have := e1.trans e2.symm
    simp only [drive] at this
    exact mul_left_cancel₀ (Real.sqrt_pos.2 hκ).ne' this
  exact hne r₁ r₂ (by exact_mod_cast hpos) (by exact_mod_cast h₂) hB12

variable {X : Ω → FieldSample}

/-- **The driver identity** on good paths. -/
theorem drvRd_palmQ (hc : Continuous fun t => B t ω)
    (hne : ∀ r s : ℚ, 0 < r → r < s → B (r : ℝ).toNNReal ω ≠ B (s : ℝ).toNNReal ω)
    (hκ : 0 < κ) {x : ℝ} (hx : x ∈ palmA κ T B ω) (u : ℝ) (hu0 : 0 ≤ u) :
    drvRd T (palmQ κ T B ω x) u = (collided κ T B X ω x).2 u := by
  classical
  set τ := palmTau κ T B ω x with hτdef
  have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
  have hτT : τ < T := ENNReal.toReal_lt_of_lt_ofReal hx
  have htau : tauHat T (Vstop κ T τ B ω) = τ := tauHat_Vstop hc hne hκ hτ0 hτT
  have hVc := continuous_Vstop_e5 (κ := κ) (T := T) hc τ
  have hWc := continuous_W0p_e5 (κ := κ) (T := T) hc
  have hcol : (collided κ T B X ω x).2 u = drive κ B ω (T - τ + max u 0) - drive κ B ω (T - τ) :=
    rfl
  rw [hcol, max_eq_left hu0]
  show (if u ≤ tauHat T (Vstop κ T τ B ω) then
      evq (Vstop κ T τ B ω) (tauHat T (Vstop κ T τ B ω) - u) -
        evq (Vstop κ T τ B ω) (tauHat T (Vstop κ T τ B ω))
    else evq (W0p κ T B ω) (u - tauHat T (Vstop κ T τ B ω)) -
        evq (Vstop κ T τ B ω) (tauHat T (Vstop κ T τ B ω))) = _
  have hVτ : evq (Vstop κ T τ B ω) τ = drive κ B ω (T - τ) - drive κ B ω T := by
    rw [evq_of_continuous hVc]
    simp only [Vstop, Real.coe_toNNReal _ hτ0, min_self]
    exact Vr_apply_e5 hτ0 hτT.le
  rw [htau, hVτ]
  split_ifs with hu
  · rw [evq_of_continuous hVc]
    simp only [Vstop, Real.coe_toNNReal _ (sub_nonneg.2 hu),
      min_eq_left (sub_le_self τ hu0)]
    rw [Vr_apply_e5 (sub_nonneg.2 hu) ((sub_le_self τ hu0).trans hτT.le),
      show T - (τ - u) = T - τ + u by ring]
    ring
  · push Not at hu
    rw [evq_of_continuous hWc]
    show drive κ B ω (T + max ((u - τ).toNNReal : ℝ) 0) - drive κ B ω T - _ = _
    rw [Real.coe_toNNReal _ (sub_nonneg.2 hu.le), max_eq_left (sub_nonneg.2 hu.le),
      show T + (u - τ) = T - τ + u by ring]
    ring

end Det

/-- **Driver readability** (proved): for Brownian `B` and `κ > 0`, `drvRd T` reads the collided
driver from `(x, V^τ, W⁰)` a.s. under the Palm measure on `{τ < T}`. -/
theorem drvReadable_drvRd {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {κ T : ℝ}
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ} (hB : IsBrownianReal B P)
    (hκ : 0 < κ) (δ : ℝ) : DrvReadable κ T P B X ϖ δ (drvRd T) := by
  refine ⟨measurable_drvRd T, ?_⟩
  filter_upwards [hB.cont, ae_brownian_ne hB] with ω hc hne
  exact Eventually.of_forall fun x hx => drvRd_palmQ hc hne hκ hx

end E5
end QuantumZipper

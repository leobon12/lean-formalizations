import QuantumZipper.Proofs.Thm11.CharFunFwd
import QuantumZipper.Proofs.Thm11.PushTame
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# AS-1: the right-hand side of Theorem 1.1 (conditional Gaussian step)

Blueprint `THM11_BLUEPRINT.md` §8, node AS-1 (option S). For `T > 0`, a Brownian motion `B`, a
zero-boundary GFF `X` independent of `B` and `ρ : TestFun H`, with `W = drive κ B ω`,
`D_T = ℍ \ K_T`, `f_T = fwdMap W T` and `ν_T^± = pushTest W T (ρ^±)`:

  `E exp(i ⟨𝔥_T + h̃∘f_T, ρ⟩) = E exp(i ∫ρ 𝔥_T − E_T(ρ)/2)`,

`E_T(ρ) = ∬ ρ(x)ρ(y) 1_{D_T}(x) 1_{D_T}(y) G(f_T x, f_T y)` (`Efwd`), given, almost surely:

* `TameCond W T ρ^±`: the barrier condition, the log condition and the strip decay under which
  RG-3a/RG-2 (`PushTame.coordChangeOn_pushTest_ae_eq`) give `evalReg X ν_T^± = X ν_T^±`;
* integrability of `ρ 𝔥_T`.

Main results:

* `charFun_rhs_fwd`: the identity above.
* `rhs_fwd_version`: the right-hand field agrees a.s. with a field `Y` whose pairings are
  measurable and a.s. linear (the inputs of `CharFunFwd.fieldLaw_eq_of_charFun`).
* `fieldLaw_congr_ae`: a.s. equal fields have the same `fieldLaw H`.

Route (as in `CharFun.charFun_rhs`): replace `B` by a version with continuous paths, pass to
the driver path in `C([0,T], ℝ)` (where the forward flow is jointly measurable, via the tamed
flow), condition on the path through the product law given by independence, apply RG-2
pathwise, then the Gaussian characteristic function.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace CharFunRhs

open CharFun CharFunFwd PushTame

/-! ## Definitions -/

/-- The right-hand field `𝔥_T + h̃∘f_T` of Theorem 1.1 for a driver `W` and a GFF sample `x`. -/
def Yfwd (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample) : FieldSample :=
  ofFun (hTfwd κ W T) + coordChangeOn x (fwdMap W T) (H \ fwdHull W T)

/-- The energy `E_T(ρ) = ∬ ρ(x)ρ(y) 1_{D_T}(x) 1_{D_T}(y) G(f_T x, f_T y)`. -/
def Efwd (W : ℝ → ℝ) (T : ℝ) (ρ : ℂ → ℝ) : ℝ :=
  ∫ x, ∫ y, ρ x * ρ y * (H \ fwdHull W T).indicator (1 : ℂ → ℝ) x *
    (H \ fwdHull W T).indicator (1 : ℂ → ℝ) y * greenH (fwdMap W T x) (fwdMap W T y)

/-- The barrier condition (FD-5): real points `±R` outside the real parts of `supp ρ` are not
swallowed by time `T`. -/
def Barrier (W : ℝ → ℝ) (T : ℝ) (ρ : ℂ → ℝ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ (∀ a ∈ tsupport ρ, |a.re| < R) ∧ (∃ v, IsForwardSol W (R : ℂ) T v) ∧
    ∃ v, IsForwardSol W ((-R : ℝ) : ℂ) T v

/-- The driver-path conditions under which RG-3a + RG-2 apply to `ν_T = pushTest W T ρ⁺`:
barriers, `∫ log⁻ Im dν_T < ∞`, and log-log strip decay. -/
def TameCond (W : ℝ → ℝ) (T : ℝ) (ρ : ℂ → ℝ) : Prop :=
  Barrier W T ρ ∧
    ∫⁻ x, ENNReal.ofReal (-Real.log x.im) ∂pushTest W T (fun z => ENNReal.ofReal (ρ z)) < ⊤ ∧
    ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ t : ℝ, 1 ≤ t →
      pushTest W T (fun z => ENNReal.ofReal (ρ z)) {z | z.im < Real.exp (-Real.exp t)} ≤
        ENNReal.ofReal (C * t ^ (-(1 + η)))

/-! ## Elementary facts -/

theorem tf_reg (ρ : TestFun H) : Continuous ρ.1 ∧ HasCompactSupport ρ.1 ∧ tsupport ρ.1 ⊆ H :=
  ⟨tf_continuous ρ, ρ.2.2.1, ρ.2.2.2⟩

theorem tf_reg_neg (ρ : TestFun H) : Continuous (fun z => -ρ.1 z) ∧
    HasCompactSupport (fun z => -ρ.1 z) ∧ tsupport (fun z => -ρ.1 z) ⊆ H := by
  refine ⟨(tf_continuous ρ).neg, ρ.2.2.1.neg, ?_⟩
  show tsupport (-ρ.1) ⊆ H
  rw [tsupport_neg]
  exact ρ.2.2.2

theorem pairRaw_Yfwd (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (x : FieldSample) (ρ : ℂ → ℝ) :
    pairRaw (Yfwd κ W T x) ρ = pairRaw (ofFun (hTfwd κ W T)) ρ +
      (evalReg x (pushTest W T fun z => ENNReal.ofReal (ρ z)) -
        evalReg x (pushTest W T fun z => ENNReal.ofReal (-ρ z))) := by
  rw [Yfwd, pairRaw_add]
  rfl

theorem pairRaw_ofFun_of_integrable {g ρ : ℂ → ℝ} (hρ : Continuous ρ)
    (hi : Integrable fun z => ρ z * g z) : pairRaw (ofFun g) ρ = ∫ z, ρ z * g z := by
  have hm : ∀ b : ℂ → ℝ, Measurable b → ∫ z, g z ∂(tdens b) = ∫ z, max (b z) 0 * g z :=
    fun b hb => by
      rw [tdens, integral_withDensity_eq_integral_toReal_smul
        (f := fun z => ENNReal.ofReal (b z)) hb.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      simp [ENNReal.toReal_ofReal', smul_eq_mul]
  have i1 : Integrable fun z => max (ρ z) 0 * g z := by
    refine (hi.indicator (measurableSet_lt measurable_const hρ.measurable :
      MeasurableSet {z | (0 : ℝ) < ρ z})).congr
      (ae_of_all _ fun z => ?_)
    by_cases h : 0 < ρ z
    · simp [indicator, h, max_eq_left h.le]
    · simp [indicator, h, max_eq_right (not_lt.1 h)]
  have i2 : Integrable fun z => max (-ρ z) 0 * g z := by
    refine (hi.indicator (measurableSet_lt hρ.measurable measurable_const :
      MeasurableSet {z | ρ z < (0 : ℝ)})).neg.congr
      (ae_of_all _ fun z => ?_)
    by_cases h : ρ z < 0
    · simp [indicator, h, max_eq_left (neg_nonneg.2 h.le)]
    · simp [indicator, h, max_eq_right (neg_nonpos.2 (not_lt.1 h))]
  rw [pairRaw_eq_tdens]
  simp only [ofFun]
  rw [hm ρ hρ.measurable, hm (fun z => -ρ z) hρ.measurable.neg, ← integral_sub i1 i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [← sub_mul, max_sub_max_neg]

theorem integral_lin_int {g ρ₁ ρ₂ ρ₃ : ℂ → ℝ} (i1 : Integrable fun z => ρ₁ z * g z)
    (i2 : Integrable fun z => ρ₂ z * g z) (a : ℝ) (h : ∀ z, ρ₃ z = a * ρ₁ z + ρ₂ z) :
    ∫ z, ρ₃ z * g z = a * (∫ z, ρ₁ z * g z) + ∫ z, ρ₂ z * g z := by
  rw [← integral_const_mul, ← integral_add (i1.const_mul a) i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [h z]
  ring

theorem fieldLaw_congr_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y₁ Y₂ : Ω → FieldSample} (h : ∀ᵐ ω ∂P, Y₁ ω = Y₂ ω) :
    fieldLaw H Y₁ P = fieldLaw H Y₂ P := by
  unfold fieldLaw
  refine Measure.map_congr ?_
  filter_upwards [h] with ω hω
  rw [hω]

/-! ## Dependence on the driver only through `[0, T]` -/

section Congr

variable {W W' : ℝ → ℝ} {T : ℝ}

theorem isForwardSol_iff_of_eqOn (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) {z : ℂ} {u : ℝ → ℂ} :
    IsForwardSol W z T u ↔ IsForwardSol W' z T u :=
  ⟨isForwardSol_congr_drive h, isForwardSol_congr_drive fun r hr => (h r hr).symm⟩

theorem fwdMap_eq_of_eqOn (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) :
    fwdMap W T = fwdMap W' T := by
  funext z
  have e : IsForwardSol W z T = IsForwardSol W' z T :=
    funext fun u => propext (isForwardSol_iff_of_eqOn h)
  unfold fwdMap
  rw [e]

theorem fwdHull_eq_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) : fwdHull W T = fwdHull W' T := by
  ext a
  rw [NonSwallow.mem_fwdHull_iff_tamed hW hT, NonSwallow.mem_fwdHull_iff_tamed hW' hT]
  have key : ∀ (k : ℕ) (q : ℚ), 0 ≤ (q : ℝ) → (q : ℝ) ≤ T →
      tamedZ W (1 / ((k : ℝ) + 1)) a q = tamedZ W' (1 / ((k : ℝ) + 1)) a q :=
    fun k q h0 hq => tamedZ_congr_drive hW hW' (by positivity) h0 a
      (fun r hr => h r ⟨hr.1, hr.2.trans hq⟩)
  constructor
  · rintro ⟨ha, hk⟩
    refine ⟨ha, fun k => ?_⟩
    obtain ⟨q, h0, hq, hlt⟩ := hk k
    exact ⟨q, h0, hq, by rwa [← key k q h0 hq]⟩
  · rintro ⟨ha, hk⟩
    refine ⟨ha, fun k => ?_⟩
    obtain ⟨q, h0, hq, hlt⟩ := hk k
    exact ⟨q, h0, hq, by rwa [key k q h0 hq]⟩

theorem logDerivFwd_eq_of_eqOn (hT : 0 ≤ T) (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) :
    logDerivFwd W T = logDerivFwd W' T := by
  funext z
  unfold logDerivFwd
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le hT] at hs
  simp only [fwdMap_eq_of_eqOn (T := s) fun r hr => h r ⟨hr.1, hr.2.trans hs.2⟩]

theorem hTfwd_eq_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) (κ : ℝ) : hTfwd κ W T = hTfwd κ W' T := by
  unfold hTfwd
  rw [fwdHull_eq_of_eqOn hW hW' hT h, fwdMap_eq_of_eqOn h, logDerivFwd_eq_of_eqOn hT h]

theorem Yfwd_eq_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) (κ : ℝ) : Yfwd κ W T = Yfwd κ W' T := by
  unfold Yfwd
  rw [hTfwd_eq_of_eqOn hW hW' hT h, fwdHull_eq_of_eqOn hW hW' hT h, fwdMap_eq_of_eqOn h]

theorem Efwd_eq_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) : Efwd W T = Efwd W' T := by
  unfold Efwd
  rw [fwdHull_eq_of_eqOn hW hW' hT h, fwdMap_eq_of_eqOn h]

theorem pushTest_eq_of_eqOn (hW : Continuous W) (hW' : Continuous W') (hT : 0 ≤ T)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) : pushTest W T = pushTest W' T := by
  funext φ
  unfold pushTest
  rw [fwdHull_eq_of_eqOn hW hW' hT h, fwdMap_eq_of_eqOn h]

end Congr

/-! ## Consequences of the tameness conditions (RG-3a + RG-2) -/

section Tame

variable {W : ℝ → ℝ} {T : ℝ} {a : ℂ → ℝ}

theorem TameCond.adm (h : TameCond W T a) (hW : Continuous W) (hW0 : W 0 = 0) (hT : 0 < T)
    (hreg : Continuous a ∧ HasCompactSupport a ∧ tsupport a ⊆ H) :
    IsAdmissibleH (pushTest W T fun z => ENNReal.ofReal (a z)) := by
  obtain ⟨ha, hac, haH⟩ := hreg
  obtain ⟨⟨R, hR, hKR, hp, hm⟩, hlog, -⟩ := h
  obtain ⟨M, hM⟩ := ha.bounded_above_of_compact_support hac
  exact (pushTest_tame hW hW0 hT ha.measurable.ennreal_ofReal (c := ENNReal.ofReal M)
    ENNReal.ofReal_lt_top
    (fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸
      hM z))) hac haH
    (fun z hz => by rw [image_eq_zero_of_notMem_tsupport hz, ENNReal.ofReal_zero])
    hR hKR hp hm hlog).1

end Tame

/-! ## The energy of pushforwards for `greenH` -/

/-! ## Linearity of the GFF on pushforwards by a measurable map -/

/-! ## The driver path space and joint measurability of the forward flow -/

section Path

variable {T : ℝ}

/-- The coordinates `r ↦ f(proj_{[0,T]} r)` of a path `f ∈ C([0,T], ℝ)`. -/
def Bc (hT : 0 ≤ T) (r : ℝ≥0) (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ := f (projIcc 0 T hT r)

theorem measurable_Bc (hT : 0 ≤ T) (r : ℝ≥0) : Measurable (Bc hT r) :=
  ContinuousMap.measurable_eval _

theorem continuous_Bc (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) : Continuous fun r => Bc hT r f :=
  f.continuous.comp (continuous_projIcc.comp NNReal.continuous_coe)

theorem continuous_drive_Bc (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    Continuous (drive κ (Bc hT) f) :=
  continuous_const.mul ((continuous_Bc hT f).comp continuous_real_toNNReal)

theorem drive_eq_drive_Bc (κ : ℝ) (hT : 0 ≤ T) {Ω : Type*} {B' : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t => B' t ω) (ω : Ω) :
    ∀ r ∈ Icc (0 : ℝ) T, drive κ B' ω r = drive κ (Bc hT) (pathC T B' hc ω) r := by
  intro r hr
  simp [drive, Bc, pathC, Real.coe_toNNReal r hr.1, projIcc_of_mem hT hr]

/-- The domain `{(f, z) : z ∈ ℍ \ K_T(f)}`. -/
def DomS (κ : ℝ) (hT : 0 ≤ T) : Set (C(Icc (0 : ℝ) T, ℝ) × ℂ) :=
  {p | p.2 ∈ H \ fwdHull (drive κ (Bc hT) p.1) T}

theorem measurableSet_DomS (κ : ℝ) (hT : 0 ≤ T) : MeasurableSet (DomS κ hT) := by
  have hS := NonSwallow.measurableSet_fwdHull_prod (measurable_Bc hT) (continuous_Bc hT) κ hT
  have e : DomS κ hT = {p | 0 < p.2.im} ∩ (Prod.swap ⁻¹'
      {p : ℂ × C(Icc (0 : ℝ) T, ℝ) | p.1 ∈ fwdHull (drive κ (Bc hT) p.2) T})ᶜ := by
    ext p; exact Iff.rfl
  rw [e]
  exact (measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)).inter
    (hS.preimage measurable_swap).compl

theorem measurableSet_sec (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    MeasurableSet (H \ fwdHull (drive κ (Bc hT) f) T) :=
  (measurableSet_DomS κ hT).preimage measurable_prodMk_left

/-- A jointly measurable version of `f_T`. -/
def FmF (κ : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, ℝ) × ℂ) : ℂ :=
  limUnder atTop fun k : ℕ => tamedZ (drive κ (Bc hT) p.1) (1 / ((k : ℝ) + 1)) p.2 T

/-- A jointly measurable version of `arg f_T'`. -/
def AmF (κ : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, ℝ) × ℂ) : ℝ :=
  limUnder atTop fun k : ℕ => tamedA (drive κ (Bc hT) p.1) (1 / ((k : ℝ) + 1)) p.2 T

theorem measurable_FmF (κ : ℝ) (hT : 0 ≤ T) : Measurable (FmF κ hT) := by
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  exact ((measurable_tamed_drive κ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)) (Bc hT)
    (continuous_Bc hT) hT (fun r _ => measurable_Bc hT r)).1.comp
      measurable_swap).stronglyMeasurable

theorem measurable_AmF (κ : ℝ) (hT : 0 ≤ T) : Measurable (AmF κ hT) := by
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  exact ((measurable_tamed_drive κ (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)) (Bc hT)
    (continuous_Bc hT) hT (fun r _ => measurable_Bc hT r)).2.comp
      measurable_swap).stronglyMeasurable

theorem measurable_FmF_sec (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    Measurable fun z => FmF κ hT (f, z) :=
  (measurable_FmF κ hT).comp measurable_prodMk_left

/-- Off the hull, the tamed flow agrees with the forward flow for small taming parameters. -/
theorem eventually_tamed_eq {W : ℝ → ℝ} (hW : Continuous W) (hT : 0 ≤ T) {a : ℂ}
    (ha : a ∈ H \ fwdHull W T) :
    ∀ᶠ k : ℕ in atTop, tamedZ W (1 / ((k : ℝ) + 1)) a T = fwdMap W T a ∧
      tamedA W (1 / ((k : ℝ) + 1)) a T = (logDerivFwd W T a).im := by
  have ha0 : 0 < a.im := ha.1
  obtain ⟨u, hu⟩ := exists_isForwardSol_of_not_mem_fwdHull hT ha.1 ha.2
  obtain ⟨s0, hs0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT)
    (Complex.continuous_im.comp_continuousOn hu.1)
  have hm : 0 < (u s0).im := FwdClock.sol_im_pos hW ha0 hu hs0
  obtain ⟨k0, hk0⟩ := exists_nat_one_div_lt hm
  refine eventually_atTop.2 ⟨k0, fun k hk => ?_⟩
  set c : ℝ := 1 / ((k : ℝ) + 1) with hcdef
  have hc : 0 < c := by positivity
  have hck : c ≤ 1 / ((k0 : ℝ) + 1) := by
    rw [hcdef]
    gcongr
  have him : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (u t).im := fun t ht => by
    have h2 : (u s0).im ≤ (u t).im := by simpa using isMinOn_iff.1 hmin t ht
    linarith
  have heq := tamedZ_eq_of_isForwardSol hW hc hT hu him
  have himZ : ∀ t ∈ Icc (0 : ℝ) T, c ≤ (tamedZ W c a t).im := fun t ht => by
    rw [heq t ht]; exact him t ht
  refine ⟨?_, (im_logDerivFwd_eq_tamedA hW hc hT ha0 himZ T ⟨hT, le_rfl⟩).symm⟩
  rw [heq T ⟨hT, le_rfl⟩, fwdMap_eq hW ha0 hu ⟨hT, le_rfl⟩]

theorem FmF_eq (κ : ℝ) (hT : 0 ≤ T) {p : C(Icc (0 : ℝ) T, ℝ) × ℂ} (hp : p ∈ DomS κ hT) :
    FmF κ hT p = fwdMap (drive κ (Bc hT) p.1) T p.2 :=
  (tendsto_const_nhds.congr' ((eventually_tamed_eq (continuous_drive_Bc κ hT p.1) hT hp).mono
    fun _ hk => hk.1.symm)).limUnder_eq

theorem AmF_eq (κ : ℝ) (hT : 0 ≤ T) {p : C(Icc (0 : ℝ) T, ℝ) × ℂ} (hp : p ∈ DomS κ hT) :
    AmF κ hT p = (logDerivFwd (drive κ (Bc hT) p.1) T p.2).im :=
  (tendsto_const_nhds.congr' ((eventually_tamed_eq (continuous_drive_Bc κ hT p.1) hT hp).mono
    fun _ hk => hk.2.symm)).limUnder_eq

/-- A jointly measurable version of `𝔥_T`. -/
def hTmF (κ : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, ℝ) × ℂ) : ℝ :=
  (DomS κ hT).indicator (fun p => h0fwd κ (FmF κ hT p) - chiC κ * AmF κ hT p) p

theorem measurable_hTmF (κ : ℝ) (hT : 0 ≤ T) : Measurable (hTmF κ hT) := by
  have h0 : Measurable (h0fwd κ) := by
    unfold h0fwd; exact measurable_const.mul Complex.measurable_arg
  exact ((h0.comp (measurable_FmF κ hT)).sub (measurable_const.mul (measurable_AmF κ hT))).indicator
    (measurableSet_DomS κ hT)

theorem hTmF_eq (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (z : ℂ) :
    hTmF κ hT (f, z) = hTfwd κ (drive κ (Bc hT) f) T z := by
  by_cases hz : (f, z) ∈ DomS κ hT
  · rw [hTmF, indicator_of_mem hz, FmF_eq κ hT hz, AmF_eq κ hT hz]
    unfold hTfwd
    have hz' : z ∈ H \ fwdHull (drive κ (Bc hT) f) T := hz
    simp only [hz', ↓reduceIte]
  · rw [hTmF, indicator_of_notMem hz]
    unfold hTfwd
    have hz' : z ∉ H \ fwdHull (drive κ (Bc hT) f) T := hz
    simp only [hz', ↓reduceIte]

theorem pushTest_Bc_eq (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (φ : ℂ → ℝ≥0∞) :
    pushTest (drive κ (Bc hT) f) T φ =
      ((volume.withDensity φ).restrict (H \ fwdHull (drive κ (Bc hT) f) T)).map
        fun z => FmF κ hT (f, z) := by
  unfold pushTest
  exact Measure.map_congr (ae_restrict_of_forall_mem (measurableSet_sec κ hT f)
    fun z hz => (FmF_eq κ hT (p := (f, z)) hz).symm)

theorem pushTest_eq_FmF (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (a : ℂ → ℝ) :
    pushTest (drive κ (Bc hT) f) T (fun z => ENNReal.ofReal (a z)) =
      (tdens ((H \ fwdHull (drive κ (Bc hT) f) T).indicator a)).map
        fun z => FmF κ hT (f, z) := by
  have hD := measurableSet_sec κ hT f
  rw [pushTest_Bc_eq, restrict_withDensity hD, ← withDensity_indicator hD, tdens]
  congr 2
  funext z
  by_cases hz : z ∈ H \ fwdHull (drive κ (Bc hT) f) T <;> simp [hz]

theorem pushTest_eq_FmF_neg (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (a : ℂ → ℝ) :
    pushTest (drive κ (Bc hT) f) T (fun z => ENNReal.ofReal (-a z)) =
      (tdens fun z => -((H \ fwdHull (drive κ (Bc hT) f) T).indicator a z)).map
        fun z => FmF κ hT (f, z) := by
  rw [pushTest_eq_FmF κ hT f (fun z => -a z)]
  congr 2
  funext z
  by_cases hz : z ∈ H \ fwdHull (drive κ (Bc hT) f) T <;> simp [hz]

/-- The integrands of the regularized evaluations, jointly in (path, sample, point). -/
def PhiK (κ : ℝ) (hT : 0 ≤ T) (k : ℕ) (q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ) : ℝ :=
  ((fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => (q.1.1, q.2)) ⁻¹' DomS κ hT).indicator
    (fun q => avgReg q.1.2 k (FmF κ hT (q.1.1, q.2))) q

theorem measurable_PhiK (κ : ℝ) (hT : 0 ≤ T) (k : ℕ) : Measurable (PhiK κ hT k) := by
  have hpr : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => (q.1.1, q.2) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  exact ((measurable_avgReg k).comp ((measurable_snd.comp measurable_fst).prodMk
    ((measurable_FmF κ hT).comp hpr))).indicator ((measurableSet_DomS κ hT).preimage hpr)

theorem evalReg_pushTest_Bc (κ : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (x : FieldSample)
    (a : ℂ → ℝ) :
    evalReg x (pushTest (drive κ (Bc hT) f) T fun z => ENNReal.ofReal (a z)) =
      limUnder atTop fun k => ∫ z, PhiK κ hT k ((f, x), z) ∂(tdens a) := by
  have hD := measurableSet_sec κ hT f
  unfold evalReg
  congr 1
  funext k
  have hav : Measurable fun w => avgReg x k w :=
    (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)
  rw [pushTest_Bc_eq, integral_map (measurable_FmF_sec κ hT f).aemeasurable
    hav.aestronglyMeasurable,
    ← integral_indicator hD]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ H \ fwdHull (drive κ (Bc hT) f) T
  · simp only [PhiK]
    rw [indicator_of_mem hz, indicator_of_mem (show ((f, x), z) ∈
      (fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => (q.1.1, q.2)) ⁻¹' DomS κ hT from hz)]
  · simp only [PhiK]
    rw [indicator_of_notMem hz, indicator_of_notMem (show ((f, x), z) ∉
      (fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ => (q.1.1, q.2)) ⁻¹' DomS κ hT from hz)]

/-- **Joint measurability** of the pairing of the right-hand field in (driver path, sample). -/
theorem measurable_pair_Yc (κ : ℝ) (hT : 0 ≤ T) (ρ : ℂ → ℝ) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      pairRaw (Yfwd κ (drive κ (Bc hT) p.1) T p.2) ρ := by
  have hi : ∀ a : ℂ → ℝ, Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      ofFun (hTfwd κ (drive κ (Bc hT) p.1) T) (tdens a) := by
    intro a
    have e : (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
        ofFun (hTfwd κ (drive κ (Bc hT) p.1) T) (tdens a)) =
        fun p => ∫ z, hTmF κ hT (p.1, z) ∂(tdens a) := by
      funext p; simp only [ofFun, hTmF_eq]
    rw [e]
    exact ((measurable_hTmF κ hT).stronglyMeasurable.integral_prod_right').measurable.comp
      measurable_fst
  have he : ∀ a : ℂ → ℝ, Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 (pushTest (drive κ (Bc hT) p.1) T fun z => ENNReal.ofReal (a z)) := by
    intro a
    have e : (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
        evalReg p.2 (pushTest (drive κ (Bc hT) p.1) T fun z => ENNReal.ofReal (a z))) =
        fun p => limUnder atTop fun k => ∫ z, PhiK κ hT k (p, z) ∂(tdens a) := by
      funext p; exact evalReg_pushTest_Bc κ hT p.1 p.2 a
    rw [e]
    exact (StronglyMeasurable.limUnder fun k =>
      (measurable_PhiK κ hT k).stronglyMeasurable.integral_prod_right').measurable
  have heq : ∀ p : C(Icc (0 : ℝ) T, ℝ) × FieldSample,
      pairRaw (Yfwd κ (drive κ (Bc hT) p.1) T p.2) ρ =
        (ofFun (hTfwd κ (drive κ (Bc hT) p.1) T) (tdens ρ) -
          ofFun (hTfwd κ (drive κ (Bc hT) p.1) T) (tdens fun z => -ρ z)) +
        (evalReg p.2 (pushTest (drive κ (Bc hT) p.1) T fun z => ENNReal.ofReal (ρ z)) -
          evalReg p.2 (pushTest (drive κ (Bc hT) p.1) T fun z => ENNReal.ofReal (-ρ z))) :=
    fun p => by rw [pairRaw_Yfwd]; rfl
  rw [show (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
    pairRaw (Yfwd κ (drive κ (Bc hT) p.1) T p.2) ρ) = _ from funext heq]
  exact ((hi _).sub (hi _)).add ((he _).sub (he _))

/-! ## The conditional Gaussian step for a fixed driver path -/

end Path

/-! ## Independence -/

theorem ae_indep_ae {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → α} {Y : Ω → β}
    (hg : Measurable g) (hY : Measurable Y) (hind : IndepFun g Y P) {E : Set (α × β)}
    (hE : MeasurableSet E) (h : ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, (g ω, Y ω') ∈ E) :
    ∀ᵐ ω ∂P, (g ω, Y ω) ∈ E := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hY.aemeasurable).1 hind
  have hQ : MeasurableSet {a : α | (P.map Y) (Prod.mk a ⁻¹' Eᶜ) = 0} :=
    measurable_measure_prodMk_left hE.compl (measurableSet_singleton 0)
  have h' : ∀ᵐ a ∂(P.map g), (P.map Y) (Prod.mk a ⁻¹' Eᶜ) = 0 := by
    refine (ae_map_iff hg.aemeasurable hQ).2 ?_
    filter_upwards [h] with ω hω
    rw [Measure.map_apply hY (measurable_prodMk_left hE.compl)]
    exact ae_iff.1 hω
  have : ∀ᵐ p ∂(P.map fun ω => (g ω, Y ω)), p ∈ E := by
    rw [hprod]
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hE).2 ?_
    filter_upwards [h'] with a ha
    exact ae_iff.2 ha
  exact (ae_map_iff (hg.prodMk hY).aemeasurable hE).1 this

/-! ## AS-1 -/

end CharFunRhs
end QuantumZipper

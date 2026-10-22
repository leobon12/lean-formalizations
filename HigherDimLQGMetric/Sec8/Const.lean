import HigherDimLQGMetric.Sec8.AeFav
import HigherDimLQGMetric.Freq.ConstLaw

/-! Constant-shift invariance of the four Section 8 conditions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Filter Topology Metric unitInterval
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

private theorem sec8_metric_eq_smul (D E : ContMetric d) (e : ℝ) (he : 0 < e)
    (h : ∀ u v : Rd d, E.1 (u, v) = e * D.1 (u, v)) :
    E = D.smul e he := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  exact h p.1 p.2

private theorem sec8_sel_scale (D E : ContMetric d) (x y : Rd d)
    (e : ℝ) (he : 0 < e)
    (h : ∀ u v : Rd d, E.1 (u, v) = e * D.1 (u, v))
    (hex : ∃ η : C(unitInterval, Rd d), IsConstSpeedGeod D x y η) :
    sec8Sel x y E.1 = sec8Sel x y D.1 := by
  have hscale := ((exists_measurable_geodSelector x y).choose_spec.2 D hex).2 e he
  rw [sec8_metric_eq_smul D E e he h]
  exact hscale


private theorem sec8_sNorm_addConst (ξ Q : ℝ) (g : DistRd d) (c r : ℝ)
    (z : Rd d) (havg : sphereAvg (addConst g c) r z = sphereAvg g r z + c) :
    sNorm ξ Q (addConst g c) r z =
      sNorm ξ Q g r z * Real.exp (ξ * c) := by
  simp only [sNorm, havg, mul_add, Real.exp_add]
  ring

private theorem sec8_macroS_addConst (ξ Q : ℝ) (g : DistRd d) (c R : ℝ)
    (havg : sphereAvg (addConst g c) (8 * R) 0 = sphereAvg g (8 * R) 0 + c) :
    macroS ξ Q (addConst g c) R =
      macroS ξ Q g R * Real.exp (ξ * c) := by
  simp only [macroS, havg, mul_add, Real.exp_add]
  ring

private theorem sec8_normCoord_scale (s e : ℝ) (hs : 0 < s) (he : 0 < e)
    (v : ℝ≥0∞) :
    ENNReal.ofReal (s * e)⁻¹ * (ENNReal.ofReal e * v) =
      ENNReal.ofReal s⁻¹ * v := by
  have hf : (s * e)⁻¹ * e = s⁻¹ := by field_simp
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.mpr (mul_pos hs he).le), hf]

private theorem sec8_config_smul (D Dt : ContMetric d) (s r e : ℝ)
    (hs : 0 < s) (he : 0 < e) (z : Rd d) :
    config (D.smul e he) (Dt.smul e he) (s * e) r z =
      config D Dt s r z := by
  unfold config
  apply Prod.ext
  · funext u v
    dsimp only
    rw [D.internal_smul he]
    exact sec8_normCoord_scale s e hs he _
  apply Prod.ext
  · funext u v
    dsimp only
    rw [Dt.internal_smul he]
    exact sec8_normCoord_scale s e hs he _
  apply Prod.ext
  · funext u v
    dsimp only
    rw [D.internal_smul he]
    exact sec8_normCoord_scale s e hs he _
  · funext u v
    dsimp only
    rw [Dt.internal_smul he]
    exact sec8_normCoord_scale s e hs he _

private theorem sec8_Exc_smul (η : C(unitInterval, Rd d)) (D : ContMetric d)
    (V : Set (Rd d)) (z : Rd d) (r ϑ e : ℝ) (he : 0 < e) :
    Exc η D V z r ϑ ↔ Exc η (D.smul e he) V z r (ϑ * e) := by
  have hθ : ENNReal.ofReal (ϑ * e) =
      ENNReal.ofReal ϑ * ENNReal.ofReal e := by
    rw [mul_comm ϑ e, ENNReal.ofReal_mul he.le, mul_comm]
  have hmul (v : ℝ≥0∞) :
      ENNReal.ofReal ϑ ≤ v ↔
        ENNReal.ofReal (ϑ * e) ≤ ENNReal.ofReal e * v := by
    rw [hθ, mul_comm (ENNReal.ofReal e) v]
    exact (ENNReal.mul_le_mul_iff_left
      ((ENNReal.ofReal_pos).2 he).ne' ENNReal.ofReal_ne_top).symm
  unfold Exc
  constructor
  · rintro ⟨α, β, hab, ha, hb, hi, hv, hm⟩
    refine ⟨α, β, hab, ha, hb, hi, hv, ?_⟩
    rw [D.internal_smul]
    exact (hmul _).mp hm
  · rintro ⟨α, β, hab, ha, hb, hi, hv, hm⟩
    refine ⟨α, β, hab, ha, hb, hi, hv, ?_⟩
    rw [D.internal_smul] at hm
    exact (hmul _).mpr hm

/-- Deterministic homogeneity of the exact source event. The hypotheses are
precisely the metric and sphere-average identities supplied almost surely by
constant Weyl scaling. -/
theorem sec8_favEvent_addConst_iff
    (D Dt : DistRd d → ContMetric d) (ξ Q Cstar q R r b : ℝ)
    (hr : 0 < r) (J : ℕ) (N : ℕ → Set (Config d))
    (V : Set (Rd d)) (f : ℕ → C(Rd d, ℝ))
    (x y : Rd d) (Z : Finset (Rd d × ℕ)) (g : DistRd d) (c : ℝ)
    (hmacro : sphereAvg (addConst g c) (8 * R) 0 =
      sphereAvg g (8 * R) 0 + c)
    (hsite : ∀ site ∈ Z, sphereAvg (addConst g c) r site.1 =
      sphereAvg g r site.1 + c)
    (hD : ∀ u v : Rd d, (D (addConst g c)).1 (u, v) =
      Real.exp (ξ * c) * (D g).1 (u, v))
    (hDt : ∀ u v : Rd d, (Dt (addConst g c)).1 (u, v) =
      Real.exp (ξ * c) * (Dt g).1 (u, v))
    (hDshift : ∀ u v : Rd d,
      (D (addConst (addFun g (-F_Z f r Z)) c)).1 (u, v) =
        Real.exp (ξ * c) * (D (addFun g (-F_Z f r Z))).1 (u, v))
    (hgeo : ∃ η : C(unitInterval, Rd d), IsConstSpeedGeod (D g) x y η)
    (hgeoShift : ∃ η : C(unitInterval, Rd d),
      IsConstSpeedGeod (D (addFun g (-F_Z f r Z))) x y η) :
    g ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z ↔
      addConst g c ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z := by
  let e := Real.exp (ξ * c)
  have he : 0 < e := Real.exp_pos _
  have hm := sec8_macroS_addConst ξ Q g c R hmacro
  have hs (site : Rd d × ℕ) (hsiteZ : site ∈ Z) :=
    sec8_sNorm_addConst ξ Q g c r site.1 (hsite site hsiteZ)
  have hDm : D (addConst g c) = (D g).smul e he :=
    sec8_metric_eq_smul _ _ e he hD
  have hDtm : Dt (addConst g c) = (Dt g).smul e he :=
    sec8_metric_eq_smul _ _ e he hDt
  have hcfg (site : Rd d × ℕ) (hsiteZ : site ∈ Z) :
      config (D (addConst g c)) (Dt (addConst g c))
        (sNorm ξ Q (addConst g c) r site.1) r site.1 =
      config (D g) (Dt g) (sNorm ξ Q g r site.1) r site.1 := by
    rw [hDm, hDtm, hs site hsiteZ]
    exact sec8_config_smul _ _ _ _ _ (sNorm_pos ξ Q g hr site.1) he _
  have hsel : sec8Sel x y (D (addConst g c)).1 = sec8Sel x y (D g).1 :=
    sec8_sel_scale _ _ x y e he hD hgeo
  have hshiftField : addFun (addConst g c) (-F_Z f r Z) =
      addConst (addFun g (-F_Z f r Z)) c := addFun_addConst _ _ _
  have hselShift :
      sec8Sel x y (D (addFun (addConst g c) (-F_Z f r Z))).1 =
        sec8Sel x y (D (addFun g (-F_Z f r Z))).1 := by
    rw [hshiftField]
    exact sec8_sel_scale _ _ x y e he hDshift hgeoShift
  have hc1 : sec8C1 D Dt ξ Q Cstar q R x y g ↔
      sec8C1 D Dt ξ Q Cstar q R x y (addConst g c) := by
    unfold sec8C1
    rw [hD x y, hDt x y, hm]
    have hring : Cstar * (e * (D g).1 (x, y)) -
        q * (macroS ξ Q g R * e) =
        e * (Cstar * (D g).1 (x, y) - q * macroS ξ Q g R) := by ring
    rw [hring]
    rw [mul_comm e (Cstar * (D g).1 (x, y) - q * macroS ξ Q g R),
      mul_comm e ((Dt g).1 (x, y))]
    exact (mul_le_mul_iff_left₀ he).symm
  have hlow (site : Rd d × ℕ) (hsiteZ : site ∈ Z) :
      q * macroS ξ Q g R ≤ sNorm ξ Q g r site.1 ↔
        q * macroS ξ Q (addConst g c) R ≤
          sNorm ξ Q (addConst g c) r site.1 := by
    rw [hm, hs site hsiteZ]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_iff_left₀ (a := e) (b := q * macroS ξ Q g R)
        (c := sNorm ξ Q g r site.1) he).symm
  have hhigh (site : Rd d × ℕ) (hsiteZ : site ∈ Z) :
      sNorm ξ Q g r site.1 ≤ 2 * q * macroS ξ Q g R ↔
        sNorm ξ Q (addConst g c) r site.1 ≤
          2 * q * macroS ξ Q (addConst g c) R := by
    rw [hm, hs site hsiteZ]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (mul_le_mul_iff_left₀ (a := e) (b := sNorm ξ Q g r site.1)
        (c := 2 * q * macroS ξ Q g R) he).symm
  have hc2 : sec8C2 D Dt ξ Q q R r J N Z g ↔
      sec8C2 D Dt ξ Q q R r J N Z (addConst g c) := by
    unfold sec8C2
    constructor
    · intro h site hsiteZ
      obtain ⟨hj, hn, hlo, hhi⟩ := h site hsiteZ
      exact ⟨hj, (hcfg site hsiteZ).symm ▸ hn,
        (hlow site hsiteZ).mp hlo, (hhigh site hsiteZ).mp hhi⟩
    · intro h site hsiteZ
      obtain ⟨hj, hn, hlo, hhi⟩ := h site hsiteZ
      exact ⟨hj, (hcfg site hsiteZ) ▸ hn,
        (hlow site hsiteZ).mpr hlo, (hhigh site hsiteZ).mpr hhi⟩
  have hc3 : sec8C3 D x y r Z g ↔ sec8C3 D x y r Z (addConst g c) := by
    unfold sec8C3
    rw [hsel]
  have hc4 : sec8C4 D ξ Q b r V f x y Z g ↔
      sec8C4 D ξ Q b r V f x y Z (addConst g c) := by
    unfold sec8C4
    constructor
    · intro h site hsiteZ
      have hi := (sec8_Exc_smul
        (sec8Sel x y (D (addFun g (-F_Z f r Z))).1) (D g)
        (sec8Collector V r site.1) site.1 r
        (b * sNorm ξ Q g r site.1) e he).mp (h site hsiteZ)
      rw [hselShift, hDm, hs site hsiteZ]
      simpa only [mul_assoc] using hi
    · intro h site hsiteZ
      have hi := h site hsiteZ
      rw [hselShift, hDm, hs site hsiteZ] at hi
      apply (sec8_Exc_smul
        (sec8Sel x y (D (addFun g (-F_Z f r Z))).1) (D g)
        (sec8Collector V r site.1) site.1 r
        (b * sNorm ξ Q g r site.1) e he).mpr
      simpa only [mul_assoc] using hi
  unfold FavEvent
  simp only [mem_ofPred_eq, hc1, hc2, hc3, hc4]

/-- Lemma 8.2's constant-shift clause, simultaneously for every constant.
Every selected trap and the macroscopic scale use the same a.s. sphere-average
limits; constant Weyl scaling is simultaneous for all constants. -/
theorem lemma82_favEvent_addConst_ae
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (Cstar q R r b : ℝ) (hr : 0 < r) (hR : 0 < R)
    (J : ℕ) (N : ℕ → Set (Config d)) (V : Set (Rd d))
    (f : ℕ → C(Rd d, ℝ)) (Mf : ℝ)
    (hf : ∀ j < J, (∀ x, 0 ≤ f j x) ∧ (∀ x, f j x ≤ Mf))
    (x y : Rd d) (Z : Finset (Rd d × ℕ))
    (hJ : ∀ site ∈ Z, site.2 < J) :
    ∀ᵐ ω ∂P, ∀ c : ℝ,
      h ω ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z ↔
      addConst (h ω) c ∈ FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z := by
  have hshift : IsLGFPlusCont
      (fun ω => addFun (h ω) (-F_Z f r Z)) P :=
    hh.isLGFPlusCont.addFun measurable_const
  have hmacro : ∀ᵐ ω ∂P, ∀ c : ℝ,
      sphereAvg (addConst (h ω) c) (8 * R) 0 =
        sphereAvg (h ω) (8 * R) 0 + c := by
    filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq (by omega : 2 ≤ d)
      (mul_pos (by norm_num : (0 : ℝ) < 8) hR) 0] with ω hlim
    obtain ⟨a, ha⟩ := hlim
    intro c
    exact sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) ha c
  have hsites : ∀ᵐ ω ∂P, ∀ site ∈ Z, ∀ c : ℝ,
      sphereAvg (addConst (h ω) c) r site.1 =
        sphereAvg (h ω) r site.1 + c := by
    refine (Filter.eventually_all_finset Z).2 fun site hsiteZ => ?_
    filter_upwards [hh.ae_exists_tendsto_sphereAvgSeq
      (by omega : 2 ≤ d) hr site.1] with ω hlim
    obtain ⟨a, ha⟩ := hlim
    intro c
    exact sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) ha c
  filter_upwards [hmacro, hsites,
    hD.ae_apply_addFun_const hh.isLGFPlusCont,
    hDt.ae_apply_addFun_const hh.isLGFPlusCont,
    hD.ae_apply_addFun_const hshift,
    hD.length P h hh.isLGFPlusCont,
    lemma27_proper hd hξ hQ hD P h hh,
    lemma82_shifted_geod_exists P h hd hh hξ hQ hD hf r hJ x y]
      with ω hmacroω hsitesω hDω hDtω hDshiftω hlen hproper hgeoShift
  letI : ProperSpace (D (h ω)).Space := hproper
  have hgeo : ∃ η : C(unitInterval, Rd d), IsConstSpeedGeod (D (h ω)) x y η :=
    sec8_exists_constSpeedGeod _ hlen x y
  intro c
  apply sec8_favEvent_addConst_iff D Dt ξ Q Cstar q R r b hr J N V f x y Z
    (h ω) c (hmacroω c) (fun site hsiteZ => hsitesω site hsiteZ c)
  · intro u v
    simpa only [addFun_const] using hDω c u v
  · intro u v
    simpa only [addFun_const] using hDtω c u v
  · intro u v
    simpa only [addFun_const] using hDshiftω c u v
  · exact hgeo
  · exact hgeoShift

/-- Adding and then removing the finite perturbation leaves the selected path
literally unchanged. -/
theorem lemma82_selector_cancel (D : DistRd d → ContMetric d)
    (f : ℕ → C(Rd d, ℝ)) (r : ℝ) (Z : Finset (Rd d × ℕ))
    (g : DistRd d) (x y : Rd d) :
    sec8Sel x y (D (addFun (addFun g (F_Z f r Z)) (-F_Z f r Z))).1 =
      sec8Sel x y (D g).1 := by
  rw [addFun_F_Z_sub]

/-- The exact source event is measurable modulo null sets under a whole-space
LGF law. Its Borel representative is `FavEventBorel`. -/
theorem lemma82_favEvent_nullMeasurable
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (Cstar q R r b : ℝ) (hr : 0 < r)
    {J : ℕ} (N : ℕ → Set (Config d))
    (hN : ∀ j < J, MeasurableSet (N j))
    (V : Set (Rd d)) (hV : IsOpen V)
    (hVA : closure V ⊆ ann (0 : Rd d) 1 3)
    (f : ℕ → C(Rd d, ℝ)) (Mf : ℝ)
    (hf : ∀ j < J, (∀ x, 0 ≤ f j x) ∧ (∀ x, f j x ≤ Mf))
    (x y : Rd d) {colour : Fin d → ℤ}
    {Z : Finset (Rd d × ℕ)}
    (hZ : IsSec8LabeledSet d J r R x y colour Z) :
    NullMeasurableSet
      (h ⁻¹' FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z) P := by
  have hB : MeasurableSet
      (h ⁻¹' FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z) :=
    (measurableSet_FavEventBorel hD.measurable hDt.measurable
      ξ Q Cstar q R r b hr J N hN V hV f x y Z).preimage hh.measurable
  have heq :
      h ⁻¹' FavEventBorel D Dt ξ Q Cstar q R r b J N V f x y Z =ᵐ[P]
        h ⁻¹' FavEvent D Dt ξ Q Cstar q R r b J N V f x y Z := by
    filter_upwards [lemma82_favEvent_ae_equiv P h hd hh hξ hQ hD hDt
      Cstar q R r b hr N V hV hVA f Mf hf x y hZ] with ω hω
    exact propext hω
  exact hB.nullMeasurableSet.congr heq

end HigherDimLQGMetric

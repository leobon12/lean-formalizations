import HigherDimLQGMetric.Sec8b.Lemma85
import HigherDimLQGMetric.Sec8b.EventBridge
import HigherDimLQGMetric.CM.Basic

/-! Replace each normalized Cameron--Martin event by its raw shifted event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open Classical MeasureTheory Set Metric Filter Topology
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- For one deterministic finite perturbation, the Borel favorable event
at its normalized Cameron--Martin shift agrees almost surely with the
geometric favorable event at the unnormalized shift. -/
theorem s7b_shiftNorm_fav_equiv_ae
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsWholeSpaceLGF h P)
    (hd : 3 ≤ d) {ξ Q cs Cs q R r : ℝ}
    (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    (hR : 0 < R) (hr : 0 < r)
    {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D)
    (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    (T : Sec8TrapData d ξ cs Cs D Dt)
    (x y : Rd d) (colour : Fin d → ℤ)
    (Z : Finset (Rd d × ℕ))
    (hZ : IsSec8LabeledSet d T.J r R x y colour Z) :
    ∀ᵐ ω ∂P,
      shiftNorm (h ω) (F_Z T.f r Z) ∈
        FavEventBorel D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z ↔
      addFun (h ω) (F_Z T.f r Z) ∈
        FavEvent D Dt ξ Q Cs q R r T.b T.J T.N T.V T.f x y Z := by
  classical
  let F := F_Z T.f r Z
  let c : ℝ := -(∫ u, F u ∂(unitSphereProb d))
  let hp : Ω → DistRd d := fun ω => addFun (h ω) F
  let hn : Ω → DistRd d := fun ω => shiftNorm (h ω) F
  let hc : Ω → DistRd d := fun ω => addConst (h ω) c
  have hJ : ∀ site ∈ Z, site.2 < T.J := by
    intro site hsite
    obtain ⟨_, _, _, _, _, _, hj⟩ := hZ.1 site hsite
    exact hj
  have hplus : IsLGFPlusCont hp P :=
    hh.isLGFPlusCont.addFun measurable_const
  have hnorm : IsLGFPlusCont hn P :=
    hplus.addConst measurable_const
  have hconst : IsLGFPlusCont hc P :=
    hh.isLGFPlusCont.addConst measurable_const
  have hmacroLimit := hh.ae_exists_tendsto_sphereAvgSeq
    (by omega : 2 ≤ d) (mul_pos (by norm_num : (0 : ℝ) < 8) hR) 0
  have hsiteLimit : ∀ᵐ ω ∂P,
      ∀ site ∈ Z, ∃ a : ℝ,
        Tendsto (sphereAvgSeq (h ω) r site.1) atTop (𝓝 a) := by
    refine (Filter.eventually_all_finset Z).2 fun site _ => ?_
    exact hh.ae_exists_tendsto_sphereAvgSeq (by omega : 2 ≤ d) hr site.1
  filter_upwards [hD.length P h hh.isLGFPlusCont,
    hD.length P hp hplus, hDt.length P hp hplus,
    hD.length P hn hnorm, hDt.length P hn hnorm,
    hD.length P hc hconst,
    lemma27_proper hd hξ hQ hD P h hh,
    hD.weyl P h hh.isLGFPlusCont,
    hD.ae_apply_addFun_const hh.isLGFPlusCont,
    hD.ae_apply_addFun_const hplus,
    hDt.ae_apply_addFun_const hplus,
    hmacroLimit, hsiteLimit]
    with ω hbaseLen hplusLen htplusLen hnormLen htnormLen hconstLen
      hproper hweyl hbaseConst hplusConst htplusConst hmacroω hsiteω
  letI : ProperSpace (D (h ω)).Space := hproper
  have hFbound : ∀ u : Rd d, 0 ≤ F u ∧ F u ≤ Z.card * T.Mf := by
    intro u
    exact F_Z_nonneg_le
      (fun j hj => ⟨(T.bumps j hj).2.2.2.1,
        (T.bumps j hj).2.2.2.2.2⟩) r hJ u
  have hW : IsWeylOf ξ F (D (h ω)) (D (hp ω)) :=
    fun u v => (hweyl F u v).symm
  have hproperPlus : ProperSpace (D (hp ω)).Space := by
    have hlo : ∀ u : Rd d, 0 ≤ ξ * F u :=
      fun u => mul_nonneg hξ.le (hFbound u).1
    have hhi : ∀ u : Rd d, ξ * F u ≤ ξ * (Z.card * T.Mf) :=
      fun u => mul_le_mul_of_nonneg_left (hFbound u).2 hξ.le
    exact sec8_proper_of_bounded_weyl (D (h ω)) (D (hp ω))
      hbaseLen ξ F hW hlo hhi
  have hgeoPlus : ∃ η : C(unitInterval, Rd d),
      IsConstSpeedGeod (D (hp ω)) x y η := by
    letI : ProperSpace (D (hp ω)).Space := hproperPlus
    exact sec8_exists_constSpeedGeod _ hplusLen x y
  have hgeoBase : ∃ η : C(unitInterval, Rd d),
      IsConstSpeedGeod (D (h ω)) x y η :=
    sec8_exists_constSpeedGeod _ hbaseLen x y
  have hmacro : sphereAvg (addConst (hp ω) c) (8 * R) 0 =
      sphereAvg (hp ω) (8 * R) 0 + c := by
    obtain ⟨a, ha⟩ := hmacroω
    have haPlus := (tendsto_sphereAvgSeq_addFun_iff (h ω) F
      (8 * R) 0 a).2 ha
    exact sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) haPlus c
  have hsites : ∀ site ∈ Z,
      sphereAvg (addConst (hp ω) c) r site.1 =
        sphereAvg (hp ω) r site.1 + c := by
    intro site hsite
    obtain ⟨a, ha⟩ := hsiteω site hsite
    have haPlus := (tendsto_sphereAvgSeq_addFun_iff
      (h ω) F r site.1 a).2 ha
    exact sphereAvg_addConst_of_tendsto (by omega : 1 ≤ d) haPlus c
  have hDplusConst : ∀ u v : Rd d,
      (D (addConst (hp ω) c)).1 (u, v) =
        Real.exp (ξ * c) * (D (hp ω)).1 (u, v) := by
    intro u v
    simpa only [addFun_const] using hplusConst c u v
  have hDtplusConst : ∀ u v : Rd d,
      (Dt (addConst (hp ω) c)).1 (u, v) =
        Real.exp (ξ * c) * (Dt (hp ω)).1 (u, v) := by
    intro u v
    simpa only [addFun_const] using htplusConst c u v
  have hDbaseConst : ∀ u v : Rd d,
      (D (addConst (h ω) c)).1 (u, v) =
        Real.exp (ξ * c) * (D (h ω)).1 (u, v) := by
    intro u v
    simpa only [addFun_const] using hbaseConst c u v
  have hcancel : addFun (hp ω) (-F) = h ω := by
    dsimp only [hp, F]
    exact addFun_F_Z_sub (h ω) T.f r Z
  have hDshift : ∀ u v : Rd d,
      (D (addConst (addFun (hp ω) (-F)) c)).1 (u, v) =
        Real.exp (ξ * c) * (D (addFun (hp ω) (-F))).1 (u, v) := by
    simpa only [hcancel] using hDbaseConst
  have hraw : hp ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N
      T.V T.f x y Z ↔
      hn ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N
        T.V T.f x y Z := by
    have hconstIff := sec8_favEvent_addConst_iff D Dt ξ Q Cs q R r
      T.b hr T.J T.N T.V T.f x y Z (hp ω) c hmacro hsites
      hDplusConst hDtplusConst hDshift hgeoPlus (by
        rw [hcancel]
        exact hgeoBase)
    simpa only [hp, hn, shiftNorm, F, c] using hconstIff
  have hproperConst : ProperSpace (D (hc ω)).Space := by
    exact sec8_proper_of_metric_lower (D (h ω)) (D (hc ω))
      (Real.exp_pos (ξ * c)) (fun u v => by
        dsimp only [hc]
        rw [hDbaseConst])
  have hselConst : sec8Sel x y (D (hc ω)).1 0 = x ∧
      sec8Sel x y (D (hc ω)).1 1 = y := by
    letI : ProperSpace (D (hc ω)).Space := hproperConst
    exact sec8Sel_endpoints _ hconstLen x y
  have hnormMinus : addFun (hn ω) (-F) = hc ω := by
    dsimp only [hn, hp, hc, shiftNorm, c]
    rw [addFun_addConst, addFun_F_Z_sub]
  have haway : ∀ site ∈ Z,
      x ∉ closedBall site.1 (4 * r) ∧
      y ∉ closedBall site.1 (4 * r) := by
    intro site hs
    obtain ⟨_, _, _, _, hx, hy, _⟩ := hZ.1 site hs
    exact ⟨hx, hy⟩
  have hborel : hn ω ∈ FavEventBorel D Dt ξ Q Cs q R r T.b
      T.J T.N T.V T.f x y Z ↔
      hn ω ∈ FavEvent D Dt ξ Q Cs q R r T.b T.J T.N
        T.V T.f x y Z := by
    apply FavEventBorel_iff_FavEvent D Dt ξ Q Cs q R r T.b
      hr T.J T.N T.V T.openV T.closureV T.f x y Z (hn ω)
      hnormLen htnormLen haway
    · rw [hnormMinus]
      exact hselConst.1
    · rw [hnormMinus]
      exact hselConst.2
  exact hborel.trans hraw.symm

end HigherDimLQGMetric

import HigherDimLQGContinuity.ForcingCount.PathGeom
import HigherDimLQGContinuity.Norm.Rho
import HigherDimLQGMetric.Sec8.ExcursionMeas
import HigherDimLQGMetric.Select.InternalBorel
import HigherDimLQGMetric.Field.Measurable

/-!
# Measurability of the count events (Borel representatives)

Packet Q9, Part B `b:lem-events` ([C] l. 945, 1028–1030; NA2 item 20(b), R8, R13; ruling M34 pattern). For Borel
validity sets `S_ℓ` of the label catalogue (part (ii) of the site certificate), `countEventABor K 𝔆 S Z` is a Borel
set (`measurableSet_countEventABor`) which agrees with `A_Z` at every field whose two normalized metrics are length
metrics (`countEventA_iff_bor`): the comparison clause is closed and the barrier clause open in the metric
(compactness of the spheres), eligibility and validity are Borel through `S_ℓ` on length metrics, the canonical
geodesics are Borel (`sec8Sel`), first and last collector visits are the library's Borel hitting times
(`sec8FirstHit`, `sec8LastHit`), and internal distances in the inspections are the library's ambient Borel functions
(`measurable_internal_ambient`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-! ## First and last visits of the real-time path of a unit-interval path -/

theorem q9_realPath_mem_iff (γ : C(unitInterval, Rd d)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (F : Set (Rd d)) : s7b_realPath γ t ∈ F ↔ γ ⟨t, ht⟩ ∈ F := by
  have h := s7b_realPath_coe γ ⟨t, ht⟩
  simp only at h
  rw [h]

theorem q9_realPath_visit_iff (γ : C(unitInterval, Rd d)) (F : Set (Rd d)) :
    (∃ t ∈ Icc (0 : ℝ) 1, s7b_realPath γ t ∈ F) ↔ ∃ t : unitInterval, γ t ∈ F := by
  constructor
  · rintro ⟨t, ht, hF⟩
    exact ⟨⟨t, ht⟩, (q9_realPath_mem_iff γ ht F).1 hF⟩
  · rintro ⟨t, hF⟩
    exact ⟨t, t.2, (q9_realPath_mem_iff γ t.2 F).2 hF⟩

theorem q9_firstVisit_realPath (γ : C(unitInterval, Rd d)) {F : Set (Rd d)} (hF : IsClosed F)
    (hvis : ∃ t : unitInterval, γ t ∈ F) :
    firstVisit (s7b_realPath γ) 0 1 F = (sec8FirstHit γ F 0 : ℝ) := by
  have hmem := sec8FirstHit_mem γ F hF 0
  have hle : ∀ t : unitInterval, γ t ∈ F → sec8FirstHit γ F 0 ≤ t := fun t ht =>
    sInf_le (Or.inr ⟨show (0 : unitInterval) ≤ t from t.2.1, ht⟩)
  have ht₁F : γ (sec8FirstHit γ F 0) ∈ F := by
    rcases hmem with h1 | ⟨-, hF1⟩
    · obtain ⟨t', ht'⟩ := hvis
      have h2 := hle t' ht'
      rw [h1] at h2
      have ht'1 : t' = 1 := le_antisymm le_top h2
      rw [h1, ← ht'1]
      exact ht'
    · exact hF1
  unfold firstVisit
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨(sec8FirstHit γ F 0).2, (q9_realPath_mem_iff γ (sec8FirstHit γ F 0).2 F).2 ht₁F⟩
  · rintro t ⟨ht01, htF⟩
    exact hle ⟨t, ht01⟩ ((q9_realPath_mem_iff γ ht01 F).1 htF)

theorem q9_lastVisit_realPath (γ : C(unitInterval, Rd d)) {F : Set (Rd d)} (hF : IsClosed F)
    (hvis : ∃ t : unitInterval, γ t ∈ F) :
    lastVisit (s7b_realPath γ) 0 1 F = (sec8LastHit γ F 1 : ℝ) := by
  have hmem := sec8LastHit_mem γ F hF 1
  have hle : ∀ t : unitInterval, γ t ∈ F → t ≤ sec8LastHit γ F 1 := fun t ht =>
    le_sSup (Or.inr ⟨show t ≤ (1 : unitInterval) from t.2.2, ht⟩)
  have ht₁F : γ (sec8LastHit γ F 1) ∈ F := by
    rcases hmem with h1 | ⟨-, hF1⟩
    · obtain ⟨t', ht'⟩ := hvis
      have h2 := hle t' ht'
      rw [h1] at h2
      have ht'1 : t' = 0 := le_antisymm h2 bot_le
      rw [h1, ← ht'1]
      exact ht'
    · exact hF1
  unfold lastVisit
  apply IsGreatest.csSup_eq
  constructor
  · exact ⟨(sec8LastHit γ F 1).2, (q9_realPath_mem_iff γ (sec8LastHit γ F 1).2 F).2 ht₁F⟩
  · rintro t ⟨ht01, htF⟩
    exact hle ⟨t, ht01⟩ ((q9_realPath_mem_iff γ ht01 F).1 htF)

/-! ## Ambient Borel internal distances in balls -/

/-- A Borel function of `(metric, x, y)` equal to the internal distance in `B_r(z)` on length metrics. -/
def q9FV (z : Rd d) (r : ℝ) : C(Rd d × Rd d, ℝ) × Rd d × Rd d → ℝ≥0∞ :=
  (measurable_internal_ambient (isOpen_ball (x := z) (ε := r))).choose

theorem measurable_q9FV (z : Rd d) (r : ℝ) : Measurable (q9FV z r) :=
  (measurable_internal_ambient (isOpen_ball (x := z) (ε := r))).choose_spec.1

theorem q9FV_spec (z : Rd d) (r : ℝ) (G : ContMetric d) (hG : G.IsLength) (x y : Rd d) :
    G.internal (ball z r) x y = q9FV z r (G.1, x, y) :=
  (measurable_internal_ambient (isOpen_ball (x := z) (ε := r))).choose_spec.2 G hG x y

/-! ## The Borel events -/

/-- Borel eligibility (the source validity through the Borel sets `S`). -/
def EligBor (K : CountData d) (𝔆 : Catalogue d) (S : K.cat.Label → Set (ContMetric d × ContMetric d))
    (z : Rd d) (H : DistRd d) : Prop :=
  (∃ ℓ, (countSiteD K 𝔆.s z H, countSiteE K 𝔆.s z H) ∈ S ℓ) ∧ countUnit K 𝔆.s z H ∈ Icc 𝔆.Q (2 * 𝔆.Q) ∧
    ∃ t : unitInterval, sec8Sel K.x K.y (rho K.D H).1 t ∈ closedBall z (3 * 𝔆.s / 2)

/-- Borel trigger of the site `z` for the selection `Z` (first and last collector hits of the canonical geodesic of
`H - f_Z`, and the ambient Borel internal distance in `B_{4s}(z)`). -/
def TrigBor (K : CountData d) (𝔆 : Catalogue d) (Z : Finset (Rd d × K.cat.Label)) (z : Rd d)
    (H : DistRd d) : Prop :=
  (∃ t : unitInterval, sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1 t ∈
      annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2)) ∧
    ENNReal.ofReal K.btrig ≤ ENNReal.ofReal (countUnit K 𝔆.s z H)⁻¹ *
      q9FV z (4 * 𝔆.s) ((rho K.D H).1,
        sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1
          (sec8FirstHit (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1)
            (annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2)) 0),
        sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1
          (sec8LastHit (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1)
            (annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2)) 1))

open Classical in
/-- **The Borel representative of `A_Z`** (Part B `b:lem-events`). -/
def countEventABor (K : CountData d) (𝔆 : Catalogue d) (S : K.cat.Label → Set (ContMetric d × ContMetric d))
    (Z : Finset (Rd d × K.cat.Label)) : Set (DistRd d) :=
  {H | CompOn (rho K.E H) (rho K.D H) K.c K.ηloc K.Rsrc ∧
    (K.c - K.gΔ) * (rho K.D H).1 (K.x, K.y) ≤ (rho K.E H).1 (K.x, K.y) ∧
    (rho K.D H).1 (K.x, K.y) ≤ K.U₀ ∧
    (∀ u ∈ sphere (0 : Rd d) 8, ∀ w ∈ sphere (0 : Rd d) K.Rsrc, 2 * K.U₀ < (rho K.D H).1 (u, w)) ∧
    K.Δ ^ (-(1 / 2 : ℝ)) ≤ ((𝔆.Z.filter fun z => EligBor K 𝔆 S z H).card : ℝ) ∧
    ∀ p ∈ Z, (countSiteD K 𝔆.s p.1 H, countSiteE K 𝔆.s p.1 H) ∈ S p.2 ∧
      countUnit K 𝔆.s p.1 H ∈ Icc 𝔆.Q (2 * 𝔆.Q) ∧ TrigBor K 𝔆 Z p.1 H}

/-! ## Agreement on length metrics -/

/-- The barrier clause for length metrics (compactness of the spheres). -/
theorem q9_barrier_iff {G : ContMetric d} (hG : G.IsLength) {U₀ R : ℝ} (hU₀ : 0 ≤ U₀) :
    ENNReal.ofReal (2 * U₀) < setDistIn G univ (sphere (0 : Rd d) 8) (sphere (0 : Rd d) R) ↔
      ∀ u ∈ sphere (0 : Rd d) 8, ∀ w ∈ sphere (0 : Rd d) R, 2 * U₀ < G.1 (u, w) := by
  have hset : setDistIn G univ (sphere (0 : Rd d) 8) (sphere (0 : Rd d) R) =
      ⨅ (u ∈ sphere (0 : Rd d) 8) (w ∈ sphere (0 : Rd d) R), ENNReal.ofReal (G.1 (u, w)) := by
    unfold setDistIn
    simp only [G.internal_univ_of_isLength hG]
  rw [hset]
  constructor
  · intro h u hu w hw
    have h1 : ⨅ (u ∈ sphere (0 : Rd d) 8) (w ∈ sphere (0 : Rd d) R), ENNReal.ofReal (G.1 (u, w)) ≤
        ENNReal.ofReal (G.1 (u, w)) := iInf₂_le_of_le u hu (iInf₂_le_of_le w hw le_rfl)
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).1 (h.trans_le h1)
  · intro h
    rcases ((sphere (0 : Rd d) 8) ×ˢ (sphere (0 : Rd d) R)).eq_empty_or_nonempty with he | hne
    · have : ⨅ (u ∈ sphere (0 : Rd d) 8) (w ∈ sphere (0 : Rd d) R), ENNReal.ofReal (G.1 (u, w)) = ⊤ := by
        simp only [iInf_eq_top]
        intro u hu w hw
        exact absurd (Set.mk_mem_prod hu hw) (he ▸ Set.notMem_empty _)
      rw [this]
      exact ENNReal.ofReal_lt_top
    · obtain ⟨p₀, hp₀, hmin⟩ := ((isCompact_sphere (0 : Rd d) 8).prod
        (isCompact_sphere (0 : Rd d) R)).exists_isMinOn hne (G.continuous_apply.continuousOn)
      have hlow : ENNReal.ofReal (G.1 p₀) ≤
          ⨅ (u ∈ sphere (0 : Rd d) 8) (w ∈ sphere (0 : Rd d) R), ENNReal.ofReal (G.1 (u, w)) :=
        le_iInf₂ fun u hu => le_iInf₂ fun w hw =>
          ENNReal.ofReal_le_ofReal (hmin (Set.mk_mem_prod hu hw))
      refine lt_of_lt_of_le ?_ hlow
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by linarith)).2 (h p₀.1 hp₀.1 p₀.2 hp₀.2)

section Agree

variable {K : CountData d} {𝔆 : Catalogue d} {S : K.cat.Label → Set (ContMetric d × ContMetric d)}

theorem q9_eligible_iff_bor
    (hS : ∀ ℓ (D E : ContMetric d), D.IsLength → E.IsLength → ((D, E) ∈ S ℓ ↔ K.cat.Source ℓ D E))
    {H : DistRd d} (hDl : (rho K.D H).IsLength) (hEl : (rho K.E H).IsLength) (z : Rd d) :
    IsEligible K 𝔆 z H ↔ EligBor K 𝔆 S z H := by
  have hDl' : (countSiteD K 𝔆.s z H).IsLength := q9SiteNorm_isLength hDl _ _ _
  have hEl' : (countSiteE K 𝔆.s z H).IsLength := q9SiteNorm_isLength hEl _ _ _
  unfold IsEligible EligBor
  have h1 : (∃ ℓ, K.cat.Source ℓ (countSiteD K 𝔆.s z H) (countSiteE K 𝔆.s z H)) ↔
      ∃ ℓ, (countSiteD K 𝔆.s z H, countSiteE K 𝔆.s z H) ∈ S ℓ :=
    exists_congr fun ℓ => (hS ℓ _ _ hDl' hEl').symm
  have h3 := q9_realPath_visit_iff (sec8Sel K.x K.y (rho K.D H).1) (closedBall z (3 * 𝔆.s / 2))
  rw [h1]
  exact and_congr_right fun _ => and_congr_right fun _ => h3

theorem q9_trigger_iff_bor (hs : 0 < 𝔆.s) {Z : Finset (Rd d × K.cat.Label)} {H : DistRd d}
    (hDl : (rho K.D H).IsLength) (z : Rd d) :
    PassesTrigger (countSiteD K 𝔆.s z H)
      (q9SitePath (q9Path K.D K.x K.y (addFun H (-selBump K 𝔆.s Z))) z 𝔆.s) 0 1 K.btrig ↔
      TrigBor K 𝔆 Z z H := by
  set γ := sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1 with hγ
  set F := annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) with hFdef
  have hF : IsClosed F := isClosed_annCl _ _ _
  have hP : q9Path K.D K.x K.y (addFun H (-selBump K 𝔆.s Z)) = s7b_realPath γ := rfl
  rw [hP]
  have hvisit_iff : (∃ t ∈ Icc (0 : ℝ) 1, q9SitePath (s7b_realPath γ) z 𝔆.s t ∈ siteC d) ↔
      ∃ t : unitInterval, γ t ∈ F := by
    rw [← q9_realPath_visit_iff γ F]
    exact exists_congr fun t => and_congr_right fun _ => q9_sitePath_mem_siteC_iff hs t
  unfold PassesTrigger TrigBor
  rw [hvisit_iff]
  refine and_congr_right fun hvis => ?_
  have hsets : {t | t ∈ Icc (0 : ℝ) 1 ∧ q9SitePath (s7b_realPath γ) z 𝔆.s t ∈ siteC d} =
      {t | t ∈ Icc (0 : ℝ) 1 ∧ s7b_realPath γ t ∈ F} := by
    ext t
    exact and_congr_right fun _ => q9_sitePath_mem_siteC_iff hs t
  have hfirst : firstVisit (q9SitePath (s7b_realPath γ) z 𝔆.s) 0 1 (siteC d) = (sec8FirstHit γ F 0 : ℝ) := by
    rw [← q9_firstVisit_realPath γ hF hvis]
    unfold firstVisit
    rw [hsets]
  have hlast : lastVisit (q9SitePath (s7b_realPath γ) z 𝔆.s) 0 1 (siteC d) = (sec8LastHit γ F 1 : ℝ) := by
    rw [← q9_lastVisit_realPath γ hF hvis]
    unfold lastVisit
    rw [hsets]
  rw [hfirst, hlast]
  have hS : 0 < countUnit K 𝔆.s z H := countUnit_pos K hs z H
  change ENNReal.ofReal K.btrig ≤ (q9SiteNorm (rho K.D H) z 𝔆.s (countUnit K 𝔆.s z H)).internal (siteB d) _ _ ↔ _
  rw [q9SiteNorm_internal hs hS, q9Aff_image_siteB hs, q9Aff_apply_sitePath hs, q9Aff_apply_sitePath hs,
    s7b_realPath_coe, s7b_realPath_coe, q9FV_spec z (4 * 𝔆.s) _ hDl]

open Classical in
/-- **`A_Z` agrees with its Borel representative** at every field whose normalized metrics are length metrics. -/
theorem countEventA_iff_bor (hs : 0 < 𝔆.s)
    (hS : ∀ ℓ (D E : ContMetric d), D.IsLength → E.IsLength → ((D, E) ∈ S ℓ ↔ K.cat.Source ℓ D E))
    (hU₀ : 0 ≤ K.U₀) {Z : Finset (Rd d × K.cat.Label)} {H : DistRd d}
    (hDl : (rho K.D H).IsLength) (hEl : (rho K.E H).IsLength) :
    H ∈ countEventA K 𝔆 Z ↔ H ∈ countEventABor K 𝔆 S Z := by
  have hDl' : ∀ z, (countSiteD K 𝔆.s z H).IsLength := fun z => q9SiteNorm_isLength hDl _ _ _
  have hEl' : ∀ z, (countSiteE K 𝔆.s z H).IsLength := fun z => q9SiteNorm_isLength hEl _ _ _
  have hfilter : (𝔆.Z.filter fun z => IsEligible K 𝔆 z H) = 𝔆.Z.filter fun z => EligBor K 𝔆 S z H :=
    Finset.filter_congr fun z _ => q9_eligible_iff_bor hS hDl hEl z
  simp only [countEventA, countEventB, countEventABor, mem_ofPred_eq, hfilter, q9_barrier_iff hDl hU₀,
    and_assoc]
  refine and_congr_right fun _ => ?_
  refine and_congr_right fun _ => ?_
  refine and_congr_right fun _ => ?_
  refine and_congr_right fun _ => ?_
  refine and_congr_right fun _ => ?_
  refine forall₂_congr fun p _ => ?_
  rw [hS p.2 _ _ (hDl' p.1) (hEl' p.1), q9_trigger_iff_bor hs hDl p.1]

end Agree

/-! ## Measurability -/

section Meas

variable {K : CountData d} {𝔆 : Catalogue d} {S : K.cat.Label → Set (ContMetric d × ContMetric d)}

theorem measurable_countUnit (K : CountData d) (s : ℝ) (z : Rd d) : Measurable (countUnit K s z) := by
  unfold countUnit scaleS
  exact measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
    (measurable_sphereAvg_left _ _)))

theorem q9_measurable_siteNorm_rho {D : DistRd d → ContMetric d} (hD : Measurable D) {s : ℝ} (hs : 0 < s)
    (z : Rd d) {U : DistRd d → ℝ} (hU : Measurable U) (hUpos : ∀ H, 0 < U H) :
    Measurable fun H => q9SiteNorm (rho D H) z s (U H) := by
  let a : C(Rd d × Rd d, Rd d × Rd d) := ⟨fun p => (s • p.1 + z, s • p.2 + z), by fun_prop⟩
  have hpre : Measurable (fun H => (rho D H).1.comp a) :=
    (ContinuousMap.continuous_precomp a).measurable.comp (measurable_subtype_coe.comp (measurable_rho hD))
  have hamb : Measurable (fun H => (U H)⁻¹ • (rho D H).1.comp a) := hU.inv.smul hpre
  have hEmb : MeasurableEmbedding ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe (measurableSet_isContinuousMetric_select d)
  apply (hEmb.measurable_comp_iff).mp
  convert hamb using 1
  funext H
  simp only [Function.comp_apply, q9SiteNorm_eq hs (hUpos H)]
  rfl

theorem measurable_countSiteD (hD : Measurable K.D) {s : ℝ} (hs : 0 < s) (z : Rd d) :
    Measurable fun H => countSiteD K s z H :=
  q9_measurable_siteNorm_rho hD hs z (measurable_countUnit K s z) fun H => countUnit_pos K hs z H

theorem measurable_countSiteE (hE : Measurable K.E) {s : ℝ} (hs : 0 < s) (z : Rd d) :
    Measurable fun H => countSiteE K s z H :=
  q9_measurable_siteNorm_rho hE hs z (measurable_countUnit K s z) fun H => countUnit_pos K hs z H

theorem q9_measurable_rho_coe {D : DistRd d → ContMetric d} (hD : Measurable D) :
    Measurable fun H => (rho D H).1 :=
  measurable_subtype_coe.comp (measurable_rho hD)

theorem q9_measurable_rho_apply {D : DistRd d → ContMetric d} (hD : Measurable D) (p : Rd d × Rd d) :
    Measurable fun H => (rho D H).1 p :=
  (ContinuousMap.measurable_eval p).comp (q9_measurable_rho_coe hD)

theorem q9_measurableSet_compOn {D E : DistRd d → ContMetric d} (hD : Measurable D) (hE : Measurable E)
    (c η R : ℝ) : MeasurableSet {H | CompOn (rho E H) (rho D H) c η R} := by
  let T : Set (C(Rd d × Rd d, ℝ) × C(Rd d × Rd d, ℝ)) :=
    ⋂ x ∈ closedBall (0 : Rd d) R, ⋂ y ∈ closedBall (0 : Rd d) R, {p | p.1 (x, y) ≤ c * p.2 (x, y) + η}
  have hT : IsClosed T := by
    refine isClosed_biInter fun x _ => isClosed_biInter fun y _ => isClosed_le ?_ ?_
    · exact (continuous_eval_const (x, y)).comp continuous_fst
    · exact continuous_const.mul ((continuous_eval_const (x, y)).comp continuous_snd) |>.add
        continuous_const
  have heq : {H | CompOn (rho E H) (rho D H) c η R} =
      (fun H => ((rho E H).1, (rho D H).1)) ⁻¹' T := by
    ext H
    simp only [CompOn, T, mem_ofPred_eq, mem_preimage, mem_iInter]
  rw [heq]
  exact ((q9_measurable_rho_coe hE).prodMk (q9_measurable_rho_coe hD)) hT.measurableSet

theorem q9_measurableSet_barrier {D : DistRd d → ContMetric d} (hD : Measurable D) (U₀ R : ℝ) :
    MeasurableSet {H | ∀ u ∈ sphere (0 : Rd d) 8, ∀ w ∈ sphere (0 : Rd d) R, 2 * U₀ < (rho D H).1 (u, w)} := by
  have hopen : IsOpen {f : C(Rd d × Rd d, ℝ) |
      MapsTo f ((sphere (0 : Rd d) 8) ×ˢ (sphere (0 : Rd d) R)) (Ioi (2 * U₀))} :=
    ContinuousMap.isOpen_setOfPred_mapsTo ((isCompact_sphere _ _).prod (isCompact_sphere _ _)) isOpen_Ioi
  have heq : {H | ∀ u ∈ sphere (0 : Rd d) 8, ∀ w ∈ sphere (0 : Rd d) R, 2 * U₀ < (rho D H).1 (u, w)} =
      (fun H => (rho D H).1) ⁻¹' {f : C(Rd d × Rd d, ℝ) |
        MapsTo f ((sphere (0 : Rd d) 8) ×ˢ (sphere (0 : Rd d) R)) (Ioi (2 * U₀))} := by
    ext H
    simp only [mem_ofPred_eq, mem_preimage, MapsTo, mem_prod, mem_Ioi, Prod.forall]
    constructor
    · intro h u w hp
      exact h u hp.1 w hp.2
    · intro h u hu w hw
      exact h u w ⟨hu, hw⟩
  rw [heq]
  exact (q9_measurable_rho_coe hD) hopen.measurableSet

theorem q9_measurableSet_pathHits {F : Set (Rd d)} (hF : IsClosed F) :
    MeasurableSet {γ : C(unitInterval, Rd d) | ∃ t : unitInterval, γ t ∈ F} := by
  have h := isClosed_sec8_path_hits_closed F hF univ isClosed_univ
  simp only [mem_univ, true_and] at h
  exact h.measurableSet

theorem q9_measurable_selPath {D : DistRd d → ContMetric d} (hD : Measurable D) (x y : Rd d)
    (g : C(Rd d, ℝ)) : Measurable fun H => sec8Sel x y (rho D (addFun H g)).1 :=
  (measurable_sec8Sel x y).comp ((q9_measurable_rho_coe hD).comp (measurable_addFun_left g))

theorem q9_measurableSet_eligBor (hD : Measurable K.D) (hE : Measurable K.E) (hs : 0 < 𝔆.s)
    (hSm : ∀ ℓ, MeasurableSet (S ℓ)) (z : Rd d) : MeasurableSet {H | EligBor K 𝔆 S z H} := by
  have : Countable K.cat.Label := by
    let _ := K.cat.fintypeLabel
    infer_instance
  have h1 : MeasurableSet {H | ∃ ℓ, (countSiteD K 𝔆.s z H, countSiteE K 𝔆.s z H) ∈ S ℓ} := by
    simp only [ofPred_exists]
    exact MeasurableSet.iUnion fun ℓ =>
      ((measurable_countSiteD hD hs z).prodMk (measurable_countSiteE hE hs z)) (hSm ℓ)
  have h2 : MeasurableSet {H | countUnit K 𝔆.s z H ∈ Icc 𝔆.Q (2 * 𝔆.Q)} :=
    (measurable_countUnit K 𝔆.s z) measurableSet_Icc
  have h3 : MeasurableSet {H | ∃ t : unitInterval, sec8Sel K.x K.y (rho K.D H).1 t ∈ closedBall z (3 * 𝔆.s / 2)} := by
    have hm : Measurable fun H => sec8Sel K.x K.y (rho K.D H).1 :=
      (measurable_sec8Sel _ _).comp (q9_measurable_rho_coe hD)
    exact hm (q9_measurableSet_pathHits isClosed_closedBall)
  exact h1.inter (h2.inter h3)

theorem q9_measurableSet_trigBor (hD : Measurable K.D) (Z : Finset (Rd d × K.cat.Label)) (z : Rd d) :
    MeasurableSet {H | TrigBor K 𝔆 Z z H} := by
  set F := annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) with hFdef
  have hF : IsClosed F := isClosed_annCl _ _ _
  have hγ := q9_measurable_selPath hD K.x K.y (-selBump K 𝔆.s Z)
  have h1 := hγ (q9_measurableSet_pathHits hF)
  have hfirst : Measurable fun H =>
      (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1)
        (sec8FirstHit (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1) F 0) :=
    continuous_eval.measurable.comp (hγ.prodMk ((measurable_sec8FirstHit F hF 0).comp hγ))
  have hlast : Measurable fun H =>
      (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1)
        (sec8LastHit (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1) F 1) :=
    continuous_eval.measurable.comp (hγ.prodMk ((measurable_sec8LastHit F hF 1).comp hγ))
  have hval : Measurable fun H => ENNReal.ofReal (countUnit K 𝔆.s z H)⁻¹ *
      q9FV z (4 * 𝔆.s) ((rho K.D H).1,
        (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1)
          (sec8FirstHit (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1) F 0),
        (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1)
          (sec8LastHit (sec8Sel K.x K.y (rho K.D (addFun H (-selBump K 𝔆.s Z))).1) F 1)) :=
    (ENNReal.measurable_ofReal.comp (measurable_countUnit K 𝔆.s z).inv).mul
      ((measurable_q9FV z (4 * 𝔆.s)).comp ((q9_measurable_rho_coe hD).prodMk (hfirst.prodMk hlast)))
  exact h1.inter (measurableSet_le measurable_const hval)

open Classical in
theorem q9_measurableSet_card_le {P : Rd d → DistRd d → Prop} (hP : ∀ z, MeasurableSet {H | P z H})
    (T : Finset (Rd d)) (r : ℝ) : MeasurableSet {H | r ≤ ((T.filter fun z => P z H).card : ℝ)} := by
  have hfun : (fun H => ((T.filter fun z => P z H).card : ℝ)) =
      fun H => ∑ z ∈ T, if P z H then (1 : ℝ) else 0 := by
    funext H
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hm : Measurable fun H => ((T.filter fun z => P z H).card : ℝ) := by
    rw [hfun]
    exact Finset.measurable_sum _ fun z _ => Measurable.ite (hP z) measurable_const measurable_const
  exact measurableSet_le measurable_const hm

open Classical in
/-- **`A_Z` has a Borel representative** (Part B `b:lem-events`). -/
theorem measurableSet_countEventABor (hD : Measurable K.D) (hE : Measurable K.E) (hs : 0 < 𝔆.s)
    (hSm : ∀ ℓ, MeasurableSet (S ℓ)) (Z : Finset (Rd d × K.cat.Label)) :
    MeasurableSet (countEventABor K 𝔆 S Z) := by
  have h1 := q9_measurableSet_compOn hD hE K.c K.ηloc K.Rsrc
  have h2 : MeasurableSet {H | (K.c - K.gΔ) * (rho K.D H).1 (K.x, K.y) ≤ (rho K.E H).1 (K.x, K.y)} :=
    measurableSet_le (measurable_const.mul (q9_measurable_rho_apply hD _)) (q9_measurable_rho_apply hE _)
  have h3 : MeasurableSet {H | (rho K.D H).1 (K.x, K.y) ≤ K.U₀} :=
    measurableSet_le (q9_measurable_rho_apply hD _) measurable_const
  have h4 := q9_measurableSet_barrier hD K.U₀ K.Rsrc
  have h5 := q9_measurableSet_card_le (fun z => q9_measurableSet_eligBor hD hE hs hSm z) 𝔆.Z (K.Δ ^ (-(1 / 2 : ℝ)))
  have h6 : MeasurableSet {H | ∀ p ∈ Z, (countSiteD K 𝔆.s p.1 H, countSiteE K 𝔆.s p.1 H) ∈ S p.2 ∧
      countUnit K 𝔆.s p.1 H ∈ Icc 𝔆.Q (2 * 𝔆.Q) ∧ TrigBor K 𝔆 Z p.1 H} := by
    simp only [ofPred_forall]
    refine Finset.measurableSet_biInter Z fun p _ => ?_
    exact (((measurable_countSiteD hD hs p.1).prodMk (measurable_countSiteE hE hs p.1)) (hSm p.2)).inter
      (((measurable_countUnit K 𝔆.s p.1) measurableSet_Icc).inter (q9_measurableSet_trigBor hD Z p.1))
  exact h1.inter (h2.inter (h3.inter (h4.inter (h5.inter h6))))

end Meas

end HigherDimLQGContinuity

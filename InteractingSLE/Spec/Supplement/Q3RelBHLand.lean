/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Q3RelBHChart
import InteractingSLE.Spec.Supplement.RelTrans

/-!
# The boundary-hitting mean identification with a retained chart landing off a finite set: landing and transition

Packet PROVE-Q3-REL. PROVE-RELTRANS's landing and transition layer (`RelTransLand`) for a retained chart whose
inverse lands only off a finite set `Sb` (`IsRetainedChartOff`). A real point `z` of the joint chart is **good**
(`IsGoodPt`) when its relative landing point `F̄̃_u(z)` is not one of the exceptional points. The good real points form
an open set (`isOpen_goodPt`); on it the joint landing map is continuous (`continuousOn_landing`), and every statement
of `RelTransLand` holds at good points, with the same proofs. Points of the relative hull image are good as soon as the
exceptional points lie off the closed relative hull (`goodPt_of_mem_closure`).

Deterministic. Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Supp8.Q3Rel

open BHMean (jointInv jointFwd jointLift jointChart)
open RelTrans (nhdsWithin_H_neBot_of_mem_Hbar ofReal_mem_Hbar transBdry)

/-- **A good point of the joint chart's boundary**: its relative landing point is not an exceptional point. -/
def IsGoodPt (Sb : Finset ℝ) (Wr : ℝ → ℝ) (u : ℝ) (z : ℂ) : Prop :=
  ∀ b ∈ Sb, extendFrom H (fwdMapInv Wr u) z ≠ (b : ℂ)

section Landing

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- The retained inverse `Ψi` has a limit at every point of `ℍ̄` other than the exceptional points. -/
theorem exists_tendsto_retainedInv (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) {y : ℂ} (hy : y ∈ Hbar)
    (hyb : ∀ b ∈ Sb, y ≠ (b : ℂ)) : ∃ p, Tendsto Ψi (𝓝[H] y) (𝓝 p) := by
  by_cases hyH : y ∈ H
  · exact ⟨Ψi y, (hΨ.diff_inv.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds hyH)).tendsto.mono_left
      nhdsWithin_le_nhds⟩
  · have hyim : y.im = 0 := le_antisymm (not_lt.1 hyH) hy
    have hyr : y = (y.re : ℂ) := Complex.ext (by simp) (by simp [hyim])
    obtain ⟨p, hp⟩ := hΨ.inv_lands y.re fun hb => hyb _ hb hyr
    rw [← hyr] at hp
    exact ⟨p, hp⟩

/-- **The joint parametrization lands at every good point of `ℍ̄`**, at `ℓ(z) = Ψ̄i(F̄̃_u(z))`. -/
theorem tendsto_jointInv (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) {z : ℂ} (hz : z ∈ Hbar) (hg : IsGoodPt Sb Wr u z) :
    Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 (extendFrom H (jointInv Ψi Wr u) z)) ∧
      Tendsto Ψi (𝓝[H] (extendFrom H (fwdMapInv Wr u) z)) (𝓝 (extendFrom H (jointInv Ψi Wr u) z)) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) z with hycdef
  have hycb : yc ∈ Hbar := BHMean.extendFrom_mem_Hbar hηr hWr hWr0 hu hz
  have hlimF : Tendsto (fwdMapInv Wr u) (𝓝[H] z) (𝓝[H] yc) :=
    tendsto_nhdsWithin_iff.2 ⟨(hηr.hasBdryLimits hWr hWr0 hu).tendsto hz,
      eventually_nhdsWithin_of_forall fun v hv => QuantumZipper.RS.fwdMapInv_mem_H hWr hWr0 hu hv⟩
  obtain ⟨p, hp⟩ := exists_tendsto_retainedInv hΨ hycb hg
  have hJ : Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p) := hp.comp hlimF
  have he : extendFrom H (jointInv Ψi Wr u) z = p := extendFrom_eq (by rw [closure_H]; exact hz) hJ
  rw [he]
  exact ⟨hJ, hp⟩

/-- **The joint landing map is continuous at the good points of `ℍ̄`.** -/
theorem continuousOn_extendFrom_jointInv (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    ContinuousOn (extendFrom H (jointInv Ψi Wr u)) {z | z ∈ Hbar ∧ IsGoodPt Sb Wr u z} :=
  continuousOn_extendFrom (fun z hz => by rw [closure_H]; exact hz.1) fun _ hz =>
    ⟨_, (tendsto_jointInv hΨ hWr hWr0 hηr hu hz.1 hz.2).1⟩

/-- **The good real points form an open set.** -/
theorem isOpen_goodPt (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    IsOpen {s : ℝ | IsGoodPt Sb Wr u (s : ℂ)} := by
  have hc : Continuous fun s : ℝ => extendFrom H (fwdMapInv Wr u) (s : ℂ) :=
    (hηr.hasBdryLimits hWr hWr0 hu).continuousOn.comp_continuous Complex.continuous_ofReal ofReal_mem_Hbar
  have e : {s : ℝ | IsGoodPt Sb Wr u (s : ℂ)} =
      ⋂ b ∈ Sb, {s : ℝ | extendFrom H (fwdMapInv Wr u) (s : ℂ) ≠ (b : ℂ)} := by
    ext s
    simp only [IsGoodPt, mem_ofPred_eq, mem_iInter]
  rw [e]
  exact isOpen_biInter_finset fun b _ => isOpen_ne_fun hc continuous_const

/-- The joint landing map along the good real points is continuous. -/
theorem continuousOn_landing (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    ContinuousOn (fun s : ℝ => extendFrom H (jointInv Ψi Wr u) (s : ℂ)) {s : ℝ | IsGoodPt Sb Wr u (s : ℂ)} :=
  (continuousOn_extendFrom_jointInv hΨ hWr hWr0 hηr hu).comp Complex.continuous_ofReal.continuousOn
    fun s hs => ⟨ofReal_mem_Hbar s, hs⟩

/-- **The set `U` of good real points landing off the closed retained set is open.** -/
theorem isOpen_landOff (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) :
    IsOpen {s : ℝ | IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A} :=
  (continuousOn_landing hΨ hWr hWr0 hηr hu).isOpen_inter_preimage (isOpen_goodPt hWr hWr0 hηr hu)
    isClosed_closure.isOpen_compl

/-- **A real landing point of the joint parametrization is not a point of the joint complement.** -/
theorem extendFrom_jointInv_notMem (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z.im = 0) (hg : IsGoodPt Sb Wr u z) :
    extendFrom H (jointInv Ψi Wr u) z ∉ H \ (A ∪ fwdHull w t) := by
  intro hp
  have hzb : z ∈ Hbar := show (0 : ℝ) ≤ z.im from hz.ge
  have hJ := (tendsto_jointInv hΨ hWr hWr0 hηr hu hzb hg).1
  have hc : ContinuousAt (jointFwd Ψ Wr u) (extendFrom H (jointInv Ψi Wr u) z) :=
    (differentiableAt_jointFwd hΨ hw ht hWr hWr0 hu hK hd hp).continuousAt
  have h1 : Tendsto (fun y => jointFwd Ψ Wr u (jointInv Ψi Wr u y)) (𝓝[H] z)
      (𝓝 (jointFwd Ψ Wr u (extendFrom H (jointInv Ψi Wr u) z))) := hc.tendsto.comp hJ
  have h2 : Tendsto (fun y => jointFwd Ψ Wr u (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 z) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun y hy =>
      (jointFwd_jointInv hΨ hw ht hWr hWr0 hu hK hd hy).symm)
  have := nhdsWithin_H_neBot_of_mem_Hbar hzb
  have he := tendsto_nhds_unique h1 h2
  have hpos : (0 : ℝ) < (jointFwd Ψ Wr u (extendFrom H (jointInv Ψi Wr u) z)).im :=
    jointFwd_mem hΨ hw ht hWr hWr0 hu hK hd hp
  rw [he, hz] at hpos
  exact lt_irrefl _ hpos

/-- Off the closed retained set, a real good landing point is not a point of `ℍ ∖ K_t`. -/
theorem notMem_compl_fwdHull_of_landOff (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z.im = 0) (hg : IsGoodPt Sb Wr u z) (hzA : extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    extendFrom H (jointInv Ψi Wr u) z ∉ H \ fwdHull w t := fun hp =>
  extendFrom_jointInv_notMem hΨ hw ht hWr hWr0 hηr hu hK hd hz hg
    ⟨hp.1, fun h => h.elim (fun hA => hzA (subset_closure hA)) hp.2⟩

/-- **Around a good point landing off `cl A`, every real point is good and lands off `cl A`.** -/
theorem exists_ball_land (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hWr : Continuous Wr)
    (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) {x : ℝ} (hg : IsGoodPt Sb Wr u (x : ℂ))
    (hx : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A) :
    ∃ r > 0, ∀ z ∈ ball (x : ℂ) r, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ closure A := by
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 (isOpen_landOff hΨ hWr hWr0 hηr hu) x ⟨hg, hx⟩
  refine ⟨r, hr, fun z hz hz0 => ?_⟩
  have hzr : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [hz0])
  have hmem : z.re ∈ ball x r := by
    rw [mem_ball, ← Complex.isometry_ofReal.dist_eq, ← hzr]
    exact hz
  have h : IsGoodPt Sb Wr u (z.re : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (z.re : ℂ) ∉ closure A := hsub hmem
  rw [← hzr] at h
  exact h

/-- The landing hypothesis of `exists_int_jointChart` on such a ball. -/
theorem hland_of_ball (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) {x r : ℝ}
    (hball : ∀ z ∈ ball (x : ℂ) r, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    ∀ z ∈ ball (x : ℂ) r, z.im = 0 → ∃ p, p ∉ H \ fwdHull w t ∧ Tendsto (jointInv Ψi Wr u) (𝓝[H] z) (𝓝 p) :=
  fun z hz hz0 => ⟨_, notMem_compl_fwdHull_of_landOff hΨ hw ht hWr hWr0 hηr hu hK hd hz0 (hball z hz hz0).1
    (hball z hz hz0).2, (tendsto_jointInv hΨ hWr hWr0 hηr hu (show (0 : ℝ) ≤ z.im from hz0.ge)
      (hball z hz hz0).1).1⟩

/-- **Points of the relative hull image are good** when the exceptional points lie off the closed relative hull. -/
theorem goodPt_of_mem_closure (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u)) {z : ℂ}
    (hzK : extendFrom H (fwdMapInv Wr u) z ∈ closure (fwdHull Wr u)) : IsGoodPt Sb Wr u z :=
  fun b hb he => hSbK b hb (he ▸ hzK)

/-- **On the relative hull image the joint parametrization lands on the closed explored hull.** -/
theorem extendFrom_jointInv_mem_closure (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    (hSbK : ∀ b ∈ Sb, (b : ℂ) ∉ closure (fwdHull Wr u))
    {z : ℂ} (hz : z ∈ Hbar) (hzK : extendFrom H (fwdMapInv Wr u) z ∈ closure (fwdHull Wr u)) :
    extendFrom H (jointInv Ψi Wr u) z ∈ closure (fwdHull w t) :=
  landing_mem_closure hΨ hw ht hK hd hWr hu hzK
    (tendsto_jointInv hΨ hWr hWr0 hηr hu hz (goodPt_of_mem_closure hSbK hzK)).2

/-- **Off the relative hull image**, a good landing point off the closed retained set is a real point off the closed
explored hull (the argument of `retained_side`). -/
theorem landing_real_of_notMem (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (ht : 0 ≤ t)
    (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u)
    (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A)) {x : ℝ}
    (hg : IsGoodPt Sb Wr u (x : ℂ))
    (hy : extendFrom H (fwdMapInv Wr u) (x : ℂ) ∉ closure (fwdHull Wr u))
    (hpA : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A) :
    (extendFrom H (jointInv Ψi Wr u) (x : ℂ)).im = 0 ∧
      extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure (fwdHull w t) := by
  set yc : ℂ := extendFrom H (fwdMapInv Wr u) (x : ℂ) with hycdef
  set p : ℂ := extendFrom H (jointInv Ψi Wr u) (x : ℂ) with hpdef
  have hyim : yc.im = 0 := BHMean.im_extendFrom_eq_zero_of_notMem_closure hηr hWr hWr0 hu hy
  have hp : Tendsto Ψi (𝓝[H] yc) (𝓝 p) := (tendsto_jointInv hΨ hWr hWr0 hηr hu (ofReal_mem_Hbar x) hg).2
  have hycb : yc ∈ Hbar := show (0 : ℝ) ≤ yc.im from hyim.ge
  have := nhdsWithin_H_neBot_of_mem_Hbar hycb
  have hpbar : p ∈ Hbar := by
    rw [← closure_H]
    exact mem_closure_of_tendsto hp (eventually_nhdsWithin_of_forall fun v hv => (hΨ.inv_mem v hv).1)
  have hpC : p ∉ H \ A := notMem_compl_of_tendsto_inv hΨ hyim hp
  have hpre : p.im = 0 :=
    le_antisymm (not_lt.1 fun hpos => hpC ⟨hpos, fun h => hpA (subset_closure h)⟩) hpbar
  refine ⟨hpre, fun hpK => ?_⟩
  have hpr : p = (p.re : ℂ) := Complex.ext (by simp) (by simp [hpre])
  obtain ⟨x', hx'⟩ := hΨ.fwd_lands p.re (by rw [← hpr]; exact hpA)
  rw [← hpr] at hx'
  have hpw : Tendsto Ψi (𝓝[H] yc) (𝓝[H \ A] p) :=
    tendsto_nhdsWithin_iff.2 ⟨hp, eventually_nhdsWithin_of_forall fun v hv => hΨ.inv_mem v hv⟩
  have h1 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] yc) (𝓝 (x' : ℂ)) := hx'.comp hpw
  have h2 : Tendsto (fun v => Ψ (Ψi v)) (𝓝[H] yc) (𝓝 yc) :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' (eventually_nhdsWithin_of_forall fun v hv =>
      (hΨ.fwd_inv v hv).symm)
  have hx'y : (x' : ℂ) = yc := tendsto_nhds_unique h1 h2
  apply hy
  have hKsub : fwdHull w t ⊆ H \ A := BHMean.fwdHull_subset_compl hd hw ht
  have hNeK : (𝓝[fwdHull w t] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hpK
  have h3 : Tendsto Ψ (𝓝[fwdHull w t] p) (𝓝 (x' : ℂ)) := hx'.mono_left (nhdsWithin_mono p hKsub)
  rw [← hx'y]
  exact mem_closure_of_tendsto h3 (eventually_nhdsWithin_of_forall fun z hz => hK ▸ mem_image_of_mem Ψ hz)

end Landing

/-! ### The transition and its boundary values -/

section Transition

variable {A : Set ℂ} {Ψ Ψi LΨ : ℂ → ℂ} {Sb : Finset ℝ} {w Wr : ℝ → ℝ} {η ηr : ℝ → ℂ} {t u : ℝ}

/-- **The transition has a real limit** at every good real point landing off the closed retained set, and the inverse
explored map sends it to the joint landing point. -/
theorem exists_tendsto_transition (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {z : ℂ} (hz : z.im = 0) (hg : IsGoodPt Sb Wr u z) (hzA : extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    ∃ v : ℂ, v.im = 0 ∧ extendFrom H (fwdMapInv w t) v = extendFrom H (jointInv Ψi Wr u) z ∧
      Tendsto (fun y => fwdMap w t (jointInv Ψi Wr u y)) (𝓝[H] z) (𝓝 v) := by
  have hzb : z ∈ Hbar := show (0 : ℝ) ≤ z.im from hz.ge
  have hc := isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd
  have hCt : ((jointChart Ψ Ψi LΨ Wr u).dom : Set ℂ) ⊆ H \ fwdHull w t := by
    rw [coe_dom_jointChart hΨ hw ht hWr hWr0 hu hK hd]
    exact fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩
  obtain ⟨v, hv, hFv, hT⟩ := Sec7.Lemma71O.exists_tendsto_fwdMap_comp hη hw hw0 ht hc hCt hzb
    (tendsto_jointInv hΨ hWr hWr0 hηr hu hzb hg).1
  exact ⟨v, Sec7.Lemma71O.im_eq_zero_of_land hw hw0 ht hv hFv
    (notMem_compl_fwdHull_of_landOff hΨ hw ht hWr hWr0 hηr hu hK hd hz hg hzA), hFv, hT⟩

/-- **The transition is real-boundary conformal** on a half-disc whose real points are good and land off the closed
retained set (Schwarz reflection across the real diameter). -/
theorem isRealBoundaryConformal_transition (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w)
    (hw0 : w 0 = 0) (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hηr : IsLoewnerTrace Wr ηr) (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u)
    (hd : Disjoint (closure (fwdHull w t)) (closure A)) {x r : ℝ}
    (hball : ∀ z ∈ ball (x : ℂ) r, z.im = 0 →
      IsGoodPt Sb Wr u z ∧ extendFrom H (jointInv Ψi Wr u) z ∉ closure A) :
    R16.IsRealBoundaryConformal (extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y)) x r :=
  Sec7.Lemma71O.isRealBoundaryConformal_extendFrom (c := jointChart Ψ Ψi LΨ Wr u)
    (D := H \ fwdHull w t)
    (isConformal_jointChart hΨ hw ht hWr hWr0 hu hK hd) (coe_dom_jointChart hΨ hw ht hWr hWr0 hu hK hd)
    (fun y hy => ⟨hy.1, fun h => hy.2 (Or.inr h)⟩)
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hw ht) (QuantumZipper.FwdHolo.injOn_fwdMap hw ht)
    (fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hw ht hz) fun z hz hz0 => by
      obtain ⟨v, hv, -, hT⟩ := exists_tendsto_transition hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hz0
        (hball z hz hz0).1 (hball z hz hz0).2
      exact ⟨v, hv, hT⟩

/-- **The boundary values of the transition have a positive derivative** at every good point landing off
`cl A`. -/
theorem hasDerivAt_transBdry (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {x : ℝ} (hg : IsGoodPt Sb Wr u (x : ℂ)) (hx : extendFrom H (jointInv Ψi Wr u) (x : ℂ) ∉ closure A) :
    ∃ d > 0, HasDerivAt (transBdry Ψi w Wr t u) d x := by
  obtain ⟨r, hr, hball⟩ := exists_ball_land hΨ hWr hWr0 hηr hu hg hx
  have hrbc := isRealBoundaryConformal_transition hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd hball
  set φ : ℂ → ℂ := extendFrom H fun y => fwdMap w t (jointInv Ψi Wr u y) with hφdef
  have hxb : (x : ℂ) ∈ ball (x : ℂ) r := mem_ball_self hr
  have hdiff : HasDerivAt (schwarzReflect φ) (deriv (schwarzReflect φ) x) x :=
    ((hrbc.differentiableOn_schwarzReflect).differentiableAt (isOpen_ball.mem_nhds hxb)).hasDerivAt
  have heq : transBdry Ψi w Wr t u = fun s : ℝ => (schwarzReflect φ s).re := by
    funext s
    simp only [transBdry, schwarzReflect, Complex.ofReal_im, le_refl, ↓reduceIte, hφdef]
  refine ⟨(deriv (schwarzReflect φ) x).re, (hrbc.deriv_schwarzReflect_pos hxb).2, ?_⟩
  rw [heq]
  exact hdiff.real_of_complex

/-- **The boundary values of the transition increase strictly on every interval of good points landing off
`cl A`.** -/
theorem strictMonoOn_transBdry (hΨ : IsRetainedChartOff A Ψ Ψi LΨ Sb) (hw : Continuous w) (hw0 : w 0 = 0)
    (hη : IsLoewnerTrace w η) (ht : 0 ≤ t) (hWr : Continuous Wr) (hWr0 : Wr 0 = 0) (hηr : IsLoewnerTrace Wr ηr)
    (hu : 0 ≤ u) (hK : Ψ '' fwdHull w t = fwdHull Wr u) (hd : Disjoint (closure (fwdHull w t)) (closure A))
    {a b : ℝ}
    (hU : ∀ s ∈ Icc a b, IsGoodPt Sb Wr u (s : ℂ) ∧ extendFrom H (jointInv Ψi Wr u) (s : ℂ) ∉ closure A) :
    StrictMonoOn (transBdry Ψi w Wr t u) (Icc a b) := by
  have hder : ∀ s ∈ Icc a b, ∃ d > 0, HasDerivAt (transBdry Ψi w Wr t u) d s := fun s hs =>
    hasDerivAt_transBdry hΨ hw hw0 hη ht hWr hWr0 hηr hu hK hd (hU s hs).1 (hU s hs).2
  refine strictMonoOn_of_deriv_pos (convex_Icc a b) (fun s hs => ?_) (fun s hs => ?_)
  · obtain ⟨d, -, hd'⟩ := hder s hs
    exact hd'.continuousAt.continuousWithinAt
  · obtain ⟨d, hd0, hd'⟩ := hder s (interior_subset hs)
    rw [hd'.deriv]
    exact hd0

end Transition

end InteractingSLE.Supp8.Q3Rel

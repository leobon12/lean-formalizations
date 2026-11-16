/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermProcMain
import InteractingSLE.Spec.RealContact.Hit

/-!
# The base event of the completed second path and its good samples

Packet PROVE-RC-TERM, second run (ruling R124). For an own time `N` of the second path and a capped version `ηc₂` of
it (cap `capR 0 N`):

* `rightReal x k`: the closed set of real points at least `1/(k+1)` to the right of `x`;
* **`baseEv`**: the second lifetime is at most `N`, the first lifetime is positive, the second version ends at a real
  point left of `x₂`, and the second version has no real point right of `x₁` on `[0, N]`;
* **`measurableSet_baseEv`**: it is an event of the retained σ-algebra `retSigma76 … 0 N` (lifetime records, capped
  coordinates, hits of closed sets);
* **`ae_isTermGood_of_baseEv`**: almost surely every sample of the base event is good (`Term.IsTermGood`): the
  hypotheses of `Term.isKSample_of_facts` hold for the versions (W5 — the sealed `IsFlowLine.stays_right_of_lt` —, the
  contact rule `Hit.ae_contact_cases`, W0a, Aux. lemma 25);
* **`ae_mem_baseEv_of_trigger`**: almost surely the trigger of the path statement with `ζ₂ ≤ N` lies in the base event
  (`Term.real_of_trigger`).

Uses the closed inputs W5, W0a and the contact rule only (R48-neutral).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.RealContact

namespace Term

open Restart Restart.RetAux79 Supp7 Exist.Staged Exist.StagedLaw Sec2.Assembly Sec7.Lemma76F RLC.AStopProc

/-! ### The base event -/

/-- The closed set of real points at least `1/(k+1)` to the right of `x`. -/
def rightReal (x : ℝ) (k : ℕ) : Set ℂ := {z | z.im = 0 ∧ x + 1 / ((k : ℝ) + 1) ≤ z.re}

theorem isClosed_rightReal (x : ℝ) (k : ℕ) : IsClosed (rightReal x k) :=
  (isClosed_eq Complex.continuous_im continuous_const).inter (isClosed_le continuous_const Complex.continuous_re)

theorem rightReal_nonempty (x : ℝ) (k : ℕ) : (rightReal x k).Nonempty :=
  ⟨((x + 1 / ((k : ℝ) + 1) : ℝ) : ℂ), ofReal_im _, by rw [ofReal_re]⟩

theorem exists_mem_rightReal {x : ℝ} {z : ℂ} (him : z.im = 0) (hre : x < z.re) : ∃ k : ℕ, z ∈ rightReal x k := by
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.2 hre)
  exact ⟨k, him, by linarith⟩

section Base

variable {Ω : Type u}

/-- **The base event** of the completed second path at own time `N` (see the module docstring). -/
def baseEv (N : ℝ≥0) (ηc₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞) (x₁ x₂ : ℝ) : Set Ω :=
  {ω | lifeRec (ζ₂ ω) N ≠ ⊤} ∩ ({ω | lifeRec (ζ₁ ω) ((0 : ℝ≥0) : ℝ≥0∞) = ⊤} ∩
    ({ω | (ηc₂ ω N).im = 0} ∩ ({ω | (ηc₂ ω N).re < x₂} ∩
      ⋂ k : ℕ, {ω | ∃ s ≤ N, ηc₂ ω s ∈ rightReal x₁ k}ᶜ)))

variable [mΩ : MeasurableSpace Ω] {P : Measure Ω} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {x₁ x₂ : ℝ}

/-- **The base event is an event of the retained σ-algebra at `(0, N)`.** -/
theorem measurableSet_baseEv (hζ₁ : Measurable ζ₁) (hζ₂ : Measurable ζ₂) {N : ℝ≥0} {ηc₂ : Ω → ℝ≥0 → ℂ}
    (hc₂ : ∀ ω, Continuous (ηc₂ ω)) (hmc₂ : ∀ s, Measurable fun ω => ηc₂ ω s)
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s)) :
    MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] (baseEv N ηc₂ ζ₁ ζ₂ x₁ x₂) := by
  have hN : Measurable[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] fun ω => ηc₂ ω N :=
    measurable_capped_right_retSigma76 hc₂ hmc₂ hag₂ le_rfl
  have h1 : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] {ω | lifeRec (ζ₂ ω) N ≠ ⊤} :=
    (measurable_lifeRec_retSigma76_right P η₁ η₂ ζ₁ ζ₂ hζ₂ 0 N (measurableSet_singleton ⊤)).compl
  have h2 : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] {ω | lifeRec (ζ₁ ω) ((0 : ℝ≥0) : ℝ≥0∞) = ⊤} :=
    measurable_lifeRec_retSigma76_left P η₁ η₂ ζ₁ ζ₂ hζ₁ 0 N (measurableSet_singleton ⊤)
  have h3 : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] {ω | (ηc₂ ω N).im = 0} :=
    (Complex.measurable_im.comp hN) (measurableSet_singleton 0)
  have h4 : MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] {ω | (ηc₂ ω N).re < x₂} :=
    measurableSet_lt (Complex.measurable_re.comp hN) measurable_const
  have h5 : ∀ k : ℕ, MeasurableSet[retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N] {ω | ∃ s ≤ N, ηc₂ ω s ∈ rightReal x₁ k} := by
    intro k
    have h := @measurableSet_inter_exists_mem Ω (retSigma76 P η₁ η₂ ζ₁ ζ₂ 0 N) univ MeasurableSet.univ
      (fun ω s => ηc₂ ω (min s N))
      (fun s => measurable_capped_right_retSigma76 hc₂ hmc₂ hag₂ (min_le_right s N)) (fun _ => N)
      measurable_const (fun ω _ => ((hc₂ ω).comp (continuous_id.min continuous_const)).continuousOn)
      (rightReal x₁ k) (isClosed_rightReal x₁ k) (rightReal_nonempty x₁ k)
    have e : {ω | ∃ s ≤ N, ηc₂ ω s ∈ rightReal x₁ k} =
        univ ∩ {ω | ∃ s ≤ N, ηc₂ ω (min s N) ∈ rightReal x₁ k} := by
      ext ω
      constructor
      · rintro ⟨s, hs, hm⟩
        exact ⟨trivial, s, hs, by rwa [min_eq_left hs]⟩
      · rintro ⟨-, s, hs, hm⟩
        exact ⟨s, hs, by rwa [min_eq_left hs] at hm⟩
    rw [e]
    exact h
  exact h1.inter (h2.inter (h3.inter (h4.inter (MeasurableSet.iInter fun k => (h5 k).compl))))

end Base

/-! ### Good samples -/

section Good

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {η₁ η₂ : Ω → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω → ℝ≥0∞} {κ : ℝ} {b : ℝ → ℝ}
  {jumps : Finset ℝ} {x₁ x₂ θ₁ θ₂ : ℝ}

/-- **The pathwise facts of the two flow lines used below, almost surely** (W5, the contact rule, W0a, injectivity,
the closed half-plane, the good first path). -/
theorem ae_pathFacts (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps) (hx : x₂ ≤ x₁)
    (hD : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ))
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂) :
    ∀ᵐ ω ∂P, InjOn (η₂ ω) {t | (t : ℝ≥0∞) ≤ ζ₂ ω} ∧ IsPathGood (η₁ ω) (ζ₁ ω) x₁ ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → 0 ≤ (η₁ ω t).im) ∧
      (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω → HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) ∧
      (∀ x t : ℝ≥0, (x : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) ≤ ζ₂ ω → 0 < t → η₁ ω x = η₂ ω t →
        (t : ℝ≥0∞) = ζ₂ ω) ∧
      (x₂ < x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω →
        (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂) := by
  have hθ := Supp7.lt_of_weight hκ hκ4 hD
  have hw0a : ∀ᵐ ω ∂P, x₂ < x₁ → 0 < ζ₁ ω → 0 < ζ₂ ω →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₂ ω → η₂ ω t ≠ x₁) ∧ ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁ ω s ≠ x₂ := by
    by_cases hlt : x₂ < x₁
    · filter_upwards [Supp7.w0aStatement κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hlt hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂]
        with ω hω _ h1 h2
      exact hω h1 h2
    · exact Eventually.of_forall fun ω h' => absurd h' hlt
  filter_upwards [Theorem15.ae_injOn_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₂,
    ae_isPathGood_of_isFlowLine Theorem15.aux25Statement hκ hκ4 hη₁, Supp7.ae_im_nonneg_of_isFlowLine hη₁,
    (IsFlowLine.stays_right_of_lt hκ hκ4 b jumps hb hx hθ hh hη₁ hη₂).1,
    Hit.ae_contact_cases hκ hκ4 hb hx hD hh hη₁ hη₂, hw0a] with ω hinj₂ hpg him hord hcc hw
  exact ⟨hinj₂, hpg, him, hord, fun x t hx' ht ht0 he => (hcc x t hx' ht ht0 he).2.1, hw⟩

/-- **Almost surely every sample of the base event is good** (see the module docstring). -/
theorem ae_isTermGood_of_baseEv (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁)
    (hD : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ))
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {c : BoundaryWord} {g : Ω → DistOn upperHalfPlaneOpens} {E : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : ∀ ω, IsRegularDriver (E ω)) (hE2 : ∀ ω, (E ω).2 = ζ₂ ω)
    (hfl : IsFlowLineDriver κ c.fn c.jumps θ₂ P g (fun s ω => (E ω).1 s) (fun ω => (E ω).2))
    (htrace : ∀ᵐ ω ∂P, IsGeneratingTrace (E ω).1 (ζ₂ ω) (fun t => η₂ ω t - x₂))
    {N : ℝ≥0} {η₁' : Ω → ℝ≥0 → ℂ}
    (ha₁ : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s = η₁ ω s)
    {ηc₂ : Ω → ℝ≥0 → ℂ} (hc₂ : ∀ ω, Continuous (ηc₂ ω))
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s)) :
    ∀ᵐ ω ∂P, ω ∈ baseEv N ηc₂ ζ₁ ζ₂ x₁ x₂ → IsTermGood N E ηc₂ η₁' ζ₁ x₁ x₂ ω := by
  filter_upwards [ae_pathFacts hκ hκ4 hb hx hD hh hη₁ hη₂, ae_isDrvGood_of_isFlowLineDriver hκ ⊤ hreg hfl,
    htrace, ha₁, hag₂] with ω hfacts hgood htr e₁ e₂ hω
  obtain ⟨hinj₂, hpg, him, hord, hcc, hw⟩ := hfacts
  obtain ⟨hfin, hpos, htim, htre, hno⟩ := hω
  -- the lifetimes
  have hle : ζ₂ ω ≤ N := by
    by_contra hlt
    exact hfin ((lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).2 (not_le.1 hlt))
  have hζ₁pos : 0 < ζ₁ ω := by
    have := (lifeRec_eq_top_iff_of_ne_top (ζ := ζ₁ ω) (ENNReal.coe_ne_top (r := 0))).1 hpos
    simpa using this
  have hfin₂ : ζ₂ ω ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  set T : ℝ≥0 := (ζ₂ ω).toNNReal with hTdef
  have hTζ : (T : ℝ≥0∞) = ζ₂ ω := ENNReal.coe_toNNReal hfin₂
  have hTE : (T : ℝ≥0∞) = (E ω).2 := by rw [hE2]; exact hTζ
  have hTN : T ≤ N := by
    have : (T : ℝ≥0∞) ≤ N := hTζ ▸ hle
    exact_mod_cast this
  have hleE : (E ω).2 ≤ N := by rw [hE2]; exact hle
  -- the record
  have hrec : pRec N E ω = termRec (E ω) := recOf_coe_eq_top hleE
  have hU : pU N E ω = rdrv (termRec (E ω)) := by
    unfold pU
    rw [hrec]
  have hpT : pT N E ω = T := by
    unfold pT
    rw [hrec, termRec_stop, hE2]
  -- the second version
  have hcap : ∀ s : ℝ≥0, capTime (capR 0 N) (ζ₂ ω) s = min s T := by
    intro s
    unfold capTime
    rw [min_eq_left (hle.trans (ENNReal.coe_le_coe.2 (lt_capR_right 0 N).le))]
  have hv₂ : ∀ s : ℝ≥0, ηc₂ ω s = η₂ ω (min s T) := fun s => by rw [e₂ s, hcap s]
  have hv₂le : ∀ s : ℝ≥0, s ≤ T → ηc₂ ω s = η₂ ω s := fun s hs => by rw [hv₂ s, min_eq_left hs]
  have hv₂E : ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ (E ω).2 → ηc₂ ω s = η₂ ω s := fun s hs =>
    hv₂le s (by
      have : (s : ℝ≥0∞) ≤ (T : ℝ≥0∞) := hTE ▸ hs
      exact_mod_cast this)
  have hη : IsGeneratingTrace (E ω).1 (E ω).2 (fun t => η₂ ω t - (x₂ : ℂ)) := by rw [hE2]; exact htr
  have h₂0 : η₂ ω 0 = x₂ := sub_eq_zero.1 hη.1
  have hηc : IsGeneratingTrace (E ω).1 (E ω).2 (fun t => ηc₂ ω t - (x₂ : ℂ)) :=
    isGeneratingTrace_congr_le hη fun t ht => by
      show ηc₂ ω t - (x₂ : ℂ) = η₂ ω t - (x₂ : ℂ)
      rw [hv₂E t ht]
  have hinjc : InjOn (ηc₂ ω) {t | (t : ℝ≥0∞) ≤ (E ω).2} := by
    intro s hs t ht hst
    rw [hv₂E s hs, hv₂E t ht] at hst
    exact hinj₂ (by rw [← hE2]; exact hs) (by rw [← hE2]; exact ht) hst
  -- the tip
  have htipN : ηc₂ ω N = ηc₂ ω T := by rw [hv₂ N, min_eq_right hTN, hv₂le T le_rfl]
  set e : ℝ := (ηc₂ ω N).re with hedef
  have htip : ηc₂ ω T = (e : ℂ) := by
    rw [← htipN]
    exact Complex.ext (by simp [hedef]) (by simpa using htim)
  have hex : e < x₂ := htre
  have hTpos : 0 < T := by
    by_contra h0
    have hT0 : T = 0 := le_antisymm (not_lt.1 h0) zero_le
    have : ηc₂ ω T = (x₂ : ℂ) := by rw [hT0, hv₂le 0 (by rw [hT0]), h₂0]
    rw [htip] at this
    have : e = x₂ := by exact_mod_cast this
    exact hex.ne this
  have hζ₂pos : 0 < ζ₂ ω := by
    rw [← hTζ]
    exact_mod_cast hTpos
  -- no real point beyond the first seed, and never at the first seed
  have hreal : ∀ t ≤ T, (ηc₂ ω t).im = 0 → (ηc₂ ω t).re ≤ x₁ := by
    intro t ht him0
    by_contra hgt
    obtain ⟨k, hk⟩ := exists_mem_rightReal him0 (not_le.1 hgt)
    exact (mem_iInter.1 hno k) ⟨t, ht.trans hTN, hk⟩
  have hne : ∀ t : ℝ≥0, 0 < t → t ≤ T → ηc₂ ω t ≠ x₁ := by
    intro t ht0 htT he
    rw [hv₂le t htT] at he
    have htζ : (t : ℝ≥0∞) ≤ ζ₂ ω := hTζ ▸ ENNReal.coe_le_coe.2 htT
    rcases hx.lt_or_eq with hlt | heq
    · exact (hw hlt hζ₁pos hζ₂pos).1 t htζ he
    · rw [← heq, ← h₂0] at he
      exact ht0.ne' (hinj₂ htζ (show ((0 : ℝ≥0) : ℝ≥0∞) ≤ ζ₂ ω from zero_le) he)
  -- the first version
  obtain ⟨hinj₁, w, hwc, hw0, hgen₁⟩ := hpg
  have hgen₁' : IsGeneratingTrace w (ζ₁ ω) (fun t => η₁' ω t - (x₁ : ℂ)) :=
    isGeneratingTrace_congr_le hgen₁ fun t ht => by
      show η₁' ω t - (x₁ : ℂ) = η₁ ω t - (x₁ : ℂ)
      rw [e₁ t ht]
  have hinj₁' : InjOn (η₁' ω) {t | (t : ℝ≥0∞) ≤ ζ₁ ω} := by
    intro s hs t ht hst
    rw [e₁ s hs, e₁ t ht] at hst
    exact hinj₁ hs ht hst
  have hpg' : IsPathGood (η₁' ω) (ζ₁ ω) x₁ := ⟨hinj₁', w, hwc, hw0, hgen₁'⟩
  have hbar' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ₁ ω → 0 ≤ (η₁' ω t).im := fun t ht => by
    rw [e₁ t ht]
    exact him t ht
  have hord' : ∀ a : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → ∀ c : ℝ≥0, c < T →
      HasOrderedProperCompletions (η₁' ω) a (ηc₂ ω) c := by
    intro a ha c hc
    have hcζ : (c : ℝ≥0∞) < ζ₂ ω := hTζ ▸ ENNReal.coe_lt_coe.2 hc
    refine Sec7.HasOrderedProperCompletions.congr_prefix (fun t ht => ?_) (fun t ht => ?_) (hord a c ha hcζ)
    · exact (e₁ t ((ENNReal.coe_le_coe.2 ht).trans ha.le)).symm
    · exact (hv₂le t (ht.trans hc.le)).symm
  have hcont' : ∀ x t : ℝ≥0, (x : ℝ≥0∞) < ζ₁ ω → t ≤ T → 0 < t → η₁' ω x = ηc₂ ω t → t = T := by
    intro x t hx' ht ht0 he
    rw [e₁ x hx'.le, hv₂le t ht] at he
    have := hcc x t hx' (hTζ ▸ ENNReal.coe_le_coe.2 ht) ht0 he
    rw [← hTζ] at this
    exact_mod_cast this
  have hseed' : x₂ < x₁ → ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → η₁' ω s ≠ x₂ := fun hlt s hs => by
    rw [e₁ s hs]
    exact (hw hlt hζ₁pos hζ₂pos).2 s hs
  have hdg : LocalExt.IsDrvGood (recHist (termRec (E ω))) :=
    hgood (by rw [min_eq_right le_top, hE2]; exact hfin₂)
  have hK := isKSample_of_facts hx (hreg ω) hdg hTE hηc hinjc htip hex hreal hne hgen₁' hwc hw0 hinj₁' hbar'
    hord' hζ₁pos hcont' hseed'
  refine ⟨hleE, ⟨e - x₂, w, sub_neg.2 hex, ?_⟩, hpg', fun s hs => ?_, hc₂ ω⟩
  · rw [hU, hpT]
    exact hK
  · rw [hpT] at hs ⊢
    rw [hv₂ s, min_eq_right hs, hv₂le T le_rfl]

/-- **Almost surely the trigger of the path statement with `ζ₂ ≤ N` lies in the base event.** -/
theorem ae_mem_baseEv_of_trigger (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hx : x₂ ≤ x₁)
    (hD : κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ))
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂)
    {N : ℝ≥0} {ηc₂ : Ω → ℝ≥0 → ℂ}
    (hag₂ : ∀ᵐ ω ∂P, ∀ s, ηc₂ ω s = η₂ ω (capTime (capR 0 N) (ζ₂ ω) s)) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (e : ℝ), (T : ℝ≥0∞) = ζ₂ ω → η₂ ω T = (e : ℂ) → e < x₂ →
      (∃ (s : ℝ≥0) (y : ℝ), (s : ℝ≥0∞) < ζ₁ ω ∧ η₁ ω s = (y : ℂ) ∧ y ≤ e) → T ≤ N →
      ω ∈ baseEv N ηc₂ ζ₁ ζ₂ x₁ x₂ := by
  obtain ⟨_, _, _, _, _, _, -, -, htr₂⟩ := id hη₂
  filter_upwards [ae_pathFacts hκ hκ4 hb hx hD hh hη₁ hη₂, hag₂, htr₂] with ω hfacts e₂ htr T e hTζ htip hex
    ⟨s, y, hs, hy, hye⟩ hTN
  obtain ⟨hinj₂, hpg, him, hord, hcc, hw⟩ := hfacts
  have h₂0 : η₂ ω 0 = x₂ := sub_eq_zero.1 htr.1
  have h₁0 : η₁ ω 0 = x₁ := sub_eq_zero.1 hpg.2.choose_spec.2.2.1
  have hle : ζ₂ ω ≤ N := hTζ ▸ ENNReal.coe_le_coe.2 hTN
  have hcap : ∀ r : ℝ≥0, capTime (capR 0 N) (ζ₂ ω) r = min r T := by
    intro r
    unfold capTime
    rw [min_eq_left (hle.trans (ENNReal.coe_le_coe.2 (lt_capR_right 0 N).le)), ← hTζ, ENNReal.toNNReal_coe]
  have hv₂ : ∀ r : ℝ≥0, ηc₂ ω r = η₂ ω (min r T) := fun r => by rw [e₂ r, hcap r]
  have hreal := real_of_trigger (ζ := ζ₁ ω) hx h₁0 h₂0 htip hex
    (fun a ha c hc => hord a c ha (hTζ ▸ ENNReal.coe_lt_coe.2 hc))
    (fun x t hx' ht ht0 he => by
      have := hcc x t hx' (hTζ ▸ ENNReal.coe_le_coe.2 ht) ht0 he
      rw [← hTζ] at this
      exact_mod_cast this) hs hy hye
  refine ⟨?_, ?_, ?_, ?_, mem_iInter.2 fun k => ?_⟩
  · exact fun htop => (not_lt.2 hle) ((lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).1 htop)
  · refine (lifeRec_eq_top_iff_of_ne_top ENNReal.coe_ne_top).2 ?_
    exact lt_of_le_of_lt (by simp) hs
  · show (ηc₂ ω N).im = 0
    rw [hv₂ N, min_eq_right hTN, htip, ofReal_im]
  · show (ηc₂ ω N).re < x₂
    rw [hv₂ N, min_eq_right hTN, htip, ofReal_re]
    exact hex
  · rintro ⟨r, -, him0, hre⟩
    rw [hv₂ r] at him0 hre
    have h1 := hreal (min r T) (min_le_right _ _) him0
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith

end Good

end Term

end InteractingSLE.RealContact

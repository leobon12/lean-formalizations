/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71NOuter
import InteractingSLE.Spec.Sec7.Lemma613
import InteractingSLE.Spec.Sec7.SideHeightBoxProb
import InteractingSLE.Spec.Sec7.Lemma71MMain

/-!
# Lemma 7.1's side limits: the outer side limits of the pocket chart almost surely

Packet PROVE-LEMMA71N (specification Remark 6.7, `source/spec/p145-192.md` L566–L590). On a pocket construction over
a three-curve space (`Lemma71K.IsPocketConstruction`, `Lemma72B.IsThreeCurveSpace`), with a branch shift that is almost
surely the inherited branch (`IsPocketBranch`), the pocket chart has the outer side limits (`OuterSideLimit`) almost
surely, for every harmonic representative of the mean of the complete outer curves:

* `explored_stopsβ`, `explored_stopsα`: the explored sets of the three curves at the stops `![q, 0, 0]`, `![0, q, 0]`
  are the walls' stopped prefixes (`wallPrefix`);
* `ae_exists_isPocketFrame`: the pathwise pocket frame (`IsPocketFrame`) holds almost surely;
* **`ae_outerSideLimit`**: Proposition 3.8 for the complete outer union against each wall's prefix at every rational
  stop (`SideHeightBox.ae_tendsto_sub_of_locals`, the explored sets of the three curves being local and determined by
  the field), the single-curve side heights of each wall (`Lemma613.sideHeight_of_map`, with the determination map of
  the §4.2 reference), and the pathwise assembly `outerSideLimit_of_heights`.

Conditional helper (on the §4.2 reference `Lemma71H.Cond44ReferenceStatement`, an input of the three-curve space
itself, and on the branch `IsPocketBranch`); it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec7.Lemma71N

open QuantumZipper (H Hbar chiC)
open LocalSets Sec6

section Stops

variable {Ω : Type*}

/-- The stops of the left wall's prefix alone (curves ordered `β, α, γ`). -/
abbrev stopsβ (q : ℚ≥0) : Fin 3 → ℝ≥0∞ := ![((q : ℝ≥0) : ℝ≥0∞), 0, 0]

/-- The stops of the right wall's prefix alone. -/
abbrev stopsα (q : ℚ≥0) : Fin 3 → ℝ≥0∞ := ![0, ((q : ℝ≥0) : ℝ≥0∞), 0]

theorem setOf_le_zero : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ 0} = {0} := by
  ext t
  simp only [mem_ofPred_eq, nonpos_iff_eq_zero, ENNReal.coe_eq_zero, mem_singleton_iff]

theorem explored_stopsβ (β α γ : Ω → ℝ≥0 → ℂ) (q : ℚ≥0) (ω : Ω) (hα0 : (α ω 0).im = 0)
    (hγ0 : (γ ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => stopsβ q i) ω = wallPrefix (β ω) q := by
  unfold explored wallPrefix
  rw [Three.iUnion_fin_three]
  simp only [Three.threeCurves, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, setOf_le_zero, image_singleton]
  ext z
  simp only [mem_inter_iff, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨(h | rfl) | rfl, hz⟩
    · exact ⟨h, hz⟩
    · exact absurd hz (by show ¬ 0 < (α ω 0).im; rw [hα0]; exact lt_irrefl 0)
    · exact absurd hz (by show ¬ 0 < (γ ω 0).im; rw [hγ0]; exact lt_irrefl 0)
  · rintro ⟨h, hz⟩
    exact ⟨Or.inl (Or.inl h), hz⟩

theorem explored_stopsα (β α γ : Ω → ℝ≥0 → ℂ) (q : ℚ≥0) (ω : Ω) (hβ0 : (β ω 0).im = 0)
    (hγ0 : (γ ω 0).im = 0) :
    explored (Three.threeCurves β α γ) (fun i _ => stopsα q i) ω = wallPrefix (α ω) q := by
  unfold explored wallPrefix
  rw [Three.iUnion_fin_three]
  simp only [Three.threeCurves, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, setOf_le_zero, image_singleton]
  ext z
  simp only [mem_inter_iff, mem_union, mem_singleton_iff]
  constructor
  · rintro ⟨(rfl | h) | rfl, hz⟩
    · exact absurd hz (by show ¬ 0 < (β ω 0).im; rw [hβ0]; exact lt_irrefl 0)
    · exact ⟨h, hz⟩
    · exact absurd hz (by show ¬ 0 < (γ ω 0).im; rw [hγ0]; exact lt_irrefl 0)
  · rintro ⟨h, hz⟩
    exact ⟨Or.inl (Or.inr h), hz⟩

/-- The capped curve `t ↦ η(min t q)` has the same prefix up to `q`. -/
theorem image_capped_eq (η : ℝ≥0 → ℂ) (q : ℝ≥0) :
    (fun t => η (min t q)) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} = η '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ q} := by
  refine image_congr fun t ht => ?_
  have : t ≤ q := by exact_mod_cast ht
  simp only [min_eq_left this]

end Stops

/-! ### The outer side limits almost surely -/

section Prob

variable {κ θ₁ θ₂ a b : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {β α γ : Ω → ℝ≥0 → ℂ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
  {C : Ω → Set ℂ} {c : Ω → Chart} {γ' : Ω → ℝ → ℂ}

omit [IsProbabilityMeasure P] in
/-- **The pathwise pocket frame holds almost surely** on a pocket construction over a three-curve space. -/
theorem ae_exists_isPocketFrame (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : Lemma71K.IsPocketConstruction P β α γ C c γ') :
    ∀ᵐ ω ∂P, ∃ (Ψ : ℂ → ℂ) (a' b' : ℝ), IsPocketFrame (β ω) (α ω) (C ω) (c ω) Ψ a' b' := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hae⟩ := hS'
  have hpc' := hpc
  obtain ⟨-, -, hconf, hdom, -⟩ := hpc'
  filter_upwards [hae, Lemma71L.ae_pocketGood hS hpc] with ω hω hg
  obtain ⟨-, -, -, -, -, -, hβα, hsβ, hsα, -⟩ := hω
  obtain ⟨-, -, -, hb, hfr, a', b', Ψ, hM, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, -⟩ := hg
  exact ⟨Ψ, a', b', hsβ, hsα, hβα, hb, hM, hconf ω, hdom ω, hΨc, hΨi, hΨH, hΨ0, hΨinf, hΨeq, hfr⟩

/-- **Proposition 6.1 for the two outer curves in the pocket chart, almost surely** (Remark 6.7; the pocket's
two-curve result). On a pocket construction over a three-curve space, with a branch shift `n` that is almost surely the
inherited branch (`IsPocketBranch`), for every version `gT` of the local-set mean of the complete outer curves:
almost surely, for every harmonic representative `vT` of `gT`, the shifted pocket chart has the outer side limits with
the heights `λ − θ₂χ` (left wall `β`, its right side) and `−λ − θ₁χ` (right wall `α`, its left side). The named input
is the §4.2 reference (the determination of each outer flow line, `Lemma613.exists_map_of_cond44`); Proposition 3.8
is `SideHeightBox.ae_tendsto_sub_of_locals` and the single-curve heights `Lemma613.sideHeight_of_map`, at every
rational stop. Conditional helper (on the branch and the §4.2 reference). -/
theorem ae_outerSideLimit (href : Lemma71H.Cond44ReferenceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : θ₁ < 0) (hθ₂ : 0 < θ₂) (ha : sleLambda κ - π * chiC κ + θ₂ * chiC κ ≤ a)
    (hb : sleLambda κ - θ₁ * chiC κ ≤ b) (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : Lemma71K.IsPocketConstruction P β α γ C c γ') {n : Ω → ℤ}
    (hN : ∀ᵐ ω ∂P, IsPocketBranch (β ω) (α ω) (c ω) (n ω)) {gT : Ω → DistOn upperHalfPlaneOpens}
    (hgT : IsLocalSetMean (explored (Three.threeCurves β α γ) fun i _ => Three.outerStops i)
      (WholeField.centredField h u₀) P gT) :
    ∀ᵐ ω ∂P, ∀ vT : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd vT (H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω) →
      (∀ ψ : TestOn upperHalfPlaneOpens,
        tsupport ψ ⊆ H \ explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω →
          gT ω ψ = ∫ x, vT x * ψ x) →
      OuterSideLimit (Lemma71E.shiftLift (c ω) (n ω)) vT u₀ (chiC κ) (sleLambda κ - θ₂ * chiC κ)
        (-sleLambda κ - θ₁ * chiC κ) := by
  classical
  set χ := chiC κ with hχdef
  have hχ : 0 < χ := Sec4.chiC_pos hκ hκ4
  have hS' := hS
  obtain ⟨hh, hu₀, hh0, hβfl, hαfl, -, hβ62, hα62, hγ62, hae⟩ := hS'
  have hbpc := isPiecewiseConstant_prop74Data a b
  have hθχ : θ₁ * χ ≤ θ₂ * χ := mul_le_mul_of_nonneg_right (hθ₁.trans hθ₂).le hχ.le
  have hΦβ := Lemma613.exists_map_of_cond44 href hκ hκ4 ha (by linarith) hh hβfl
  have hΦα := Lemma613.exists_map_of_cond44 href hκ hκ4 (θ := θ₁) (by linarith) hb hh hαfl
  obtain ⟨_, _, Wβ, _, _, _, -, hcβ, htrβ⟩ := id hβfl
  obtain ⟨_, _, Wα, _, _, _, -, hcα, htrα⟩ := id hαfl
  obtain ⟨hc3, h03, him3, hηm3, hdet3, hloc3, htr3⟩ := Lemma71G.IsLemma62Curve.three hβ62 hα62 hγ62
  set hc' := WholeField.centredField h u₀ with hc'def
  have hloc : ∀ s : Fin 3 → ℝ≥0∞, IsLocalSet (explored (Three.threeCurves β α γ) fun i _ => s i) hc' P :=
    fun s => isLocalSet_explored_of_tendsto (τ := fun i _ => s i) (S := fun j _ _ => s j) hh0 hc3 h03 hηm3 hdet3
      hloc3 htr3 (fun _ => measurable_const) (fun j => isGalmarino_const (s j)) (fun _ _ => rfl)
  have hm : ∀ s : Fin 3 → ℝ≥0∞, Measurable[_, hittingSigma] (explored (Three.threeCurves β α γ) fun i _ => s i) :=
    measurable_explored_const hc3 hηm3
  have hdet := comap_explored_const_le_aeSigma hc3 hdet3
  have hunb : ∀ s : Fin 3 → ℝ≥0∞, ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (explored (Three.threeCurves β α γ) (fun i _ => s i) ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (explored (Three.threeCurves β α γ)
        (fun i _ => s i) ω)) z) := fun s => Eventually.of_forall fun ω =>
    not_isBounded_lowerUnion_explored (fun i => hc3 i ω) (fun i => by rw [h03 i ω]; simp) (fun i t => him3 i ω t)
  -- the means of the wall prefixes
  choose gβ hgβ using fun q : ℚ≥0 => IsLocalSet.exists_isLocalSetMean hh0 (hm (stopsβ q)) (hloc (stopsβ q))
  choose gα hgα using fun q : ℚ≥0 => IsLocalSet.exists_isLocalSetMean hh0 (hm (stopsα q)) (hloc (stopsα q))
  -- Proposition 3.8 against each prefix
  have hPβ := fun q : ℚ≥0 => SideHeightBox.ae_tendsto_sub_of_locals hh0 (hm _) (hm (stopsβ q)) (hloc _) (hloc _)
    (hdet _) (hdet _) (hunb _) (hunb _) hgT (hgβ q)
  have hPα := fun q : ℚ≥0 => SideHeightBox.ae_tendsto_sub_of_locals hh0 (hm _) (hm (stopsα q)) (hloc _) (hloc _)
    (hdet _) (hdet _) (hunb _) (hunb _) hgT (hgα q)
  -- the walls start at `0`
  have hβ00 : ∀ ω, β ω 0 = 0 := fun ω => h03 0 ω
  have hα00 : ∀ ω, α ω 0 = 0 := fun ω => h03 1 ω
  have hγ00 : ∀ ω, γ ω 0 = 0 := fun ω => h03 2 ω
  have hβc : ∀ ω, Continuous (β ω) := fun ω => hc3 0 ω
  have hαc : ∀ ω, Continuous (α ω) := fun ω => hc3 1 ω
  have hEβ : ∀ q ω, explored (Three.threeCurves β α γ) (fun i _ => stopsβ q i) ω = wallPrefix (β ω) q := fun q ω =>
    explored_stopsβ β α γ q ω (by rw [hα00 ω]; simp) (by rw [hγ00 ω]; simp)
  have hEα : ∀ q ω, explored (Three.threeCurves β α γ) (fun i _ => stopsα q i) ω = wallPrefix (α ω) q := fun q ω =>
    explored_stopsα β α γ q ω (by rw [hβ00 ω]; simp) (by rw [hγ00 ω]; simp)
  -- the single-curve heights of the capped walls
  have hgβ' : ∀ q : ℚ≥0, IsLocalSetMean (fun ω => (fun t => β ω (min t (q : ℝ≥0))) ''
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0)} ∩ H) hc' P (gβ q) := fun q => by
    have e : (fun ω => (fun t => β ω (min t (q : ℝ≥0))) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0)} ∩ H) =
        explored (Three.threeCurves β α γ) (fun i _ => stopsβ q i) := funext fun ω => by
      rw [hEβ, wallPrefix, image_capped_eq]
    rw [e]; exact hgβ q
  have hgα' : ∀ q : ℚ≥0, IsLocalSetMean (fun ω => (fun t => α ω (min t (q : ℝ≥0))) ''
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0)} ∩ H) hc' P (gα q) := fun q => by
    have e : (fun ω => (fun t => α ω (min t (q : ℝ≥0))) '' {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (q : ℝ≥0)} ∩ H) =
        explored (Three.threeCurves β α γ) (fun i _ => stopsα q i) := funext fun ω => by
      rw [hEα, wallPrefix, image_capped_eq]
    rw [e]; exact hgα q
  have hcapβ : ∀ q : ℚ≥0, ∀ᵐ ω ∂P, ∀ t, β ω (min t (q : ℝ≥0)) = β ω (Restart.capTime (q : ℝ≥0) (ζβ ω) t) :=
    fun q => by
      filter_upwards [hae] with ω hω t
      rw [Restart.capTime, hω.1]
      simp
  have hcapα : ∀ q : ℚ≥0, ∀ᵐ ω ∂P, ∀ t, α ω (min t (q : ℝ≥0)) = α ω (Restart.capTime (q : ℝ≥0) (ζα ω) t) :=
    fun q => by
      filter_upwards [hae] with ω hω t
      rw [Restart.capTime, hω.2.1]
      simp
  have hSβ := fun q : ℚ≥0 => Lemma613.sideHeight_of_map hκ hκ4 hbpc hh hβfl hΦβ Wβ htrβ hu₀ (q : ℝ≥0) (q : ℝ≥0)
    le_rfl (fun ω t => β ω (min t (q : ℝ≥0))) (fun ω => (hβc ω).comp (continuous_id.min continuous_const))
    (fun t => hηm3 0 (min t q)) (hcapβ q) (gβ q) (hgβ' q)
  have hSα := fun q : ℚ≥0 => Lemma613.sideHeight_of_map hκ hκ4 hbpc hh hαfl hΦα Wα htrα hu₀ (q : ℝ≥0) (q : ℝ≥0)
    le_rfl (fun ω t => α ω (min t (q : ℝ≥0))) (fun ω => (hαc ω).comp (continuous_id.min continuous_const))
    (fun t => hηm3 1 (min t q)) (hcapα q) (gα q) (hgα' q)
  -- the probability-one event
  filter_upwards [hae, ae_exists_isPocketFrame hS hpc, hN, htrβ, htrα, hcβ.1.2.2.2.2, hcα.1.2.2.2.2,
    ae_all_iff.2 hPβ, ae_all_iff.2 hPα, ae_all_iff.2 hSβ, ae_all_iff.2 hSα,
    ae_all_iff.2 fun q => (hgβ q).2.1, ae_all_iff.2 fun q => (hgα q).2.1] with ω hω hFω hNω htβ htα hpβ hpα
    hcmpβ hcmpα hshβ hshα hrβ hrα vT hvT hvTr
  obtain ⟨Ψ, a', b', hF⟩ := hFω
  obtain ⟨hζβ, hζα, -⟩ := hω
  obtain ⟨hwβ0, -, -, hcwβ, -⟩ := hpβ
  obtain ⟨hwα0, -, -, hcwα, -⟩ := hpα
  rw [hζβ] at hcwβ htβ
  rw [hζα] at hcwα htα
  have hWβc : Continuous fun t => Wβ t ω :=
    continuousOn_univ.1 (hcwβ.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hWαc : Continuous fun t => Wα t ω :=
    continuousOn_univ.1 (hcwα.mono fun t _ => show (t : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have htrβ' : IsGeneratingTrace (fun t => Wβ t ω) ⊤ (β ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htβ
  have htrα' : IsGeneratingTrace (fun t => Wα t ω) ⊤ (α ω) := by
    simpa only [Complex.ofReal_zero, sub_zero] using htα
  choose vβ hvβ hvβr using hrβ
  choose vα hvα hvαr using hrα
  have hAT : explored (Three.threeCurves β α γ) (fun i _ => Three.outerStops i) ω =
      (range (β ω) ∪ range (α ω)) ∩ H := Three.explored_threeOuter β α γ ω (by rw [hγ00 ω]; simp)
  refine outerSideLimit_of_heights hF hNω hWβc hwβ0 htrβ' hWαc hwα0 htrα' hAT vβ vα ?_ ?_ ?_ ?_
  · intro q p hp1 hp2 hp3 hp4
    have := hcmpβ q vT (vβ q) hvT hvTr (hvβ q) (hvβr q) p
    rw [hEβ q ω] at this
    exact this hp1 hp2 hp3 hp4
  · intro q p hp1 hp2 hp3 hp4
    have := hcmpα q vT (vα q) hvT hvTr (hvα q) (hvαr q) p
    rw [hEα q ω] at this
    exact this hp1 hp2 hp3 hp4
  · intro q t₀ ht₀ hH F hF hFle y hy hy0
    have hv := hvβ q
    have hvr := hvβr q
    rw [hEβ q ω, wallPrefix, ← image_capped_eq] at hv hvr
    have := (hshβ q (by rw [hζβ]; exact ENNReal.coe_lt_top) (vβ q) hv hvr t₀ ht₀ hH F hF hFle y
      (by simpa only [Complex.ofReal_zero, sub_zero] using hy)).1 hy0
    simpa only [Complex.ofReal_zero, sub_zero] using this
  · intro q t₀ ht₀ hH F hF hFle y hy hy0
    have hv := hvα q
    have hvr := hvαr q
    rw [hEα q ω, wallPrefix, ← image_capped_eq] at hv hvr
    have := (hshα q (by rw [hζα]; exact ENNReal.coe_lt_top) (vα q) hv hvr t₀ ht₀ hH F hF hFle y
      (by simpa only [Complex.ofReal_zero, sub_zero] using hy)).2 hy0
    simpa only [Complex.ofReal_zero, sub_zero] using this

end Prob

end InteractingSLE.Sec7.Lemma71N

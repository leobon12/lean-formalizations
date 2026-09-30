import QuantumZipper.Proofs.Section5.Prop16Headline
import QuantumZipper.Proofs.Section5.Prop16D4WInNice
import QuantumZipper.Proofs.Section5.Prop16LocalAssembly
import QuantumZipper.Proofs.Section5.Prop16GNu
import QuantumZipper.Proofs.LQG.Positivity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6: positivity of `E ν_h[a,b]` (task PROP16-GEN)

Sheffield, arXiv:1012.4797, Proposition 1.6 (PDF p. 24) only assumes `E ν_h[a,b] < ∞`; the
normalization "normalized to be a probability measure" presupposes `E ν_h[a,b] > 0`. Here that
positivity is **proved** from the other hypotheses of `theorem1_6` (without assuming it):

* `prop16Gen_ae_nice_bpos`: almost surely the mixed field `X ω` agrees, on the dyadic folded
  circles near `V = D ∪ (a,b)`, with `y + ψ`, where `y` is a good free-field sample whose
  boundary measure charges every interval and `ψ` is continuous on `V`. This is the transfer
  argument of `Prop16Asm.prop16LocNiceStmt_of_coupling` (the domain Markov coupling
  `prop16MixedFreeLocCoupling_holds`), with the almost-sure event on the coupling space enlarged
  by M4-P2 (`Positivity.ae_forall_pos_qBoundaryMeasure_Ioo`) instead of the area properties;
  unlike `Prop16LocNiceStmt` it does not presuppose positivity.
* `prop16Nu_Ioo_pos_of_agree`: deterministically, then `ν_h = e^{γ(ψ+𝔥₀)/2} ν_y` on `(a,b)`
  (`LocalRule.isVagueLimitOnR_add_ofFun`), so `ν_h(a,b) > 0`.
* `prop16Gen_lintegral_pos`: `0 < ∫⁻ ν_h[a,b] dP`.

Mathematical source: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math.
185 (2011), §3 (the boundary measure is a.s. positive on intervals; the local measure of
`𝔥₀ + h̃` is the free one tilted by a continuous density). Own elementary wiring.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area.G

/-- **The domain Markov transfer with a boundary-positive witness.** No positivity hypothesis on
`E ν_h[a,b]`. Copy of the transfer in `prop16LocNiceStmt_of_coupling`, with M4-P2 (boundary)
added to the almost-sure event on the coupling space. -/
theorem prop16Gen_ae_nice_bpos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : Set ℂ} {c d a b : ℝ}
    (hgeo : K3.Prop16Geometry D c d) (hab : a < b) (hca : c ≤ a) (hbd : b ≤ d)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsMixedGFF D (realSet (Icc c d)) X P) :
    ∀ᵐ ω ∂P, ∃ W : Set ℂ, IsOpen W ∧ W ∩ Hbar = D ∪ realSet (Ioo a b) ∧
      ∃ (y : FieldSample) (ψ : ℂ → ℝ), IsLQGGood γ y ∧
        (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ y (Ioo u v)) ∧
        ContinuousOn ψ (D ∪ realSet (Ioo a b)) ∧ CircAgree W (X ω) (y + ofFun ψ) := by
  obtain ⟨W, hWo, hWV⟩ := locGood_exists_open hgeo hca hbd
  obtain ⟨Ω₀, _, _, P₀, Y, Xf, hP₀, hY, hXf, hag⟩ :=
    prop16MixedFreeLocCoupling_holds D c d a b hgeo hab hca hbd
  set V := D ∪ realSet (Ioo a b) with hVdef
  have hVW : ∀ {s : Set ℂ}, s ⊆ Hbar → (s ⊆ V ↔ s ⊆ W) := fun {s} hs =>
    ⟨fun h u hu => by rw [← hWV] at h; exact (h hu).1,
      fun h u hu => by rw [← hWV]; exact ⟨h hu, hs hu⟩⟩
  have hsubH : ∀ (n k : ℕ) (z : ℂ), closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ Hbar :=
    fun _ _ _ => inter_subset_right
  let I := {m : Measure ℂ // m ∈ locCircSet V}
  have : Countable I := (locCircSet_countable V).to_subtype
  have hadm : ∀ i : I, IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) i.1 := by
    rintro ⟨_, n, k, z, hz, hsub, rfl⟩
    exact locGood_isAdmissible_circle hgeo hca hbd hWo hWV
      (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k) ((hVW (hsubH n k z)).1 hsub)
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY (fun i : I => i.1) hadm
  have hS : ∀ᵐ ω₀ ∂P₀, ω₀ ∈ {ω₀ | IsLQGGood γ (Xf ω₀) ∧
      (∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ (Xf ω₀) (Ioo u v)) ∧
      ∃ ψ : ℂ → ℝ, ContinuousOn ψ V ∧
      Prop16Area.G.CircAgree V (Y ω₀) (Xf ω₀ + ofFun ψ)} := by
    filter_upwards [AreaOffsets.ae_isLQGGood hXf hγ hγ2,
      Positivity.ae_forall_pos_qBoundaryMeasure_Ioo hXf (P := P₀) hγ hγ2, hag]
      with ω₀ h1 h2 h4 using ⟨h1, h2, h4⟩
  have hmF : Measurable fun ω (i : I) => X ω i.1 :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hmG : Measurable fun ω (i : I) => Y ω i.1 :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  filter_upwards [locGood_ae_exists_of_map_eq hmF.aemeasurable hmG hlaw hS] with ω hω
  obtain ⟨ω₀, ⟨hgood, hpos, ψ, hψ, hag'⟩, hFG⟩ := hω
  refine ⟨W, hWo, hWV, Xf ω₀, ψ, hgood, hpos, hψ, fun n k z hz hsub => ?_⟩
  have hsubV := (hVW (hsubH n k z)).2 hsub
  have h1 := congrFun hFG ⟨_, n, k, z, hz, hsubV, rfl⟩
  exact h1.trans (hag' n k z hz hsubV)

/-- **Deterministic core.** If `x` agrees near `V = D ∪ (a,b)` with `y + ψ`, `y` good with a
boundary measure charging every interval, then `ν_{𝔥₀ + x}(a,b) > 0`. -/
theorem prop16Nu_Ioo_pos_of_agree {γ : ℝ} {D : Set ℂ} {a b : ℝ} (hab : a < b) {h0 : ℂ → ℝ}
    (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b))) {x : FieldSample} {W : Set ℂ}
    (hWo : IsOpen W) (hWV : W ∩ Hbar = D ∪ realSet (Ioo a b)) {y : FieldSample} {ψ : ℂ → ℝ}
    (hy : IsLQGGood γ y) (hpos : ∀ u v : ℝ, u < v → 0 < qBoundaryMeasure γ y (Ioo u v))
    (hψ : ContinuousOn ψ (D ∪ realSet (Ioo a b))) (hag : CircAgree W x (y + ofFun ψ)) :
    0 < prop16Nu γ h0 a b x (Ioo a b) := by
  have hVW : D ∪ realSet (Ioo a b) ⊆ W := fun z hz => by rw [← hWV] at hz; exact hz.1
  have hag' := circAgree_ofFun_add hWV hψ hh0 hag
  set ψ' : ℂ → ℝ := fun z => ψ z + h0 z with hψ'_def
  have hψ' : ContinuousOn ψ' (W ∩ Hbar) := by rw [hWV]; exact hψ.add hh0
  have hRW : ∀ t ∈ Ioo a b, (t : ℂ) ∈ W := fun t ht => hVW (Or.inr ⟨t, ht, rfl⟩)
  have hlim := isVagueLimitOnR_of_circAgree hWo hag' hRW
    (LocalRule.isVagueLimitOnR_add_ofFun hy.1 isOpen_Ioo
      (isVagueLimitOnR_restrict_of (isVagueLimitR_of_good hy) isOpen_Ioo) hWo hRW hψ')
  have heq : prop16Nu γ h0 a b x = ((qBoundaryMeasure γ y).restrict (Ioo a b)).withDensity
      fun t => ENNReal.ofReal (Real.exp (γ / 2 * ψ' t)) :=
    LocalRule.qBoundaryMeasureOn_eq isOpen_Ioo hlim
  have hcont : ContinuousOn (fun t : ℝ => ENNReal.ofReal (Real.exp (γ / 2 * ψ' t))) (Ioo a b) :=
    ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hψ'.comp Complex.continuous_ofReal.continuousOn
        fun t ht => ⟨hRW t ht, show (0:ℝ) ≤ ((t:ℝ):ℂ).im by simp⟩)))
  rw [heq, pos_iff_ne_zero, ne_eq,
    withDensity_apply_eq_zero' (hcont.aemeasurable measurableSet_Ioo)]
  have hset : {t : ℝ | ENNReal.ofReal (Real.exp (γ / 2 * ψ' t)) ≠ 0} ∩ Ioo a b = Ioo a b := by
    ext t
    simp [Real.exp_pos]
  rw [hset, Measure.restrict_apply measurableSet_Ioo, inter_self]
  exact (hpos a b hab).ne'

/-- **`E ν_h[a,b] > 0`** from the hypotheses of Proposition 1.6 (no positivity assumed). -/
theorem prop16Gen_lintegral_pos {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : Set ℂ} {c d a b : ℝ}
    (hgeo : K3.Prop16Geometry D c d) (hab : a < b) (hca : c ≤ a) (hbd : b ≤ d) {h0 : ℂ → ℝ}
    (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b)))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hX : IsMixedGFF D (realSet (Icc c d)) X P) :
    0 < ∫⁻ ω, prop16Nu γ h0 a b (X ω) (Icc a b) ∂P := by
  have hn := prop16Gen_ae_nice_bpos hγ hγ2 hgeo hab hca hbd hX
  have hloc : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω) :=
    hn.mono fun _ ⟨W, hWo, hWV, y, ψ, hy, _, hψ, hag⟩ => ⟨W, hWo, hWV, y, ψ, hy, hψ, hag⟩
  have hν := aemeasurable_prop16Nu hX.measurable_coord
    (prop16_hexB hγ hgeo.1 hgeo.2.2.2.1 hh0 hloc)
  have hm : AEMeasurable (fun ω => prop16Nu γ h0 a b (X ω) (Icc a b)) P :=
    (Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hν
  have hp : ∀ᵐ ω ∂P, 0 < prop16Nu γ h0 a b (X ω) (Icc a b) :=
    hn.mono fun ω ⟨W, hWo, hWV, y, ψ, hy, hpos, hψ, hag⟩ =>
      (prop16Nu_Ioo_pos_of_agree hab hh0 hWo hWV hy hpos hψ hag).trans_le
        (measure_mono Ioo_subset_Icc_self)
  rw [pos_iff_ne_zero]
  intro h0'
  rw [lintegral_eq_zero_iff' hm] at h0'
  obtain ⟨ω, h1, h2⟩ := (hp.and h0').exists
  exact h1.ne' h2

end Prop16Asm

end QuantumZipper

import QuantumZipper.Proofs.Section5.Prop16LocalRule

/-!
# Proposition 1.6, M4-P7-LOC (part 3): `hexB`, `hA0`, `hA1` from a local good-sample property

`IsLocallyGoodOn γ V x` (for `V` relatively open in `Hbar`): on an open `W` with
`W ∩ Hbar = V`, the sample `x` agrees on the dyadic folded circles inside `W` with `y + ψ`,
where `y` is a good sample (`IsLQGGood`, e.g. a free field mod constants on `ℍ`,
`AreaOffsets.ae_isLQGGood`) and `ψ` is continuous on `V`. For a mixed GFF on `D` with free
part `[c,d]` this is the domain Markov decomposition "free field on `ℍ` restricted to `D` =
mixed GFF + independent Neumann-harmonic function" (Sheffield, *Gaussian free fields for
mathematicians*, PTRF 139 (2007), Thm. 2.17, in its mixed-boundary form; cf. the M7 coupling
`MixedFreeCouplingHalfDiscStmt`), read along the countably many dyadic circles.

* `local_limits_of_isLocallyGoodOn` (deterministic): for `h = 𝔥₀ + x` with `𝔥₀` continuous on
  `D ∪ (a,b)`, the local boundary limit on `(a,b)` exists, and so do the local area limits of
  every zoomed field `h(· + t) + C/γ` on `D − t` and of its rescalings by `s > 0` on
  `s⁻¹(D − t)`. Route: locality (`Prop16LocalAgree`), the local rule (5.1) of `LocalRule`, and
  the transformation rules of `GoodTransforms` for the good field `y`.
* `prop16_hexB`, `prop16_hA0`, `prop16_hA1`: the inputs `hexB`, `hA0`, `hA1` of
  `prop16_areaConvergesInLawOn_of_inputs''` for Proposition 1.6's objects, from
  `∀ᵐ ω, IsLocallyGoodOn γ (D ∪ (a,b)) (X ω)`.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 2.1 and §6 (locality and coordinate-change rule of the measures); Sheffield,
arXiv:1012.4797, Prop. 1.6 (pp. 24–25). The formal arguments are our own elementary ones.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace QuantumZipper

namespace Prop16Area

namespace G

open GoodSample RegClosure LocalRule CircleFubini

/-- **Local good sample on `V`** (M4-P7-LOC input). -/
def IsLocallyGoodOn (γ : ℝ) (V : Set ℂ) (x : FieldSample) : Prop :=
  ∃ W : Set ℂ, IsOpen W ∧ W ∩ Hbar = V ∧ ∃ (y : FieldSample) (ψ : ℂ → ℝ),
    IsLQGGood γ y ∧ ContinuousOn ψ V ∧ CircAgree W x (y + ofFun ψ)

theorem integrable_fc_of_continuousOn {g : ℂ → ℝ} {d : ℂ} (hd : d ∈ Hbar) {r : ℝ} (hr : 0 < r)
    (hg : ContinuousOn g (closedBall d r ∩ Hbar)) : Integrable g (foldedCircle d r) := by
  have hi := hg.integrableOn_compact (μ := foldedCircle d r) (isCompact_closedBall_inter_Hbar d r)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem (ae_fc_mem_ball_inter hd hr)] at hi

theorem circAgree_ofFun_add {V W : Set ℂ} (hWV : W ∩ Hbar = V) {x y : FieldSample}
    {ψ h0 : ℂ → ℝ} (hψ : ContinuousOn ψ V) (hh0 : ContinuousOn h0 V)
    (h : CircAgree W x (y + ofFun ψ)) :
    CircAgree W (ofFun h0 + x) (y + ofFun (fun z => ψ z + h0 z)) := by
  intro n k z hz hW
  have hc := CircleCont.dyadicRoundC_mem_Hbar hz n
  have hsub : closedBall (dyadicRoundC n z) (radius k) ∩ Hbar ⊆ V := fun u hu => by
    rw [← hWV]; exact ⟨hW hu, hu.2⟩
  rw [Pi.add_apply, h n k z hz hW, Pi.add_apply, Pi.add_apply]
  simp only [ofFun]
  rw [integral_add (integrable_fc_of_continuousOn hc (radius_pos k) (hψ.mono hsub))
    (integrable_fc_of_continuousOn hc (radius_pos k) (hh0.mono hsub))]
  ring

/-- Local area limit on `U` for a field agreeing on `W ⊇ U` with `z + φ`, `z` good. -/
theorem exists_limit_of_agree {γ : ℝ} {W U : Set ℂ} (hWo : IsOpen W) {x z : FieldSample}
    {φ : ℂ → ℝ} (hz : IsLQGGood γ z) (hφ : ContinuousOn φ (W ∩ Hbar))
    (h : CircAgree W x (z + ofFun φ)) (hUo : IsOpen U) (hUH : U ⊆ H) (hUW : U ⊆ W) :
    ∃ m, IsVagueLimitOn U (areaApprox γ x) m :=
  ⟨_, isVagueLimitOn_of_circAgree hWo h hUH hUW (isVagueLimitOn_add_ofFun hz.1 hUo hUH
    (isVagueLimitOn_restrict_sub hUo hUH (isVagueLimitOn_H_of_good hz)) hWo hUW hφ)⟩

/-- **Deterministic core of M4-P7-LOC.** -/
theorem local_limits_of_isLocallyGoodOn {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D)
    (hDH : D ⊆ H) {a b : ℝ} {h0 : ℂ → ℝ} (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b)))
    {x : FieldSample} (hx : IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) x) :
    (∃ ν, IsVagueLimitOnR (Ioo a b) (bdryApprox γ (ofFun h0 + x)) ν) ∧
    (∀ C t : ℝ, ∃ m, IsVagueLimitOn (zoomDomain D t)
      (areaApprox γ (zoomField γ C (ofFun h0 + x) t)) m) ∧
    (∀ C t s : ℝ, 0 < s → ∃ m, IsVagueLimitOn ((fun z => (s : ℂ) * z) ⁻¹' zoomDomain D t)
      (areaApprox γ (rescale (zoomField γ C (ofFun h0 + x) t) (Qc γ) s)) m) := by
  obtain ⟨W, hWo, hWV, y, ψ, hy, hψ, hag⟩ := hx
  have hVW : D ∪ realSet (Ioo a b) ⊆ W := fun z hz => by rw [← hWV] at hz; exact hz.1
  have hag' := circAgree_ofFun_add hWV hψ hh0 hag
  set ψ' : ℂ → ℝ := fun z => ψ z + h0 z with hψ'_def
  have hψ' : ContinuousOn ψ' (W ∩ Hbar) := by rw [hWV]; exact hψ.add hh0
  have hRW : ∀ t ∈ Ioo a b, (t : ℂ) ∈ W := fun t ht => hVW (Or.inr ⟨t, ht, rfl⟩)
  -- the zoomed fields
  have hZag : ∀ C t : ℝ, CircAgree ((fun z => z + (t : ℂ)) ⁻¹' W)
      (zoomField γ C (ofFun h0 + x) t) (zoomField γ C y t + ofFun (fun u => ψ' (u + t))) := by
    intro C t
    have h1 := fcAgree_addConst (fcAgree_translate hWo hag' t) (C / γ)
    have h2 := fcAgree_addConst (fcAgree_translate_add_ofFun hy.1 hWo hψ' t) (C / γ)
    rw [addConst_add_ofFun] at h2
    exact (h1.trans h2).circAgree
  have hZg : ∀ C t : ℝ, IsLQGGood γ (zoomField γ C y t) := fun C t =>
    (hy.translate t).addConst (C / γ)
  have hWt : ∀ t : ℝ, IsOpen ((fun z => z + (t : ℂ)) ⁻¹' W) := fun t =>
    hWo.preimage (continuous_id.add continuous_const)
  have hψt : ∀ t : ℝ, ContinuousOn (fun u => ψ' (u + t))
      ((fun z => z + (t : ℂ)) ⁻¹' W ∩ Hbar) := fun t =>
    hψ'.comp (continuous_id.add continuous_const).continuousOn
      fun u hu => ⟨hu.1, mapsTo_add_real t hu.2⟩
  have hUo : ∀ t : ℝ, IsOpen (zoomDomain D t) := fun t =>
    hD.preimage (continuous_id.add continuous_const)
  have hUH : ∀ t : ℝ, zoomDomain D t ⊆ H := fun t z hz => by
    have : 0 < (z + (t : ℂ)).im := hDH hz
    show 0 < z.im
    simpa using this
  have hUW : ∀ t : ℝ, zoomDomain D t ⊆ (fun z => z + (t : ℂ)) ⁻¹' W := fun t z hz =>
    hVW (Or.inl hz)
  refine ⟨⟨_, isVagueLimitOnR_of_circAgree hWo hag' hRW
      (isVagueLimitOnR_add_ofFun hy.1 isOpen_Ioo
        (isVagueLimitOnR_restrict_of (isVagueLimitR_of_good hy) isOpen_Ioo) hWo hRW hψ')⟩,
    fun C t => exists_limit_of_agree (hWt t) (hZg C t) (hψt t) (hZag C t) (hUo t) (hUH t) (hUW t),
    fun C t s hs => ?_⟩
  have hag2 := ((fcAgree_rescale (hWt t) (hZag C t) (Qc γ) hs).trans
    (fcAgree_rescale_add_ofFun (hZg C t).1 (hWt t) (hψt t) (Qc γ) hs)).circAgree
  refine exists_limit_of_agree ((hWt t).preimage (continuous_const.mul continuous_id))
    ((hZg C t).rescale hγ hs)
    ((hψt t).comp (continuous_const.mul continuous_id).continuousOn
      fun u hu => ⟨hu.1, mapsTo_mul_pos hs hu.2⟩) hag2
    ((hUo t).preimage (continuous_const.mul continuous_id)) (fun z hz => ?_)
    (fun z hz => hUW t hz)
  have h1 : 0 < ((s : ℂ) * z).im := hUH t hz
  rw [Complex.im_ofReal_mul] at h1
  show 0 < z.im
  exact pos_of_mul_pos_right h1 hs.le

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`hexB` for Proposition 1.6.** -/
theorem prop16_hexB {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {a b : ℝ}
    {h0 : ℂ → ℝ} (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b))) {P : Measure Ω}
    {X : Ω → FieldSample}
    (hloc : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω)) :
    ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitOnR (Ioo a b) (bdryApprox γ (ofFun h0 + X ω)) ν :=
  hloc.mono fun _ hω => (local_limits_of_isLocallyGoodOn hγ hD hDH hh0 hω).1

/-- **`hA0` for Proposition 1.6.** -/
theorem prop16_hA0 {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {a b : ℝ}
    {h0 : ℂ → ℝ} (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b))) {P : Measure Ω}
    {X : Ω → FieldSample}
    (hloc : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω)) :
    ∀ C : ℝ, ∀ᵐ ω ∂P, ∀ t ∈ Ioo a b, ∃ m, IsVagueLimitOn (zoomDomain D t)
      (areaApprox γ (zoomField γ C (ofFun h0 + X ω) t)) m := fun C =>
  hloc.mono fun _ hω t _ => (local_limits_of_isLocallyGoodOn hγ hD hDH hh0 hω).2.1 C t

/-- **`hA1` for Proposition 1.6.** -/
theorem prop16_hA1 {γ : ℝ} (hγ : 0 < γ) {D : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H) {a b : ℝ}
    {h0 : ℂ → ℝ} (hh0 : ContinuousOn h0 (D ∪ realSet (Ioo a b))) {P : Measure Ω}
    {X : Ω → FieldSample}
    (hloc : ∀ᵐ ω ∂P, IsLocallyGoodOn γ (D ∪ realSet (Ioo a b)) (X ω)) :
    ∀ C : ℝ, ∀ᵐ ω ∂P, ∀ t ∈ Ioo a b, ∀ s : ℝ, 0 < s → ∃ m,
      IsVagueLimitOn ((fun z => (s : ℂ) * z) ⁻¹' zoomDomain D t)
        (areaApprox γ (rescale (zoomField γ C (ofFun h0 + X ω) t) (Qc γ) s)) m := fun C =>
  hloc.mono fun _ hω t _ s hs => (local_limits_of_isLocallyGoodOn hγ hD hDH hh0 hω).2.2 C t s hs

end G

end Prop16Area

end QuantumZipper

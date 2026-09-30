import QuantumZipper.Proofs.Thm18.G3Zc2CondPalm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C 2: conditioning on the whole far-increment process

For the two-point (partner) step the conditioning event may depend on the level `L`, so the
conditioning variable must be the **whole** process of far increments (an uncountable family,
product σ-algebra), with the uniformity over events coming after `∀ᶠ L`.

* `exists_ae_eq_preimage_of_coords`: if every coordinate of `V : Ω → (K → ℝ)` is a.s. a measurable
  function of `Ξ`, then every event `{V ∈ B}` (`B` measurable in the product σ-algebra) is a.s.
  equal to an event `{Ξ ∈ B'}` (good-sets argument: such `B` form a σ-algebra containing the
  generating cylinders).
* `cond_zoom_of_lawEq'`: `cond_zoom_of_lawEq` (G3Zc2Cond) under this weaker hypothesis.
* `cond_zoom_palm_free'`: `cond_zoom_palm_free` (G3Zc2CondPalm) for an arbitrary (uncountable)
  family `q` of far balanced pairs, uniformly over measurable events of the whole conditioning
  process, `∀ᶠ L` before `∀ B`.

Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric InnerProductSpace
open scoped NNReal ENNReal Topology ComplexConjugate

namespace QuantumZipper
namespace G3Cv

open D3Plus K3 GFFExist LQGDimension.ExistAsm

/-- **Good sets.** -/
theorem exists_ae_eq_preimage_of_coords {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {E' : Type} [MeasurableSpace E'] {Ξ : Ω → E'} {K : Type} {V : Ω → (K → ℝ)}
    (hV : ∀ k, ∃ F : E' → ℝ, Measurable F ∧ ∀ᵐ ω ∂P, V ω k = F (Ξ ω))
    {B : Set (K → ℝ)} (hB : MeasurableSet B) :
    ∃ B' : Set E', MeasurableSet B' ∧ V ⁻¹' B =ᵐ[P] Ξ ⁻¹' B' := by
  let M : MeasurableSpace (K → ℝ) :=
    { MeasurableSet' := fun B => ∃ B' : Set E', MeasurableSet B' ∧ V ⁻¹' B =ᵐ[P] Ξ ⁻¹' B'
      measurableSet_empty := ⟨∅, MeasurableSet.empty, by simp⟩
      measurableSet_compl := fun B ⟨B', hB', he⟩ => ⟨B'ᶜ, hB'.compl, by
        rw [preimage_compl, preimage_compl]; exact he.compl⟩
      measurableSet_iUnion := fun f hf => by
        choose g hg he using hf
        exact ⟨⋃ n, g n, MeasurableSet.iUnion hg, by
          rw [preimage_iUnion, preimage_iUnion]; exact EventuallyEq.countable_iUnion he⟩ }
  have hle : (MeasurableSpace.pi : MeasurableSpace (K → ℝ)) ≤ M := by
    refine iSup_le fun k => ?_
    rw [MeasurableSpace.comap_le_iff_le_map]
    intro A hA
    obtain ⟨F, hF, hFe⟩ := hV k
    refine ⟨F ⁻¹' A, hF hA, ?_⟩
    filter_upwards [hFe] with ω h
    show (V ω ∈ (fun f : K → ℝ => f k) ⁻¹' A) = (Ξ ω ∈ F ⁻¹' A)
    simp only [mem_preimage, h]
  exact hle B hB

/-- **Conditional zoom limit, transferred by law, for conditioning events a.s. in `σ(Ξ)`.** -/
theorem cond_zoom_of_lawEq' (hD3 : D3PlusIStmtRich) {γ α r : ℝ} {ρ₀ : Measure ℂ}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ}
    (hS : Setup γ α r ρ₀ P X Ξ g) {Zf : ℝ → Ω → FieldSample}
    (hag : ∀ᵐ ω ∂P, ∀ L : ℝ, AgreeNear (Zf L ω) (zoomModel γ α L ρ₀ (X ω) (g ω)) r)
    {Eb : Type} [MeasurableSpace Eb] {V : Ω → Eb}
    (hVΞ : ∀ B : Set Eb, MeasurableSet B →
      ∃ B' : Set E', MeasurableSet B' ∧ V ⁻¹' B =ᵐ[P] Ξ ⁻¹' B')
    (hm : ∀ L, AEMeasurable (fun ω => (dyadData r (Zf L ω), V ω)) P)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {Z' : ℝ → Ω' → FieldSample}
    {V' : Ω' → Eb} (hm' : ∀ L, AEMeasurable (fun ω => (dyadData r (Z' L ω), V' ω)) P')
    (hlaw : ∀ L, (P.map fun ω => (dyadData r (Zf L ω), V ω)) =
      P'.map fun ω => (dyadData r (Z' L ω), V' ω))
    (hg' : ∀ L, ∀ᵐ ω ∂P', ∃ m, IsVagueLimitOn (halfDisc r) (areaApprox γ (Z' L ω)) m)
    {Ω₁ : Type} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {Y' : Ω₁ → FieldSample} (hY' : IsQuantumWedge γ α Y' P₁) (R : ℕ)
    {Γ : (ℕ → ℝ) × (TestFun H → ℝ) → ℝ≥0∞} (hΓ : Measurable Γ) (hΓ1 : ∀ y, Γ y ≤ 1)
    (η : ℝ≥0∞) (hη : 0 < η) :
    ∀ᶠ L in atTop, ∀ B : Set Eb, MeasurableSet B →
      ∫⁻ ω, B.indicator 1 (V' ω) * Γ (locFieldFull R (canonicalOn γ (Z' L ω) (halfDisc r))) ∂P' ≤
          P' (V' ⁻¹' B) * ∫⁻ ω, Γ (locFieldFull R (Y' ω)) ∂P₁ + η ∧
        P' (V' ⁻¹' B) * ∫⁻ ω, Γ (locFieldFull R (Y' ω)) ∂P₁ ≤
          ∫⁻ ω, B.indicator 1 (V' ω) * Γ (locFieldFull R (canonicalOn γ (Z' L ω) (halfDisc r)))
            ∂P' + η := by
  set c := ∫⁻ ω, Γ (locFieldFull R (Y' ω)) ∂P₁ with hc
  have hVm : AEMeasurable V P := (hm 0).snd
  have hV'm : AEMeasurable V' P' := (hm' 0).snd
  have hZm : ∀ L, AEMeasurable (fun ω => dyadData r (Zf L ω)) P := fun L => (hm L).fst
  obtain ⟨hg, hb⟩ := tendsto_dyadBad_of_setup hS hag hZm R
  have hη4 : 0 < η / 4 := ENNReal.div_pos hη.ne' (by norm_num)
  have hmarg : ∀ L, (P.map fun ω => (dyadData r (Zf L ω), V ω))
      (Prod.fst ⁻¹' dyadBad γ r R) = (P.map fun ω => dyadData r (Zf L ω)) (dyadBad γ r R) :=
    fun L => by
      rw [← Measure.map_apply measurable_fst (measurableSet_dyadBad γ r R),
        AEMeasurable.map_map_of_aemeasurable measurable_fst.aemeasurable (hm L)]
      rfl
  have hPB : ∀ B : Set Eb, MeasurableSet B → P' (V' ⁻¹' B) = P (V ⁻¹' B) := fun B hB => by
    have h1 : (P.map V) B = (P'.map V') B := by
      have e := congrArg (fun μ : Measure ((DyIdxIn r → ℝ) × Eb) => μ.map Prod.snd) (hlaw 0)
      rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hm 0),
        AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable (hm' 0)] at e
      exact congrArg (fun μ : Measure Eb => μ B) e
    rw [Measure.map_apply₀ hVm hB.nullMeasurableSet,
      Measure.map_apply₀ hV'm hB.nullMeasurableSet] at h1
    exact h1.symm
  have hi1 : ∀ (T : Type) (A : Set T) (x : T), A.indicator (1 : T → ℝ≥0∞) x ≤ 1 :=
    fun T A x => by by_cases hx : x ∈ A <;> simp [hx]
  filter_upwards [d3_transfer_of_agree hD3 hS hag hY' R (η / 4) hη4,
    hb.eventually (Iic_mem_nhds hη4)] with L hL hbL B hB
  obtain ⟨B', hB', hBe⟩ := hVΞ B hB
  have hΦ : Measurable[(condSigma Ξ X r).prod inferInstance]
      (fun p : Ω × ((ℕ → ℝ) × (TestFun H → ℝ)) => B'.indicator 1 (Ξ p.1) * Γ p.2) := by
    have h1 : Measurable[condSigma Ξ X r] fun ω => B'.indicator (1 : E' → ℝ≥0∞) (Ξ ω) :=
      ((measurable_const.indicator hB').comp (comap_measurable Ξ)).mono le_sup_left le_rfl
    let _ : MeasurableSpace Ω := condSigma Ξ X r
    exact (h1.comp measurable_fst).mul (hΓ.comp measurable_snd)
  obtain ⟨k1, k2⟩ := hL _ hΦ fun p => (mul_le_mul' (hi1 _ _ _) (hΓ1 p.2)).trans (by rw [mul_one])
  have hind : ∀ᵐ ω ∂P, B'.indicator (1 : E' → ℝ≥0∞) (Ξ ω) = B.indicator 1 (V ω) := by
    filter_upwards [hBe] with ω h
    have h' : (ω ∈ V ⁻¹' B) = (ω ∈ Ξ ⁻¹' B') := h
    by_cases hx : V ω ∈ B
    · have hx' : Ξ ω ∈ B' := by
        have : ω ∈ Ξ ⁻¹' B' := h' ▸ (show ω ∈ V ⁻¹' B from hx)
        exact this
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']; rfl
    · have hx' : Ξ ω ∉ B' := fun hx' => hx (by
        have : ω ∈ V ⁻¹' B := h' ▸ (show ω ∈ Ξ ⁻¹' B' from hx')
        exact this)
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
  have eV : ∫⁻ ω, B'.indicator 1 (Ξ ω) *
      Γ (locFieldFull R (canonicalOn γ (Zf L ω) (halfDisc r))) ∂P =
      ∫⁻ ω, B.indicator 1 (V ω) * Γ (locFieldFull R (canonicalOn γ (Zf L ω) (halfDisc r))) ∂P :=
    lintegral_congr_ae (hind.mono fun ω h => by simp only [h])
  have eR : ∫⁻ ω, ∫⁻ ω', B'.indicator 1 (Ξ ω) * Γ (locFieldFull R (Y' ω')) ∂P₁ ∂P =
      P (V ⁻¹' B) * c := by
    have e1 : ∀ ω, ∫⁻ ω', B'.indicator (1 : E' → ℝ≥0∞) (Ξ ω) * Γ (locFieldFull R (Y' ω')) ∂P₁ =
        B'.indicator 1 (Ξ ω) * c := fun ω =>
      lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top (hi1 _ _ _))
    simp_rw [e1]
    rw [lintegral_mul_const' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top
      (Thm18Asm.g1z_lintegral_le_one hΓ1 _))]
    congr 1
    rw [lintegral_congr_ae hind, ← lintegral_indicator_one₀ (hVm.nullMeasurable hB)]
    refine lintegral_congr fun ω => ?_
    show B.indicator 1 (V ω) = (V ⁻¹' B).indicator 1 ω
    by_cases hx : V ω ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show ω ∈ V ⁻¹' B from hx)]; rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show ω ∉ V ⁻¹' B from hx)]
  rw [eV, eR] at k1 k2
  obtain ⟨a1, a2⟩ := lintegral_cond_dyad (R := R) (hm L) (hg L) hΓ hΓ1 hB
  obtain ⟨b1, b2⟩ := lintegral_cond_dyad (R := R) (hm' L) (hg' L) hΓ hΓ1 hB
  rw [← hlaw L] at b1 b2
  rw [hmarg] at a1 a2 b1 b2
  rw [hPB B hB]
  have hsum : η / 4 + η / 4 + η / 4 + η / 4 = η := by
    have h4 : η / 4 * 4 = η := ENNReal.div_mul_cancel (by norm_num) (by norm_num)
    calc η / 4 + η / 4 + η / 4 + η / 4 = η / 4 * 4 := by ring
      _ = η := h4
  set A' := ∫⁻ ω, B.indicator 1 (V' ω) *
    Γ (locFieldFull R (canonicalOn γ (Z' L ω) (halfDisc r))) ∂P' with hA'
  set A := ∫⁻ ω, B.indicator 1 (V ω) *
    Γ (locFieldFull R (canonicalOn γ (Zf L ω) (halfDisc r))) ∂P with hA
  set b := (P.map fun ω => dyadData r (Zf L ω)) (dyadBad γ r R) with hbdef
  set pc := P (V ⁻¹' B) * c with hpc
  constructor
  · calc A' ≤ _ := b1
      _ ≤ (A + b) + b := add_le_add a2 le_rfl
      _ ≤ (pc + η / 4 + η / 4 + η / 4) + η / 4 := add_le_add (add_le_add k1 hbL) hbL
      _ = pc + (η / 4 + η / 4 + η / 4 + η / 4) := by ring
      _ = pc + η := by rw [hsum]
  · calc pc ≤ A + η / 4 + η / 4 := k2
      _ ≤ (_ + b) + η / 4 + η / 4 := add_le_add (add_le_add a1 le_rfl) le_rfl
      _ ≤ ((A' + b) + b) + η / 4 + η / 4 :=
          add_le_add (add_le_add (add_le_add b2 le_rfl) le_rfl) le_rfl
      _ ≤ ((A' + η / 4) + η / 4) + η / 4 + η / 4 :=
          add_le_add (add_le_add (add_le_add (add_le_add le_rfl hbL) hbL) le_rfl) le_rfl
      _ = A' + (η / 4 + η / 4 + η / 4 + η / 4) := by ring
      _ = A' + η := by rw [hsum]

end G3Cv
end QuantumZipper

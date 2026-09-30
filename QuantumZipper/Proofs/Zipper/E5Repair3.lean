import QuantumZipper.Proofs.Zipper.E5Repair2
import QuantumZipper.Proofs.Zipper.E5Main5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5 repair, part 3: the zoom model is TV-near the target under a Wiener measure (D39)

Restated copies of `E5.germDensity_withDensity` (E5Dens), `E5.tvNear_germ` (E5Main2),
`E5.tvNear_model_germ`, `E5.tvNear_model` (E5Main4) and `E5.ZoomModel.tvNear` (E5Main5), whose
committed versions assume the unsatisfiable `IsBrownianReal (fun t b => b t) W`
(`E5Final4.not_isBrownianReal_coord`). Here `W` is only assumed pre-Brownian (Wiener measure on
the product path space, decision D39). The proofs are the committed ones verbatim; the only
change is that they call the repaired E5a `germDensity_core'` (E5Repair2).
Source: Sheffield arXiv:1012.4797, §5.4, proof of Lemma 5.6 (as for the committed versions).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity

section DensRepair

variable {Ω : Type*} [MeasurableSpace Ω] {R : Measure Ω} [IsProbabilityMeasure R]
  {𝕍 : Type*} [MeasurableSpace 𝕍] {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
variable {V : Ω → 𝕍} {D : Ω → ℝ≥0 → ℝ} {u₀ : ℝ≥0} {w : Ω → ℝ≥0∞}

/-- **E5-DENS** (E5a under a weighted reference measure). Under a probability measure `R`, let the
germ `D|_{[0,u₀]}` of a continuous path `D` be Wiener-distributed and independent of `V`, and let
`P := R.withDensity w` be a probability measure. If the scales `a_n(V) > 0` tend to `0` in
`P`-probability, then, uniformly over measurable `Γ` with `|Γ| ≤ 1`,
`E_P Γ(V, (a_n⁻¹ D(a_n² t))_{t ≤ S}) − E_P ∫ Γ(V, b|_{[0,S]}) W(db) → 0`. -/
theorem germDensity_withDensity'
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    (hV : Measurable V) (hD : Measurable D) (hDc : ∀ ω, Continuous (D ω)) (hu₀ : 0 < u₀)
    (hind : IndepFun V (fun ω => pathRestr u₀ (D ω)) R)
    (hDW : R.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀))
    (hw1 : ∫⁻ ω, w ω ∂R = 1)
    {a : ℕ → 𝕍 → ℝ≥0} (ha : ∀ n, Measurable (a n)) (hapos : ∀ n v, 0 < a n v)
    (hprob : ∀ ε : ℝ≥0, 0 < ε →
      Tendsto (fun n => R.withDensity w {ω | ε ≤ a n (V ω)}) atTop (𝓝 0))
    (S : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    ∃ N, ∀ n ≥ N, ∀ Γ : 𝕍 × (Iic S → ℝ) → ℝ, Measurable Γ → (∀ p, |Γ p| ≤ 1) →
      |∫ ω, Γ (V ω, LengthMarkov.GermDensity.rescale S (a n (V ω)) (D ω)) ∂(R.withDensity w) -
        ∫ ω, ∫ b, Γ (V ω, pathRestr S b) ∂W ∂(R.withDensity w)| ≤ η := by
  have : IsProbabilityMeasure (R.withDensity w) := isProbabilityMeasure_withDensity_of hw1
  exact germDensity_core' hW hV hD hDc hu₀ measurable_psiD psiD_nonneg integral_psiD
    (fun Φ hΦ hC => hlaw_withDensity hV hD hind hDW hw1 Φ hΦ hC) ha hapos hprob S hη

end DensRepair

section GermRepair

variable {Ω₁ : Type*} [MeasurableSpace Ω₁]
variable {𝕍 : Type*} [MeasurableSpace 𝕍] {W : Measure (ℝ≥0 → ℝ)}

/-- **The germ step (E5 steps (3)–(4)) in `TVNear` form.** Under a probability measure `Rr` the
germ `D|_{[0,u₀]}` of a continuous path `D` is Wiener and independent of `V`; `𝐏 := Rr.withDensity
w` is a probability measure; the scales `aV C (V) > 0` tend to `0` in `𝐏`-probability along
every sequence `C n → ∞`. Then, uniformly over measurable tests `Γ ∈ [0,1]` of
`Θ C (V, rescaled germ)`, the rescaled germ may be replaced by an independent Wiener path. -/
theorem tvNear_germ' {Rr : Measure Ω₁} [IsProbabilityMeasure Rr] [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {V : Ω₁ → 𝕍} (hV : Measurable V) {D : Ω₁ → ℝ≥0 → ℝ} (hD : Measurable D)
    (hDc : ∀ ω, Continuous (D ω)) {u₀ : ℝ≥0} (hu₀ : 0 < u₀)
    (hind : IndepFun V (fun ω => pathRestr u₀ (D ω)) Rr)
    (hDW : Rr.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀))
    {w : Ω₁ → ℝ≥0∞} (hw1 : ∫⁻ ω, w ω ∂Rr = 1)
    {E : Type*} [MeasurableSpace E] (S : ℝ≥0) (aV : ℝ → 𝕍 → ℝ≥0) (haV : ∀ C, Measurable (aV C))
    (hapos : ∀ C v, 0 < aV C v)
    (hprob : ∀ Cs : ℕ → ℝ, Tendsto Cs atTop atTop → ∀ ε : ℝ≥0, 0 < ε →
      Tendsto (fun n => Rr.withDensity w {ω | ε ≤ aV (Cs n) (V ω)}) atTop (𝓝 0))
    (Θ : ℝ → 𝕍 → (Iic S → ℝ) → E) (hΘ : ∀ C, Measurable (Function.uncurry (Θ C))) :
    TVNear (fun C Γ => ∫⁻ ω, Γ (Θ C (V ω) (LengthMarkov.GermDensity.rescale S (aV C (V ω)) (D ω))) ∂(Rr.withDensity w))
      (fun C Γ => ∫⁻ ω, ∫⁻ b, Γ (Θ C (V ω) (pathRestr S b)) ∂W ∂(Rr.withDensity w)) := by
  have : IsProbabilityMeasure (Rr.withDensity w) := isProbabilityMeasure_withDensity_of hw1
  refine TVNear.of_seq fun η hη Cs hCs => ?_
  rcases eq_or_ne η ⊤ with rfl | hηt
  · exact Eventually.of_forall fun n Γ _ hΓ1 => by simp
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηt
  obtain ⟨N, hN⟩ := germDensity_withDensity' hW hV hD hDc hu₀ hind hDW hw1
    (a := fun n => aV (Cs n)) (fun n => haV _) (fun n v => hapos _ v) (hprob Cs hCs) S hηr
  rw [eventually_atTop]
  refine ⟨N, fun n hn Γ hΓ hΓ1 => ?_⟩
  have hΓ'm : Measurable fun p : 𝕍 × (Iic S → ℝ) => (Γ (Θ (Cs n) p.1 p.2)).toReal :=
    (hΓ.comp (hΘ (Cs n))).ennreal_toReal
  have hΓ'1 : ∀ p : 𝕍 × (Iic S → ℝ), |(Γ (Θ (Cs n) p.1 p.2)).toReal| ≤ 1 := fun p => by
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hΓ1 _)
  have h := hN n hn (fun p : 𝕍 × (Iic S → ℝ) => (Γ (Θ (Cs n) p.1 p.2)).toReal) hΓ'm hΓ'1
  -- measurability of the two integrands
  have hresc : ∀ ω, LengthMarkov.GermDensity.rescale S (aV (Cs n) (V ω)) (D ω) = rescaleLim S (aV (Cs n) (V ω)) (D ω) :=
    fun ω => (rescaleLim_of_continuous (hDc ω) _ _).symm
  have hfm : Measurable fun ω => Γ (Θ (Cs n) (V ω) (LengthMarkov.GermDensity.rescale S (aV (Cs n) (V ω)) (D ω))) := by
    simp_rw [hresc]
    exact (hΓ.comp (hΘ (Cs n))).comp (hV.prodMk ((measurable_rescaleLim S).comp
      (((haV _).comp hV).prodMk hD)))
  have hjm : Measurable fun p : Ω₁ × (ℝ≥0 → ℝ) => Γ (Θ (Cs n) (V p.1) (pathRestr S p.2)) :=
    (hΓ.comp (hΘ (Cs n))).comp ((hV.comp measurable_fst).prodMk
      ((measurable_pathRestr S).comp measurable_snd))
  have hgm : Measurable fun ω => ∫⁻ b, Γ (Θ (Cs n) (V ω) (pathRestr S b)) ∂W :=
    hjm.lintegral_prod_right'
  have hinner : ∀ ω, ∫ b, (Γ (Θ (Cs n) (V ω) (pathRestr S b))).toReal ∂W =
      (∫⁻ b, Γ (Θ (Cs n) (V ω) (pathRestr S b)) ∂W).toReal := fun ω =>
    integral_toReal (hjm.comp (measurable_const.prodMk measurable_id)).aemeasurable
      (Eventually.of_forall fun b => (hΓ1 _).trans_lt ENNReal.one_lt_top)
  refine lintegral_two_sided_of_integral hfm.aemeasurable hgm.aemeasurable (fun ω => hΓ1 _)
    (fun ω => ?_) hηt (by simpa only [hinner] using h)
  calc ∫⁻ b, Γ (Θ (Cs n) (V ω) (pathRestr S b)) ∂W ≤ ∫⁻ _, 1 ∂W := lintegral_mono fun b => hΓ1 _
    _ = 1 := by simp

end GermRepair

section ModelRepair

open D3Plus

variable {Ω₁ : Type} [MeasurableSpace Ω₁]
variable {γ α r κ : ℝ} {ρ₀ : Measure ℂ} {Q : Measure Ω₁} [IsProbabilityMeasure Q]
  {X' : Ω₁ → FieldSample} {E' : Type} [MeasurableSpace E'] {Ξ : Ω₁ → E'}
variable {𝕍 : Type*} [MeasurableSpace 𝕍] {F : Type} [MeasurableSpace F] (fr : ℕ → FieldSample → F)

/-- Steps (3)–(4) for the germ-free correction `g₀`: E5-DENS with the scales of D3⁺(iii). -/
theorem tvNear_model_germ' {g₀ : Ω₁ → ℂ → ℝ} (hS₀ : D3Plus.Setup γ α r ρ₀ Q X' Ξ g₀)
    (hm₀ : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (g₀ ω)) (R : ℕ)
    {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {Rr : Measure Ω₁} [IsProbabilityMeasure Rr] {w : Ω₁ → ℝ≥0∞} (hw1 : ∫⁻ ω, w ω ∂Rr = 1)
    (hQ : Q = Rr.withDensity w)
    {V : Ω₁ → 𝕍} (hV : Measurable V) {D : Ω₁ → ℝ≥0 → ℝ} (hD : Measurable D)
    (hDc : ∀ ω, Continuous (D ω)) {u₀ : ℝ≥0} (hu₀ : 0 < u₀)
    (hind : IndepFun V (fun ω => pathRestr u₀ (D ω)) Rr)
    (hDW : Rr.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀))
    (a : ℝ → 𝕍 → ℝ) (ha : ∀ C, Measurable (a C)) (y : ℝ → 𝕍 → F)
    (hy : ∀ C, Measurable (y C))
    (hay : ∀ C ω, zScale γ α r ρ₀ C (X' ω) (g₀ ω) = a C (V ω) ∧
      zLoc fr γ α r ρ₀ R C (X' ω) (g₀ ω) = y C (V ω)) :
    TVNear (fun C Γ => ∫⁻ ω, modelInt fr κ γ α r ρ₀ R X' g₀ D C Γ ω ∂Q)
      (fun C Γ => ∫⁻ ω, germInt fr κ γ α r ρ₀ R W X' g₀ C Γ ω ∂Q) := by
  classical
  set aV : ℝ → 𝕍 → ℝ≥0 := fun C v => if 0 < a C v then (a C v).toNNReal else 1 with haV_def
  have haV : ∀ C, Measurable (aV C) := fun C =>
    Measurable.ite (measurableSet_lt measurable_const (ha C)) (ha C).real_toNNReal
      measurable_const
  have hapos : ∀ C v, 0 < aV C v := fun C v => by
    simp only [haV_def]
    split_ifs with h
    · exact Real.toNNReal_pos.2 h
    · exact one_pos
  set Θ : ℝ → 𝕍 → (Iic (R : ℝ≥0) → ℝ) → F × (ℝ≥0 → ℝ) :=
    fun C v f => (y C v, drvWin κ R f) with hΘ_def
  have hΘ : ∀ C, Measurable (Function.uncurry (Θ C)) := fun C =>
    ((hy C).comp measurable_fst).prodMk ((measurable_drvWin κ R).comp measurable_snd)
  -- (a) the model integrand agrees with the E5-DENS integrand off the D3⁺(iii) bad set
  have h1 : TVNear (fun C Γ => ∫⁻ ω, modelInt fr κ γ α r ρ₀ R X' g₀ D C Γ ω ∂Q)
      (fun C Γ => ∫⁻ ω, Γ (Θ C (V ω) (LengthMarkov.GermDensity.rescale (R : ℝ≥0)
        (aV C (V ω)) (D ω))) ∂Q) := by
    refine TVNear.of_eq_off _ (fun C Γ ω => Γ (Θ C (V ω) (LengthMarkov.GermDensity.rescale
        (R : ℝ≥0) (aV C (V ω)) (D ω))))
      (scaleBad γ α r ρ₀ X' g₀ 1) (measurableSet_scaleBad hm₀ 1)
      (fun C Γ h1 ω => h1 _) (fun C Γ h1 ω => h1 _) ?_
      (fun Cs hCs => tendsto_scaleBad hS₀ hm₀ one_pos Cs hCs)
    intro C Γ ω hω
    simp only [scaleBad, Set.mem_ofPred_eq, not_not] at hω
    obtain ⟨e1, e2⟩ := hay C ω
    have hpos : 0 < a C (V ω) := e1 ▸ hω.1
    simp only [modelInt, hΘ_def, haV_def, if_pos hpos, e1, e2]
  -- (b) E5-DENS
  have hprob : ∀ Cs : ℕ → ℝ, Tendsto Cs atTop atTop → ∀ ε : ℝ≥0, 0 < ε →
      Tendsto (fun n => Rr.withDensity w {ω | ε ≤ aV (Cs n) (V ω)}) atTop (𝓝 0) := by
    intro Cs hCs ε hε
    rw [← hQ]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_scaleBad hS₀ hm₀ (ε := (ε : ℝ)) (by exact_mod_cast hε) Cs hCs)
      (fun n => zero_le) (fun n => measure_mono fun ω hω => ?_)
    simp only [Set.mem_ofPred_eq] at hω
    simp only [scaleBad, Set.mem_ofPred_eq]
    rintro ⟨hp, hlt⟩
    obtain ⟨e1, -⟩ := hay (Cs n) ω
    rw [e1] at hp hlt
    have : aV (Cs n) (V ω) = (a (Cs n) (V ω)).toNNReal := by simp only [haV_def, if_pos hp]
    rw [this] at hω
    have h2 : (ε : ℝ) ≤ a (Cs n) (V ω) := by
      have := (Real.le_toNNReal_iff_coe_le hp.le).1 hω
      exact this
    linarith
  have h2 := tvNear_germ' (W := W) (Rr := Rr) hW hV hD hDc hu₀ hind hDW hw1 (R : ℝ≥0) aV haV
    hapos hprob Θ hΘ
  rw [← hQ] at h2
  -- (c) the germ-replaced integrand is `germInt`
  refine h1.trans (h2.trans (TVNear.of_eventually_eq (Eventually.of_forall fun C Γ _ _ => ?_)))
  refine lintegral_congr fun ω => ?_
  simp only [germInt, hΘ_def, (hay C ω).2]

/-- **The zoom model is TV-near the target** (E5 steps (2)–(5)): from D3⁺(i), D3⁺(ii), the
proved D3⁺(iii) and E5-DENS. -/
theorem tvNear_model' (hI : D3IG fr) (hII : D3IIG fr) {g g₀ : Ω₁ → ℂ → ℝ}
    (hS : D3Plus.Setup γ α r ρ₀ Q X' Ξ g) (hS₀ : D3Plus.Setup γ α r ρ₀ Q X' Ξ g₀)
    (hm : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (g ω))
    (hm₀ : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (g₀ ω))
    (hbadm : ∀ K : ℝ, MeasurableSet[condSigma Ξ X' r] (gBad r g g₀ K))
    (hbad : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ Q (gBad r g g₀ K) ≤ ε) (R : ℕ)
    {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W)
    {Rr : Measure Ω₁} [IsProbabilityMeasure Rr] {w : Ω₁ → ℝ≥0∞} (hw1 : ∫⁻ ω, w ω ∂Rr = 1)
    (hQ : Q = Rr.withDensity w)
    {V : Ω₁ → 𝕍} (hV : Measurable V) {D : Ω₁ → ℝ≥0 → ℝ} (hD : Measurable D)
    (hDm : Measurable[condSigma Ξ X' r] D)
    (hDc : ∀ ω, Continuous (D ω)) {u₀ : ℝ≥0} (hu₀ : 0 < u₀)
    (hind : IndepFun V (fun ω => pathRestr u₀ (D ω)) Rr)
    (hDW : Rr.map (fun ω => pathRestr u₀ (D ω)) = W.map (pathRestr u₀))
    (a : ℝ → 𝕍 → ℝ) (ha : ∀ C, Measurable (a C)) (y : ℝ → 𝕍 → F)
    (hy : ∀ C, Measurable (y C))
    (hay : ∀ C ω, zScale γ α r ρ₀ C (X' ω) (g₀ ω) = a C (V ω) ∧
      zLoc fr γ α r ρ₀ R C (X' ω) (g₀ ω) = y C (V ω))
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {Y : Ω' → FieldSample} (hY : IsQuantumWedge γ α Y P') :
    TVNear (fun C Γ => ∫⁻ ω, modelInt fr κ γ α r ρ₀ R X' g D C Γ ω ∂Q) (targetF fr κ R W P' Y) := by
  refine TVNear.of_approx fun η hη => ?_
  obtain ⟨K, hK0, hKη⟩ := hbad η hη
  set bad := gBad r g g₀ K with hbad_def
  have hbadA : MeasurableSet bad := condSigma_le_ambient hS _ (hbadm K)
  have hSK := setup_piecewise hS hS₀ (hbadm K)
  have hmK : ∀ C, Measurable fun ω => zScale γ α r ρ₀ C (X' ω) (switchG bad g g₀ ω) := by
    intro C
    classical
    have : (fun ω => zScale γ α r ρ₀ C (X' ω) (switchG bad g g₀ ω)) =
        bad.piecewise (fun ω => zScale γ α r ρ₀ C (X' ω) (g₀ ω))
          (fun ω => zScale γ α r ρ₀ C (X' ω) (g ω)) := by
      funext ω
      by_cases h : ω ∈ bad
      · rw [switchG_of_mem h, Set.piecewise_eq_of_mem _ _ _ h]
      · rw [switchG_of_not_mem h, Set.piecewise_eq_of_notMem _ _ _ h]
    rw [this]
    exact Measurable.piecewise hbadA (hm₀ C) (hm C)
  have hKb : ∀ ω, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar,
      |switchG bad g g₀ ω z - g₀ ω z| ≤ K := by
    intro ω z hz
    by_cases h : ω ∈ bad
    · rw [switchG_of_mem h, sub_self, abs_zero]; exact hK0
    · rw [switchG_of_not_mem h]
      simp only [hbad_def, gBad, Set.mem_ofPred_eq, not_not] at h
      exact h z hz
  refine ⟨fun C Γ => ∫⁻ ω, modelInt fr κ γ α r ρ₀ R X' (switchG bad g g₀) D C Γ ω ∂Q, ?_, ?_⟩
  · exact (tvNear_model_pair fr hSK hmK R hDc).trans ((tvNear_pair_lsc fr hII hSK hS₀ hKb R hDm).trans
      ((tvNear_model_pair fr hS₀ hm₀ R hDc).symm.trans
        ((tvNear_model_germ' fr hS₀ hm₀ R hW hw1 hQ hV hD hDc hu₀ hind hDW a ha y hy hay).trans
          (tvNear_germ_target fr hI hS₀ hY R))))
  · refine Eventually.of_forall fun C Γ _ hΓ1 => ?_
    have heq : ∀ ω, ω ∉ bad → modelInt fr κ γ α r ρ₀ R X' g D C Γ ω =
        modelInt fr κ γ α r ρ₀ R X' (switchG bad g g₀) D C Γ ω := fun ω h => by
      simp only [modelInt, switchG_of_not_mem h]
    exact ⟨(lintegral_le_add_of_eq_off (fun ω => hΓ1 _) hbadA heq).trans (by gcongr),
      (lintegral_le_add_of_eq_off (fun ω => hΓ1 _) hbadA fun ω h => (heq ω h).symm).trans
        (by gcongr)⟩

end ModelRepair

/-- **The zoom model is TV-near the target** (`ZoomModel.tvNear` under a Wiener measure `W`). -/
theorem ZoomModel.tvNear' {F : Type} [MeasurableSpace F] {fr : ℕ → FieldSample → F} {κ : ℝ}
    {R : ℕ} {W : Measure (ℝ≥0 → ℝ)} [IsProbabilityMeasure W]
    (hW : IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W) (M : ZoomModel fr κ R W)
    (hI : D3IG fr) (hII : D3IIG fr) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {Y : Ω' → FieldSample}
    (hY : IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P') :
    TVNear M.fn (targetF fr κ R W P' Y) :=
  tvNear_model' fr hI hII M.hS M.hS₀ M.hm M.hm₀ M.hbadm M.hbad R hW M.hw1 M.hQ M.hV M.hD M.hDm
    M.hDc M.hu₀ M.hind M.hDW M.a M.ha M.y M.hy M.hay hY

end E5
end QuantumZipper

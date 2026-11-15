import InteractingSLE.GFF.LocalSets.Prop38Layer

/-!
# Proposition 3.8: the moment bound on one patch

Specification §3.2, proof of Proposition 3.8 (pp. 59–60), packet PROVE-LS-C.

For a patch `U = B(c, 4R)` the event `E = {A₁ ∩ U ⊆ A₂}` (`inclEvent`, measurable for
`σ(A₁) ∨ σ(A₂)`) is the analogue of the specification's `E = {B ∩ U ∩ O = ∅}`: on it,
`(ℍ ∖ A₂) ∩ U ⊆ ℍ ∖ A`, so the Green variance of `ℍ ∖ A` dominates that of `(ℍ ∖ A₂) ∩ U`, and the
Koebe bound on the component of `ℍ ∖ A₂` gives `σ²_{ℍ∖A₂}(ψ) − σ²_{ℍ∖A}(ψ) ≤ 4 τ_n (∫ψ)²` for the
bump `ψ` at a point `y` of the `n`-th dyadic layer of `ℍ ∖ A₂` (`lintegral_layer_indicator_le`,
the hypothesis `hmom` of `ae_eventually_abs_lt_of_layer`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Metric
open scoped ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper LQGMetric
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open GFF (layerSet bumpMass bumpMass_pos bumpFun)

/-! ### The inclusion event `{A₁ ∩ U ⊆ A₂}` -/

section Incl

variable {Ω : Type*}

/-- The closed rational balls `B̄(x_k, 1/(j+1))` (`x_k` a dense sequence). -/
def ratBall (p : ℕ × ℕ) : Set ℂ :=
  closedBall (TopologicalSpace.denseSeq ℂ p.1) (1 / ((p.2 : ℝ) + 1))

open Classical in
/-- A measurable version of the event `{A₁ ∩ U ⊆ A₂}`: every closed rational ball in `U ∩ ℍ` that
avoids `A₂` avoids `A₁`. -/
def inclEvent (A₁ A₂ : Ω → Set ℂ) (U : Set ℂ) : Set Ω :=
  ⋂ p : ℕ × ℕ, if ratBall p ⊆ U ∩ H then
    {ω | Disjoint (ratBall p) (relClosureH (A₂ ω))}ᶜ ∪
      {ω | Disjoint (ratBall p) (relClosureH (A₁ ω))} else univ

theorem measurableSet_inclEvent (A₁ A₂ : Ω → Set ℂ) (U : Set ℂ) :
    MeasurableSet[MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma]
      (inclEvent A₁ A₂ U) := by
  classical
  refine MeasurableSet.iInter fun p => ?_
  by_cases hp : ratBall p ⊆ U ∩ H
  · simp only [hp, ↓reduceIte]
    have hK : IsCompact (ratBall p) := isCompact_closedBall _ _
    have hKH : ratBall p ⊆ H := hp.trans inter_subset_right
    refine MeasurableSet.union (MeasurableSet.compl ?_) ?_
    · exact (le_sup_right : MeasurableSpace.comap A₂ hittingSigma ≤ _) _
        ⟨_, measurableSet_disjoint_relClosureH hK hKH, rfl⟩
    · exact (le_sup_left : MeasurableSpace.comap A₁ hittingSigma ≤ _) _
        ⟨_, measurableSet_disjoint_relClosureH hK hKH, rfl⟩
  · simp only [hp, ↓reduceIte]; exact MeasurableSet.univ

/-- On relatively closed sets, `inclEvent` is the inclusion event. -/
theorem mem_inclEvent_iff {A₁ A₂ : Ω → Set ℂ} {U : Set ℂ} (hU : IsOpen U) {ω : Ω}
    (h₁ : A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω)) (h₂ : A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) :
    ω ∈ inclEvent A₁ A₂ U ↔ A₁ ω ∩ U ⊆ A₂ ω := by
  classical
  simp only [inclEvent, mem_iInter]
  constructor
  · intro h z ⟨hz₁, hzU⟩
    by_contra hz₂
    have hzH : z ∈ H := h₁.1 hz₁
    have hW : IsOpen (U ∩ (H \ A₂ ω)) := hU.inter h₂.2
    obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.1 hW z ⟨hzU, hzH, hz₂⟩
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by positivity)
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z
      (1 / ((j : ℝ) + 1)) (by positivity)
    have hsub : ratBall (k, j) ⊆ U ∩ (H \ A₂ ω) := by
      intro w hw
      refine hεW ?_
      rw [mem_ball]
      have h1 : dist w (TopologicalSpace.denseSeq ℂ k) ≤ 1 / ((j : ℝ) + 1) := hw
      have := dist_triangle w (TopologicalSpace.denseSeq ℂ k) z
      rw [dist_comm] at hk
      linarith
    have hp : ratBall (k, j) ⊆ U ∩ H := fun w hw => ⟨(hsub hw).1, (hsub hw).2.1⟩
    have := h (k, j)
    simp only [hp, ↓reduceIte] at this
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq] at this
    rw [relClosureH_eq h₂.1 h₂.2, relClosureH_eq h₁.1 h₁.2] at this
    rcases this with h' | h'
    · exact h' (Set.disjoint_left.2 fun w hw hw₂ => (hsub hw).2.2 hw₂)
    · have hzB : z ∈ ratBall (k, j) := by
        show dist z (TopologicalSpace.denseSeq ℂ k) ≤ _
        exact hk.le
      exact Set.disjoint_left.1 h' hzB hz₁
  · intro h p
    split_ifs with hp
    · simp only [mem_union, mem_compl_iff, mem_ofPred_eq]
      rw [relClosureH_eq h₂.1 h₂.2, relClosureH_eq h₁.1 h₁.2]
      by_cases hd : Disjoint (ratBall p) (A₂ ω)
      · right
        exact Set.disjoint_left.2 fun w hw hw₁ =>
          Set.disjoint_left.1 hd hw (h ⟨hw₁, (hp hw).1⟩)
      · left; exact hd
    · exact mem_univ _

end Incl

/-! ### Layers of `ℍ ∖ A₂` and the parameters -/

lemma mem_layerSet_compl_iff (S : Set ℂ) (c : ℂ) (R : ℝ) (n : ℕ) (y : ℂ) :
    y ∈ layerSet (H \ relClosureH S) c R n ↔
      dist y c < 3 * R ∧ (1 / 2 : ℝ) ^ (n + 2) ≤ compDist S y ∧
        compDist S y ≤ 2 * (1 / 2 : ℝ) ^ n := by
  constructor
  · rintro ⟨⟨⟨_, hyc⟩, h1⟩, h2⟩
    exact ⟨hyc, h1, h2⟩
  · rintro ⟨hyc, h1, h2⟩
    refine ⟨⟨⟨?_, hyc⟩, h1⟩, h2⟩
    by_contra hy
    have : compDist S y = 0 := infDist_zero_of_mem hy
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 2) := by positivity
    linarith

theorem measurableSet_layerSet_compl {Ω : Type*} [MeasurableSpace Ω] {A : Ω → Set ℂ}
    (hA : Measurable[_, hittingSigma] A) (c : ℂ) (R : ℝ) (n : ℕ) :
    MeasurableSet {p : Ω × ℂ | p.2 ∈ layerSet (H \ relClosureH (A p.1)) c R n} := by
  have e : {p : Ω × ℂ | p.2 ∈ layerSet (H \ relClosureH (A p.1)) c R n} =
      {p : Ω × ℂ | dist p.2 c < 3 * R} ∩ {p | (1 / 2 : ℝ) ^ (n + 2) ≤ compDist (A p.1) p.2} ∩
        {p | compDist (A p.1) p.2 ≤ 2 * (1 / 2 : ℝ) ^ n} := by
    ext p
    simp only [mem_ofPred_eq, mem_inter_iff, mem_layerSet_compl_iff, and_assoc]
  rw [e]
  have hd := measurable_compDist hA
  exact ((measurableSet_lt (measurable_snd.dist measurable_const) measurable_const).inter
    (measurableSet_le measurable_const hd)).inter (measurableSet_le hd measurable_const)

theorem measurableSet_mem_layerSet_compl {Ω : Type*} (A : Ω → Set ℂ) (c : ℂ) (R : ℝ) (n : ℕ)
    (y : ℂ) : MeasurableSet[MeasurableSpace.comap A hittingSigma]
      {ω | y ∈ layerSet (H \ relClosureH (A ω)) c R n} := by
  have hd := @measurable_compDist_left Ω (MeasurableSpace.comap A hittingSigma) A
    (comap_measurable A) y
  have e : {ω | y ∈ layerSet (H \ relClosureH (A ω)) c R n} =
      {ω | dist y c < 3 * R} ∩ {ω | (1 / 2 : ℝ) ^ (n + 2) ≤ compDist (A ω) y} ∩
        {ω | compDist (A ω) y ≤ 2 * (1 / 2 : ℝ) ^ n} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_layerSet_compl_iff, and_assoc]
  rw [e]
  exact ((MeasurableSet.const _).inter (measurableSet_le measurable_const hd)).inter
    (measurableSet_le hd measurable_const)

/-- The Koebe scale `(2a/(cR))^(1/C₂)` is monotone in `a`. -/
lemma koebe_rpow_mono {R a b : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (hab : a ≤ b) :
    (2 * a / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤
      (2 * b / (koebeCovConst * R)) ^ koebeDistExp⁻¹ := by
  have hc := koebeCovConst_pos
  exact Real.rpow_le_rpow (by positivity) (by gcongr) (inv_nonneg.2 koebeDistExp_pos.le)

/-- The Koebe scale at the inner edge `2^{-n-2}` of the `n`-th layer. -/
def tauLo (R : ℝ) (n : ℕ) : ℝ :=
  (2 * (1 / 2 : ℝ) ^ (n + 2) / (koebeCovConst * R)) ^ koebeDistExp⁻¹

/-- The Koebe scale at the outer edge `2 · 2^{-n}` of the `n`-th layer. -/
def tauHi (R : ℝ) (n : ℕ) : ℝ :=
  (2 * (2 * (1 / 2 : ℝ) ^ n) / (koebeCovConst * R)) ^ koebeDistExp⁻¹

/-- The bump radius used on the `n`-th layer. -/
def bumpRad (R : ℝ) (n : ℕ) : ℝ := tauLo R n * (1 / 2 : ℝ) ^ (n + 2) / 2

lemma tauLo_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < tauLo R n :=
  Real.rpow_pos_of_pos (by have := koebeCovConst_pos; positivity) _

lemma bumpRad_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < bumpRad R n := by
  have := tauLo_pos hR n; unfold bumpRad; positivity

lemma tauLo_le_tauHi {R : ℝ} (hR : 0 < R) (n : ℕ) : tauLo R n ≤ tauHi R n :=
  koebe_rpow_mono hR (by positivity) (by
    rw [pow_add]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) n])

lemma bumpRad_lt {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : tauHi R n ≤ 1 / 4) :
    bumpRad R n < (1 / 2 : ℝ) ^ (n + 2) := by
  have h1 := tauLo_le_tauHi hR n
  have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 2) := by positivity
  unfold bumpRad; nlinarith

/-- A point of a layer of `ℍ ∖ A` has its bump ball inside `ℍ ∖ A`. -/
lemma closedBall_bumpRad_subset {S : Set ℂ} {c y : ℂ} {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : tauHi R n ≤ 1 / 4) (hy : y ∈ layerSet (H \ relClosureH S) c R n) :
    closedBall y (bumpRad R n) ⊆ H \ relClosureH S := by
  refine (closedBall_subset_ball ((bumpRad_lt hR hn).trans_le hy.1.2)).trans ?_
  exact ball_infDist_compl_subset

/-! ### The moment bound on a patch -/

section Moment

variable {Ω : Type*} {𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **The pointwise exponential moment on a patch** (hypothesis `hmom` of
`ae_eventually_abs_lt_of_layer`). -/
theorem lintegral_layer_indicator_le {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A₁ A₂ : Ω → Set ℂ}
    (hA₁ : Measurable[mΩ, hittingSigma] A₁) (hA₂ : Measurable[mΩ, hittingSigma] A₂)
    (hA₁c : ∀ᵐ ω ∂P, A₁ ω ⊆ H ∧ IsOpen (H \ A₁ ω))
    (hA₂c : ∀ᵐ ω ∂P, A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω))
    (hunb : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ ω)) z))
    (h𝒥 : 𝒥 ≤ mΩ) (h₂𝒥 : germSigma A₂ h ≤ 𝒥)
    (h₁₂𝒥 : MeasurableSpace.comap A₁ hittingSigma ⊔ MeasurableSpace.comap A₂ hittingSigma ≤ 𝒥)
    {g₀ g₂ : Ω → DistOn upperHalfPlaneOpens} (hg₀m : Measurable[𝒥] g₀)
    (hg₀c : IsCondZeroBoundaryGFF P 𝒥 (fun ω => H \ (A₁ ω ∪ A₂ ω)) fun ω => h ω - g₀ ω)
    (hg₂ : IsLocalSetMean A₂ h P g₂) {c : ℂ} {R : ℝ} (hR : 0 < R) {n : ℕ}
    (hn : tauHi R n ≤ 1 / 4) (y : ℂ) (l : ℝ) (hl : 2 * l ^ 2 * tauHi R n ≤ 1) :
    ∫⁻ ω, (inclEvent A₁ A₂ (ball c (4 * R)) ∩
        {ω | y ∈ layerSet (H \ relClosureH (A₂ ω)) c R n}).indicator
      (fun ω => ENNReal.ofReal (Real.exp (l * (bumpPair (fun ω => g₀ ω - g₂ ω) (bumpRad R n)
        (bumpRad_pos hR n) (ω, y) / (bumpRad R n ^ 2 * bumpMass))))) ω ∂P ≤
      ENNReal.ofReal (Real.exp 1) := by
  set δ := bumpRad R n with hδdef
  have hδ : 0 < δ := bumpRad_pos hR n
  set m := δ ^ 2 * bumpMass with hm
  have hm0 : 0 < m := by have := bumpMass_pos; positivity
  set E := inclEvent A₁ A₂ (ball c (4 * R))
  set F := {ω | y ∈ layerSet (H \ relClosureH (A₂ ω)) c R n}
  by_cases hy : δ < y.im
  · set ψ := bumpTestH δ hδ y with hψ
    have hψc : ⇑ψ = bumpFun y δ := coe_bumpTestH_of_lt hδ hy
    have hAm : Measurable[mΩ, hittingSigma] fun ω => A₁ ω ∪ A₂ ω :=
      measurable_union_hitting hA₁ hA₂
    have hAc : ∀ᵐ ω ∂P, (A₁ ω ∪ A₂ ω) ⊆ H ∧ IsOpen (H \ (A₁ ω ∪ A₂ ω)) := by
      filter_upwards [hA₁c, hA₂c] with ω ⟨hs₁, ho₁⟩ ⟨hs₂, ho₂⟩
      refine ⟨union_subset hs₁ hs₂, ?_⟩
      have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
        ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
      rw [e]; exact ho₁.inter ho₂
    have hE : MeasurableSet[𝒥] E := h₁₂𝒥 _ (measurableSet_inclEvent A₁ A₂ _)
    have hF : MeasurableSet[MeasurableSpace.comap A₂ hittingSigma] F :=
      measurableSet_mem_layerSet_compl A₂ c R n y
    have hκ : ∀ᵐ ω ∂P, ω ∈ E → ω ∈ F →
        zeroGFFTestCov (H \ A₂ ω) ψ ψ - zeroGFFTestCov (H \ (A₁ ω ∪ A₂ ω)) ψ ψ ≤
          4 * tauHi R n * m ^ 2 := by
      filter_upwards [hA₁c, hA₂c, hunb] with ω h1 h2 hu hωE hωF
      have hincl := (mem_inclEvent_iff isOpen_ball h1 h2).1 hωE
      have hrc := relClosureH_eq h2.1 h2.2
      have hωF' : y ∈ layerSet (H \ A₂ ω) c R n := by
        have := hωF; simp only [F, mem_ofPred_eq, hrc] at this; exact this
      obtain ⟨⟨⟨hyO, hyc⟩, hd1⟩, hd2⟩ := hωF'
      rw [mem_ball] at hyc
      set d := infDist y (H \ A₂ ω)ᶜ with hd
      have ht : (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ ≤ tauHi R n :=
        koebe_rpow_mono hR infDist_nonneg hd2
      have htlo : tauLo R n ≤ (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ :=
        koebe_rpow_mono hR (by positivity) hd1
      have hball : ball y R ⊆ ball c (4 * R) := fun z hz => by
        rw [mem_ball] at hz ⊢; have := dist_triangle z y c; linarith
      have hG2 := zeroGFFTestCov_sub_le_of_component h2.2 isOpen_ball hu hyO hR hball
        (ht.trans hn) ψ (fun z => by rw [hψc]; exact GFF.bumpFun_nonneg y δ z) (fun z hz => by
          rw [hψc] at hz
          have hzy : dist z y < δ := by
            by_contra hge
            exact hz (GFF.bumpFun_eq_zero hδ (not_lt.1 hge))
          have h3 : δ < tauLo R n * (1 / 2 : ℝ) ^ (n + 2) := by
            have := tauLo_pos hR n
            have : (0 : ℝ) < (1 / 2 : ℝ) ^ (n + 2) := by positivity
            rw [hδdef, bumpRad]; nlinarith
          have h4 : tauLo R n * (1 / 2 : ℝ) ^ (n + 2) ≤
              (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * d :=
            mul_le_mul htlo hd1 (by positivity) (le_trans (tauLo_pos hR n).le htlo)
          linarith)
      have hint : ∫ z, ψ z = m := by rw [hψc]; exact GFF.integral_bumpFun hδ
      rw [hint] at hG2
      have hsub : (H \ A₂ ω) ∩ ball c (4 * R) ⊆ H \ (A₁ ω ∪ A₂ ω) := by
        rintro z ⟨⟨hzH, hz₂⟩, hzU⟩
        refine ⟨hzH, fun h' => h'.elim (fun hz₁ => hz₂ (hincl ⟨hz₁, hzU⟩)) hz₂⟩
      have hmono := zeroGFFTestCov_mono (h2.2.inter isOpen_ball)
        (by have e : H \ (A₁ ω ∪ A₂ ω) = (H \ A₁ ω) ∩ (H \ A₂ ω) := by
              ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff]; tauto
            rw [e]; exact h1.2.inter h2.2) hsub sdiff_subset ψ
      have h5 : 4 * (2 * d / (koebeCovConst * R)) ^ koebeDistExp⁻¹ * m ^ 2 ≤
          4 * tauHi R n * m ^ 2 := by gcongr
      linarith
    have key := lintegral_indicator_exp_meanDiff_le (𝒥 := 𝒥) hh hAm hA₂ hAc hA₂c h𝒥 h₂𝒥 hg₀m hg₀c
      hg₂ ψ hE hF hκ (l / m)
    have e1 : ∀ ω, bumpPair (fun ω => g₀ ω - g₂ ω) δ (bumpRad_pos hR n) (ω, y) =
        g₀ ω ψ - g₂ ω ψ := fun ω => by
      simp only [bumpPair, hy, ↓reduceIte, sub_apply]
      rfl
    have e4 : ∀ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l *
        (bumpPair (fun ω => g₀ ω - g₂ ω) δ (bumpRad_pos hR n) (ω, y) / m)))) ω =
        (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l / m * (g₀ ω ψ - g₂ ω ψ)))) ω :=
      fun ω => by
        have : ∀ ω, l * (bumpPair (fun ω => g₀ ω - g₂ ω) δ (bumpRad_pos hR n) (ω, y) / m) =
            l / m * (g₀ ω ψ - g₂ ω ψ) := fun ω => by rw [e1]; ring
        simp only [this]
    rw [lintegral_congr e4]
    refine key.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
    have e3 : (l / m) ^ 2 * (4 * tauHi R n * m ^ 2) / 2 = 2 * l ^ 2 * tauHi R n := by
      field_simp
      ring
    rw [e3]; exact hl
  · have hF0 : ∀ ω, ω ∉ F := by
      intro ω hω
      exact hy ((closedBall_subset_H_iff hδ.le).1
        ((closedBall_bumpRad_subset hR hn hω).trans sdiff_subset))
    have h0 : ∀ ω, (E ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l *
        (bumpPair (fun ω => g₀ ω - g₂ ω) δ hδ (ω, y) / m)))) ω = 0 := fun ω =>
      indicator_of_notMem (fun h => hF0 ω h.2) _
    calc _ = ∫⁻ _, (0 : ℝ≥0∞) ∂P := lintegral_congr h0
      _ = 0 := lintegral_zero
      _ ≤ _ := zero_le

end Moment

end LocalSets
end InteractingSLE

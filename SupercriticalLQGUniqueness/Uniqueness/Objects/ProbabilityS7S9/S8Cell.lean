import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S8Local
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9.S7
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LMIter2T




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

open LQGMetric (DistC addConst circleAvg)

 

 


theorem acr_le_ambientAcross_of_barrier (D : LSCMetric) (hB : BiLipschitz.Barrier.Barrier D)
    (hL : D.IsLengthSpace) (w : ℂ) {a b : ℝ} (hab : a ≤ b) :
    Objects.CorrectedEvent.acr D w a b ≤ Objects.CorrectedEvent.ambientAcross D w a b := by
  unfold Objects.CorrectedEvent.ambientAcross
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε hlt => ?_
  obtain ⟨P, s, t, hP, hPs, hPt, hlen⟩ := hL x y hlt (ε : ℝ) (by exact_mod_cast hε)
  rw [ENNReal.ofReal_coe_nnreal] at hlen
  have hfin : D.len P s t ≠ ⊤ :=
    (hlen.trans_lt (ENNReal.add_lt_top.2 ⟨hlt, ENNReal.coe_lt_top⟩)).ne
  have hcont := BiLipschitz.Barrier.continuousOn_of_barrier D hB hP hfin
  have hf : ContinuousOn (fun u => dist (P u) w) (Icc s t) :=
    (continuous_id.dist continuous_const).comp_continuousOn hcont
  have hxa : dist (P s) w ≤ a := by rw [hPs]; exact (mem_sphere.mp hx).le
  have hyb : b ≤ dist (P t) w := by rw [hPt]; exact (mem_sphere.mp hy).ge
  obtain ⟨σ, τ, hsσ, hστ, hτt, hfσ, hfτ, hin⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hP.1 hf hab hxa hyb
  have hPστ : D.IsCurve P σ τ := ⟨hστ, hP.2.mono (Icc_subset_Icc hsσ hτt)⟩
  have htrace : P '' Icc σ τ ⊆ Objects.CorrectedEvent.cann w a b := by
    rintro _ ⟨u, hu, rfl⟩
    exact hin u hu
  have hσ : P σ ∈ sphere w a := mem_sphere.mpr hfσ
  have hτ : P τ ∈ sphere w b := mem_sphere.mpr hfτ
  calc Objects.CorrectedEvent.acr D w a b ≤ D.len P σ τ := by
        unfold Objects.CorrectedEvent.acr
        exact iInf_le_of_le P (iInf_le_of_le σ (iInf_le_of_le τ (iInf_le_of_le hPστ
          (iInf_le_of_le htrace (iInf_le_of_le hσ (iInf_le _ hτ))))))
    _ ≤ D.len P s t := eVariationOn.mono _ (Icc_subset_Icc hsσ hτt)
    _ ≤ D (x, y) + ε := hlen

 
theorem ambientAcross_eq_acrossDist (D : LSCMetric) (w : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    Objects.CorrectedEvent.ambientAcross D w a b = acrossDist D ⟨(w, a, b), ha, hab⟩ := rfl

 

 
def SupProxyAt (κ : ℝ) (d : LSCMetric) (R : ℝ) (w : ℂ) : Prop :=
  ∃ hR : 0 < R, SupProxy κ d hR w

theorem supProxyAt_iff (κ : ℝ) (d : LSCMetric) {R : ℝ} (hR : 0 < R) (w : ℂ) :
    SupProxyAt κ d R w ↔ SupProxy κ d hR w :=
  ⟨fun ⟨_, h⟩ => h, fun h => ⟨hR, h⟩⟩

 


theorem supGood_of_proxy (C : Objects.CorrectedEvent.Constants) (d : LSCMetric) (c : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell)
    (k : ℕ)
    (hP : SupProxyAt (1 / 2 * Real.exp (-C.ξ * C.A_max)) d (Objects.CorrectedEvent.supRadius C k)
      (Objects.CorrectedEvent.cellCenter c s l))
    (hfin : Objects.CorrectedEvent.acr d (Objects.CorrectedEvent.cellCenter c s l) ((1 + 1 / 20) * Objects.CorrectedEvent.supRadius C k)
      ((2 - 1 / 20) * Objects.CorrectedEvent.supRadius C k) < ⊤) :
    Objects.CorrectedEvent.supGood C d c s l k := by
  obtain ⟨hR, hprox⟩ := hP
  set R := Objects.CorrectedEvent.supRadius C k with hRdef
  set w := Objects.CorrectedEvent.cellCenter c s l with hwdef
  obtain ⟨hfinO, hle, hpos⟩ := hprox
  have hout : Objects.CorrectedEvent.around d w ((2 + 1 / 20) * R) ((3 - 1 / 20) * R) =
      aroundDist d (supOuter hR w) :=
    around_eq_aroundDist d w _ _ (by positivity) (by nlinarith)
  have hin : acrossDist d (supInner hR w) ≤
      Objects.CorrectedEvent.acr d w ((1 + 1 / 20) * R) ((2 - 1 / 20) * R) := by
    have h1 : Objects.CorrectedEvent.ambientAcross d w ((1 + 1 / 20) * R) ((2 - 1 / 20) * R) =
        acrossDist d (supInner hR w) :=
      ambientAcross_eq_acrossDist d w (by positivity) (by nlinarith)
    rw [← h1]
    exact Objects.ProbabilityS1S2.ambientAcross_le_acr d w _ _
  change Objects.CorrectedEvent.around d w ((2 + 1 / 20) * R) ((3 - 1 / 20) * R) < ⊤ ∧
    0 < Objects.CorrectedEvent.acr d w ((1 + 1 / 20) * R) ((2 - 1 / 20) * R) ∧
    Objects.CorrectedEvent.acr d w ((1 + 1 / 20) * R) ((2 - 1 / 20) * R) < ⊤ ∧
    Objects.CorrectedEvent.around d w ((2 + 1 / 20) * R) ((3 - 1 / 20) * R) ≤
      ENNReal.ofReal (1 / 2 * Real.exp (-C.ξ * C.A_max)) *
        Objects.CorrectedEvent.acr d w ((1 + 1 / 20) * R) ((2 - 1 / 20) * R)
  rw [hout]
  exact ⟨hfinO, hpos.trans_le hin, hfin, hle.trans (mul_le_mul' le_rfl hin)⟩

 

 
theorem ae_acrossDist_lt_top (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (A : EuclideanAnnulus) : ∀ᵐ g ∂μ, acrossDist (D g) A < ⊤ := by
  have hV := (hD.tightness μ id hμ (fun r g => circleAvg g r 0)
    (fun r => ae_isCircleAverage_old hμ.1 r 0) A).1
  set r1 : Ioi (0 : ℝ) := ⟨1, Set.mem_Ioi.mpr one_pos⟩
  have hsub : ∀ M : ℝ, {g : DistC | ¬ acrossDist (D g) A < ⊤} ⊆
      {g | ENNReal.ofReal M < ENNReal.ofReal (((r1 : ℝ)) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * circleAvg (id g) r1 0))) *
          acrossDist (D (id g)) (A.dilate r1 r1.2)} := by
    intro M g hg
    simp only [mem_ofPred_eq, not_lt, top_le_iff] at hg
    simp only [mem_ofPred_eq, id_eq]
    have hA : A.dilate (r1 : ℝ) r1.2 = A := Positivity.Witnesses.dilate_one A
    rw [hA, hg]
    have hn : ENNReal.ofReal (((r1 : ℝ)) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * circleAvg g r1 0))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (mul_pos (Real.rpow_pos_of_pos one_pos _) (Real.exp_pos _))).ne'
    rw [ENNReal.mul_top hn]
    exact ENNReal.ofReal_lt_top
  have hzero : μ {g : DistC | ¬ acrossDist (D g) A < ⊤} = 0 := by
    refine le_antisymm ?_ (zero_le)
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨M, _, hM⟩ := hV.2 ε (by exact_mod_cast hε)
    rw [zero_add]
    calc μ {g : DistC | ¬ acrossDist (D g) A < ⊤} ≤ _ := measure_mono (hsub M)
      _ ≤ ENNReal.ofReal ε := (hM r1).1
      _ = ε := ENNReal.ofReal_coe_nnreal
  exact ae_iff.2 hzero

 

theorem four_pow_scale (R₀ : ℝ) {K j : ℕ} (hj : j ≤ K + 1) :
    (4 : ℝ) ^ (K + 2) * R₀ * (1 / 4) ^ j / 4 = 4 ^ (K + 1 - j) * R₀ := by
  have hsplit : (4 : ℝ) ^ (K + 2) = 4 ^ (K + 1 - j) * 4 ^ j * 4 := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have h4 : (4 : ℝ) ^ j * (1 / 4) ^ j = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hsplit]
  calc (4 : ℝ) ^ (K + 1 - j) * 4 ^ j * 4 * R₀ * (1 / 4) ^ j / 4
      = 4 ^ (K + 1 - j) * R₀ * (4 ^ j * (1 / 4) ^ j) := by ring
    _ = 4 ^ (K + 1 - j) * R₀ := by rw [h4, mul_one]

 


theorem supProxy_iteration (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ (w : ℂ) (R₀ : ℝ), 0 < R₀ → ∀ K : ℕ, 1 ≤ K →
      μ {g | ∀ k ∈ Finset.Icc 1 K, ¬ SupProxyAt κ (D g) (4 ^ k * R₀) w} ≤
        ENNReal.ofReal (c * Real.exp (-a * K)) := by
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  obtain ⟨p₀, hp0, hp1, hmarg⟩ := supProxy_marginal ξ Q hQ D hD κ hκ
  obtain ⟨a, b, c, ha, hb0, _, hc0, H⟩ :=
    TwoScale.S36.annulus_iteration2_ae_translated_open (1 / 4) (3 / 4) (by norm_num) (by norm_num)
      (by norm_num) p₀ hp0 hp1
  refine ⟨a, c, ha, hc0, ?_⟩
  intro w R₀ hR₀ K hK
  set ρ : ℕ → ℝ := fun j => (4 : ℝ) ^ (K + 2) * R₀ * (1 / 4) ^ j with hρdef
  have hρpos : ∀ j, 0 < ρ j := fun j => by positivity
  have hρsucc : ∀ j, ρ (j + 1) = ρ j * (1 / 4) := by
    intro j
    show (4 : ℝ) ^ (K + 2) * R₀ * (1 / 4) ^ (j + 1) = (4 : ℝ) ^ (K + 2) * R₀ * (1 / 4) ^ j * (1 / 4)
    rw [pow_succ]
    ring
  have hρanti : Antitone ρ := by
    refine antitone_nat_of_succ_le fun j => ?_
    rw [hρsucc]
    have := hρpos j
    linarith
  have hρratio : ∀ j, ρ (j + 1) / ρ j ≤ 1 / 4 := by
    intro j
    rw [hρsucc, mul_comm, mul_div_assoc, div_self (hρpos j).ne', mul_one]
  set E : ℕ → Set DistC := fun j => {g | SupProxyAt κ (D g) (ρ j / 4) w} with hEdef
  have hEeq : ∀ j, E j = {g | SupProxy κ (D (id g)) (show 0 < ρ j / 4 by
      have := hρpos j; positivity) w} := by
    intro j
    ext g
    exact supProxyAt_iff κ (D g) _ w
  have hE : ∀ j, LQGMetric.Blueprint.AEEventIn μ
      (LQGMetric.Blueprint.fieldSigma
        (fun g => addConst (id g) (-circleAvg (id g) (ρ j) w))
        (LQGMetric.Blueprint.annulus w ((1 / 4) * ρ j) ((3 / 4) * ρ j))) (E j) := by
    intro j
    rw [hEeq j]
    exact supProxy_aeEventIn μ id hμ ξ Q D hD κ (hρpos j) w
  have hpE : ∀ j, ENNReal.ofReal p₀ ≤ μ (E j) := by
    intro j
    rw [hEeq j]
    exact hmarg μ id hμ (ρ j / 4) _ w
  have hcount := H μ id hμ.1 w ρ E hρpos hρanti hρratio hE hpE K
  refine le_trans (measure_mono ?_) hcount
  intro g hg
  simp only [mem_ofPred_eq] at hg ⊢
  have hzero : LQGMetric.Blueprint.countOcc E K g = 0 := by
    classical
    unfold LQGMetric.Blueprint.countOcc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hgj
    have hj' := Finset.mem_Icc.mp hj
    have hk : K + 1 - j ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    apply hg (K + 1 - j) hk
    have hscale : ρ j / 4 = 4 ^ (K + 1 - j) * R₀ := four_pow_scale R₀ (by omega)
    have hgj' : SupProxyAt κ (D g) (ρ j / 4) w := hgj
    rw [hscale] at hgj'
    exact hgj'
  rw [hzero]
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  simp only [Nat.cast_zero]
  nlinarith

 

 
theorem supRadius_eq (C : Objects.CorrectedEvent.Constants) (k : ℕ) :
    Objects.CorrectedEvent.supRadius C k = 4 ^ k * (2 * C.A_sup * C.r) := by
  unfold Objects.CorrectedEvent.supRadius
  ring

 



theorem badCell_subset_measurable (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (Amax : ℝ) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q → C.A_max = Amax →
      ∀ (c₀ : ℂ) (s : ℝ) (l : Objects.CorrectedEvent.Cell), 1 ≤ Objects.CorrectedEvent.supK C →
      ∃ B : Set DistC, MeasurableSet B ∧
        {g | Objects.CorrectedEvent.badCell C (D g) c₀ s l} ⊆ B ∧
        μ B ≤ ENNReal.ofReal (c * Real.exp (-a * (Objects.CorrectedEvent.supK C : ℝ))) := by
  set κ : ℝ := 1 / 2 * Real.exp (-(ξ : ℝ) * Amax) with hκdef
  have hκ : 0 < κ := by positivity
  obtain ⟨a, c, ha, hc, H⟩ := supProxy_iteration μ hμ ξ Q D hD κ hκ
  refine ⟨a, c, ha, hc, ?_⟩
  intro C hξ hQ hAmax c₀ s l hK
  have hR₀ : 0 < 2 * C.A_sup * C.r := by
    have := C.supPos
    have := C.rPos
    positivity
  set K := Objects.CorrectedEvent.supK C with hKdef
  set w := Objects.CorrectedEvent.cellCenter c₀ s l with hwdef
  set R₀ := 2 * C.A_sup * C.r with hR₀def
  
  have hgff : LQGMetric.IsGFFPlusCont (id : DistC → DistC) μ :=
    LQGMetric.GM.detGFFPlusCont hμ.1
  have hQ' : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hreg : ∀ᵐ g ∂μ, BiLipschitz.Barrier.Barrier (D g) ∧ (D g).IsLengthSpace ∧
      ∀ k ∈ Finset.Icc 1 K, ∀ hk : 0 < 4 ^ k * R₀,
        acrossDist (D g) (supInner hk w) < ⊤ := by
    have hfinK : ∀ᵐ g ∂μ, ∀ k : ℕ, ∀ hk : 0 < 4 ^ k * R₀,
        acrossDist (D g) (supInner hk w) < ⊤ := by
      refine ae_all_iff.2 fun k => ?_
      have hk : 0 < (4 : ℝ) ^ k * R₀ := by positivity
      filter_upwards [ae_acrossDist_lt_top μ hμ ξ Q D hD (supInner hk w)] with g hg hk'
      exact hg
    filter_upwards [BiLipschitz.Barrier.ae_barrier hD hQ' μ id hμ, hD.length μ id hgff, hfinK] with g hB hL hF
    exact ⟨hB, hL, fun k _ hk => hF k hk⟩
  obtain ⟨N, hNsub, hNm, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.1 hreg)
  set E : ℕ → Set DistC := fun k => {g | SupProxyAt κ (D g) (4 ^ k * R₀) w} with hEdef
  have hEm : ∀ k, MeasurableSet (E k) := by
    intro k
    have hk : 0 < (4 : ℝ) ^ k * R₀ := by positivity
    have heq : E k = {g | SupProxy κ (D g) hk w} := by
      ext g
      exact supProxyAt_iff κ (D g) hk w
    rw [heq]
    exact measurableSet_supProxy hD.measurable κ hk w
  refine ⟨(⋂ k ∈ Finset.Icc 1 K, (E k)ᶜ) ∪ N, ?_, ?_, ?_⟩
  · exact (Finset.measurableSet_biInter _ fun k _ => (hEm k).compl).union hNm
  · intro g hg
    by_cases hgN : g ∈ N
    · exact Or.inr hgN
    · left
      have hgreg : BiLipschitz.Barrier.Barrier (D g) ∧ (D g).IsLengthSpace ∧
          ∀ k ∈ Finset.Icc 1 K, ∀ hk : 0 < 4 ^ k * R₀,
            acrossDist (D g) (supInner hk w) < ⊤ := by
        by_contra hn
        exact hgN (hNsub hn)
      obtain ⟨hB, hL, hF⟩ := hgreg
      simp only [mem_iInter, mem_compl_iff]
      intro k hk hgk
      have hbad : ¬ Objects.CorrectedEvent.supGood C (D g) c₀ s l k := hg k hk
      apply hbad
      have hkpos : 0 < (4 : ℝ) ^ k * R₀ := by positivity
      have hRk : Objects.CorrectedEvent.supRadius C k = 4 ^ k * R₀ := by rw [supRadius_eq]
      apply supGood_of_proxy C (D g) c₀ s l k
      · have hgk' : SupProxyAt κ (D g) (4 ^ k * R₀) w := hgk
        rw [hRk, show (1 / 2 * Real.exp (-C.ξ * C.A_max)) = κ by rw [hξ, hAmax]]
        exact hgk'
      · rw [hRk]
        calc Objects.CorrectedEvent.acr (D g) w ((1 + 1 / 20) * (4 ^ k * R₀)) ((2 - 1 / 20) * (4 ^ k * R₀))
            ≤ Objects.CorrectedEvent.ambientAcross (D g) w ((1 + 1 / 20) * (4 ^ k * R₀))
                ((2 - 1 / 20) * (4 ^ k * R₀)) :=
              acr_le_ambientAcross_of_barrier (D g) hB hL w (by nlinarith)
          _ = acrossDist (D g) (supInner hkpos w) :=
              ambientAcross_eq_acrossDist (D g) w (by positivity) (by nlinarith)
          _ < ⊤ := hF k hk hkpos
  · calc μ ((⋂ k ∈ Finset.Icc 1 K, (E k)ᶜ) ∪ N)
        ≤ μ (⋂ k ∈ Finset.Icc 1 K, (E k)ᶜ) + μ N := measure_union_le _ _
      _ = μ (⋂ k ∈ Finset.Icc 1 K, (E k)ᶜ) := by rw [hNnull, add_zero]
      _ ≤ μ {g | ∀ k ∈ Finset.Icc 1 K, ¬ SupProxyAt κ (D g) (4 ^ k * R₀) w} := by
          apply measure_mono
          intro g hg
          simp only [mem_iInter, mem_compl_iff] at hg
          exact fun k hk => hg k hk
      _ ≤ ENNReal.ofReal (c * Real.exp (-a * (K : ℝ))) := H w R₀ hR₀ K hK


end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS7S9

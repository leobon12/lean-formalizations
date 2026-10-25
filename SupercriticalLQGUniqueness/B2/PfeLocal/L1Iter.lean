import SupercriticalLQGUniqueness.B2.PfeLocal.L1Compare

 


















set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l1Scale (k₀ k : ℕ) : ℝ := (1 / 16 : ℝ) ^ (k₀ + k)

theorem l1Scale_pos (k₀ k : ℕ) : 0 < l1Scale k₀ k := by unfold l1Scale; positivity

theorem l1_countOcc_mono {Ω : Type} {E F : ℕ → Set Ω} {K : ℕ} {ω : Ω}
    (h : ∀ k ∈ Finset.Icc 1 K, ω ∈ E k → ω ∈ F k) :
    LQGMetric.Blueprint.countOcc E K ω ≤ LQGMetric.Blueprint.countOcc F K ω := by
  classical
  unfold LQGMetric.Blueprint.countOcc
  apply Finset.card_le_card
  intro k hk
  rw [Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, h k hk.1 hk.2⟩

 
def l1HeatFam (ξ : ℝ) (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (q : Finset ℂ) (z : ℂ) (k₀ : ℕ) (C : ℝ)
    (ε : Set.Ioi (0 : ℝ)) (k : ℕ) : Set DistC :=
  {g | l1HeatGood ξ (m ε)
    (m ⟨(ε : ℝ) / l1Scale k₀ k, Set.mem_Ioi.mpr (div_pos ε.2 (l1Scale_pos k₀ k))⟩)
    (V ε g) q z (l1Scale k₀ k) C (circleAvg g (l1Scale k₀ k) z)}

 
theorem l1_canonical_count_bound (hS4 : Iface.DG20Section4) (hPerc : Iface.DG20PercEstimate')
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ)) (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    (V : Set.Ioi (0 : ℝ) → DistC → C(ℂ, ℝ)) (hVm : ∀ δ, Measurable (V δ))
    (hV : ∀ δ : Set.Ioi (0 : ℝ), ∀ᵐ g ∂normGFFLaw, ∀ z, V δ g z = heatMollify (δ : ℝ) g z)
    (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (a : ℝ) (ha : 0 < a) (b : ℝ) (hb : 0 < b) (hb1 : b < 1) :
    ∃ C c₀ : ℝ, 1 < C ∧ 0 < c₀ ∧ ∀ (z : ℂ) (k₀ J : ℕ) (e : ℕ → Set.Ioi (0 : ℝ)),
      Tendsto (fun n => (e n : ℝ)) atTop (𝓝 0) → ∀ τ : ℝ, 0 < τ →
        ∀ᶠ n in atTop, normGFFLaw {g | (LQGMetric.Blueprint.countOcc
          (l1HeatFam ξ m V q z k₀ C (e n)) J g : ℝ) < b * J} ≤
            ENNReal.ofReal (c₀ * Real.exp (-a * J)) + ENNReal.ofReal τ := by
  obtain ⟨hprob, hcan⟩ := PfeAxioms.normalized_canonical_model
  obtain ⟨p, c₀, hp0, hp1, hc0, hiter⟩ :=
    Uniqueness.Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open (1 / 16) (3 / 4)
      (by norm_num) (by norm_num) (by norm_num) a ha b hb hb1
  set η : ℝ := (1 - p) / (3 * (q.card + 4)) with hη
  have hη0 : 0 < η := by rw [hη]; apply div_pos (by linarith); positivity
  obtain ⟨C₁, ε₀, hC₁, hε₀, hgood⟩ := l1_heat_good_prob hS4 hPerc ξ Q hQ m hm V hVm hV q η hη0
  set E : ℝ := Real.exp (|(ξ : ℝ)| * 1) with hE
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_exp (by positivity)
  set C₂ : ℝ := C₁ * E with hC₂
  set C₃ : ℝ := C₂ * E with hC₃
  have hC₂0 : 0 < C₂ := by positivity
  have hC₃1 : 1 < C₃ := by
    have : C₁ ≤ C₂ := by rw [hC₂]; nlinarith
    have : C₂ ≤ C₃ := by rw [hC₃]; nlinarith
    linarith
  refine ⟨C₃, c₀, hC₃1, hc0, fun z k₀ J e he τ hτ => ?_⟩
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℂ
  set r : ℕ → ℝ := l1Scale k₀ with hr
  set ρ : ℕ → ℝ := fun k => 4 * r k with hρ
  have hr0 : ∀ k, 0 < r k := l1Scale_pos k₀
  
  set τ' : ℝ := min ((1 - p) / 3) (τ / (J + 1)) with hτ'
  have hτ'0 : 0 < τ' := lt_min (by linarith) (by positivity)
  have hev : ∀ᶠ n in atTop, ∀ k ∈ Finset.Icc 1 J,
      (e n : ℝ) / r k < ε₀ ∧ Real.sqrt (e n : ℝ) ≤ r k / 16 ∧
        normGFFLaw {g | ¬ l1CompGood V D (e n) z (r k) (ρ k) 1 g} ≤ ENNReal.ofReal τ' := by
    rw [Filter.eventually_all_finset]
    intro k _
    refine ((he.div_const (r k)).eventually (gt_mem_nhds (by rw [zero_div]; exact hε₀))).and
      (((Real.continuous_sqrt.tendsto 0).comp he).eventually
        (ge_mem_nhds (by rw [Real.sqrt_zero]; exact div_pos (hr0 k) (by norm_num) :
          Real.sqrt 0 < r k / 16)) |>.and ?_)
    exact (l1_tendsto_compBad V hVm hV hDc z (r k) (ρ k) 1 one_pos e he).eventually
      (ge_mem_nhds (ENNReal.ofReal_pos.2 hτ'0))
  filter_upwards [hev] with n hn
  set ε : Set.Ioi (0 : ℝ) := e n
  
  let ε' : ℕ → Set.Ioi (0 : ℝ) := fun k =>
    ⟨(ε : ℝ) / r k, Set.mem_Ioi.mpr (div_pos ε.2 (hr0 k))⟩
  classical
  let Ev : ℕ → Set DistC := fun k =>
    if k ∈ Finset.Icc 1 J then
      {g | l1LocGood ξ (m ε) (m (ε' k)) (ε : ℝ) ε.2 (l1Recenter z (ρ k) g) q z (r k) C₂}
    else univ
  have hcirc : ∀ k, ∀ᵐ g ∂normGFFLaw,
      circleAvg (l1Recenter z (ρ k) g) (r k) z = circleAvg g (r k) z - circleAvg g (ρ k) z :=
    fun k => l1_ae_circleAvg_recenter z (hr0 k) (ρ k)
  have hcircAll : ∀ᵐ g ∂normGFFLaw, ∀ k,
      circleAvg (l1Recenter z (ρ k) g) (r k) z = circleAvg g (r k) z - circleAvg g (ρ k) z :=
    ae_all_iff.2 hcirc
  
  have hEvMeas : ∀ k, LQGMetric.Blueprint.AEEventIn normGFFLaw
      (LQGMetric.Blueprint.fieldSigma
        (fun g => addConst (id g) (-circleAvg (id g) (ρ k) z))
        (LQGMetric.Blueprint.annulus z (1 / 16 * ρ k) (3 / 4 * ρ k))) (Ev k) := by
    intro k
    refine ⟨Ev k, ?_, Filter.EventuallyEq.rfl⟩
    by_cases hk : k ∈ Finset.Icc 1 J
    · have hset : Ev k = (fun g => addConst (id g) (-circleAvg (id g) (ρ k) z)) ⁻¹'
          {y | l1LocGood ξ (m ε) (m (ε' k)) (ε : ℝ) ε.2 y q z (r k) C₂} := by
        simp only [Ev, hk, ↓reduceIte]; rfl
      rw [hset, show 1 / 16 * ρ k = r k / 4 by simp only [hρ]; ring,
        show 3 / 4 * ρ k = 3 * r k by simp only [hρ]; ring]
      exact l1_measurableSet_fieldSigma_locGood ξ (m ε) (m (ε' k)) ε.2 q hq z (hr0 k) C₂
        (hn k hk).2.1 _
    · simp only [Ev, hk, ↓reduceIte]
      exact MeasurableSet.univ
  have hEvProb : ∀ k, ENNReal.ofReal p ≤ normGFFLaw (Ev k) := by
    intro k
    by_cases hk : k ∈ Finset.Icc 1 J
    · simp only [Ev, hk, ↓reduceIte]
      obtain ⟨hk1, -, hk3⟩ := hn k hk
      have hheat := hgood z (r k) (hr0 k) ε hk1
      
      have hsub : {g | l1LocGood ξ (m ε) (m (ε' k)) (ε : ℝ) ε.2 (l1Recenter z (ρ k) g) q z
          (r k) C₂}ᶜ ≤ᵐ[normGFFLaw]
          {g | ¬ l1HeatGood ξ (m ε) (m (ε' k)) (V ε g) q z (r k) C₁ (circleAvg g (r k) z)} ∪
            {g | ¬ l1CompGood V D ε z (r k) (ρ k) 1 g} := by
        filter_upwards [hcirc k] with g hg hloc
        by_contra hnot
        simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hnot
        exact hloc (l1_heat_to_loc ξ (m ε) (m (ε' k)) V hDd ε q hq z (hr0 k) (ρ k)
          (by linarith) 1 hg hnot.2 hnot.1)
      have hbad : normGFFLaw {g | l1LocGood ξ (m ε) (m (ε' k)) (ε : ℝ) ε.2
          (l1Recenter z (ρ k) g) q z (r k) C₂}ᶜ ≤ ENNReal.ofReal (1 - p) := by
        calc _ ≤ normGFFLaw ({g | ¬ l1HeatGood ξ (m ε) (m (ε' k)) (V ε g) q z (r k) C₁
              (circleAvg g (r k) z)} ∪ {g | ¬ l1CompGood V D ε z (r k) (ρ k) 1 g}) :=
            measure_mono_ae hsub
          _ ≤ ENNReal.ofReal ((q.card + 4) * η) + ENNReal.ofReal τ' :=
            (measure_union_le _ _).trans (add_le_add hheat hk3)
          _ ≤ ENNReal.ofReal (1 - p) := by
            rw [← ENNReal.ofReal_add (by positivity) hτ'0.le]
            apply ENNReal.ofReal_le_ofReal
            have h1 : (q.card + 4) * η = (1 - p) / 3 := by
              rw [hη]; field_simp
            have h2 : τ' ≤ (1 - p) / 3 := min_le_left _ _
            linarith
      have hmeas : MeasurableSet {g | l1LocGood ξ (m ε) (m (ε' k)) (ε : ℝ) ε.2
          (l1Recenter z (ρ k) g) q z (r k) C₂} :=
        (measurable_l1Recenter z (ρ k)) (l1_measurableSet_locGood ξ (m ε) (m (ε' k)) ε.2 q z
          (r k) C₂)
      rw [prob_compl_eq_one_sub hmeas] at hbad
      have : ENNReal.ofReal p = 1 - ENNReal.ofReal (1 - p) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]; congr 1; ring
      rw [this]
      refine tsub_le_iff_tsub_le.1 hbad |>.trans_eq' ?_
      rfl
    · simp only [Ev, hk, ↓reduceIte, measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le
  have hanti : Antitone ρ := by
    intro i j hij
    simp only [hρ, hr, l1Scale]
    have : (1 / 16 : ℝ) ^ (k₀ + j) ≤ (1 / 16 : ℝ) ^ (k₀ + i) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  have hratio : ∀ k, ρ (k + 1) / ρ k ≤ 1 / 16 := by
    intro k
    have hpos : 0 < ρ k := by simp only [hρ]; linarith [hr0 k]
    rw [div_le_iff₀ hpos]
    simp only [hρ, hr, l1Scale, show k₀ + (k + 1) = (k₀ + k) + 1 by omega, pow_succ]
    linarith
  have hit := hiter normGFFLaw id hcan.1 z ρ Ev (fun k => by simp only [hρ]; linarith [hr0 k])
    hanti hratio hEvMeas hEvProb J
  have hcmp : ∀ᵐ g ∂normGFFLaw,
      (∀ k ∈ Finset.Icc 1 J, l1CompGood V D ε z (r k) (ρ k) 1 g) →
        LQGMetric.Blueprint.countOcc Ev J g ≤
          LQGMetric.Blueprint.countOcc (l1HeatFam ξ m V q z k₀ C₃ ε) J g := by
    filter_upwards [hcircAll] with g hg hcomp
    apply l1_countOcc_mono
    intro k hk hgk
    simp only [Ev, hk, ↓reduceIte, mem_ofPred_eq] at hgk
    exact l1_loc_to_heat ξ (m ε) (m (ε' k)) V hDd ε q hq z (hr0 k) (ρ k) hC₂0 1 (hg k)
      (hcomp k hk) hgk
  have hsub : {g | (LQGMetric.Blueprint.countOcc (l1HeatFam ξ m V q z k₀ C₃ ε) J g : ℝ) <
      b * J} ≤ᵐ[normGFFLaw]
      ({g | (LQGMetric.Blueprint.countOcc Ev J g : ℝ) < b * J} ∪
        ⋃ k ∈ Finset.Icc 1 J, {g | ¬ l1CompGood V D ε z (r k) (ρ k) 1 g}) := by
    filter_upwards [hcmp] with g hg hlt
    by_cases hall : ∀ k ∈ Finset.Icc 1 J, l1CompGood V D ε z (r k) (ρ k) 1 g
    · left
      exact lt_of_le_of_lt (by exact_mod_cast hg hall) hlt
    · right
      push Not at hall
      obtain ⟨k, hk, hk'⟩ := hall
      exact mem_biUnion hk hk'
  have hsum : ∑ k ∈ Finset.Icc 1 J, ENNReal.ofReal τ' ≤ ENNReal.ofReal τ := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : τ' ≤ τ / (J + 1) := min_le_right _ _
    have h2 : (J : ℝ) * (τ / (J + 1)) ≤ τ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    calc (J : ℝ) * τ' ≤ (J : ℝ) * (τ / (J + 1)) := by gcongr
      _ ≤ τ := h2
  calc normGFFLaw {g | (LQGMetric.Blueprint.countOcc (l1HeatFam ξ m V q z k₀ C₃ ε) J g : ℝ) <
        b * J}
      ≤ normGFFLaw ({g | (LQGMetric.Blueprint.countOcc Ev J g : ℝ) < b * J} ∪
        ⋃ k ∈ Finset.Icc 1 J, {g | ¬ l1CompGood V D ε z (r k) (ρ k) 1 g}) :=
        measure_mono_ae hsub
    _ ≤ normGFFLaw {g | (LQGMetric.Blueprint.countOcc Ev J g : ℝ) < b * J} +
        ∑ k ∈ Finset.Icc 1 J, normGFFLaw {g | ¬ l1CompGood V D ε z (r k) (ρ k) 1 g} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal (c₀ * Real.exp (-a * J)) + ∑ k ∈ Finset.Icc 1 J, ENNReal.ofReal τ' :=
        add_le_add hit (Finset.sum_le_sum fun k hk => (hn k hk).2.2)
    _ ≤ ENNReal.ofReal (c₀ * Real.exp (-a * J)) + ENNReal.ofReal τ := add_le_add le_rfl hsum

end SupercriticalLQGUniqueness.B2.PfeLocal

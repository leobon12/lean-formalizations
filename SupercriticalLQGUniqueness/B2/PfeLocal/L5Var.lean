import SupercriticalLQGUniqueness.B2.PfeLocal.L5Grid

 
























set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum LQGMetric.LM

 
def l5Mesh (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem l5Mesh_pos (j : ℕ) : 0 < l5Mesh j := by unfold l5Mesh; positivity

 
def l5Shift (M i : ℕ) : ℝ × ℝ := ((i : ℝ) / M, (i : ℝ) / M)

theorem l5Shift_mem {M i : ℕ} (hi : i < M) :
    (l5Shift M i).1 ∈ Icc (0 : ℝ) 1 ∧ (l5Shift M i).2 ∈ Icc (0 : ℝ) 1 := by
  have hM : (0 : ℝ) < M := by exact_mod_cast Nat.zero_lt_of_lt hi
  have h1 : (i : ℝ) / M ≤ 1 := by
    rw [div_le_one hM]; exact_mod_cast hi.le
  have h0 : (0 : ℝ) ≤ (i : ℝ) / M := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact ⟨⟨h0, h1⟩, ⟨h0, h1⟩⟩

 
def l5SqEnc {Ω : Type} (L : Ω → LSCMetric) (R : ℝ) (j M i : ℕ) (ω : Ω) :
    t17Box (l5Mesh j) R → L5Code → ℝ≥0∞ :=
  fun k => l5Enc (t17Square (l5Mesh j) (l5Shift M i) k) (L ω)

theorem measurable_l5SqEnc {Ω : Type} [MeasurableSpace Ω] {L : Ω → LSCMetric}
    (hL : Measurable L) (R : ℝ) (j M i : ℕ) : Measurable (l5SqEnc L R j M i) :=
  measurable_pi_iff.2 fun k => (measurable_l5Enc _).comp hL

theorem l5SqEnc_diag {Ω : Type} [MeasurableSpace Ω] {L : Ω → LSCMetric}
    (hL : Measurable L) (R : ℝ) (j M i : ℕ) :
    MeasurableSet {p : (t17Box (l5Mesh j) R → L5Code → ℝ≥0∞) × Ω |
      l5SqEnc L R j M i p.2 = p.1} := by
  have : {p : (t17Box (l5Mesh j) R → L5Code → ℝ≥0∞) × Ω | l5SqEnc L R j M i p.2 = p.1} =
      ⋂ k, ⋂ c, {p | l5SqEnc L R j M i p.2 k c = p.1 k c} := by
    ext p
    simp only [mem_setOf_eq, mem_iInter, funext_iff]
  rw [this]
  refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun c => measurableSet_eq_fun ?_ ?_
  · exact (measurable_pi_apply c).comp ((measurable_pi_apply k).comp
      ((measurable_l5SqEnc hL R j M i).comp measurable_snd))
  · exact (measurable_pi_apply c).comp ((measurable_pi_apply k).comp measurable_fst)

 
theorem l5_sum_lintegral_le {α ι' : Type} [MeasurableSpace α] (μ : Measure α) (s : Finset ι')
    (g : ι' → α → ℝ≥0∞) : ∑ i ∈ s, ∫⁻ a, g i a ∂μ ≤ ∫⁻ a, ∑ i ∈ s, g i a ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    refine (add_le_add le_rfl ih).trans ?_
    refine (le_lintegral_add (g i) fun a => ∑ i ∈ s, g i a).trans_eq ?_
    congr 1
    funext a
    rw [Finset.sum_insert hi]

 
theorem l5_tendsto_lintegral_zero {α : Type} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] (g : ℕ → α → ℝ≥0∞) {C : ℝ≥0∞} (hC : C ≠ ∞) {G : Set α}
    (hG : ∀ᵐ a ∂μ, a ∈ G) (hbd : ∀ n, ∀ a ∈ G, g n a ≤ C)
    (hlim : ∀ a ∈ G, Tendsto (fun n => g n a) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ a, g n a ∂μ) atTop (𝓝 0) := by
  choose g' hg'm hg'le hg'eq using fun n => exists_measurable_le_lintegral_eq μ (g n)
  have hlim' : Tendsto (fun n => ∫⁻ a, g' n a ∂μ) atTop (𝓝 (∫⁻ _, 0 ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun _ => C) hg'm
      (fun n => hG.mono fun a ha => (hg'le n a).trans (hbd n a ha)) ?_ ?_
    · rw [lintegral_const]; exact ENNReal.mul_ne_top hC (measure_ne_top _ _)
    · filter_upwards [hG] with a ha
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim a ha)
        (fun n => zero_le) (fun n => hg'le n a)
  rw [lintegral_zero] at hlim'
  exact hlim'.congr fun n => (hg'eq n).symm

 

theorem l5_pair_bound {D D'' : LSCMetric} (K : ℝ≥0) (hK : 1 ≤ K)
    (hle : ∀ x y, D''.1 (x, y) ≤ K * D.1 (x, y)) (R : ℝ) {O O' : Set ℂ} (P : ℝ → ℂ)
    (hP : D.IsCurve P 0 1) (hPc : Continuous P)
    (hPtr : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ closedBall (0 : ℂ) R) (hP0 : P 0 ∈ O) (hP1 : P 1 ∈ O')
    (hlen : D.len P 0 1 = compactPathInf D (closedBall 0 R) O O') (hfin : D.len P 0 1 ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ} (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1)
    (T : Finset (ℤ × ℤ)) (hT : T ⊆ t17Box ε R)
    (henc : ∀ k ∈ t17Box ε R, k ∉ T →
      l5Enc (t17Square ε θ k) D'' = l5Enc (t17Square ε θ k) D) :
    compactPathInf D'' (closedBall 0 R) O O' ≤ compactPathInf D (closedBall 0 R) O O' +
      ((K : ℝ≥0∞) - 1) * (pathLengthIn D P 0 1 (t17Grid ε θ) +
        ∑ k ∈ T, pathLengthIn D P 0 1 (t17Square ε θ k)) := by
  have hc : T17Curve (D.pt ∘ P) 0 1 := ⟨zero_le_one, hP.2, hfin⟩
  have htr : ∀ t ∈ Icc (0 : ℝ) 1, ‖P t‖ ≤ R := fun t ht => mem_closedBall_zero_iff.1 (hPtr t ht)
  have hres := l5_len_resample K hK hle P hc hPc.continuousOn hε hθ1 hθ2 htr T hT henc
  have hc'' := l5_t17Curve_of_le K hle hc
  have hF'' : compactPathInf D'' (closedBall 0 R) O O' ≤ D''.len P 0 1 :=
    l5_compactPathInf_le D'' P 0 1 ⟨zero_le_one, hc''.2.1⟩ hPtr hP0 hP1
  rw [← hlen]
  exact hF''.trans hres

 

theorem l5_var_zero {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (L : Ω → LSCMetric) (hL : Measurable L)
    (K : ℝ≥0) (hK : 1 ≤ K) (G₀ : Set Ω) (hG₀ : ∀ᵐ ω ∂ν, ω ∈ G₀)
    (hcmp : ∀ ω₁ ∈ G₀, ∀ ω₂ ∈ G₀, ∀ x y, (L ω₂).1 (x, y) ≤ K * (L ω₁).1 (x, y))
    (R : ℝ) {O O' : Set ℂ} (hO : IsCompact O) (hO' : IsCompact O')
    (hind : ∀ j M i : ℕ, ν.map (l5SqEnc L R j M i) =
      Measure.pi fun k => ν.map fun ω => l5SqEnc L R j M i ω k) :
    ∃ c : ℝ≥0∞, ∀ᵐ ω ∂ν, compactPathInf (L ω) (closedBall 0 R) O O' = c := by
  set F : Ω → ℝ≥0∞ := fun ω => compactPathInf (L ω) (closedBall 0 R) O O' with hFdef
  have hFm : Measurable F :=
    (compactPathInf_measurable (isCompact_closedBall _ _) hO hO').comp hL
  by_cases hinf : ∀ ω ∈ G₀, F ω = ∞
  · exact ⟨∞, hG₀.mono hinf⟩
  push Not at hinf
  obtain ⟨ω₀, hω₀, hfin₀⟩ := hinf
  set B' : ℝ≥0∞ := K * F ω₀
  have hB'fin : B' ≠ ∞ := ENNReal.mul_ne_top ENNReal.coe_ne_top hfin₀
  have hFle : ∀ ω ∈ G₀, F ω ≤ B' := fun ω hω =>
    l5_compactPathInf_le_mul K hK (hcmp ω₀ hω₀ ω hω) _ _ _
  have hFfin : ∀ ω ∈ G₀, F ω ≠ ∞ := fun ω hω => ne_top_of_le_ne_top hB'fin (hFle ω hω)
  set B : ℝ := B'.toReal
  have hB0 : 0 ≤ B := ENNReal.toReal_nonneg
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set Kr : ℝ := (K : ℝ) - 1
  have hKr : 0 ≤ Kr := by simp only [Kr]; linarith
  
  have hmin : ∀ ω ∈ G₀, ∃ P : ℝ → ℂ, (L ω).IsCurve P 0 1 ∧ Continuous P ∧
      (∀ t ∈ Icc (0 : ℝ) 1, P t ∈ closedBall (0 : ℂ) R) ∧ P 0 ∈ O ∧ P 1 ∈ O' ∧
      (L ω).len P 0 1 = F ω := fun ω hω =>
    l5_exists_minimizer (L ω) (isCompact_closedBall _ _) hO.isClosed hO'.isClosed (hFfin ω hω)
  choose! P hPc hPcont hPtr hP0 hP1 hPlen using hmin
  have hPfin : ∀ a ∈ G₀, (L a).len (P a) 0 1 ≠ ∞ := fun a ha => by
    rw [hPlen a ha]; exact hFfin a ha
  have hcurve : ∀ a ∈ G₀, T17Curve ((L a).pt ∘ P a) 0 1 := fun a ha =>
    ⟨zero_le_one, (hPc a ha).2, hPfin a ha⟩
  
  set f : Ω → ℝ := fun ω => (min (F ω) B').toReal
  have hfm : Measurable f := (hFm.min measurable_const).ennreal_toReal
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => ENNReal.toReal_nonneg
  have hfB : ∀ ω, f ω ≤ B := fun ω => ENNReal.toReal_mono hB'fin (min_le_right _ _)
  have hfG : ∀ ω ∈ G₀, f ω = (F ω).toReal := fun ω hω => by
    simp only [f, min_eq_left (hFle ω hω)]
  
  set gr : ℕ → ℕ → ℕ → Ω → ℝ := fun j M i a =>
    (pathLengthIn (L a) (P a) 0 1 (t17Grid (l5Mesh j) (l5Shift M i))).toReal
  set sq : ℕ → ℕ → ℕ → (ℤ × ℤ) → Ω → ℝ := fun j M i k a =>
    (pathLengthIn (L a) (P a) 0 1 (t17Square (l5Mesh j) (l5Shift M i) k)).toReal
  set ND : ℕ → Ω → ℝ≥0∞ := fun j a => ⨆ y : ℂ,
    t17LenMeas ((L a).pt ∘ P a) 0 1 (Icc 0 1 ∩ P a ⁻¹' ball y (1 / ((j : ℝ) + 1)))
  set nd : ℕ → Ω → ℝ := fun j a => (ND j a).toReal
  have hpl : ∀ a ∈ G₀, ∀ S : Set ℂ, pathLengthIn (L a) (P a) 0 1 S ≤ F a := fun a ha S => by
    rw [← hPlen a ha]; exact pathLengthIn_le_len _ _ (hPc a ha) (hPfin a ha) S
  have hplf : ∀ a ∈ G₀, ∀ S : Set ℂ, pathLengthIn (L a) (P a) 0 1 S ≠ ∞ := fun a ha S =>
    ne_top_of_le_ne_top (hFfin a ha) (hpl a ha S)
  have hlenB : ∀ a ∈ G₀, (F a).toReal ≤ B := fun a ha => ENNReal.toReal_mono hB'fin (hFle a ha)
  have hNDle : ∀ j, ∀ a ∈ G₀, ND j a ≤ F a := fun j a ha => by
    refine iSup_le fun y => ?_
    rw [← hPlen a ha]
    show _ ≤ eVariationOn ((L a).pt ∘ P a) (Icc 0 1)
    rw [← t17LenMeas_Icc (hcurve a ha)]
    exact measure_mono inter_subset_left
  have hNDf : ∀ j, ∀ a ∈ G₀, ND j a ≠ ∞ := fun j a ha =>
    ne_top_of_le_ne_top (hFfin a ha) (hNDle j a ha)
  
  have hpair : ∀ j M i : ℕ, i < M → ∀ a ∈ G₀, ∀ b ∈ G₀, ∀ T : Finset (ℤ × ℤ),
      T ⊆ t17Box (l5Mesh j) R →
      (∀ k ∈ t17Box (l5Mesh j) R, k ∉ T → l5Enc (t17Square (l5Mesh j) (l5Shift M i) k) (L b) =
        l5Enc (t17Square (l5Mesh j) (l5Shift M i) k) (L a)) →
      f b - f a ≤ Kr * (gr j M i a + ∑ k ∈ T, sq j M i k a) := by
    intro j M i hi a ha b hb T hT henc
    have h := l5_pair_bound K hK (hcmp a ha b hb) R (P a) (hPc a ha) (hPcont a ha) (hPtr a ha)
      (hP0 a ha) (hP1 a ha) (hPlen a ha) (hPfin a ha) (l5Mesh_pos j) (l5Shift_mem hi).1
      (l5Shift_mem hi).2 T hT henc
    have hsumf : (∑ k ∈ T, pathLengthIn (L a) (P a) 0 1
        (t17Square (l5Mesh j) (l5Shift M i) k)) ≠ ∞ :=
      ENNReal.sum_ne_top.2 fun k _ => hplf a ha _
    have hX : ((K : ℝ≥0∞) - 1) * (pathLengthIn (L a) (P a) 0 1
        (t17Grid (l5Mesh j) (l5Shift M i)) + ∑ k ∈ T, pathLengthIn (L a) (P a) 0 1
          (t17Square (l5Mesh j) (l5Shift M i) k)) ≠ ∞ :=
      ENNReal.mul_ne_top (ENNReal.sub_ne_top ENNReal.coe_ne_top)
        (ENNReal.add_ne_top.2 ⟨hplf a ha _, hsumf⟩)
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hFfin a ha, hX⟩) h
    rw [ENNReal.toReal_add (hFfin a ha) hX, ENNReal.toReal_mul,
      ENNReal.toReal_add (hplf a ha _) hsumf, ENNReal.toReal_sum fun k _ => hplf a ha _,
      ENNReal.toReal_sub_of_le (by exact_mod_cast hK) ENNReal.coe_ne_top, ENNReal.coe_toReal,
      ENNReal.toReal_one] at h2
    rw [hfG b hb, hfG a ha]
    simp only [gr, sq, Kr]
    linarith
  
  set c₀ : ℕ → ℕ → ℕ → Ω → ℝ≥0∞ := fun j M i a => ENNReal.ofReal ((Kr * gr j M i a) ^ 2)
  set c₁ : ℕ → ℕ → ℕ → (ℤ × ℤ) → Ω → ℝ≥0∞ := fun j M i k a =>
    ENNReal.ofReal ((Kr * (gr j M i a + sq j M i k a)) ^ 2)
  have hgr0 : ∀ j M i a, 0 ≤ gr j M i a := fun _ _ _ _ => ENNReal.toReal_nonneg
  have hsq0 : ∀ j M i k a, 0 ≤ sq j M i k a := fun _ _ _ _ _ => ENNReal.toReal_nonneg
  have hnd0 : ∀ j a, 0 ≤ nd j a := fun _ _ => ENNReal.toReal_nonneg
  have hpos : ∀ x y : ℝ, x ≤ y → 0 ≤ y →
      ENNReal.ofReal (max x 0 ^ 2) ≤ ENNReal.ofReal (y ^ 2) := fun x y hxy hy =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_max_right _ _) (max_le hxy hy) 2)
  have hes : ∀ j M i : ℕ, i < M → ENNReal.ofReal (variance f ν) ≤
      ∫⁻ a, (c₀ j M i a + ∑ k : t17Box (l5Mesh j) R, c₁ j M i k a) ∂ν := by
    intro j M i hi
    refine l5_es_bound ν (measurable_l5SqEnc hL R j M i) (hind j M i) (l5SqEnc_diag hL R j M i)
      hfm hB0 hf0 hfB hG₀ (c₀ j M i) (fun k => c₁ j M i k) ?_ ?_
    · intro a ha b hb hY
      have := hpair j M i hi a ha b hb ∅ (Finset.empty_subset _) fun k hk _ =>
        congrFun hY ⟨k, hk⟩
      rw [Finset.sum_empty, add_zero] at this
      exact hpos _ _ this (mul_nonneg hKr (hgr0 _ _ _ _))
    · intro a ha k b hb hY
      have := hpair j M i hi a ha b hb {k.1} (Finset.singleton_subset_iff.2 k.2)
        fun k' hk' hk'T => hY ⟨k', hk'⟩ fun h => hk'T (Finset.mem_singleton.2
          (congrArg Subtype.val h))
      rw [Finset.sum_singleton] at this
      exact hpos _ _ this (mul_nonneg hKr (add_nonneg (hgr0 _ _ _ _) (hsq0 _ _ _ _ _)))
  
  set N : ℕ → ℕ := fun j => (t17Box (l5Mesh j) R).card
  have hround : ∀ j M : ℕ, ∀ a ∈ G₀, ∑ i ∈ Finset.range M,
      (c₀ j M i a + ∑ k : t17Box (l5Mesh j) R, c₁ j M i k a) ≤
      ENNReal.ofReal (Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * (2 * B ^ 2) +
        2 * (M : ℝ) * (B * nd j a))) := by
    intro j M a ha
    set ℓ := (F a).toReal
    have hℓ0 : 0 ≤ ℓ := ENNReal.toReal_nonneg
    have hℓB : ℓ ≤ B := hlenB a ha
    have hgrle : ∀ i, gr j M i a ≤ ℓ := fun i =>
      ENNReal.toReal_mono (hFfin a ha) (hpl a ha _)
    have htr : ∀ t ∈ Icc (0 : ℝ) 1, ‖P a t‖ ≤ R := fun t ht =>
      mem_closedBall_zero_iff.1 (hPtr a ha t ht)
    have hsqsum : ∀ i, i < M → ∑ k ∈ t17Box (l5Mesh j) R, sq j M i k a ≤ ℓ := by
      intro i hi
      have hd := l5_len_decomp (L a) (P a) (hcurve a ha) (hPcont a ha).continuousOn
        (l5Mesh_pos j) (l5Shift_mem hi).1 (l5Shift_mem hi).2 htr
      rw [hPlen a ha] at hd
      have hle : ∑ k ∈ t17Box (l5Mesh j) R, pathLengthIn (L a) (P a) 0 1
          (t17Square (l5Mesh j) (l5Shift M i) k) ≤ F a := by
        rw [hd]; exact le_add_self
      have := ENNReal.toReal_mono (hFfin a ha) hle
      rwa [ENNReal.toReal_sum fun k _ => hplf a ha _] at this
    have hsqnd : ∀ i k, sq j M i k a ≤ nd j a := fun i k =>
      ENNReal.toReal_mono (hNDf j a ha) (l5_square_le_ball (L a) (P a) 0 1 j (l5Shift M i) k)
    have hgrsum : ∑ i ∈ Finset.range M, gr j M i a ≤ 2 * ℓ := by
      have h := l5_grid_sum (L a) (P a) (hcurve a ha) (hPcont a ha).continuousOn (l5Mesh_pos j) M
      rw [hPlen a ha] at h
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofNat_ne_top (hFfin a ha)) h
      rwa [ENNReal.toReal_sum fun i _ => hplf a ha _, ENNReal.toReal_mul,
        ENNReal.toReal_ofNat] at h2
    have hsub : ∀ k ∈ t17Box (l5Mesh j) R, True := fun _ _ => trivial
    have e1 : ∀ i, c₀ j M i a + ∑ k : t17Box (l5Mesh j) R, c₁ j M i k a =
        ENNReal.ofReal ((Kr * gr j M i a) ^ 2 +
          ∑ k ∈ t17Box (l5Mesh j) R, (Kr * (gr j M i a + sq j M i k a)) ^ 2) := by
      intro i
      rw [ENNReal.ofReal_add (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun _ _ => sq_nonneg _]
      congr 1
      exact Finset.sum_coe_sort (t17Box (l5Mesh j) R) fun k => c₁ j M i k a
    rw [Finset.sum_congr rfl fun i _ => e1 i,
      ← ENNReal.ofReal_sum_of_nonneg fun i _ => add_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hk : ∀ i, i < M → ∑ k ∈ t17Box (l5Mesh j) R, (Kr * (gr j M i a + sq j M i k a)) ^ 2 ≤
        Kr ^ 2 * (2 * (N j : ℝ) * gr j M i a ^ 2 + 2 * (nd j a * ℓ)) := by
      intro i hi
      calc ∑ k ∈ t17Box (l5Mesh j) R, (Kr * (gr j M i a + sq j M i k a)) ^ 2
          ≤ ∑ k ∈ t17Box (l5Mesh j) R, Kr ^ 2 * (2 * gr j M i a ^ 2 + 2 * sq j M i k a ^ 2) :=
            Finset.sum_le_sum fun k _ => by
              nlinarith [mul_nonneg (sq_nonneg Kr) (sq_nonneg (gr j M i a - sq j M i k a))]
        _ = Kr ^ 2 * (2 * (N j : ℝ) * gr j M i a ^ 2 +
              2 * ∑ k ∈ t17Box (l5Mesh j) R, sq j M i k a ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_const, nsmul_eq_mul]
            simp only [N]
            ring
        _ ≤ Kr ^ 2 * (2 * (N j : ℝ) * gr j M i a ^ 2 + 2 * (nd j a * ℓ)) := by
            gcongr
            exact (l5_sum_sq_le _ _ (fun k _ => hsq0 _ _ _ _ _) fun k _ => hsqnd i k).trans
              (mul_le_mul_of_nonneg_left (hsqsum i hi) (hnd0 j a))
    have hgsq : ∑ i ∈ Finset.range M, gr j M i a ^ 2 ≤ 2 * ℓ ^ 2 := by
      calc ∑ i ∈ Finset.range M, gr j M i a ^ 2 ≤ ℓ * ∑ i ∈ Finset.range M, gr j M i a :=
            l5_sum_sq_le _ _ (fun i _ => hgr0 _ _ _ _) fun i _ => hgrle i
        _ ≤ ℓ * (2 * ℓ) := mul_le_mul_of_nonneg_left hgrsum hℓ0
        _ = 2 * ℓ ^ 2 := by ring
    calc ∑ i ∈ Finset.range M, ((Kr * gr j M i a) ^ 2 +
          ∑ k ∈ t17Box (l5Mesh j) R, (Kr * (gr j M i a + sq j M i k a)) ^ 2)
        ≤ ∑ i ∈ Finset.range M, Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * gr j M i a ^ 2 +
            2 * (nd j a * ℓ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := hk i (Finset.mem_range.1 hi)
          calc (Kr * gr j M i a) ^ 2 +
                ∑ k ∈ t17Box (l5Mesh j) R, (Kr * (gr j M i a + sq j M i k a)) ^ 2
              ≤ (Kr * gr j M i a) ^ 2 +
                  Kr ^ 2 * (2 * (N j : ℝ) * gr j M i a ^ 2 + 2 * (nd j a * ℓ)) :=
                add_le_add le_rfl this
            _ = _ := by ring
      _ = Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * ∑ i ∈ Finset.range M, gr j M i a ^ 2 +
            (M : ℝ) * (2 * (nd j a * ℓ))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
            Finset.card_range, nsmul_eq_mul]
      _ ≤ Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * (2 * B ^ 2) + 2 * (M : ℝ) * (B * nd j a)) := by
          have hN0 : (0 : ℝ) ≤ 1 + 2 * (N j : ℝ) := by positivity
          have h1 : (1 + 2 * (N j : ℝ)) * ∑ i ∈ Finset.range M, gr j M i a ^ 2 ≤
              (1 + 2 * (N j : ℝ)) * (2 * B ^ 2) := by
            refine mul_le_mul_of_nonneg_left (hgsq.trans ?_) hN0
            have := pow_le_pow_left₀ hℓ0 hℓB 2
            linarith
          have h2 : (M : ℝ) * (2 * (nd j a * ℓ)) ≤ 2 * (M : ℝ) * (B * nd j a) := by
            have := mul_le_mul_of_nonneg_left hℓB (hnd0 j a)
            have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
            nlinarith
          have := add_le_add h1 h2
          exact mul_le_mul_of_nonneg_left this (sq_nonneg _)
  
  set I : ℕ → ℝ≥0∞ := fun j => ∫⁻ a, ENNReal.ofReal (nd j a) ∂ν
  have hVj : ∀ j : ℕ, ENNReal.ofReal (variance f ν) ≤
      ENNReal.ofReal (2 * Kr ^ 2 * B ^ 2 / ((j : ℝ) + 1)) +
        ENNReal.ofReal (2 * Kr ^ 2 * B) * I j := by
    intro j
    set M : ℕ := (1 + 2 * N j) * (j + 1)
    have hM0 : (M : ℝ≥0∞) ≠ 0 := by
      have : 0 < M := Nat.mul_pos (by omega) (Nat.succ_pos j)
      exact_mod_cast this.ne'
    have hMt : (M : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top M
    have h1 : (M : ℝ≥0∞) * ENNReal.ofReal (variance f ν) ≤
        ∫⁻ a, ENNReal.ofReal (Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * (2 * B ^ 2) +
          2 * (M : ℝ) * (B * nd j a))) ∂ν := by
      calc (M : ℝ≥0∞) * ENNReal.ofReal (variance f ν) =
            ∑ i ∈ Finset.range M, ENNReal.ofReal (variance f ν) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.range M,
              ∫⁻ a, (c₀ j M i a + ∑ k : t17Box (l5Mesh j) R, c₁ j M i k a) ∂ν :=
            Finset.sum_le_sum fun i hi => hes j M i (Finset.mem_range.1 hi)
        _ ≤ ∫⁻ a, ∑ i ∈ Finset.range M,
              (c₀ j M i a + ∑ k : t17Box (l5Mesh j) R, c₁ j M i k a) ∂ν :=
            l5_sum_lintegral_le ν _ _
        _ ≤ _ := lintegral_mono_ae (hG₀.mono fun a ha => hround j M a ha)
    have hpt : ∀ a, ENNReal.ofReal (Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * (2 * B ^ 2) +
        2 * (M : ℝ) * (B * nd j a))) = (M : ℝ≥0∞) * ENNReal.ofReal (2 * Kr ^ 2 * B ^ 2 /
          ((j : ℝ) + 1)) + ((M : ℝ≥0∞) * ENNReal.ofReal (2 * Kr ^ 2 * B)) *
            ENNReal.ofReal (nd j a) := by
      intro a
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (by positivity)),
        ← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) (by positivity))
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by positivity)) (hnd0 j a))]
      congr 1
      simp only [M]
      push_cast
      field_simp
    have h2 : ∫⁻ a, ENNReal.ofReal (Kr ^ 2 * ((1 + 2 * (N j : ℝ)) * (2 * B ^ 2) +
        2 * (M : ℝ) * (B * nd j a))) ∂ν = (M : ℝ≥0∞) *
          (ENNReal.ofReal (2 * Kr ^ 2 * B ^ 2 / ((j : ℝ) + 1)) +
            ENNReal.ofReal (2 * Kr ^ 2 * B) * I j) := by
      simp_rw [hpt]
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top hMt ENNReal.ofReal_ne_top)]
      ring
    exact (ENNReal.mul_le_mul_iff_right hM0 hMt).1 (h1.trans h2.le)
  
  have hIlim : Tendsto I atTop (𝓝 0) := by
    refine l5_tendsto_lintegral_zero ν (fun j a => ENNReal.ofReal (nd j a)) ENNReal.ofReal_ne_top
      hG₀ (fun j a ha => ENNReal.ofReal_le_ofReal ((ENNReal.toReal_mono (hFfin a ha)
        (hNDle j a ha)).trans (hlenB a ha))) fun a ha => ?_
    have h1 := l5_nondawdle (L a) (P a) (hPc a ha) (hPcont a ha).continuousOn (hPtr a ha)
      (hP0 a ha) (hP1 a ha) (hPlen a ha).le (hPfin a ha)
    have h2 : Tendsto (fun j => nd j a) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
      rw [ENNReal.toReal_zero] at this
      exact this
    have h3 := ENNReal.tendsto_ofReal h2
    simpa using h3
  have hu : Tendsto (fun j : ℕ => ENNReal.ofReal (2 * Kr ^ 2 * B ^ 2 / ((j : ℝ) + 1)) +
      ENNReal.ofReal (2 * Kr ^ 2 * B) * I j) atTop (𝓝 0) := by
    have t1 : Tendsto (fun j : ℕ => ENNReal.ofReal (2 * Kr ^ 2 * B ^ 2 / ((j : ℝ) + 1)))
        atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * Kr ^ 2 * B ^ 2)
      rw [mul_zero] at this
      have h := ENNReal.tendsto_ofReal this
      rw [ENNReal.ofReal_zero] at h
      refine h.congr fun j => ?_
      congr 1
      ring
    have t2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * Kr ^ 2 * B)) hIlim
      (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at t2
    simpa using t1.add t2
  have hV0 : ENNReal.ofReal (variance f ν) = 0 :=
    le_antisymm (ge_of_tendsto' hu hVj) bot_le
  have hvar : variance f ν = 0 :=
    le_antisymm (ENNReal.ofReal_eq_zero.1 hV0) (variance_nonneg _ _)
  rw [variance_eq_integral hfm.aemeasurable] at hvar
  set m := ∫ x, f x ∂ν
  have hint : Integrable (fun ω => (f ω - m) ^ 2) ν :=
    l5_integrable_of_bound ν ((hfm.sub measurable_const).pow_const 2) (C := (2 * B) ^ 2)
      fun ω => by
        have hm0 : 0 ≤ m := integral_nonneg hf0
        have hmB : m ≤ B := by
          calc m ≤ ∫ _, B ∂ν := integral_mono_of_nonneg (Eventually.of_forall hf0)
                (integrable_const B) (Eventually.of_forall hfB)
            _ = B := by simp
        rw [abs_of_nonneg (sq_nonneg _)]
        have : |f ω - m| ≤ 2 * B := by
          rw [abs_le]; constructor <;> linarith [hf0 ω, hfB ω]
        calc (f ω - m) ^ 2 = |f ω - m| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint).1 hvar
  refine ⟨ENNReal.ofReal m, ?_⟩
  filter_upwards [hae, hG₀] with ω hω hωG
  have hfω : f ω = m := by
    have h0 : (f ω - m) ^ 2 = 0 := hω
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
    linarith
  show F ω = ENNReal.ofReal m
  rw [← hfω, hfG ω hωG, ENNReal.ofReal_toReal (hFfin ω hωG)]

end SupercriticalLQGUniqueness.B2.PfeLocal

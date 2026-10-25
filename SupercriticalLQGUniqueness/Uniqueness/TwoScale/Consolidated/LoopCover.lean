import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated.RationalAround
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity




 









set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated

 
def aroundAt (D : LSCMetric) (x : ℂ) (ρ σ : ℝ) : ℝ≥0∞ := aroundRat (D, (x, ρ, σ))

 
def loopF (D : LSCMetric) (x : ℂ) (r δ : ℝ) : ℝ≥0∞ := aroundAt D x (δ * r) (Real.sqrt δ * r)

 
def loopG (D : LSCMetric) (x : ℂ) (r : ℝ) (j : ℚ × ℚ) : ℝ≥0∞ :=
  aroundAt D x (((j.2 : ℚ) : ℝ) * r) (Real.sqrt ((j.1 : ℚ) : ℝ) * r)

 
def ValidPair (j : ℚ × ℚ) : Prop :=
  0 < ((j.1 : ℚ) : ℝ) ∧ ((j.1 : ℚ) : ℝ) < ((j.2 : ℚ) : ℝ) ∧
    ((j.2 : ℚ) : ℝ) < Real.sqrt ((j.1 : ℚ) : ℝ) ∧ ((j.2 : ℚ) : ℝ) < 1

theorem aroundAt_eq (D : LSCMetric) (x : ℂ) (ρ σ : ℝ) (h : 0 < ρ ∧ ρ < σ) :
    aroundAt D x ρ σ = aroundDist D ⟨(x, (ρ, σ)), h⟩ :=
  (aroundDist_eq_aroundRat D ⟨(x, (ρ, σ)), h⟩).symm

theorem lt_sqrt_self {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : δ < Real.sqrt δ := by
  rw [Real.lt_sqrt h0.le]
  nlinarith

theorem loop_annulus_valid {δ r : ℝ} (hr : 0 < r) (h0 : 0 < δ) (h1 : δ < 1) :
    0 < δ * r ∧ δ * r < Real.sqrt δ * r :=
  ⟨mul_pos h0 hr, mul_lt_mul_of_pos_right (lt_sqrt_self h0 h1) hr⟩

 
theorem loopF_le_loopG (D : LSCMetric) (x : ℂ) {r : ℝ} (hr : 0 < r) {j : ℚ × ℚ}
    (hj : ValidPair j) {δ : ℝ} (hδ₁ : ((j.1 : ℚ) : ℝ) ≤ δ) (hδ₂ : δ ≤ ((j.2 : ℚ) : ℝ)) :
    loopF D x r δ ≤ loopG D x r j := by
  have hδpos : 0 < δ := lt_of_lt_of_le hj.1 hδ₁
  have hδ1 : δ < 1 := lt_of_le_of_lt hδ₂ hj.2.2.2
  have hA := loop_annulus_valid hr hδpos hδ1
  have hB : 0 < ((j.2 : ℚ) : ℝ) * r ∧
      ((j.2 : ℚ) : ℝ) * r < Real.sqrt ((j.1 : ℚ) : ℝ) * r :=
    ⟨mul_pos (lt_trans hj.1 hj.2.1) hr, mul_lt_mul_of_pos_right hj.2.2.1 hr⟩
  unfold loopF loopG
  rw [aroundAt_eq D x _ _ hA, aroundAt_eq D x _ _ hB]
  apply aroundDist_le_of_nested
  · change δ * r + dist x x ≤ ((j.2 : ℚ) : ℝ) * r
    rw [dist_self, add_zero]
    exact mul_le_mul_of_nonneg_right hδ₂ hr.le
  · change Real.sqrt ((j.1 : ℚ) : ℝ) * r ≤ Real.sqrt δ * r - dist x x
    rw [dist_self, sub_zero]
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hδ₁) hr.le

 

theorem loopG_lt_of_close (D : LSCMetric) (x : ℂ) {r : ℝ} (hr : 0 < r) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16) {c : ℝ≥0∞} (hc : loopF D x r δ < c) :
    ∃ η > 0, ∀ j : ℚ × ℚ, δ - η < ((j.1 : ℚ) : ℝ) → ((j.1 : ℚ) : ℝ) < δ →
      δ < ((j.2 : ℚ) : ℝ) → ((j.2 : ℚ) : ℝ) < δ + η → ValidPair j ∧ loopG D x r j < c := by
  have hδ1 : δ < 1 := by linarith
  have hA := loop_annulus_valid hr hδ0 hδ1
  have hc' := hc
  unfold loopF at hc'
  rw [aroundAt_eq D x _ _ hA] at hc'
  have hc'' := hc'
  simp only [aroundDist, iInf_lt_iff] at hc''
  obtain ⟨P, a, b, hP, hPA, hsep, hlen⟩ := hc''
  obtain ⟨η₀, hη₀, hadm⟩ := admissible_of_close D ⟨(x, (δ * r, Real.sqrt δ * r)), hA⟩ hP hPA hsep
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ0
  set η := min (η₀ / r) (min (η₀ * Real.sqrt δ / r) (δ / 2)) with hηdef
  have hη₁ : η ≤ η₀ / r := min_le_left _ _
  have hη₂ : η ≤ η₀ * Real.sqrt δ / r := (min_le_right _ _).trans (min_le_left _ _)
  have hη₃ : η ≤ δ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hηpos : 0 < η := lt_min (div_pos hη₀ hr) (lt_min (div_pos (mul_pos hη₀ hsδ) hr)
    (by linarith))
  refine ⟨η, hηpos, ?_⟩
  intro j hj₁ hj₁' hj₂ hj₂'
  set δ₁ : ℝ := ((j.1 : ℚ) : ℝ) with hδ₁def
  set δ₂ : ℝ := ((j.2 : ℚ) : ℝ) with hδ₂def
  have hδ₁pos : 0 < δ₁ := by linarith
  have hs₁ : 0 ≤ Real.sqrt δ₁ := Real.sqrt_nonneg _
  have hsq₁ : Real.sqrt δ₁ ^ 2 = δ₁ := Real.sq_sqrt hδ₁pos.le
  have hsq : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ0.le
  have hsle : Real.sqrt δ₁ ≤ Real.sqrt δ := Real.sqrt_le_sqrt hj₁'.le
  
  have hhalf : Real.sqrt (δ / 2) ≤ Real.sqrt δ₁ := Real.sqrt_le_sqrt (by linarith)
  have hsmall : δ₂ < Real.sqrt (δ / 2) := by
    rw [Real.lt_sqrt (by linarith)]
    nlinarith
  have hvalid : ValidPair j := ⟨hδ₁pos, by linarith, lt_of_lt_of_le hsmall hhalf, by linarith⟩
  refine ⟨hvalid, ?_⟩
  have hB : 0 < δ₂ * r ∧ δ₂ * r < Real.sqrt δ₁ * r :=
    ⟨mul_pos (by linarith) hr, mul_lt_mul_of_pos_right hvalid.2.2.1 hr⟩
  unfold loopG
  rw [aroundAt_eq D x _ _ hB]
  
  have hroot : Real.sqrt δ - Real.sqrt δ₁ < η₀ / r := by
    have hkey : (Real.sqrt δ - Real.sqrt δ₁) * Real.sqrt δ ≤ δ - δ₁ := by nlinarith
    have hwidth : δ - δ₁ < η₀ * Real.sqrt δ / r := by linarith
    have : (Real.sqrt δ - Real.sqrt δ₁) * Real.sqrt δ < (η₀ / r) * Real.sqrt δ := by
      calc (Real.sqrt δ - Real.sqrt δ₁) * Real.sqrt δ ≤ δ - δ₁ := hkey
        _ < η₀ * Real.sqrt δ / r := hwidth
        _ = (η₀ / r) * Real.sqrt δ := by ring
    exact lt_of_mul_lt_mul_right this hsδ.le
  have hadm' := hadm ⟨(x, (δ₂ * r, Real.sqrt δ₁ * r)), hB⟩
    (by change dist x x < η₀; rw [dist_self]; exact hη₀)
    (by change δ * r + dist x x < δ₂ * r; rw [dist_self, add_zero]
        exact mul_lt_mul_of_pos_right hj₂ hr)
    (by change δ₂ * r < δ * r + η₀
        have : δ₂ < δ + η₀ / r := by linarith
        have h2 := mul_lt_mul_of_pos_right this hr
        rw [add_mul, div_mul_cancel₀ η₀ hr.ne'] at h2
        exact h2)
    (by change Real.sqrt δ * r - η₀ < Real.sqrt δ₁ * r
        have h2 := mul_lt_mul_of_pos_right hroot hr
        rw [sub_mul, div_mul_cancel₀ η₀ hr.ne'] at h2
        linarith)
    (by change Real.sqrt δ₁ * r < Real.sqrt δ * r - dist x x
        rw [dist_self, sub_zero]
        exact mul_lt_mul_of_pos_right (Real.sqrt_lt_sqrt hδ₁pos.le hj₁') hr)
  have hle : aroundDist D ⟨(x, (δ₂ * r, Real.sqrt δ₁ * r)), hB⟩ ≤ D.len P a b := by
    unfold aroundDist
    exact iInf_le_of_le P <| iInf_le_of_le a <| iInf_le_of_le b <| iInf_le_of_le hP <|
      iInf_le_of_le hadm'.1 <| iInf_le_of_le hadm'.2 le_rfl
  exact lt_of_le_of_lt hle hlen


 
theorem bound_left_cont {θ δ : ℝ} (hδ : 0 < δ) {T : ℝ≥0∞} (hT : T ≠ ⊤)
    {e : ℝ≥0∞} (he : e ≠ 0) :
    ∃ η > 0, ∀ δ₁ : ℝ, δ - η < δ₁ → δ₁ < δ → 0 < δ₁ →
      ENNReal.ofReal (δ ^ θ) * T ≤ ENNReal.ofReal (δ₁ ^ θ) * T + e := by
  by_cases heT : e = ⊤
  · exact ⟨1, one_pos, fun δ₁ _ _ _ => by rw [heT, add_top]; exact le_top⟩
  set t := T.toReal with ht
  have hTt : T = ENNReal.ofReal t := (ENNReal.ofReal_toReal hT).symm
  set e' := e.toReal with he'
  have he'pos : 0 < e' := ENNReal.toReal_pos he heT
  have hcont : ContinuousAt (fun y : ℝ => y ^ θ) δ :=
    Real.continuousAt_rpow_const δ θ (Or.inl hδ.ne')
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcont (e' / (t + 1))
    (div_pos he'pos (by positivity))
  refine ⟨η, hηpos, fun δ₁ h₁ h₂ h₃ => ?_⟩
  have hd : dist δ₁ δ < η := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hclose := hη hd
  rw [Real.dist_eq, abs_lt] at hclose
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have hreal : δ ^ θ * t ≤ δ₁ ^ θ * t + e' := by
    have h1 : δ ^ θ - δ₁ ^ θ < e' / (t + 1) := by linarith [hclose.1]
    have h2 : (δ ^ θ - δ₁ ^ θ) * t ≤ e' / (t + 1) * t :=
      mul_le_mul_of_nonneg_right h1.le ht0
    have h3 : e' / (t + 1) * t ≤ e' := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hδθ : 0 ≤ δ ^ θ := Real.rpow_nonneg hδ.le θ
  have hδ₁θ : 0 ≤ δ₁ ^ θ := Real.rpow_nonneg h₃.le θ
  rw [hTt, ← ENNReal.ofReal_mul hδθ, ← ENNReal.ofReal_mul hδ₁θ,
    ← ENNReal.ofReal_toReal heT, ← ENNReal.ofReal_add (mul_nonneg hδ₁θ ht0) he'pos.le]
  exact ENNReal.ofReal_le_ofReal hreal

 

theorem loop_forall_iff_cover (D : LSCMetric) (x : ℂ) {r θ δ₀ : ℝ} (hr : 0 < r)
    (hθ : 0 < θ) (hδ₀ : 0 < δ₀) (hδ₀' : δ₀ ≤ 1 / 16) {T : ℝ≥0∞} (hT : T ≠ ⊤) :
    (∀ δ ∈ Ioc 0 δ₀, loopF D x r δ ≤ ENNReal.ofReal (δ ^ θ) * T) ↔
      ∀ m n : ℕ, ∃ Φ : Finset (ℚ × ℚ), (∀ j ∈ Φ, ValidPair j) ∧
        Icc (δ₀ / (m + 1)) δ₀ ⊆ (⋃ j ∈ Φ, Ioo ((j.1 : ℚ) : ℝ) ((j.2 : ℚ) : ℝ)) ∧
        ∀ j ∈ Φ, loopG D x r j <
          ENNReal.ofReal (((j.1 : ℚ) : ℝ) ^ θ) * T + ((n : ℝ≥0∞) + 1)⁻¹ := by
  constructor
  · intro hall m n
    set ε : ℝ≥0∞ := ((n : ℝ≥0∞) + 1)⁻¹ with hεdef
    have hε0 : ε ≠ 0 := ENNReal.inv_ne_zero.mpr (by simp)
    have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε0).ne'
    let S : Set (ℚ × ℚ) := {j | ValidPair j ∧
      loopG D x r j < ENNReal.ofReal (((j.1 : ℚ) : ℝ) ^ θ) * T + ε}
    have hcov : Icc (δ₀ / (m + 1)) δ₀ ⊆ ⋃ j : S, Ioo ((j.1.1 : ℚ) : ℝ) ((j.1.2 : ℚ) : ℝ) := by
      intro δ hδ
      have hδpos : 0 < δ := lt_of_lt_of_le (by positivity) hδ.1
      have hδle : δ ≤ 1 / 16 := hδ.2.trans hδ₀'
      have hF := hall δ ⟨hδpos, hδ.2⟩
      have hgfin : ENNReal.ofReal (δ ^ θ) * T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT
      have hlt : loopF D x r δ < ENNReal.ofReal (δ ^ θ) * T + ε / 2 :=
        lt_of_le_of_lt hF (ENNReal.lt_add_right hgfin hε2)
      obtain ⟨η, hηpos, hη⟩ := loopG_lt_of_close D x hr hδpos hδle hlt
      obtain ⟨η', hη'pos, hη'⟩ := bound_left_cont (θ := θ) hδpos hT hε2
      obtain ⟨q₁, hq₁a, hq₁b⟩ :=
        exists_rat_btwn (show max (max (δ - η) (δ - η')) (δ / 2) < δ by
          apply max_lt (max_lt (by linarith) (by linarith)) (by linarith))
      obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show δ < δ + η by linarith)
      have h1 : δ - η < (q₁ : ℝ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hq₁a
      have h1' : δ - η' < (q₁ : ℝ) :=
        lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hq₁a
      have h1'' : δ / 2 < (q₁ : ℝ) := lt_of_le_of_lt (le_max_right _ _) hq₁a
      obtain ⟨hvalid, hG⟩ := hη (q₁, q₂) h1 hq₁b hq₂a hq₂b
      have hgδ := hη' (q₁ : ℝ) h1' hq₁b (by linarith)
      have hG' : loopG D x r (q₁, q₂) <
          ENNReal.ofReal (((q₁ : ℚ) : ℝ) ^ θ) * T + ε := by
        calc loopG D x r (q₁, q₂) < ENNReal.ofReal (δ ^ θ) * T + ε / 2 := hG
          _ ≤ (ENNReal.ofReal (((q₁ : ℚ) : ℝ) ^ θ) * T + ε / 2) + ε / 2 := by gcongr
          _ = ENNReal.ofReal (((q₁ : ℚ) : ℝ) ^ θ) * T + ε := by
            rw [add_assoc, ENNReal.add_halves]
      exact mem_iUnion.mpr ⟨⟨(q₁, q₂), hvalid, hG'⟩, hq₁b, hq₂a⟩
    obtain ⟨t, ht⟩ := isCompact_Icc.elim_finite_subcover
      (fun j : S => Ioo ((j.1.1 : ℚ) : ℝ) ((j.1.2 : ℚ) : ℝ)) (fun _ => isOpen_Ioo) hcov
    refine ⟨t.image Subtype.val, ?_, ?_, ?_⟩
    · intro j hj
      obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp hj
      exact j'.2.1
    · intro δ hδ
      obtain ⟨j', hj', hδj⟩ := mem_iUnion₂.mp (ht hδ)
      exact mem_iUnion₂.mpr ⟨j'.1, Finset.mem_image_of_mem _ hj', hδj⟩
    · intro j hj
      obtain ⟨j', _, rfl⟩ := Finset.mem_image.mp hj
      exact j'.2.2
  · intro hcov δ hδ
    obtain ⟨m, hm⟩ := exists_nat_ge (δ₀ / δ)
    have hδm : δ₀ / ((m : ℝ) + 1) ≤ δ := by
      rw [div_le_iff₀ (by positivity)]
      have := (div_le_iff₀ hδ.1).mp hm
      nlinarith [hδ.1]
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (a := (ε : ℝ≥0∞)) (by exact_mod_cast hε.ne')
    obtain ⟨Φ, hvalid, hcover, hbound⟩ := hcov m n
    obtain ⟨j, hjΦ, hδj⟩ := mem_iUnion₂.mp (hcover ⟨hδm, hδ.2⟩)
    have hle := loopF_le_loopG D x hr (hvalid j hjΦ) hδj.1.le hδj.2.le
    have hmono : ENNReal.ofReal (((j.1 : ℚ) : ℝ) ^ θ) * T ≤ ENNReal.ofReal (δ ^ θ) * T :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (hvalid j hjΦ).1.le hδj.1.le hθ.le)) le_rfl
    have hεn : ((n : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) := by
      refine le_trans ?_ hn.le
      exact ENNReal.inv_le_inv.mpr le_self_add
    calc loopF D x r δ ≤ loopG D x r j := hle
      _ ≤ ENNReal.ofReal (((j.1 : ℚ) : ℝ) ^ θ) * T + ((n : ℝ≥0∞) + 1)⁻¹ := (hbound j hjΦ).le
      _ ≤ ENNReal.ofReal (δ ^ θ) * T + ε := add_le_add hmono hεn


 
def CoverCond (δ₀ : ℝ) (m : ℕ) (Φ : Finset (ℚ × ℚ)) : Prop :=
  (∀ j ∈ Φ, ValidPair j) ∧
    Icc (δ₀ / (m + 1)) δ₀ ⊆ (⋃ j ∈ Φ, Ioo ((j.1 : ℚ) : ℝ) ((j.2 : ℚ) : ℝ))

theorem measurable_loopG (r : ℝ) (j : ℚ × ℚ) :
    Measurable fun p : LSCMetric × ℂ × ℝ≥0∞ => loopG p.1 p.2.1 r j := by
  unfold loopG aroundAt
  exact measurable_aroundRat.comp
    (measurable_fst.prodMk (measurable_snd.fst.prodMk measurable_const))

 

theorem measurableSet_loopClause {r θ δ₀ : ℝ} (hr : 0 < r) (hθ : 0 < θ) (hδ₀ : 0 < δ₀)
    (hδ₀' : δ₀ ≤ 1 / 16) :
    MeasurableSet {p : LSCMetric × ℂ × ℝ≥0∞ | p.2.2 ≠ ⊤ ∧
      ∀ δ ∈ Ioc 0 δ₀, loopF p.1 p.2.1 r δ ≤ ENNReal.ofReal (δ ^ θ) * p.2.2} := by
  classical
  have key : {p : LSCMetric × ℂ × ℝ≥0∞ | p.2.2 ≠ ⊤ ∧
      ∀ δ ∈ Ioc 0 δ₀, loopF p.1 p.2.1 r δ ≤ ENNReal.ofReal (δ ^ θ) * p.2.2} =
      {p : LSCMetric × ℂ × ℝ≥0∞ | p.2.2 ≠ ⊤} ∩
        ⋂ m : ℕ, ⋂ n : ℕ, ⋃ Φ : Finset (ℚ × ℚ),
          ({_p : LSCMetric × ℂ × ℝ≥0∞ | CoverCond δ₀ m Φ} ∩
            ⋂ j ∈ Φ, {p : LSCMetric × ℂ × ℝ≥0∞ | loopG p.1 p.2.1 r j <
              ENNReal.ofReal (((j.1 : ℚ) : ℝ) ^ θ) * p.2.2 + ((n : ℝ≥0∞) + 1)⁻¹}) := by
    ext p
    simp only [mem_inter_iff, mem_iInter, mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hT, hall⟩
      refine ⟨hT, fun m n => ?_⟩
      obtain ⟨Φ, h1, h2, h3⟩ := (loop_forall_iff_cover p.1 p.2.1 hr hθ hδ₀ hδ₀' hT).mp hall m n
      exact ⟨Φ, ⟨h1, h2⟩, fun j hj => h3 j hj⟩
    · rintro ⟨hT, hcov⟩
      refine ⟨hT, (loop_forall_iff_cover p.1 p.2.1 hr hθ hδ₀ hδ₀' hT).mpr fun m n => ?_⟩
      obtain ⟨Φ, ⟨h1, h2⟩, h3⟩ := hcov m n
      exact ⟨Φ, h1, h2, h3⟩
  rw [key]
  refine MeasurableSet.inter ?_ ?_
  · exact measurable_snd.snd (measurableSet_singleton (⊤ : ℝ≥0∞)).compl
  · refine MeasurableSet.iInter fun m => MeasurableSet.iInter fun n => ?_
    refine MeasurableSet.iUnion fun Φ => ?_
    refine (MeasurableSet.const _).inter ?_
    refine Finset.measurableSet_biInter Φ fun j _ => ?_
    exact measurableSet_lt (measurable_loopG r j)
      ((measurable_const.mul measurable_snd.snd).add measurable_const)




end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Consolidated

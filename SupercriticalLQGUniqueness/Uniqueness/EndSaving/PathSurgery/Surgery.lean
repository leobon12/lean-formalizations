import SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery.FirstEntry
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.WeylLength.WeylLength




 





set_option autoImplicit false
noncomputable section

open Set Metric Finset LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery

private def euclidForget (D : LSCMetric) : D.Space → ℂ := id

 


theorem weyl_len_eq_of_zero_trace (Dold Dref : LSCMetric)
    (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget Dold))
    (hWeyl : ∀ p : ℂ × ℂ, Dref p = weylScale ξ f Dold p)
    {P : ℝ → ℂ} {a b : ℝ} (hP : Dold.IsCurve P a b)
    (hf : ∀ u ∈ Icc a b, f (P u) = 0) :
    Dref.len P a b = Dold.len P a b := by
  have hLS47 := Toolkit.WeylLength.weylCurveLength_eq_of_zero_on_trace
    Dold ξ f hforget hP hf
  have hlen : Dref.len P a b =
      HigherDimLQGMetric.curveLengthWith
        (fun x y : ℂ => Dref (x, y)) P a b := by
    rw [Dref.len_eq_curveLength,
      ← HigherDimLQGMetric.curveLengthWith_edist]
    rfl
  rw [hlen]
  have heq : (fun x y : ℂ => Dref (x, y)) =
      (fun x y : ℂ => weylScale ξ f Dold (x, y)) := by
    funext x y
    exact hWeyl (x, y)
  rw [heq]
  exact hLS47

 

theorem weyl_geodesic_isCurve (Dold Dref : LSCMetric)
    (ξ : ℝ) (f : C(ℂ, ℝ))
    (hWeyl : ∀ p : ℂ × ℂ, Dref p = weylScale ξ f Dold p)
    (P : ℝ → ℂ) {T C : ℝ}
    (hG : IsGeodesicCurve (Dold.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dold.pt ∘ P) (Icc 0 T))
    (hBound : ∀ u ∈ Icc 0 T, ξ * f (P u) ≤ C) :
    Dref.IsCurve P 0 T := by
  let K : NNReal := ⟨Real.exp C, (Real.exp_pos C).le⟩
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (Real.exp C) := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hLip : LipschitzOnWith K (Dref.pt ∘ P) (Icc 0 T) := by
    intro s hs t ht
    rcases le_total s t with hst | hts
    · have h := weyl_subpath_le Dold Dref ξ f hWeyl P (c := C) hG hu
        hs.1 hst ht.2 (by
          intro u hu'
          exact hBound u (Icc_subset_Icc hs.1 ht.2 hu'))
      change Dref (P s, P t) ≤ (K : ℝ≥0∞) * edist s t
      rw [hK, edist_dist, Real.dist_eq, abs_sub_comm,
        abs_of_nonneg (sub_nonneg.mpr hst)]
      exact h
    · have h := weyl_subpath_le Dold Dref ξ f hWeyl P (c := C) hG hu
        ht.1 hts hs.2 (by
          intro u hu'
          exact hBound u (Icc_subset_Icc ht.1 hs.2 hu'))
      change Dref (P s, P t) ≤ (K : ℝ≥0∞) * edist s t
      rw [Dref.2.1.symm (P s) (P t), hK, edist_dist, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hts)]
      exact h
  exact ⟨hG.1, hLip.continuousOn⟩

 


theorem weyl_geodesic_isCurve_of_continuous (Dold Dref : LSCMetric)
    (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget Dold))
    (hWeyl : ∀ p : ℂ × ℂ, Dref p = weylScale ξ f Dold p)
    (P : ℝ → ℂ) {T : ℝ}
    (hG : IsGeodesicCurve (Dold.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dold.pt ∘ P) (Icc 0 T)) :
    Dref.IsCurve P 0 T := by
  have hPcont : ContinuousOn P (Icc 0 T) :=
    hforget.comp_continuousOn hG.2.1
  have hFcont : ContinuousOn (fun u => ξ * f (P u)) (Icc 0 T) :=
    continuousOn_const.mul (f.continuous.comp_continuousOn hPcont)
  have hcomp : IsCompact ((fun u => ξ * f (P u)) '' Icc 0 T) :=
    isCompact_Icc.image_of_continuousOn hFcont
  obtain ⟨C, hC⟩ := hcomp.bddAbove
  exact weyl_geodesic_isCurve Dold Dref ξ f hWeyl P hG hu
    (by intro u hu; exact hC (mem_image_of_mem _ hu))

 

theorem curve_length_le_of_metric_le (D D' : LSCMetric) (C : NNReal)
    (hcomp : ∀ x y : ℂ, D' (x, y) ≤ (C : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (a b : ℝ) :
    D'.len P a b ≤ (C : ℝ≥0∞) * D.len P a b := by
  let F : D.Space → D'.Space := fun x => x
  have hLip : LipschitzOnWith C F univ := by
    intro x _ y _
    change D' (x, y) ≤ (C : ℝ≥0∞) * D (x, y)
    exact hcomp x y
  have h := hLip.comp_eVariationOn_le
    (g := D.pt ∘ P) (s := Icc a b) (by
      intro t _
      exact mem_univ _)
  change D'.len P a b ≤ (C : ℝ≥0∞) * D.len P a b at h
  exact h

 
theorem isCurve_of_metric_le (D D' : LSCMetric) (C : NNReal)
    (hcomp : ∀ x y : ℂ, D' (x, y) ≤ (C : ℝ≥0∞) * D (x, y))
    {P : ℝ → ℂ} {a b : ℝ} (hP : D.IsCurve P a b) :
    D'.IsCurve P a b := by
  let F : D.Space → D'.Space := fun x => x
  have hLip : LipschitzOnWith C F univ := by
    intro x _ y _
    change D' (x, y) ≤ (C : ℝ≥0∞) * D (x, y)
    exact hcomp x y
  refine ⟨hP.1, ?_⟩
  have hFc : Continuous F := continuousOn_univ.mp hLip.continuousOn
  exact hFc.comp_continuousOn hP.2

 
theorem spliceN_self (P : ℝ → ℂ) (τ σ : ℕ → ℝ) (n : ℕ) :
    spliceN P (fun _ => P) τ σ n = P := by
  induction n with
  | zero => rfl
  | succ n ih =>
      funext t
      simp only [spliceN, ih]
      split_ifs <;> rfl

 


theorem reparam_curve_to_interval (D : LSCMetric) {R : ℝ → ℂ}
    {a b s t : ℝ} (hR : D.IsCurve R a b) (hst : s < t) :
    ∃ Q : ℝ → ℂ, D.IsCurve Q s t ∧ Q s = R a ∧ Q t = R b ∧
      D.len Q s t = D.len R a b ∧
      ∀ u ∈ Icc s t, Q u ∈ R '' Icc a b := by
  obtain ⟨γ, hlenγ, hrangeγ⟩ :=
    exists_path_of_curve hR.1 hR.2
  let φ : ℝ → ℝ := fun u => (u - s) / (t - s)
  let Q : ℝ → ℂ := fun u => γ.extend (φ u)
  have hden : 0 < t - s := sub_pos.mpr hst
  have hφc : Continuous φ := by fun_prop
  have hφmono : Monotone φ := by
    intro u v huv
    exact div_le_div_of_nonneg_right (sub_le_sub_right huv s) hden.le
  have hφs : φ s = 0 := by simp [φ]
  have hφt : φ t = 1 := by
    dsimp [φ]
    exact div_self hden.ne'
  have hQcont : Continuous (D.pt ∘ Q) := by
    exact γ.continuous_extend.comp hφc
  have hQcurve : D.IsCurve Q s t := ⟨hst.le, hQcont.continuousOn⟩
  have hQs : Q s = R a := by
    change γ.extend (φ s) = _
    rw [hφs]
    rw [γ.extend_zero]
    rfl
  have hQt : Q t = R b := by
    change γ.extend (φ t) = _
    rw [hφt]
    rw [γ.extend_one]
    rfl
  have hQlen : D.len Q s t = D.len R a b := by
    change curveLength (γ.extend ∘ φ) s t = _
    rw [curveLength_comp_of_continuousOn_monotoneOn γ.extend hst.le
      hφc.continuousOn (hφmono.monotoneOn _), hφs, hφt]
    exact hlenγ
  refine ⟨Q, hQcurve, hQs, hQt, hQlen, ?_⟩
  intro u hu
  have hφu : φ u ∈ Icc (0 : ℝ) 1 := by
    constructor
    · rw [← hφs]
      exact hφmono hu.1
    · rw [← hφt]
      exact hφmono hu.2
  have hγmem : γ ⟨φ u, hφu⟩ ∈ Set.range γ := Set.mem_range_self _
  have hRmem := hrangeγ hγmem
  change γ.extend (φ u) ∈ R '' Icc a b
  rw [γ.extend_extends' ⟨φ u, hφu⟩]
  obtain ⟨w, hw, heq⟩ := hRmem
  refine ⟨w, hw, ?_⟩
  exact heq

 

theorem internal_shortcut_path (D : LSCMetric) (Y : Set ℂ)
    {x y : ℂ} (hx : x ∈ Y) (hy : y ∈ Y)
    {s t : ℝ} (hst : s < t)
    {M ε : ℝ≥0∞} (hM : M ≠ ∞) (hε : 0 < ε)
    (hES : D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) ≤ M) :
    ∃ Q : ℝ → ℂ, D.IsCurve Q s t ∧ Q s = x ∧ Q t = y ∧
      (∀ u ∈ Icc s t, Q u ∈ Y) ∧ D.len Q s t < M + ε := by
  have hlt : D.internal Y (⟨x, hx⟩, ⟨y, hy⟩) < M + ε :=
    hES.trans_lt (ENNReal.lt_add_right hM hε.ne')
  unfold LSCMetric.internal at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨R, a, b, hR, hRY, hRa, hRb, hRlen⟩ := hlt
  obtain ⟨Q, hQ, hQs, hQt, hQlen, hQrange⟩ :=
    reparam_curve_to_interval D hR hst
  refine ⟨Q, hQ, hQs.trans hRa, hQt.trans hRb, ?_, ?_⟩
  · intro u hu
    obtain ⟨v, hv, hQv⟩ := hQrange u hu
    rw [← hQv]
    exact hRY v hv
  · rw [hQlen]
    exact hRlen

 


theorem finite_surgery_path_ledger_slack
    (D D' : LSCMetric) (Cplus Cstar d : NNReal) (slack : ℝ≥0∞)
    (hC : Cstar + d = Cplus)
    (hcomp : ∀ x y : ℂ, D' (x, y) ≤ (Cplus : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (Q : ℕ → ℝ → ℂ)
    (τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hP : D.IsCurve P 0 T)
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (horder : ∀ i j, i < j → j < n → σ i < τ j)
    (hQ : ∀ i < n, D'.IsCurve (Q i) (τ i) (σ i))
    (hτ : ∀ i < n, P (τ i) = Q i (τ i))
    (hσ : ∀ i < n, Q i (σ i) = P (σ i))
    (hLocal : ∀ i < n, D.len P (τ i) (σ i) = ENNReal.ofReal (σ i - τ i))
    (hShortcut : ∀ i < n,
      D'.len (Q i) (τ i) (σ i) ≤
        (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i) + slack) :
    D'.len (spliceN P Q τ σ n) 0 T +
        (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) ≤
      (Cplus : ℝ≥0∞) * D.len P 0 T + (n : ℝ≥0∞) * slack := by
  have hP' : D'.IsCurve P 0 T :=
    isCurve_of_metric_le D D' Cplus hcomp hP
  have hsplit' := finite_splice_length D' P Q τ σ n T hP'
    hbound horder hQ hτ hσ
  have hPsub : ∀ i < n, D.IsCurve P (τ i) (σ i) := by
    intro i hi
    have hbi := hbound i hi
    exact ⟨hbi.2.1, hP.2.mono (Icc_subset_Icc hbi.1 hbi.2.2)⟩
  have hsplit := finite_splice_length D P (fun _ => P) τ σ n T hP
    hbound horder hPsub (by intro _ _; rfl) (by intro _ _; rfl)
  rw [spliceN_self] at hsplit
  have hpieces : ∀ i ∈ range n,
      D'.len P (gapStart σ i) (τ i) + D'.len (Q i) (τ i) (σ i) ≤
      (Cplus : ℝ≥0∞) * D.len P (gapStart σ i) (τ i) +
        (Cstar : ℝ≥0∞) * D.len P (τ i) (σ i) + slack := by
    intro i hi
    have hin : i < n := mem_range.mp hi
    calc
      D'.len P (gapStart σ i) (τ i) + D'.len (Q i) (τ i) (σ i)
          ≤ (Cplus : ℝ≥0∞) * D.len P (gapStart σ i) (τ i) +
              ((Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i) + slack) :=
            add_le_add (curve_length_le_of_metric_le D D' Cplus hcomp P _ _)
              (hShortcut i hin)
      _ = _ := by rw [← hLocal i hin]; ac_rfl
  have hsum : ∑ i ∈ range n,
      (D'.len P (gapStart σ i) (τ i) + D'.len (Q i) (τ i) (σ i)) ≤
      ∑ i ∈ range n,
        ((Cplus : ℝ≥0∞) * D.len P (gapStart σ i) (τ i) +
          (Cstar : ℝ≥0∞) * D.len P (τ i) (σ i) + slack) :=
    sum_le_sum hpieces
  have hfinal := curve_length_le_of_metric_le D D' Cplus hcomp P (gapStart σ n) T
  calc
    D'.len (spliceN P Q τ σ n) 0 T +
          (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i)
        = (∑ i ∈ range n,
            (D'.len P (gapStart σ i) (τ i) +
              D'.len (Q i) (τ i) (σ i))) +
            D'.len P (gapStart σ n) T +
            (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) := by rw [hsplit']
    _ ≤ (∑ i ∈ range n,
            ((Cplus : ℝ≥0∞) * D.len P (gapStart σ i) (τ i) +
              (Cstar : ℝ≥0∞) * D.len P (τ i) (σ i) + slack)) +
            (Cplus : ℝ≥0∞) * D.len P (gapStart σ n) T +
            (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) := by
          gcongr
    _ = (Cplus : ℝ≥0∞) *
          ((∑ i ∈ range n,
              (D.len P (gapStart σ i) (τ i) + D.len P (τ i) (σ i))) +
              D.len P (gapStart σ n) T) +
          (n : ℝ≥0∞) * slack := by
          push_cast [← hC]
          simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib,
            Finset.sum_const, nsmul_eq_mul, card_range]
          ring_nf
          simp only [Finset.sum_add_distrib]
          ring
    _ = (Cplus : ℝ≥0∞) * D.len P 0 T +
          (n : ℝ≥0∞) * slack := by rw [← hsplit]

 

theorem finite_surgery_path_ledger
    (D D' : LSCMetric) (Cplus Cstar d : NNReal)
    (hC : Cstar + d = Cplus)
    (hcomp : ∀ x y : ℂ, D' (x, y) ≤ (Cplus : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (Q : ℕ → ℝ → ℂ)
    (τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hP : D.IsCurve P 0 T)
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (horder : ∀ i j, i < j → j < n → σ i < τ j)
    (hQ : ∀ i < n, D'.IsCurve (Q i) (τ i) (σ i))
    (hτ : ∀ i < n, P (τ i) = Q i (τ i))
    (hσ : ∀ i < n, Q i (σ i) = P (σ i))
    (hLocal : ∀ i < n, D.len P (τ i) (σ i) = ENNReal.ofReal (σ i - τ i))
    (hShortcut : ∀ i < n,
      D'.len (Q i) (τ i) (σ i) ≤
        (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i)) :
    D'.len (spliceN P Q τ σ n) 0 T +
        (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) ≤
      (Cplus : ℝ≥0∞) * D.len P 0 T := by
  have h := finite_surgery_path_ledger_slack D D' Cplus Cstar d 0 hC
    hcomp P Q τ σ n hP hbound horder hQ hτ hσ hLocal
    (by intro i hi; simpa only [add_zero] using hShortcut i hi)
  simpa only [mul_zero, add_zero] using h

 


theorem finite_surgery_of_internal_ES
    (D D' : LSCMetric) (Cplus Cstar d : NNReal)
    (hC : Cstar + d = Cplus)
    (hcomp : ∀ x y : ℂ, D' (x, y) ≤ (Cplus : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (Y : ℕ → Set ℂ)
    (τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hP : D.IsCurve P 0 T)
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (hstrict : ∀ i < n, τ i < σ i)
    (horder : ∀ i j, i < j → j < n → σ i < τ j)
    (hYτ : ∀ i (_hi : i < n), P (τ i) ∈ Y i)
    (hYσ : ∀ i (_hi : i < n), P (σ i) ∈ Y i)
    (hLocal : ∀ i < n, D.len P (τ i) (σ i) = ENNReal.ofReal (σ i - τ i))
    (hES : ∀ i (hi : i < n),
      D'.internal (Y i)
        (⟨P (τ i), hYτ i hi⟩, ⟨P (σ i), hYσ i hi⟩) ≤
      (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i)) :
    D' (P 0, P T) +
        (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) ≤
      (Cplus : ℝ≥0∞) * D.len P 0 T := by
  classical
  let B : ℝ≥0∞ := (Cplus : ℝ≥0∞) * D.len P 0 T
  change D' (P 0, P T) +
      (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) ≤ B
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε hB
  let δ : NNReal := ε / ((n : NNReal) + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδ' : (0 : ℝ≥0∞) < (δ : ℝ≥0∞) := ENNReal.coe_pos.mpr hδ
  have hExist : ∀ i : ℕ, ∀ hi : i < n,
      ∃ Q : ℝ → ℂ, D'.IsCurve Q (τ i) (σ i) ∧
        Q (τ i) = P (τ i) ∧ Q (σ i) = P (σ i) ∧
        (∀ u ∈ Icc (τ i) (σ i), Q u ∈ Y i) ∧
        D'.len Q (τ i) (σ i) <
          (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i) + (δ : ℝ≥0∞) := by
    intro i hi
    have hM : (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i) ≠ ∞ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
    exact internal_shortcut_path D' (Y i) (hYτ i hi) (hYσ i hi)
      (hstrict i hi) hM hδ' (hES i hi)
  let Q : ℕ → ℝ → ℂ := fun i =>
    if hi : i < n then Classical.choose (hExist i hi) else P
  have hQdata : ∀ i < n, D'.IsCurve (Q i) (τ i) (σ i) ∧
      Q i (τ i) = P (τ i) ∧ Q i (σ i) = P (σ i) ∧
      (∀ u ∈ Icc (τ i) (σ i), Q i u ∈ Y i) ∧
      D'.len (Q i) (τ i) (σ i) <
        (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i) + (δ : ℝ≥0∞) := by
    intro i hi
    simpa only [Q, dite_eq_left hi] using Classical.choose_spec (hExist i hi)
  have hledger := finite_surgery_path_ledger_slack D D' Cplus Cstar d
    (δ : ℝ≥0∞) hC hcomp P Q τ σ n hP hbound horder
    (by intro i hi; exact (hQdata i hi).1)
    (by intro i hi; exact (hQdata i hi).2.1.symm)
    (by intro i hi; exact (hQdata i hi).2.2.1)
    hLocal
    (by intro i hi; exact (hQdata i hi).2.2.2.2.le)
  have hends := finite_splice_cost D' P Q τ σ
    (isCurve_of_metric_le D D' Cplus hcomp hP) n hbound horder
    (by intro i hi; exact (hQdata i hi).1)
    (by intro i hi; exact (hQdata i hi).2.1.symm)
    (by intro i hi; exact (hQdata i hi).2.2.1)
  have hend : D' (P 0, P T) ≤ D'.len (spliceN P Q τ σ n) 0 T := by
    have h := edist_le_curveLength (D'.pt ∘ spliceN P Q τ σ n) hends.1.1
    change D' (spliceN P Q τ σ n 0, spliceN P Q τ σ n T) ≤
      D'.len (spliceN P Q τ σ n) 0 T at h
    simpa only [hends.2.1, hends.2.2.1] using h
  have hδsum : (n : ℝ≥0∞) * (δ : ℝ≥0∞) ≤ (ε : ℝ≥0∞) := by
    have hn : (0 : NNReal) < (n : NNReal) + 1 := by positivity
    have hnle : (n : NNReal) ≤ (n : NNReal) + 1 := by simp
    have hreal : (n : NNReal) * δ ≤ ε := by
      dsimp [δ]
      calc
        (n : NNReal) * (ε / ((n : NNReal) + 1)) =
            (ε / ((n : NNReal) + 1)) * (n : NNReal) := mul_comm _ _
        _ ≤ (ε / ((n : NNReal) + 1)) * ((n : NNReal) + 1) :=
          mul_le_mul_of_nonneg_left hnle (by positivity)
        _ = ε := div_mul_cancel₀ _ hn.ne'
    exact_mod_cast hreal
  calc
    D' (P 0, P T) + (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i)
        ≤ D'.len (spliceN P Q τ σ n) 0 T +
            (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) :=
          by simpa only [add_comm] using
            (add_le_add_right hend
              ((d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i)))
    _ ≤ B + (n : ℝ≥0∞) * (δ : ℝ≥0∞) := hledger
    _ ≤ B + (ε : ℝ≥0∞) := by
          simpa only [add_comm] using (add_le_add_left hδsum B)

 


theorem finite_surgery_ball_ES
    (D D' : LSCMetric) (Cplus Cstar d : NNReal)
    (hC : Cstar + d = Cplus)
    (hcomp : ∀ x y : ℂ, D' (x, y) ≤ (Cplus : ℝ≥0∞) * D (x, y))
    (P : ℝ → ℂ) (z : ℕ → ℂ) (r τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hP : D.IsCurve P 0 T)
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (hstrict : ∀ i < n, τ i < σ i)
    (hτmono : ∀ i j, i < j → j < n → τ i ≤ τ j)
    (hball : ∀ i < n, ∀ u ∈ Icc (τ i) (σ i),
      P u ∈ ball (z i) (4 * r i))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (ball (z i) (4 * r i)) (ball (z j) (4 * r j)))
    (hLocal : ∀ i < n, D.len P (τ i) (σ i) = ENNReal.ofReal (σ i - τ i))
    (hES : ∀ i (_hi : i < n)
      (hτ : P (τ i) ∈ ball (z i) (4 * r i))
      (hσ : P (σ i) ∈ ball (z i) (4 * r i)),
      D'.internal (ball (z i) (4 * r i))
        (⟨P (τ i), hτ⟩, ⟨P (σ i), hσ⟩) ≤
      (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i)) :
    D' (P 0, P T) +
        (d : ℝ≥0∞) * ∑ i ∈ range n, D.len P (τ i) (σ i) ≤
      (Cplus : ℝ≥0∞) * D.len P 0 T := by
  have htimes := ball_segments_disjoint_times (range n) P z
    (fun i => 4 * r i) τ σ
    (by intro i hi; exact hball i (mem_range.mp hi))
    (by intro i hi j hj; exact hdisj i (mem_range.mp hi) j (mem_range.mp hj))
    (by intro i hi; exact (hbound i (mem_range.mp hi)).2.1)
  have horder : ∀ i j, i < j → j < n → σ i < τ j := by
    intro i j hij hj
    have hi : i < n := hij.trans hj
    rcases htimes i (mem_range.mpr hi) j (mem_range.mpr hj)
      (Nat.ne_of_lt hij) with h | h
    · exact h
    · have hmono := hτmono i j hij hj
      have hstrictj := hstrict j hj
      linarith
  let Y : ℕ → Set ℂ := fun i => ball (z i) (4 * r i)
  have hYτ : ∀ i (_hi : i < n), P (τ i) ∈ Y i := by
    intro i hi
    exact hball i hi (τ i) ⟨le_rfl, (hstrict i hi).le⟩
  have hYσ : ∀ i (_hi : i < n), P (σ i) ∈ Y i := by
    intro i hi
    exact hball i hi (σ i) ⟨(hstrict i hi).le, le_rfl⟩
  exact finite_surgery_of_internal_ES D D' Cplus Cstar d hC hcomp
    P Y τ σ n hP hbound hstrict horder hYτ hYσ hLocal
    (by intro i hi; exact hES i hi (hYτ i hi) (hYσ i hi))

 



theorem finite_surgery_ball_ES_weyl
    (Dold Dref Dtilde : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget Dold))
    (hWeyl : ∀ p : ℂ × ℂ, Dref p = weylScale ξ f Dold p)
    (Cplus Cstar d : NNReal) (hC : Cstar + d = Cplus)
    (hcomp : ∀ x y : ℂ,
      Dtilde (x, y) ≤ (Cplus : ℝ≥0∞) * Dref (x, y))
    (P : ℝ → ℂ) (z : ℕ → ℂ) (r τ σ : ℕ → ℝ) {T : ℝ} (n : ℕ)
    (hG : IsGeodesicCurve (Dold.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dold.pt ∘ P) (Icc 0 T))
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (hstrict : ∀ i < n, τ i < σ i)
    (hτmono : ∀ i j, i < j → j < n → τ i ≤ τ j)
    (hball : ∀ i < n, ∀ u ∈ Icc (τ i) (σ i),
      P u ∈ ball (z i) (4 * r i))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (ball (z i) (4 * r i)) (ball (z j) (4 * r j)))
    (hfzero : ∀ i < n, ∀ x ∈ ball (z i) (4 * r i), f x = 0)
    (hES : ∀ i (_hi : i < n)
      (hτ : P (τ i) ∈ ball (z i) (4 * r i))
      (hσ : P (σ i) ∈ ball (z i) (4 * r i)),
      Dtilde.internal (ball (z i) (4 * r i))
        (⟨P (τ i), hτ⟩, ⟨P (σ i), hσ⟩) ≤
      (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i)) :
    Dtilde (P 0, P T) +
        (d : ℝ≥0∞) * ∑ i ∈ range n, Dref.len P (τ i) (σ i) ≤
      (Cplus : ℝ≥0∞) * Dref.len P 0 T := by
  have hLocal : ∀ i < n,
      Dref.len P (τ i) (σ i) = ENNReal.ofReal (σ i - τ i) := by
    intro i hi
    have hb := hbound i hi
    have hPold : Dold.IsCurve P (τ i) (σ i) :=
      ⟨hb.2.1, hG.2.1.mono (Icc_subset_Icc hb.1 hb.2.2)⟩
    have hzero : ∀ u ∈ Icc (τ i) (σ i), f (P u) = 0 := by
      intro u hu'
      exact hfzero i hi (P u) (hball i hi u hu')
    calc
      Dref.len P (τ i) (σ i) = Dold.len P (τ i) (σ i) :=
        weyl_len_eq_of_zero_trace Dold Dref ξ f hforget hWeyl hPold hzero
      _ = ENNReal.ofReal (σ i - τ i) :=
        curveLength_of_hasUnitSpeedOn hu ⟨hb.1, hb.2.1.trans hb.2.2⟩
          ⟨hb.1.trans hb.2.1, hb.2.2⟩
  have hPref : Dref.IsCurve P 0 T :=
    weyl_geodesic_isCurve_of_continuous Dold Dref ξ f hforget hWeyl P hG hu
  exact finite_surgery_ball_ES Dref Dtilde Cplus Cstar d hC hcomp
    P z r τ σ n hPref hbound hstrict hτmono hball hdisj hLocal hES

 


theorem finite_surgery_ES_spent
    (Dold Dref Dtilde : LSCMetric) (ξ : ℝ) (f : C(ℂ, ℝ))
    (hforget : Continuous (euclidForget Dold))
    (hWeyl : ∀ p : ℂ × ℂ, Dref p = weylScale ξ f Dold p)
    (Cplus Cstar gap c Cspent : NNReal) (hC : Cstar + gap = Cplus)
    (hcomp : ∀ x y : ℂ,
      Dtilde (x, y) ≤ (Cplus : ℝ≥0∞) * Dref (x, y))
    (P : ℝ → ℂ) (z : ℕ → ℂ) (r τ σ : ℕ → ℝ) {T : ℝ} (n m : ℕ)
    (K₁ K₂ : Set ℂ) (B : ℝ≥0∞)
    (hG : IsGeodesicCurve (Dold.pt ∘ P) 0 T)
    (hu : HasUnitSpeedOn (Dold.pt ∘ P) (Icc 0 T))
    (hK₁ : P 0 ∈ K₁) (hK₂ : P T ∈ K₂)
    (hbound : ∀ i < n, 0 ≤ τ i ∧ τ i ≤ σ i ∧ σ i ≤ T)
    (hstrict : ∀ i < n, τ i < σ i)
    (hτmono : ∀ i j, i < j → j < n → τ i ≤ τ j)
    (hball : ∀ i < n, ∀ u ∈ Icc (τ i) (σ i),
      P u ∈ ball (z i) (4 * r i))
    (hdisj : ∀ i < n, ∀ j < n, i ≠ j →
      Disjoint (ball (z i) (4 * r i)) (ball (z j) (4 * r j)))
    (hfzero : ∀ i < n, ∀ x ∈ ball (z i) (4 * r i), f x = 0)
    (hTime : ∀ i < n,
      (c : ℝ≥0∞) * B ≤ ENNReal.ofReal (σ i - τ i))
    (hSpent : Dref.len P 0 T ≤
      setDistLSC Dref K₁ K₂ + (Cspent : ℝ≥0∞) * B * (m : ℝ≥0∞))
    (hES : ∀ i (_hi : i < n)
      (hτ : P (τ i) ∈ ball (z i) (4 * r i))
      (hσ : P (σ i) ∈ ball (z i) (4 * r i)),
      Dtilde.internal (ball (z i) (4 * r i))
        (⟨P (τ i), hτ⟩, ⟨P (σ i), hσ⟩) ≤
      (Cstar : ℝ≥0∞) * ENNReal.ofReal (σ i - τ i)) :
    setDistLSC Dtilde K₁ K₂ +
        (gap : ℝ≥0∞) * (c : ℝ≥0∞) * B * (n : ℝ≥0∞) ≤
      (Cplus : ℝ≥0∞) * setDistLSC Dref K₁ K₂ +
        (Cplus : ℝ≥0∞) * (Cspent : ℝ≥0∞) * B * (m : ℝ≥0∞) := by
  have hseg : ∀ i < n,
      Dref.len P (τ i) (σ i) = ENNReal.ofReal (σ i - τ i) := by
    intro i hi
    have hb := hbound i hi
    have hPold : Dold.IsCurve P (τ i) (σ i) :=
      ⟨hb.2.1, hG.2.1.mono (Icc_subset_Icc hb.1 hb.2.2)⟩
    have hzero : ∀ u ∈ Icc (τ i) (σ i), f (P u) = 0 := by
      intro u hu'
      exact hfzero i hi (P u) (hball i hi u hu')
    calc
      Dref.len P (τ i) (σ i) = Dold.len P (τ i) (σ i) :=
        weyl_len_eq_of_zero_trace Dold Dref ξ f hforget hWeyl hPold hzero
      _ = ENNReal.ofReal (σ i - τ i) :=
        curveLength_of_hasUnitSpeedOn hu ⟨hb.1, hb.2.1.trans hb.2.2⟩
          ⟨hb.1.trans hb.2.1, hb.2.2⟩
  have hsum : (n : ℝ≥0∞) * ((c : ℝ≥0∞) * B) ≤
      ∑ i ∈ range n, Dref.len P (τ i) (σ i) := by
    calc
      (n : ℝ≥0∞) * ((c : ℝ≥0∞) * B) =
          ∑ _i ∈ range n, (c : ℝ≥0∞) * B := by
            simp only [sum_const, card_range, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum (by
        intro i hi
        rw [hseg i (mem_range.mp hi)]
        exact hTime i (mem_range.mp hi))
  have hDist : setDistLSC Dtilde K₁ K₂ ≤ Dtilde (P 0, P T) := by
    unfold setDistLSC
    exact iInf_le_of_le (P 0) <| iInf_le_of_le hK₁ <|
      iInf_le_of_le (P T) <| iInf_le_of_le hK₂ le_rfl
  have hSurgery := finite_surgery_ball_ES_weyl Dold Dref Dtilde ξ f
    hforget hWeyl Cplus Cstar gap hC hcomp P z r τ σ n
    hG hu hbound hstrict hτmono hball hdisj hfzero hES
  calc
    setDistLSC Dtilde K₁ K₂ +
        (gap : ℝ≥0∞) * (c : ℝ≥0∞) * B * (n : ℝ≥0∞)
        = setDistLSC Dtilde K₁ K₂ +
            (gap : ℝ≥0∞) * ((n : ℝ≥0∞) * ((c : ℝ≥0∞) * B)) := by ring
    _ ≤ Dtilde (P 0, P T) +
          (gap : ℝ≥0∞) * ∑ i ∈ range n, Dref.len P (τ i) (σ i) := by
          gcongr
    _ ≤ (Cplus : ℝ≥0∞) * Dref.len P 0 T := hSurgery
    _ ≤ (Cplus : ℝ≥0∞) *
          (setDistLSC Dref K₁ K₂ +
            (Cspent : ℝ≥0∞) * B * (m : ℝ≥0∞)) := by gcongr
    _ = (Cplus : ℝ≥0∞) * setDistLSC Dref K₁ K₂ +
          (Cplus : ℝ≥0∞) * (Cspent : ℝ≥0∞) * B * (m : ℝ≥0∞) := by ring


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.PathSurgery

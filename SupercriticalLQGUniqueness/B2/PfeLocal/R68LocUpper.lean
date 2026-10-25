import SupercriticalLQGUniqueness.B2.PfeLocal.R68LocWeyl
import SupercriticalLQGUniqueness.B2.PfeLocal.L6Locality

 




















set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open Uniqueness.Toolkit.CompactPathInfimum

 
def r68Y (G : LSCMetric) (Q : Set ℂ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℝ) : ℝ≥0∞ :=
  compactPathInf G (cthickening η Q) (cthickening η (l5Ball b₁)) (cthickening η (l5Ball b₂))

 
def r68Z (D : LSCMetric) (Q : Set ℂ) (b₁ b₂ : ℚ × ℚ × ℚ) : ℝ≥0∞ :=
  compactPathInf D Q (l5Ball b₁) (l5Ball b₂)

 
theorem r68_exists_ball {x : ℂ} {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ b : ℚ × ℚ × ℚ, x ∈ l5Ball b ∧ ∀ η : ℝ, 0 ≤ η → η ≤ ρ / 4 →
      cthickening η (l5Ball b) ⊆ ball x ρ := by
  obtain ⟨q₁, hq₁⟩ := exists_rat_btwn (show x.re - ρ / 8 < x.re + ρ / 8 by linarith)
  obtain ⟨q₂, hq₂⟩ := exists_rat_btwn (show x.im - ρ / 8 < x.im + ρ / 8 by linarith)
  obtain ⟨r, hr⟩ := exists_rat_btwn (show ρ / 4 < ρ / 3 by linarith)
  set c : ℂ := ⟨(q₁ : ℝ), (q₂ : ℝ)⟩ with hc
  have hdist : dist c x < ρ / 4 := by
    rw [Complex.dist_eq]
    have h1 : |c.re - x.re| < ρ / 8 := by
      rw [abs_lt]; simp only [hc]; constructor <;> linarith [hq₁.1, hq₁.2]
    have h2 : |c.im - x.im| < ρ / 8 := by
      rw [abs_lt]; simp only [hc]; constructor <;> linarith [hq₂.1, hq₂.2]
    calc ‖c - x‖ ≤ |(c - x).re| + |(c - x).im| := Complex.norm_le_abs_re_add_abs_im _
      _ = |c.re - x.re| + |c.im - x.im| := by simp
      _ < ρ / 8 + ρ / 8 := add_lt_add h1 h2
      _ = ρ / 4 := by ring
  refine ⟨(q₁, q₂, r), ?_, fun η hη hηρ => ?_⟩
  · show x ∈ closedBall c (r : ℝ)
    rw [mem_closedBall, dist_comm]; linarith [hr.1]
  · have hr0 : (0 : ℝ) ≤ r := by linarith [hr.1]
    show cthickening η (closedBall c (r : ℝ)) ⊆ ball x ρ
    rw [cthickening_closedBall hη hr0]
    intro w hw
    rw [mem_closedBall] at hw
    rw [mem_ball]
    linarith [dist_triangle w c x, hr.2]

 
theorem r68_lowerNbhdObs_le_internal {G : ℕ → LSCMetric} {D : LSCMetric}
    (hDforget : Continuous (PfeWeyl.euclidForget D)) {W V : Set ℂ} (hW : IsOpen W)
    (hWV : W ⊆ V)
    (H : ∀ (k : ℕ) (b₁ b₂ : ℚ × ℚ × ℚ) (η : ℚ), 0 < η →
      liminf (fun n => r68Y (G n) (closure (l6Exh W k)) b₁ b₂ η) atTop ≤
        r68Z D (closure (l6Exh W k)) b₁ b₂)
    (x y : W) :
    PfeAxioms.lowerNeighborhoodObservable G V ⟨(x : ℂ), hWV x.2⟩ ⟨(y : ℂ), hWV y.2⟩ ≤
      D.internal W (x, y) := by
  unfold PfeAxioms.lowerNeighborhoodObservable
  refine iSup_le fun κ => ?_
  set ρ : ℝ := 1 / ((κ : ℝ) + 1) with hρ
  have hρ0 : 0 < ρ := by positivity
  unfold LSCMetric.internal
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPW => le_iInf fun ha => le_iInf fun hb => ?_
  
  have hPc : ContinuousOn P (Icc a b) := hDforget.comp_continuousOn hP.2
  have hKc : IsCompact (P '' Icc a b) := (isCompact_Icc).image_of_continuousOn hPc
  have hKW : P '' Icc a b ⊆ W := by rintro _ ⟨t, ht, rfl⟩; exact hPW t ht
  obtain ⟨k, hk⟩ := exists_l6Exh_of_compact hKc hW hKW
  set Q : Set ℂ := closure (l6Exh W k) with hQ
  have hQc : IsCompact Q := isCompact_closure_l6Exh W k
  have hQW : Q ⊆ W := closure_l6Exh_subset W k
  obtain ⟨η₀, hη₀, hη₀W⟩ := hQc.exists_cthickening_subset_open hW hQW
  obtain ⟨η, hη, hηle⟩ := exists_rat_btwn (show (0 : ℝ) < min η₀ (ρ / 4) from lt_min hη₀ (by linarith))
  have hη1 : (η : ℝ) ≤ η₀ := hηle.le.trans (min_le_left _ _)
  have hη2 : (η : ℝ) ≤ ρ / 4 := hηle.le.trans (min_le_right _ _)
  obtain ⟨b₁, hxb, hb₁⟩ := r68_exists_ball (x := (x : ℂ)) hρ0
  obtain ⟨b₂, hyb, hb₂⟩ := r68_exists_ball (x := (y : ℂ)) hρ0
  have hηpos : (0 : ℚ) < η := by exact_mod_cast hη
  
  have hstep : ∀ n, PfeAxioms.neighborhoodInternal (G n) V ⟨(x : ℂ), hWV x.2⟩ ⟨(y : ℂ), hWV y.2⟩
      (1 / ((κ : ℝ) + 1)) ≤ r68Y (G n) Q b₁ b₂ η := by
    intro n
    unfold r68Y compactPathInf
    refine le_iInf fun P' => le_iInf fun s => le_iInf fun t => le_iInf fun hP' =>
      le_iInf fun htr => le_iInf fun hs => le_iInf fun ht => ?_
    have hsV : P' s ∈ V := hWV (hη₀W ((cthickening_mono hη1 Q) (htr s ⟨le_rfl, hP'.1⟩)))
    have htV : P' t ∈ V := hWV (hη₀W ((cthickening_mono hη1 Q) (htr t ⟨hP'.1, le_rfl⟩)))
    have hsx : dist (P' s) x < ρ := by
      have := hb₁ η (by exact_mod_cast hη.le) hη2 hs; rwa [mem_ball] at this
    have hty : dist (P' t) y < ρ := by
      have := hb₂ η (by exact_mod_cast hη.le) hη2 ht; rwa [mem_ball] at this
    unfold PfeAxioms.neighborhoodInternal
    refine iInf_le_of_le ⟨P' s, hsV⟩ (iInf_le_of_le hsx (iInf_le_of_le ⟨P' t, htV⟩
      (iInf_le_of_le hty ?_)))
    unfold LSCMetric.internal
    exact iInf_le_of_le P' (iInf_le_of_le s (iInf_le_of_le t (iInf_le_of_le hP'
      (iInf_le_of_le (fun u hu => hWV (hη₀W ((cthickening_mono hη1 Q) (htr u hu))))
        (iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl))))))
  calc liminf (fun n => PfeAxioms.neighborhoodInternal (G n) V ⟨(x : ℂ), hWV x.2⟩
        ⟨(y : ℂ), hWV y.2⟩ (1 / ((κ : ℝ) + 1))) atTop
      ≤ liminf (fun n => r68Y (G n) Q b₁ b₂ η) atTop :=
        liminf_le_liminf (Eventually.of_forall hstep)
    _ ≤ r68Z D Q b₁ b₂ := H k b₁ b₂ η hηpos
    _ ≤ D.len P a b := by
        unfold r68Z
        refine l5_compactPathInf_le D P a b hP (fun t ht => ?_) (by rw [ha]; exact hxb)
          (by rw [hb]; exact hyb)
        exact subset_closure (hk ⟨t, ht, rfl⟩)

end SupercriticalLQGUniqueness.B2.PfeLocal

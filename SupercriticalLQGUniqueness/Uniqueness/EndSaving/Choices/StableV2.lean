import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.LemmasASV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.CountingCore.Section4Counting




 

















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
def cSub (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : ℝ :=
  (par.Cacross / (par.Caround * cSpent ξ par)) *
    (cNew ξ par - 2 * par.Caround * par.Ctime / par.Cacross)

theorem cSub_pos (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : 0 < cSub ξ par := by
  unfold cSub
  have h1 := sub_pos.mpr (cNew_gt ξ par)
  have := par.across_pos
  have := par.around_pos
  have := cSpent_pos ξ par
  positivity

theorem cSub_lt_one (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : cSub ξ par < 1 := by
  unfold cSub
  have ha := par.across_pos
  have hr := par.around_pos
  have hra := par.around_gt_across
  have hct := par.tube_pos
  have hcm := par.time_pos
  have hsp : 2 * par.Caround ≤ cSpent ξ par := by
    unfold cSpent
    have : (1 : ℝ) ≤ Real.exp ((ξ : ℝ) * par.Cmax) :=
      Real.one_le_exp (mul_nonneg ξ.property.le par.max_pos.le)
    nlinarith
  have hcn : cNew ξ par ≤ par.Cacross := by
    unfold cNew
    have := Real.exp_pos (-(ξ : ℝ) * par.Cmax)
    nlinarith
  have hβ : 0 < 2 * par.Caround * par.Ctime / par.Cacross := by positivity
  have hsp0 := cSpent_pos ξ par
  rw [div_mul_eq_mul_div, div_lt_one (by positivity)]
  calc par.Cacross * (cNew ξ par - 2 * par.Caround * par.Ctime / par.Cacross)
      < par.Cacross * par.Cacross := by
        apply mul_lt_mul_of_pos_left _ ha
        linarith
    _ < par.Caround * par.Caround := by nlinarith
    _ ≤ par.Caround * cSpent ξ par := by nlinarith

 

theorem stable_subset_pathwise {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (ω : Ω)
    (hω : SampleRegularV2 μ h D D' ξ Q cMid par pbar r obj ω)
    (hF : EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω))
    (hU : ∀ W ⊆ Z, W.Nonempty → ∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W (h ω))) K₁ K₂ P T) :
    ∃ Z' ⊆ Z, EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z' (h ω) ∧
      cSub ξ par * Z.card ≤ Z'.card := by
  classical
  have hFsave := hF
  rcases hF with ⟨hZne, hconfig, hbr₀, havg₀, _, hlocal, P₀, T₀, hgeod₀, _⟩
  set g := h ω with hg
  set z : ℤ × ℤ → ℂ := fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i with hz
  have hr0 : (0 : ℝ) < r := r.property
  have hξ : (0 : ℝ) ≤ ξ := ξ.property.le
  
  have hU' : ∀ W, W ⊆ Z → ∃ P : ℝ → ℂ, ∃ T : ℝ,
      EndSaving.FiniteEvents.UniqueSetGeodesic
        (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W g)) K₁ K₂ P T := by
    intro W hW
    rcases W.eq_empty_or_nonempty with hWe | hWne
    · subst hWe
      rw [subtractBumps_empty]
      exact ⟨P₀, T₀, hgeod₀⟩
    · exact hU W hW hWne
  choose! PW TW hPW using hU'
  
  have hloc : ∀ i ∈ Z, ∃ c : ℝ, IsCircleAverage g r (z i) c ∧
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q c hbr₀ := by
    intro i hi
    obtain ⟨_, c, hc, hbin⟩ := hlocal i hi
    exact ⟨c, hc, hbin⟩
  choose! c hc hbin using hloc
  have hE : ∀ i ∈ Z, g ∈ (obj i).E := fun i hi => (hlocal i hi).1
  set B := scaleB ξ Q b q hbr₀ with hB
  have hBpos : 0 < B := scaleB_pos ξ Q b q hbr₀
  set N : ℤ × ℤ → ℝ := fun i => scaleN ξ Q r (c i) with hN
  have hN2B : ∀ i ∈ Z, N i ≤ 2 * B := by
    intro i hi
    have := (hbin i hi).2
    simp only [hN, scaleN, hB, scaleB]
    linarith
  
  let keep : Finset (ℤ × ℤ) → Finset (ℤ × ℤ) := fun W => W.filter fun i =>
    ∃ e ∈ ovSet (PW W) (TW W) (ball (z i) (4 * (r : ℝ))) (obj i).V,
      ENNReal.ofReal (par.Ctime * N i) ≤ D g (PW W e.2.1, PW W e.2.2.1)
  let L : Finset (ℤ × ℤ) → ℝ := fun W =>
    (OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W g)) K₁ K₂).toReal
  have hsetW : ∀ W ⊆ Z,
      OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W g)) K₁ K₂ =
        ENNReal.ofReal (TW W) := fun W hW => ((hPW W hW).1.2.2.2).symm
  have hTW0 : ∀ W ⊆ Z, 0 ≤ TW W := fun W hW =>
    (EndSaving.FiniteEvents.SetGeodesic.isGeodesic _ K₁ K₂ _ _ (hPW W hW).1).1
  have hLW : ∀ W ⊆ Z, L W = TW W := by
    intro W hW
    simp only [L]
    rw [hsetW W hW, ENNReal.toReal_ofReal (hTW0 W hW)]
  have hkeep : ∀ W ⊆ Z, keep W ⊆ W := fun W _ => Finset.filter_subset _ _
  set β := 2 * par.Caround * par.Ctime / par.Cacross with hβ
  set K := (par.Caround / par.Cacross) * cSpent ξ par with hK
  have hβ0 : 0 ≤ β := by
    have := par.around_pos; have := par.time_pos; have := par.across_pos; positivity
  have hK0 : 0 < K := by
    have := par.around_pos; have := par.across_pos; have := cSpent_pos ξ par; positivity
  
  have hupper : L Z ≤ L ∅ - cNew ξ par * B * (Z.card : ℝ) := by
    have hup := upper_fbarV2_of_regular μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g
      hω.1 hFsave hbr₀ havg₀
    have h0 : OptimalConstants.Ratios.setDist (D g) K₁ K₂ = ENNReal.ofReal (TW ∅) := by
      have := hsetW ∅ (Finset.empty_subset Z)
      rwa [subtractBumps_empty] at this
    rw [hsetW Z le_rfl, h0, ← ENNReal.ofReal_add (hTW0 Z le_rfl)
      (by have := cNew_pos ξ par; positivity)] at hup
    have hreal := (ENNReal.ofReal_le_ofReal_iff (hTW0 ∅ (Finset.empty_subset Z))).mp hup
    rw [hLW Z le_rfl, hLW ∅ (Finset.empty_subset Z)]
    linarith
  
  have hincrement : ∀ W ⊆ Z, keep W ≠ W →
      L (keep W) ≤ L W + β * B * ((W.card : ℝ) - ((keep W).card : ℝ)) := by
    intro W hW _
    set Kp := keep W with hKp
    set R := W \ Kp with hR
    have hKpZ : Kp ⊆ Z := (hkeep W hW).trans hW
    have hRZ : R ⊆ Z := (Finset.sdiff_subset).trans hW
    have hKR : Disjoint Kp R := Finset.disjoint_sdiff
    have hunion : Kp ∪ R = W := Finset.union_sdiff_of_subset (hkeep W hW)
    have hreg : RegularAt D (ξ : ℝ)
        (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Kp ∪ R) g) := by
      rw [hunion]; exact hω.2 W
    have hgeod : EndSaving.FiniteEvents.SetGeodesic
        (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (Kp ∪ R) g))
        K₁ K₂ (PW W) (TW W) := by
      rw [hunion]; exact (hPW W hW).1
    have hlow := lower_general_max_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ obj Z Kp R hconfig
      hKpZ hRZ hKR ω hreg (fun i hi => hE i (hRZ hi)) (PW W) (TW W) hgeod
    rw [hunion] at hlow
    
    have hregK := hω.2 Kp
    have hWK : ∀ p : ℂ × ℂ, D g p = weylScale ξ
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Kp))
        (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Kp g)) p := by
      intro p
      rw [hregK.weyl, addFun_subtract_self]
    have hmono : ∀ x y : ℂ,
        D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Kp g) (x, y) ≤ D g (x, y) :=
      EndSaving.Spent.metric_le_weyl _ _ ξ hξ _ hregK.forget hWK
        (fun x => bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj Kp x)
    have hsup : ∀ i ∈ R,
        (⨆ e ∈ ovSet (PW W) (TW W) (ball (z i) (4 * (r : ℝ))) (obj i).V,
          D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Kp g)
            (PW W e.2.1, PW W e.2.2.1)) ≤ ENNReal.ofReal (2 * par.Ctime * B) := by
      intro i hi
      have hiW : i ∈ W := (Finset.mem_sdiff.mp hi).1
      have hiK : i ∉ Kp := (Finset.mem_sdiff.mp hi).2
      refine iSup₂_le fun e he => ?_
      have hnot : ¬ ENNReal.ofReal (par.Ctime * N i) ≤ D g (PW W e.2.1, PW W e.2.2.1) := by
        intro hle
        exact hiK (Finset.mem_filter.mpr ⟨hiW, e, he, hle⟩)
      calc D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Kp g)
            (PW W e.2.1, PW W e.2.2.1) ≤ D g (PW W e.2.1, PW W e.2.2.1) := hmono _ _
        _ ≤ ENNReal.ofReal (par.Ctime * N i) := (lt_of_not_ge hnot).le
        _ ≤ ENNReal.ofReal (2 * par.Ctime * B) := by
            apply ENNReal.ofReal_le_ofReal
            have := hN2B i (hRZ hi)
            have := par.time_pos
            nlinarith
    have hsum : ENNReal.ofReal (par.Caround / par.Cacross) * ∑ i ∈ R,
        (⨆ e ∈ ovSet (PW W) (TW W) (ball (z i) (4 * (r : ℝ))) (obj i).V,
          D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Kp g)
            (PW W e.2.1, PW W e.2.2.1)) ≤ ENNReal.ofReal (β * B * R.card) := by
      calc _ ≤ ENNReal.ofReal (par.Caround / par.Cacross) *
            ∑ _i ∈ R, ENNReal.ofReal (2 * par.Ctime * B) := by
            gcongr with i hi
            exact hsup i hi
        _ = ENNReal.ofReal (β * B * R.card) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ← ENNReal.ofReal_mul (div_nonneg par.around_pos.le par.across_pos.le)]
            congr 1
            rw [hβ]
            ring
    have hβB : 0 ≤ β * B * R.card := mul_nonneg (mul_nonneg hβ0 hBpos.le) (Nat.cast_nonneg _)
    have hfinal := hlow.trans (add_le_add le_rfl hsum)
    rw [hsetW Kp hKpZ, hsetW W hW, ← ENNReal.ofReal_add (hTW0 W hW) hβB] at hfinal
    have hreal := (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hTW0 W hW) hβB)).mp hfinal
    have hcardR : (R.card : ℝ) = (W.card : ℝ) - (Kp.card : ℝ) := by
      rw [hR, Finset.card_sdiff_of_subset (hkeep W hW), Nat.cast_sub (Finset.card_le_card (hkeep W hW))]
    rw [hLW Kp hKpZ, hLW W hW, ← hcardR]
    linarith
  
  have hspent : ∀ W ⊆ Z, L ∅ ≤ L W + K * B * (W.card : ℝ) := by
    intro W hW
    have hreg : RegularAt D (ξ : ℝ)
        (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (∅ ∪ W) g) := by
      rw [Finset.empty_union]; exact hω.2 W
    have hgeod : EndSaving.FiniteEvents.SetGeodesic
        (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj (∅ ∪ W) g))
        K₁ K₂ (PW W) (TW W) := by
      rw [Finset.empty_union]; exact (hPW W hW).1
    have hlow := lower_general_max_v2 μ h D D' ξ Q cMid par pbar r b K₁ K₂ obj Z ∅ W hconfig
      (Finset.empty_subset _) hW (Finset.disjoint_empty_left W) ω hreg
      (fun i hi => hE i (hW hi)) (PW W) (TW W) hgeod
    rw [Finset.empty_union, subtractBumps_empty] at hlow
    set d1 := D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W g) with hd1
    have hWh : ∀ p : ℂ × ℂ, D g p = weylScale ξ
        (LQGMetric.testCont (EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W)) d1 p := by
      intro p
      rw [(hω.2 W).weyl, addFun_subtract_self]
    have hG := EndSaving.FiniteEvents.SetGeodesic.isGeodesic d1 K₁ K₂ _ _ (hPW W hW).1
    have hsup : ∀ i ∈ W,
        (⨆ e ∈ ovSet (PW W) (TW W) (ball (z i) (4 * (r : ℝ))) (obj i).V,
          D g (PW W e.2.1, PW W e.2.2.1)) ≤ ENNReal.ofReal (cSpent ξ par * B) := by
      intro i hi
      refine iSup₂_le fun e he => ?_
      have hO : IsOpen (ball (z i) (4 * (r : ℝ))) := isOpen_ball
      have hVO : closure ((obj i).V : Set ℂ) ⊆ ball (z i) (4 * (r : ℝ)) := by
        intro x hx
        have := ((obj i).closure_V_annulus hx).2
        rw [mem_ball]; linarith
      obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO he.1
      obtain ⟨h0, _, h23, _, h4T, _, _, _, hτV, hσV, _, _⟩ := he.1
      have hτC : e.2.1 ∈ EndSaving.Spent.closedContactTimes (PW W) ((obj i).V : Set ℂ) (TW W) :=
        ⟨⟨h0.trans he12.le, h23.trans (he34.le.trans h4T)⟩, hτV⟩
      have hσC : e.2.2.1 ∈ EndSaving.Spent.closedContactTimes (PW W) ((obj i).V : Set ℂ) (TW W) :=
        ⟨⟨(h0.trans he12.le).trans h23, he34.le.trans h4T⟩, hσV⟩
      have hout : ∀ x ∈ K₁ ∪ K₂, 4 * (r : ℝ) ≤ dist x (z i) := by
        intro x hx
        have hnot : x ∉ ball (z i) (4 * (r : ℝ)) :=
          fun hb => Set.disjoint_left.mp (hconfig.2 i (hW hi)) hb (Or.inl hx)
        simpa only [mem_ball, not_lt] using hnot
      have hspentI := EndSaving.FiniteEvents.objectAtV2_spent_closed_contacts μ h D D' ξ Q cMid par pbar (z i) r
        (obj i) ω (hE i (hW hi)) (c i) (hc i (hW hi)) d1 _ (hω.2 W).barrier (hω.2 W).length hWh
        (fun x => bumpSum_nonneg μ h D D' ξ Q cMid par pbar r obj W x)
        (fun x => bumpSum_le_Cmax μ h D D' ξ Q cMid par pbar r obj b K₁ K₂ Z W hconfig hW x)
        (PW W) hG (hPW W hW).1.1.2.1 (hout _ (Or.inl (hPW W hW).1.2.1))
        (hout _ (Or.inr (hPW W hW).1.2.2.1)) ⟨_, hτC⟩ _
        (EndSaving.FiniteEvents.localSizeBin_upper_ennreal ξ Q r b q (c i) hbr₀ (hbin i (hW hi)))
      have htarget : (ENNReal.ofReal (Real.exp ((ξ : ℝ) * par.Cmax)) * ENNReal.ofReal par.Caround *
          2) * ENNReal.ofReal B = ENNReal.ofReal (cSpent ξ par * B) := by
        unfold cSpent
        rw [ENNReal.ofReal_mul (by have := par.around_pos; positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        simp only [ENNReal.ofReal_ofNat]
        ring
      rw [← htarget]
      exact (le_iSup₂_of_le (f := fun (u : ℝ) (_ : u ∈ EndSaving.Spent.closedContactTimes (PW W)
          ((obj i).V : Set ℂ) (TW W)) => ⨆ v ∈ EndSaving.Spent.closedContactTimes (PW W)
            ((obj i).V : Set ℂ) (TW W), D g (PW W u, PW W v)) e.2.1 hτC
          (le_iSup₂_of_le (f := fun (v : ℝ) (_ : v ∈ EndSaving.Spent.closedContactTimes (PW W)
            ((obj i).V : Set ℂ) (TW W)) => D g (PW W e.2.1, PW W v)) e.2.2.1 hσC le_rfl)).trans
        (le_sup_left.trans hspentI)
    have hsum : ENNReal.ofReal (par.Caround / par.Cacross) * ∑ i ∈ W,
        (⨆ e ∈ ovSet (PW W) (TW W) (ball (z i) (4 * (r : ℝ))) (obj i).V,
          D g (PW W e.2.1, PW W e.2.2.1)) ≤ ENNReal.ofReal (K * B * W.card) := by
      calc _ ≤ ENNReal.ofReal (par.Caround / par.Cacross) *
            ∑ _i ∈ W, ENNReal.ofReal (cSpent ξ par * B) := by
            gcongr with i hi
            exact hsup i hi
        _ = ENNReal.ofReal (K * B * W.card) := by
            rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ← ENNReal.ofReal_mul (div_nonneg par.around_pos.le par.across_pos.le)]
            congr 1
            rw [hK]
            ring
    have hKB : 0 ≤ K * B * W.card := mul_nonneg (mul_nonneg hK0.le hBpos.le) (Nat.cast_nonneg _)
    have hfinal := hlow.trans (add_le_add le_rfl hsum)
    have h0 : OptimalConstants.Ratios.setDist (D g) K₁ K₂ = ENNReal.ofReal (TW ∅) := by
      have := hsetW ∅ (Finset.empty_subset Z)
      rwa [subtractBumps_empty] at this
    rw [h0, hsetW W hW, ← ENNReal.ofReal_add (hTW0 W hW) hKB] at hfinal
    have hreal := (ENNReal.ofReal_le_ofReal_iff (add_nonneg (hTW0 W hW) hKB)).mp hfinal
    rw [hLW ∅ (Finset.empty_subset Z), hLW W hW]
    linarith
  obtain ⟨W, hWZ, hWne, hWfix, hWcard⟩ := EndSaving.CountingCore.stableDeletion_card_ratio Z keep L B (cNew ξ par)
    β K hZne hBpos hβ0 (cNew_gt ξ par) hK0 hkeep hupper hincrement hspent
  refine ⟨W, hWZ, ⟨EndSaving.FiniteEvents.fbarV2_mono μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z W g
    hWZ hWne hFsave, PW W, TW W, hPW W hWZ, ?_⟩, ?_⟩
  · intro i hi
    have hik : i ∈ keep W := by rw [hWfix]; exact hi
    obtain ⟨_, e, he, hle⟩ := Finset.mem_filter.mp hik
    have hO : IsOpen (ball (z i) (4 * (r : ℝ))) := isOpen_ball
    have hVO : closure ((obj i).V : Set ℂ) ⊆ ball (z i) (4 * (r : ℝ)) := by
      intro x hx
      have := ((obj i).closure_V_annulus hx).2
      rw [mem_ball]; linarith
    obtain ⟨he12, he34, _, _⟩ := exc_basic hO hVO he.1
    have hinside := he.1.2.2.2.2.2.2.2.1
    have hτ : PW W e.2.1 ∈ ball (z i) (4 * (r : ℝ)) :=
      hinside _ ⟨he12, lt_of_le_of_lt he.1.2.2.1 he34⟩
    have hσ : PW W e.2.2.1 ∈ ball (z i) (4 * (r : ℝ)) :=
      hinside _ ⟨lt_of_lt_of_le he12 he.1.2.2.1, he34⟩
    refine ⟨c i, hc i (hWZ hi), e.1, e.2.1, e.2.2.1, e.2.2.2, he.1, hτ, hσ, ?_⟩
    rw [← ENNReal.ofReal_mul par.time_pos.le]
    exact hle.trans (BiLipschitz.Barrier.edist_le_internal' (D g) _ (⟨PW W e.2.1, hτ⟩, ⟨PW W e.2.2.1, hσ⟩))
  · have hcs : (cNew ξ par - β) / K = cSub ξ par := by
      rw [hK, hβ, cSub]
      have := par.across_pos; have := par.around_pos; have := cSpent_pos ξ par
      field_simp
    rw [← hcs]
    exact hWcard

 




theorem stable_subset_of_uniqueGeodesics_v2 {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h μ)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r) :
    ∀ᵐ ω ∂μ, ∀ (b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ) (Z : Finset (ℤ × ℤ)),
      EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω) →
      (∀ W ⊆ Z, W.Nonempty → ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic
          (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W (h ω))) K₁ K₂ P T) →
      ∃ Z' ⊆ Z, EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z' (h ω) ∧
        cSub ξ par * Z.card ≤ Z'.card := by
  filter_upwards [ae_sampleRegularV2 μ h hh D D' ξ Q cMid hD par pbar r obj] with ω hω
  intro b q K₁ K₂ Z hF hU
  exact stable_subset_pathwise μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z ω hω hF hU


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.ChoicesSitesV2




 

















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset Filter
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
theorem family_E_congr {Ω : Type} [MeasurableSpace Ω]
    {μ : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q cMid : ℝ} {par : EndSaving.Interfaces.Parameters ξ} {pbar : Set.Ioo (0 : ℝ) 1}
    {R : EndSaving.Interfaces.AdmissibleRadii}
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    {z z' : ℂ} {r r' : Set.Ioi (0 : ℝ)} (hr : r.1 ∈ R.radii) (hr' : r'.1 ∈ R.radii)
    (hz : z = z') (hrr : r = r') : (family z r hr).E = (family z' r' hr').E := by
  subst hz; subst hrr; rfl

 
theorem admissible_countable (R : EndSaving.Interfaces.AdmissibleRadii) :
    {r : Set.Ioi (0 : ℝ) | r.1 ∈ R.radii}.Countable := by
  have hR : R.radii.Countable := by
    have hsub : R.radii ⊆ ⋃ n : ℤ, {r | r ∈ R.radii ∧ ⌊Real.logb 8 r⌋ = n} :=
      fun r hr => mem_iUnion.mpr ⟨_, hr, rfl⟩
    refine (Set.countable_iUnion fun n => ?_).mono hsub
    apply Set.Subsingleton.countable
    intro r hr s hs
    exact admissible_floor_injective R hr.1 hs.1 (hr.2.trans hs.2.symm)
  exact hR.preimage Subtype.val_injective

 
def ckConst (k : ℕ) (cs : ℝ) : ℝ :=
  ((k - ⌈cs * k⌉₊).factorial : ℝ) / (2 ^ k * (k.factorial : ℝ))

theorem ckConst_pos (k : ℕ) (cs : ℝ) : 0 < ckConst k cs := by
  unfold ckConst
  have := Nat.factorial_pos (k - ⌈cs * k⌉₊)
  have := Nat.factorial_pos k
  positivity

 
theorem final_count (ck A x cs : ℝ) (hck : 0 < ck) (hA1 : 1 ≤ A) (hx1 : 1 ≤ x)
    (k m : ℕ) (hm : cs * k ≤ m)
    (hA : 1 / ck ≤ A ^ (cs * k)) (s : ℕ) (hs : A * x ^ (1 / 2 : ℝ) ≤ s) :
    x ^ ((cs / 2) * k) ≤ ck * (s : ℝ) ^ m := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hsq : 1 ≤ x ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  set base := A * x ^ (1 / 2 : ℝ) with hbase
  have hb1 : 1 ≤ base := by nlinarith
  have h1 : base ^ m ≤ (s : ℝ) ^ m := pow_le_pow_left₀ (by linarith) hs m
  have h2 : base ^ (cs * k) ≤ base ^ m := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hb1 hm
  have h3 : base ^ (cs * k) = A ^ (cs * k) * x ^ ((cs / 2) * k) := by
    rw [hbase, Real.mul_rpow (by linarith) (Real.rpow_nonneg hx0.le _), ← Real.rpow_mul hx0.le]
    congr 2
    ring
  have hxp : 0 < x ^ ((cs / 2) * k) := Real.rpow_pos_of_pos hx0 _
  calc x ^ ((cs / 2) * k) = ck * (1 / ck) * x ^ ((cs / 2) * k) := by field_simp
    _ ≤ ck * A ^ (cs * k) * x ^ ((cs / 2) * k) := by gcongr
    _ = ck * base ^ (cs * k) := by rw [h3]; ring
    _ ≤ ck * (s : ℝ) ^ m := by gcongr; exact h2.trans h1

 

theorem prop_choices_pathwise {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1) (R : EndSaving.Interfaces.AdmissibleRadii)
    (family : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), r.1 ∈ R.radii →
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar z r)
    (η : Set.Ioo (0 : ℝ) 1) (k : ℕ) (hk : 0 < k) (A : ℝ) (hA1 : 1 ≤ A)
    (hA2k : (2 * k : ℝ) ≤ A)
    (hAc : 1 / ckConst k (cSub ξ par) ≤ A ^ (cSub ξ par * k))
    (x₀ : ℝ) (hfib : ∀ ε : ℝ, 0 < ε → x₀ ≤ ε⁻¹ →
      A * (ε⁻¹) ^ (1 / 2 : ℝ) ≤ ((nLev η ε : ℝ) + 1) / mBox ξ Q ε - 1)
    (b : Set.Ioi (0 : ℝ)) (ε : ℝ) (hε : 0 < ε) (hεη : ε ≤ (η : ℝ) / 1000) (hεx : x₀ ≤ ε⁻¹)
    (K₁ K₂ : Set ℂ) (hK₁ : IsCompact K₁)
    (hball₁ : K₁ ⊆ ball (0 : ℂ) (2 * (b : ℝ)))
    (hsep₁₂ : ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ EndSaving.Interfaces.euclidSetDist K₁ K₂)
    (hsep₁b : ENNReal.ofReal ((η : ℝ) * (b : ℝ)) ≤ EndSaving.Interfaces.euclidSetDist K₁ (sphere (0 : ℂ) b))
    (ω : Ω)
    (hG : ω ∈ EndSaving.InterfaceV2.PrintedCountingBadEventV2 h D D' ξ Q cPlus R
      (fun z r hr => (family z r hr).E) b ⟨ε, hε⟩ K₁ K₂)
    (hreg0 : RegularAt D (ξ : ℝ) (h ω))
    (hreg : ∀ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
      SampleRegularV2 μ h D D' ξ Q cMid par pbar r
        (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) ω)
    (hU0 : ∃ P : ℝ → ℂ, ∃ T : ℝ, EndSaving.FiniteEvents.UniqueSetGeodesic (D (h ω)) K₁ K₂ P T)
    (hU : ∀ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii) (W : Finset (ℤ × ℤ)),
      EndSaving.Interfaces.Configuration r b K₁ K₂ W → W.Nonempty → ∃ P : ℝ → ℂ, ∃ T : ℝ,
        EndSaving.FiniteEvents.UniqueSetGeodesic (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r
          (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) W (h ω))) K₁ K₂ P T) :
    ∃ (r : Set.Ioi (0 : ℝ)) (hr : r.1 ∈ R.radii),
      ε ^ 2 * (b : ℝ) ≤ (r : ℝ) ∧ (r : ℝ) ≤ ε * (b : ℝ) ∧
      ∃ q : Set.Ioi (0 : ℝ), EndSaving.Interfaces.IsDyadicSize (q : ℝ) ∧
        (1 / 2) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) ≤ (q : ℝ) ∧ (q : ℝ) ≤ ε ^ ((ξ : ℝ) * (Q - 3)) ∧
        ∃ 𝓕 : Finset (Finset (ℤ × ℤ)),
          (∀ Z ∈ 𝓕, Z.card ≤ k ∧ EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂
            (fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr) Z (h ω)) ∧
          (ε⁻¹) ^ ((cSub ξ par / 2) * k) ≤ (𝓕.card : ℝ) := by
  classical
  obtain ⟨hbr, hbrc, hgap, hsize, hcover⟩ := hG
  obtain ⟨P, T, hgeod⟩ := hU0
  have hGeo := EndSaving.FiniteEvents.SetGeodesic.isGeodesic _ K₁ K₂ P T hgeod.1
  have hPc : ContinuousOn P (Icc 0 T) := hreg0.continuousOn ⟨hGeo.1, hGeo.2.1⟩
  have hb : (0 : ℝ) < b := b.property
  have hη0 : (0 : ℝ) < η := η.property.1
  have hη1 : (η : ℝ) < 1 := η.property.2
  have hε1 : ε ≤ 1 := hεη.trans (by linarith)
  obtain ⟨t, rr, ii, hrz, ℓ, hsite⟩ := covered_level_sites μ h D D' ξ Q cMid par pbar R
    family η b ε hε hεη K₁ K₂ hK₁ hball₁ hsep₁₂ hsep₁b ω hbr hsize hcover P T hPc hGeo.1
    hgeod.1.2.1 hgeod.1.2.2.1
  set J := nLev η ε with hJ
  
  set lo := (1 / 2) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) with hlo
  set hi := ε ^ ((ξ : ℝ) * (Q - 3)) with hhi
  have hlo0 : 0 < lo := by positivity
  set box : Finset (ℤ × ℤ) :=
    (Finset.Icc ⌊Real.logb 8 (ε ^ 2 * b)⌋ ⌊Real.logb 8 (ε * b)⌋) ×ˢ
      (Finset.Icc ⌈Real.logb 2 lo⌉ ⌊Real.logb 2 hi⌋) with hbox
  set f : ℕ → ℤ × ℤ := fun j => (⌊Real.logb 8 (rr j)⌋, ℓ j) with hf
  set s := Finset.range (J + 1) with hs
  have hmaps : ∀ j ∈ s, f j ∈ box := by
    intro j hj
    have hjJ : j ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    obtain ⟨_, _, hrlo, hrhi, _, _, _, _, _, hqlo, hqhi, _, _⟩ := hsite j hjJ
    rw [Finset.mem_product]
    exact ⟨floor_logb_mem_box hε hb hrlo hrhi, dyadic_exp_mem_box hlo0 hqlo hqhi⟩
  have hboxne : box.Nonempty := ⟨f 0, hmaps 0 (by simp [hs])⟩
  have hboxpos : 0 < box.card := Finset.card_pos.mpr hboxne
  set n := (J + 1) / box.card with hn
  have hcardn : box.card * n ≤ s.card := by
    rw [Finset.card_range]; exact Nat.mul_div_le (J + 1) box.card
  obtain ⟨y, _, hny⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hboxne hcardn
  set 𝒥 := s.filter (fun j => f j = y) with h𝒥
  
  have hboxle : (box.card : ℝ) ≤ mBox ξ Q ε := by
    rw [hbox, Finset.card_product, Nat.cast_mul]
    unfold mBox
    apply mul_le_mul (card_floor_box_le hε hε1 hb) (card_dyadic_box_le hlo0)
      (Nat.cast_nonneg _)
    have : 0 ≤ Real.logb 8 ε⁻¹ := Real.logb_nonneg (by norm_num) ((one_le_inv₀ hε).mpr hε1)
    linarith
  have hnreal : ((J : ℝ) + 1) / mBox ξ Q ε - 1 ≤ (n : ℝ) := by
    have hlt := Nat.lt_div_mul_add (a := J + 1) hboxpos
    have hlt' : ((J : ℝ) + 1) < (n : ℝ) * box.card + box.card := by exact_mod_cast hlt
    have hbpos : (0 : ℝ) < box.card := by exact_mod_cast hboxpos
    have h1 : ((J : ℝ) + 1) / box.card - 1 < (n : ℝ) := by
      rw [div_sub_one hbpos.ne', div_lt_iff₀ hbpos]; linarith
    have h2 : ((J : ℝ) + 1) / mBox ξ Q ε ≤ ((J : ℝ) + 1) / box.card :=
      div_le_div_of_nonneg_left (by positivity) hbpos hboxle
    linarith
  have hfibε := hfib ε hε hεx
  have hx1 : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
  have hsq1 : 1 ≤ (ε⁻¹) ^ (1 / 2 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have h𝒥card : A * (ε⁻¹) ^ (1 / 2 : ℝ) ≤ (𝒥.card : ℝ) := by
    have : (n : ℝ) ≤ 𝒥.card := by exact_mod_cast hny
    linarith
  have h𝒥ne : 𝒥.Nonempty := by
    rw [← Finset.card_pos]
    have : (1 : ℝ) ≤ 𝒥.card := by nlinarith
    exact_mod_cast this
  obtain ⟨j₀, hj₀⟩ := h𝒥ne
  have hj₀J : j₀ ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hj₀).1)
  have hmem𝒥 : ∀ j ∈ 𝒥, j ≤ J ∧ f j = f j₀ := by
    intro j hj
    have h1 := Finset.mem_filter.mp hj
    have h2 := Finset.mem_filter.mp hj₀
    exact ⟨Nat.lt_succ_iff.mp (Finset.mem_range.mp h1.1), h1.2.trans h2.2.symm⟩
  obtain ⟨_, hr₀, hrlo₀, hrhi₀, _, _, _, _, _, hqlo₀, hqhi₀, _, _⟩ := hsite j₀ hj₀J
  set r := rr j₀ with hrdef
  have hsame : ∀ j ∈ 𝒥, rr j = r ∧ ℓ j = ℓ j₀ := by
    intro j hj
    obtain ⟨hjJ, hfj⟩ := hmem𝒥 j hj
    obtain ⟨_, hrj, _, _, _, _, _, _, _, _, _, _, _⟩ := hsite j hjJ
    have hfl := congrArg Prod.fst hfj
    have hℓ := congrArg Prod.snd hfj
    simp only [hf] at hfl hℓ
    exact ⟨Subtype.ext (admissible_floor_injective R hrj hr₀ hfl), hℓ⟩
  set q : Set.Ioi (0 : ℝ) := ⟨(2 : ℝ) ^ (ℓ j₀), Set.mem_Ioi.mpr (zpow_pos (by norm_num) _)⟩
    with hqdef
  set obj := fun i => family (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r hr₀ with hobj
  
  set S := 𝒥.image ii with hS
  have hw : ∀ j ∈ 𝒥, LQGMetric.GM.gridPt (((rr j : ℝ)) / 100) (ii j) =
      LQGMetric.GM.gridPt ((r : ℝ) / 100) (ii j) := by
    intro j hj; rw [(hsame j hj).1]
  have hr0 : (0 : ℝ) < r := r.property
  have hinj : Set.InjOn ii 𝒥 := by
    intro j hj j' hj' hjj
    by_contra hne
    obtain ⟨hjJ, _⟩ := hmem𝒥 j hj
    obtain ⟨hj'J, _⟩ := hmem𝒥 j' hj'
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hdisj⟩ := hsite j hjJ
    have hd := hdisj j' hj'J hne
    rw [hw j hj, hw j' hj', hjj, (hsame j hj).1, (hsame j' hj').1] at hd
    have hc : LQGMetric.GM.gridPt ((r : ℝ) / 100) (ii j') ∈
        ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) (ii j')) (4 * (r : ℝ)) :=
      mem_ball_self (by positivity)
    exact Set.disjoint_left.mp hd hc hc
  have hScard : S.card = 𝒥.card := Finset.card_image_of_injOn hinj
  have hpre : ∀ i ∈ S, ∃ j ∈ 𝒥, ii j = i := fun i hi => Finset.mem_image.mp hi
  choose! jOf hjOf hiijOf using hpre
  
  have hsiteS : ∀ i ∈ S,
      t (jOf i) ∈ Icc 0 T ∧
      P (t (jOf i)) ∈ ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r ∧
      h ω ∈ (obj i).E ∧
      IsCircleAverage (h ω) r (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (hrz (jOf i)) ∧
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q (hrz (jOf i)) hbr ∧
      Disjoint (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
        (K₁ ∪ K₂ ∪ sphere (0 : ℂ) b) := by
    intro i hi
    set j := jOf i
    have hj := hjOf i hi
    have hji : ii j = i := hiijOf i hi
    obtain ⟨hjJ, _⟩ := hmem𝒥 j hj
    obtain ⟨hrj, hℓj⟩ := hsame j hj
    obtain ⟨htj, _, _, _, hPw, ⟨hrr', hE⟩, hcirc, hb1, hb2, _, _, hobst, _⟩ := hsite j hjJ
    have hwi : LQGMetric.GM.gridPt (((rr j : ℝ)) / 100) (ii j) =
        LQGMetric.GM.gridPt ((r : ℝ) / 100) i := by rw [hw j hj, hji]
    rw [hwi] at hPw hobst hE hcirc
    refine ⟨htj, ?_, ?_, ?_, ?_, ?_⟩
    · have : ((rr j : ℝ)) / 25 ≤ r := by rw [hrj]; linarith
      exact ball_subset_ball this hPw
    · simp only [hobj]
      rw [family_E_congr family hrr' hr₀ rfl hrj] at hE
      exact hE
    · rw [hrj] at hcirc; exact hcirc
    · rw [← hrj]
      simp only [scaleN, scaleB, oneIoi, one_mul] at hb1 hb2
      rw [hℓj] at hb1 hb2
      constructor
      · simp only [hqdef]; nlinarith
      · simp only [hqdef]; nlinarith
    · rw [hrj] at hobst; exact hobst
  have hdisjS : ∀ i ∈ S, ∀ i' ∈ S, i ≠ i' →
      Disjoint (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) (4 * (r : ℝ)))
        (ball (LQGMetric.GM.gridPt ((r : ℝ) / 100) i') (4 * (r : ℝ))) := by
    intro i hi i' hi' hii'
    have hjne : jOf i ≠ jOf i' := by
      intro heq; apply hii'; rw [← hiijOf i hi, ← hiijOf i' hi', heq]
    obtain ⟨hjJ, _⟩ := hmem𝒥 _ (hjOf i hi)
    obtain ⟨hj'J, _⟩ := hmem𝒥 _ (hjOf i' hi')
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hd⟩ := hsite (jOf i) hjJ
    have h := hd (jOf i') hj'J hjne
    rw [hw _ (hjOf i hi), hw _ (hjOf i' hi'), hiijOf i hi, hiijOf i' hi',
      (hsame _ (hjOf i hi)).1, (hsame _ (hjOf i' hi')).1] at h
    exact h
  have hconfigS : ∀ Z ⊆ S, EndSaving.Interfaces.Configuration r b K₁ K₂ Z := fun Z hZ =>
    ⟨fun i hi i' hi' hii' => hdisjS i (hZ hi) i' (hZ hi') hii',
      fun i hi => (hsiteS i (hZ hi)).2.2.2.2.2⟩
  
  have hgapq : OptimalConstants.Ratios.setDist (D' (h ω)) K₁ K₂ ≥ cPlus * OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ -
      ENNReal.ofReal ((q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) := by
    refine le_trans (tsub_le_tsub_left ?_ _) hgap
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 ≤ (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) := by
      have := Real.rpow_pos_of_pos hb ((ξ : ℝ) * Q); positivity
    have : (1 / 2 : ℝ) * ε ^ (2 * (ξ : ℝ) * (Q + 3)) ≤ (q : ℝ) := hqlo₀
    calc (1 / 2 : ℝ) * ((⟨ε, hε⟩ : Set.Ioi (0 : ℝ)) : ℝ) ^ (2 * (ξ : ℝ) * (Q + 3)) *
          (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)
        = ((1 / 2 : ℝ) * ε ^ (2 * (ξ : ℝ) * (Q + 3))) *
          ((b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) := by simp only; ring
      _ ≤ (q : ℝ) * ((b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)) := by gcongr
      _ = (q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr) := by ring
  
  have hFbar : ∀ Z ⊆ S, Z.Nonempty →
      EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z (h ω) := by
    intro Z hZ hZne
    refine ⟨hZne, hconfigS Z hZ, hbr, hbrc, hgapq, ?_, P, T, hgeod, ?_⟩
    · intro i hi
      obtain ⟨_, _, hE, hcirc, hbin, _⟩ := hsiteS i (hZ hi)
      exact ⟨hE, hrz (jOf i), hcirc, hbin⟩
    · intro i hi
      obtain ⟨htj, hPb, _⟩ := hsiteS i (hZ hi)
      exact ⟨t (jOf i), htj, hPb⟩
  
  have hstable : ∀ A' ∈ S.powersetCard k, ∃ Z' ⊆ A',
      EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z' (h ω) ∧
        cSub ξ par * A'.card ≤ Z'.card := by
    intro A' hA'
    obtain ⟨hA'S, hA'k⟩ := Finset.mem_powersetCard.mp hA'
    have hA'ne : A'.Nonempty := by rw [← Finset.card_pos, hA'k]; exact hk
    exact stable_subset_pathwise μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj A' ω
      (hreg r hr₀) (hFbar A' hA'S hA'ne)
      (fun W hW hWne => hU r hr₀ W (hconfigS W (hW.trans hA'S)) hWne)
  set Φ : Finset (ℤ × ℤ) → Finset (ℤ × ℤ) := fun A' =>
    if hA' : A' ∈ S.powersetCard k then Classical.choose (hstable A' hA') else A' with hΦ
  have hΦspec : ∀ A' ∈ S.powersetCard k, Φ A' ⊆ A' ∧
      EndSaving.FiniteEvents.FV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj (Φ A') (h ω) ∧
        cSub ξ par * A'.card ≤ (Φ A').card := by
    intro A' hA'
    simp only [hΦ, hA', ↓reduceDIte]
    exact Classical.choose_spec (hstable A' hA')
  set m := ⌈cSub ξ par * k⌉₊ with hm
  have hcs := cSub_pos ξ par
  have hcs1 := cSub_lt_one ξ par
  have hmk : m ≤ k := by
    apply Nat.ceil_le.mpr
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have hcardm : ∀ A' ∈ S.powersetCard k, m ≤ (Φ A').card := by
    intro A' hA'
    apply Nat.ceil_le.mpr
    have h := (hΦspec A' hA').2.2
    rw [(Finset.mem_powersetCard.mp hA').2] at h
    exact h
  have hk2 : 2 * k ≤ S.card := by
    rw [hScard]
    have : (2 * k : ℝ) ≤ 𝒥.card := by nlinarith
    exact_mod_cast this
  have himage := EndSaving.ChoicesCore.stableSubset_image_poly_m S k m Φ hk2 hk hmk
    (fun A' hA' => (hΦspec A' hA').1) hcardm
  have hfinal := final_count (ckConst k (cSub ξ par)) A ε⁻¹ (cSub ξ par)
    (ckConst_pos k (cSub ξ par)) hA1 hx1 k m (Nat.le_ceil _) hAc S.card
    (by rw [hScard]; exact h𝒥card)
  refine ⟨r, hr₀, hrlo₀, hrhi₀, q, ⟨ℓ j₀, rfl⟩, hqlo₀, hqhi₀, (S.powersetCard k).image Φ, ?_,
    hfinal.trans ?_⟩
  · intro Z hZ
    obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hZ
    obtain ⟨hsub, hFV, _⟩ := hΦspec A' hA'
    exact ⟨(Finset.card_le_card hsub).trans (Finset.mem_powersetCard.mp hA').2.le, hFV⟩
  · simpa only [ckConst, hm] using himage


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

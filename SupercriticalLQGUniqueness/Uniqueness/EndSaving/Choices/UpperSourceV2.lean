import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices.UpperV2




 










set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Finset LQGMetric.MetricGeometry
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

open LQGMetric (DistC TestC)

 
def cNew (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : ℝ :=
  par.Cacross - 4 * Real.exp (-(ξ : ℝ) * par.Cmax) * par.Ctube

 
theorem cNew_gt (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) :
    2 * par.Caround * par.Ctime / par.Cacross < cNew ξ par := by
  have h := par.strict_slack
  have heq : 2 * par.Caround * par.Ctime / par.Cacross =
      (2 * par.Caround / par.Cacross) * par.Ctime := by ring
  rw [heq]
  exact h

theorem cNew_pos (ξ : Set.Ioi (0 : ℝ)) (par : EndSaving.Interfaces.Parameters ξ) : 0 < cNew ξ par := by
  have h := cNew_gt ξ par
  have hpos : 0 < 2 * par.Caround * par.Ctime / par.Cacross := by
    have := par.around_pos
    have := par.time_pos
    have := par.across_pos
    positivity
  linarith

 
def scaleB (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (b q : Set.Ioi (0 : ℝ)) (hbr : ℝ) : ℝ :=
  (q : ℝ) * (b : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hbr)

theorem scaleB_pos (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (b q : Set.Ioi (0 : ℝ)) (hbr : ℝ) :
    0 < scaleB ξ Q b q hbr := by
  unfold scaleB
  have hq : (0 : ℝ) < q := q.property
  have hb : (0 : ℝ) < b := b.property
  have := Real.rpow_pos_of_pos hb ((ξ : ℝ) * Q)
  positivity

 
def scaleN (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (r : Set.Ioi (0 : ℝ)) (hrz : ℝ) : ℝ :=
  (r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * hrz)

theorem scaleN_pos (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (r : Set.Ioi (0 : ℝ)) (hrz : ℝ) :
    0 < scaleN ξ Q r hrz := by
  unfold scaleN
  have hr : (0 : ℝ) < r := r.property
  have := Real.rpow_pos_of_pos hr ((ξ : ℝ) * Q)
  positivity

 
theorem bumpSum_nonneg {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (W : Finset (ℤ × ℤ)) (x : ℂ) :
    0 ≤ EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W x := by
  unfold EndSaving.FiniteEvents.bumpSumV2
  rw [show ((∑ i ∈ W, (obj i).f : TestC) : ℂ → ℝ) x = ∑ i ∈ W, (obj i).f x by
    induction W using Finset.induction_on with
    | empty => simp
    | insert j W hj ih =>
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        change ((obj j).f + ∑ i ∈ W, (obj i).f : TestC) x = _
        rw [← ih]
        rfl]
  exact Finset.sum_nonneg fun i _ => (obj i).f_nonneg x

 
theorem bumpSum_apply {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (W : Finset (ℤ × ℤ)) (x : ℂ) :
    EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W x = ∑ i ∈ W, (obj i).f x := by
  unfold EndSaving.FiniteEvents.bumpSumV2
  induction W using Finset.induction_on with
  | empty => rfl
  | insert j W hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      change ((obj j).f + ∑ i ∈ W, (obj i).f : TestC) x = _
      rw [← ih]
      rfl

 
theorem subtractBumps_eq_addFun {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r : Set.Ioi (0 : ℝ))
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (W : Finset (ℤ × ℤ)) (g : DistC) :
    EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj W g =
      LQGMetric.addFun g
        (LQGMetric.testCont (-EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj W)) := by
  unfold EndSaving.FiniteEvents.subtractBumpsV2
  exact subTest_eq_addFun g _

 
theorem upper_fbarV2_of_regular {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (h : Ω → DistC) (D D' : DistC → LSCMetric)
    (ξ : Set.Ioi (0 : ℝ)) (Q cMid : ℝ) (cPlus : ℝ≥0∞)
    (par : EndSaving.Interfaces.Parameters ξ) (pbar : Set.Ioo (0 : ℝ) 1)
    (r b q : Set.Ioi (0 : ℝ)) (K₁ K₂ : Set ℂ)
    (obj : ∀ i : ℤ × ℤ,
      EndSaving.InterfaceV2.ObjectAtV2 μ h D D' ξ Q cMid par pbar
        (LQGMetric.GM.gridPt ((r : ℝ) / 100) i) r)
    (Z : Finset (ℤ × ℤ)) (g : DistC) (hreg : RegularAt D (ξ : ℝ) g)
    (hF : EndSaving.FiniteEvents.FbarV2 μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z g)
    (hbr : ℝ) (hb : IsCircleAverage g b 0 hbr) :
    OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g)) K₁ K₂ +
        ENNReal.ofReal (cNew ξ par * scaleB ξ Q b q hbr * Z.card) ≤
      OptimalConstants.Ratios.setDist (D g) K₁ K₂ := by
  rcases hF with ⟨_, hconfig, hbr₀, havg₀, _, hlocal, P, T, hgeod, hhit⟩
  have hbreq : hbr₀ = hbr := isCircleAverage_unique havg₀ hb
  subst hbreq
  set Dh := D g with hDh
  set Dm := D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z g) with hDm
  set f := EndSaving.FiniteEvents.bumpSumV2 μ h D D' ξ Q cMid par pbar r obj Z with hf
  set F : C(ℂ, ℝ) := LQGMetric.testCont (-f) with hFdef
  set z : ℤ × ℤ → ℂ := fun i => LQGMetric.GM.gridPt ((r : ℝ) / 100) i with hz
  have hr0 : (0 : ℝ) < r := r.property
  have hWeyl : ∀ p : ℂ × ℂ, Dm p = weylScale ξ F Dh p := by
    intro p
    rw [hreg.weyl F, hDm, subtractBumps_eq_addFun]
  have hFval : ∀ x : ℂ, F x = -(∑ i ∈ Z, (obj i).f x) := by
    intro x
    rw [hFdef, testCont_apply]
    change -(f x) = _
    rw [hf, bumpSum_apply]
  have hFnonpos : ∀ x : ℂ, F x ≤ 0 := by
    intro x
    rw [hFval]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => (obj i).f_nonneg x)
  have hFU : ∀ i ∈ Z, ∀ x ∈ ((obj i).U : Set ℂ), F x ≤ -par.Cmax := by
    intro i hi x hx
    rw [hFval]
    apply neg_le_neg
    rw [← (obj i).f_on_U x hx]
    exact Finset.single_le_sum (fun j _ => (obj j).f_nonneg x) hi
  have hG : IsGeodesicCurve (Dh.pt ∘ P) 0 T := EndSaving.FiniteEvents.SetGeodesic.isGeodesic Dh K₁ K₂ P T hgeod.1
  have hu : HasUnitSpeedOn (Dh.pt ∘ P) (Icc 0 T) := hgeod.1.1.2.1
  
  have hsite : ∀ i ∈ Z, ∃ hrz : ℝ, ∃ π : ℝ → ℂ, ∃ α β : ℝ,
      IsCircleAverage g r (z i) hrz ∧
      EndSaving.FiniteEvents.LocalSizeBin ξ Q r b q hrz hbr₀ ∧
      Dh.IsCurve π α β ∧ (∀ t ∈ Icc α β, π t ∈ ((obj i).U : Set ℂ)) ∧
      LQGMetric.Disconnects (π '' Icc α β) (sphere (z i) r) (sphere (z i) (3 * r)) ∧
      Dh.len π α β ≤ ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r hrz) ∧
      ENNReal.ofReal par.Cacross * ENNReal.ofReal (scaleN ξ Q r hrz) ≤
        OptimalConstants.Ratios.setDist Dh ((obj i).V : Set ℂ) (sphere (z i) r ∪ sphere (z i) (3 * r)) := by
    intro i hi
    obtain ⟨hE, hrz, hc, hbin⟩ := hlocal i hi
    obtain ⟨hcross, _, hsep⟩ := (obj i).E_bounds g hE hrz hc
    obtain ⟨π, α, β, hπ, hπU, hπsep, hπlen⟩ := hsep
    exact ⟨hrz, π, α, β, hc, hbin, hπ, hπU, hπsep, hπlen, hcross⟩
  choose! hrz π α β hc hbin hπ hπU hπsep hπlen hcross using hsite
  have hout : ∀ i ∈ Z, ∀ x ∈ K₁ ∪ K₂, x ∉ ball (z i) (4 * r) := by
    intro i hi x hx hball
    exact Set.disjoint_left.mp (hconfig.2 i hi) hball (Or.inl hx)
  have hmain := upper_pathwise Dh Dm ξ par.Cmax ξ.property.le F hreg.forget
    (fun hQ => hreg.continuousOn hQ) hWeyl hFnonpos P hG hu Z z r hr0
    (fun i hi j hj hij => hconfig.1 i hi j hj hij)
    (fun i hi => hout i hi (P 0) (Or.inl hgeod.1.2.1))
    (fun i hi => hout i hi (P T) (Or.inr hgeod.1.2.2.1))
    (fun i hi => hhit i hi)
    (fun i => ((obj i).V : Set ℂ)) π α β hπ
    (fun i hi => by
      rintro _ ⟨t, ht, rfl⟩
      exact (subset_closure.trans (obj i).closure_U_V) (hπU i hi t ht))
    (fun i hi => by
      rintro _ ⟨t, ht, rfl⟩
      exact ((obj i).U_annular).1 (hπU i hi t ht))
    hπsep
    (fun i hi u hu => hFU i hi _ (hπU i hi u hu))
    (fun i => ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i)))
    (fun i => ENNReal.ofReal par.Cacross * ENNReal.ofReal (scaleN ξ Q r (hrz i)))
    hπlen hcross
  
  set B := scaleB ξ Q b q hbr₀ with hB
  set e := Real.exp (-((ξ : ℝ) * par.Cmax)) with he
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have hcn := cNew_pos ξ par
  have hterm : ∀ i ∈ Z, ENNReal.ofReal (cNew ξ par * B) +
      ENNReal.ofReal e * (ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i))) ≤
      ENNReal.ofReal par.Cacross * ENNReal.ofReal (scaleN ξ Q r (hrz i)) := by
    intro i hi
    have hn := scaleN_pos ξ Q r (hrz i)
    have hBn : B ≤ scaleN ξ Q r (hrz i) := (hbin i hi).1
    have hct := par.tube_pos.le
    rw [← ENNReal.ofReal_mul hct, ← ENNReal.ofReal_mul he0,
      ← ENNReal.ofReal_add (mul_nonneg hcn.le (scaleB_pos ξ Q b q hbr₀).le)
        (mul_nonneg he0 (mul_nonneg hct hn.le)),
      ← ENNReal.ofReal_mul par.across_pos.le]
    apply ENNReal.ofReal_le_ofReal
    have he' : e = Real.exp (-(ξ : ℝ) * par.Cmax) := by rw [he, neg_mul]
    have hcnew : cNew ξ par = par.Cacross - 4 * e * par.Ctube := by
      rw [cNew, he']
    have h1 : cNew ξ par * B ≤ cNew ξ par * scaleN ξ Q r (hrz i) :=
      mul_le_mul_of_nonneg_left hBn hcn.le
    have h2 : e * (par.Ctube * scaleN ξ Q r (hrz i)) ≥ 0 := by positivity
    rw [hcnew] at h1 ⊢
    nlinarith [h1, h2]
  have hfinR : ∑ i ∈ Z, ENNReal.ofReal e *
      (ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i))) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  have hsumB : ENNReal.ofReal (cNew ξ par * B * Z.card) =
      ∑ _i ∈ Z, ENNReal.ofReal (cNew ξ par * B) := by
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul
      (mul_nonneg hcn.le (scaleB_pos ξ Q b q hbr₀).le), ENNReal.ofReal_natCast, mul_comm]
  have hsetDm : OptimalConstants.Ratios.setDist Dm K₁ K₂ ≤ Dm (P 0, P T) :=
    iInf₂_le_of_le (P 0) hgeod.1.2.1 (iInf₂_le (P T) hgeod.1.2.2.1)
  have hDhT : OptimalConstants.Ratios.setDist Dh K₁ K₂ = ENNReal.ofReal T := hgeod.1.2.2.2.symm
  rw [hDhT]
  have key : OptimalConstants.Ratios.setDist Dm K₁ K₂ + ENNReal.ofReal (cNew ξ par * B * Z.card) +
      ∑ i ∈ Z, ENNReal.ofReal e *
        (ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i))) ≤
      ENNReal.ofReal T + ∑ i ∈ Z, ENNReal.ofReal e *
        (ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i))) := by
    calc OptimalConstants.Ratios.setDist Dm K₁ K₂ + ENNReal.ofReal (cNew ξ par * B * Z.card) +
          ∑ i ∈ Z, ENNReal.ofReal e *
            (ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i)))
        = OptimalConstants.Ratios.setDist Dm K₁ K₂ + ∑ i ∈ Z, (ENNReal.ofReal (cNew ξ par * B) +
            ENNReal.ofReal e *
              (ENNReal.ofReal par.Ctube * ENNReal.ofReal (scaleN ξ Q r (hrz i)))) := by
          rw [hsumB, Finset.sum_add_distrib, add_assoc]
      _ ≤ Dm (P 0, P T) + ∑ i ∈ Z,
            ENNReal.ofReal par.Cacross * ENNReal.ofReal (scaleN ξ Q r (hrz i)) := by
          gcongr with i hi
          exact hterm i hi
      _ ≤ _ := hmain
  exact (ENNReal.add_le_add_iff_right hfinR).mp key

 



theorem lem_new_dist_upper_v2 {Ω : Type} [MeasurableSpace Ω]
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
      ∀ hbr : ℝ, IsCircleAverage (h ω) b 0 hbr →
        OptimalConstants.Ratios.setDist (D (EndSaving.FiniteEvents.subtractBumpsV2 μ h D D' ξ Q cMid par pbar r obj Z (h ω)))
            K₁ K₂ + ENNReal.ofReal (cNew ξ par * scaleB ξ Q b q hbr * Z.card) ≤
          OptimalConstants.Ratios.setDist (D (h ω)) K₁ K₂ := by
  filter_upwards [ae_regularAt_self hD μ h hh] with ω hreg
  intro b q K₁ K₂ Z hF hbr hb
  exact upper_fbarV2_of_regular μ h D D' ξ Q cMid cPlus par pbar r b q K₁ K₂ obj Z
    (h ω) hreg hF hbr hb


end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Choices

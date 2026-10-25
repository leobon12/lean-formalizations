import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.LawTransport
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Cor




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 

theorem eVariationOn_le_of_edist_le {α : Type*} [LinearOrder α] {E F : Type*}
    [PseudoEMetricSpace E] [PseudoEMetricSpace F] {f : α → E} {g : α → F} {s : Set α}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ edist (g x) (g y)) :
    eVariationOn f s ≤ eVariationOn g s := by
  refine iSup_mono fun p => Finset.sum_le_sum fun i _ => ?_
  exact h _ (p.2.2.2 _) _ (p.2.2.2 _)

 

theorem dist_le_intExt (D : LSCMetric) (U : Set ℂ) (x y : ℂ) : D (x, y) ≤ intExt D U x y := by
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun _ =>
    le_iInf fun ha => le_iInf fun hb => ?_
  rw [← ha, ← hb]
  exact LSCMetric.apply_le_len D P hP.1

theorem intExt_mono_set {D : LSCMetric} {U V : Set ℂ} (hUV : U ⊆ V) (x y : ℂ) :
    intExt D V x y ≤ intExt D U x y := by
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hU =>
    le_iInf fun ha => le_iInf fun hb => ?_
  exact iInf_le_of_le P (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
    (iInf_le_of_le (fun t ht => hUV (hU t ht)) (iInf_le_of_le ha (iInf_le _ hb))))))

 
theorem intExt_le_len_sub {D : LSCMetric} {U : Set ℂ} {P : ℝ → ℂ} {s t a b : ℝ}
    (hP : D.IsCurve P s t) (hU : ∀ τ ∈ Icc s t, P τ ∈ U) (hsa : s ≤ a) (hab : a ≤ b)
    (hbt : b ≤ t) : intExt D U (P a) (P b) ≤ D.len P a b := by
  have hc : D.IsCurve P a b := ⟨hab, hP.2.mono (Icc_subset_Icc hsa hbt)⟩
  exact intExt_le_len hc fun τ hτ => hU τ ⟨hsa.trans hτ.1, hτ.2.trans hbt⟩

theorem intExt_eq_of_internal_eq {D₁ D₂ : LSCMetric} {U : Set ℂ}
    (h : D₁.internal U = D₂.internal U) (x y : ℂ) : intExt D₁ U x y = intExt D₂ U x y := by
  by_cases hx : x ∈ U
  · by_cases hy : y ∈ U
    · exact congrFun h (⟨x, hx⟩, ⟨y, hy⟩)
    · rw [intExt_eq_top_of_not_mem_right _ hy, intExt_eq_top_of_not_mem_right _ hy]
  · rw [intExt_eq_top_of_not_mem_left _ hx, intExt_eq_top_of_not_mem_left _ hx]

theorem internal_eq_of_intExt_eq {D₁ D₂ : LSCMetric} {U : Set ℂ}
    (h : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) : D₁.internal U = D₂.internal U := by
  funext p
  exact h p.1 p.2

 

 

theorem curve_len_transfer {D₁ D₂ : LSCMetric} {U : Set ℂ}
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) {P : ℝ → ℂ} {s t : ℝ}
    (hP : D₁.IsCurve P s t) (hU : ∀ τ ∈ Icc s t, P τ ∈ U) (hfin : D₁.len P s t ≠ ⊤) :
    D₂.IsCurve P s t ∧ D₂.len P s t ≤ D₁.len P s t := by
  have hst : s ≤ t := hP.1
  set f₁ : ℝ → D₁.Space := D₁.pt ∘ P with hf₁
  have hBV : BoundedVariationOn f₁ (Icc s t) := hfin
  have hsmem : s ∈ Icc s t := ⟨le_rfl, hst⟩
  set φ : ℝ → ℝ := variationOnFromTo f₁ (Icc s t) s with hφ
  have hφmono : MonotoneOn φ (Icc s t) :=
    variationOnFromTo.monotoneOn hBV.locallyBoundedVariationOn hsmem
  have hφcont : ContinuousOn φ (Icc s t) := fun x hx =>
    (hBV.continuousWithinAt_variationOnFromTo_iff hsmem hx).2 (hP.2 x hx)
  
  have hsub : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, a ≤ b →
      D₁.len P a b = ENNReal.ofReal (φ b - φ a) := by
    intro a ha b hb hab
    have hadd := variationOnFromTo.add hBV.locallyBoundedVariationOn hsmem ha hb
    have hab' : variationOnFromTo f₁ (Icc s t) a b = φ b - φ a := by
      change φ a + variationOnFromTo f₁ (Icc s t) a b = φ b at hadd
      linarith
    rw [← hab', variationOnFromTo.eq_of_le f₁ (Icc s t) hab,
      inter_eq_right.mpr (Icc_subset_Icc ha.1 hb.2)]
    have hle : eVariationOn f₁ (Icc a b) ≤ eVariationOn f₁ (Icc s t) :=
      eVariationOn.mono f₁ (Icc_subset_Icc ha.1 hb.2)
    exact (ENNReal.ofReal_toReal (ne_top_of_le_ne_top hfin hle)).symm
  
  have hdom : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t,
      edist ((D₂.pt ∘ P) a) ((D₂.pt ∘ P) b) ≤ edist (φ a) (φ b) := by
    have key : ∀ a ∈ Icc s t, ∀ b ∈ Icc s t, a ≤ b →
        edist ((D₂.pt ∘ P) a) ((D₂.pt ∘ P) b) ≤ edist (φ a) (φ b) := by
      intro a ha b hb hab
      calc
        edist ((D₂.pt ∘ P) a) ((D₂.pt ∘ P) b) = D₂ (P a, P b) := rfl
        _ ≤ intExt D₂ U (P a) (P b) := dist_le_intExt D₂ U _ _
        _ = intExt D₁ U (P a) (P b) := (hI _ _).symm
        _ ≤ D₁.len P a b := intExt_le_len_sub hP hU ha.1 hab hb.2
        _ = ENNReal.ofReal (φ b - φ a) := hsub a ha b hb hab
        _ = edist (φ a) (φ b) := by
          rw [edist_dist, Real.dist_eq, abs_sub_comm,
            abs_of_nonneg (sub_nonneg.mpr (hφmono ha hb hab))]
    intro a ha b hb
    rcases le_total a b with hab | hba
    · exact key a ha b hb hab
    · rw [edist_comm, edist_comm (φ a)]
      exact key b hb a ha hba
  refine ⟨⟨hst, ?_⟩, ?_⟩
  · intro x hx
    have hφx := tendsto_iff_edist_tendsto_0.mp (hφcont x hx)
    apply tendsto_iff_edist_tendsto_0.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hφx
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hdom y hy x hx
  · have h1 : eVariationOn (D₂.pt ∘ P) (Icc s t) ≤ eVariationOn φ (Icc s t) :=
      eVariationOn_le_of_edist_le hdom
    have h2 : eVariationOn φ (Icc s t) = ENNReal.ofReal (φ t - φ s) := by
      have h := hφmono.eVariationOn_eq hsmem ⟨hst, le_rfl⟩
      rwa [inter_eq_left.mpr (subset_refl _)] at h
    calc
      D₂.len P s t = eVariationOn (D₂.pt ∘ P) (Icc s t) := rfl
      _ ≤ ENNReal.ofReal (φ t - φ s) := h1.trans h2.le
      _ = D₁.len P s t := (hsub s hsmem t ⟨hst, le_rfl⟩ hst).symm

theorem curve_len_transfer_eq {D₁ D₂ : LSCMetric} {U : Set ℂ}
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) {P : ℝ → ℂ} {s t : ℝ}
    (hP : D₁.IsCurve P s t) (hU : ∀ τ ∈ Icc s t, P τ ∈ U) (hfin : D₁.len P s t ≠ ⊤) :
    D₂.IsCurve P s t ∧ D₂.len P s t = D₁.len P s t := by
  obtain ⟨hc₂, hle⟩ := curve_len_transfer hI hP hU hfin
  have hfin₂ : D₂.len P s t ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  obtain ⟨-, hge⟩ := curve_len_transfer (fun x y => (hI x y).symm) hc₂ hU hfin₂
  exact ⟨hc₂, le_antisymm hle hge⟩

 

theorem intExt_le_transfer {D₁ D₂ : LSCMetric} {U Y : Set ℂ} (hYU : Y ⊆ U)
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) (x y : ℂ) :
    intExt D₂ Y x y ≤ intExt D₁ Y x y := by
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hY => le_iInf fun ha => le_iInf fun hb => ?_
  by_cases hfin : D₁.len P a b = ⊤
  · rw [hfin]
    exact le_top
  · obtain ⟨hc₂, hlen⟩ := curve_len_transfer_eq hI hP (fun τ hτ => hYU (hY τ hτ)) hfin
    rw [← hlen, ← ha, ← hb]
    exact intExt_le_len hc₂ hY

theorem intExt_transfer {D₁ D₂ : LSCMetric} {U Y : Set ℂ} (hYU : Y ⊆ U)
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) (x y : ℂ) :
    intExt D₁ Y x y = intExt D₂ Y x y :=
  le_antisymm (intExt_le_transfer hYU (fun x y => (hI x y).symm) x y)
    (intExt_le_transfer hYU hI x y)

theorem internal_transfer {D₁ D₂ : LSCMetric} {U Y : Set ℂ} (hYU : Y ⊆ U)
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) : D₁.internal Y = D₂.internal Y :=
  internal_eq_of_intExt_eq (intExt_transfer hYU hI)

 

 
theorem subset_of_preconnected_avoid {V S T : Set ℂ} (hV : IsOpen V)
    (hcl : closure V ⊆ V ∪ S) (hT : IsPreconnected T) (hTS : ∀ y ∈ T, y ∉ S)
    (hTV : (T ∩ V).Nonempty) : T ⊆ V := by
  refine hT.subset_of_closure_inter_subset hV hTV ?_
  rintro y ⟨hyc, hyT⟩
  rcases hcl hyc with hyV | hyS
  · exact hyV
  · exact absurd hyS (hTS y hyT)

 


theorem iInf_intExt_le {D : LSCMetric} (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ), D.IsCurve γ a b →
      ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) {U V S : Set ℂ} (hV : IsOpen V) (hcl : closure V ⊆ V ∪ S)
    (hS : IsClosed S) (hVSU : V ∪ S ⊆ U) {x y : ℂ} (hx : x ∈ V) (hy : y ∈ S) :
    ⨅ y' ∈ S, intExt D U x y' ≤ D (x, y) := by
  by_cases htop : D (x, y) = ⊤
  · rw [htop]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨P, a, b, hP, hPa, hPb, hlen⟩ :=
    hL x y (lt_top_iff_ne_top.mpr htop) ε (by exact_mod_cast hε)
  have hab : a ≤ b := hP.1
  have hPc : ContinuousOn P (Icc a b) := hcont P a b hP
  set T : Set ℝ := Icc a b ∩ P ⁻¹' S with hTdef
  have hTc : IsClosed T := hPc.preimage_isClosed_of_isClosed isClosed_Icc hS
  have hTne : T.Nonempty := ⟨b, ⟨hab, le_rfl⟩, by rw [mem_preimage, hPb]; exact hy⟩
  have hTbdd : BddBelow T := ⟨a, fun t ht => ht.1.1⟩
  set τ := sInf T with hτdef
  have hτT : τ ∈ T := hTc.csInf_mem hTne hTbdd
  have haτ : a ≤ τ := hτT.1.1
  have hτb : τ ≤ b := hτT.1.2
  have hbefore : ∀ t ∈ Ico a τ, P t ∉ S := by
    intro t ht hPt
    have : τ ≤ t := csInf_le hTbdd ⟨⟨ht.1, ht.2.le.trans hτb⟩, hPt⟩
    exact (not_le_of_gt ht.2) this
  have hinV : ∀ t ∈ Ico a τ, P t ∈ V := by
    by_cases haτ' : a = τ
    · intro t ht
      exact absurd (haτ' ▸ ht.2) (not_lt_of_ge ht.1)
    have hpre : IsPreconnected (P '' Ico a τ) :=
      isPreconnected_Ico.image P (hPc.mono (Ico_subset_Icc_self.trans
        (Icc_subset_Icc le_rfl hτb)))
    have hsub := subset_of_preconnected_avoid hV hcl hpre
      (by rintro _ ⟨t, ht, rfl⟩; exact hbefore t ht)
      ⟨P a, ⟨a, ⟨le_rfl, lt_of_le_of_ne haτ haτ'⟩, rfl⟩, by rw [hPa]; exact hx⟩
    exact fun t ht => hsub ⟨t, ht, rfl⟩
  have hinU : ∀ t ∈ Icc a τ, P t ∈ U := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with htτ | htτ
    · exact hVSU (Or.inr (htτ ▸ hτT.2))
    · exact hVSU (Or.inl (hinV t ⟨ht.1, htτ⟩))
  have hcurve : D.IsCurve P a τ := ⟨haτ, hP.2.mono (Icc_subset_Icc le_rfl hτb)⟩
  have h1 : intExt D U (P a) (P τ) ≤ D.len P a τ := intExt_le_len hcurve hinU
  have h2 : D.len P a τ ≤ D.len P a b :=
    eVariationOn.mono _ (Icc_subset_Icc le_rfl hτb)
  rw [hPa] at h1
  calc
    ⨅ y' ∈ S, intExt D U x y' ≤ intExt D U x (P τ) :=
      iInf₂_le (f := fun y' (_ : y' ∈ S) => intExt D U x y') (P τ) hτT.2
    _ ≤ D.len P a b := h1.trans h2
    _ ≤ D (x, y) + ENNReal.ofReal ε := hlen
    _ = D (x, y) + ε := by rw [ENNReal.ofReal_coe_nnreal]

 
theorem setDist_eq_iInf_intExt {D : LSCMetric} (hcont : ∀ (γ : ℝ → ℂ) (a b : ℝ),
      D.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL : D.IsLengthSpace) {U V S M : Set ℂ} (hV : IsOpen V) (hcl : closure V ⊆ V ∪ S)
    (hS : IsClosed S) (hVSU : V ∪ S ⊆ U) (hMV : M ⊆ V) :
    OptimalConstants.Ratios.setDist D M S = ⨅ x ∈ M, ⨅ y ∈ S, intExt D U x y := by
  apply le_antisymm
  · exact iInf₂_mono fun x _ => iInf₂_mono fun y _ => dist_le_intExt D U x y
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    exact (iInf₂_le x hx).trans (iInf_intExt_le hcont hL hV hcl hS hVSU (hMV hx) hy)

 
theorem setDist_transfer {D₁ D₂ : LSCMetric}
    (hc₁ : ∀ (γ : ℝ → ℂ) (a b : ℝ), D₁.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hc₂ : ∀ (γ : ℝ → ℂ) (a b : ℝ), D₂.IsCurve γ a b → ContinuousOn γ (Icc a b))
    (hL₁ : D₁.IsLengthSpace) (hL₂ : D₂.IsLengthSpace) {U V S M : Set ℂ} (hV : IsOpen V)
    (hcl : closure V ⊆ V ∪ S) (hS : IsClosed S) (hVSU : V ∪ S ⊆ U) (hMV : M ⊆ V)
    (hI : ∀ x y, intExt D₁ U x y = intExt D₂ U x y) :
    OptimalConstants.Ratios.setDist D₁ M S = OptimalConstants.Ratios.setDist D₂ M S := by
  rw [setDist_eq_iInf_intExt hc₁ hL₁ hV hcl hS hVSU hMV,
    setDist_eq_iInf_intExt hc₂ hL₂ hV hcl hS hVSU hMV]
  simp only [hI]

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

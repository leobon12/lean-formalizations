/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsRun
import InteractingSLE.Spec.Supplement.WalkIntArc
import InteractingSLE.Spec.Supplement.WalkIntFiberCollar
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# The common-arc bookkeeping from the pieces' traversal direction

Packet PROVE-WALK-WORDS (the chronology-free fields of `WalkPairArcDataStatement`). Deterministic core
`exists_arcData`: given the two walks' proper parametrizations (ranges = physical sets), `PieceData` for every recorded
piece of both walks, and the **traversal direction** of common points (`hdir`: if a right-walk piece passes through
`z` then `z'` in its own time order, so does every left-walk piece through both), every nondegenerate preconnected
common subset `S` of a right piece and a left piece yields all the data of `WalkPairArcDataStatement`:

* a common point `p ∈ S` interior to a common arc of the two complete walks (`WalkInt.exists_common_arc_local_eq`),
  inside both pieces' launch domains and off the finitely many piece ends (`exists_mem_H_near` twice, then an open
  set of parameters minus a finite set);
* own times `tʳ`, `tˡ` of `p` with fresh windows (`α ∈ ℍ`), rational prefix times, global Loewner models
  (`PieceData.exists_model`);
* the local walk geometry (`exists_ball_walk_window`) and the local equality of the two walks.

The only input not derived here is `hdir` (the walk chronology, PROVE-T14-WALKINT).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWords

open WalkBdry

theorem exists_nnrat_mem_Ioo {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < (q : ℝ≥0) ∧ (q : ℝ≥0) < b := by
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := LocalExt.dense_range_coe_nnrat.exists_between h
  exact ⟨q, hq⟩

/-- A rational time in `(t, t + δ)` before the stop `S > t`. -/
theorem exists_nnrat_window {t : ℝ≥0} {S : ℝ≥0∞} (htS : (t : ℝ≥0∞) < S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ q : ℚ≥0, (t : ℝ) < ((q : ℝ≥0) : ℝ) ∧ ((q : ℝ≥0) : ℝ) < t + δ ∧ (((q : ℝ≥0)) : ℝ≥0∞) < S := by
  obtain ⟨r, htr, hrS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htS
  have htr' : t < r := ENNReal.coe_lt_coe.1 htr
  set d : ℝ≥0 := ⟨δ, hδ.le⟩ with hd
  have hlt : t < min r (t + d) := lt_min htr' (lt_add_of_pos_right _ (by rw [← NNReal.coe_pos]; exact hδ))
  obtain ⟨q, h1, h2⟩ := exists_nnrat_mem_Ioo hlt
  refine ⟨q, by exact_mod_cast h1, ?_, lt_of_le_of_lt (ENNReal.coe_le_coe.2 (h2.le.trans (min_le_left _ _))) hrS⟩
  have := (lt_min_iff.1 h2).2
  rw [← NNReal.coe_lt_coe, NNReal.coe_add] at this
  exact this

/-- The set of piece ends (starts, and ends at finite stops) of a list of pieces. -/
def pieceEnds (l : List Piece) : Set ℂ :=
  {z | ∃ p' ∈ l, p'.1.tipAt p'.2.1 0 z ∨ ∃ s : ℝ≥0, p'.2.2 = s ∧ p'.1.tipAt p'.2.1 s z}

theorem pieceEnds_finite (l : List Piece) : (pieceEnds l).Finite := by
  have h1 : ∀ p' : Piece, ({z | p'.1.tipAt p'.2.1 0 z} : Set ℂ).Subsingleton := fun p' z hz z' hz' =>
    Chart.tipAt_unique hz hz'
  have h2 : ∀ p' : Piece, ({z | ∃ s : ℝ≥0, p'.2.2 = s ∧ p'.1.tipAt p'.2.1 s z} : Set ℂ).Subsingleton := by
    rintro p' z ⟨s, hs, hz⟩ z' ⟨s', hs', hz'⟩
    have : s = s' := ENNReal.coe_injective (hs.symm.trans hs')
    subst this
    exact Chart.tipAt_unique hz hz'
  refine ((List.finite_toSet l).biUnion fun p' _ => (h1 p').finite.union (h2 p').finite).subset ?_
  rintro z ⟨p', hp', hz⟩
  exact mem_biUnion (x := p') hp' hz

/-- **The bookkeeping of a common arc** (deterministic; see the module docstring). -/
theorem exists_arcData {sR sL : ExplState} {γR γL : ℝ≥0 → ℂ}
    (hγR : Supp9B.IsProperCurve γR) (hγL : Supp9B.IsProperCurve γL)
    (hordR : ordOf sR ⊆ range γR) (hordL : ordOf sL ⊆ range γL)
    (hwR : range γR ∩ H = wsetOf sR) (hwL : range γL ∩ H = wsetOf sL)
    (hdR : ∀ (pre post : List Piece) (pc : Piece), sR.1 = pre ++ pc :: post →
      ∃ (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hdL : ∀ (pre post : List Piece) (pc : Piece), sL.1 = pre ++ pc :: post →
      ∃ (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc (⋃ p ∈ pre, p.1.tipSet p.2.1 p.2.2) f W α)
    (hdir : ∀ pR ∈ sR.1, ∀ pL ∈ sL.1, ∀ (a a' c c' : ℝ≥0) (z z' : ℂ), (a : ℝ≥0∞) ≤ pR.2.2 →
      (a' : ℝ≥0∞) ≤ pR.2.2 → (c : ℝ≥0∞) ≤ pL.2.2 → (c' : ℝ≥0∞) ≤ pL.2.2 →
      pR.1.tipAt pR.2.1 a z → pR.1.tipAt pR.2.1 a' z' → pL.1.tipAt pL.2.1 c z → pL.1.tipAt pL.2.1 c' z' →
      a < a' → c < c')
    {pR pL : Piece} (hpR : pR ∈ sR.1) (hpL : pL ∈ sL.1) {S : Set ℂ}
    (hS : S ⊆ closure (pR.1.tipSet pR.2.1 pR.2.2) ∩ closure (pL.1.tipSet pL.2.1 pL.2.2))
    (hSc : IsPreconnected S) (hSn : ¬ S.Subsingleton) :
    ∃ (preR postR preL postL : List Piece) (pcR pcL : Piece) (τR τL : ℚ≥0) (WR WL : ℝ → ℝ)
      (ηR ηL : ℝ → ℂ) (TR TL s₀R s₀L tR tL r : ℝ),
      sR.1 = preR ++ pcR :: postR ∧ (((τR : ℝ≥0)) : ℝ≥0∞) < pcR.2.2 ∧
      sL.1 = preL ++ pcL :: postL ∧ (((τL : ℝ≥0)) : ℝ≥0∞) < pcL.2.2 ∧
      pcR.1.IsConformal ∧ pcL.1.IsConformal ∧
      Continuous WR ∧ WR 0 = 0 ∧ IsLoewnerTrace WR ηR ∧ ((τR : ℝ≥0) : ℝ) < TR ∧
        ContinuousOn (pieceDrv pcR) (Icc 0 TR) ∧ EqOn (pieceDrv pcR) WR (Icc 0 TR) ∧
      Continuous WL ∧ WL 0 = 0 ∧ IsLoewnerTrace WL ηL ∧ ((τL : ℝ≥0) : ℝ) < TL ∧
        ContinuousOn (pieceDrv pcL) (Icc 0 TL) ∧ EqOn (pieceDrv pcL) WL (Icc 0 TL) ∧
      0 ≤ s₀R ∧ s₀R < tR ∧ tR < ((τR : ℝ≥0) : ℝ) ∧ InjOn ηR (Icc 0 ((τR : ℝ≥0) : ℝ)) ∧
        (∀ s ∈ Ioc s₀R ((τR : ℝ≥0) : ℝ), ηR s ∈ H) ∧
      0 ≤ s₀L ∧ s₀L < tL ∧ tL < ((τL : ℝ≥0) : ℝ) ∧ InjOn ηL (Icc 0 ((τL : ℝ≥0) : ℝ)) ∧
        (∀ s ∈ Ioc s₀L ((τL : ℝ≥0) : ℝ), ηL s ∈ H) ∧
      pcR.1.2.1 (ηR tR) = pcL.1.2.1 (ηL tL) ∧
      (∀ s ∈ Ioc tR ((τR : ℝ≥0) : ℝ), ∃ s' ∈ Ioo tL ((τL : ℝ≥0) : ℝ),
        pcR.1.2.1 (ηR s) = pcL.1.2.1 (ηL s')) ∧
      0 < r ∧
      wsetOf sR ∩ ball (pcR.1.2.1 (ηR tR)) r ⊆ prefixSet preR pcR τR ∧
      wsetOf sL ∩ ball (pcR.1.2.1 (ηR tR)) r ⊆ prefixSet preL pcL τL ∧
      wsetOf sR ∩ ball (pcR.1.2.1 (ηR tR)) r = wsetOf sL ∩ ball (pcR.1.2.1 (ηR tR)) r ∧
      ∀ z ∈ wsetOf sL ∩ ball (pcR.1.2.1 (ηR tR)) r,
        ∃ s' ∈ Icc 0 ((τL : ℝ≥0) : ℝ), ηL s' ∈ H ∧ z = pcL.1.2.1 (ηL s') := by
  classical
  -- the two pieces and their data
  obtain ⟨preR, postR, hsR⟩ := List.append_of_mem hpR
  obtain ⟨preL, postL, hsL⟩ := List.append_of_mem hpL
  obtain ⟨fR, VR, αR, dR⟩ := hdR _ _ _ hsR
  obtain ⟨fL, VL, αL, dL⟩ := hdL _ _ _ hsL
  have hmemR : ∀ p' ∈ sR.1, ∀ w ∈ p'.1.tipSet p'.2.1 p'.2.2, w ∈ range γR := fun p' hp' w hw =>
    hordR (mem_iUnion₂.2 ⟨p', hp', hw⟩)
  have hmemL : ∀ p' ∈ sL.1, ∀ w ∈ p'.1.tipSet p'.2.1 p'.2.2, w ∈ range γL := fun p' hp' w hw =>
    hordL (mem_iUnion₂.2 ⟨p', hp', hw⟩)
  have hclR : ∀ p' ∈ sR.1, IsClosed (p'.1.tipSet p'.2.1 p'.2.2) := fun p' hp' => by
    obtain ⟨a', b', h'⟩ := List.append_of_mem hp'
    obtain ⟨_, _, _, d'⟩ := hdR _ _ _ h'
    exact d'.isClosed_tipSet
  have hclL : ∀ p' ∈ sL.1, IsClosed (p'.1.tipSet p'.2.1 p'.2.2) := fun p' hp' => by
    obtain ⟨a', b', h'⟩ := List.append_of_mem hp'
    obtain ⟨_, _, _, d'⟩ := hdL _ _ _ h'
    exact d'.isClosed_tipSet
  have hpostR : ∀ p' ∈ postR, ∀ z ∈ p'.1.tipSet p'.2.1 p'.2.2, z ∈ pR.1.tipSet pR.2.1 pR.2.2 →
      p'.1.tipAt p'.2.1 0 z := by
    intro p' hp' z hz hzpc
    obtain ⟨m, post', hpost⟩ := List.append_of_mem hp'
    have hdec : sR.1 = (preR ++ pR :: m) ++ p' :: post' := by rw [hsR, hpost]; simp
    obtain ⟨_, _, _, d'⟩ := hdR _ _ _ hdec
    exact d'.tipAt_zero_of_mem (fun w hw => mem_iUnion₂.2 ⟨pR, by simp, hw⟩) hz hzpc
  have hpostL : ∀ p' ∈ postL, ∀ z ∈ p'.1.tipSet p'.2.1 p'.2.2, z ∈ pL.1.tipSet pL.2.1 pL.2.2 →
      p'.1.tipAt p'.2.1 0 z := by
    intro p' hp' z hz hzpc
    obtain ⟨m, post', hpost⟩ := List.append_of_mem hp'
    have hdec : sL.1 = (preL ++ pL :: m) ++ p' :: post' := by rw [hsL, hpost]; simp
    obtain ⟨_, _, _, d'⟩ := hdL _ _ _ hdec
    exact d'.tipAt_zero_of_mem (fun w hw => mem_iUnion₂.2 ⟨pL, by simp, hw⟩) hz hzpc
  set gR : ℝ≥0 → ℂ := fun t => fR (αR t) with hgR
  set gL : ℝ≥0 → ℂ := fun t => fL (αL t) with hgL
  have hcR : closure (pR.1.tipSet pR.2.1 pR.2.2) = gR '' {t | (t : ℝ≥0∞) ≤ pR.2.2} := by
    rw [dR.isClosed_tipSet.closure_eq, dR.tipSet_eq]
  have hcL : closure (pL.1.tipSet pL.2.1 pL.2.2) = gL '' {t | (t : ℝ≥0∞) ≤ pL.2.2} := by
    rw [dL.isClosed_tipSet.closure_eq, dL.tipSet_eq]
  -- the common arc of the complete walks
  have hemb := WalkCont.isClosedEmbedding_of_isProperCurve hγR
  have hSsub : S ⊆ range γR ∩ range γL := by
    intro z hz
    obtain ⟨h1, h2⟩ := hS hz
    rw [hcR] at h1; rw [hcL] at h2
    obtain ⟨t, ht, rfl⟩ := h1
    obtain ⟨t', ht', he⟩ := h2
    refine ⟨hmemR pR hpR _ (by rw [dR.tipSet_eq]; exact ⟨t, ht, rfl⟩), ?_⟩
    rw [← he]; exact hmemL pL hpL _ (by rw [dL.tipSet_eq]; exact ⟨t', ht', rfl⟩)
  obtain ⟨a, b, hab, hsub, hloc⟩ := WalkInt.exists_common_arc_local_eq hγR hγL hSsub hSc hSn
  -- two distinct times on each piece
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.not_subsingleton_iff.1 hSn
  have htwoR : ∀ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) ≤ pR.2.2 → ∃ t₁ : ℝ≥0, (t₁ : ℝ≥0∞) ≤ pR.2.2 ∧ t₀ ≠ t₁ := by
    intro t₀ _
    have hx' := (hS hx).1; have hy' := (hS hy).1
    rw [hcR] at hx' hy'
    obtain ⟨tx, htx, rfl⟩ := hx'
    obtain ⟨ty, hty, rfl⟩ := hy'
    by_cases h : t₀ = tx
    · exact ⟨ty, hty, fun h' => hxy (by rw [← h, h'])⟩
    · exact ⟨tx, htx, h⟩
  have htwoL : ∀ t₀ : ℝ≥0, (t₀ : ℝ≥0∞) ≤ pL.2.2 → ∃ t₁ : ℝ≥0, (t₁ : ℝ≥0∞) ≤ pL.2.2 ∧ t₀ ≠ t₁ := by
    intro t₀ _
    have hx' := (hS hx).2; have hy' := (hS hy).2
    rw [hcL] at hx' hy'
    obtain ⟨tx, htx, rfl⟩ := hx'
    obtain ⟨ty, hty, rfl⟩ := hy'
    by_cases h : t₀ = tx
    · exact ⟨ty, hty, fun h' => hxy (by rw [← h, h'])⟩
    · exact ⟨tx, htx, h⟩
  -- the complement of the far part of the arc
  set V₀ : Set ℂ := (γR '' {u | u ≤ a ∨ b ≤ u})ᶜ with hV₀
  have hV₀o : IsOpen V₀ := (hemb.isClosedMap _ ((isClosed_le continuous_id continuous_const).union
    (isClosed_le continuous_const continuous_id))).isOpen_compl
  have hV₀mem : ∀ z ∈ range γR, z ∈ V₀ → ∃ u ∈ Ioo a b, γR u = z := by
    rintro z ⟨u, rfl⟩ hz
    refine ⟨u, ⟨?_, ?_⟩, rfl⟩
    · by_contra h; exact hz ⟨u, Or.inl (not_lt.1 h), rfl⟩
    · by_contra h; exact hz ⟨u, Or.inr (not_lt.1 h), rfl⟩
  have hV₀arc : ∀ u ∈ Ioo a b, γR u ∈ V₀ := by
    rintro u hu ⟨u', hu', he⟩
    have := hγR.2.1 he
    subst this
    rcases hu' with h | h
    · exact absurd hu.1 (not_lt.2 h)
    · exact absurd hu.2 (not_lt.2 h)
  -- a point of the arc in the launch domain of the right piece
  set u₀ : ℝ≥0 := (a + b) / 2 with hu₀
  have hu₀ab : u₀ ∈ Ioo a b := by
    have hab' : (a : ℝ) < b := by exact_mod_cast hab
    have hr : (u₀ : ℝ) = ((a : ℝ) + b) / 2 := by rw [hu₀]; push_cast; ring
    constructor
    · rw [← NNReal.coe_lt_coe, hr]; linarith
    · rw [← NNReal.coe_lt_coe, hr]; linarith
  have hq₀S : γR u₀ ∈ S := hsub ⟨u₀, Ioo_subset_Icc_self hu₀ab, rfl⟩
  obtain ⟨t₀, ht₀, he₀⟩ : γR u₀ ∈ gR '' {t | (t : ℝ≥0∞) ≤ pR.2.2} := by rw [← hcR]; exact (hS hq₀S).1
  obtain ⟨t₀', ht₀', hne₀⟩ := htwoR t₀ ht₀
  obtain ⟨t₁, ht₁, hα₁, hg₁⟩ := dR.exists_mem_H_near ht₀ ht₀' hne₀ hV₀o
    (by have h := hV₀arc u₀ hu₀ab; rw [← he₀] at h; exact h)
  obtain ⟨u₁, hu₁, he₁⟩ := hV₀mem _ (hmemR pR hpR _ (by rw [dR.tipSet_eq]; exact ⟨t₁, ht₁, rfl⟩)) hg₁
  have hq₁R : gR t₁ ∈ pR.1.2.1 '' H := ⟨αR t₁, hα₁, (dR.eq_of_mem_H hα₁).symm⟩
  -- a point of the arc in both launch domains
  obtain ⟨r₁, hr₁, heq₁⟩ := hloc u₁ hu₁
  have hq₁S : γR u₁ ∈ S := hsub ⟨u₁, Ioo_subset_Icc_self hu₁, rfl⟩
  obtain ⟨t₂, ht₂, he₂⟩ : γR u₁ ∈ gL '' {t | (t : ℝ≥0∞) ≤ pL.2.2} := by rw [← hcL]; exact (hS hq₁S).2
  obtain ⟨t₂', ht₂', hne₂⟩ := htwoL t₂ ht₂
  set V₁ : Set ℂ := ball (γR u₁) r₁ ∩ (pR.1.2.1 '' H) ∩ V₀ with hV₁
  have hV₁o : IsOpen V₁ := (isOpen_ball.inter dR.conf.isOpen_image).inter hV₀o
  have hq₁V₁ : gL t₂ ∈ V₁ := by
    rw [he₂]
    exact ⟨⟨mem_ball_self hr₁, by rw [he₁]; exact hq₁R⟩, hV₀arc u₁ hu₁⟩
  obtain ⟨t₃, ht₃, hα₃, hg₃⟩ := dL.exists_mem_H_near ht₂ ht₂' hne₂ hV₁o hq₁V₁
  have hq₂γL : gL t₃ ∈ range γL ∩ ball (γR u₁) r₁ :=
    ⟨hmemL pL hpL _ (by rw [dL.tipSet_eq]; exact ⟨t₃, ht₃, rfl⟩), hg₃.1.1⟩
  rw [← heq₁] at hq₂γL
  obtain ⟨u₂, hu₂, he₂'⟩ := hV₀mem _ hq₂γL.1 hg₃.2
  set O : Set ℂ := (pR.1.2.1 '' H) ∩ (pL.1.2.1 '' H) with hOdef
  have hOo : IsOpen O := dR.conf.isOpen_image.inter dL.conf.isOpen_image
  have hu₂O : γR u₂ ∈ O := by
    rw [he₂']
    exact ⟨hg₃.1.2, ⟨αL t₃, hα₃, (dL.eq_of_mem_H hα₃).symm⟩⟩
  -- the good parameters form an open set, which is infinite
  have hGo : IsOpen (γR ⁻¹' O ∩ Ioo a b) := (hOo.preimage hγR.1).inter isOpen_Ioo
  obtain ⟨ε, hε, hεG⟩ := Metric.isOpen_iff.1 hGo u₂ ⟨hu₂O, hu₂⟩
  set e : ℝ≥0 := ⟨ε / 2, by positivity⟩ with hedef
  have he0 : 0 < e := by rw [← NNReal.coe_pos]; show 0 < ε / 2; positivity
  have hfin := (pieceEnds_finite (sR.1 ++ sL.1)).preimage (hγR.2.1.injOn)
  obtain ⟨u, hu, huF⟩ := (Set.Ioo_infinite (lt_add_of_pos_right u₂ he0)).exists_notMem_finite hfin
  have huG : u ∈ γR ⁻¹' O ∩ Ioo a b := hεG (by
    rw [mem_ball, NNReal.dist_eq, abs_lt]
    have h1 : (u₂ : ℝ) < u := by exact_mod_cast hu.1
    have h2 : (u : ℝ) < u₂ + ε / 2 := by
      have := hu.2
      rw [← NNReal.coe_lt_coe, NNReal.coe_add] at this
      exact this
    constructor <;> linarith)
  -- the common point and its own times
  set p : ℂ := γR u with hpdef
  have hpO : p ∈ O := huG.1
  have hpF : p ∉ pieceEnds (sR.1 ++ sL.1) := huF
  obtain ⟨ra, hra, heqa⟩ := hloc u huG.2
  have hpS : p ∈ S := hsub ⟨u, Ioo_subset_Icc_self huG.2, rfl⟩
  obtain ⟨tR, htRD, htRe⟩ : p ∈ gR '' {t | (t : ℝ≥0∞) ≤ pR.2.2} := by rw [← hcR]; exact (hS hpS).1
  obtain ⟨tL, htLD, htLe⟩ : p ∈ gL '' {t | (t : ℝ≥0∞) ≤ pL.2.2} := by rw [← hcL]; exact (hS hpS).2
  have hendR : 0 < tR ∧ (tR : ℝ≥0∞) < pR.2.2 := by
    refine ⟨?_, lt_of_le_of_ne htRD fun h => hpF ⟨pR, List.mem_append_left _ hpR, Or.inr ⟨tR, h.symm, ?_⟩⟩⟩
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ tR) with h0 | h0
      · refine absurd ⟨pR, List.mem_append_left _ hpR, Or.inl ?_⟩ hpF
        rw [← htRe, ← h0]; exact dR.tipAt (by simp)
      · exact h0
    · rw [← htRe]; exact dR.tipAt htRD
  have hendL : 0 < tL ∧ (tL : ℝ≥0∞) < pL.2.2 := by
    refine ⟨?_, lt_of_le_of_ne htLD fun h => hpF ⟨pL, List.mem_append_right _ hpL, Or.inr ⟨tL, h.symm, ?_⟩⟩⟩
    · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ tL) with h0 | h0
      · refine absurd ⟨pL, List.mem_append_right _ hpL, Or.inl ?_⟩ hpF
        rw [← htLe, ← h0]; exact dL.tipAt (by simp)
      · exact h0
    · rw [← htLe]; exact dL.tipAt htLD
  have hnoR : ∀ p' ∈ postR, ¬ p'.1.tipAt p'.2.1 0 (gR tR) := fun p' hp' h => hpF
    ⟨p', List.mem_append_left _ (by rw [hsR]; simp [hp']), Or.inl (by rw [← htRe]; exact h)⟩
  have hnoL : ∀ p' ∈ postL, ¬ p'.1.tipAt p'.2.1 0 (gL tL) := fun p' hp' h => hpF
    ⟨p', List.mem_append_right _ (by rw [hsL]; simp [hp']), Or.inl (by rw [← htLe]; exact h)⟩
  -- the left window, prefix time and model
  obtain ⟨εL, hεL, hwinL⟩ := dL.exists_window htLD dL.conf.isOpen_image
    (by show gL tL ∈ _; rw [htLe]; exact hpO.2)
  set δL : ℝ := min εL (tL : ℝ) with hδLdef
  have hδL : 0 < δL := lt_min hεL (by exact_mod_cast hendL.1)
  have hδL1 : δL ≤ εL := min_le_left _ _
  have hδL2 : δL ≤ tL := min_le_right _ _
  obtain ⟨τL, hτL1, hτL2, hτLS⟩ := exists_nnrat_window hendL.2 hδL
  set s₀L : ℝ := (tL : ℝ) - δL / 2 with hs₀L
  have hHwL : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pL.2.2 → s₀L < t → (t : ℝ) < (τL : ℝ≥0) → αL t ∈ H := by
    intro t ht h1 h2
    refine dL.mem_H_of_mem_image ht (hwinL t ht ?_)
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨WL, ηL, TL, hτTL, hWLc, hWL0, hηL, hpcL, hagL, hηLα⟩ := dL.exists_model hτLS
  obtain ⟨ρL, hρL, hwinL2⟩ := exists_ball_walk_window hsL dL hclL hpostL hendL.1 htLD hnoL
    (lo := s₀L) (hi := ((τL : ℝ≥0) : ℝ)) (by rw [hs₀L]; linarith) hτL1
  have hcL' : fL (αL tL) = p := htLe
  rw [hcL'] at hwinL2
  -- the right window, prefix time and model
  obtain ⟨εR, hεR, hwinR⟩ := dR.exists_window htRD (dR.conf.isOpen_image.inter isOpen_ball)
    (V := pR.1.2.1 '' H ∩ ball p (min ρL ra))
    (by show gR tR ∈ pR.1.2.1 '' H ∩ ball p (min ρL ra)
        rw [htRe]; exact ⟨hpO.1, mem_ball_self (lt_min hρL hra)⟩)
  set δR : ℝ := min εR (tR : ℝ) with hδRdef
  have hδR : 0 < δR := lt_min hεR (by exact_mod_cast hendR.1)
  have hδR1 : δR ≤ εR := min_le_left _ _
  have hδR2 : δR ≤ tR := min_le_right _ _
  obtain ⟨τR, hτR1, hτR2, hτRS⟩ := exists_nnrat_window hendR.2 hδR
  set s₀R : ℝ := (tR : ℝ) - δR / 2 with hs₀R
  have hwinR' : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ pR.2.2 → s₀R < t → (t : ℝ) ≤ (τR : ℝ≥0) →
      gR t ∈ pR.1.2.1 '' H ∩ ball p (min ρL ra) := by
    intro t ht h1 h2
    refine hwinR t ht ?_
    rw [abs_lt]; constructor <;> linarith
  obtain ⟨WR, ηR, TR, hτTR, hWRc, hWR0, hηR, hpcR, hagR, hηRα⟩ := dR.exists_model hτRS
  obtain ⟨ρR, hρR, hwinR2⟩ := exists_ball_walk_window hsR dR hclR hpostR hendR.1 htRD hnoR
    (lo := s₀R) (hi := ((τR : ℝ≥0) : ℝ)) (by rw [hs₀R]; linarith) hτR1
  have hcR' : fR (αR tR) = p := htRe
  rw [hcR'] at hwinR2
  -- the model traces at the own times
  have hηRt : ∀ t : ℝ≥0, (t : ℝ) ≤ TR → ηR t = αR t := fun t ht => by
    rw [hηRα t ⟨t.coe_nonneg, ht⟩, Real.toNNReal_coe]
  have hηLt : ∀ t : ℝ≥0, (t : ℝ) ≤ TL → ηL t = αL t := fun t ht => by
    rw [hηLα t ⟨t.coe_nonneg, ht⟩, Real.toNNReal_coe]
  have htSR : ∀ t : ℝ≥0, (t : ℝ) ≤ (τR : ℝ≥0) → (t : ℝ≥0∞) ≤ pR.2.2 := fun t ht =>
    le_trans (ENNReal.coe_le_coe.2 (by exact_mod_cast ht)) hτRS.le
  have htSL : ∀ t : ℝ≥0, (t : ℝ) ≤ (τL : ℝ≥0) → (t : ℝ≥0∞) ≤ pL.2.2 := fun t ht =>
    le_trans (ENNReal.coe_le_coe.2 (by exact_mod_cast ht)) hτLS.le
  have hαR : αR tR ∈ H := dR.mem_H_of_mem_image htRD (by show gR tR ∈ _; rw [htRe]; exact hpO.1)
  have hαL : αL tL ∈ H := dL.mem_H_of_mem_image htLD (by show gL tL ∈ _; rw [htLe]; exact hpO.2)
  have hpR' : pR.1.2.1 (ηR tR) = p := by
    rw [hηRt tR (hτR1.le.trans hτTR.le), ← dR.eq_of_mem_H hαR]; exact htRe
  have hpL' : pL.1.2.1 (ηL tL) = p := by
    rw [hηLt tL (hτL1.le.trans hτTL.le), ← dL.eq_of_mem_H hαL]; exact htLe
  have hr0 : 0 < min ρR (min ρL ra) := lt_min hρR (lt_min hρL hra)
  have hrR : min ρR (min ρL ra) ≤ ρR := min_le_left _ _
  have hrL : min ρR (min ρL ra) ≤ ρL := (min_le_right _ _).trans (min_le_left _ _)
  have hra' : min ρR (min ρL ra) ≤ ra := (min_le_right _ _).trans (min_le_right _ _)
  have htR0 : (0 : ℝ) ≤ tR := tR.coe_nonneg
  have htL0 : (0 : ℝ) ≤ tL := tL.coe_nonneg
  -- injectivity and freshness of the models
  have hinjR : InjOn ηR (Icc 0 ((τR : ℝ≥0) : ℝ)) := by
    intro r₁ hr₁ r₂ hr₂ he
    rw [hηRα r₁ ⟨hr₁.1, hr₁.2.trans hτTR.le⟩, hηRα r₂ ⟨hr₂.1, hr₂.2.trans hτTR.le⟩] at he
    have hd1 := htSR r₁.toNNReal (by rw [Real.coe_toNNReal _ hr₁.1]; exact hr₁.2)
    have hd2 := htSR r₂.toNNReal (by rw [Real.coe_toNNReal _ hr₂.1]; exact hr₂.2)
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) (dR.inj hd1 hd2 (show fR (αR _) = fR (αR _) by rw [he]))
    simp only [Real.coe_toNNReal _ hr₁.1, Real.coe_toNNReal _ hr₂.1] at h
    exact h
  have hinjL : InjOn ηL (Icc 0 ((τL : ℝ≥0) : ℝ)) := by
    intro r₁ hr₁ r₂ hr₂ he
    rw [hηLα r₁ ⟨hr₁.1, hr₁.2.trans hτTL.le⟩, hηLα r₂ ⟨hr₂.1, hr₂.2.trans hτTL.le⟩] at he
    have hd1 := htSL r₁.toNNReal (by rw [Real.coe_toNNReal _ hr₁.1]; exact hr₁.2)
    have hd2 := htSL r₂.toNNReal (by rw [Real.coe_toNNReal _ hr₂.1]; exact hr₂.2)
    have h := congrArg (fun t : ℝ≥0 => (t : ℝ)) (dL.inj hd1 hd2 (show fL (αL _) = fL (αL _) by rw [he]))
    simp only [Real.coe_toNNReal _ hr₁.1, Real.coe_toNNReal _ hr₂.1] at h
    exact h
  have hfreshR : ∀ s ∈ Ioc s₀R ((τR : ℝ≥0) : ℝ), ηR s ∈ H := by
    intro s hs
    have hs0 : 0 ≤ s := by rw [hs₀R] at hs; linarith [hs.1]
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
    rw [hηRα s ⟨hs0, hs.2.trans hτTR.le⟩]
    have hS' := htSR s.toNNReal (by rw [hs']; exact hs.2)
    exact dR.mem_H_of_mem_image hS' (hwinR' _ hS' (by rw [hs']; exact hs.1) (by rw [hs']; exact hs.2)).1
  have hfreshL : ∀ s ∈ Ioc s₀L ((τL : ℝ≥0) : ℝ), ηL s ∈ H := by
    intro s hs
    have hs0 : 0 ≤ s := by rw [hs₀L] at hs; linarith [hs.1]
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
    rw [hηLα s ⟨hs0, hs.2.trans hτTL.le⟩]
    have hS' := htSL s.toNNReal (by rw [hs']; exact hs.2)
    by_cases hlt : s < (τL : ℝ≥0)
    · exact hHwL _ hS' (by rw [hs']; exact hs.1) (by rw [hs']; exact hlt)
    · have hseq : s = (τL : ℝ≥0) := le_antisymm hs.2 (not_lt.1 hlt)
      refine dL.mem_H_of_mem_image hS' (hwinL _ hS' ?_)
      rw [hs', abs_lt]; constructor <;> linarith
  refine ⟨preR, postR, preL, postL, pR, pL, τR, τL, WR, WL, ηR, ηL, TR, TL, s₀R, s₀L, tR, tL,
    min ρR (min ρL ra), hsR, hτRS, hsL, hτLS, dR.conf, dL.conf, hWRc, hWR0, hηR, hτTR, hpcR, hagR,
    hWLc, hWL0, hηL, hτTL, hpcL, hagL, by rw [hs₀R]; linarith, by rw [hs₀R]; linarith, hτR1, hinjR, hfreshR,
    by rw [hs₀L]; linarith, by rw [hs₀L]; linarith, hτL1, hinjL, hfreshL, by rw [hpR', hpL'], ?_, hr0,
    ?_, ?_, ?_, ?_⟩
  · -- the direction
    intro s hs
    have hs0 : 0 ≤ s := htR0.trans hs.1.le
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0
    have hs'S := htSR s.toNNReal (by rw [hs']; exact hs.2)
    obtain ⟨hdom', hball'⟩ := hwinR' _ hs'S (by rw [hs', hs₀R]; linarith [hs.1]) (by rw [hs']; exact hs.2)
    have hαs : αR s.toNNReal ∈ H := dR.mem_H_of_mem_image hs'S hdom'
    have hzR : gR s.toNNReal ∈ range γR := hmemR pR hpR _ (by rw [dR.tipSet_eq]; exact ⟨_, hs'S, rfl⟩)
    have hzH : gR s.toNNReal ∈ H := by
      show fR (αR s.toNNReal) ∈ H
      rw [dR.eq_of_mem_H hαs]; exact dR.conf.2.1 hαs
    have hzL : gR s.toNNReal ∈ range γL ∩ ball p ra := by
      rw [← heqa]; exact ⟨hzR, ball_subset_ball (min_le_right _ _) hball'⟩
    have hzW : gR s.toNNReal ∈ wsetOf sL := by rw [← hwL]; exact ⟨hzL.1, hzH⟩
    obtain ⟨t, htS, ht1, ht2, hte⟩ := hwinL2 _ ⟨hzW.1, ball_subset_ball (min_le_left _ _) hball'⟩
    have hlt : tL < t := hdir pR hpR pL hpL tR s.toNNReal tL t p (gR s.toNNReal) htRD hs'S htLD htS
      (by rw [← htRe]; exact dR.tipAt htRD) (dR.tipAt hs'S) (by rw [← htLe]; exact dL.tipAt htLD)
      (by rw [hte]; exact dL.tipAt htS) (by rw [← NNReal.coe_lt_coe, hs']; exact hs.1)
    refine ⟨t, ⟨by exact_mod_cast hlt, ht2⟩, ?_⟩
    have hαt : αL t ∈ H := hHwL t htS ht1 ht2
    rw [hηRα s ⟨hs0, hs.2.trans hτTR.le⟩, hηLt t (ht2.le.trans hτTL.le), ← dR.eq_of_mem_H hαs,
      ← dL.eq_of_mem_H hαt]
    exact hte
  · -- the right walk near `p` is its prefix
    rw [hpR']
    rintro z ⟨⟨hzO, hzH⟩, hzb⟩
    obtain ⟨t, htS, -, ht2, rfl⟩ := hwinR2 _ ⟨hzO, ball_subset_ball hrR hzb⟩
    refine ⟨Or.inr ⟨t, ?_, dR.tipAt htS⟩, hzH⟩
    exact ENNReal.coe_le_coe.2 (by exact_mod_cast ht2.le)
  · -- the left walk near `p` is its prefix
    rw [hpR']
    rintro z ⟨⟨hzO, hzH⟩, hzb⟩
    obtain ⟨t, htS, -, ht2, rfl⟩ := hwinL2 _ ⟨hzO, ball_subset_ball hrL hzb⟩
    refine ⟨Or.inr ⟨t, ?_, dL.tipAt htS⟩, hzH⟩
    exact ENNReal.coe_le_coe.2 (by exact_mod_cast ht2.le)
  · -- the two walks agree near `p`
    rw [hpR', ← hwR, ← hwL]
    ext z
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : z ∈ range γR ∩ ball p ra := ⟨h1, ball_subset_ball hra' h3⟩
      rw [heqa] at h4
      exact ⟨⟨h4.1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : z ∈ range γL ∩ ball p ra := ⟨h1, ball_subset_ball hra' h3⟩
      rw [← heqa] at h4
      exact ⟨⟨h4.1, h2⟩, h3⟩
  · -- the left walk near `p` is its own piece's trace
    rw [hpR']
    rintro z ⟨⟨hzO, -⟩, hzb⟩
    obtain ⟨t, htS, ht1, ht2, rfl⟩ := hwinL2 _ ⟨hzO, ball_subset_ball hrL hzb⟩
    have hαt := hHwL t htS ht1 ht2
    refine ⟨t, ⟨t.coe_nonneg, ht2.le⟩, by rw [hηLt t (ht2.le.trans hτTL.le)]; exact hαt, ?_⟩
    rw [hηLt t (ht2.le.trans hτTL.le)]
    exact dL.eq_of_mem_H hαt

/-- **Named input: the traversal direction of common points** (Theorem GW4, proof, p. 637: "Every common contact is
ordered the same way on the two walks"; with each recorded piece traversed by its walk in its own time). Almost surely,
if a recorded piece of the right walk passes through `z` at own time `a` and through `z'` at a later own time `a'`,
then every recorded piece of the left walk passing through `z` at `c` and through `z'` at `c'` has `c < c'`.
Same hypotheses as `WalkPairArcDataStatement`. -/
def WalkPieceDirectionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkInf.WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkNorm.WalkPiecesSimple κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (WalkMean.walkRuns κ b jumps E ω).1.1, ∀ pL ∈ (WalkMean.walkRuns κ b jumps E ω).2.1,
        ∀ (a a' c c' : ℝ≥0) (z z' : ℂ), (a : ℝ≥0∞) ≤ pR.2.2 → (a' : ℝ≥0∞) ≤ pR.2.2 →
          (c : ℝ≥0∞) ≤ pL.2.2 → (c' : ℝ≥0∞) ≤ pL.2.2 →
          pR.1.tipAt pR.2.1 a z → pR.1.tipAt pR.2.1 a' z' → pL.1.tipAt pL.2.1 c z → pL.1.tipAt pL.2.1 c' z' →
          a < a' → c < c'

/-- **`WalkPairArcDataStatement` from the traversal direction**: every other field (pieces, a common fresh point,
prefix times, global models, local walk geometry) is derived. -/
theorem walkPairArcDataStatement_of_direction (hdir : WalkPieceDirectionStatement.{u}) :
    WalkPairArcDataStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  filter_upwards [hdir κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple, hfacts, hsimple,
    hRR, hRL] with ω hω hf hs hωR hωL pR hpR pL hpL S hS hSc hSn
  obtain ⟨⟨γR, hγR, -, hrγR⟩, ⟨γL, hγL, -, hrγL⟩, -⟩ := hf
  refine exists_arcData hγR hγL ?_ ?_ ?_ ?_ ?_ ?_ hω hpR hpL hS hSc hSn
  · intro z hz; rw [hrγR]; exact Or.inl (Or.inr hz)
  · intro z hz; rw [hrγL]; exact Or.inl (Or.inr hz)
  · rw [hrγR]; exact WalkIntFiber.physOf_inter_H _ _
  · rw [hrγL]; exact WalkIntFiber.physOf_inter_H _ _
  · intro pre post pc hs'
    exact exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)
      (fun k c θ hl => WalkNorm.pieceRegular_of_event hωR k c θ hl) (fun k c θ hl => hs true k c θ hl) hs'
  · intro pre post pc hs'
    exact exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)
      (fun k c θ hl => WalkNorm.pieceRegular_of_event hωL k c θ hl) (fun k c θ hl => hs false k c θ hl) hs'

/-- **Theorem 1.4's leaf `WalkBdry.WalkPairGeomStatement`** from the traversal direction, the contact order, the
proper walk parametrizations and GW1 piece simplicity. -/
theorem walkPairGeomStatement_of_direction (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hS : GW1Z.GW1PieceSimpleStatement.{u}) (hdir : WalkPieceDirectionStatement.{u}) :
    WalkBdry.WalkPairGeomStatement.{u} :=
  walkPairGeomStatement_of_arcData hCO hPR hPL hS (walkPairArcDataStatement_of_direction hdir)

end InteractingSLE.Theorem14.WalkWords
